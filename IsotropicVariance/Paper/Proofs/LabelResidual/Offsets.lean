/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Labels
public import Mathlib.Data.Finset.Card
public import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Counting offsets which fail to contain a bounded set in one core

These are the random-offset counts used in the proof of Lemma `lem:residual`.

A failure is witnessed by an integer group boundary in a short coordinate
interval. Counting its residues and taking a union bound gives the estimate.
-/

@[expose] public section

namespace IsotropicVariance.Paper.Proofs.LabelResidual.OffsetGeometry

/-- The residue of an integer as an offset. -/
def offsetResidue (L : ℕ+) (z : ℤ) : Fin (L : ℕ) :=
  ⟨(z % (L : ℤ)).toNat, by
    have hpos : 0 < (L : ℤ) := by exact_mod_cast L.pos
    have hlo := Int.emod_nonneg z hpos.ne'
    have hhi := Int.emod_lt_of_pos z hpos
    omega⟩

/-- The offset of an integer group boundary is its residue. -/
theorem offsetResidue_boundary (L : ℕ+) (u : Fin (L : ℕ)) (k : ℤ) :
    offsetResidue L ((u : ℕ) + (L : ℤ) * k) = u := by
  apply Fin.ext
  change ((((u : ℕ) : ℤ) + (L : ℤ) * k) % (L : ℤ)).toNat = (u : ℕ)
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast u.isLt)]
  exact Int.toNat_natCast _

/-- Offsets having a group boundary in the real interval `(a,b]`. -/
noncomputable def boundaryOffsets (L : ℕ+) (a b : ℝ) : Finset (Fin (L : ℕ)) :=
  (Finset.Ioc ⌊a⌋ ⌊b⌋).image (offsetResidue L)

/-- At most `b-a+1` offsets have a boundary in an interval of length `b-a`. -/
theorem card_boundaryOffsets_le (L : ℕ+) {a b : ℝ} (hab : a ≤ b) :
    ((boundaryOffsets L a b).card : ℝ) ≤ b - a + 1 := by
  have hcard := Finset.card_image_le (s := Finset.Ioc ⌊a⌋ ⌊b⌋) (f := offsetResidue L)
  have hcast : ((Finset.Ioc ⌊a⌋ ⌊b⌋).card : ℝ) = (⌊b⌋ : ℝ) - (⌊a⌋ : ℝ) := by
    exact_mod_cast Int.card_Ioc_of_le ⌊a⌋ ⌊b⌋ (Int.floor_mono hab)
  calc
    _ ≤ ((Finset.Ioc ⌊a⌋ ⌊b⌋).card : ℝ) := by exact_mod_cast hcard
    _ = (⌊b⌋ : ℝ) - (⌊a⌋ : ℝ) := hcast
    _ ≤ _ := by linarith only [Int.floor_le b, Int.lt_floor_add_one a]

/-- A core in cube units, with the upper faces half open. -/
def groupCore {m : ℕ} (L : ℕ+) (L₁ : ℝ) (u : Fin m → Fin (L : ℕ))
    (k : Fin m → ℤ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {y | ∀ i, (u i : ℝ) + (L : ℝ) * (k i : ℝ) + L₁ ≤ y i ∧
    y i < (u i : ℝ) + (L : ℝ) * (k i : ℝ) + (L : ℝ) - L₁}

/-- The offsets at which a set fails to lie in one group core. -/
noncomputable def badOffsets {m : ℕ} (L : ℕ+) (L₁ : ℝ)
    (S : Set (EuclideanSpace ℝ (Fin m))) : Finset (Fin m → Fin (L : ℕ)) :=
  by
    classical
    exact Finset.univ.filter (fun u => ¬ ∃ k, S ⊆ groupCore L L₁ u k)

/-- If a coordinate box does not fit in a core, one coordinate offset has a
boundary in the corresponding enlarged interval. -/
theorem badOffsets_subset_boundary_union {m : ℕ} (L : ℕ+) {L₁ D : ℝ}
    (a : Fin m → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS : ∀ y ∈ S, ∀ i, a i ≤ y i ∧ y i ≤ a i + D) :
    badOffsets L L₁ S ⊆ Finset.univ.biUnion (fun i : Fin m =>
      Finset.univ.filter (fun u : Fin m → Fin (L : ℕ) =>
        u i ∈ boundaryOffsets L (a i - L₁) (a i + D + L₁))) := by
  classical
  intro u hu
  have hbad := (Finset.mem_filter.mp hu).2
  by_contra hnot
  have hnone : ∀ i, u i ∉ boundaryOffsets L (a i - L₁) (a i + D + L₁) := by
    intro i hi
    exact hnot (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
  have hL : 0 < (L : ℝ) := by exact_mod_cast L.pos
  let k : Fin m → ℤ := fun i => ⌊(a i - L₁ - (u i : ℕ)) / (L : ℝ)⌋
  apply hbad
  refine ⟨k, fun y hy i => ?_⟩
  have hfloor := Int.floor_le ((a i - L₁ - (u i : ℕ)) / (L : ℝ))
  have hfloor' := Int.lt_floor_add_one ((a i - L₁ - (u i : ℕ)) / (L : ℝ))
  have hlo := (le_div_iff₀ hL).mp hfloor
  have hhi := (div_lt_iff₀ hL).mp hfloor'
  change (u i : ℝ) + (L : ℝ) * (k i : ℝ) + L₁ ≤ y i ∧
    y i < (u i : ℝ) + (L : ℝ) * (k i : ℝ) + (L : ℝ) - L₁
  constructor
  · linarith only [hlo, (hS y hy i).1]
  · have hboundary : a i + D + L₁ < (u i : ℝ) + (L : ℝ) * (k i : ℝ) + (L : ℝ) := by
      by_contra hn
      have hzlo : a i - L₁ < (((u i : ℕ) : ℤ) + (L : ℤ) * (k i + 1) : ℤ) := by
        push_cast
        dsimp only [k]
        nlinarith only [hhi]
      have hzhi : ((((u i : ℕ) : ℤ) + (L : ℤ) * (k i + 1) : ℤ) : ℝ) ≤ a i + D + L₁ := by
        push_cast
        linarith only [le_of_not_gt hn]
      apply hnone i
      apply Finset.mem_image.mpr
      refine ⟨((u i : ℕ) : ℤ) + (L : ℤ) * (k i + 1),
        Finset.mem_Ioc.mpr ⟨Int.floor_lt.mpr hzlo, Int.le_floor.mpr hzhi⟩, ?_⟩
      exact offsetResidue_boundary L (u i) (k i + 1)
    linarith only [hboundary, (hS y hy i).2]

/-- Restricting one coordinate of an offset vector costs the expected factor
`L^(m-1)` in its cardinality. -/
theorem card_coordinate_offsets_le {m : ℕ} (L : ℕ+) (i : Fin m)
    (B : Finset (Fin (L : ℕ))) :
    (Finset.univ.filter (fun u : Fin m → Fin (L : ℕ) => u i ∈ B)).card ≤
      B.card * (L : ℕ) ^ (m - 1) := by
  classical
  let U := Finset.univ.filter (fun u : Fin m → Fin (L : ℕ) => u i ∈ B)
  let F : U → B × ({j : Fin m // j ≠ i} → Fin (L : ℕ)) :=
    fun u => (⟨u.1 i, (Finset.mem_filter.mp u.2).2⟩, fun j => u.1 j)
  have hF : Function.Injective F := by
    intro u v h
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      exact congrArg (fun p => p.1.1) h
    · exact congrArg (fun p => p.2 ⟨j, hji⟩) h
  have hc := Fintype.card_le_of_injective F hF
  have hdim : Fintype.card {j : Fin m // j ≠ i} = m - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hdim] using hc

/-- The explicit random-offset count: at most `m(D+2L₁+2)L^(m-1)` offsets
fail to place a set in one core. -/
theorem card_badOffsets_le {m : ℕ} (L : ℕ+) {L₁ D : ℝ}
    (hL₁ : 0 ≤ L₁) (hD : 0 ≤ D) (a : Fin m → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS : ∀ y ∈ S, ∀ i, a i ≤ y i ∧ y i ≤ a i + D) :
    ((badOffsets L L₁ S).card : ℝ) ≤
      (m : ℝ) * (D + 2 * L₁ + 2) * (L : ℝ) ^ (m - 1) := by
  classical
  have hsub := badOffsets_subset_boundary_union (L₁ := L₁) L a S hS
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcoord (i : Fin m) :
      ((Finset.univ.filter (fun u : Fin m → Fin (L : ℕ) =>
        u i ∈ boundaryOffsets L (a i - L₁) (a i + D + L₁))).card : ℝ) ≤
          (D + 2 * L₁ + 2) * (L : ℝ) ^ (m - 1) := by
    have hbound := card_boundaryOffsets_le L
      (by linarith only [hD, hL₁] : a i - L₁ ≤ a i + D + L₁)
    have h := card_coordinate_offsets_le L i (boundaryOffsets L (a i - L₁) (a i + D + L₁))
    have hcast : ((Finset.univ.filter (fun u : Fin m → Fin (L : ℕ) =>
        u i ∈ boundaryOffsets L (a i - L₁) (a i + D + L₁))).card : ℝ) ≤
          ((boundaryOffsets L (a i - L₁) (a i + D + L₁)).card : ℝ) * (L : ℝ) ^ (m - 1) := by
      exact_mod_cast h
    refine hcast.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith only [hbound]
  calc
    _ ≤ ∑ i : Fin m, ((Finset.univ.filter (fun u : Fin m → Fin (L : ℕ) =>
        u i ∈ boundaryOffsets L (a i - L₁) (a i + D + L₁))).card : ℝ) := by exact_mod_cast hc
    _ ≤ ∑ _i : Fin m, (D + 2 * L₁ + 2) * (L : ℝ) ^ (m - 1) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The same estimate for the normalized counting law on offset vectors. -/
theorem badOffsets_probability_le {m : ℕ} (L : ℕ+) {L₁ D : ℝ}
    (hL₁ : 0 ≤ L₁) (hD : 0 ≤ D) (a : Fin m → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hS : ∀ y ∈ S, ∀ i, a i ≤ y i ∧ y i ≤ a i + D) :
    ((badOffsets L L₁ S).card : ℝ) / (Fintype.card (Fin m → Fin (L : ℕ)) : ℝ) ≤
      (m : ℝ) * (D + 2 * L₁ + 2) / (L : ℝ) := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast L.pos
  have hc := card_badOffsets_le L hL₁ hD a S hS
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at *
  by_cases hm : m = 0
  · subst m
    simpa only [Nat.cast_zero, zero_mul, pow_zero, div_one, zero_div] using hc
  · have hm' : m = (m - 1) + 1 := by omega
    apply (div_le_div_iff₀ (by positivity : 0 < (L : ℝ) ^ m) hL).mpr
    have hpow : (L : ℝ) ^ m = (L : ℝ) ^ (m - 1) * (L : ℝ) := by
      conv_lhs => rw [hm']
      rw [pow_succ]
    rw [hpow]
    nlinarith only [mul_le_mul_of_nonneg_right hc hL.le]

end IsotropicVariance.Paper.Proofs.LabelResidual.OffsetGeometry
