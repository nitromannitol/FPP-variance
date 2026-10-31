/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Minima on compact families and finite penalties -/

@[expose] public section
open Set MeasureTheory
open scoped Topology
namespace IsotropicVariance.Infra.Selection

/-- A nonempty compact constraint set. -/
structure CompactFamily (K : Type*) [TopologicalSpace K] where
  carrier : Set K
  isCompact : IsCompact carrier
  nonempty : carrier.Nonempty

namespace CompactFamily
variable {K : Type*} [TopologicalSpace K]

/-- The minimum value, defined independently of a continuity certificate. -/
noncomputable def minValue (S : CompactFamily K) (f : K → ℝ) : ℝ := sInf (f '' S.carrier)

/-- A minimizing point in a compact family. -/
noncomputable def minPoint (S : CompactFamily K) (f : K → ℝ) (hf : Continuous f) : K :=
  (S.isCompact.exists_isMinOn S.nonempty hf.continuousOn).choose

lemma minPoint_mem (S : CompactFamily K) (f : K → ℝ) (hf : Continuous f) :
    S.minPoint f hf ∈ S.carrier :=
  (S.isCompact.exists_isMinOn S.nonempty hf.continuousOn).choose_spec.1

lemma minPoint_le (S : CompactFamily K) (f : K → ℝ) (hf : Continuous f)
    {x : K} (hx : x ∈ S.carrier) : f (S.minPoint f hf) ≤ f x :=
  (S.isCompact.exists_isMinOn S.nonempty hf.continuousOn).choose_spec.2 hx

lemma minValue_eq (S : CompactFamily K) (f : K → ℝ) (hf : Continuous f) :
    S.minValue f = f (S.minPoint f hf) := by
  apply IsLeast.csInf_eq
  exact ⟨⟨_, S.minPoint_mem f hf, rfl⟩, by
    rintro _ ⟨x, hx, rfl⟩; exact S.minPoint_le f hf hx⟩

lemma minValue_le (S : CompactFamily K) (f : K → ℝ) (hf : Continuous f)
    {x : K} (hx : x ∈ S.carrier) : S.minValue f ≤ f x := by
  rw [S.minValue_eq f hf]; exact S.minPoint_le f hf hx

/-- Retaining precisely the minimizers is again a nonempty compact constraint. -/
noncomputable def argmin (S : CompactFamily K) (f : K → ℝ) (hf : Continuous f) :
    CompactFamily K where
  carrier := {x ∈ S.carrier | f x = S.minValue f}
  isCompact := S.isCompact.inter_right (isClosed_eq hf continuous_const)
  nonempty := ⟨S.minPoint f hf, S.minPoint_mem f hf, (S.minValue_eq f hf).symm⟩

/-- The whole compact space as a constraint. -/
def whole (K : Type*) [TopologicalSpace K] [CompactSpace K] [Nonempty K] : CompactFamily K :=
  ⟨univ, isCompact_univ, univ_nonempty⟩

/-- A zero constraint is recovered by integer penalties, without any uniqueness assumption. -/
lemma minValue_zero_penalty [CompactSpace K] [Nonempty K]
    (g h : K → ℝ) (hg : Continuous g) (hh : Continuous h) (hpos : ∀ x, 0 ≤ g x)
    (S : CompactFamily K) (hS : S.carrier = {x | g x = 0}) :
    S.minValue h = ⨆ n : ℕ, (whole K).minValue (fun x => h x + n * g x) := by
  let a : ℕ → ℝ := fun n => (whole K).minValue (fun x => h x + n * g x)
  have hc (n : ℕ) : Continuous (fun x => h x + n * g x) := by fun_prop
  let x := S.minPoint h hh
  have hx : g x = 0 := by simpa [hS] using S.minPoint_mem h hh
  have ha (n : ℕ) : a n ≤ S.minValue h := by
    have H := (whole K).minValue_le _ (hc n) (mem_univ x)
    simpa [a, hx, S.minValue_eq h hh, x] using H
  have hb : BddAbove (range a) := ⟨S.minValue h, by rintro _ ⟨n, rfl⟩; exact ha n⟩
  apply le_antisymm
  · apply le_of_forall_lt
    intro r hr
    let U : ℕ → Set K := fun n => {x | r < h x + n * g x}
    have hcover : (univ : Set K) ⊆ ⋃ n, U n := by
      intro y _
      by_cases hy : g y = 0
      · have hyS : y ∈ S.carrier := by simpa [hS]
        exact mem_iUnion.mpr ⟨0, by
          change r < h y + (0 : ℕ) * g y
          simpa using hr.trans_le (S.minValue_le h hh hyS)⟩
      · have hgy : 0 < g y := lt_of_le_of_ne (hpos y) (Ne.symm hy)
        obtain ⟨n, hn⟩ := exists_nat_gt ((r - h y) / g y)
        refine mem_iUnion.mpr ⟨n, ?_⟩
        change r < h y + n * g y
        have := (div_lt_iff₀ hgy).mp hn
        linarith
    have hdir : Directed (· ⊆ ·) U := by
      intro n m
      refine ⟨max n m, ?_, ?_⟩
      · intro y hy
        change r < h y + (n : ℝ) * g y at hy
        change r < h y + (max n m : ℕ) * g y
        exact hy.trans_le (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (show (n : ℝ) ≤ (max n m : ℕ) by exact_mod_cast le_max_left n m) (hpos y)))
      · intro y hy
        change r < h y + (m : ℝ) * g y at hy
        change r < h y + (max n m : ℕ) * g y
        exact hy.trans_le (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (show (m : ℝ) ≤ (max n m : ℕ) by exact_mod_cast le_max_right n m) (hpos y)))
    obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover U
      (fun n => isOpen_lt continuous_const (hc n)) hcover hdir
    have H := hn (mem_univ ((whole K).minPoint _ (hc n)))
    change r < h _ + n * g _ at H
    have H' : r < a n := by
      change r < (whole K).minValue _
      rw [(whole K).minValue_eq _ (hc n)]
      exact H
    exact H'.trans_le (le_ciSup hb n)
  · exact ciSup_le ha

end CompactFamily
end IsotropicVariance.Infra.Selection
