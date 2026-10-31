/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.RRReplacement
public import CurvatureVariance.Paper.Proofs.Gain.Step2Offsets
public import CurvatureVariance.Paper.Proofs.Gain.AVLabels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The block sum on the good event

The step off the event `E` in the second paragraph of [AB26, proof of Lemma 6.3], which the proof of
Lemma `lem:residual` follows: only one block contributes to `Y_i(j,k)`, and its label takes the same
value at the old and the new weights. Deterministic form (`rewardSum_le_of_subset_subIndices`): let
`S` be a set of fine-cube indices containing the fine cubes of the edges of every old slab geodesic
between the row cubes and the fine cubes of the points of the row cubes, and let `S` lie in the
subcube index set `subIndices L o g₀` of one block `g₀` (the good event). If the new weights of
every block agree with the old ones off the block, the old and new normalized slab passage times on
the subcube faces of `g₀` are within `X(old)`, `X(new)` of a label, and the label takes the same
value at the old and new weights, then the block sum is at most `(X(new) + X(old))²`.
-/
@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- The subcube indices of a block are indices of the block. -/
theorem subIndices_subset_blockIndices (L : ℕ) (o g : Fin m → ℤ) :
    subIndices L o g ⊆ blockIndices L o g := by
  intro j hj c
  obtain ⟨h1, h2⟩ := hj c
  have h0 : (0 : ℤ) ≤ (⌈Real.sqrt L⌉₊ : ℤ) := Int.natCast_nonneg _
  constructor <;> linarith

/-- Blocks other than `g₀` miss a set of indices inside the subcube indices of `g₀`. -/
theorem disjoint_blockIndices_of_subset_subIndices {L : ℕ} (hL : 1 ≤ L) {o g₀ g : Fin m → ℤ}
    {S : Set (Fin m → ℤ)} (hS : S ⊆ subIndices L o g₀) (hg : g ≠ g₀) :
    Disjoint (blockIndices L o g) S := by
  refine Set.disjoint_left.2 fun j' hj'g hj'S => hg ?_
  have h1 := (mem_blockIndices_iff_blockOf_eq hL o g j').1 hj'g
  have h2 := (mem_blockIndices_iff_blockOf_eq hL o g₀ j').1
    (subIndices_subset_blockIndices L o g₀ (hS hj'S))
  rw [← h1, h2]

/-- **The block sum on the good event** (in the proof of Lemma `lem:residual`). -/
theorem rewardSum_le_of_subset_subIndices {M : Model m} {K : ℕ} {A : ℝ} {n L : ℕ}
    (hL : 1 ≤ L) {t : EuclideanSpace ℝ (Fin m)} {P : Pt m} {Ω : Type*} {old : Ω → Config m}
    {new : ℕ → (Fin m → ℤ) → Ω → Config m} {i : ℕ} {o j k g₀ : Fin m → ℤ}
    (hQ : 0 < Q M K A n) (hw : 0 < wInt M K A n) {ω : Ω} {S : Set (Fin m → ℤ)}
    {lam : Config m → Vertex m → Vertex m → ℝ} {X : Config m → ℝ}
    (hagree : ∀ g (e : Edge m), e.1 ∉ block n (wInt M K A n) L t i o g → new i g ω e = old ω e)
    (hgeo : ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j,
      ∀ v ∈ rowCube n (wInt M K A n) t i k, ∃ γ : (latticeGraph m).Walk u v,
        IsSlabGeodesic (old ω) (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ)
    (htube : ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j,
      ∀ v ∈ rowCube n (wInt M K A n) t i k, ∀ γ : (latticeGraph m).Walk u v,
        IsSlabGeodesic (old ω) (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
        ∀ e ∈ γ.edges, fineIndex (wInt M K A n) t (edgeMid e) ∈ S)
    (hrowj : ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j,
      fineIndex (wInt M K A n) t (point u) ∈ S)
    (hrowk : ∀ v ∈ rowCube n (wInt M K A n) t i k,
      fineIndex (wInt M K A n) t (point v) ∈ S)
    (hS : S ⊆ subIndices L o g₀)
    (hXold : ∀ u ∈ subcubeFace (wInt M K A n) L t o g₀ (((i : ℤ) - 1) * n),
      ∀ v ∈ subcubeFace (wInt M K A n) L t o g₀ ((i : ℤ) * n),
        |normSlabTime M K A (old ω) n P i u v - lam (old ω) u v| ≤ X (old ω))
    (hXnew : ∀ u ∈ subcubeFace (wInt M K A n) L t o g₀ (((i : ℤ) - 1) * n),
      ∀ v ∈ subcubeFace (wInt M K A n) L t o g₀ ((i : ℤ) * n),
        |normSlabTime M K A (new i g₀ ω) n P i u v - lam (new i g₀ ω) u v| ≤
          X (new i g₀ ω))
    (hlab : lam (new i g₀ ω) = lam (old ω)) :
    rewardSum M K A n t old new i j k ω ≤
      (ENNReal.ofReal (X (new i g₀ ω)) + ENNReal.ofReal (X (old ω))) ^ 2 := by
  set w := wInt M K A n
  set I := rowCube n w t ((i : ℤ) - 1) j
  set I' := rowCube n w t i k
  -- only the block `g₀` contributes
  have hzero : ∀ g, g ≠ g₀ → blockSup n i I I' (old ω) (new i g ω) = 0 := fun g hg =>
    blockSup_eq_zero_of_disjoint hgeo htube (disjoint_blockIndices_of_subset_subIndices hL hS hg)
      (hagree g)
  rw [rewardSum_eq, tsum_eq_single g₀ fun g hg => by rw [hzero g hg]; simp]
  -- the block `g₀`: both passage times are within `Q X` of `P·(v − u) + Q λ`
  set c : Vertex m → Vertex m → ℝ := fun u v =>
    inner ℝ P (point v - point u) + Q M K A n * lam (old ω) u v with hc
  have hface : ∀ (u : Vertex m) (h : ℤ), u.1 = h →
      fineIndex w t (point u) ∈ S → u ∈ subcubeFace w L t o g₀ h := by
    intro u h hu hS'
    have := mem_subcubeFace_of_fineIndex_mem hw (hS hS')
    rwa [hu] at this
  have hdev : ∀ ω' : Config m, ∀ u v,
      |normSlabTime M K A ω' n P i u v - lam (old ω) u v| ≤ X ω' →
      |slabTimeReal ω' (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - c u v| ≤ Q M K A n * X ω' := by
    intro ω' u v h
    have heq : slabTimeReal ω' (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - c u v =
        Q M K A n * (normSlabTime M K A ω' n P i u v - lam (old ω) u v) := by
      simp only [hc, normSlabTime]
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos hQ]
    exact mul_le_mul_of_nonneg_left h hQ.le
  have h1 : ∀ u ∈ I, ∀ v ∈ I',
      |slabTimeReal (old ω) (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - c u v| ≤
        Q M K A n * X (old ω) := fun u hu v hv =>
    hdev _ u v (hXold u (hface u _ hu.1 (hrowj u hu)) v (hface v _ hv.1 (hrowk v hv)))
  have h2 : ∀ u ∈ I, ∀ v ∈ I',
      |slabTimeReal (new i g₀ ω) (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - c u v| ≤
        Q M K A n * X (new i g₀ ω) := fun u hu v hv => by
    have h := hXnew u (hface u _ hu.1 (hrowj u hu)) v (hface v _ hv.1 (hrowk v hv))
    rw [hlab] at h
    exact hdev _ u v h
  have hb := blockSup_le_of_abs_sub_le hQ h1 h2
  have hQ2 : (ENNReal.ofReal (Q M K A n ^ 2))⁻¹ = (ENNReal.ofReal (Q M K A n))⁻¹ ^ 2 := by
    rw [ENNReal.ofReal_pow hQ.le, ENNReal.inv_pow]
  rw [hQ2, ← mul_pow]
  exact pow_le_pow_left₀ bot_le hb 2

end CurvatureVariance.Paper.Gain.LabelResidual
