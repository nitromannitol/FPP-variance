/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.ChainSum
public import IsotropicVariance.Paper.Proofs.SmallMean.MeanTools
public import IsotropicVariance.Paper.Proofs.SmallMean.PairBound
public import IsotropicVariance.Infra.Measurability.SlabVersion

/-!
# The arrays of Lemma `lem:smallmean`

For the chain of slabs `chainSlab s 0 i` and their continuous independent versions `V_i`
(`Infra.Slab.exists_iIndep_slabTime_versions`), the fluctuation of the pair of cubes
`I_i(j)`, `I_{i+1}(k)` is `X_i(j, k) = Q⁻¹ sup_n |V_i(q_n) − e_i(q_n)|` along a dense sequence of
the pair, where `e_i(u, v) = E D_i(u, v)`.

* `fluct`: the fluctuation as a measurable functional of the version (`measurable_fluct`).
* `iIndepFun_fluct_arrays`: the arrays, one function of each version, are independent over `i`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.SmallMean

open Infra.Slab

variable {m : ℕ}

/-- The normalized fluctuation of a field `V` around a mean `e` along a sequence `q`. -/
noncomputable def fluct (V e : Pt m × Pt m → ℝ) (q : ℕ → Pt m × Pt m) (Q : ℝ) : ℝ :=
  Q⁻¹ * ⨆ n, |V (q n) - e (q n)|

theorem fluct_nonneg (V e : Pt m × Pt m → ℝ) (q : ℕ → Pt m × Pt m) {Q : ℝ} (hQ : 0 ≤ Q) :
    0 ≤ fluct V e q Q :=
  mul_nonneg (inv_nonneg.2 hQ) (Real.iSup_nonneg fun _ => abs_nonneg _)

/-- The fluctuation is a measurable functional of the field. -/
theorem measurable_fluct (e : Pt m × Pt m → ℝ) (q : ℕ → Pt m × Pt m) (Q : ℝ) :
    Measurable fun V : Pt m × Pt m → ℝ => fluct V e q Q := by
  refine (Measurable.iSup fun n => ?_).const_mul _
  exact continuous_abs.measurable.comp ((measurable_pi_apply (q n)).sub_const _)

/-- A continuous field is bounded by its fluctuation on a compact pair containing the
sequence densely, when the mean is continuous there. -/
theorem abs_sub_le_mul_fluct {V e : Pt m × Pt m → ℝ} {S : Set (Pt m × Pt m)}
    (hS : IsCompact S) (hV : Continuous V) (he : ContinuousOn e S) {q : ℕ → Pt m × Pt m}
    (hq : ∀ n, q n ∈ S) (hdense : S ⊆ closure (range q)) {Q : ℝ} (hQ : 0 < Q) {x : Pt m × Pt m}
    (hx : x ∈ S) : |V x - e x| ≤ Q * fluct V e q Q := by
  have hf : ContinuousOn (fun y => |V y - e y|) S := (hV.continuousOn.sub he).abs
  obtain ⟨B, hB⟩ := hS.bddAbove_image hf
  have hb : BddAbove (range fun n => |V (q n) - e (q n)|) :=
    ⟨B, by rintro _ ⟨n, rfl⟩; exact hB ⟨q n, hq n, rfl⟩⟩
  have hcl : IsClosed (S ∩ {y | |V y - e y| ≤ ⨆ n, |V (q n) - e (q n)|}) :=
    hf.preimage_isClosed_of_isClosed hS.isClosed isClosed_Iic
  have hsub : range q ⊆ S ∩ {y | |V y - e y| ≤ ⨆ n, |V (q n) - e (q n)|} := by
    rintro _ ⟨n, rfl⟩
    exact ⟨hq n, le_ciSup hb n⟩
  have hx' := (hcl.closure_subset_iff.mpr hsub) (hdense hx)
  rw [fluct, ← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul]
  exact hx'.2

/-- **Independence of the arrays**: functions of independent versions, one for each slab. -/
theorem iIndepFun_fluct_arrays {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : ℕ}
    {V : Fin M → Ω → Pt m × Pt m → ℝ} (hV : iIndepFun (fun i ω => V i ω) P)
    (g : Fin M → (Pt m × Pt m → ℝ) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ)
    (hg : ∀ i j k, Measurable fun F => g i F j k) :
    iIndepFun (fun i ω => g i (V i ω)) P := by
  have hgm : ∀ i, Measurable (g i) := fun i =>
    measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => hg i j k
  exact hV.comp (fun i => g i) hgm

end IsotropicVariance.Paper.Proofs.SmallMean
