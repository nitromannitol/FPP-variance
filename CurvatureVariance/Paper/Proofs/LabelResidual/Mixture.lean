/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Independent uniform offsets: the mixture over offset families

The proof of Lemma `lem:residual`, as the first paragraph of [AB26, proof of Lemma 6.3], takes the
offsets of the slabs random, uniform and independent, and independent of the weights given the
offsets.
Formally, for a family of probability measures `Pr σ` on a space `Ω`, indexed by the offset families
`σ : ι → S` (`ι` the slabs, `S` the finite set of offsets of one slab), the mixture
`offsetMixture Pr = |S|^{-|ι|} ∑_σ δ_σ ⊗ Pr σ` on `(ι → S) × Ω`.

* `lintegral_offsetMixture`: `∫ f d(offsetMixture Pr) = |S|^{-|ι|} ∑_σ ∫ f(σ, ·) d(Pr σ)`, for every
  `f` (no measurability needed, as `ω ↦ (σ, ω)` is a measurable embedding).
* `iIndepFun_offsetMixture`: if, for every `σ`, the slab variables `U i` are independent under
  `Pr σ`, and the law of `U i` under `Pr σ` depends only on `σ i`, then the pairs `(σ i, U i)` are
  independent under the mixture. This is what makes the arrays lemma applicable on average over
  the offsets.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper.Gain

variable {ι S Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace Ω]

/-- The mixture `|S|^{-|ι|} ∑_σ δ_σ ⊗ Pr σ` over the offset families `σ : ι → S`. -/
noncomputable def offsetMixture (Pr : (ι → S) → Measure Ω) : Measure ((ι → S) × Ω) :=
  ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹ • ∑ σ, (Measure.dirac σ).prod (Pr σ)

/-- **Integrals under the mixture** are averages over the offset families. -/
theorem lintegral_offsetMixture (Pr : (ι → S) → Measure Ω) [∀ σ, SFinite (Pr σ)] (f : (ι → S) × Ω → ℝ≥0∞) :
    ∫⁻ x, f x ∂offsetMixture Pr =
      ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹ * ∑ σ, ∫⁻ ω, f (σ, ω) ∂Pr σ := by
  unfold offsetMixture
  rw [lintegral_smul_measure, lintegral_finsetSum_measure, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Measure.dirac_prod, (measurableEmbedding_prodMk_left σ).lintegral_map]

omit [MeasurableSingletonClass S] in
/-- The measure of a measurable set under the mixture. -/
theorem offsetMixture_apply (Pr : (ι → S) → Measure Ω) [∀ σ, SFinite (Pr σ)] {E : Set ((ι → S) × Ω)}
    (hE : MeasurableSet E) :
    offsetMixture Pr E =
      ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹ * ∑ σ, Pr σ (Prod.mk σ ⁻¹' E) := by
  unfold offsetMixture
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hE]

omit [MeasurableSingletonClass S] in
/-- The mixture of probability measures is a probability measure. -/
theorem isProbabilityMeasure_offsetMixture [Nonempty S] (Pr : (ι → S) → Measure Ω)
    [∀ σ, IsProbabilityMeasure (Pr σ)] : IsProbabilityMeasure (offsetMixture Pr) := by
  constructor
  rw [offsetMixture_apply Pr MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)

section Independence

variable {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {Pr : (ι → S) → Measure Ω}
  [∀ σ, IsProbabilityMeasure (Pr σ)] {U : ∀ i, Ω → β i}

omit [MeasurableSingletonClass S] in
/-- The product formula for the measure of a cylinder under the mixture. -/
theorem offsetMixture_iInter (hU : ∀ i, Measurable (U i)) (hind : ∀ σ, iIndepFun U (Pr σ))
    (hloc : ∀ i σ σ', σ i = σ' i → (Pr σ).map (U i) = (Pr σ').map (U i))
    {B : ∀ i, Set (S × β i)} (hB : ∀ i, MeasurableSet (B i)) :
    offsetMixture Pr (⋂ i, (fun x : (ι → S) × Ω => (x.1 i, U i x.2)) ⁻¹' B i) =
      ∏ i, ((Fintype.card S : ℝ≥0∞)⁻¹ *
        ∑ s, ((Pr fun _ => s).map (U i)) (Prod.mk s ⁻¹' B i)) := by
  have hW : ∀ i, Measurable fun x : (ι → S) × Ω => (x.1 i, U i x.2) := fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((hU i).comp measurable_snd)
  rw [offsetMixture_apply Pr (MeasurableSet.iInter fun i => hW i (hB i))]
  have hsec : ∀ σ : ι → S, Prod.mk σ ⁻¹' (⋂ i, (fun x : (ι → S) × Ω => (x.1 i, U i x.2)) ⁻¹' B i)
      = ⋂ i, U i ⁻¹' (Prod.mk (σ i) ⁻¹' B i) := by
    intro σ
    ext ω
    simp
  have hprod : ∀ σ : ι → S, Pr σ (⋂ i, U i ⁻¹' (Prod.mk (σ i) ⁻¹' B i)) =
      ∏ i, ((Pr fun _ => σ i).map (U i)) (Prod.mk (σ i) ⁻¹' B i) := by
    intro σ
    have h := (hind σ).measure_inter_preimage_eq_mul Finset.univ
      (sets := fun i => Prod.mk (σ i) ⁻¹' B i) (fun i _ => measurable_prodMk_left (hB i))
    simp only [Finset.mem_univ, iInter_true] at h
    rw [h]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Measure.map_apply (hU i) (measurable_prodMk_left (hB i)), hloc i σ (fun _ => σ i) rfl]
  simp_rw [hsec, hprod]
  set g : ∀ i, S → ℝ≥0∞ := fun i s => ((Pr fun _ => s).map (U i)) (Prod.mk s ⁻¹' B i) with hg
  have hswap : ∑ σ : ι → S, ∏ i, g i (σ i) = ∏ i, ∑ s, g i s := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hc : ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹ = ∏ _i : ι, (Fintype.card S : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow, Finset.prod_const, Finset.card_univ]
  change ((Fintype.card (ι → S) : ℝ≥0∞))⁻¹ * ∑ σ : ι → S, ∏ i, g i (σ i) = _
  rw [hswap, hc, ← Finset.prod_mul_distrib]

omit [MeasurableSingletonClass S] in
/-- **Independence under the mixture** (in the proof of Lemma `lem:residual`, with
independent uniform offsets): if the slab variables `U i` are independent under each `Pr σ` and the
law of `U i` under `Pr σ` depends only on `σ i`, then the pairs `(σ i, U i)` are independent under
`offsetMixture Pr`. -/
theorem iIndepFun_offsetMixture [Nonempty S] (hU : ∀ i, Measurable (U i))
    (hind : ∀ σ, iIndepFun U (Pr σ))
    (hloc : ∀ i σ σ', σ i = σ' i → (Pr σ).map (U i) = (Pr σ').map (U i)) :
    iIndepFun (fun i (x : (ι → S) × Ω) => (x.1 i, U i x.2)) (offsetMixture Pr) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets hsets
  set m : ∀ i, Set (S × β i) → ℝ≥0∞ := fun i B => (Fintype.card S : ℝ≥0∞)⁻¹ *
    ∑ s, ((Pr fun _ => s).map (U i)) (Prod.mk s ⁻¹' B) with hm
  have hm_univ : ∀ i, m i univ = 1 := by
    intro i
    have : ∀ s : S, ((Pr fun _ => s).map (U i)) (Prod.mk s ⁻¹' (univ : Set (S × β i))) = 1 :=
      fun s => by
        rw [preimage_univ, Measure.map_apply (hU i) MeasurableSet.univ, preimage_univ,
          measure_univ]
    simp only [hm, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _)
  -- the cylinder over `T`
  set B : ∀ i, Set (S × β i) := fun i => if i ∈ T then sets i else univ with hB
  have hBm : ∀ i, MeasurableSet (B i) := fun i => by
    by_cases hi : i ∈ T
    · simp only [hB, hi, ite_true]; exact hsets i hi
    · simp only [hB, hi, ite_false]; exact MeasurableSet.univ
  have hinter : (⋂ i ∈ T, (fun x : (ι → S) × Ω => (x.1 i, U i x.2)) ⁻¹' sets i) =
      ⋂ i, (fun x : (ι → S) × Ω => (x.1 i, U i x.2)) ⁻¹' B i := by
    ext x
    simp only [mem_iInter, mem_preimage, hB]
    refine ⟨fun h i => ?_, fun h i hi => by simpa [hi] using h i⟩
    by_cases hi : i ∈ T
    · simpa [hi] using h i hi
    · simp [hi]
  rw [hinter, offsetMixture_iInter hU hind hloc hBm]
  change ∏ i, m i (B i) = _
  have hleft : ∏ i, m i (B i) = ∏ i ∈ T, m i (sets i) := by
    rw [← Finset.prod_subset (Finset.subset_univ T) (fun i _ hi => by simp [hB, hi, hm_univ])]
    exact Finset.prod_congr rfl fun i hi => by simp [hB, hi]
  rw [hleft]
  refine Finset.prod_congr rfl fun i hi => ?_
  -- the single cylinder
  set B' : ∀ i', Set (S × β i') := fun i' => if i' = i then sets i' else univ with hB'
  have hB'm : ∀ i', MeasurableSet (B' i') := fun i' => by
    by_cases h : i' = i
    · subst h; simp only [hB', ite_true]; exact hsets i' hi
    · simp only [hB', h, ite_false]; exact MeasurableSet.univ
  have hsingle : (fun x : (ι → S) × Ω => (x.1 i, U i x.2)) ⁻¹' sets i =
      ⋂ i', (fun x : (ι → S) × Ω => (x.1 i', U i' x.2)) ⁻¹' B' i' := by
    ext x
    simp only [mem_iInter, mem_preimage, hB']
    refine ⟨fun h i' => ?_, fun h => by simpa using h i⟩
    by_cases h' : i' = i
    · subst h'; simpa using h
    · simp [h']
  rw [hsingle, offsetMixture_iInter hU hind hloc hB'm]
  change m i (sets i) = ∏ i', m i' (B' i')
  rw [Finset.prod_eq_single i (fun i' _ h' => by simp [hB', h', hm_univ])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp [hB']

end Independence

end CurvatureVariance.Paper.Gain.LabelResidual
