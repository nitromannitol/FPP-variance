/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.BridgeInfo
public import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Conditional expectations given independent information

Three generic measure-theoretic lemmas, used in the proof of Lemma `lem:blocks`.

* `indep_aeClosure_left`: independence passes to the almost sure closure.
* `indep_sup_left_of_indep`: if `a` is independent of `b ⊔ c` and `b` of `c`, then `a ⊔ b` is
  independent of `c`.
* `exists_setLIntegral_eq_of_indep`: a conditional expectation (of a nonnegative function) given
  `a` is also one given `a ⊔ c` when `c` is independent of the rest.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.BlockReplacement

open Gain.Bridge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Independence passes to the almost sure closure of the first σ-algebra. -/
theorem indep_aeClosure_left {m₁ m₂ : MeasurableSpace Ω} (h : Indep m₁ m₂ P) :
    Indep (aeClosure m₁ P) m₂ P := by
  rw [Indep_iff] at h ⊢
  intro t1 t2 ht1 ht2
  obtain ⟨t, ht, hte⟩ := (measurableSet_aeClosure_iff).1 ht1
  rw [measure_congr (hte.inter EventuallyEq.rfl), measure_congr hte]
  exact h t t2 ht ht2

/-- If `a` is independent of `b ⊔ c` and `b` of `c`, then `a ⊔ b` is independent of `c`. -/
theorem indep_sup_left_of_indep [IsProbabilityMeasure P] {a b c : MeasurableSpace Ω}
    (ha : a ≤ mΩ) (hb : b ≤ mΩ) (hc : c ≤ mΩ) (h₁ : Indep a (b ⊔ c) P) (h₂ : Indep b c P) :
    Indep (a ⊔ b) c P := by
  let p : Set (Set Ω) := {s | ∃ u v, MeasurableSet[a] u ∧ MeasurableSet[b] v ∧ s = u ∩ v}
  have hp : IsPiSystem p := by
    rintro _ ⟨u, v, hu, hv, rfl⟩ _ ⟨u', v', hu', hv', rfl⟩ _
    refine ⟨u ∩ u', v ∩ v', hu.inter hu', hv.inter hv', ?_⟩
    ext x; simp only [mem_inter_iff]; tauto
  have hgen : a ⊔ b = MeasurableSpace.generateFrom p := by
    apply le_antisymm
    · refine sup_le (fun s hs => ?_) (fun s hs => ?_)
      · exact MeasurableSpace.measurableSet_generateFrom ⟨s, univ, hs, MeasurableSet.univ, by simp⟩
      · exact MeasurableSpace.measurableSet_generateFrom ⟨univ, s, MeasurableSet.univ, hs, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨u, v, hu, hv, rfl⟩
      exact (le_sup_left (a := a) (b := b) _ hu).inter (le_sup_right (a := a) (b := b) _ hv)
  refine IndepSets.indep (sup_le ha hb) hc hp (@MeasurableSpace.isPiSystem_measurableSet _ c)
    hgen (@MeasurableSpace.generateFrom_measurableSet _ c).symm ?_
  rw [IndepSets_iff]
  rintro _ w ⟨u, v, hu, hv, rfl⟩ hw
  have hv' : MeasurableSet[b ⊔ c] v := le_sup_left (a := b) (b := c) _ hv
  have hw' : MeasurableSet[b ⊔ c] w := le_sup_right (a := b) (b := c) _ hw
  have e1 : P (u ∩ v ∩ w) = P u * P (v ∩ w) := by
    rw [inter_assoc]; exact ((Indep_iff _ _ _).1 h₁) u (v ∩ w) hu (hv'.inter hw')
  rw [e1, ((Indep_iff _ _ _).1 h₂) v w hv hw, ((Indep_iff _ _ _).1 h₁) u v hu hv', mul_assoc]

section Cond

variable {Ω' E : Type*} [mΩ' : MeasurableSpace Ω'] [mE : MeasurableSpace E]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {Q : Measure E} [IsProbabilityMeasure Q]
  {old : Ω' → E}

private theorem setLIntegral_inter_of_indep {Ω : Type*} [m0 : MeasurableSpace Ω]
    {M1 M2 : MeasurableSpace Ω}
    {μ : @Measure Ω m0} (h1 : M1 ≤ m0) (h2 : M2 ≤ m0) (hind : Indep M1 M2 μ) {u w : Set Ω}
    (hu : MeasurableSet[M1] u) (hw : MeasurableSet[M2] w) {f : Ω → ℝ≥0∞}
    (hf : Measurable[M1] f) :
    ∫⁻ x in u ∩ w, f x ∂μ = (∫⁻ x in u, f x ∂μ) * μ w := by
  have hu0 := h1 _ hu
  have hw0 := h2 _ hw
  have e : ∀ x, (u ∩ w).indicator f x = u.indicator f x * w.indicator 1 x := by
    intro x
    by_cases hxu : x ∈ u <;> by_cases hxw : x ∈ w <;> simp [hxu, hxw, indicator]
  rw [← lintegral_indicator (hu0.inter hw0), ← lintegral_indicator hu0]
  simp_rw [e]
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace h1 h2 hind
    (hf.indicator hu) (f := u.indicator f) (g := w.indicator 1) (measurable_const.indicator hw)
  rw [this, lintegral_indicator_one hw0]

omit [IsProbabilityMeasure P'] [IsProbabilityMeasure Q] in
private theorem aux_measurable (hold : MeasurePreserving old P' Q) : Measurable old :=
  hold.measurable

omit [IsProbabilityMeasure P'] [IsProbabilityMeasure Q] in
private theorem aux_preimage (hold : MeasurePreserving old P' Q) {s : Set E}
    (hs : MeasurableSet s) : P' (old ⁻¹' s) = Q s :=
  hold.measure_preimage hs.nullMeasurableSet

omit [IsProbabilityMeasure P'] in
/-- A conditional expectation given `a` that is also one given `a ⊔ c`: if `old` is measure
preserving, `a` and `c` are independent, `g` is measurable for a σ-algebra `𝒜` containing the
pullback of `a` and independent of the pullback of `c`, then there is an `a`-measurable `φ` whose
integrals over sets of `a ⊔ c` agree with those of `g` over their preimages. -/
theorem exists_setLIntegral_eq_of_indep (hold : MeasurePreserving old P' Q)
    {a c : MeasurableSpace E} (ha : a ≤ mE) (hc : c ≤ mE) (hac : Indep a c Q)
    {𝒜 : MeasurableSpace Ω'} (h𝒜 : 𝒜 ≤ mΩ') (ha𝒜 : a.comap old ≤ 𝒜)
    (hind : Indep 𝒜 (c.comap old) P') {g : Ω' → ℝ≥0∞} (hg : Measurable[𝒜] g)
    (hfin : ∫⁻ ω, g ω ∂P' ≠ ∞) :
    ∃ φ : E → ℝ≥0∞, Measurable[a] φ ∧ ∀ A : Set E, MeasurableSet[a ⊔ c] A →
      ∫⁻ x in A, φ x ∂Q = ∫⁻ ω in old ⁻¹' A, g ω ∂P' := by
  have hom : Measurable[mΩ', mE] old := aux_measurable (mΩ' := mΩ') (mE := mE) hold
  have hg0 : Measurable[mΩ'] g := Measurable.mono hg h𝒜 le_rfl
  set μ2 : @Measure E mE := @Measure.map _ _ mΩ' mE old (@Measure.withDensity _ mΩ' P' g) with hμ2
  have hμ2A : ∀ A, MeasurableSet[mE] A → μ2 A = ∫⁻ ω in old ⁻¹' A, g ω ∂P' := by
    intro A hA
    rw [hμ2, Measure.map_apply hom hA, withDensity_apply _ (hom hA)]
  have hμ2fin : IsFiniteMeasure μ2 := by
    refine ⟨?_⟩
    rw [hμ2A _ MeasurableSet.univ]
    simp only [preimage_univ, Measure.restrict_univ]
    exact lt_top_iff_ne_top.2 hfin
  have : IsFiniteMeasure (μ2.trim ha) := isFiniteMeasure_trim ha
  have : IsFiniteMeasure (Q.trim ha) := isFiniteMeasure_trim ha
  have hac' : μ2.trim ha ≪ Q.trim ha := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
    rw [trim_measurableSet_eq ha hs] at hs0 ⊢
    rw [hμ2A _ (ha _ hs)]
    have : P' (old ⁻¹' s) = 0 := by
      rw [aux_preimage (mΩ' := mΩ') (mE := mE) hold (ha _ hs)]; exact hs0
    exact setLIntegral_measure_zero _ _ this
  set φ : E → ℝ≥0∞ := (μ2.trim ha).rnDeriv (Q.trim ha) with hφ
  have hφa : Measurable[a] φ := Measure.measurable_rnDeriv _ _
  have step1 : ∀ A, MeasurableSet[a] A → ∫⁻ x in A, φ x ∂Q = μ2 A := by
    intro A hA
    have h1 := Measure.setLIntegral_rnDeriv hac' A
    rw [← setLIntegral_trim ha hφa hA]
    rw [hφ, h1, trim_measurableSet_eq ha hA]
  refine ⟨φ, hφa, fun A hA => ?_⟩
  have hle : a ⊔ c ≤ mE := sup_le ha hc
  have hA0 : MeasurableSet[mE] A := hle _ hA
  rw [← hμ2A _ hA0]
  set ρ : @Measure E mE := Q.withDensity φ with hρ
  have hρA : ∀ A, MeasurableSet[mE] A → ρ A = ∫⁻ x in A, φ x ∂Q := fun A hA =>
    withDensity_apply _ hA
  have hρfin : IsFiniteMeasure ρ := by
    refine ⟨?_⟩
    rw [hρA _ MeasurableSet.univ, step1 _ (@MeasurableSet.univ _ a)]
    exact hμ2fin.measure_univ_lt_top
  have : IsFiniteMeasure (ρ.trim hle) := isFiniteMeasure_trim hle
  have : IsFiniteMeasure (μ2.trim hle) := isFiniteMeasure_trim hle
  have key : ρ.trim hle = μ2.trim hle := by
    let p : Set (Set E) := {s | ∃ u w, MeasurableSet[a] u ∧ MeasurableSet[c] w ∧ s = u ∩ w}
    have hp : IsPiSystem p := by
      rintro _ ⟨u, v, hu, hv, rfl⟩ _ ⟨u', v', hu', hv', rfl⟩ _
      refine ⟨u ∩ u', v ∩ v', hu.inter hu', hv.inter hv', ?_⟩
      ext x; simp only [mem_inter_iff]; tauto
    have hgen : a ⊔ c = MeasurableSpace.generateFrom p := by
      apply le_antisymm
      · refine sup_le (fun s hs => ?_) (fun s hs => ?_)
        · exact MeasurableSpace.measurableSet_generateFrom
            ⟨s, univ, hs, MeasurableSet.univ, by simp⟩
        · exact MeasurableSpace.measurableSet_generateFrom
            ⟨univ, s, MeasurableSet.univ, hs, by simp⟩
      · refine MeasurableSpace.generateFrom_le ?_
        rintro _ ⟨u, v, hu, hv, rfl⟩
        exact (le_sup_left (a := a) (b := c) _ hu).inter (le_sup_right (a := a) (b := c) _ hv)
    refine MeasureTheory.ext_of_generate_finite (m0 := a ⊔ c) p hgen hp ?_ ?_
    · rintro _ ⟨u, w, hu, hw, rfl⟩
      have huw : MeasurableSet[mE] (u ∩ w) := (ha _ hu).inter (hc _ hw)
      have huw' : MeasurableSet[a ⊔ c] (u ∩ w) :=
        (le_sup_left (a := a) (b := c) _ hu).inter (le_sup_right (a := a) (b := c) _ hw)
      rw [trim_measurableSet_eq hle huw', trim_measurableSet_eq hle huw']
      rw [hρA _ huw, hμ2A _ huw, setLIntegral_inter_of_indep (m0 := mE) ha hc hac hu hw hφa, step1 u hu,
        preimage_inter, setLIntegral_inter_of_indep (m0 := mΩ') h𝒜 ((MeasurableSpace.comap_mono hc).trans hom.comap_le) hind
          (ha𝒜 _ ⟨u, hu, rfl⟩) ⟨w, hw, rfl⟩ hg, ← hμ2A _ (ha _ hu),
        ← aux_preimage (mΩ' := mΩ') (mE := mE) hold (hc _ hw)]
    · have hU : MeasurableSet[a ⊔ c] (univ : Set E) := MeasurableSet.univ
      rw [trim_measurableSet_eq hle hU, trim_measurableSet_eq hle hU, hρA _ MeasurableSet.univ,
        step1 _ (@MeasurableSet.univ _ a)]
  have := congrArg (fun m => m A) key
  simp only [trim_measurableSet_eq hle hA] at this
  rw [← hρA _ hA0]
  exact this

end Cond

end IsotropicVariance.Paper.Proofs.BlockReplacement
