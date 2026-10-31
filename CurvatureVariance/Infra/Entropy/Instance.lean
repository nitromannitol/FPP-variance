/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Entropy.FiniteCoordinates

/-!
# The Benaïm–Rossignol instance with centered-difference operators

[BR, Proposition 2.1, pp. 546–547], specialized to finite coordinate value spaces and the operators
`R_i = √c (Id − E_i)`, as used in the proof of Proposition `prop:gain` (through
[AB26, Proposition 1.3]). The partial-integration commutation is proved by Fubini; there is no
abstract domain-stability or commutation premise in the exported instance.
-/

@[expose] public section

open MeasureTheory Real

namespace CurvatureVariance.Infra.Entropy

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- Centered coordinate differences commute with every partial coordinate average.
This verifies the commutation in BR Proposition 2.1, including the partial averages used by
its martingale proof; no abstract domain-stability or commutation hypothesis is needed. -/
theorem extendCoord_scaledDiff_integrateOut (c : ℝ) (i : ι) (T : Set ι)
    {g : (∀ j, X j) → ℝ} (hgm : Measurable g) (hgi : Integrable g (Measure.infinitePi μ)) :
    extendCoord i (scaledDiff μ c i) (integrateOut μ T g) =ᵐ[Measure.infinitePi μ]
      integrateOut μ T (extendCoord i (scaledDiff μ c i) g) := by
  have hRg : extendCoord i (scaledDiff μ c i) g = fun x => c * (g x - coordAvg μ i g x) :=
    funext fun x => extendCoord_scaledDiff c i g x
  have hRTg : extendCoord i (scaledDiff μ c i) (integrateOut μ T g) =
      fun x => c * (integrateOut μ T g x - coordAvg μ i (integrateOut μ T g) x) :=
    funext fun x => extendCoord_scaledDiff c i _ x
  rw [hRg, hRTg]
  filter_upwards [coordAvg_integrateOut (μ := μ) (T := T) i hgm hgi,
    integrateOut_sub_ae (T := T) hgi (integrable_coordAvg i hgi)] with x h1 h2
  rw [h1]
  simp only [integrateOut, integral_const_mul] at h2 ⊢
  rw [h2]

/-- BR Proposition 2.1 for the paper's centered-difference operators on countably many
finite value spaces, with any prescribed uniform coordinate logarithmic Sobolev constant.
Its complementary/partial-integration commutation is proved, rather than assumed.
Atoms of mass zero are allowed. No uniform atom lower bound is required if the LSI is given. -/
theorem variance_mul_log_le_of_finite_coordinate_lsi [Countable ι]
    {L : ℝ} (hL : 0 ≤ L)
    (hLSI : ∀ i (g : X i → ℝ), eentropy (μ i) (fun y => g y ^ 2) ≤
      ENNReal.ofReal (L * ∫ y, (g y - ∫ z, g z ∂μ i) ^ 2 ∂μ i))
    {f : (∀ j, X j) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (Measure.infinitePi μ))
    (hA : Summable fun i => ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ) :
    ProbabilityTheory.variance f (Measure.infinitePi μ) *
      log (ProbabilityTheory.variance f (Measure.infinitePi μ) /
        ∑' i, (∫ x, |coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
      L * ∑' i, ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ := by
  let c := Real.sqrt L
  have hc2 : c ^ 2 = L := Real.sq_sqrt hL
  let R : ∀ i, (X i → ℝ) →ₗ[ℝ] (X i → ℝ) := fun i => scaledDiff μ c i
  let A : ∀ i, Submodule ℝ (X i → ℝ) := fun _ => ⊤
  have hRf : ∀ i, extendCoord i (R i) f = fun x => c * coordDiff μ i f x :=
    fun i => funext fun x => extendCoord_scaledDiff c i f x
  have hRconst : ∀ i (a : ℝ), R i (fun _ => a) =ᵐ[μ i] 0 := by
    intro i a
    exact ae_of_all _ fun y => by simp [R, scaledDiff_apply]
  have hlocal : ∀ i, ∀ g ∈ A i, eentropy (μ i) (fun y => g y ^ 2) ≤
      ENNReal.ofReal (∫ y, R i g y ^ 2 ∂μ i) := by
    intro i g _
    convert hLSI i g using 1
    simp only [R, scaledDiff_apply, mul_pow, hc2, integral_const_mul]
  have hcomm : ∀ i, ∀ g ∈ productDomain μ A, ∀ T : Set ι, i ∉ T →
      integrateOut μ T g ∈ productDomain μ A ∧
        extendCoord i (R i) (integrateOut μ T g) =ᵐ[Measure.infinitePi μ]
          integrateOut μ T (extendCoord i (R i) g) := by
    intro i g hg T _
    exact ⟨⟨measurable_integrateOut hg.1, memLp_integrateOut hg.2.1,
      fun j => ae_of_all _ fun x => Submodule.mem_top⟩,
      extendCoord_scaledDiff_integrateOut (μ := μ) c i T hg.1 (hg.2.1.integrable one_le_two)⟩
  have hfD : f ∈ productDomain μ A := ⟨hfm, hf, fun j => ae_of_all _ fun x => Submodule.mem_top⟩
  have hR2 : ∀ i, MemLp (extendCoord i (R i) f) 2 (Measure.infinitePi μ) := fun i => by
    rw [hRf]; exact (memLp_coordDiff i hf).const_mul c
  have hRsq : ∀ i, ∫ x, extendCoord i (R i) f x ^ 2 ∂Measure.infinitePi μ =
      L * ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ := by
    intro i
    rw [hRf, ← integral_const_mul]
    congr 1; funext x; rw [mul_pow, hc2]
  have hRsum : Summable fun i => ∫ x, extendCoord i (R i) f x ^ 2 ∂Measure.infinitePi μ := by
    simp_rw [hRsq]; exact hA.mul_left L
  have hBR := variance_mul_log_le_of_logSobolev A R (fun i g _ => MemLp.of_discrete)
    (fun i a => Submodule.mem_top) (fun i g _ => MemLp.of_discrete) hRconst hlocal hcomm f hfD
    hR2 hRsum
  rwa [tsum_congr hRsq, tsum_mul_left] at hBR

/-- BR's applied instance with the ordinary entropy/variance coordinate premise. Its constant is
the supplied `c`, with no extra factor. -/
theorem br_instance_of_coordinate_lsi [Countable ι] {c : ℝ} (hc : 0 ≤ c)
    (hLSI : ∀ i (g : X i → ℝ), entropy (μ i) (fun y => g y ^ 2) ≤
      c * ProbabilityTheory.variance g (μ i))
    {f : (∀ j, X j) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (Measure.infinitePi μ))
    (hA : Summable fun i => ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ) :
    ProbabilityTheory.variance f (Measure.infinitePi μ) *
      log (ProbabilityTheory.variance f (Measure.infinitePi μ) /
        ∑' i, (∫ x, |coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
      c * ∑' i, ∫ x, coordDiff μ i f x ^ 2 ∂Measure.infinitePi μ := by
  apply variance_mul_log_le_of_finite_coordinate_lsi hc ?_ hfm hf hA
  intro i g
  rw [eentropy_eq_ofReal_entropy (ae_of_all _ fun y => sq_nonneg _) Integrable.of_finite
    Integrable.of_finite]
  have h := hLSI i g
  rw [ProbabilityTheory.variance_eq_integral (Measurable.of_discrete.aemeasurable)] at h
  exact ENNReal.ofReal_le_ofReal h

end CurvatureVariance.Infra.Entropy
