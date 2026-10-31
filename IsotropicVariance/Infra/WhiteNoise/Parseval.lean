/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoise.Fourier
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Parseval's identity on a unit box

For a bounded measurable function supported in a unit box `∏ᵢ (aᵢ, aᵢ + 1]` (in orthonormal
coordinates), the squared Fourier coefficients sum to `∫ ψ²`. The proof transfers the statement
from the `L²` Fourier basis of `UnitAddTorus` in Mathlib.
-/

@[expose] public section

open MeasureTheory Set

namespace IsotropicVariance.Infra.WhiteNoise

section Torus

/-- The measure on the unit circle used by Mathlib's `UnitAddTorus` Fourier analysis (a local
instance there). -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- The periodization of `G`, viewed as a function on the torus through the box
`∏ᵢ (aᵢ, aᵢ + 1]`. -/
noncomputable def periodize (a : d → ℝ) (G : (d → ℝ) → ℝ) (t : UnitAddTorus d) : ℂ :=
  (G (fun i => (AddCircle.equivIoc 1 (a i) (t i) : ℝ)) : ℂ)

omit [Fintype d] in
theorem periodize_coe {a : d → ℝ} (G : (d → ℝ) → ℝ) {x : d → ℝ}
    (hx : x ∈ {x : d → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)}) :
    periodize a G (fun i => (x i : UnitAddCircle)) = (G x : ℂ) := by
  unfold periodize
  congr 2
  funext i
  rw [AddCircle.equivIoc_coe_of_mem (hx i)]

omit [Fintype d] in
theorem measurable_periodize (a : d → ℝ) {G : (d → ℝ) → ℝ} (hG : Measurable G) :
    Measurable (periodize a G) := by
  have h : periodize a G = (fun y : d → ℝ => (G y : ℂ)) ∘
      (fun t : UnitAddTorus d => fun i => (AddCircle.equivIoc 1 (a i) (t i) : ℝ)) := rfl
  rw [h]
  refine (Complex.measurable_ofReal.comp hG).comp ?_
  exact measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc 1 (a i)).measurable.comp (measurable_pi_apply i))

theorem mFourier_neg_coe (k : d → ℤ) (y : d → ℝ) :
    UnitAddTorus.mFourier (-k) (fun i => (y i : UnitAddCircle)) =
      Complex.exp (∑ i, 2 * Real.pi * Complex.I * (-(k i : ℂ)) * y i) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, Int.cast_neg,
    fourier_coe_apply]
  rw [Complex.exp_sum]
  simp

theorem mFourierCoeff_periodize (a : d → ℝ) {G : (d → ℝ) → ℝ}
    (h0 : ∀ x, (∃ i, x i ∉ Ioc (a i) (a i + 1)) → G x = 0) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (periodize a G) k =
      ∫ y, G y • Complex.exp (∑ i, 2 * Real.pi * Complex.I * (-(k i : ℂ)) * y i) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ a]
  calc _ = ∫ x in {x : d → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)}, G x • Complex.exp
        (∑ i, 2 * Real.pi * Complex.I * (-(k i : ℂ)) * x i) := by
        refine setIntegral_congr_fun ?_ fun x hx => ?_
        · exact MeasurableSet.univ_pi' fun i => measurableSet_Ioc (a := a i)
        · simp only [periodize_coe G hx, mFourier_neg_coe, Complex.real_smul]
          ring
    _ = _ := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
        have : G x = 0 := h0 x (by simpa using hx)
        simp [this]

theorem integral_norm_sq_periodize (a : d → ℝ) {G : (d → ℝ) → ℝ}
    (h0 : ∀ x, (∃ i, x i ∉ Ioc (a i) (a i + 1)) → G x = 0) :
    ∫ t, ‖periodize a G t‖ ^ 2 = ∫ y, G y ^ 2 := by
  refine (UnitAddTorus.integral_preimage (fun t => ‖periodize a G t‖ ^ 2) a).trans ?_
  calc _ = ∫ x in {x : d → ℝ | ∀ i, x i ∈ Ioc (a i) (a i + 1)}, G x ^ 2 := by
        refine setIntegral_congr_fun ?_ fun x hx => ?_
        · exact MeasurableSet.univ_pi' fun i => measurableSet_Ioc (a := a i)
        · simp [periodize_coe G hx]
    _ = _ := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
        have : G x = 0 := h0 x (by simpa using hx)
        simp [this]

/-- Parseval's identity on `d → ℝ`. -/
theorem hasSum_sq_norm_mFourierCoeff_periodize (a : d → ℝ) {G : (d → ℝ) → ℝ}
    (hG : Measurable G) {C : ℝ} (hC : ∀ x, |G x| ≤ C)
    (h0 : ∀ x, (∃ i, x i ∉ Ioc (a i) (a i + 1)) → G x = 0) :
    HasSum (fun k : d → ℤ => ‖∫ y, G y • Complex.exp
      (∑ i, 2 * Real.pi * Complex.I * (-(k i : ℂ)) * y i)‖ ^ 2) (∫ y, G y ^ 2) := by
  have hb : ∀ t, ‖periodize a G t‖ ≤ C := fun t => by simpa [periodize] using hC _
  obtain ⟨f, hf⟩ : ∃ f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)),
      (f : UnitAddTorus d → ℂ) =ᵐ[volume] periodize a G :=
    ⟨_, (MemLp.of_bound (μ := (volume : Measure (UnitAddTorus d)))
      (measurable_periodize a hG).aestronglyMeasurable C
      (Filter.Eventually.of_forall hb)).coeFn_toLp⟩
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff f
  have hc : ∀ k, UnitAddTorus.mFourierCoeff f k =
      UnitAddTorus.mFourierCoeff (periodize a G) k := by
    intro k
    unfold UnitAddTorus.mFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hf] with t ht
    rw [ht]
  have hi : ∫ t, ‖f t‖ ^ 2 = ∫ y, G y ^ 2 := by
    rw [← integral_norm_sq_periodize a h0]
    refine integral_congr_ae ?_
    filter_upwards [hf] with t ht
    rw [ht]
  simp only [hc, hi, mFourierCoeff_periodize a h0] at h
  exact h

end Torus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Parseval's identity on a unit box.** If `ψ` is bounded, measurable and vanishes outside the
box `∏ᵢ (aᵢ, aᵢ + 1]` (in orthonormal coordinates), then `∑ₖ ‖c_k(ψ)‖² = ∫ ψ²`. -/
theorem hasSum_sq_norm_fourierCoeff {ψ : E → ℝ} (a : Coord E → ℝ) (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ x, |ψ x| ≤ C)
    (h0 : ∀ x, (∃ i, coord x i ∉ Set.Ioc (a i) (a i + 1)) → ψ x = 0) :
    HasSum (fun k => ‖fourierCoeff k ψ‖ ^ 2) (∫ x, ψ x ^ 2) := by
  set G : (Coord E → ℝ) → ℝ := ψ ∘ (coordEquiv E).symm with hGdef
  have hmp := measurePreserving_coordEquiv (E := E)
  have hGm : Measurable G := hψ.comp (coordEquiv E).symm.measurable
  have hGb : ∀ y, |G y| ≤ C := fun y => hC _
  have hG0 : ∀ y, (∃ i, y i ∉ Ioc (a i) (a i + 1)) → G y = 0 := by
    intro y ⟨i, hi⟩
    apply h0
    refine ⟨i, ?_⟩
    simpa [← coe_coordEquiv] using hi
  have hGψ : ∀ x, G (coord x) = ψ x := by
    intro x
    simp [hGdef, ← coe_coordEquiv]
  have h := hasSum_sq_norm_mFourierCoeff_periodize a hGm hGb hG0
  have hint : ∫ x, ψ x ^ 2 = ∫ y, G y ^ 2 := by
    rw [← hmp.integral_comp' (g := fun y => G y ^ 2)]
    simp [coe_coordEquiv, hGψ]
  have hcoef : ∀ k : Coord E → ℤ, fourierCoeff k ψ = ∫ y, G y • Complex.exp
      (∑ i, 2 * Real.pi * Complex.I * (-(k i : ℂ)) * y i) := by
    intro k
    rw [← hmp.integral_comp' (g := fun y => G y • Complex.exp
      (∑ i, 2 * Real.pi * Complex.I * (-(k i : ℂ)) * y i))]
    unfold fourierCoeff
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [coe_coordEquiv, hGψ, fourierChar, fourierPhase_apply]
    congr 2
    push_cast
    rw [neg_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hint]
  simpa only [hcoef] using h

end IsotropicVariance.Infra.WhiteNoise
