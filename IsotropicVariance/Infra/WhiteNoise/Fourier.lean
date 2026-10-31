/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoise.Coordinates
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Characters and Fourier coefficients in orthonormal coordinates

For `k ∈ ℤ^n` (`n = finrank ℝ E`), the character of frequency `k` is
`e_k(x) = exp(i θ_k(x))`, where `θ_k(x) = -2π ∑ᵢ kᵢ coord x i` is a real linear form
(`fourierPhase`). The Fourier coefficient of `ψ : E → ℝ` is `c_k(ψ) = ∫ ψ(x) e_k(x) dx`
(`fourierCoeff`).

Restricted to a unit box in coordinates, these are the coefficients of the Fourier series of the
periodized function (`IsotropicVariance.Infra.WhiteNoise.Parseval`). Integration by parts turns
derivatives into multiplication by the frequency (`IsotropicVariance.Infra.WhiteNoise.Decay`).
-/

@[expose] public section

open MeasureTheory

namespace IsotropicVariance.Infra.WhiteNoise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The phase `θ_k(x) = -2π ∑ᵢ kᵢ coord x i` of the character of frequency `k`. -/
noncomputable def fourierPhase (k : Coord E → ℤ) : E →L[ℝ] ℝ :=
  ∑ i, (-(2 * Real.pi * k i)) • (ContinuousLinearMap.proj i).comp (coordCLM E)

theorem fourierPhase_apply (k : Coord E → ℤ) (x : E) :
    fourierPhase k x = -(2 * Real.pi * ∑ i, (k i : ℝ) * coord x i) := by
  simp only [fourierPhase, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.proj_apply, coordCLM_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The phase on a basis vector. -/
theorem fourierPhase_coordBasis (k : Coord E → ℤ) (j : Coord E) :
    fourierPhase k (coordBasis E j) = -(2 * Real.pi * k j) := by
  rw [fourierPhase_apply]
  simp [coord_coordBasis]

/-- The character `e_k(x) = exp(i θ_k(x))` of frequency `k`. -/
noncomputable def fourierChar (k : Coord E → ℤ) (x : E) : ℂ :=
  Complex.exp (fourierPhase k x * Complex.I)

theorem norm_fourierChar (k : Coord E → ℤ) (x : E) : ‖fourierChar k x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem continuous_fourierChar (k : Coord E → ℤ) : Continuous (fourierChar (E := E) k) := by
  unfold fourierChar
  have := (fourierPhase (E := E) k).continuous
  fun_prop

/-- The derivative of a character. -/
theorem hasFDerivAt_fourierChar (k : Coord E → ℤ) (x : E) :
    HasFDerivAt (fourierChar k) (fourierChar k x • (fourierPhase k).smulRight Complex.I) x := by
  have h : fourierChar (E := E) k = fun y => Complex.exp ((fourierPhase k).smulRight Complex.I y) := by
    ext y
    simp [fourierChar, Complex.real_smul]
  rw [h]
  exact ((fourierPhase k).smulRight Complex.I).hasFDerivAt.cexp

theorem differentiable_fourierChar (k : Coord E → ℤ) : Differentiable ℝ (fourierChar (E := E) k) :=
  fun x => (hasFDerivAt_fourierChar k x).differentiableAt

/-- The directional derivative of a character: `∂_v e_k = i θ_k(v) e_k`. -/
theorem fderiv_fourierChar_apply (k : Coord E → ℤ) (x v : E) :
    fderiv ℝ (fourierChar k) x v = (fourierPhase k v * Complex.I) * fourierChar k x := by
  rw [(hasFDerivAt_fourierChar k x).fderiv]
  simp [Complex.real_smul, mul_comm]

variable [MeasurableSpace E] [BorelSpace E]

/-- The Fourier coefficient `c_k(ψ) = ∫ ψ(x) e_k(x) dx`. -/
noncomputable def fourierCoeff (k : Coord E → ℤ) (ψ : E → ℝ) : ℂ :=
  ∫ x, ψ x • fourierChar k x

theorem integrable_smul_fourierChar (k : Coord E → ℤ) {ψ : E → ℝ} (hψ : Integrable ψ) :
    Integrable (fun x => ψ x • fourierChar k x) :=
  hψ.smul_bdd 1 (continuous_fourierChar k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_fourierChar k x).le)

theorem fourierCoeff_add (k : Coord E → ℤ) {ψ φ : E → ℝ} (hψ : Integrable ψ)
    (hφ : Integrable φ) : fourierCoeff k (ψ + φ) = fourierCoeff k ψ + fourierCoeff k φ := by
  simp only [fourierCoeff, Pi.add_apply, add_smul]
  exact integral_add (integrable_smul_fourierChar k hψ) (integrable_smul_fourierChar k hφ)

theorem fourierCoeff_smul (k : Coord E → ℤ) (c : ℝ) (ψ : E → ℝ) :
    fourierCoeff k (c • ψ) = c • fourierCoeff k ψ := by
  simp only [fourierCoeff, Pi.smul_apply, smul_eq_mul, mul_smul]
  exact integral_smul c _

theorem fourierCoeff_zero (k : Coord E → ℤ) : fourierCoeff k (0 : E → ℝ) = 0 := by
  simp [fourierCoeff]

theorem fourierCoeff_congr (k : Coord E → ℤ) {ψ φ : E → ℝ} (h : ∀ x, ψ x = φ x) :
    fourierCoeff k ψ = fourierCoeff k φ := by
  rw [funext h]

end IsotropicVariance.Infra.WhiteNoise
