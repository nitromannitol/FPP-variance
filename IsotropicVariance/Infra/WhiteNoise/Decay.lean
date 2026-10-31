/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoise.Fourier
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Decay of the Fourier coefficients of test functions

**Integration by parts.** For a compactly supported `C¹` function `ψ`,
`c_k(∂_v ψ) = -i θ_k(v) c_k(ψ)` (`fourierCoeff_fderiv`).

**The decay operator.** On `𝓓_K(E, ℝ)`:
- `dirDerivCLM K v` is the directional derivative;
- `laplaceCLM K j = -(4π²)⁻¹ ∂_{b_j}²` is the second derivative in the direction of the `j`-th basis
  vector, normalized so that `c_k(laplaceCLM K j f) = k_j² c_k(f)`;
- `decayCLM K N = 1 + ∑ⱼ (laplaceCLM K j)^N` satisfies
  `c_k(decayCLM K N f) = (1 + ∑ⱼ k_j^{2N}) c_k(f)`.

The resulting bound (`norm_fourierCoeff_le_decay`) is
`‖c_k(f)‖ ≤ (1 + ∑ⱼ k_j^{2N})⁻¹ |K| N₀(decayCLM K N f)`.
Here `N₀` is the sup norm, a continuous seminorm on `𝓓_K(E, ℝ)`, and `decayCLM K N` is a continuous
linear map.
-/

@[expose] public section

open MeasureTheory
open scoped Distributions

namespace IsotropicVariance.Infra.WhiteNoise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Integration by parts**: `c_k(∂_v ψ) = -i θ_k(v) c_k(ψ)` for a compactly supported `C¹`
function `ψ`. -/
theorem fourierCoeff_fderiv {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (k : Coord E → ℤ) (v : E) :
    fourierCoeff k (fun x => fderiv ℝ ψ x v) =
      -(fourierPhase k v * Complex.I) * fourierCoeff k ψ := by
  have hd : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hcont : Continuous fun x => fderiv ℝ ψ x v :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have he := continuous_fourierChar (E := E) k
  have h₁ : Integrable (fun x => fderiv ℝ ψ x v • fourierChar k x) :=
    (hcont.smul he).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).smul_right
  have h₂ : Integrable (fun x => ψ x • fderiv ℝ (fourierChar k) x v) := by
    simp_rw [fderiv_fourierChar_apply]
    exact (hψ.continuous.smul (continuous_const.mul he)).integrable_of_hasCompactSupport
      hc.smul_right
  have h₃ : Integrable (fun x => ψ x • fourierChar k x) :=
    (hψ.continuous.smul he).integrable_of_hasCompactSupport hc.smul_right
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h₁ h₂ h₃
    (fun x _ => hd x) (fun x _ => differentiable_fourierChar k x)
  simp_rw [fderiv_fourierChar_apply] at h
  unfold fourierCoeff
  rw [← neg_eq_iff_eq_neg.mpr h]
  simp_rw [← mul_smul_comm]
  rw [integral_const_mul, neg_mul]

section SupportedIn

variable (K : TopologicalSpace.Compacts E)

/-- The directional derivative `f ↦ ∂_v f` as a continuous linear map on `𝓓_K(E, ℝ)`. -/
noncomputable def dirDerivCLM (v : E) : 𝓓_{K}(E, ℝ) →L[ℝ] 𝓓_{K}(E, ℝ) :=
  (ContDiffMapSupportedIn.postcompCLM (ContinuousLinearMap.apply ℝ ℝ v)).comp
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)

/-- The normalized second derivative `-(4π²)⁻¹ ∂_{b_j}²` on `𝓓_K(E, ℝ)`. -/
noncomputable def laplaceCLM (j : Coord E) : 𝓓_{K}(E, ℝ) →L[ℝ] 𝓓_{K}(E, ℝ) :=
  (-(4 * Real.pi ^ 2)⁻¹ : ℝ) •
    (dirDerivCLM K (coordBasis E j)).comp (dirDerivCLM K (coordBasis E j))

/-- The decay operator `1 + ∑ⱼ (laplaceCLM K j)^N` on `𝓓_K(E, ℝ)`. -/
noncomputable def decayCLM (N : ℕ) : 𝓓_{K}(E, ℝ) →L[ℝ] 𝓓_{K}(E, ℝ) :=
  1 + ∑ j, laplaceCLM K j ^ N

/-- The Fourier coefficient as a linear map on `𝓓_K(E, ℝ)`. -/
noncomputable def fourierCoeffLM (k : Coord E → ℤ) : 𝓓_{K}(E, ℝ) →ₗ[ℝ] ℂ where
  toFun f := fourierCoeff k f
  map_add' f g := by
    change fourierCoeff k (⇑f + ⇑g) = _
    exact fourierCoeff_add k (f.contDiff.continuous.integrable_of_hasCompactSupport f.compact_supp)
      (g.contDiff.continuous.integrable_of_hasCompactSupport g.compact_supp)
  map_smul' c f := by
    change fourierCoeff k (c • ⇑f) = _
    exact fourierCoeff_smul k c f

variable {K}

theorem fourierCoeffLM_apply (k : Coord E → ℤ) (f : 𝓓_{K}(E, ℝ)) :
    fourierCoeffLM K k f = fourierCoeff k f := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem dirDerivCLM_apply (v : E) (f : 𝓓_{K}(E, ℝ)) (x : E) :
    dirDerivCLM K v f x = fderiv ℝ f x v := by
  simp [dirDerivCLM, ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ f le_top]

theorem fourierCoeff_dirDerivCLM (k : Coord E → ℤ) (v : E) (f : 𝓓_{K}(E, ℝ)) :
    fourierCoeff k (dirDerivCLM K v f) = -(fourierPhase k v * Complex.I) * fourierCoeff k f := by
  rw [← fourierCoeff_fderiv (f.contDiff.of_le (mod_cast le_top)) f.compact_supp k v]
  exact fourierCoeff_congr k (dirDerivCLM_apply v f)

theorem fourierCoeff_laplaceCLM (k : Coord E → ℤ) (j : Coord E) (f : 𝓓_{K}(E, ℝ)) :
    fourierCoeff k (laplaceCLM K j f) = (((k j : ℝ) ^ 2 : ℝ) : ℂ) * fourierCoeff k f := by
  have h : ⇑(laplaceCLM K j f) = (-(4 * Real.pi ^ 2)⁻¹ : ℝ) •
      ⇑(dirDerivCLM K (coordBasis E j) (dirDerivCLM K (coordBasis E j) f)) := rfl
  rw [h, fourierCoeff_smul, fourierCoeff_dirDerivCLM, fourierCoeff_dirDerivCLM,
    fourierPhase_coordBasis, Complex.real_smul]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp
  linear_combination (-4 * (k j : ℂ) ^ 2 * fourierCoeff k f) * Complex.I_sq

theorem fourierCoeff_laplaceCLM_pow (k : Coord E → ℤ) (j : Coord E) (N : ℕ)
    (f : 𝓓_{K}(E, ℝ)) :
    fourierCoeff k ((laplaceCLM K j ^ N) f) =
      (((k j : ℝ) ^ (2 * N) : ℝ) : ℂ) * fourierCoeff k f := by
  induction N generalizing f with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, fourierCoeff_laplaceCLM]
    push_cast
    ring

/-- **The decay identity**: `c_k(decayCLM K N f) = (1 + ∑ⱼ k_j^{2N}) c_k(f)`. -/
theorem fourierCoeff_decayCLM (k : Coord E → ℤ) (N : ℕ) (f : 𝓓_{K}(E, ℝ)) :
    fourierCoeff k (decayCLM K N f) =
      ((1 + ∑ j, (k j : ℝ) ^ (2 * N) : ℝ) : ℂ) * fourierCoeff k f := by
  rw [← fourierCoeffLM_apply, decayCLM, add_apply, one_apply_eq_self, sum_apply, map_add,
    map_sum]
  simp only [fourierCoeffLM_apply, fourierCoeff_laplaceCLM_pow]
  push_cast
  rw [add_mul, Finset.sum_mul, one_mul]

/-- The sup norm bound `‖c_k(f)‖ ≤ |K| N₀(f)`. -/
theorem norm_fourierCoeff_le_seminorm (k : Coord E → ℤ) (f : 𝓓_{K}(E, ℝ)) :
    ‖fourierCoeff k f‖ ≤
      volume.real (K : Set E) * ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K 0 f := by
  have hK : volume (K : Set E) < ⊤ := K.isCompact.measure_lt_top
  unfold fourierCoeff
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (K : Set E)) fun x hx => by
    simp [f.zero_on_compl hx]]
  refine (norm_setIntegral_le_of_norm_le_const hK fun x _ => ?_).trans_eq (mul_comm _ _)
  rw [norm_smul, norm_fourierChar, mul_one]
  exact ContDiffMapSupportedIn.norm_apply_le_seminorm ℝ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem one_add_sum_pow_pos (k : Coord E → ℤ) (N : ℕ) : 0 < 1 + ∑ j, (k j : ℝ) ^ (2 * N) := by
  have : 0 ≤ ∑ j, (k j : ℝ) ^ (2 * N) :=
    Finset.sum_nonneg fun j _ => (even_two_mul N).pow_nonneg _
  linarith

/-- **Decay of Fourier coefficients**:
`‖c_k(f)‖ ≤ (1 + ∑ⱼ k_j^{2N})⁻¹ |K| N₀(decayCLM K N f)`. -/
theorem norm_fourierCoeff_le_decay (k : Coord E → ℤ) (N : ℕ) (f : 𝓓_{K}(E, ℝ)) :
    ‖fourierCoeff k f‖ ≤ (1 + ∑ j, (k j : ℝ) ^ (2 * N))⁻¹ *
      (volume.real (K : Set E) * ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K 0 (decayCLM K N f)) := by
  have hw := one_add_sum_pow_pos k N
  have h := norm_fourierCoeff_le_seminorm k (decayCLM K N f)
  rw [fourierCoeff_decayCLM, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le] at h
  rw [le_inv_mul_iff₀ hw]
  exact h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
variable (K) in
/-- The sup norm is continuous on `𝓓_K(E, ℝ)`. -/
theorem continuous_seminorm_zero :
    Continuous (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K 0) :=
  (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K).continuous_seminorm 0

end SupportedIn

end IsotropicVariance.Infra.WhiteNoise
