/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfig
public import IsotropicVariance.Statements.Configurations.WhiteNoiseConfigInstMeasurableSpace
public import IsotropicVariance.Statements.Noise.IsWhiteNoise
public import IsotropicVariance.Statements.Space.Pt
public import IsotropicVariance.Infra.WhiteNoise.Noise
public import IsotropicVariance.Infra.WhiteNoise.GaussianSeries
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Existence of Gaussian white noise

**Construction.** Let `(ωⱼ)`, `j = (z, k, b) ∈ ℤ^n × ℤ^n × Bool`, be independent standard
Gaussians on `Ω = ℤ^n × ℤ^n × Bool → ℝ` (`Measure.infinitePi`, a standard Borel space). On the good
set (full measure), the noise is `W(ω)(φ) = ∑ⱼ aⱼ(φ) ωⱼ`, where the `aⱼ(φ)` are the real and
imaginary parts of the local Fourier coefficients `c_k(φ χ_z)` (`noiseCoeff`). Off the good set,
`W(ω) = 0`.

**Proof.**
* **Continuity.** For each `ω`, `W(ω)` is a continuous linear functional on `𝓓(E, ℝ)`. By the
  universal property of the test-function topology (`TestFunction.mkCLM`), it suffices that it is
  continuous on every `𝓓_K(E, ℝ)`. There it is bounded by
  `∑_{z ∈ Z_K} B_z(φ) ∑ⱼ |ωⱼ| u_z(j)`, a continuous function of `φ` vanishing at `0`.
* **Measurability.** Each evaluation `ω ↦ W(ω)(φ)` is measurable; these generate the σ-algebra of
  configurations.
* **Laws.** `W(φ)` is an almost surely absolutely convergent series of independent standard
  Gaussians with `∑ⱼ aⱼ(φ)² = ∫ φ²` (`hasSum_noiseCoeff_sq`). So its law is
  `gaussianReal 0 (∫ φ²)` (`hasLaw_tsum_mul_gaussian`).

**The definitions.** The construction uses the definitions `IsotropicVariance.Pt`,
`IsotropicVariance.WhiteNoiseConfig` with its σ-algebra `WhiteNoiseConfig.instMeasurableSpace`,
and `IsotropicVariance.IsWhiteNoise`. `exists_isWhiteNoise` has exactly the type of the companion
theorem `IsotropicVariance.exists_isWhiteNoise`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

namespace IsotropicVariance.Infra.WhiteNoise

/-! ### Continuity of a linear functional bounded by a continuous function -/

/-- A linear functional bounded by a continuous function vanishing at `0` is continuous. -/
theorem continuous_of_abs_le {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (T : V →ₗ[ℝ] ℝ) {q : V → ℝ} (hq : Continuous q) (hq0 : q 0 = 0)
    (hT : ∀ v, |T v| ≤ q v) : Continuous T := by
  refine continuous_of_continuousAt_zero T ?_
  rw [ContinuousAt, map_zero]
  refine squeeze_zero_norm (fun v => (Real.norm_eq_abs _).trans_le (hT v)) ?_
  simpa [hq0] using hq.tendsto 0

/-! ### The noise -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The value of the noise: `∑ⱼ aⱼ(φ) ωⱼ` on the good set, `0` elsewhere. -/
noncomputable def noiseValue (ω : NoiseIndex E → ℝ) (φ : 𝓓((⊤ : Opens E), ℝ)) : ℝ :=
  (goodSet (E := E)).indicator (fun ω => ∑' j, noiseCoeff φ j * ω j) ω

theorem noiseValue_of_mem {ω : NoiseIndex E → ℝ} (hω : ω ∈ goodSet)
    (φ : 𝓓((⊤ : Opens E), ℝ)) : noiseValue ω φ = ∑' j, noiseCoeff φ j * ω j :=
  Set.indicator_of_mem hω _

theorem noiseValue_of_notMem {ω : NoiseIndex E → ℝ} (hω : ω ∉ goodSet)
    (φ : 𝓓((⊤ : Opens E), ℝ)) : noiseValue ω φ = 0 :=
  Set.indicator_of_notMem hω _

theorem noiseValue_add (ω : NoiseIndex E → ℝ) (φ ψ : 𝓓((⊤ : Opens E), ℝ)) :
    noiseValue ω (φ + ψ) = noiseValue ω φ + noiseValue ω ψ := by
  by_cases hω : ω ∈ goodSet
  · rw [noiseValue_of_mem hω, noiseValue_of_mem hω, noiseValue_of_mem hω]
    have h : noiseCoeff (⇑(φ + ψ)) = noiseCoeff ⇑φ + noiseCoeff ⇑ψ :=
      noiseCoeff_add φ.continuous ψ.continuous
    simp only [h, Pi.add_apply, add_mul]
    exact (summable_noiseCoeff_mul_of_contDiff φ.contDiff φ.hasCompactSupport hω).tsum_add
      (summable_noiseCoeff_mul_of_contDiff ψ.contDiff ψ.hasCompactSupport hω)
  · simp [noiseValue_of_notMem hω]

theorem noiseValue_smul (ω : NoiseIndex E → ℝ) (c : ℝ) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    noiseValue ω (c • φ) = c • noiseValue ω φ := by
  by_cases hω : ω ∈ goodSet
  · rw [noiseValue_of_mem hω, noiseValue_of_mem hω]
    have h : noiseCoeff (⇑(c • φ)) = c • noiseCoeff ⇑φ := noiseCoeff_smul c φ
    simp only [h, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact tsum_mul_left
  · simp [noiseValue_of_notMem hω]

/-- On the good set, the noise restricted to `𝓓_K(E, ℝ)` as a linear map. -/
noncomputable def noiseLM (K : Compacts E) {ω : NoiseIndex E → ℝ} (hω : ω ∈ goodSet) :
    𝓓_{K}(E, ℝ) →ₗ[ℝ] ℝ where
  toFun φ := ∑' j, noiseCoeff φ j * ω j
  map_add' φ ψ := by
    have h : noiseCoeff (⇑(φ + ψ)) = noiseCoeff ⇑φ + noiseCoeff ⇑ψ :=
      noiseCoeff_add φ.contDiff.continuous ψ.contDiff.continuous
    simp only [h, Pi.add_apply, add_mul]
    exact (summable_noiseCoeff_mul φ hω).tsum_add (summable_noiseCoeff_mul ψ hω)
  map_smul' c φ := by
    have h : noiseCoeff (⇑(c • φ)) = c • noiseCoeff ⇑φ := noiseCoeff_smul c φ
    simp only [h, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
    exact tsum_mul_left

theorem continuous_noiseLM (K : Compacts E) {ω : NoiseIndex E → ℝ} (hω : ω ∈ goodSet) :
    Continuous (noiseLM K hω) :=
  continuous_of_abs_le (noiseLM K hω)
    (q := fun φ => ∑ z ∈ cubesMeeting K, cubeBound K z φ * ∑' j, |ω j| * cubeWeight z j)
    (continuous_finsetSum _ fun z _ => (continuous_cubeBound K z).mul continuous_const)
    (by simp [cubeBound_zero]) fun φ => abs_tsum_noiseCoeff_mul_le φ hω

/-- For every `ω`, the noise is continuous on every `𝓓_K(E, ℝ)`. -/
theorem continuous_noiseValue_comp (ω : NoiseIndex E → ℝ) (K : Compacts E)
    (K_sub : (K : Set E) ⊆ ((⊤ : Opens E) : Set E)) :
    Continuous (noiseValue ω ∘ TestFunction.ofSupportedIn K_sub) := by
  by_cases hω : ω ∈ goodSet
  · have h : noiseValue ω ∘ TestFunction.ofSupportedIn K_sub = noiseLM K hω := by
      funext φ
      exact noiseValue_of_mem hω _
    rw [h]
    exact continuous_noiseLM K hω
  · have h : noiseValue ω ∘ TestFunction.ofSupportedIn K_sub = fun _ => 0 := by
      funext φ
      exact noiseValue_of_notMem hω _
    rw [h]
    exact continuous_const

/-- The noise `W(ω)` as a continuous linear functional on `𝓓(E, ℝ)`. -/
noncomputable def noiseCLM (ω : NoiseIndex E → ℝ) : 𝓓((⊤ : Opens E), ℝ) →L[ℝ] ℝ :=
  TestFunction.mkCLM ℝ (noiseValue ω) (noiseValue_add ω) (noiseValue_smul ω)
    (continuous_noiseValue_comp ω)

/-- The white noise, as a random white-noise configuration. -/
noncomputable def noise (ω : NoiseIndex E → ℝ) : WhiteNoiseConfig E :=
  noiseCLM ω

/-- The underlying probability measure: independent standard Gaussian coordinates. -/
noncomputable abbrev noiseMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Measure (NoiseIndex E → ℝ) :=
  Measure.infinitePi fun _ : NoiseIndex E => gaussianReal 0 1

theorem measurable_noise_apply (φ : 𝓓((⊤ : Opens E), ℝ)) :
    Measurable fun ω : NoiseIndex E → ℝ => noise ω φ :=
  (measurable_tsum_mul (noiseCoeff φ)).indicator measurableSet_goodSet

/-- The noise is measurable. -/
theorem measurable_noise : Measurable (noise (E := E)) := by
  refine measurable_iff_comap_le.2 ?_
  rw [WhiteNoiseConfig.instMeasurableSpace, MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_comp]
  exact (measurable_noise_apply φ).comap_le

/-- **The laws**: `W(φ)` is centered Gaussian with variance `∫ φ²`. -/
theorem hasLaw_noise (φ : 𝓓((⊤ : Opens E), ℝ)) :
    HasLaw (fun ω => noise ω φ) (gaussianReal 0 (∫ x, φ x ^ 2).toNNReal) (noiseMeasure E) := by
  refine hasLaw_tsum_mul_gaussian (hasSum_noiseCoeff_sq φ.continuous φ.hasCompactSupport)
    (measurable_noise_apply φ).aemeasurable ?_
  filter_upwards [ae_mem_goodSet] with ω hω
  exact ⟨summable_noiseCoeff_mul_of_contDiff φ.contDiff φ.hasCompactSupport hω,
    noiseValue_of_mem hω φ⟩

/-- **Gaussian white noise exists** on every finite-dimensional real inner product space, on a
standard Borel probability space. -/
theorem exists_isWhiteNoise_of_innerProductSpace :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (W : Ω → WhiteNoiseConfig E), IsProbabilityMeasure P ∧ IsWhiteNoise W P :=
  ⟨NoiseIndex E → ℝ, inferInstance, inferInstance, noiseMeasure E, noise, inferInstance,
    measurable_noise, hasLaw_noise⟩

/-- **Gaussian white noise exists** on `ℝ^d = Pt m`, on a standard Borel probability space: the
statement of the theorem `IsotropicVariance.exists_isWhiteNoise`. -/
theorem exists_isWhiteNoise (m : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (W : Ω → WhiteNoiseConfig (Pt m)), IsProbabilityMeasure P ∧ IsWhiteNoise W P :=
  exists_isWhiteNoise_of_innerProductSpace

end IsotropicVariance.Infra.WhiteNoise
