/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoise.Decay
public import IsotropicVariance.Infra.WhiteNoise.Parseval
public import IsotropicVariance.Infra.WhiteNoise.Partition
public import IsotropicVariance.Infra.WhiteNoise.Summability

/-!
# The coefficients of white noise

White noise on `E` is `W(φ) = ∑ⱼ aⱼ(φ) ωⱼ` over `j = (z, k, b) ∈ ℤ^n × ℤ^n × Bool`, where
`(ωⱼ)` are independent standard Gaussians. The coefficients are the real (`b = true`) and imaginary
(`b = false`) parts of the local Fourier coefficients `c_k(φ χ_z)`, with `(χ_z)` the cube bumps
(`∑_z χ_z² = 1`).

* **Variance** (`hasSum_noiseCoeff_sq`): `∑ⱼ aⱼ(φ)² = ∫ φ²`, by Parseval on each cube and
  `∑_z χ_z² = 1`.
* **Bounds on `𝓓_K`** (`abs_noiseCoeff_mul_le`):
  `|aⱼ(φ) ωⱼ| ≤ ∑_{z ∈ Z_K} B_z(φ) |ωⱼ| u_z(j)`, where `Z_K` is the finite set of cubes meeting
  `K`, `u_z(z', k, b) = [z' = z] (1 + ∑ᵢ kᵢ^{2n})⁻¹`, and `B_z` is a continuous function on
  `𝓓_K(E, ℝ)` vanishing at `0` (`continuous_cubeBound`).
* **The good set** `goodSet`, where `∑ⱼ |ωⱼ| u_z(j) < ∞` for every `z`, is measurable and has full
  measure. On it every series `∑ⱼ aⱼ(φ) ωⱼ` converges absolutely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions

namespace IsotropicVariance.Infra.WhiteNoise

/-- A nonnegative family on a product with fiberwise sums `g b` and `∑ g = s` has sum `s`. -/
theorem hasSum_prod_of_nonneg {β γ : Type*} {f : β × γ → ℝ} (hf : 0 ≤ f) {g : β → ℝ} {s : ℝ}
    (hg : ∀ b, HasSum (fun c => f (b, c)) (g b)) (hs : HasSum g s) : HasSum f s := by
  have hg' : (fun b => ∑' c, f (b, c)) = g := funext fun b => (hg b).tsum_eq
  have hsum : Summable f :=
    (summable_prod_of_nonneg hf).2 ⟨fun b => (hg b).summable, hg' ▸ hs.summable⟩
  exact (hsum.hasSum.prod_fiberwise hg).unique hs ▸ hsum.hasSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- The index set `ℤ^n × ℤ^n × Bool` of the Gaussian coordinates: cube, frequency, and real or
imaginary part. -/
abbrev NoiseIndex : Type := (Coord E → ℤ) × (Coord E → ℤ) × Bool

variable (E) in
/-- The exponent `N = n` of the decay operator. -/
noncomputable abbrev decayExp : ℕ := Fintype.card (Coord E)

/-- The frequency weight `(1 + ∑ᵢ kᵢ^{2n})⁻¹`. -/
noncomputable def freqWeight (k : Coord E → ℤ) : ℝ :=
  (1 + ∑ i, (k i : ℝ) ^ (2 * decayExp E))⁻¹

omit [FiniteDimensional ℝ E] in
theorem freqWeight_nonneg (k : Coord E → ℤ) : 0 ≤ freqWeight k :=
  (inv_pos.2 (one_add_sum_pow_pos k _)).le

omit [FiniteDimensional ℝ E] in
theorem summable_freqWeight : Summable (freqWeight (E := E)) :=
  summable_inv_one_add_sum_pow (Coord E)

/-- The weight `u_z(z', k, b) = [z' = z] (1 + ∑ᵢ kᵢ^{2n})⁻¹` of the cube `z`. -/
noncomputable def cubeWeight (z : Coord E → ℤ) (j : NoiseIndex E) : ℝ :=
  if j.1 = z then freqWeight j.2.1 else 0

omit [FiniteDimensional ℝ E] in
theorem cubeWeight_nonneg (z : Coord E → ℤ) (j : NoiseIndex E) : 0 ≤ cubeWeight z j := by
  unfold cubeWeight
  split_ifs
  exacts [freqWeight_nonneg _, le_rfl]

omit [FiniteDimensional ℝ E] in
theorem summable_cubeWeight (z : Coord E → ℤ) : Summable (cubeWeight (E := E) z) := by
  have hinj : Function.Injective fun q : (Coord E → ℤ) × Bool => ((z, q) : NoiseIndex E) :=
    fun _ _ h => (Prod.ext_iff.1 h).2
  have hq : Summable fun q : (Coord E → ℤ) × Bool => freqWeight (E := E) q.1 := by
    refine (summable_prod_of_nonneg fun q => freqWeight_nonneg q.1).2
      ⟨fun _ => Summable.of_finite, ?_⟩
    simpa [tsum_fintype] using summable_freqWeight.mul_left 2
  refine (hinj.summable_iff fun j hj => ?_).1 (hq.congr fun q => by simp [cubeWeight])
  obtain ⟨z', k, b⟩ := j
  have : z' ≠ z := fun h => hj ⟨(k, b), by simp [h]⟩
  simp [cubeWeight, this]

/-- The good set: `∑ⱼ |ωⱼ| u_z(j) < ∞` for every cube `z`. -/
def goodSet : Set (NoiseIndex E → ℝ) :=
  {ω | ∀ z, Summable fun j => |ω j| * cubeWeight z j}

omit [FiniteDimensional ℝ E] in
theorem measurableSet_goodSet : MeasurableSet (goodSet (E := E)) := by
  rw [goodSet, Set.ofPred_forall]
  exact MeasurableSet.iInter fun z =>
    measurableSet_setOf_summable_abs_mul (cubeWeight_nonneg z)

omit [FiniteDimensional ℝ E] in
/-- The good set has full measure. -/
theorem ae_mem_goodSet :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : NoiseIndex E => gaussianReal 0 1), ω ∈ goodSet := by
  simp only [goodSet, Set.mem_ofPred_eq]
  exact ae_all_iff.2 fun z => ae_summable_abs_mul (cubeWeight_nonneg z) (summable_cubeWeight z)

variable [MeasurableSpace E] [BorelSpace E]

/-- The local Fourier coefficient `c_k(ψ χ_z)`. -/
noncomputable def localCoeff (z k : Coord E → ℤ) (ψ : E → ℝ) : ℂ :=
  fourierCoeff k fun x => ψ x * cubeBump z x

/-- The coefficients `aⱼ(ψ)` of white noise: real and imaginary parts of `c_k(ψ χ_z)`. -/
noncomputable def noiseCoeff (ψ : E → ℝ) (j : NoiseIndex E) : ℝ :=
  if j.2.2 then (localCoeff j.1 j.2.1 ψ).re else (localCoeff j.1 j.2.1 ψ).im

theorem abs_noiseCoeff_le (ψ : E → ℝ) (j : NoiseIndex E) :
    |noiseCoeff ψ j| ≤ ‖localCoeff j.1 j.2.1 ψ‖ := by
  unfold noiseCoeff
  split_ifs
  exacts [Complex.abs_re_le_norm _, Complex.abs_im_le_norm _]

theorem integrable_mul_cubeBump {ψ : E → ℝ} (hψ : Continuous ψ) (z : Coord E → ℤ) :
    Integrable fun x => ψ x * cubeBump z x :=
  (hψ.mul (contDiff_cubeBump z).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_cubeBump z).mul_left

theorem noiseCoeff_add {ψ φ : E → ℝ} (hψ : Continuous ψ) (hφ : Continuous φ) :
    noiseCoeff (ψ + φ) = noiseCoeff ψ + noiseCoeff φ := by
  funext j
  have h : localCoeff j.1 j.2.1 (ψ + φ) = localCoeff j.1 j.2.1 ψ + localCoeff j.1 j.2.1 φ := by
    rw [localCoeff, localCoeff, localCoeff, ← fourierCoeff_add _ (integrable_mul_cubeBump hψ _)
      (integrable_mul_cubeBump hφ _)]
    exact fourierCoeff_congr _ fun x => by simp [add_mul]
  simp only [noiseCoeff, h, Pi.add_apply]
  split_ifs <;> simp

theorem noiseCoeff_smul (c : ℝ) (ψ : E → ℝ) : noiseCoeff (c • ψ) = c • noiseCoeff ψ := by
  funext j
  have h : localCoeff j.1 j.2.1 (c • ψ) = c • localCoeff j.1 j.2.1 ψ := by
    rw [localCoeff, localCoeff, ← fourierCoeff_smul]
    exact fourierCoeff_congr _ fun x => by simp [mul_assoc]
  simp only [noiseCoeff, h, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

section Cubes

/-- The finite set of cubes meeting the compact set `K`. -/
noncomputable def cubesMeeting (K : TopologicalSpace.Compacts E) : Finset (Coord E → ℤ) :=
  (finite_setOf_cubeBump_ne_zero K.isCompact.isBounded).toFinset

theorem localCoeff_eq_zero {K : TopologicalSpace.Compacts E} {ψ : E → ℝ}
    (hψ : ∀ x ∉ (K : Set E), ψ x = 0) {z : Coord E → ℤ} (hz : z ∉ cubesMeeting K)
    (k : Coord E → ℤ) : localCoeff z k ψ = 0 := by
  have h : ∀ x, ψ x * cubeBump z x = 0 := by
    intro x
    by_cases hx : x ∈ (K : Set E)
    · have : cubeBump z x = 0 := by
        by_contra hne
        exact hz ((Set.Finite.mem_toFinset _).2 ⟨x, hx, hne⟩)
      rw [this, mul_zero]
    · rw [hψ x hx, zero_mul]
  rw [localCoeff, fourierCoeff_congr k h]
  exact fourierCoeff_zero k

end Cubes

/-! ### Variance -/

/-- **The variance of the coefficients**: `∑ⱼ aⱼ(ψ)² = ∫ ψ²` for a continuous compactly supported
`ψ`. -/
theorem hasSum_noiseCoeff_sq {ψ : E → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    HasSum (fun j => noiseCoeff ψ j ^ 2) (∫ x, ψ x ^ 2) := by
  set K : TopologicalSpace.Compacts E := ⟨tsupport ψ, hc⟩
  have hK : ∀ x ∉ (K : Set E), ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hc
  -- the two inner sums: over `b`, then over `k` (Parseval on the cube `z`)
  have hb : ∀ z k, HasSum (fun b => noiseCoeff ψ (z, k, b) ^ 2) (‖localCoeff z k ψ‖ ^ 2) := by
    intro z k
    convert hasSum_fintype (fun b => noiseCoeff ψ (z, k, b) ^ 2) using 1
    simp only [Fintype.sum_bool, noiseCoeff, ite_true, Bool.false_eq_true, ite_false]
    linarith [Complex.sq_norm_sub_sq_re (localCoeff z k ψ)]
  have hk : ∀ z, HasSum (fun k => ‖localCoeff z k ψ‖ ^ 2) (∫ x, (ψ x * cubeBump z x) ^ 2) := by
    intro z
    refine hasSum_sq_norm_fourierCoeff (fun i => (z i : ℝ) / 2 - 1 / 4)
      (hψ.mul (contDiff_cubeBump z).continuous).measurable (C := C) (fun x => ?_) (fun x hx => ?_)
    · rw [abs_mul]
      calc |ψ x| * |cubeBump z x| ≤ C * 1 :=
            mul_le_mul (hC x) (abs_cubeBump_le_one z x) (abs_nonneg _)
              ((norm_nonneg _).trans (hC x))
        _ = C := mul_one C
    · obtain ⟨i, hi⟩ := hx
      rw [cubeBump_eq_zero ⟨i, fun h => hi ⟨by linarith [h.1], by linarith [h.2]⟩⟩, mul_zero]
  -- the outer sum over the cubes is finite
  have hz : HasSum (fun z => ∫ x, (ψ x * cubeBump z x) ^ 2) (∫ x, ψ x ^ 2) := by
    have h0 : ∀ z ∉ cubesMeeting K, ∫ x, (ψ x * cubeBump z x) ^ 2 = 0 := by
      intro z hz
      have : ∀ x, ψ x * cubeBump z x = 0 := by
        intro x
        by_cases hx : x ∈ (K : Set E)
        · have : cubeBump z x = 0 := by
            by_contra hne
            exact hz ((Set.Finite.mem_toFinset _).2 ⟨x, hx, hne⟩)
          rw [this, mul_zero]
        · rw [hK x hx, zero_mul]
      simp [this]
    have hint : ∀ z, Integrable fun x => (ψ x * cubeBump z x) ^ 2 := fun z =>
      ((hψ.mul (contDiff_cubeBump z).continuous).pow 2).integrable_of_hasCompactSupport
        ((hasCompactSupport_cubeBump z).mono fun x hx h => hx (by simp [h]))
    have hsum : ∑ z ∈ cubesMeeting K, ∫ x, (ψ x * cubeBump z x) ^ 2 = ∫ x, ψ x ^ 2 := by
      rw [← integral_finsetSum _ fun z _ => hint z]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [mul_pow, ← Finset.mul_sum]
      by_cases hx : x ∈ (K : Set E)
      · have h2 : ∀ z ∉ cubesMeeting K, cubeBump z x ^ 2 = 0 := fun z hz => by
          have : cubeBump z x = 0 := by
            by_contra hne
            exact hz ((Set.Finite.mem_toFinset _).2 ⟨x, hx, hne⟩)
          simp [this]
        rw [(hasSum_sum_of_ne_finset_zero h2).unique (hasSum_cubeBump_sq x), mul_one]
      · simp [hK x hx]
    exact hsum ▸ hasSum_sum_of_ne_finset_zero h0
  exact hasSum_prod_of_nonneg (fun _ => sq_nonneg _)
    (fun z => hasSum_prod_of_nonneg (fun _ => sq_nonneg _) (hb z) (hk z)) hz

/-! ### Bounds on `𝓓_K` -/

section SupportedIn

variable {K : TopologicalSpace.Compacts E}

variable (K) in
/-- Multiplication by the cube bump `χ_z` on `𝓓_K(E, ℝ)`. -/
noncomputable def cubeMulCLM (z : Coord E → ℤ) : 𝓓_{K}(E, ℝ) →L[ℝ] 𝓓_{K}(E, ℝ) :=
  ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (contDiff_cubeBump z)

omit [MeasurableSpace E] [BorelSpace E] in
theorem cubeMulCLM_apply (z : Coord E → ℤ) (φ : 𝓓_{K}(E, ℝ)) (x : E) :
    cubeMulCLM K z φ x = φ x * cubeBump z x := by
  simp [cubeMulCLM]

variable (K) in
/-- The bound `B_z(φ) = |K| N₀(decayCLM K n (φ χ_z))`. -/
noncomputable def cubeBound (z : Coord E → ℤ) (φ : 𝓓_{K}(E, ℝ)) : ℝ :=
  volume.real (K : Set E) *
    ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K 0 (decayCLM K (decayExp E) (cubeMulCLM K z φ))

theorem cubeBound_nonneg (z : Coord E → ℤ) (φ : 𝓓_{K}(E, ℝ)) : 0 ≤ cubeBound K z φ :=
  mul_nonneg measureReal_nonneg (apply_nonneg _ _)

variable (K) in
theorem continuous_cubeBound (z : Coord E → ℤ) : Continuous (cubeBound K z) :=
  continuous_const.mul ((continuous_seminorm_zero K).comp
    ((decayCLM K (decayExp E)).continuous.comp (cubeMulCLM K z).continuous))

theorem cubeBound_zero (z : Coord E → ℤ) : cubeBound K z 0 = 0 := by
  simp [cubeBound]

theorem norm_localCoeff_le (z k : Coord E → ℤ) (φ : 𝓓_{K}(E, ℝ)) :
    ‖localCoeff z k φ‖ ≤ freqWeight k * cubeBound K z φ := by
  have h := norm_fourierCoeff_le_decay k (decayExp E) (cubeMulCLM K z φ)
  rw [fourierCoeff_congr k (cubeMulCLM_apply z φ)] at h
  exact h

/-- **The bound on the terms**: `|aⱼ(φ) ωⱼ| ≤ ∑_{z ∈ Z_K} B_z(φ) |ωⱼ| u_z(j)` for `φ ∈ 𝓓_K`. -/
theorem abs_noiseCoeff_mul_le (φ : 𝓓_{K}(E, ℝ)) (ω : NoiseIndex E → ℝ) (j : NoiseIndex E) :
    |noiseCoeff φ j * ω j| ≤
      ∑ z ∈ cubesMeeting K, cubeBound K z φ * (|ω j| * cubeWeight z j) := by
  have hnn : ∀ z ∈ cubesMeeting K, 0 ≤ cubeBound K z φ * (|ω j| * cubeWeight z j) :=
    fun z _ => mul_nonneg (cubeBound_nonneg z φ)
      (mul_nonneg (abs_nonneg _) (cubeWeight_nonneg z j))
  obtain ⟨z, k, b⟩ := j
  by_cases hz : z ∈ cubesMeeting K
  · refine le_trans ?_ (Finset.single_le_sum hnn hz)
    rw [abs_mul, cubeWeight, ite_eq_left rfl]
    calc |noiseCoeff φ (z, k, b)| * |ω (z, k, b)|
        ≤ (freqWeight k * cubeBound K z φ) * |ω (z, k, b)| :=
          mul_le_mul_of_nonneg_right
            ((abs_noiseCoeff_le _ _).trans (norm_localCoeff_le z k φ)) (abs_nonneg _)
      _ = _ := by ring
  · have h0 : noiseCoeff φ (z, k, b) = 0 := by
      simp only [noiseCoeff, localCoeff_eq_zero (fun x hx => φ.zero_on_compl hx) hz k]
      split_ifs <;> simp
    rw [h0, zero_mul, abs_zero]
    exact Finset.sum_nonneg hnn

/-- On the good set, the series `∑ⱼ aⱼ(φ) ωⱼ` converges absolutely. -/
theorem summable_noiseCoeff_mul (φ : 𝓓_{K}(E, ℝ)) {ω : NoiseIndex E → ℝ} (hω : ω ∈ goodSet) :
    Summable fun j => noiseCoeff φ j * ω j :=
  Summable.of_norm_bounded (summable_sum fun z _ => (hω z).mul_left (cubeBound K z φ))
    fun j => (Real.norm_eq_abs _).trans_le (abs_noiseCoeff_mul_le φ ω j)

/-- On the good set, `|∑ⱼ aⱼ(φ) ωⱼ| ≤ ∑_{z ∈ Z_K} B_z(φ) ∑ⱼ |ωⱼ| u_z(j)`. -/
theorem abs_tsum_noiseCoeff_mul_le (φ : 𝓓_{K}(E, ℝ)) {ω : NoiseIndex E → ℝ}
    (hω : ω ∈ goodSet) :
    |∑' j, noiseCoeff φ j * ω j| ≤
      ∑ z ∈ cubesMeeting K, cubeBound K z φ * ∑' j, |ω j| * cubeWeight z j := by
  rw [← Real.norm_eq_abs]
  exact tsum_of_norm_bounded (hasSum_sum fun z _ => (hω z).hasSum.mul_left (cubeBound K z φ))
    fun j => (Real.norm_eq_abs _).trans_le (abs_noiseCoeff_mul_le φ ω j)

end SupportedIn

/-- On the good set, the series converges absolutely for every smooth compactly supported `ψ`. -/
theorem summable_noiseCoeff_mul_of_contDiff {ψ : E → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) {ω : NoiseIndex E → ℝ} (hω : ω ∈ goodSet) :
    Summable fun j => noiseCoeff ψ j * ω j :=
  summable_noiseCoeff_mul
    (ContDiffMapSupportedIn.of_support_subset (K := ⟨tsupport ψ, hc⟩) hψ (subset_tsupport ψ)) hω

end IsotropicVariance.Infra.WhiteNoise
