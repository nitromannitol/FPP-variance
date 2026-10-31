/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Statements.Main.LintegralExpPassageTimeLe
public import IsotropicVariance.Statements.Main.LintegralExpPassageTimeLeOfIsPoissonProcess
public import IsotropicVariance.Statements.Main.LintegralExpPassageTimeLeOfIsWhiteNoise
import IsotropicVariance.Paper.Proofs.Profiles.Basic

/-!
# The variance bound stated after Theorem `thm:main`, and the abstract

The paper remarks that Theorem `thm:main` implies `Var[T(0, x)] ≤ 2 C² |x|^{1-ε}` for `|x| ≥ 1`.
This file proves that sentence, with the same `ε` and `C`, in the three settings of Theorems
`thm:main` and `thm:general`, and then the two bounds of the abstract of the paper,
`E[exp(|T_n − μ n| / n^{(1−ε)/2})] ≤ C` and `Var T_n ≤ C n^{1−ε}`, for a smaller `ε`.

* `evariance_le_of_lintegral_exp_le`: if `E[exp(|X − c| / s)] ≤ 2`, then `Var X ≤ 2 s²`. Indeed
  `e^t ≥ 1 + t² / 2` for `t ≥ 0` gives `E[(X − c)²] ≤ 2 s²`, and the variance is at most the second
  moment about any constant.
* `evariance_le_of_lintegral_exp_rpow_le`: the case `s = C r^{(1−ε)/2}`, which is the scale of
  Theorems `thm:main` and `thm:general`.
* `variance_passageTime_le_two_sq`, `variance_passageTime_le_two_sq_of_isWhiteNoise` and
  `variance_passageTime_le_two_sq_of_isPoissonProcess`: the conclusions of
  `IsotropicVariance.lintegral_exp_passageTime_le`,
  `IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise` and
  `IsotropicVariance.lintegral_exp_passageTime_le_of_isPoissonProcess`, together with the variance
  bound, for the same `μ`, `ε` and `C`.
* `exists_abstract_bounds`: the passage from these conclusions to the two bounds of the abstract,
  for `n ≥ 1`. With `ε' = ε/2`, for `n ≥ C^{4/ε}` the scale of the abstract is at least that of the
  theorem. For smaller `n`, `0 ≤ T_n ≤ b n` for an upper bound `b` of the density, so the variable
  in the exponential is bounded.
* `abstract_bounds_passageTime`, `abstract_bounds_passageTime_of_isWhiteNoise` and
  `abstract_bounds_passageTime_of_isPoissonProcess`: the two bounds of the abstract, in the three
  settings.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology Distributions

namespace IsotropicVariance.Paper.Closing

/-- A random variable whose exponential moment on the scale `s` about a constant `c` is at most
`2` has variance at most `2 s²`. -/
theorem evariance_le_of_lintegral_exp_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) {c s : ℝ} (hs : 0 < s)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - c| / s)) ∂P ≤ 2) :
    evariance X P ≤ ENNReal.ofReal (2 * s ^ 2) := by
  have hs2 : 0 < 2 * s ^ 2 := by positivity
  have hY : AEMeasurable (fun ω => X ω - c) P := hX.sub_const c
  have hpt : ∀ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) + 1 ≤
      ENNReal.ofReal (Real.exp (|X ω - c| / s)) := by
    intro ω
    have ht : 0 ≤ |X ω - c| / s := div_nonneg (abs_nonneg _) hs.le
    have hq := Real.quadratic_le_exp_of_nonneg ht
    have hsq : (|X ω - c| / s) ^ 2 / 2 = (X ω - c) ^ 2 / (2 * s ^ 2) := by
      rw [div_pow, sq_abs, div_div, mul_comm (s ^ 2)]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (div_nonneg (sq_nonneg _) hs2.le) zero_le_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hq, hsq, ht])
  have hmass : ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P ≤ 1 := by
    have hadd : ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P + 1 ≤ 1 + 1 := by
      calc ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P + 1
          = ∫⁻ ω, (ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) + 1) ∂P := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - c| / s)) ∂P := lintegral_mono hpt
        _ ≤ 2 := h
        _ = 1 + 1 := one_add_one_eq_two.symm
    exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 hadd
  have hsecond : ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P ≤ ENNReal.ofReal (2 * s ^ 2) := by
    calc ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P
        = ∫⁻ ω, ENNReal.ofReal (2 * s ^ 2) *
            ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← ENNReal.ofReal_mul hs2.le, mul_div_cancel₀ _ hs2.ne']
      _ = ENNReal.ofReal (2 * s ^ 2) *
            ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2 / (2 * s ^ 2)) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * s ^ 2) * 1 := mul_le_mul_right hmass _
      _ = ENNReal.ofReal (2 * s ^ 2) := mul_one _
  have hint : Integrable (fun ω => (X ω - c) ^ 2) P := by
    refine ⟨(hY.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    exact hsecond.trans_lt ENNReal.ofReal_lt_top
  have hYL : MemLp (fun ω => X ω - c) 2 P :=
    (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).2 hint
  have hXL : MemLp X 2 P := by
    have hsum := hYL.add (memLp_const c)
    have hfun : (fun ω => X ω - c) + (fun _ => c) = X := by
      funext ω
      exact sub_add_cancel (X ω) c
    rwa [hfun] at hsum
  rw [← hXL.ofReal_variance_eq, ← variance_sub_const hX.aestronglyMeasurable c]
  calc ENNReal.ofReal (variance (fun ω => X ω - c) P)
      ≤ ENNReal.ofReal (∫ ω, (X ω - c) ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (variance_le_expectation_sq hY.aestronglyMeasurable)
    _ = ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P :=
        ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg _)
    _ ≤ ENNReal.ofReal (2 * s ^ 2) := hsecond

/-- The case `s = C r^{(1−ε)/2}` of `evariance_le_of_lintegral_exp_le`, for `r ≥ 1`: the variance
is at most `2 C² r^{1-ε}`. -/
theorem evariance_le_of_lintegral_exp_rpow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) {c C ε r : ℝ} (hC : 0 < C)
    (hr : 1 ≤ r)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - c| / (C * r ^ ((1 - ε) / 2)))) ∂P ≤ 2) :
    evariance X P ≤ ENNReal.ofReal (2 * C ^ 2 * r ^ (1 - ε)) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hs : 0 < C * r ^ ((1 - ε) / 2) := mul_pos hC (Real.rpow_pos_of_pos (by linarith only [hr]) _)
  have hsq : (r ^ ((1 - ε) / 2)) ^ 2 = r ^ (1 - ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0]
    norm_num
  have hb := evariance_le_of_lintegral_exp_le hX hs h
  rwa [mul_pow, hsq, ← mul_assoc] at hb

/-- **The variance bound after Theorem `thm:main`.** Under the hypotheses of Theorem `thm:main`,
the `μ`, `ε` and `C` of its conclusion also satisfy `Var[T(0, x)] ≤ 2 C² |x|^{1-ε}` for every point
`x` with `|x| ≥ 1`. -/
theorem variance_passageTime_le_two_sq {m : ℕ} (hm : 1 ≤ m) {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ =>
        t⁻¹ * ∫ ω, passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁) ∂P) atTop (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (convolutionDensity χ ψ (W ω)) 0 x - μ * ‖x‖| /
                (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 ∧
          evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ≤
            ENNReal.ofReal (2 * C ^ 2 * ‖x‖ ^ (1 - ε)) := by
  obtain ⟨μ, hμ, ε, hε, C, hC, hb⟩ := IsotropicVariance.lintegral_exp_passageTime_le hm hW χ
    hχ_radial hχ_support ψ hψ a b ha hψ_bounds
  exact ⟨μ, hμ, ε, hε, C, hC, fun x hx => ⟨(hb x hx).1, (hb x hx).2,
    evariance_le_of_lintegral_exp_rpow_le (hb x hx).1 hC hx (hb x hx).2⟩⟩

/-- **The variance bound after Theorem `thm:general`, for Gaussian white noise.** Under the
hypotheses of Theorem `thm:general`, the `μ`, `ε` and `C` of its conclusion also satisfy
`Var[T(0, x)] ≤ 2 C² |x|^{1-ε}` for every point `x` with `|x| ≥ 1`. -/
theorem variance_passageTime_le_two_sq_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, passageTime (ρ (W ω)) 0 (t • e₁) ∂P) atTop
        (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (ρ (W ω)) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 ∧
          evariance (fun ω => passageTime (ρ (W ω)) 0 x) P ≤
            ENNReal.ofReal (2 * C ^ 2 * ‖x‖ ^ (1 - ε)) := by
  obtain ⟨μ, hμ, ε, hε, C, hC, hb⟩ :=
    IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise hm hW hρ
  exact ⟨μ, hμ, ε, hε, C, hC, fun x hx => ⟨(hb x hx).1, (hb x hx).2,
    evariance_le_of_lintegral_exp_rpow_le (hb x hx).1 hC hx (hb x hx).2⟩⟩

/-- **The variance bound after Theorem `thm:general`, for a homogeneous Poisson process.** Under
the hypotheses of Theorem `thm:general`, the `μ`, `ε` and `C` of its conclusion also satisfy
`Var[T(0, x)] ≤ 2 C² |x|^{1-ε}` for every point `x` with `|x| ≥ 1`. -/
theorem variance_passageTime_le_two_sq_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, passageTime (ρ (η ω)) 0 (t • e₁) ∂P) atTop
        (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (ρ (η ω)) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 ∧
          evariance (fun ω => passageTime (ρ (η ω)) 0 x) P ≤
            ENNReal.ofReal (2 * C ^ 2 * ‖x‖ ^ (1 - ε)) := by
  obtain ⟨μ, hμ, ε, hε, C, hC, hb⟩ :=
    IsotropicVariance.lintegral_exp_passageTime_le_of_isPoissonProcess hm hlam hη hρ
  exact ⟨μ, hμ, ε, hε, C, hC, fun x hx => ⟨(hb x hx).1, (hb x hx).2,
    evariance_le_of_lintegral_exp_rpow_le (hb x hx).1 hC hx (hb x hx).2⟩⟩

/-! ## The abstract -/

/-- **From the theorems to the abstract**. If the passage times `T(0, x)` of a
density bounded above satisfy `E[exp(|T(0, x) − μ|x|| / (C |x|^{(1−ε)/2}))] ≤ 2` for `|x| ≥ 1`, then
there are `ε' > 0` and `C' < ∞` such that, for `T_n = T(0, n e₁)` and every real `n ≥ 1`,
`E[exp(|T_n − μ n| / n^{(1−ε')/2})] ≤ C'` and `Var T_n ≤ C' n^{1−ε'}`. -/
theorem exists_abstract_bounds {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {σ : Ω → Pt m → ℝ} {B μ ε C : ℝ} (hB : ∀ ω x, σ ω x ≤ B)
    (hε : 0 < ε) (hC : 0 < C)
    (h : ∀ x : Pt m, 1 ≤ ‖x‖ → AEMeasurable (fun ω => passageTime (σ ω) 0 x) P ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp
        (|passageTime (σ ω) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2) :
    ∃ ε' : ℝ, 0 < ε' ∧ ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℝ, 1 ≤ n →
      AEMeasurable (fun ω => passageTime (σ ω) 0 (n • e₁)) P ∧
        ∫⁻ ω, ENNReal.ofReal (Real.exp
            (|passageTime (σ ω) 0 (n • e₁) - μ * n| / n ^ ((1 - ε') / 2))) ∂P ≤
          ENNReal.ofReal C' ∧
        evariance (fun ω => passageTime (σ ω) 0 (n • e₁)) P ≤
          ENNReal.ofReal (C' * n ^ (1 - ε')) := by
  set B' := max B 0
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hBB' : ∀ ω x, σ ω x ≤ B' := fun ω x => (hB ω x).trans (le_max_left _ _)
  set n₀ : ℝ := max 1 (C ^ (4 / ε))
  have hn₀1 : 1 ≤ n₀ := le_max_left _ _
  have hn₀0 : 0 < n₀ := zero_lt_one.trans_le hn₀1
  set a : ℝ := (1 - ε / 2) / 2 with ha
  set D : ℝ := (B' + |μ|) * n₀ * n₀ ^ |a|
  set C' : ℝ := max (max 2 (Real.exp D)) (2 * C ^ 2)
  have h2C' : (2 : ℝ) ≤ C' := (le_max_left _ _).trans (le_max_left _ _)
  have hEC' : Real.exp D ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨ε / 2, half_pos hε, C', zero_lt_two.trans_le h2C', fun n hn => ?_⟩
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hnorm : ‖n • (e₁ : Pt m)‖ = n := by
    rw [norm_smul, norm_e₁, mul_one, Real.norm_of_nonneg hn0.le]
  obtain ⟨hmeas, hint⟩ := h (n • e₁) (hnorm.symm ▸ hn)
  rw [hnorm] at hint
  refine ⟨hmeas, ?_, ?_⟩
  · rcases le_or_gt n₀ n with hle | hlt
    · -- large `n`: the scale of the abstract is at least that of the theorem
      have hCn : C ≤ n ^ (ε / 4) := by
        have hpow : (C ^ (4 / ε)) ^ (ε / 4) = C := by
          rw [← Real.rpow_mul hC.le, show 4 / ε * (ε / 4) = 1 by field_simp, Real.rpow_one]
        calc C = (C ^ (4 / ε)) ^ (ε / 4) := hpow.symm
          _ ≤ n ^ (ε / 4) := Real.rpow_le_rpow (Real.rpow_nonneg hC.le _)
            ((le_max_right _ _).trans hle) (by positivity)
      have hsplit : n ^ a = n ^ (ε / 4) * n ^ ((1 - ε) / 2) := by
        rw [← Real.rpow_add hn0, ha]
        congr 1
        ring
      have hscale : C * n ^ ((1 - ε) / 2) ≤ n ^ a := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right hCn (Real.rpow_nonneg hn0.le _)
      refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
        (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hscale))) (hint.trans ?_)
      rw [← ENNReal.ofReal_ofNat 2]
      exact ENNReal.ofReal_le_ofReal h2C'
    · -- small `n`: the variable in the exponential is bounded
      have hinv : (n ^ a)⁻¹ ≤ n₀ ^ |a| := by
        rw [← Real.rpow_neg hn0.le]
        calc n ^ (-a) ≤ n ^ |a| := Real.rpow_le_rpow_of_exponent_le hn (neg_le_abs a)
          _ ≤ n₀ ^ |a| := Real.rpow_le_rpow hn0.le hlt.le (abs_nonneg a)
      have hpt : ∀ ω, |passageTime (σ ω) 0 (n • e₁) - μ * n| / n ^ a ≤ D := fun ω => by
        have h0 := Proofs.Profiles.passageTime_nonneg (σ ω) 0 (n • (e₁ : Pt m))
        have h1 := Proofs.Profiles.passageTime_le_mul_dist (hBB' ω) hB0 0 (n • (e₁ : Pt m))
        rw [dist_zero_left, hnorm] at h1
        have habs : |passageTime (σ ω) 0 (n • e₁) - μ * n| ≤ (B' + |μ|) * n₀ := by
          calc |passageTime (σ ω) 0 (n • e₁) - μ * n|
              ≤ |passageTime (σ ω) 0 (n • e₁)| + |μ * n| := abs_sub _ _
            _ = passageTime (σ ω) 0 (n • e₁) + |μ| * n := by
                rw [abs_of_nonneg h0, abs_mul, abs_of_pos hn0]
            _ ≤ (B' + |μ|) * n := by linarith only [h1]
            _ ≤ (B' + |μ|) * n₀ := mul_le_mul_of_nonneg_left hlt.le (by positivity)
        rw [div_eq_mul_inv]
        exact mul_le_mul habs hinv (by positivity) (by positivity)
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp
            (|passageTime (σ ω) 0 (n • e₁) - μ * n| / n ^ a)) ∂P
          ≤ ∫⁻ _, ENNReal.ofReal (Real.exp D) ∂P :=
            lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hpt ω))
        _ = ENNReal.ofReal (Real.exp D) := by simp
        _ ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hEC'
  · refine (evariance_le_of_lintegral_exp_rpow_le hmeas hC hn hint).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hε])) (by positivity)
      (zero_lt_two.le.trans h2C')

/-- **The abstract of the paper**, for the density `ρ = ψ(χ∗W)` of Theorem
`thm:main`: for `T_n = T(0, n e₁)`, the time constant `μ` exists, and there are `ε > 0` and `C < ∞`
such that `E[exp(|T_n − μ n| / n^{(1−ε)/2})] ≤ C` and `Var T_n ≤ C n^{1−ε}` for every real
`n ≥ 1`. -/
theorem abstract_bounds_passageTime {m : ℕ} (hm : 1 ≤ m) {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ =>
        t⁻¹ * ∫ ω, passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁) ∂P) atTop (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, 1 ≤ n →
        AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (n • e₁)) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (convolutionDensity χ ψ (W ω)) 0 (n • e₁) - μ * n| /
                n ^ ((1 - ε) / 2))) ∂P ≤ ENNReal.ofReal C ∧
          evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (n • e₁)) P ≤
            ENNReal.ofReal (C * n ^ (1 - ε)) := by
  obtain ⟨μ, hμ, ε, hε, C, hC, hb⟩ := IsotropicVariance.lintegral_exp_passageTime_le hm hW χ
    hχ_radial hχ_support ψ hψ a b ha hψ_bounds
  exact ⟨μ, hμ, exists_abstract_bounds (σ := fun ω => convolutionDensity χ ψ (W ω)) (B := b)
    (fun _ _ => (hψ_bounds _).2) hε hC hb⟩

/-- **The abstract of the paper**, for a local density over Gaussian white noise
(Theorem `thm:general`). -/
theorem abstract_bounds_passageTime_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, passageTime (ρ (W ω)) 0 (t • e₁) ∂P) atTop
        (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, 1 ≤ n →
        AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 (n • e₁)) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (ρ (W ω)) 0 (n • e₁) - μ * n| / n ^ ((1 - ε) / 2))) ∂P ≤
            ENNReal.ofReal C ∧
          evariance (fun ω => passageTime (ρ (W ω)) 0 (n • e₁)) P ≤
            ENNReal.ofReal (C * n ^ (1 - ε)) := by
  obtain ⟨μ, hμ, ε, hε, C, hC, hb⟩ :=
    IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise hm hW hρ
  obtain ⟨_, B, -, hab⟩ := hρ.bounds
  exact ⟨μ, hμ, exists_abstract_bounds (σ := fun ω => ρ (W ω)) (B := B)
    (fun _ _ => (hab _ _).2) hε hC hb⟩

/-- **The abstract of the paper**, for a local density over a homogeneous Poisson
process (Theorem `thm:general`). -/
theorem abstract_bounds_passageTime_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, passageTime (ρ (η ω)) 0 (t • e₁) ∂P) atTop
        (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, 1 ≤ n →
        AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 (n • e₁)) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (ρ (η ω)) 0 (n • e₁) - μ * n| / n ^ ((1 - ε) / 2))) ∂P ≤
            ENNReal.ofReal C ∧
          evariance (fun ω => passageTime (ρ (η ω)) 0 (n • e₁)) P ≤
            ENNReal.ofReal (C * n ^ (1 - ε)) := by
  obtain ⟨μ, hμ, ε, hε, C, hC, hb⟩ :=
    IsotropicVariance.lintegral_exp_passageTime_le_of_isPoissonProcess hm hlam hη hρ
  obtain ⟨_, B, -, hab⟩ := hρ.bounds
  exact ⟨μ, hμ, exists_abstract_bounds (σ := fun ω => ρ (η ω)) (B := B)
    (fun _ _ => (hab _ _).2) hε hC hb⟩

end IsotropicVariance.Paper.Closing
