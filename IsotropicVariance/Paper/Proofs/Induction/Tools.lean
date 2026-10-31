/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Basic
public import IsotropicVariance.Infra.TimeConstant.Mean
public import IsotropicVariance.Paper.Defs.Scales

/-!
# Tools for Section `sec:completion`: stochastic bounds, variances, scales

* `isOs_one_of_le`: a variable bounded by `θ log 2` is `O_1(θ)`.
* `evariance_le_lintegral_sq_sub`: the variance is at most the second moment about any constant.
* `evariance_le_of_isOs_one`: `|X − c| ≤ O_1(θ)` gives `Var X ≤ 4θ²` (from `x² ≤ 2eˣ`).
* `evariance_eq_of_map_eq`: the variance depends only on the law.
* `abs_TRV_sub_le`: `|T_s − s| ≤ C s` on every outcome, with `C` from the bounds of the density.
* Elementary facts about `Q_s = A s^{1/2 − 1/K}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace IsotropicVariance.Paper.Proofs.Induction

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A variable bounded by `θ log 2` is `O_1(θ)`. -/
theorem isOs_one_of_le [IsProbabilityMeasure P] {θ : ℝ} {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hθ : 0 < θ) (hle : ∀ᵐ ω ∂P, X ω ≤ θ * Real.log 2) : Cited.IsOs P 1 θ X := by
  refine ⟨hX, ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ (1 : ℝ))) ∂P
      ≤ ∫⁻ _ω, ENNReal.ofReal 2 ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hle] with ω hω
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_one]
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have h1 : max (X ω) 0 / θ ≤ Real.log 2 := by
          rw [div_le_iff₀ hθ]
          exact max_le (by linarith) (by positivity)
        calc Real.exp (max (X ω) 0 / θ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 h1
          _ = 2 := Real.exp_log (by norm_num)
    _ = 2 := by simp

/-- The variance is at most the second moment about any constant. -/
theorem evariance_le_lintegral_sq_sub [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P)
    (c : ℝ) : evariance X P ≤ ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P := by
  have hXc : MemLp (fun ω => X ω - c) 2 P := hX.sub (memLp_const c)
  rw [← hX.ofReal_variance_eq, ← variance_sub_const hX.aestronglyMeasurable c]
  have hint : Integrable (fun ω => (X ω - c) ^ 2) P := hXc.integrable_sq
  calc ENNReal.ofReal (variance (fun ω => X ω - c) P)
      ≤ ENNReal.ofReal (∫ ω, (X ω - c) ^ 2 ∂P) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := variance_le_expectation_sq (μ := P) hXc.aestronglyMeasurable
        simpa only [Pi.pow_apply] using this
    _ = ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P :=
        ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg _)

/-- `x² ≤ 2eˣ` for `x ≥ 0`. -/
theorem sq_le_two_mul_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ 2 * Real.exp x := by
  have := Real.quadratic_le_exp_of_nonneg hx
  nlinarith

/-- **Variance from an `O_1` bound**: `|X − c| ≤ O_1(θ)` gives `Var X ≤ 4θ²`. -/
theorem evariance_le_of_isOs_one [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P)
    {c θ : ℝ} (hθ : 0 < θ) (h : Cited.IsOs P 1 θ fun ω => |X ω - c|) :
    evariance X P ≤ ENNReal.ofReal (4 * θ ^ 2) := by
  refine (evariance_le_lintegral_sq_sub hX c).trans ?_
  calc ∫⁻ ω, ENNReal.ofReal ((X ω - c) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * θ ^ 2) *
          ENNReal.ofReal (Real.exp ((max |X ω - c| 0 / θ) ^ (1 : ℝ))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_one, max_eq_left (abs_nonneg _)]
        have hx : 0 ≤ |X ω - c| / θ := div_nonneg (abs_nonneg _) hθ.le
        have h2 := sq_le_two_mul_exp hx
        rw [div_pow, div_le_iff₀ (by positivity), sq_abs] at h2
        nlinarith
    _ = ENNReal.ofReal (2 * θ ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((max |X ω - c| 0 / θ) ^ (1 : ℝ))) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * θ ^ 2) * 2 := by gcongr; exact h.2
    _ = ENNReal.ofReal (4 * θ ^ 2) := by
        rw [show (4 : ℝ) * θ ^ 2 = 2 * θ ^ 2 * 2 by ring,
          ENNReal.ofReal_mul' (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-- The variance of a random variable as an integral against its law. -/
theorem evariance_eq_lintegral_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : AEMeasurable f P) :
    evariance f P = ∫⁻ x, ENNReal.ofReal ((x - ∫ y, y ∂(P.map f)) ^ 2) ∂(P.map f) := by
  have h1 : (∫ y, y ∂(P.map f)) = ∫ x, f x ∂P := integral_map hf aestronglyMeasurable_id
  rw [h1, lintegral_map' (f := fun x => ENNReal.ofReal ((x - ∫ x, f x ∂P) ^ 2)) (by fun_prop) hf,
    evariance_eq_lintegral_ofReal]

/-- The variance of a random variable depends only on its law. -/
theorem evariance_eq_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {f : Ω → ℝ} {g : Ω' → ℝ} (hf : AEMeasurable f P)
    (hg : AEMeasurable g P') (h : P.map f = P'.map g) : evariance f P = evariance g P' := by
  rw [evariance_eq_lintegral_map hf, evariance_eq_lintegral_map hg, h]

/-- The integral of a function of a random variable depends only on its law. -/
theorem lintegral_comp_eq_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {f : Ω → ℝ} {g : Ω' → ℝ} (hf : AEMeasurable f P)
    (hg : AEMeasurable g P') (h : P.map f = P'.map g) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (f ω) ∂P = ∫⁻ ω, F (g ω) ∂P' := by
  rw [← lintegral_map' hF.aemeasurable hf, ← lintegral_map' hF.aemeasurable hg, h]

/-- The mean of a random variable depends only on its law. -/
theorem integral_eq_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {f : Ω → ℝ} {g : Ω' → ℝ} (hf : AEMeasurable f P)
    (hg : AEMeasurable g P') (h : P.map f = P'.map g) : ∫ ω, f ω ∂P = ∫ ω, g ω ∂P' :=
  calc ∫ ω, f ω ∂P = ∫ y, y ∂(P.map f) := (integral_map hf aestronglyMeasurable_id).symm
    _ = ∫ y, y ∂(P'.map g) := by rw [h]
    _ = ∫ ω, g ω ∂P' := integral_map hg aestronglyMeasurable_id

/-! ### The setting -/

section Setting

variable {m : ℕ} (X : Setting m)

/-- `T_s` has the deterministic bounds of the density. -/
theorem TRV_bounds : ∃ a b : ℝ, 0 < a ∧ ∀ s, 0 ≤ s → ∀ ω,
    a * s ≤ X.TRV s ω ∧ X.TRV s ω ≤ b * s := by
  obtain ⟨a, b, ha, hab⟩ := Infra.TimeConstant.setting_passTime_bounds X
  refine ⟨a, b, ha, fun s hs ω => ?_⟩
  have hd : dist (0 : Pt m) (s • e₁) = s := by
    simpa only [zero_smul, zero_sub, abs_neg, abs_of_nonneg hs] using
      Infra.TimeConstant.dist_smul_e₁ (m := m) 0 s
  simpa only [Setting.TRV, hd] using hab ω 0 (s • e₁)

/-- `|T_s − s| ≤ C s` on every outcome. -/
theorem abs_TRV_sub_le : ∃ C : ℝ, 0 < C ∧ ∀ s, 0 ≤ s → ∀ ω, |X.TRV s ω - s| ≤ C * s := by
  obtain ⟨a, b, ha, hab⟩ := TRV_bounds X
  refine ⟨|b| + 1, by positivity, fun s hs ω => ?_⟩
  have h0 : 0 ≤ X.TRV s ω := (mul_nonneg ha.le hs).trans (hab s hs ω).1
  have h1 : X.TRV s ω ≤ |b| * s := (hab s hs ω).2.trans
    (mul_le_mul_of_nonneg_right (le_abs_self b) hs)
  rw [abs_le]
  constructor <;> nlinarith

/-- `|T_s − s|` is almost everywhere measurable. -/
theorem aemeasurable_abs_TRV_sub (s : ℝ) : AEMeasurable (fun ω => |X.TRV s ω - s|) X.P :=
  continuous_abs.measurable.comp_aemeasurable
    ((Infra.TimeConstant.integrable_TRV X s).aemeasurable.sub_const s)

end Setting

/-! ### The scale `Q_s` -/

/-- The exponent `1/2 − 1/K` is positive for `K ≥ 10`. -/
theorem exponent_pos {K : ℕ} (hK : 10 ≤ K) : 0 < (1 : ℝ) / 2 - 1 / (K : ℝ) := by
  have : (10 : ℝ) ≤ K := by exact_mod_cast hK
  have : 1 / (K : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) this
  linarith

/-- `Q_s ≥ A` for `s ≥ 1`. -/
theorem le_Q {K : ℕ} (hK : 10 ≤ K) {A s : ℝ} (hA : 0 ≤ A) (hs : 1 ≤ s) : A ≤ Q K A s :=
  le_mul_of_one_le_right hA (Real.one_le_rpow hs (exponent_pos hK).le)

/-- `Q_t² = A² t^{1 − 2/K}`. -/
theorem Q_sq (K : ℕ) (A : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Q K A t ^ 2 = A ^ 2 * t ^ (1 - 2 / (K : ℝ)) := by
  rw [Q, mul_pow, ← Real.rpow_natCast (t ^ _), ← Real.rpow_mul ht]
  congr 2
  push_cast
  ring

end IsotropicVariance.Paper.Proofs.Induction
