/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Induction.Tools
public import IsotropicVariance.Paper.Proofs.Profiles.Basic
public import IsotropicVariance.Infra.TimeConstant.Limit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Mean tools for Lemma `lem:smallmean`

* `integral_passTime_eq_mean`, `evariance_passTime_eq`: isotropy of `T(u, v)`, from
  `Profiles.map_passTime_eq_map_TRV`.
* `variance_le_two_mul_add`: the variance split.
* `abs_pow_le_interp`, `add_three_pow_le`: pointwise interpolation and convexity.
* `eventually_log_pow_le`, `eventually_sqrt_mul_log_le`: logarithms against powers.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

namespace IsotropicVariance.Paper.Proofs.SmallMean

variable {m : ℕ}

theorem integral_passTime_eq_mean (hm : 1 ≤ m) (X : Setting m) (u v : Pt m) :
    ∫ ω, X.passTime ω u v ∂X.P = X.mean (dist u v) := by
  have h := Profiles.map_passTime_eq_map_TRV (X := X) hm u v
  have h1 := integral_map (μ := X.P) (Profiles.aemeasurable_passTime u v)
    (f := id) aestronglyMeasurable_id
  have h2 := integral_map (μ := X.P) (Infra.TimeConstant.integrable_TRV X (dist u v)).aemeasurable
    (f := id) aestronglyMeasurable_id
  rw [h] at h1
  unfold Setting.mean
  simp only [id] at h1 h2
  rw [← h1, h2]

theorem evariance_passTime_eq (hm : 1 ≤ m) (X : Setting m) (u v : Pt m) :
    evariance (fun ω => X.passTime ω u v) X.P = evariance (X.TRV (dist u v)) X.P :=
  Induction.evariance_eq_of_map_eq (Profiles.aemeasurable_passTime u v)
    (Infra.TimeConstant.integrable_TRV X _).aemeasurable (Profiles.map_passTime_eq_map_TRV hm u v)

/-- The variance of `D` is at most `2 Var T + 2 E(D − T)²`. -/
theorem variance_le_two_mul_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D T : Ω → ℝ} (hD : MemLp D 2 P) (hT : MemLp T 2 P) :
    variance D P ≤ 2 * variance T P + 2 * ∫ ω, (D ω - T ω) ^ 2 ∂P := by
  have hE : MemLp (fun ω => D ω - T ω) 2 P := hD.sub hT
  have hDi : Integrable D P := hD.integrable (by norm_num)
  have hTi : Integrable T P := hT.integrable (by norm_num)
  have hEi : Integrable (fun ω => D ω - T ω) P := hE.integrable (by norm_num)
  have hvD : variance D P = ∫ ω, (D ω - P[D]) ^ 2 ∂P := variance_eq_integral hD.aemeasurable
  have hvT : variance T P = ∫ ω, (T ω - P[T]) ^ 2 ∂P := variance_eq_integral hT.aemeasurable
  have hvE : variance (fun ω => D ω - T ω) P
      = ∫ ω, ((D ω - T ω) - P[fun ω => D ω - T ω]) ^ 2 ∂P := variance_eq_integral hE.aemeasurable
  have hvle : variance (fun ω => D ω - T ω) P ≤ ∫ ω, (D ω - T ω) ^ 2 ∂P := by
    have := variance_le_expectation_sq (μ := P) (X := fun ω => D ω - T ω)
      hE.aestronglyMeasurable
    simpa [Pi.pow_apply] using this
  have hEm : P[fun ω => D ω - T ω] = P[D] - P[T] := integral_sub hDi hTi
  have ha : Integrable (fun ω => (T ω - P[T]) ^ 2) P := by
    have := (hT.sub (memLp_const (P[T]))).integrable_sq
    simpa using this
  have hb : Integrable (fun ω => ((D ω - T ω) - P[fun ω => D ω - T ω]) ^ 2) P :=
    (hE.sub (memLp_const _)).integrable_sq
  have hpt : ∀ ω, (D ω - P[D]) ^ 2 ≤ 2 * (T ω - P[T]) ^ 2
      + 2 * ((D ω - T ω) - P[fun ω => D ω - T ω]) ^ 2 := by
    intro ω
    rw [hEm]
    nlinarith [sq_nonneg ((T ω - P[T]) - ((D ω - T ω) - (P[D] - P[T])))]
  have hint : ∫ ω, (D ω - P[D]) ^ 2 ∂P ≤ ∫ ω, (2 * (T ω - P[T]) ^ 2
      + 2 * ((D ω - T ω) - P[fun ω => D ω - T ω]) ^ 2) ∂P :=
    integral_mono (by simpa using (hD.sub (memLp_const (P[D]))).integrable_sq)
      ((ha.const_mul 2).add (hb.const_mul 2)) hpt
  rw [integral_add (ha.const_mul 2) (hb.const_mul 2), integral_const_mul,
    integral_const_mul, ← hvT, ← hvE] at hint
  linarith

/-- Interpolation between `L²` and `L^{2p}`, pointwise. -/
theorem abs_pow_le_interp (y : ℝ) {l : ℝ} (hl : 0 < l) {p : ℕ} (hp : 2 ≤ p) :
    |y| ^ p ≤ l ^ (p - 2) * y ^ 2 + |y| ^ (2 * p) / l ^ p := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  have hlp : 0 < l ^ (k + 2) := by positivity
  have e : k + 2 - 2 = k := by omega
  rw [e]
  have h2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  rw [h2]
  have ha : 0 ≤ |y| := abs_nonneg y
  have t1 : 0 ≤ l ^ k * |y| ^ 2 := by positivity
  have t2 : 0 ≤ |y| ^ (2 * (k + 2)) / l ^ (k + 2) := by positivity
  rcases le_total |y| l with h | h
  · calc |y| ^ (k + 2) = |y| ^ k * |y| ^ 2 := pow_add _ _ _
      _ ≤ l ^ k * |y| ^ 2 := by gcongr
      _ ≤ _ := by linarith
  · refine le_trans ?_ (le_add_of_nonneg_left t1)
    rw [le_div_iff₀ hlp]
    calc |y| ^ (k + 2) * l ^ (k + 2) ≤ |y| ^ (k + 2) * |y| ^ (k + 2) := by gcongr
      _ = |y| ^ (2 * (k + 2)) := by rw [← pow_add]; congr 1; ring

/-- Convexity of the power: `(a + b + c)^p ≤ 3^{p−1}(a^p + b^p + c^p)`. -/
theorem add_three_pow_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {p : ℕ}
    (hp : 1 ≤ p) : (a + b + c) ^ p ≤ 3 ^ (p - 1) * (a ^ p + b ^ p + c ^ p) := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ p) := convexOn_pow p
  have h := hconv.map_sum_le (t := Finset.univ) (w := fun _ : Fin 3 => (1 / 3 : ℝ))
    (p := ![a, b, c]) (by intro i _; norm_num) (by simp)
    (by intro i _; fin_cases i <;> simpa)
  simp [Fin.sum_univ_three] at h
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have e : (a + b + c) = 3 * ((3⁻¹ * a + 3⁻¹ * b + 3⁻¹ * c)) := by ring
  rw [e, mul_pow]
  simp only [Nat.add_sub_cancel]
  have h3 : (3:ℝ) ^ (k + 1) = 3 ^ k * 3 := pow_succ _ _
  have : (3⁻¹ * a + 3⁻¹ * b + 3⁻¹ * c) ^ (k + 1) ≤ 3⁻¹ * a ^ (k + 1) + 3⁻¹ * b ^ (k + 1) + 3⁻¹ * c ^ (k + 1) := by
    simpa [mul_comm] using h
  calc (3:ℝ) ^ (k + 1) * (3⁻¹ * a + 3⁻¹ * b + 3⁻¹ * c) ^ (k + 1)
      ≤ 3 ^ (k + 1) * (3⁻¹ * a ^ (k + 1) + 3⁻¹ * b ^ (k + 1) + 3⁻¹ * c ^ (k + 1)) := by gcongr
    _ = _ := by rw [h3]; ring

/-- **Logarithms against powers**. -/
theorem eventually_log_pow_le (C : ℝ) (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ s : ℝ in atTop, C * Real.log (2 + s) ^ k ≤ s ^ a := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := (tendsto_rpow_atTop ha).eventually_ge_atTop (C * 1)
    filter_upwards [this] with s hs
    simpa using hs
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : 0 < a / k := div_pos ha hkpos
  have hlo := isLittleO_log_rpow_atTop hb
  have hbig : (fun s : ℝ => Real.log (2 + s)) =O[atTop] fun s => Real.log s := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    have h0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
    have h1 : 0 ≤ Real.log (2 + s) := Real.log_nonneg (by linarith)
    have h2 : Real.log (2 + s) ≤ Real.log (s * s) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_mul (by linarith) (by linarith)] at h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg h1]
    linarith
  have hpow := (hbig.trans_isLittleO hlo).pow hk
  have hconv : (fun s : ℝ => (s ^ (a / k)) ^ k) =ᶠ[atTop] fun s => s ^ a := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    field_simp
  have hfin := (hpow.congr' Filter.EventuallyEq.rfl hconv).const_mul_left C
  filter_upwards [hfin.bound one_pos, eventually_gt_atTop (0 : ℝ)] with s hs hs0
  have h := le_of_eq_of_le (Real.norm_eq_abs _).symm hs
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hs0.le a)] at h
  exact (le_abs_self _).trans h

/-- The same with a square root inside. -/
theorem eventually_sqrt_mul_log_le (C : ℝ) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ s : ℝ in atTop, C * Real.sqrt (s * Real.log (2 + s)) ≤ s / D := by
  filter_upwards [eventually_log_pow_le (C ^ 2 * D ^ 2) 1 one_pos, eventually_ge_atTop (1 : ℝ)]
    with s hs hs1
  rw [pow_one, Real.rpow_one] at hs
  have hs0 : 0 ≤ s := by linarith
  have hlog : 0 ≤ Real.log (2 + s) := Real.log_nonneg (by linarith)
  have hx : 0 ≤ s * Real.log (2 + s) := mul_nonneg hs0 hlog
  have hsD : 0 ≤ s / D := by positivity
  rcases le_total C 0 with hC | hC
  · have : C * Real.sqrt (s * Real.log (2 + s)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC (Real.sqrt_nonneg _)
    linarith
  · have e : C * Real.sqrt (s * Real.log (2 + s)) = Real.sqrt (C ^ 2 * (s * Real.log (2 + s))) := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
    rw [e, Real.sqrt_le_iff]
    refine ⟨hsD, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs hs0]

end IsotropicVariance.Paper.Proofs.SmallMean
