/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.LabelsBlock
public import CurvatureVariance.Paper.Proofs.Gain.FAParams
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The functions of `L` in Lemma `lem:labels`

The quantities of the proof of Lemma `lem:labels` that depend only on `L` and on the constants,
never on `K`, `N`, `A`, the target, the subgradient, the slab, the offset or the block. The
exponent is `k = 8d` (`faExp`, `d = m + 1`).

* `labelLog L = log(2 + (L+1)^{2(d−1)})`: the logarithm of equation `eq:union` over the at most
  `(L+1)^{2(d−1)}` pairs of cubes covering `Γ_G`, of order `log(2+L)`.
* `labelD`, `labelMoment`: the moment of order `2k` of an `O₁(θ)` variable.
* `labelHolder`: `ε₁(L)`, the error of the Hölder step, `(π(L) · 2^{2k+1} E Y^{2k})^{1/(2k)}`.
* `labelClipError`: `ε₃(L)`, the clipping error `E[(Y − L⁴/2)₊^k]^{1/k}`, bounded by `‖Y²‖_k/(2L⁴)`.

`tendsto_labelHolder` and `tendsto_labelClipError`: these tend to zero. The first is the point of
the Hölder step: `π(L)` has size `L^{2(d−1)} L^{−4d}`, and the moment of the cancelled variable has
only the logarithm.
-/

@[expose] public section

open Filter Topology

namespace CurvatureVariance.Paper.Gain

/-- The logarithm of equation `eq:union` over the pairs of cubes covering `Γ_G`. -/
noncomputable def labelLog (m L : ℕ) : ℝ :=
  Real.log (2 + ((L : ℝ) + 1) ^ (2 * m))

/-- The constant `2 (1 + (2k)!)` of the moment of order `2k` of an `O₁` variable. -/
noncomputable def labelD (m : ℕ) : ℝ :=
  2 * (1 + ((2 * faExp m).factorial : ℝ))

/-- The bound `2 (1 + (2k)!) θ^{2k}` of the moment of order `2k` of an `O₁(θ)` variable. -/
noncomputable def labelMoment (m : ℕ) (θ : ℝ) : ℝ :=
  labelD m * θ ^ (2 * faExp m)

/-- `ε₁(L)`: the error of the Hölder step. -/
noncomputable def labelHolder (m : ℕ) (Cd CR θ : ℝ) (L : ℕ) : ℝ :=
  (labelLeaveProb m Cd CR L *
      (2 ^ (2 * faExp m) * (2 * labelMoment m (θ * labelLog m L)))) ^
    (1 / (2 * ((faExp m : ℕ) : ℝ)))

/-- `ε₃(L)`: the clipping error at the level `L⁴`. -/
noncomputable def labelClipError (m : ℕ) (θ : ℝ) (L : ℕ) : ℝ :=
  labelD m * (θ * labelLog m L) ^ 2 / (2 * (L : ℝ) ^ 4)

variable {m : ℕ}

theorem labelLog_pos (m L : ℕ) : 0 < labelLog m L := by
  unfold labelLog
  refine Real.log_pos ?_
  have : (0 : ℝ) ≤ ((L : ℝ) + 1) ^ (2 * m) := by positivity
  linarith

theorem one_le_labelD (m : ℕ) : 1 ≤ labelD m := by
  unfold labelD
  have : (0 : ℝ) ≤ ((2 * faExp m).factorial : ℝ) := Nat.cast_nonneg _
  linarith

theorem labelMoment_nonneg (m : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ labelMoment m θ := by
  unfold labelMoment
  have := one_le_labelD m
  exact mul_nonneg (by linarith) (pow_nonneg hθ _)

theorem labelHolder_nonneg (m : ℕ) (Cd : ℝ) {CR θ : ℝ} (hCR : 0 ≤ CR) (hθ : 0 ≤ θ) (L : ℕ) :
    0 ≤ labelHolder m Cd CR θ L := by
  unfold labelHolder
  have h1 := labelLeaveProb_nonneg m (Cd := Cd) hCR L
  have h2 := labelMoment_nonneg m (mul_nonneg hθ (labelLog_pos m L).le)
  exact Real.rpow_nonneg (mul_nonneg h1 (mul_nonneg (pow_nonneg (by norm_num) _)
    (mul_nonneg (by norm_num) h2))) _

/-- The inequality of the Hölder step for `ε₁(L)`. -/
theorem sqrt_mul_sqrt_le_labelHolder (m : ℕ) (Cd : ℝ) {CR θ : ℝ} (hCR : 0 ≤ CR) (hθ : 0 ≤ θ)
    (L : ℕ) :
    Real.sqrt (labelLeaveProb m Cd CR L) *
        Real.sqrt (2 ^ (2 * faExp m) * (2 * labelMoment m (θ * labelLog m L))) ≤
      labelHolder m Cd CR θ L ^ faExp m := by
  have h1 := labelLeaveProb_nonneg m (Cd := Cd) hCR L
  have h2 := labelMoment_nonneg m (mul_nonneg hθ (labelLog_pos m L).le)
  have h3 : 0 ≤ (2 : ℝ) ^ (2 * faExp m) * (2 * labelMoment m (θ * labelLog m L)) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (by norm_num) h2)
  unfold labelHolder
  rw [rpow_one_div_two_mul_pow (mul_nonneg h1 h3) (one_le_faExp m), Real.sqrt_mul h1]

theorem labelClipError_nonneg (m : ℕ) (θ : ℝ) (L : ℕ) : 0 ≤ labelClipError m θ L := by
  unfold labelClipError
  have := one_le_labelD m
  have h : 0 ≤ labelD m := by linarith
  positivity

/-- The inequality of the clipping error: `c ≤ (2 B ε₃)^k` for `B = L⁴`. -/
theorem labelMoment_le_clipError (m : ℕ) {L : ℕ} (hL : 1 ≤ L) (θ : ℝ) :
    labelMoment m (θ * labelLog m L) ≤
      (2 * (L : ℝ) ^ 4 * labelClipError m θ L) ^ faExp m := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hD := one_le_labelD m
  have hk := one_le_faExp m
  have e : 2 * (L : ℝ) ^ 4 * labelClipError m θ L = labelD m * (θ * labelLog m L) ^ 2 := by
    unfold labelClipError
    field_simp
  rw [e, mul_pow, labelMoment, pow_mul (θ * labelLog m L) 2 (faExp m)]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (sq_nonneg (θ * labelLog m L)) _)
  calc labelD m = labelD m ^ 1 := (pow_one _).symm
    _ ≤ labelD m ^ faExp m := pow_le_pow_right₀ hD hk

/-! ### The atom bound -/

/-- The atom bound `α_L = 1/(((L + 1)(2L⁴ + ξ))^k |Λ|)`, `Λ` the alphabet of the values of `Ψ_G`, for
the mesh step `τ` and the rounding step `ξ`. -/
noncomputable def labelAlpha (m L : ℕ) (τ ξ : ℝ) : ℝ :=
  1 / ((((L : ℝ) + 1) * (2 * (L : ℝ) ^ 4 + ξ)) ^ faExp m *
    (labelAlphabet (meshPairs m L τ) ((L : ℝ) ^ 4) ξ).card)

theorem labelAlpha_pos (m L : ℕ) (τ : ℝ) {ξ : ℝ} (hξ : 0 < ξ) : 0 < labelAlpha m L τ ξ := by
  unfold labelAlpha
  have h1 : (0 : ℝ) < (labelAlphabet (meshPairs m L τ) ((L : ℝ) ^ 4) ξ).card := by
    exact_mod_cast labelAlphabet_card_pos (by positivity) hξ
  have h2 : (0 : ℝ) < ((L : ℝ) + 1) * (2 * (L : ℝ) ^ 4 + ξ) := by positivity
  exact one_div_pos.mpr (mul_pos (pow_pos h2 _) h1)

/-- `α_L |Λ| ≤ 1`: every value of `X_G` has probability at least `α_L`, the value `ψ*` included. -/
theorem labelAlpha_mul_card_le_one (m : ℕ) {L : ℕ} (hL : 1 ≤ L) (τ : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    labelAlpha m L τ ξ * (labelAlphabet (meshPairs m L τ) ((L : ℝ) ^ 4) ξ).card ≤ 1 := by
  have hc : (0 : ℝ) < (labelAlphabet (meshPairs m L τ) ((L : ℝ) ^ 4) ξ).card := by
    exact_mod_cast labelAlphabet_card_pos (by positivity) hξ
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h4 : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ hL'
  have h1 : 1 ≤ ((L : ℝ) + 1) * (2 * (L : ℝ) ^ 4 + ξ) := by nlinarith only [h4, hL', hξ]
  have ha : 1 ≤ (((L : ℝ) + 1) * (2 * (L : ℝ) ^ 4 + ξ)) ^ faExp m := one_le_pow₀ h1
  rw [labelAlpha, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]
  exact inv_le_one_of_one_le₀ ha

/-- `(2L⁴ + ξ)^k |Λ| α_L ≤ (1/(L+1))^k`: the error of the merging. -/
theorem merge_le_labelAlpha (m L : ℕ) (τ : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    (2 * (L : ℝ) ^ 4 + ξ) ^ faExp m *
        ((labelAlphabet (meshPairs m L τ) ((L : ℝ) ^ 4) ξ).card * labelAlpha m L τ ξ) ≤
      faStep L ^ faExp m := by
  have hc : (0 : ℝ) < (labelAlphabet (meshPairs m L τ) ((L : ℝ) ^ 4) ξ).card := by
    exact_mod_cast labelAlphabet_card_pos (by positivity) hξ
  have hb : 0 < 2 * (L : ℝ) ^ 4 + ξ := by positivity
  have hX : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  rw [labelAlpha, pow_mul_mul_one_div_eq hb hX hc]
  rfl

/-! ### The limits -/

/-- `log(2 + (L+1)^{2m})^N / (2 + (L+1)^{2m}) → 0`. -/
theorem tendsto_labelLog_pow_div (hm : 1 ≤ m) (N : ℕ) :
    Tendsto (fun L : ℕ => labelLog m L ^ N / (2 + ((L : ℝ) + 1) ^ (2 * m))) atTop (𝓝 0) := by
  have hx : Tendsto (fun L : ℕ => (2 : ℝ) + ((L : ℝ) + 1) ^ (2 * m)) atTop atTop := by
    refine tendsto_atTop_add_const_left _ _ ?_
    exact (tendsto_pow_atTop (by omega)).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 N one_ne_zero).comp hx
  refine h.congr fun L => ?_
  simp only [Function.comp_apply, one_mul, add_zero, labelLog]

/-- The Markov quotient, with a radius at least `√X/b`:
`2 X^a C/r^{2k} ≤ 2 b^{2k} C X^a/X^k`. -/
theorem markov_quotient_le' {X r C b : ℝ} {a k : ℕ} (hX : 0 < X) (hb : 0 < b)
    (hr : Real.sqrt X / b ≤ r) (hC : 0 ≤ C) :
    2 * X ^ a * C / r ^ (2 * k) ≤ 2 * b ^ (2 * k) * C * X ^ a / X ^ k := by
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hpow : (Real.sqrt X / b) ^ (2 * k) * b ^ (2 * k) = X ^ k := by
    rw [← mul_pow, div_mul_cancel₀ _ hb.ne', pow_mul, Real.sq_sqrt hX.le]
  have hle : (Real.sqrt X / b) ^ (2 * k) ≤ r ^ (2 * k) := pow_le_pow_left₀ (by positivity) hr _
  rw [div_le_div_iff₀ (pow_pos hr0 _) (pow_pos hX _), ← hpow]
  have h0 : 0 ≤ 2 * X ^ a * C * b ^ (2 * k) := by positivity
  calc 2 * X ^ a * C * ((Real.sqrt X / b) ^ (2 * k) * b ^ (2 * k))
      = (2 * X ^ a * C * b ^ (2 * k)) * (Real.sqrt X / b) ^ (2 * k) := by ring
    _ ≤ (2 * X ^ a * C * b ^ (2 * k)) * r ^ (2 * k) :=
        mul_le_mul_of_nonneg_left hle h0
    _ = 2 * b ^ (2 * k) * C * X ^ a * r ^ (2 * k) := by ring

/-- The bound `π(L)`, beyond the threshold `((8 C_d + 17)/7)²`, is at most
`6 (8(C_d + 1))^{8d} C/(2 + (L+1)^{2m})`: the power `L^{−4d}` of the paper beats the number of pairs
of cubes, and there is `(L+1)^{−2m}` to spare. -/
theorem labelLeaveProb_le (m : ℕ) {Cd CR : ℝ} (hCd : 0 ≤ Cd) (hCR : 0 ≤ CR) {L : ℕ}
    (hL : ((8 * Cd + 17) / 7) ^ 2 ≤ L) :
    labelLeaveProb m Cd CR L ≤
      6 * (8 * (Cd + 1)) ^ (2 * (4 * (m + 1))) * CR / (2 + ((L : ℝ) + 1) ^ (2 * m)) := by
  have hr := leaveRadius_ge hCd hL
  have hX : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hX1 : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hb : (0 : ℝ) < 8 * (Cd + 1) := by positivity
  have hr0 : 0 < leaveRadius Cd L :=
    lt_of_lt_of_le (by have := Real.sqrt_pos.2 hX; positivity) hr
  have hq : 8 * (m + 1) = 2 * (4 * (m + 1)) := by ring
  unfold labelLeaveProb
  rw [ite_eq_left hr0, hq]
  refine (markov_quotient_le' hX hb hr hCR).trans ?_
  set X : ℝ := (L : ℝ) + 1
  set B : ℝ := (8 * (Cd + 1)) ^ (2 * (4 * (m + 1))) * CR
  have hB : 0 ≤ B := by positivity
  have hXa : 1 ≤ X ^ (2 * m) := one_le_pow₀ hX1
  have hx0 : (0 : ℝ) < 2 + X ^ (2 * m) := by linarith
  rw [show 2 * (8 * (Cd + 1)) ^ (2 * (4 * (m + 1))) * CR * X ^ (2 * m) = 2 * B * X ^ (2 * m) by
      simp only [B]; ring,
    show 6 * (8 * (Cd + 1)) ^ (2 * (4 * (m + 1))) * CR = 6 * B by simp only [B]; ring,
    div_le_div_iff₀ (pow_pos hX _) hx0]
  have h1 : X ^ (2 * m) * X ^ (2 * m) ≤ X ^ (4 * (m + 1)) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hX1 (by omega)
  have h2 : (2 + X ^ (2 * m)) * X ^ (2 * m) ≤ 3 * X ^ (4 * (m + 1)) := by
    nlinarith only [h1, hXa]
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * B)
  linarith only [h3]

/-- **`ε₁(L) → 0`.** -/
theorem tendsto_labelHolder (hm : 1 ≤ m) {Cd CR θ : ℝ} (hCd : 0 ≤ Cd) (hCR : 0 ≤ CR) (hθ : 0 ≤ θ) :
    Tendsto (labelHolder m Cd CR θ) atTop (𝓝 0) := by
  set c : ℝ := 2 ^ (2 * faExp m) * (2 * (labelD m * θ ^ (2 * faExp m))) with hc
  have hD := one_le_labelD m
  have hc0 : 0 ≤ c := by
    have : 0 ≤ labelD m := by linarith
    have h2 : 0 ≤ θ ^ (2 * faExp m) := pow_nonneg hθ _
    exact mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (by norm_num) (mul_nonneg this h2))
  set A : ℝ := 6 * (8 * (Cd + 1)) ^ (2 * (4 * (m + 1))) * CR * c with hA
  have hA0 : 0 ≤ A := by positivity
  have hlim := (tendsto_labelLog_pow_div hm (2 * faExp m)).const_mul A
  rw [mul_zero] at hlim
  have hf : Tendsto (fun L : ℕ => labelLeaveProb m Cd CR L *
      (2 ^ (2 * faExp m) * (2 * labelMoment m (θ * labelLog m L)))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun L => mul_nonneg
      (labelLeaveProb_nonneg m hCR L) (mul_nonneg (pow_nonneg (by norm_num) _)
        (mul_nonneg (by norm_num) (labelMoment_nonneg m
          (mul_nonneg hθ (labelLog_pos m L).le))))) ?_ hlim
    refine eventually_atTop.2 ⟨⌈((8 * Cd + 17) / 7) ^ 2⌉₊, fun L hL => ?_⟩
    have hL' : ((8 * Cd + 17) / 7) ^ 2 ≤ L := by
      have : (⌈((8 * Cd + 17) / 7) ^ 2⌉₊ : ℝ) ≤ L := by exact_mod_cast hL
      exact (Nat.le_ceil _).trans this
    have hP := labelLeaveProb_le m hCd hCR hL'
    have e : (2 : ℝ) ^ (2 * faExp m) * (2 * labelMoment m (θ * labelLog m L)) =
        c * labelLog m L ^ (2 * faExp m) := by
      simp only [c, labelMoment, mul_pow]
      ring
    have hl : 0 ≤ labelLog m L ^ (2 * faExp m) := pow_nonneg (labelLog_pos m L).le _
    rw [e]
    calc labelLeaveProb m Cd CR L * (c * labelLog m L ^ (2 * faExp m))
        ≤ 6 * (8 * (Cd + 1)) ^ (2 * (4 * (m + 1))) * CR / (2 + ((L : ℝ) + 1) ^ (2 * m)) *
            (c * labelLog m L ^ (2 * faExp m)) :=
          mul_le_mul_of_nonneg_right hP (mul_nonneg hc0 hl)
      _ = A * (labelLog m L ^ (2 * faExp m) / (2 + ((L : ℝ) + 1) ^ (2 * m))) := by
          simp only [A]
          ring
  have h := hf.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ 1 / (2 * ((faExp m : ℕ) : ℝ))))
  rwa [Real.zero_rpow (by have := one_le_faExp m; positivity)] at h

/-- For `L ≥ 1`, `labelLog L ≤ (2m + 1) log(L + 2)`. -/
theorem labelLog_le (m : ℕ) {L : ℕ} (hm : 1 ≤ m) (hL : 1 ≤ L) :
    labelLog m L ≤ (2 * (m : ℝ) + 1) * Real.log ((L : ℝ) + 2) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hbase : (1 : ℝ) ≤ (L : ℝ) + 1 := by linarith
  have hbig : (2 : ℝ) ≤ ((L : ℝ) + 1) ^ (2 * m) := by
    calc (2 : ℝ) ≤ (L : ℝ) + 1 := by linarith
      _ = ((L : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((L : ℝ) + 1) ^ (2 * m) := pow_le_pow_right₀ hbase (by omega)
  have h1 : 2 + ((L : ℝ) + 1) ^ (2 * m) ≤ ((L : ℝ) + 2) ^ (2 * m + 1) := by
    have h2 : ((L : ℝ) + 1) ^ (2 * m) ≤ ((L : ℝ) + 2) ^ (2 * m) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    rw [pow_succ]
    nlinarith only [h2, hbig, hL']
  unfold labelLog
  calc Real.log (2 + ((L : ℝ) + 1) ^ (2 * m))
      ≤ Real.log (((L : ℝ) + 2) ^ (2 * m + 1)) := Real.log_le_log (by linarith) h1
    _ = (2 * (m : ℝ) + 1) * Real.log ((L : ℝ) + 2) := by
        rw [Real.log_pow]
        push_cast
        ring

/-- **`ε₃(L) → 0`.** -/
theorem tendsto_labelClipError (hm : 1 ≤ m) (θ : ℝ) :
    Tendsto (labelClipError m θ) atTop (𝓝 0) := by
  have hD := one_le_labelD m
  have hlog : Tendsto (fun L : ℕ => Real.log ((L : ℝ) + 2) ^ 2 / ((L : ℝ) + 2)) atTop (𝓝 0) := by
    have hx : Tendsto (fun L : ℕ => (L : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hx
    refine h.congr fun L => ?_
    simp only [Function.comp_apply, one_mul, add_zero]
  set A : ℝ := labelD m * θ ^ 2 * (2 * (m : ℝ) + 1) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hlim := hlog.const_mul A
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun L => labelClipError_nonneg m θ L) ?_ hlim
  refine eventually_atTop.2 ⟨2, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := by omega
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hl0 := labelLog_pos m L
  have hl := labelLog_le m hm hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hlp : 0 ≤ Real.log ((L : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hsq : labelLog m L ^ 2 ≤ (2 * (m : ℝ) + 1) ^ 2 * Real.log ((L : ℝ) + 2) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hl0.le hl 2
  have hden : (L : ℝ) + 2 ≤ 2 * (L : ℝ) ^ 4 := by
    have h1 : (L : ℝ) ≤ (L : ℝ) ^ 4 := by
      calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (L : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h2 : (2 : ℝ) ≤ (L : ℝ) ^ 4 := by
      calc (2 : ℝ) ≤ L := hL2
        _ ≤ (L : ℝ) ^ 4 := h1
    linarith
  unfold labelClipError
  calc labelD m * (θ * labelLog m L) ^ 2 / (2 * (L : ℝ) ^ 4)
      ≤ labelD m * (θ * labelLog m L) ^ 2 / ((L : ℝ) + 2) :=
        div_le_div_of_nonneg_left (by have : 0 ≤ labelD m := by linarith
                                      positivity) (by positivity) hden
    _ = labelD m * θ ^ 2 * labelLog m L ^ 2 / ((L : ℝ) + 2) := by ring
    _ ≤ labelD m * θ ^ 2 * ((2 * (m : ℝ) + 1) ^ 2 * Real.log ((L : ℝ) + 2) ^ 2) / ((L : ℝ) + 2) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsq (by have : 0 ≤ labelD m := by linarith
                                                positivity)
    _ = A * (Real.log ((L : ℝ) + 2) ^ 2 / ((L : ℝ) + 2)) := by
        simp only [A]
        ring

/-- The clipping level beats the deterministic part: `(C L² + D − L⁴/2)₊ → 0`, being eventually
`0`. -/
theorem tendsto_max_sub_clip {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    Tendsto (fun L : ℕ => max (C * (L : ℝ) ^ 2 + D - (L : ℝ) ^ 4 / 2) 0) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  refine eventually_atTop.2 ⟨⌈2 * (C + D) + 1⌉₊ + 1, fun L hL => ?_⟩
  have hL1 : (2 * (C + D) + 1) ≤ L := by
    have h : (⌈2 * (C + D) + 1⌉₊ : ℝ) ≤ L := by exact_mod_cast (Nat.le_succ _).trans hL
    exact (Nat.le_ceil _).trans h
  have hL0 : (1 : ℝ) ≤ L := by linarith
  have h2 : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith only [hL0]
  have h3 : C * (L : ℝ) ^ 2 + D ≤ (C + D) * (L : ℝ) ^ 2 := by nlinarith only [hD, hL0, h2]
  have h4 : (L : ℝ) ^ 4 = (L : ℝ) ^ 2 * (L : ℝ) ^ 2 := by ring
  have h5 : (2 * (C + D)) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    have h6 : 2 * (C + D) ≤ (L : ℝ) ^ 2 := by linarith
    exact mul_le_mul_of_nonneg_right h6 (by positivity)
  exact (max_eq_right (by linarith)).symm

end CurvatureVariance.Paper.Gain
