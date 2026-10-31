/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.ErrorScale
import IsotropicVariance.Statements.Cited.HnLemma42
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # [HN, Lemma 4.2] at the classical error scale

The deterministic last step of the second bound of Lemma `lem:classical`, which its proof
takes from Howard and Newman [HN, Lemmas 4.1 and 4.2].
`eventually_sub_le_errorScale_of_doubling` is the cited statement `Cited.hn_lemma4_2` with `ν = 1`,
`g(ℓ) = K (ℓ log(2+ℓ))^{1/2}`, `ψ = 7/4`, which lies between `√2` and `2`, and `c = 5`.

That statement concludes for large `t`. The paper leaves the other `t ≥ 1` as standard, and
`le_errorScale_of_eventually` supplies them from a deterministic linear upper bound, after
enlarging the constant. The doubling estimate is an input of these lemmas, not a premise of the
paper's statement: it is proved in `IsotropicVariance.Paper.Proofs.Classical.Mean`.
-/

@[expose] public section
open Real Set Filter Topology
namespace IsotropicVariance.Paper.Proofs.Classical

/-- The logarithm with a fixed positive shift is sublinear at real scales. -/
theorem tendsto_log_add_two_div_atTop :
    Tendsto (fun t : ℝ => log (2 + t) / t) atTop (𝓝 0) := by
  have hPlus : Tendsto (fun t : ℝ => 2 + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop 2 tendsto_id
  have h1 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hPlus
  have h2 : Tendsto (fun t : ℝ => (2 + t) / t) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun t : ℝ => (2 : ℝ) / t) atTop (𝓝 0)).add_const 1
    rw [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    field_simp
  have hh := h1.mul h2
  rw [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hPos : 2 + t ≠ 0 := by positivity
  dsimp only [Function.comp_def, id_eq]
  field_simp

/-- The classical error is little-oh of the length, at real scales. -/
theorem tendsto_errorScale_div_atTop :
    Tendsto (fun t : ℝ => errorScale t / t) atTop (𝓝 0) := by
  have hh := tendsto_log_add_two_div_atTop.sqrt
  rw [sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hProd : 0 ≤ t * log (2 + t) :=
    mul_nonneg ht.le (log_nonneg (by linarith only [ht] : (1 : ℝ) ≤ 2 + t))
  have ht0 : t ≠ 0 := ht.ne'
  calc
    sqrt (log (2 + t) / t) = sqrt ((t * log (2 + t)) / t ^ 2) := by
      congr 1
      field_simp
    _ = sqrt (t * log (2 + t)) / sqrt (t ^ 2) := sqrt_div hProd _
    _ = errorScale t / t := by rw [sqrt_sq ht.le]; rfl

/-- **[HN, Lemma 4.2] at the classical error scale** (proof of Lemma `lem:classical`): if
`H t / t → 1` and `H (2 t) ≥ 2 H t − K (t log(2+t))^{1/2}` for all large `t`, then
`H t − t ≤ 5 K (t log(2+t))^{1/2}` for all large `t`. -/
theorem eventually_sub_le_errorScale_of_doubling (H : ℝ → ℝ)
    (hLim : Tendsto (fun t : ℝ => H t / t) atTop (𝓝 1)) {K : ℝ} (hK : 0 ≤ K)
    (hDouble : ∀ᶠ t : ℝ in atTop, 2 * H t - K * errorScale t ≤ H (2 * t)) :
    ∀ᶠ t : ℝ in atTop, H t - t ≤ (5 * K) * errorScale t := by
  have hgo : Tendsto (fun t : ℝ => K * errorScale t / t) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using tendsto_errorScale_div_atTop.const_mul K
  have hψ : ∀ᶠ t : ℝ in atTop, K * errorScale (2 * t) ≤ (7 / 4) * (K * errorScale t) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    linarith only [mul_le_mul_of_nonneg_left (errorScale_two_mul_le ht) hK]
  have hHN := Cited.hn_lemma4_2 H (fun t => K * errorScale t) 1
    (fun t _ => mul_nonneg hK (errorScale_nonneg t)) hLim hgo hDouble (7 / 4) (by norm_num) hψ
    5 (by norm_num)
  filter_upwards [hHN] with t ht
  linarith only [ht]

/-- The other `t ≥ 1`: a bound for large `t` extends to every `t ≥ 1`, after enlarging the
constant, by a deterministic linear upper bound of `H`. The paper leaves this step as standard
(proof of Lemma `lem:classical`). -/
theorem le_errorScale_of_eventually (H : ℝ → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hUp : ∀ t, 0 ≤ t → H t ≤ B * t)
    (hLarge : ∀ᶠ t : ℝ in atTop, H t - t ≤ C * errorScale t) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t → H t - t ≤ D * errorScale t := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hLarge
  have hk : 0 < errorScale 1 := errorScale_pos zero_lt_one
  let A := B * |T| / errorScale 1
  have hA : 0 ≤ A := by positivity
  have hAk : A * errorScale 1 = B * |T| := div_mul_cancel₀ _ hk.ne'
  refine ⟨C + A + 1, by linarith only [hC, hA], fun t ht => ?_⟩
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hPos := errorScale_nonneg t
  have hCt := mul_nonneg hC hPos
  have hAt := mul_nonneg hA hPos
  have hSplit : (C + A + 1) * errorScale t = C * errorScale t + A * errorScale t + errorScale t := by
    ring
  rw [hSplit]
  by_cases hTt : T ≤ t
  · linarith only [hT t hTt, hAt, hPos]
  · have hSmall : t ≤ |T| := (not_le.mp hTt).le.trans (le_abs_self T)
    have hkt := mul_le_mul_of_nonneg_left (errorScale_mono zero_le_one ht) hA
    linarith only [hUp t ht0, mul_le_mul_of_nonneg_left hSmall hB, hAk, hkt, hCt, hPos, ht0]

end IsotropicVariance.Paper.Proofs.Classical
