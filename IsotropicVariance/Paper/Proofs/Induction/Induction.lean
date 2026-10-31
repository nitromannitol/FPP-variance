/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Induction.Tools
public import IsotropicVariance.Paper.Contracts.Induction
import IsotropicVariance.Paper.Proofs.Profiles.Scales

/-!
# The induction on dyadic ranges

The induction on the length in the proof of Theorem `thm:general` from Proposition
`prop:induction`.

`inductionStatement_holds` proves the contract `InductionStatement` outright.
- **The base range.** For `s ≥ 1`, `|T_s − s| ≤ Cs` on every outcome and `Q_s ≥ A`. So a large `A`
  (depending on `K` and the threshold) gives `|T_s − s| ≤ O_1(Q_s)` for `s` between one and the
  threshold.
- **The induction step.** If the bound holds on `[1, r]` with `r` at least the threshold, then
  equation `eq:premise` holds for every `N ∈ [r, 2r]`, and equation `eq:improvement` gives the
  bound on `[1, 2r]`.
- **The variance.** `x² ≤ 2eˣ` gives `Var T_t ≤ 4 Q_t² = 4A² t^{1−2/K}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

open IsotropicVariance.Paper.Proofs.Profiles (Q_pos)
namespace IsotropicVariance.Paper.Proofs.Induction

/-- **The dyadic induction** (the proof of Theorem `thm:general` from Proposition
`prop:induction`): the contract `InductionStatement`. -/
theorem inductionStatement_holds : Contracts.InductionStatement.{u} := by
  intro m _hm X _hX K hK N₀ hN₀ hImp
  obtain ⟨C, hC, hCb⟩ := abs_TRV_sub_le X
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := max 1 (C * N₀ / Real.log 2) with hAdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  -- the base range `[1, N₀]`
  have hbase : ∀ s : ℝ, 1 ≤ s → s ≤ N₀ →
      Cited.IsOs X.P 1 (Q K A s) (fun ω => |X.TRV s ω - s|) := by
    intro s hs1 hsN
    have hs0 : 0 ≤ s := zero_le_one.trans hs1
    refine isOs_one_of_le (aemeasurable_abs_TRV_sub X s) (Q_pos hA0 (by linarith))
      (Eventually.of_forall fun ω => ?_)
    calc |X.TRV s ω - s| ≤ C * s := hCb s hs0 ω
      _ ≤ C * N₀ := mul_le_mul_of_nonneg_left hsN hC.le
      _ = C * N₀ / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ A * Real.log 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) hlog.le
      _ ≤ Q K A s * Real.log 2 := mul_le_mul_of_nonneg_right (le_Q hK hA0.le hs1) hlog.le
  -- the dyadic ranges `[1, 2^k N₀]`
  have hdyadic : ∀ k : ℕ, ∀ s : ℝ, 1 ≤ s → s ≤ 2 ^ k * N₀ →
      Cited.IsOs X.P 1 (Q K A s) (fun ω => |X.TRV s ω - s|) := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
      intro s hs1 hs
      by_cases hsk : s ≤ 2 ^ k * N₀
      · exact ih s hs1 hsk
      · rw [not_le] at hsk
        have hN : N₀ ≤ s := (le_mul_of_one_le_left (by linarith) (one_le_pow₀ one_le_two)).trans
          hsk.le
        have hprem : Premise X K A s := fun s' hs'1 hs' => ih s' hs'1 (by
          rw [pow_succ] at hs
          linarith)
        exact Cited.IsOs.mono_scale (s := 1) (hImp A s hA1 hN hprem) zero_le_one
          (half_pos (Q_pos hA0 (by linarith))) (half_le_self (Q_pos hA0 (by linarith)).le)
  have hall : ∀ s : ℝ, 1 ≤ s → Cited.IsOs X.P 1 (Q K A s) (fun ω => |X.TRV s ω - s|) := by
    intro s hs1
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (s / N₀) one_lt_two
    have hN₀pos : 0 < N₀ := by linarith
    exact hdyadic k s hs1 (by rw [div_lt_iff₀ hN₀pos] at hk; exact hk.le)
  refine ⟨A, hA1, hall, fun t ht => ?_⟩
  have hvar := evariance_le_of_isOs_one (Infra.TimeConstant.memLp_TRV X t)
    (Q_pos hA0 (by linarith)) (hall t ht)
  rwa [Q_sq K A (by linarith : (0 : ℝ) ≤ t), ← mul_assoc] at hvar

end IsotropicVariance.Paper.Proofs.Induction
