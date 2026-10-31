/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Responses
import CurvatureVariance.Paper.Proofs.Gain.RRInputs
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:blocks`, the first bound of equation `eq:rewardmoment`

The proof of Lemma `lem:blocks`: the proof of [AB26, Lemma 6.1] with the cells of Section
`sec:gain` and the moment `E[R^{128d²}] ≤ C` of Lemma `lem:localization` in place of the Gaussian
tail: by Hölder's and Markov's inequalities the `L^{16d}` norm of the term of the cell `z` is at
most `C(1 + dist(z,[j,k]))^{-4d}`, and the sum over `z` is at most `C(1 + |j − k|)`.

The argument is `Gain.rewardSum_moment`, whose inputs are the contracts of the paper's
statements: Proposition `prop:profiles` (the `O₁(CQ_n)` bound of the increments), Lemma
`lem:localization` (the moment of the radius), the tube property and equation `eq:scales` (the
rounding of the row cubes). The reward array is `0` off the retained pairs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Contracts

universe u

/-- **Lemma `lem:blocks`, first bound of equation `eq:rewardmoment`**, from Lemma
`lem:localization`, Proposition `prop:profiles`, the tube
property and equation `eq:scales`. -/
theorem rewardMoment {m : ℕ} (hloc : LocalizationStatement m) (hprof : ProfilesStatement m)
    (htube : TubeStatement m) (hscales : ScalesStatement m) : RewardMomentStatement.{u} m := by
  intro bd hbd Cstar
  obtain ⟨C, hC, H⟩ := Gain.rewardSum_moment hprof hloc hscales htube bd hbd Cstar
  refine ⟨C, hC, fun K hK => ?_⟩
  obtain ⟨N₀, hN₀⟩ := H K hK
  refine ⟨N₀, fun M hM hfit N hN A hA hprem hrange n ℓ y htar L hL o _ Ω _ Pr old new hR
    i hi1 hiK j k => ?_⟩
  by_cases hret : IsRetainedPair M n (wInt M K A n) j k
  · have hm := hN₀ M hM hfit N hN A hA hprem hrange n ℓ y htar L hL o Ω Pr old new hR i hi1 hiK
      j k hret
    simpa only [reward, hret, ite_true] using hm
  · simp only [reward, hret, ite_false, zero_pow (show 16 * (m + 1) ≠ 0 by omega),
      lintegral_zero]
    exact bot_le

end CurvatureVariance.Paper.Contracts
