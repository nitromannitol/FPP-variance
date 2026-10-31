/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Scales

/-!
# Statements of Section `sec:completion`: the mean, the improvement, the induction, the theorems

* `SmallMeanStatement`: Lemma `lem:smallmean`.
* `ImprovementStatement`: equation `eq:improvement` for every `N` above a threshold independent of
  `A`, for one `K`.
* `InductionStatement`: the induction on dyadic ranges and the variance bound for a normalized
  density.
* `MainSettingStatement`: Theorem `thm:general` over the noise interface, with the variance bound
  that the paper derives from it after Theorem `thm:main`.
* `MainSettingExpStatement`: Theorem `thm:general` over the noise interface, with its own
  conclusion, the exponential moment of `|T_t − μt|` on the scale `C t^{(1−ε)/2}`.

The last four follow the proof of Theorem `thm:general`. With the bridge
`SettingOfRealizationStatement` (`IsotropicVariance.Paper.Contracts.Classical`) and the
normalization by the time constant, `MainSettingExpStatement` gives Theorem `thm:general` for both
noises, and with the example `ψ(χ∗ω)` (`Infra.Example.isLocalDensity_convolutionDensity`)
Theorem `thm:main`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Contracts

/-- **Lemma `lem:smallmean`** (nonrandom fluctuations): there is `δ > 0`
(depending on the setting only, not on `K`) such that, for `N` large depending on `K`, every
`s ∈ [N/8, N/4]` with `Var(T_r/Q_r) ≤ δ` for all `r ∈ [s, 2s]` has `E T_s − s ≤ Q_s/100`. -/
def SmallMeanStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ Cstar : ℝ, 0 < Cstar →
    ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℕ, 10 ≤ K → ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N →
      Standing X Cstar K A N → ∀ s : ℝ, N / 8 ≤ s → s ≤ N / 4 →
        (∀ r : ℝ, s ≤ r → r ≤ 2 * s →
          evariance (fun ω => X.TRV r ω / Q K A r) X.P ≤ ENNReal.ofReal δ) →
        X.mean s - s ≤ Q K A s / 100

/-- **Proposition `prop:induction`, equation `eq:improvement`**: for a
normalized density there are `K ≥ 10` and a threshold `N₀`, independent of `A`, such that for every
`A ≥ 1` and `N ≥ N₀` the induction hypothesis `eq:premise` gives `|T_N − N| ≤ O_1(Q_N/2)` (whether
or not the regime `eq:regime` holds). -/
def ImprovementStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized →
    ∃ K : ℕ, 10 ≤ K ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ A N : ℝ, 1 ≤ A → N₀ ≤ N → Premise X K A N →
      Cited.IsOs X.P 1 (Q K A N / 2) (fun ω => |X.TRV N ω - N|)

/-- **The induction** (the proof of Theorem `thm:general` from Proposition `prop:induction`):
if a normalized density has the improvement `eq:improvement` for some `K` and threshold, then for
some `A ≥ 1`, `|T_s − s| ≤ O_1(Q_s)` for every `s ≥ 1`, and hence `Var T_t ≤ 4 A² t^{1 − 2/K}` for
`t ≥ 1`. -/
def InductionStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ K : ℕ, 10 ≤ K →
    ∀ N₀ : ℝ, 2 ≤ N₀ →
    (∀ A N : ℝ, 1 ≤ A → N₀ ≤ N → Premise X K A N →
      Cited.IsOs X.P 1 (Q K A N / 2) (fun ω => |X.TRV N ω - N|)) →
    ∃ A : ℝ, 1 ≤ A ∧ (∀ s : ℝ, 1 ≤ s → Cited.IsOs X.P 1 (Q K A s) (fun ω => |X.TRV s ω - s|)) ∧
      ∀ t : ℝ, 1 ≤ t → evariance (X.TRV t) X.P ≤ ENNReal.ofReal (4 * A ^ 2 * t ^ (1 - 2 / (K : ℝ)))

/-- **Theorem `thm:general` over the noise interface**, with the variance bound that the paper
derives after Theorem `thm:main`: for every setting with `d = m + 1 ≥ 2` there is `ε > 0` such
that, for every sufficiently large `t`, `T(0, t e₁)` is a random variable with
`Var T(0, t e₁) ≤ t^{1−ε}`. -/
def MainSettingStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m,
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (X.TRV t) X.P ∧ evariance (X.TRV t) X.P ≤ ENNReal.ofReal (t ^ (1 - ε))

/-- **Theorem `thm:general` over the noise interface**, with its conclusion: for every setting
with `d = m + 1 ≥ 2`, the time constant `μ = lim_{t→∞} E[T_t]/t` exists, and there are `ε > 0`
and `C > 0` such that `|T_t − μt| ≤ O_1(C t^{(1−ε)/2})` for every `t ≥ 1`. -/
def MainSettingExpStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m,
    ∃ μ : ℝ, Tendsto (fun t : ℝ => X.mean t / t) atTop (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
        Cited.IsOs X.P 1 (C * t ^ ((1 - ε) / 2)) (fun ω => |X.TRV t ω - μ * t|)

end IsotropicVariance.Paper.Contracts
