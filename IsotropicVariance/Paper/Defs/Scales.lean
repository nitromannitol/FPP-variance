/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Model

/-!
# The scales `Q_s`, `W_s` and the standing hypotheses

`Q_s = A s^{1/2 − 1/K}` and `W_s = √(s Q_s)` (the introduction and the beginning of Section
`sec:exponential`), and the hypotheses of Sections `sec:exponential` to `sec:completion`: the
induction hypothesis (equation `eq:premise`) and the regime (equation `eq:regime`).

Here `K`, `A`, `N` are fixed and both hypotheses hold at `(K, A, N)`. The paper's thresholds ("if `N` is
sufficiently large") depend only on the law of the density and on `d`, besides the parameters
named in each statement (Section `ssec:notation`); every such threshold is read as uniform in
`A ≥ 1`, which the final induction on the length needs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace IsotropicVariance.Paper

/-- `Q_s = A s^{1/2 − 1/K}` (the introduction). -/
noncomputable def Q (K : ℕ) (A s : ℝ) : ℝ :=
  A * s ^ ((1 : ℝ) / 2 - 1 / (K : ℝ))

/-- `W_s = √(s Q_s)` (the introduction). -/
noncomputable def W (K : ℕ) (A s : ℝ) : ℝ :=
  Real.sqrt (s * Q K A s)

/-- The induction hypothesis, equation `eq:premise`: `|T_s − s| ≤ O_1(Q_s)` for every real
`s ∈ [1, N/2]`. -/
def Premise {m : ℕ} (X : Setting m) (K : ℕ) (A N : ℝ) : Prop :=
  ∀ s : ℝ, 1 ≤ s → s ≤ N / 2 → Cited.IsOs X.P 1 (Q K A s) (fun ω => |X.TRV s ω - s|)

/-- The regime, equation `eq:regime`: `Q_N ≤ C_* √(N log(2+N))`, for the fixed
constant `C_*` of the classical bounds (a parameter of every statement that assumes it). -/
def Regime (Cstar : ℝ) (K : ℕ) (A N : ℝ) : Prop :=
  Q K A N ≤ Cstar * Real.sqrt (N * Real.log (2 + N))

/-- The standing hypotheses of Sections `sec:exponential` to `sec:gain`: an integer `K ≥ 10`,
`A ≥ 1`, a length `N ≥ 2`, the induction hypothesis `eq:premise` and the regime `eq:regime`. -/
def Standing {m : ℕ} (X : Setting m) (Cstar : ℝ) (K : ℕ) (A N : ℝ) : Prop :=
  10 ≤ K ∧ 1 ≤ A ∧ 2 ≤ N ∧ Premise X K A N ∧ Regime Cstar K A N

end IsotropicVariance.Paper
