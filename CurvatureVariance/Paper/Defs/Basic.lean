/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Lattice.PassageTime
public import CurvatureVariance.Statements.Space.Point
public import CurvatureVariance.Statements.Weights.AssumptionW
public import CurvatureVariance.Statements.Weights.IsIIDWeights
public import CurvatureVariance.Statements.TimeConstant.IsTimeConstant
public import CurvatureVariance.Infra.Os.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The paper's internal objects: the model, the scales and the induction premise

Definitions for the contracts of the lattice paper.

* `Paper.Law`, `Paper.Model`, `Paper.Model.Standing`: the standing hypotheses of Sections
  `sec:prelim` to `sec:mean`: i.i.d. weights with (W), the time constant, and the expansion of
  Lemma `lem:chart` (equation `eq:curvature`) at the slope `t₀` of the direction, with exponent
  `δ ∈ (0, 1]`, a linear coefficient `p₀`, a positive definite quadratic form `q₀` and a remainder
  bound. A model is its law (`F`, `P`, `μ`, `δ`) and its chart data.
* `Paper.Bounds`, `Paper.Bounds.Valid`, `Paper.Model.Fits`: the data on which constants and
  thresholds may depend (Section `ssec:notation`): a law and bounds on the chart
  data. Every contract quantifies its constants and thresholds after a `Bounds` record and before
  the models that fit it, so that they do not depend on the direction (the uniform theorem).
  `Paper.chartBounds` is the record of Lemma `lem:chart` at a unit direction.
* `Paper.passageTimeReal`, `Paper.slopeVec`, `Paper.oneNorm`, `Paper.InBox`.
* `Paper.IsAbsOs`: `|X| ≤ O_s(θ)`, the absolute value (equations `eq:classical` and `eq:premise`).
* The scales of Section `sec:induction`: `Paper.Q`, `Paper.W`, `Paper.premiseDomain` (the set
  `𝒟(s)`, centred at `s t₀`), the induction premise `Paper.Premise` (equation `eq:premise`), and
  the range of the amplitude `Paper.RangeA` (equation `eq:regime`).

The coordinates are those chosen at the beginning of Section `sec:prelim`: the
first coordinate of `Pt m` and `Vertex m` is an original coordinate of largest absolute value of the
unit direction `ξ`, oriented along `ξ` (for the theorem at one direction, any coordinate with
nonzero component), so that `ξ = a(1, t₀)` with `a > 0`, and, as the paper states, `x₁`, the basis
vectors `e₁, …, e_d` and all coordinates refer to these coordinates. The passage to these
coordinates from the original ones is `Contracts.ReductionStatement`, and
`Contracts.ReductionUniformStatement` for the uniform theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper

/-! ## The law and the model -/

/-- The law of a model: the law `F` of the weights, the law `P` of the configuration, the time
constant `μ`, and the exponent `δ` of the curvature remainder in equation `eq:curvature`. The
constants and thresholds of the contracts depend on a model only through its law and the bounds of
a `Bounds` record. -/
structure Law (m : ℕ) where
  /-- The common law of the weights. -/
  F : Measure ℝ≥0
  /-- The law of the weight configuration. -/
  P : Measure (Config m)
  /-- The time constant. -/
  μ : PtNorm m
  /-- The exponent of the curvature remainder in equation `eq:curvature`. -/
  δ : ℝ

/-- The standing hypotheses on a law: `d = m + 1 ≥ 2`, i.i.d. weights with law `F` satisfying (W),
`μ` the time constant, and `δ ∈ (0, 1]`. -/
structure Law.Valid {m : ℕ} (L : Law m) : Prop where
  one_le_m : 1 ≤ m
  probF : IsProbabilityMeasure L.F
  assumptionW : AssumptionW m L.F
  probP : IsProbabilityMeasure L.P
  iid : IsIIDWeights L.P L.F
  timeConstant : IsTimeConstant L.P L.μ
  delta_pos : 0 < L.δ
  delta_le_one : L.δ ≤ 1

/-- The data of the model of Sections `sec:prelim` to `sec:mean`, in the coordinates chosen in
Section `sec:prelim`: its law (`F`, `P`, `μ` and the exponent `δ`), and the data of the
expansion of Lemma `lem:chart`: the slope `t₀` of the direction, the linear coefficient `p₀`, the
quadratic form `q₀` (`h ↦ h·Bh`) and the remainder bound `Crem` on the radius `rrem`. -/
structure Model (m : ℕ) extends Law m where
  /-- The constant of the curvature remainder. -/
  Crem : ℝ
  /-- The radius on which the remainder bound holds. -/
  rrem : ℝ
  /-- The slope `t₀` of the direction: `ξ = a(1, t₀)` with `a > 0` in the chosen coordinates. -/
  t₀ : EuclideanSpace ℝ (Fin m)
  /-- The linear coefficient `p₀` of equation `eq:curvature`. -/
  p₀ : EuclideanSpace ℝ (Fin m)
  /-- The quadratic part `h ↦ h·Bh` of equation `eq:curvature`. -/
  q₀ : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m))

/-- The standing hypotheses (Assumptions (W) and (Curv), Section `ssec:notation`, and the
beginning of Section `sec:prelim`): `d = m + 1 ≥ 2`; the weights are
i.i.d. with law `F` satisfying (W); `μ` is the time constant; and the expansion of Lemma
`lem:chart`, equation `eq:curvature`, at the slope `t₀`: `δ ∈ (0, 1]`, `q₀` is positive definite
(the matrix `Σ` of Lemma `lem:chart`), and
`|μ(1, t₀ + h) − μ(1, t₀) − p₀·h − q₀(h)| ≤ Crem |h|^{2+δ}` for `|h| ≤ rrem`. Lemma `lem:chart`
derives this from Assumption (Curv) (`Contracts.ChartStatement`), after the choice of coordinates
(`Contracts.ReductionStatement`). -/
structure Model.Standing {m : ℕ} (M : Model m) : Prop where
  one_le_m : 1 ≤ m
  probF : IsProbabilityMeasure M.F
  assumptionW : AssumptionW m M.F
  probP : IsProbabilityMeasure M.P
  iid : IsIIDWeights M.P M.F
  timeConstant : IsTimeConstant M.P M.μ
  delta_pos : 0 < M.δ
  delta_le_one : M.δ ≤ 1
  rrem_pos : 0 < M.rrem
  q₀_posDef : M.q₀.PosDef
  curvature : ∀ h : EuclideanSpace ℝ (Fin m), ‖h‖ ≤ M.rrem →
    |M.μ.1 (WithLp.toLp 2 ((1 : ℝ), M.t₀ + h)) - M.μ.1 (WithLp.toLp 2 ((1 : ℝ), M.t₀)) -
        inner ℝ M.p₀ h - M.q₀ h| ≤ M.Crem * ‖h‖ ^ (2 + M.δ)

/-! ## The bounds of a family of models -/

/-- The data on which the constants and thresholds of the contracts may depend: a law, a lower
bound `rrem` for the radius of the expansion, an upper bound `Crem` for its remainder constant,
two-sided bounds `lam |h|² ≤ q₀(h) ≤ Lam |h|²` for its quadratic part, and an upper bound `T` for
the slope `|t₀|` of the direction. Each contract quantifies its constants and thresholds after a
`Bounds` record and before the models that fit it (`Model.Fits`), so that they depend on the
direction only through these bounds. -/
structure Bounds (m : ℕ) where
  /-- The law of the models. -/
  law : Law m
  /-- A lower bound for the radius of the expansion. -/
  rrem : ℝ
  /-- An upper bound for the remainder constant of the expansion. -/
  Crem : ℝ
  /-- A lower bound for the quadratic form: `lam |h|² ≤ q₀(h)`. -/
  lam : ℝ
  /-- An upper bound for the quadratic form: `q₀(h) ≤ Lam |h|²`. -/
  Lam : ℝ
  /-- An upper bound for the slope of the direction: `|t₀| ≤ T`. -/
  T : ℝ

/-- The hypotheses on a `Bounds` record: its law satisfies the standing hypotheses, `rrem > 0`,
`Crem ≥ 0`, `lam > 0`, `Lam ≥ 0` and `T ≥ 0`. -/
structure Bounds.Valid {m : ℕ} (bd : Bounds m) : Prop where
  law : bd.law.Valid
  rrem_pos : 0 < bd.rrem
  Crem_nonneg : 0 ≤ bd.Crem
  lam_pos : 0 < bd.lam
  Lam_nonneg : 0 ≤ bd.Lam
  T_nonneg : 0 ≤ bd.T

/-- The model `M` fits the bounds `bd`: it has the law of `bd`, its expansion holds on a radius at
least `bd.rrem` with a remainder constant at most `bd.Crem`, its quadratic part lies between
`bd.lam |h|²` and `bd.Lam |h|²`, and its slope satisfies `|t₀| ≤ bd.T`. -/
structure Model.Fits {m : ℕ} (M : Model m) (bd : Bounds m) : Prop where
  law_eq : M.toLaw = bd.law
  rrem_le : bd.rrem ≤ M.rrem
  Crem_le : M.Crem ≤ bd.Crem
  q₀_lower : ∀ h : EuclideanSpace ℝ (Fin m), bd.lam * ‖h‖ ^ 2 ≤ M.q₀ h
  q₀_upper : ∀ h : EuclideanSpace ℝ (Fin m), M.q₀ h ≤ bd.Lam * ‖h‖ ^ 2
  t₀_le : ‖M.t₀‖ ≤ bd.T

theorem Model.Fits.F_eq {m : ℕ} {M : Model m} {bd : Bounds m} (h : M.Fits bd) :
    M.F = bd.law.F :=
  congrArg Law.F h.law_eq

theorem Model.Fits.P_eq {m : ℕ} {M : Model m} {bd : Bounds m} (h : M.Fits bd) :
    M.P = bd.law.P :=
  congrArg Law.P h.law_eq

theorem Model.Fits.μ_eq {m : ℕ} {M : Model m} {bd : Bounds m} (h : M.Fits bd) :
    M.μ = bd.law.μ :=
  congrArg Law.μ h.law_eq

theorem Model.Fits.δ_eq {m : ℕ} {M : Model m} {bd : Bounds m} (h : M.Fits bd) :
    M.δ = bd.law.δ :=
  congrArg Law.δ h.law_eq

/-- The upper bound `Λ = hi/r + M r^δ` of the quadratic part of (Curv) on the ball of radius `r`,
for a norm with `μ ≤ hi |·|` (Lemma `lem:chart`). -/
noncomputable def chartLam (hi r M δ : ℝ) : ℝ :=
  hi / r + M * r ^ δ

/-- The bounds of Lemma `lem:chart` in the coordinates of a largest coordinate of a unit direction
at which (Curv) holds with the constants `δ = L.δ, r, M, c` (the paper's `δ, r, Λ, λ`), for a norm
with `μ ≤ hi |·|`: radius `min(1, r)/4`, remainder constant `12M + 2Λ`, quadratic part between
`c d^{−3/2} |h|²` and `Λ |h|²`, and slope `|t₀| ≤ √(d−1)`, with `Λ = chartLam hi r M δ` (not the
paper's `Λ`) and `d = m + 1`. -/
noncomputable def chartBounds {m : ℕ} (L : Law m) (hi r M c : ℝ) : Bounds m where
  law := L
  rrem := min 1 r / 4
  Crem := 12 * M + 2 * chartLam hi r M L.δ
  lam := c / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
  Lam := chartLam hi r M L.δ
  T := Real.sqrt m

/-- The bounds of Lemma `lem:chart` are valid for a valid law and `hi, r, c > 0`, `M ≥ 0`. -/
theorem chartBounds_valid {m : ℕ} {L : Law m} (hL : L.Valid) {hi r M c : ℝ} (hhi : 0 < hi)
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) : (chartBounds L hi r M c).Valid := by
  have hLam : 0 ≤ chartLam hi r M L.δ := by unfold chartLam; positivity
  refine ⟨hL, ?_, ?_, ?_, hLam, Real.sqrt_nonneg _⟩ <;> simp only [chartBounds] <;> positivity

/-! ## Notation (Section `ssec:notation`) -/

/-- The passage time `T(u, v)` as a real number. -/
noncomputable def passageTimeReal {m : ℕ} (ω : Config m) (u v : Vertex m) : ℝ :=
  (passageTime ω u v : ℝ)

/-- The direction `(1, t)` of a slope `t ∈ ℝ^{d-1}` (Section `sec:prelim`). -/
def slopeVec {m : ℕ} (t : EuclideanSpace ℝ (Fin m)) : Pt m :=
  WithLp.toLp 2 ((1 : ℝ), t)

/-- The `ℓ¹` norm `|x|₁` of a vertex. -/
def oneNorm {m : ℕ} (x : Vertex m) : ℝ :=
  ((x.1.natAbs + ∑ j, (x.2 j).natAbs : ℕ) : ℝ)

/-- The vertex lies in the box `[−R, R]^d`. -/
def InBox {m : ℕ} (R : ℝ) (x : Vertex m) : Prop :=
  |(x.1 : ℝ)| ≤ R ∧ ∀ j, |(x.2 j : ℝ)| ≤ R

/-- `|X| ≤ O_s(θ)`: the absolute value is at most `O_s(θ)`, the form of every bound
`|X − Y| ≤ O_s(θ)` of the paper (equations `eq:classical`, `eq:premise` and `eq:improvement`, the
standing hypotheses of Section `sec:induction` and the proof of Theorem `thm:main`), for a random
variable `X` (a.e.-measurable). It is stronger than the two-sided `X = 0 + O_s(θ)` at the same
scale. -/
def IsAbsOs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s θ : ℝ) (X : Ω → ℝ) : Prop :=
  AEMeasurable X P ∧ CurvatureVariance.IsOs P s θ (fun ω => |X ω|)

/-! ## The scales of Section `sec:induction` -/

/-- `Q_s = A s^{1/2 − δ/K}`. -/
noncomputable def Q {m : ℕ} (M : Model m) (K : ℕ) (A s : ℝ) : ℝ :=
  A * s ^ ((1 : ℝ) / 2 - M.δ / K)

/-- `W_s = √(s Q_s)`. -/
noncomputable def W {m : ℕ} (M : Model m) (K : ℕ) (A s : ℝ) : ℝ :=
  Real.sqrt (s * Q M K A s)

/-- The integer side `⌈W_s⌉` of a lattice cube of side `W_s` (as the side `w` of the cubes
`I_i(j)` of Section `sec:cubes`). -/
noncomputable def wInt {m : ℕ} (M : Model m) (K : ℕ) (A s : ℝ) : ℕ :=
  ⌈W M K A s⌉₊

/-- The set `𝒟(s) = {y ∈ ℤ^{d-1} : |y − s t₀| ≤ s^{3/4+δ/100}}`, centred at `s t₀`, with `t₀`
the slope of the direction (Section `sec:induction`). -/
def premiseDomain {m : ℕ} (M : Model m) (s : ℝ) : Set (Fin m → ℤ) :=
  {y | ‖transversePoint y - s • M.t₀‖ ≤ s ^ ((3 : ℝ) / 4 + M.δ / 100)}

/-- The induction hypothesis, equation `eq:premise`: `|T(0,(s,y)) − μ(s,y)| ≤ O₁(Q_s)` for
`1 ≤ s ≤ 2N/3` and `y ∈ 𝒟(s)`. -/
def Premise {m : ℕ} (M : Model m) (K : ℕ) (A : ℝ) (N : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → (s : ℝ) ≤ 2 * (N : ℝ) / 3 → ∀ y ∈ premiseDomain M s,
    IsAbsOs M.P 1 (Q M K A s)
      (fun ω => passageTimeReal ω 0 ((s : ℤ), y) - M.μ.1 (point ((s : ℤ), y)))

/-- The range of the amplitude, equation `eq:regime` (Section `sec:induction`):
`Q_N ≤ C_* √(N log(2 + N))`; the opposite range is covered by the classical estimates. -/
def RangeA {m : ℕ} (M : Model m) (K : ℕ) (A : ℝ) (N : ℕ) (Cstar : ℝ) : Prop :=
  Q M K A N ≤ Cstar * Real.sqrt (N * Real.log (2 + N))

end CurvatureVariance.Paper
