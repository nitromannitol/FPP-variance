/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum
public import IsotropicVariance.Infra.Arrays.Square
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Statements of Section `sec:prelim`, part 2: straightness, slabs and arrays

* `StraightStatement`: Lemma `lem:straight`.
* `IsSlabPair`: the pairs of points of equation `eq:slab`.
* `SlabStatement`: Lemma `lem:slab`, equations `eq:slab` and `eq:columns`.
* `PenalizedArraysStatement`: Lemma `lem:polynomialarray`, proved here from
  `IsotropicVariance.Infra.Arrays.lintegral_iSup_penalizedSum_le_of_square`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Contracts

/-- **Lemma `lem:straight`**: there is `C > 0` such that, for every
`r ≥ 1`, there is a random variable `W` with `log(2 + r) ≤ W ≤ O_2(C log(2 + r))` such that, for
all points `a`, `b` in the ball of radius `r` around `0`, every point `x` of a near-geodesic from
`a` to `b` with `|x − a| ≥ C W²` satisfies `∠(x − a, b − a) ≤ 1/10`.

A near-geodesic for `ρ` (Section `ssec:overview`) is `IsOneOptimal (X.ρ ω) univ a b`. Readings:
* the ball is the closed ball, the stronger reading;
* `a ≠ b`, since `∠` is the angle between nonzero vectors (Section `ssec:notation`), so the paper
  has no meaning at `a = b`;
  `x ≠ a` is automatic, since `0 < W`;
* one constant `C` for the scale of `W` and for the threshold: the larger of two constants serves
  for both, so this is the same statement;
* the conclusion holds on every outcome. -/
def StraightStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized →
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ∃ W : X.Ω → ℝ, (∀ ω, Real.log (2 + r) ≤ W ω) ∧
        Cited.IsOs X.P 2 (C * Real.log (2 + r)) W ∧
        ∀ ω, ∀ a ∈ closedBall (0 : Pt m) r, ∀ b ∈ closedBall (0 : Pt m) r, a ≠ b →
          ∀ γ : RectifiableCurve (Pt m), IsOneOptimal (X.ρ ω) univ a b γ →
            ∀ t ∈ Icc (0 : ℝ) 1, C * W ω ^ 2 ≤ ‖γ.toFun t - a‖ →
              InnerProductGeometry.angle (γ.toFun t - a) (b - a) ≤ 1 / 10

/-- The pairs of points of equation `eq:slab`: `x` and `y` on different
faces of the slab, in either order, with `|x − z| ≤ s` and `|y − x| ≤ 5^{1/2} s`, for `s` the
width. -/
def IsSlabPair {m : ℕ} (sl : Slab m) (z x y : Pt m) : Prop :=
  (x ∈ sl.face₀ ∧ y ∈ sl.face₁ ∨ x ∈ sl.face₁ ∧ y ∈ sl.face₀) ∧
    ‖x - z‖ ≤ sl.width ∧ ‖y - x‖ ≤ Real.sqrt 5 * sl.width

/-- **Lemma `lem:slab`**: for a slab `P` of width `s > 2` and `z ∈ ℝ^d`,
equation `eq:slab`, `0 ≤ sup (T_P − T) ≤ O_1(C log²(2 + s))`, the supremum over the pairs
`IsSlabPair`; and for every positive integer `M`, every `s > 2` and every `τ ∈ ℝ^d`, equation
`eq:columns`, `0 ≤ F_τ − T(τ, τ + Ms e₁) ≤ O_1(C M log²(2 + Ms))`, which at `τ = 0` is the
bound `0 ≤ F − T_{Ms} ≤ O_1(C M log²(2 + Ms))`.

Readings:
* `T_P` is `X.slabTime b P`, with any deterministic upper bound `b` of the density in place of
  `sup ρ`;
* the lower bounds are stated pair by pair and on every outcome, which is stronger, and which has
  a meaning when there is no pair (`z` far from the slab);
* the supremum is a real `⨆`. It is a genuine supremum: the segment `[x, y]` lies in the slab, so
  `T_P(x, y) − T(x, y) ≤ 5^{1/2} b s` at every pair, and `IsOs` carries its a.e. measurability. -/
def SlabStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∃ C : ℝ, 0 < C ∧
      (∀ (sl : Slab m) (z : Pt m), 2 < sl.width →
        (∀ ω, ∀ x y : Pt m, IsSlabPair sl z x y →
          0 ≤ X.slabTime b sl ω x y - X.passTime ω x y) ∧
        Cited.IsOs X.P 1 (C * Real.log (2 + sl.width) ^ 2) (fun ω =>
          ⨆ p : {p : Pt m × Pt m // IsSlabPair sl z p.1 p.2},
            (X.slabTime b sl ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2))) ∧
      ∀ (M : ℕ) (s : ℝ) (τ : Pt m), 1 ≤ M → 2 < s →
        (∀ ω, 0 ≤ X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁)) ∧
        Cited.IsOs X.P 1 (C * M * Real.log (2 + M * s) ^ 2) (fun ω =>
          X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁))

/-- **Lemma `lem:polynomialarray`** (penalized sums of independent
arrays): with `d − 1 = m`, there is `C` such that for `M` independent arrays of nonnegative random
variables `Z_i(j, k)`, `j, k ∈ ℤ^m`, with `E[Z_i(j, k)^{4d}] ≤ 1`,
`E sup_{k₁, …, k_M} {Σ_i Z_i(k_{i−1}, k_i) − Σ_i |k_i − k_{i−1}|²} ≤ CM`, `k₀ = 0`. The statement
of `Infra.Arrays.lintegral_iSup_penalizedSum_le_of_square` (`k_{i−1}` is `pathPt 0 k i`). -/
def PenalizedArraysStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (Ω : Type u) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ),
      (∀ i j k, Measurable (fun ω => Z i ω j k)) →
      (∀ i ω j k, 0 ≤ Z i ω j k) →
      iIndepFun Z P →
      (∀ i j k, Integrable (fun ω => Z i ω j k ^ (4 * (m + 1))) P) →
      (∀ i j k, ∫ ω, Z i ω j k ^ (4 * (m + 1)) ∂P ≤ 1) →
      (∫⁻ ω, ⨆ k : Fin M → Fin m → ℤ,
        ENNReal.ofReal ((∑ i : Fin M, Z i ω (Infra.Arrays.pathPt 0 k i) (k i)) -
          ∑ i : Fin M, ∑ j : Fin m,
            ((k i j : ℝ) - (Infra.Arrays.pathPt 0 k i j : ℝ)) ^ 2) ∂P) ≤
        ENNReal.ofReal (C * M)

/-- Lemma `lem:polynomialarray` holds, by the `L²` counting of the paper's proof. -/
theorem penalizedArraysStatement_holds : PenalizedArraysStatement.{u} :=
  fun m => Infra.Arrays.lintegral_iSup_penalizedSum_le_of_square m

end IsotropicVariance.Paper.Contracts
