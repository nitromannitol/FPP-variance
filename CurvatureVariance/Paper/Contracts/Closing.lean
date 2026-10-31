/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Mean
public import CurvatureVariance.Statements.Curvature.AssumptionCAt
public import CurvatureVariance.Statements.Curvature.AssumptionCWith
public import CurvatureVariance.Statements.Space.FloorVertex

/-!
# Contracts of the closing: the induction, the reduction and the main theorems

The proof of Theorem `thm:main` given Proposition `prop:induction`, and the choice of coordinates
(the start of Section `sec:prelim`).

* `MainExpStatement`: Theorem `thm:main`: the statement of the main theorem
  `CurvatureVariance.lintegral_exp_passageTime_le`, written out here.
* `VarianceSentenceStatement`: the sentence after Theorem `thm:main`, with the `ε` and the `C` of
  the same theorem.
* `MainUniformStatement`, `MainTheoremStatement`: the statements of the theorems
  `CurvatureVariance.evariance_passageTime_floorVertex_le_uniform` and
  `CurvatureVariance.evariance_passageTime_floorVertex_le`, written out here. Neither is stated in
  the paper.
* `BaseCaseStatement`: the lengths below the threshold of the induction, and the points with `|x|`
  small.
* `DomainExpStatement`: equation `eq:premise` at every length, for one `K` and `A`.
* `ReductionUniformStatement`: the choice of coordinates, for the law of `T(0, x)` at every `x`.
* `ReductionStatement`, `OwnBoundsStatement`, `FinalTargetStatement`: the route to the theorem at
  one direction, `CurvatureVariance.evariance_passageTime_floorVertex_le`, which is not in the
  paper.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper

/-- **The base case** (the second sentence and the last sentence of the proof of Theorem `thm:main`
given Proposition `prop:induction`): for every `x ∈ ℤ^d` there is `θ > 0`, depending only on `x`
and the law, with `|T(0,x) − μ(x)| ≤ O₁(θ)`. The paper bounds `T(0,x)` by the passage time along a
path of a bounded number of edges, which has an exponential moment by (W). -/
def BaseCaseStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ x : Vertex m, ∃ θ : ℝ, 0 < θ ∧
  ∀ M : Model m, M.Standing → M.Fits bd →
    IsAbsOs M.P 1 θ (fun ω => passageTimeReal ω 0 x - M.μ.1 (point x))

/-- **Equation `eq:premise` at every length** (the third sentence of the proof of Theorem `thm:main`
given Proposition `prop:induction`: "By Proposition `prop:induction` and induction on `N`, it holds
for every integer `s ≥ 1`"):
there is `K₀` such that, for every `K ≥ K₀` with `K ≥ 10⁴`, there is `A ≥ 1`, depending only on the
bounds and `K`, such that `Paper.Premise M K A N` holds for every model that fits the bounds and
every `N`.

The statement is for every large `K`, for the reason given at `ImprovementAllKStatement`: the
paper's one `K` is a common `K` for the `2d` laws of the chosen coordinates. -/
def DomainExpStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → 10 ^ 4 ≤ K → ∃ A : ℝ, 1 ≤ A ∧
  ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, Premise M K A N

/-- **Theorem `thm:main`** at dimension `d = m + 1`: the statement of the main theorem
`CurvatureVariance.lintegral_exp_passageTime_le`, written out here. Its conclusion is
`E[exp(|T(0,x) − μ(x)| / (C|x|^{(1−ε)/2}))] ≤ 2`, with the measurability of `T(0,x)`; the paper's
`Λ, λ` are `M, c`. -/
def MainExpStatement (m : ℕ) : Prop :=
  ∀ (_ : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F], AssumptionW m F →
  ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
  ∀ μ : PtNorm m, IsTimeConstant P μ →
  ∀ δ r M c : ℝ, 0 < δ → δ ≤ 1 → 0 < r → 0 ≤ M → 0 < c →
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - μ.1 (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2

/-- **The sentence after Theorem `thm:main`**: "Theorem `thm:main` implies that
`Var[T(0,x)] ≤ 2C²|x|^{1−ε}` for every such `x`." One statement gives the bound of Theorem
`thm:main` and the variance bound, so that `ε` and `C` are shared. -/
def VarianceSentenceStatement (m : ℕ) : Prop :=
  ∀ (_ : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F], AssumptionW m F →
  ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
  ∀ μ : PtNorm m, IsTimeConstant P μ →
  ∀ δ r M c : ℝ, 0 < δ → δ ≤ 1 → 0 < r → 0 ≤ M → 0 < c →
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - μ.1 (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 ∧
            evariance (fun ω => (passageTime ω 0 x : ℝ)) P ≤
              ENNReal.ofReal (2 * C ^ 2 * ‖point x‖ ^ (1 - ε))

/-- **The main theorem, uniform in the direction** at dimension `d = m + 1`: the statement of the
theorem `CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`, written out here. It is
not stated in the paper: it is a consequence of the sentence after Theorem `thm:main`. -/
def MainUniformStatement (m : ℕ) : Prop :=
  ∀ (_ : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F], AssumptionW m F →
  ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
  ∀ μ : PtNorm m, IsTimeConstant P μ →
  ∀ δ r M c : ℝ, 0 < δ → δ ≤ 1 → 0 < r → 0 ≤ M → 0 < c →
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ n : ℕ, n₀ ≤ n →
        evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P ≤
          ENNReal.ofReal ((n : ℝ) ^ (1 - ε))

/-- **The main theorem at one direction** at dimension `d = m + 1`: the statement of the theorem
`CurvatureVariance.evariance_passageTime_floorVertex_le`, written out here. It is not in the
paper. -/
def MainTheoremStatement (m : ℕ) : Prop :=
  ∀ (_ : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F], AssumptionW m F →
  ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
  ∀ μ : PtNorm m, IsTimeConstant P μ → ∀ ξ : Pt m, ξ ≠ 0 → ∀ H : Submodule ℝ (Pt m),
    IsCompl (Submodule.span ℝ {ξ}) H → AssumptionCAt μ ξ H →
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P ≤
        ENNReal.ofReal ((n : ℝ) ^ (1 - ε))

/-- **The choice of coordinates for Theorem `thm:main`** (the start of Section `sec:prelim`, and the
last sentences of the proof of Theorem `thm:main` given Proposition `prop:induction`). Under the
hypotheses of the theorem there is `hi > 0` with `μ ≤ hi |·|` such that, for the constants
`δ, r, M, c` of (Curv), there are finitely many laws (indexed by the chosen coordinate and the sign
of the signed permutation) with the following property. For every unit vector `ξ` satisfying (Curv)
with these constants, there are an index `j`, a model satisfying the standing hypotheses and fitting
the bounds `chartBounds (law j) hi r M c` of Lemma `lem:chart`, a map `Φ` of the vertices and
`a ∈ [d^{−1/2}, 1]`, such that, for every vertex `x`:

* `T(0, x)` under `P` has the law of `T(0, Φx)` in the model;
* `μ(x)` is the time constant of the model at `Φx`;
* `|x − βξ| = |Φx − βa(1, t₀)|` for every real `β`.

The last clause says that `Φ` carries the ray `ℝ₊ξ` to the ray of the slope `t₀`, with `ξ = a(1,
t₀)` and `a = ξ₁`, so it gives the distance from `x` to the ray and, at `β = 0`, `|x| = |Φx|`, so `x
≠ 0` gives `Φx ≠ 0`. The paper says only that "permutations and sign changes of the coordinates
preserve the law of the weights, `μ` and (Curv)"; a Lean model has fixed coordinates, so the
transport is a statement. In the proof the chosen coordinate is a largest coordinate of `ξ`, `a` is
its absolute value, and `Φ` is the signed permutation. -/
def ReductionUniformStatement (m : ℕ) : Prop :=
  ∀ (_ : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F], AssumptionW m F →
  ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
  ∀ μ : PtNorm m, IsTimeConstant P μ →
  ∃ hi : ℝ, 0 < hi ∧ (∀ x : Pt m, μ.1 x ≤ hi * ‖x‖) ∧
  ∀ δ r M c : ℝ, 0 < δ → δ ≤ 1 → 0 < r → 0 ≤ M → 0 < c →
  ∃ law : Option (Fin m) × Bool → Law m, (∀ j, (law j).Valid ∧ (law j).δ = δ) ∧
  ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
    ∃ (j : Option (Fin m) × Bool) (Md : Model m) (Φ : Vertex m → Vertex m) (a : ℝ),
      Md.Standing ∧ Md.Fits (chartBounds (law j) hi r M c) ∧
      1 / Real.sqrt ((m : ℝ) + 1) ≤ a ∧ a ≤ 1 ∧
      (∀ x : Vertex m, Measure.map (fun ω => passageTimeReal ω 0 x) P =
        Measure.map (fun ω => passageTimeReal ω 0 (Φ x)) Md.P) ∧
      (∀ x : Vertex m, Md.μ.1 (point (Φ x)) = μ.1 (point x)) ∧
      ∀ (x : Vertex m) (β : ℝ),
        ‖point (Φ x) - (β * a) • slopeVec Md.t₀‖ = ‖point x - β • ξ‖

/-- **The choice of coordinates at one direction** (not in the paper; for the theorem
`CurvatureVariance.evariance_passageTime_floorVertex_le`): under the hypotheses of the theorem at
one direction there are a model `M` satisfying the standing hypotheses, a map `Φ` of the vertices
and constants `a > 0`, `C₀` such that, for every `n`, the variance of `T(0, ⌊nξ⌋)` under `P` is the
variance of `T(0, Φ⌊nξ⌋)` under `M.P`, and `|Φ⌊nξ⌋ − n a (1, t₀)| ≤ C₀`, with `t₀` the slope of the
model. In the proof, `Φ` is the signed permutation that passes to the chosen ordered and oriented
coordinates (so `ξ = a(1, t₀)` in these coordinates, `a` the absolute value of the chosen coordinate
of `ξ`), the model's time constant is `μ` composed with it, and Lemma `lem:chart` (`ChartStatement`)
gives the expansion. -/
def ReductionStatement (m : ℕ) : Prop :=
  ∀ (_ : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F], AssumptionW m F →
  ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
  ∀ μ : PtNorm m, IsTimeConstant P μ → ∀ ξ : Pt m, ξ ≠ 0 → ∀ H : Submodule ℝ (Pt m),
    IsCompl (Submodule.span ℝ {ξ}) H → AssumptionCAt μ ξ H →
    ∃ (M : Model m) (Φ : Vertex m → Vertex m) (a C₀ : ℝ), M.Standing ∧ 0 < a ∧
      (∀ n : ℕ, evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P =
        evariance (fun ω => passageTimeReal ω 0 (Φ (floorVertex ((n : ℝ) • ξ)))) M.P) ∧
      ∀ n : ℕ, ‖point (Φ (floorVertex ((n : ℝ) • ξ))) - ((n : ℝ) * a) • slopeVec M.t₀‖ ≤ C₀

/-- **Every model fits bounds of its own** (not in the paper): its law, its radius and remainder
constant, the least and greatest values of `q₀` on the unit sphere (positive definiteness and
continuity), and `T = |t₀|`. With it the uniform contracts give the theorem at one direction. -/
def OwnBoundsStatement (m : ℕ) : Prop :=
  ∀ M : Model m, M.Standing → ∃ bd : Bounds m, bd.Valid ∧ M.Fits bd

/-- **The final target** (not in the paper; for the theorem
`CurvatureVariance.evariance_passageTime_floorVertex_le`): for `0 < a₀ ≤ a₁` and `C₀` there is a
threshold `n₁`, depending only on the bounds, `a₀`, `a₁` and `C₀`, such that, if the vertices
`z n = (s_n, y_n)` stay within `C₀` of `n a (1, t₀)` with `a ∈ [a₀, a₁]`, then for `n ≥ n₁`,
`1 ≤ s_n ≤ (a + 1) n` and `y_n ∈ 𝒟(s_n)`. -/
def FinalTargetStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ a₀ a₁ C₀ : ℝ, 0 < a₀ → a₀ ≤ a₁ → ∃ n₁ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd → ∀ a : ℝ, a₀ ≤ a → a ≤ a₁ → ∀ z : ℕ → Vertex m,
    (∀ n : ℕ, ‖point (z n) - ((n : ℝ) * a) • slopeVec M.t₀‖ ≤ C₀) →
    ∀ n : ℕ, n₁ ≤ n → ∃ s : ℕ, 1 ≤ s ∧ (s : ℝ) ≤ (a + 1) * n ∧
      (z n).1 = s ∧ (z n).2 ∈ premiseDomain M s

/-! ## Arithmetic of the closing -/

/-- The arithmetic of the theorem at one direction (`MainTheoremStatement`, not in the paper): for
`ε' ≤ ε`, `ε' ≤ 1/4`, `1 ≤ s ≤ (a + 1) n` and `max C 1 · (a + 1) ≤ n^{ε'}`,
`C s^{1−2ε} ≤ n^{1−ε'}`. -/
theorem mul_rpow_le_rpow_of_le {C ε e a : ℝ} {s n : ℝ} (he : 0 < e) (he4 : e ≤ 1 / 4)
    (hee : e ≤ ε) (ha : 0 < a) (hs : 1 ≤ s) (hsn : s ≤ (a + 1) * n)
    (hB : max C 1 * (a + 1) ≤ n ^ e) : C * s ^ (1 - 2 * ε) ≤ n ^ (1 - e) := by
  have hn : 0 < n := by nlinarith
  have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have h1 : C * s ^ (1 - 2 * ε) ≤ max C 1 * s ^ (1 - 2 * e) := by
    have hpow : s ^ (1 - 2 * ε) ≤ s ^ (1 - 2 * e) :=
      Real.rpow_le_rpow_of_exponent_le hs (by linarith)
    calc C * s ^ (1 - 2 * ε) ≤ max C 1 * s ^ (1 - 2 * ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ max C 1 * s ^ (1 - 2 * e) := mul_le_mul_of_nonneg_left hpow (by linarith)
  have h2 : s ^ (1 - 2 * e) ≤ (a + 1) * n ^ (1 - 2 * e) := by
    calc s ^ (1 - 2 * e) ≤ ((a + 1) * n) ^ (1 - 2 * e) :=
          Real.rpow_le_rpow (by linarith) hsn (by linarith)
      _ = (a + 1) ^ (1 - 2 * e) * n ^ (1 - 2 * e) := Real.mul_rpow (by linarith) hn.le
      _ ≤ (a + 1) * n ^ (1 - 2 * e) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hn.le _)
          calc (a + 1) ^ (1 - 2 * e) ≤ (a + 1) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ = a + 1 := Real.rpow_one _
  have h3 : n ^ e * n ^ (1 - 2 * e) = n ^ (1 - e) := by
    rw [← Real.rpow_add hn]; ring_nf
  calc C * s ^ (1 - 2 * ε) ≤ max C 1 * ((a + 1) * n ^ (1 - 2 * e)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    _ = max C 1 * (a + 1) * n ^ (1 - 2 * e) := by ring
    _ ≤ n ^ e * n ^ (1 - 2 * e) :=
        mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hn.le _)
    _ = n ^ (1 - e) := h3

/-- `B ≤ n^e` once `n ≥ ⌈B^{1/e}⌉₊`, for `B > 0` and `e > 0`. -/
theorem le_rpow_of_ceil_le {B e : ℝ} (hB : 0 < B) (he : 0 < e) {n : ℕ}
    (hn : ⌈B ^ (1 / e)⌉₊ ≤ n) : B ≤ (n : ℝ) ^ e := by
  have h1 : B ^ (1 / e) ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  calc B = (B ^ (1 / e)) ^ e := by
        rw [← Real.rpow_mul hB.le, show 1 / e * e = 1 by field_simp, Real.rpow_one]
    _ ≤ (n : ℝ) ^ e := Real.rpow_le_rpow (Real.rpow_nonneg hB.le _) h1 he.le

end CurvatureVariance.Paper.Contracts
