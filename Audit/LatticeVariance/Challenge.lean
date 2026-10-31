/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Challenge: an exponential-moment bound for lattice first-passage percolation

This module states the main theorem of the paper *Curvature and variance in lattice first-passage
percolation*, Theorem 1.1 (`thm:main`), and the variance bound that follows from it, using only
Mathlib. Every notion the theorems use is defined below, as the paper defines it.

* **Weights.** On `ℤ^d`, `d = m + 1 ≥ 2`, the nearest-neighbour edges carry independent weights
  with common law `F` (the paper's `ν`) on `[0, ∞)`, and `T(u, v)` is the infimum, over the
  nearest-neighbour walks from `u` to `v`, of the sum of the weights of their edges.
* **(W).** `F` has an exponential moment, and `F({0}) < p_c(d)`, the critical probability of bond
  percolation on `ℤ^d`.
* **(Curv).** A unit vector `ξ ∈ ℝ^d` satisfies (Curv) with the constants `δ ∈ (0, 1]`, `r > 0`,
  `M ≥ 0` and `c > 0` (the paper's `Λ` and `λ`) when the time constant `μ` is curved on the affine
  hyperplane `ξ + ξ^⊥`: `μ(ξ + h) - μ(ξ)` is a linear functional plus a quadratic form
  `q(h) ≥ c |h|²` in `h ∈ ξ^⊥`, up to `M |h|^{2+δ}` for `|h| ≤ r`.
* **Conclusion** (`lintegral_exp_passageTime_le`). For all such constants there are `ε > 0` and
  `C > 0` such that, for every unit vector `ξ` satisfying (Curv) with these constants and every
  `x ∈ ℤ^d ∖ {0}` within distance `|x|^{3/4}` of the ray `ℝ₊ξ`, `T(0, x)` is a random variable
  (almost everywhere measurable) with `E[exp(|T(0, x) − μ(x)| / (C |x|^{(1−ε)/2}))] ≤ 2`. The
  numbers `ε` and `C` are chosen before `ξ` and `x`, so they do not depend on them. The distance
  condition asks for a point `βξ`, `β ≥ 0`, within `|x|^{3/4}` of `x`: the ray is closed, so it
  contains a nearest point of `x`. The exponential moment is a Lebesgue integral, with values in
  `[0, ∞]`.
* **Variance.** As the paper notes after Theorem 1.1, the bound gives `Var T(0, x) ≤ 2C²|x|^{1−ε}`
  for every such `x`. The theorem `variance_passageTime_floorVertex_le_uniform` states it along the
  ray, with a smaller exponent which absorbs the constant: there are `ε > 0` and `n₀`, chosen before
  `ξ`, such that `Var T(0, ⌊nξ⌋) ≤ n^{1-ε}` for every integer `n ≥ n₀`, the floor taken
  coordinatewise. The variance is Mathlib's `evariance`, with values in `[0, ∞]`.

The paper describes two objects by a characterization, and both are written here as explicit
formulas:

* The law of the configuration is the product measure `weightLaw m F`. The companions
  `weightLaw_iid` and `eq_weightLaw` state that the weights are independent with law `F` under it,
  and that it is the only such law.
* The time constant is `timeConstant m F x = lim_{n → ∞} E T(0, ⌊n x⌋) / n`, the integer part taken
  coordinatewise. The companions `tendsto_integral_passageTime_div`, `timeConstant_isNorm` and
  `ae_tendsto_passageTime_div` state, under (W), that this limit exists, that the function is a
  norm on `ℝ^d`, and that it is the paper's time constant: almost surely
  `T(0, n x) / n → μ(x)` for every `x ∈ ℤ^d`.

Every theorem below is left unproved here. The solution proves the same statements from the
library, and leanprover/comparator checks that the two agree, definitions included.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LatticeVariance

/-! ## The lattice and the weights -/

/-- The vertices of `ℤ^d = ℤ × ℤ^m`, `d = m + 1`. The product only indexes the `d` coordinates:
no direction is distinguished. -/
abbrev Vertex (m : ℕ) : Type := ℤ × (Fin m → ℤ)

/-- The nearest-neighbour graph of `ℤ^d`: `x` and `y` are adjacent when one is obtained from the
other by adding a unit coordinate vector. -/
def latticeGraph (m : ℕ) : SimpleGraph (Vertex m) :=
  SimpleGraph.fromRel fun x y => y = x + (1, 0) ∨ ∃ j : Fin m, y = x + (0, Pi.single j 1)

/-- The nearest-neighbour edges of `ℤ^d`. -/
abbrev Edge (m : ℕ) : Type := (latticeGraph m).edgeSet

/-- Weight configurations: a weight `ω e ≥ 0` on every nearest-neighbour edge. -/
abbrev Config (m : ℕ) : Type := Edge m → ℝ≥0

/-- The law of the configuration: the weights are independent, each with law `F` (the product
measure; see `weightLaw_iid` and `eq_weightLaw`). -/
noncomputable def weightLaw (m : ℕ) (F : Measure ℝ≥0) : Measure (Config m) :=
  Measure.infinitePi fun _ : Edge m => F

/-- The cost of a walk: the sum of the weights of its edges, with multiplicity. -/
def walkCost {m : ℕ} (ω : Config m) {u v : Vertex m} (p : (latticeGraph m).Walk u v) : ℝ≥0 :=
  (p.darts.map fun t => ω ⟨t.edge, t.edge_mem⟩).sum

/-- The first-passage time `T(u, v) = inf_π ∑_{e ∈ π} ω e` over the nearest-neighbour walks `π`
from `u` to `v`. -/
noncomputable def passageTime {m : ℕ} (ω : Config m) (u v : Vertex m) : ℝ≥0 :=
  ⨅ p : (latticeGraph m).Walk u v, walkCost ω p

/-! ## Bond percolation and Assumption (W) -/

/-- The open subgraph of bond percolation on `ℤ^d`: its edges are those of the set `S`. -/
def openGraph (m : ℕ) (S : Set (Edge m)) : SimpleGraph (Vertex m) :=
  SimpleGraph.fromEdgeSet ((↑) '' S)

/-- The percolation probability `θ(p)`: when each edge is open independently with probability `p`
(Mathlib's `setBernoulli`, the law of the random set of open edges), the probability that the open
cluster of the origin is infinite. -/
noncomputable def percolationProb (m : ℕ) (p : unitInterval) : ℝ≥0∞ :=
  setBernoulli (Set.univ : Set (Edge m)) p {S | {x | (openGraph m S).Reachable 0 x}.Infinite}

/-- The critical probability `p_c(d) = sup {p : θ(p) = 0}` of bond percolation on `ℤ^d`. -/
noncomputable def bondCriticalProb (m : ℕ) : ℝ :=
  sSup (Subtype.val '' {p : unitInterval | percolationProb m p = 0})

/-- **Assumption (W)** on the common law `F` of the weights (the paper's `ν`): it has an exponential
moment, and its mass at zero is smaller than the critical probability `p_c(d)`. Independence is
built into `weightLaw`. -/
def AssumptionW (m : ℕ) (F : Measure ℝ≥0) : Prop :=
  (∃ α : ℝ, 0 < α ∧ Integrable (fun x : ℝ≥0 => Real.exp (α * x)) F) ∧
    F {0} < ENNReal.ofReal (bondCriticalProb m)

/-! ## The time constant and Assumption (Curv) -/

/-- The space `ℝ^d`, `d = m + 1`, as the `L²` product `ℝ × ℝ^m`, which carries the Euclidean norm.
The product only indexes the `d` coordinates. -/
abbrev Pt (m : ℕ) : Type := WithLp 2 (ℝ × EuclideanSpace ℝ (Fin m))

/-- A vertex as a point of `ℝ^d`. -/
def point {m : ℕ} (x : Vertex m) : Pt m :=
  WithLp.toLp 2 ((x.1 : ℝ), WithLp.toLp 2 fun j => (x.2 j : ℝ))

/-- The vertex `⌊x⌋` below a point `x` of `ℝ^d`: the floor of every coordinate, in the lattice
coordinates. -/
noncomputable def floorVertex {m : ℕ} (x : Pt m) : Vertex m :=
  (⌊x.ofLp.1⌋, fun j => ⌊x.ofLp.2 j⌋)

/-- **The time constant** `μ(x) = lim_{n → ∞} E T(0, ⌊n x⌋) / n` for `x ∈ ℝ^d`, under the product
law of the weights. Under (W) the limit exists (`tendsto_integral_passageTime_div`), `μ` is a norm
(`timeConstant_isNorm`), and `T(0, n x) / n → μ(x)` almost surely for `x ∈ ℤ^d`
(`ae_tendsto_passageTime_div`). -/
noncomputable def timeConstant (m : ℕ) (F : Measure ℝ≥0) (x : Pt m) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (∫ ω, (passageTime ω 0 (floorVertex ((n : ℝ) • x)) : ℝ) ∂weightLaw m F) / n

/-- **Assumption (Curv)** at the unit vector `ξ` with the constants `δ`, `r`, `M` and `c` (the
paper's `Λ` and `λ`): with `H = ξ^⊥` the orthogonal hyperplane, there exist a linear functional
`ℓ_H : H → ℝ` and a quadratic form `q_H` on `H` with `q_H(h) ≥ c |h|²` for every `h ∈ H` such that,
for every `h ∈ H` with `|h| ≤ r`, `|μ(ξ + h) - μ(ξ) - ℓ_H(h) - q_H(h)| ≤ M |h|^{2+δ}`. Here `|h|`
is the Euclidean norm of `ℝ^d`. The ranges `δ ∈ (0, 1]`, `r > 0`, `M ≥ 0`, `c > 0` and `|ξ| = 1`
are hypotheses of the theorems. -/
def AssumptionCWith {m : ℕ} (μ : Pt m → ℝ) (ξ : Pt m) (δ r M c : ℝ) : Prop :=
  ∃ ℓ : Module.Dual ℝ (Submodule.span ℝ {ξ})ᗮ, ∃ q : QuadraticForm ℝ (Submodule.span ℝ {ξ})ᗮ,
    (∀ h, c * ‖h‖ ^ 2 ≤ q h) ∧
      ∀ h : (Submodule.span ℝ {ξ})ᗮ, ‖h‖ ≤ r →
        |μ (ξ + h) - μ ξ - ℓ h - q h| ≤ M * ‖h‖ ^ (2 + δ)

/-! ## The theorems -/

/-- **Exponential-moment bound** (Theorem 1.1, `thm:main`). Let `d = m + 1 ≥ 2` and let the
weights be independent with common law `F` satisfying (W). For all `δ ∈ (0, 1]`, `r > 0`, `M ≥ 0`
and `c > 0` there are `ε > 0` and `C > 0` such that, for every unit vector `ξ` satisfying (Curv)
with these constants and every `x ∈ ℤ^d ∖ {0}` within distance `|x|^{3/4}` of the ray `ℝ₊ξ`, the
passage time `T(0, x)` is a random variable with
`E[exp(|T(0, x) − μ(x)| / (C |x|^{(1−ε)/2}))] ≤ 2`. Since `ε` and `C` come before `ξ` and `x`,
they depend only on `d`, `F`, `δ`, `r`, `M` and `c`. -/
theorem lintegral_exp_passageTime_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 →
      AssumptionCWith (timeConstant m F) ξ δ r M c → ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) (weightLaw m F) ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - timeConstant m F (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂weightLaw m F ≤ 2 := by
  sorry

/-- **Variance bound** along the ray, which follows from Theorem 1.1 (`thm:main`), as the paper
notes after it. Let `d = m + 1 ≥ 2` and let the weights be independent with common law `F`
satisfying (W). For all `δ ∈ (0, 1]`, `r > 0`, `M ≥ 0` and `c > 0` there are `ε > 0` and `n₀` such
that, for every unit vector `ξ` satisfying (Curv) with these constants, `Var T(0, ⌊nξ⌋) ≤ n^{1-ε}`
for every integer `n ≥ n₀`. Since `ε` and `n₀` come before `ξ`, they depend only on `d`, `F`, `δ`,
`r`, `M` and `c`. The variance is Mathlib's `evariance`, with values in `[0, ∞]`; a finite value
means that `T(0, ⌊nξ⌋)` is square integrable once it is almost everywhere measurable, which
`lintegral_exp_passageTime_le` gives for these points. -/
theorem variance_passageTime_floorVertex_le_uniform {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ ξ : Pt m, ‖ξ‖ = 1 →
      AssumptionCWith (timeConstant m F) ξ δ r M c → ∀ n : ℕ, n₀ ≤ n →
        evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) (weightLaw m F) ≤
          ENNReal.ofReal ((n : ℝ) ^ (1 - ε)) := by
  sorry

/-! ## Companions: the explicit formulas are the paper's objects -/

/-- Under `weightLaw m F` the weights are independent, each with law `F`. -/
theorem weightLaw_iid (m : ℕ) (F : Measure ℝ≥0) [IsProbabilityMeasure F] :
    iIndepFun (fun (e : Edge m) (ω : Config m) => ω e) (weightLaw m F) ∧
      ∀ e : Edge m, HasLaw (fun ω : Config m => ω e) F (weightLaw m F) := by
  sorry

/-- `weightLaw m F` is the only law of the configuration under which the weights are independent,
each with law `F`. -/
theorem eq_weightLaw {m : ℕ} {F : Measure ℝ≥0} {P : Measure (Config m)}
    (hind : iIndepFun (fun (e : Edge m) (ω : Config m) => ω e) P)
    (hlaw : ∀ e : Edge m, HasLaw (fun ω : Config m => ω e) F P) :
    P = weightLaw m F := by
  sorry

/-- Under (W), the limit defining `timeConstant m F x` exists. -/
theorem tendsto_integral_passageTime_div {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (x : Pt m) :
    Tendsto (fun n : ℕ =>
        (∫ ω, (passageTime ω 0 (floorVertex ((n : ℝ) • x)) : ℝ) ∂weightLaw m F) / n)
      atTop (𝓝 (timeConstant m F x)) := by
  sorry

/-- Under (W), the time constant is a norm on `ℝ^d`: a seminorm that vanishes only at `0`. -/
theorem timeConstant_isNorm {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) :
    ∃ μ : Seminorm ℝ (Pt m), ⇑μ = timeConstant m F ∧ ∀ x, μ x = 0 → x = 0 := by
  sorry

/-- Under (W), the time constant is the paper's: for every `x ∈ ℤ^d`, almost surely
`T(0, n x) / n → μ(x)` as `n → ∞`. -/
theorem ae_tendsto_passageTime_div {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (x : Vertex m) :
    ∀ᵐ ω ∂weightLaw m F,
      Tendsto (fun n : ℕ => (passageTime ω 0 (n • x) : ℝ) / n) atTop
        (𝓝 (timeConstant m F (point x))) := by
  sorry

end LatticeVariance
