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
# The definitions of the lattice challenge

A verbatim copy of the definitions of the lattice challenge (everything in it before its
theorems), with the same imports, so that every definition elaborates exactly as in the challenge.
Only this docstring differs. The solution imports this module and the library, relates these
definitions to the library's, and proves the challenge's theorems.
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

end LatticeVariance
