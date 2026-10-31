/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
public import CurvatureVariance.Paper.Defs.Good
public import CurvatureVariance.Statements.Curvature.AssumptionCAt
public import CurvatureVariance.Statements.Curvature.AssumptionCWith

/-!
# Contracts of Section `sec:prelim`: the chart, rounding, classical bounds, the good event, cones

The statements of Section `sec:prelim` of the lattice paper.

* `ChartStatement` — Lemma `lem:chart` at one direction, for the theorem
  `CurvatureVariance.evariance_passageTime_floorVertex_le`.
* `ChartUniformStatement` — Lemma `lem:chart`, with explicit constants.
* `RoundingStatement` — equation `eq:rounding`.
* `ClassicalStatement` — equation `eq:classical`.
* `GeodesicLengthStatement` — the edge count of geodesics and of geodesics in a slab (the text
  after equation `eq:classical`).
* `SupportStatement` — Lemma `lem:support`, equations `eq:support` and `eq:angular`.
* `GoodStatement` — Lemma `lem:good`: the events `𝒢_N(S)`.
* `ConeStatement` — Lemma `lem:cone`, equation `eq:cone`, deterministic on `Paper.IsGood`.
* `ChainsExistStatement` — the chains of equation `eq:F` exist for `n ≥ 64d`.
* `SlabsStatement` — Lemma `lem:slabs`, deterministic on `Paper.IsGood`.

All statements are under the standing hypotheses `Model.Standing`, in the coordinates chosen in the
start of Section `sec:prelim`. By the convention of Section `ssec:notation`, their constants and
thresholds come after a `Bounds` record and before the models that fit it (`Model.Fits`), so they
depend only on the law and the bounds, not on the direction.

The record `Bounds` has an upper bound `T` of the slope `|t₀|`, where the paper has
`|t₀| ≤ (d−1)^{1/2}`. So the constants here depend on `T` where the paper's constants use that
bound; each such place is named in the docstring of its statement. This generality is what the
theorem at one direction, `CurvatureVariance.evariance_passageTime_floorVertex_le`, needs, and
`chartBounds` has `T = √(d−1)`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set InnerProductGeometry
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper

/-- **Lemma `lem:chart`** at one direction, in the chosen coordinates, for the theorem
`CurvatureVariance.evariance_passageTime_floorVertex_le`, which is not in the paper: let the
direction `ξ = a(1, t₀)` have positive first coordinate `a = ξ₁`, so that `t₀ = ξ₁⁻¹ ξ'` with `ξ'`
the transverse part of `ξ`; let `H` be transverse to `ξ`, and let `AssumptionCAt` hold at `ξ` and
`H`. Then there are `δ ∈ (0, 1]`, `r₀ > 0`, `C ≥ 0`, `p₀ ∈ ℝ^{d-1}` and a positive definite
quadratic form `q₀` on `ℝ^{d-1}` (the form `h ↦ h·Σh`) such that
`|μ(1, t₀ + h) − μ(1, t₀) − p₀·h − q₀(h)| ≤ C |h|^{2+δ}` for `|h| ≤ r₀` (equation `eq:curvature`).
In the proof, `δ` is the exponent of `AssumptionCAt`.

The general case reduces to this one: a nonzero `ξ` has a coordinate `k₀` with `ξ_{k₀} ≠ 0`, and the
signed permutation of the coordinates that exchanges the first coordinate with `k₀` and gives it the
sign of `ξ_{k₀}` maps `ξ` to a vector with positive first coordinate. It transports `μ`, `H`,
`AssumptionCAt` and the law of the weights (`Contracts.ReductionStatement`). -/
def ChartStatement (m : ℕ) : Prop :=
  ∀ (μ : PtNorm m) (ξ : Pt m) (H : Submodule ℝ (Pt m)), 0 < ξ.ofLp.1 →
    IsCompl (Submodule.span ℝ {ξ}) H → AssumptionCAt μ ξ H →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∃ (p₀ : EuclideanSpace ℝ (Fin m)) (q₀ : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m))),
      q₀.PosDef ∧ ∀ h : EuclideanSpace ℝ (Fin m), ‖h‖ ≤ r₀ →
        |μ.1 (slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2 + h)) - μ.1 (slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2)) -
          inner ℝ p₀ h - q₀ h| ≤ C * ‖h‖ ^ (2 + δ)

/-- **Lemma `lem:chart` with explicit constants** (equation `eq:curvature`), at a unit direction
`ζ = (a, ζ')` whose first coordinate is a largest one (`|ζ_j| ≤ a` for every transverse `j`), for a
norm with `μ ≤ hi |·|` (the paper's `μ^*`): if (Curv) holds at `ζ` on `ζ^⊥` with the constants
`δ ∈ (0, 1]`, `r > 0`, `M ≥ 0` and `c > 0` (the paper's `Λ` and `λ`; `AssumptionCWith`), then at the
slope `t₀ = a⁻¹ ζ'` there are `p₀` and a quadratic form `q₀` with `c a³ |h|² ≤ q₀(h) ≤ Λ |h|²` and
`|μ(1, t₀ + h) − μ(1, t₀) − p₀·h − q₀(h)| ≤ (12M + 2Λ) |h|^{2+δ}` for `|h| ≤ min(1, r)/4`, where
`Λ = hi/r + M r^δ` (`chartLam`).

This is stronger than the paper's statement, which has an affine `ψ`, a symmetric `Σ` and generic
constants: the paper's `ψ(h)` is here `μ(1, t₀) + p₀·h`, and its `h·Σh` is `q₀(h)`. In the proof the
transversal functional is `x ↦ ⟨x, ζ⟩` and the projection onto `ζ^⊥` is orthogonal, so both have
norm at most `1`, and `q` is bounded by `Λ` through (Curv) at `h` and `−h` and
`μ(ζ ± h) ≤ μ(ζ) + hi |h|`. -/
def ChartUniformStatement (m : ℕ) : Prop :=
  ∀ (μ : PtNorm m) (hi : ℝ), 0 < hi → (∀ x : Pt m, μ.1 x ≤ hi * ‖x‖) →
  ∀ ζ : Pt m, ‖ζ‖ = 1 → 0 < ζ.ofLp.1 → (∀ j : Fin m, |ζ.ofLp.2 j| ≤ ζ.ofLp.1) →
  ∀ δ r M c : ℝ, 0 < δ → δ ≤ 1 → 0 < r → 0 ≤ M → 0 < c → AssumptionCWith μ ζ δ r M c →
    ∃ (p₀ : EuclideanSpace ℝ (Fin m)) (q₀ : QuadraticForm ℝ (EuclideanSpace ℝ (Fin m))),
      (∀ h, c * ζ.ofLp.1 ^ 3 * ‖h‖ ^ 2 ≤ q₀ h) ∧ (∀ h, q₀ h ≤ chartLam hi r M δ * ‖h‖ ^ 2) ∧
      ∀ h : EuclideanSpace ℝ (Fin m), ‖h‖ ≤ min 1 r / 4 →
        |μ.1 (slopeVec ((ζ.ofLp.1)⁻¹ • ζ.ofLp.2 + h)) - μ.1 (slopeVec ((ζ.ofLp.1)⁻¹ • ζ.ofLp.2)) -
          inner ℝ p₀ h - q₀ h| ≤ (12 * M + 2 * chartLam hi r M δ) * ‖h‖ ^ (2 + δ)

/-- **Equation `eq:rounding`**: for `x, x' ∈ ℝ^{d-1}` and `R ≥ 2√(d−1)` with `|x − x'| ≤ R`, there
is `z ∈ ℤ^{d-1}` with `|z − x'| ≤ R` and `|z − x| ≤ 2√(d−1)`. The Lean's `c` is the paper's `x'`.
The statement is existential, as in the paper: the "namely" of the paper names one admissible
point. -/
def RoundingStatement (m : ℕ) : Prop :=
  ∀ (c x : EuclideanSpace ℝ (Fin m)) (R : ℝ), 2 * Real.sqrt m ≤ R → ‖x - c‖ ≤ R →
    ∃ z : Fin m → ℤ, ‖transversePoint z - c‖ ≤ R ∧ ‖transversePoint z - x‖ ≤ 2 * Real.sqrt m

/-- **Equation `eq:classical`**: for `x ∈ ℤ^d \ {0}`, `r = |x|₁`, `|T(0,x) − E T(0,x)| ≤ O₁(C √r)`
and `0 ≤ E T(0,x) − μ(x) ≤ C √(r log(2 + r))`. The integrability of `T(0, x)` is added: it gives
the paper's expectations their meaning. -/
def ClassicalStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ C : ℝ, 0 < C ∧
  ∀ M : Model m, M.Standing → M.Fits bd → ∀ x : Vertex m, x ≠ 0 →
    Integrable (fun ω => passageTimeReal ω 0 x) M.P ∧
    IsAbsOs M.P 1 (C * Real.sqrt (oneNorm x))
      (fun ω => passageTimeReal ω 0 x - ∫ ω', passageTimeReal ω' 0 x ∂M.P) ∧
    0 ≤ (∫ ω, passageTimeReal ω 0 x ∂M.P) - M.μ.1 (point x) ∧
    (∫ ω, passageTimeReal ω 0 x ∂M.P) - M.μ.1 (point x) ≤
      C * Real.sqrt (oneNorm x * Real.log (2 + oneNorm x))

/-- **The edge count of geodesics** (the text after equation `eq:classical`): for all vertices
`u, v` there is one random variable `X ≤ O₁(C)` such that, almost surely, every geodesic from `u` to
`v`, and every geodesic in a slab `P = [p,q] × ℝ^{d−1}` from `u` to `v` (`p + 2 ≤ q`, both endpoints
in the slab), has at most `C (1 + |u − v|₁) + X` edges. One variable serves both, which is stronger
than the paper's two bounds. The bound is almost sure, as in the paper: for degenerate
configurations (all weights zero) every simple path is a geodesic. -/
def GeodesicLengthStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ C : ℝ, 0 < C ∧
  ∀ M : Model m, M.Standing → M.Fits bd → ∀ u v : Vertex m,
    ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 C X ∧ ∀ᵐ ω ∂M.P,
      (∀ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ →
        (γ.length : ℝ) ≤ C * (1 + oneNorm (v - u)) + X ω) ∧
      (∀ p q : ℤ, p + 2 ≤ q → p ≤ u.1 → u.1 ≤ q → p ≤ v.1 → v.1 ≤ q →
        ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω p q γ →
          (γ.length : ℝ) ≤ C * (1 + oneNorm (v - u)) + X ω)

/-- **Lemma `lem:support`**, equations `eq:support` and `eq:angular`: there is `r₁ ∈ (0, r₀/2]`, and
there are `c, C > 0`, such that, for slopes `|t − t₀| ≤ r₁`, `|h| ≤ r₁` and every subgradient
`ζ_t` of `μ` at `(1, t)`,
`c|h|² − C|t − t₀|^{2+δ} ≤ μ(1,t+h) − ζ_t·(1,t+h) ≤ C|h|² + C|t − t₀|^{2+δ}`, and, for `z ≠ 0`,
`μ(z) − ζ_t·z ≥ c|z| ∠(z,(1,t))² − C|z||t − t₀|^{2+δ}`.

Readings. The radius `bd.rrem` is the paper's `r₀`: `chartBounds` has `rrem = min(1, r)/4`. A
subgradient is `IsSubgradient` (the text before Lemma `lem:support`). The proof of equation
`eq:angular` takes `β = min{1/2, r₁/(2(1+(d−1)^{1/2}+r₁))}`, using `|t₀| ≤ (d−1)^{1/2}`. With
`Bounds.T` general, `T` replaces `(d−1)^{1/2}`, so `c` and `C` depend on `T`. -/
def SupportStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ c C r₁ : ℝ, 0 < c ∧ 0 < C ∧ 0 < r₁ ∧ r₁ ≤ bd.rrem / 2 ∧
  ∀ M : Model m, M.Standing → M.Fits bd →
    (∀ t h : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        c * ‖h‖ ^ 2 - C * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            C * ‖h‖ ^ 2 + C * ‖t - M.t₀‖ ^ (2 + M.δ)) ∧
    (∀ t : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p → ∀ z : Pt m, z ≠ 0 →
        c * ‖z‖ * angle z (slopeVec t) ^ 2 - C * ‖z‖ * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
          M.μ.1 z - inner ℝ p z)

/-- **Lemma `lem:good`**: for every sufficiently large integer `N` there are events `𝒢_N(S)`,
`S ≥ log N`, increasing in `S`, with `1_{𝒢_N(S)ᶜ} ≤ O₂(C/S)`, on which the properties (1)–(3) of the
lemma hold (`Paper.IsGood`).

Readings. `Monotone G` is on all real `S`, which is stronger than the paper's `S ≥ log N` and costs
nothing: an event below `log N` is unconstrained. The events depend on `N` and `S`, and on the model
through its law only, so they are chosen after `M` and before everything else of the paper. The
constants `c`, `C` and `N₀` come before `M`. `C` is the largest of the three constants of (1)–(3)
and of `O₂(C/S)`, since the paper's `C` may change from line to line. -/
def GoodStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N →
  ∃ G : ℝ → Set (Config m), Monotone G ∧
    (∀ S : ℝ, Real.log N ≤ S →
      CurvatureVariance.IsOs M.P 2 (C / S) ((G S)ᶜ.indicator fun _ => (1 : ℝ))) ∧
    ∀ S : ℝ, Real.log N ≤ S → ∀ ω ∈ G S, IsGood M C c N S ω

/-- The cone bound, equation `eq:cone`, at a vertex with vector `a` (the paper's `v − z` or `z − u`)
of length at least `C S²`:
`∠(a, (1, t)) ≤ C (S^{1/2} |a|^{−1/4} + |t − t₀|^{1+δ/2} log N)`. The angle is measured from
`(1, t)`; only the second term involves `t₀`. -/
def ConeBound {m : ℕ} (M : Model m) (C S : ℝ) (N : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (a : Pt m) : Prop :=
  C * S ^ 2 ≤ ‖a‖ →
    angle a (slopeVec t) ≤
      C * (S ^ ((1 : ℝ) / 2) * ‖a‖ ^ (-(1 : ℝ) / 4) + ‖t - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N)

/-- **Lemma `lem:cone`**, equation `eq:cone`, on one configuration: let `C_g, c_g` be the constants
of a good event. If `N` is large, then for `S ≥ log N`, for every `ω` with `IsGood M C_g c_g N S ω`,
all `u, v ∈ [−N², N²]^d ∩ ℤ^d` with `v − u = (ℓ, ℓt)`, `1 ≤ ℓ ≤ 3N` and `|t − t₀| ≤ 3N^{−1/9}`,
every self-avoiding path from `u` to `v` with passage time at most `T(u,v) + S²` satisfies the bound
at its vertices `z` with `|v − z| ≥ CS²`, and the same bound for `∠(z − u, (1,t))` at its vertices
with `|z − u| ≥ CS²`.

Readings. The paper's "on `𝒢_N(S)`" is `IsGood`, which the events of `GoodStatement` imply: the
paper's proof uses only the properties (1)–(3), so the statement is deterministic, and stronger.
The constant `C` and the threshold depend on `C_g, c_g`, which depend on the bounds only. The
constant of the proof's `|t_j' − t| ≤ Cθ_j` depends on a bound of `|t|`, so with `Bounds.T` general
`C` and the threshold depend on `T`. The paper's `ℓ` is an integer, since `v − u` is a lattice
vector and `ℓ ≥ 1`. -/
def ConeStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cg cg : ℝ, 0 < Cg → 0 < cg → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ S : ℝ, Real.log N ≤ S →
  ∀ ω : Config m, IsGood M Cg cg N S ω →
  ∀ (ℓ : ℕ) (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m),
    InBox ((N : ℝ) ^ 2) u → InBox ((N : ℝ) ^ 2) v →
    point v - point u = (ℓ : ℝ) • slopeVec t → 1 ≤ ℓ → (ℓ : ℝ) ≤ 3 * N →
    ‖t - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) →
    ∀ γ : (latticeGraph m).Walk u v, γ.IsPath →
      (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2 → ∀ z ∈ γ.support,
        ConeBound M C S N t (point v - point z) ∧ ConeBound M C S N t (point z - point u)

/-- **The chains of equation `eq:F` exist** (the sentence after equation `eq:F`): for integers
`M ≥ 1` and `n ≥ 64d`, and `u, v ∈ ℤ^d` with `v − u = (Mn, Mnt)`, there is a chain from `u` to `v`.

The encoding is the tuple of `Paper.IsAdmissibleTuple`, not the paper's chain of points of `ℤ^d`,
for this reason. A chain has `x_i·e₁ = u·e₁ + in`, so it is determined by the tuple `y_i` of its
transverse parts (`Paper.tuplePoint`), and `|x_i − x_{i−1} − n(1,t)|` is `|y_i − y_{i−1} − nt|`. The
minimum `F` of equation `eq:F` is `Paper.slabMin`, the infimum over the tuples in `[0, ∞]`, so it
needs no hypothesis on `n`; its value is a real number only if a tuple exists. That is this
statement, with `n ≥ 64d` as in the paper. A later statement on `F` has `n ≥ N^{1/2}`, which
contains `n ≥ 64d` for `N` large. The chain is that of the rounded points of `u + in(1,t)`;
`(64d)^{3/4}/16 ≥ √d` is what the bound needs.

The second clause is that of the same chain: its increments are within `√(d−1)` of `n(1,t)`. The
paper's sentence says only that chains exist, and the proof there is "the rounded points". Lemma
`lem:rowenergy` needs this clause: "The upper bound on `F` uses the chain of the rounded points"
(the proof of Lemma `lem:rowenergy`). An arbitrary chain has increments up to `n^{3/4+δ/100}/16`,
which is too long for this upper bound. -/
def ChainsExistStatement (m : ℕ) : Prop :=
  ∀ M : Model m, M.Standing → ∀ (Ms n : ℕ), 1 ≤ Ms → 64 * (m + 1) ≤ n →
  ∀ (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m),
    point v - point u = ((Ms * n : ℕ) : ℝ) • slopeVec t →
    ∃ y : Fin (Ms + 1) → Fin m → ℤ, IsAdmissibleTuple M n Ms t u v y ∧
      ∀ i : Fin Ms, ‖transversePoint (y i.succ - y i.castSucc) - (n : ℝ) • t‖ ≤ Real.sqrt m

/-- **Lemma `lem:slabs`**, on one configuration, with the chain of its proof:
let `C_g, c_g` be the constants of a good event. If `N` is large, then for `S ≥ log N`, every `ω`
with `IsGood M C_g c_g N S ω`, and all `u, v ∈ ℤ^d` with `v − u = (ℓ, ℓt)`, `1 ≤ ℓ ≤ 3N` and
`|t − t₀| ≤ 3N^{−1/9}`:

1. if `u, v ∈ [−N², N²]^d` and `ℓ ≥ CS²`, then `0 ≤ T_P(u,v) − T(u,v) ≤ CS²` for the slab
   `P = [u·e₁, v·e₁] × ℝ^{d−1}`;
2. if `ℓ = Mn` for integers `M ≥ 1` and `n ≥ N^{1/2}`, `|t − t₀| ≤ 2n^{δ/100−1/4}`,
   `S ≤ N^{δ/1000}`, and `u, v ∈ [−3(1+|t₀|)N, 3(1+|t₀|)N]^d`, then the first vertices `x_i` of
   every geodesic from `u` to `v` on the hyperplanes `{x·e₁ = u·e₁ + in}`, `0 < i < M`, form a chain
   from `u` to `v`, and `0 ≤ F − T(u,v) ≤ CMS²`.

The lemma states only the bound in (2), which is `Closing.slabsBounds_holds`; the chain is a step of
its proof.

Readings. As in `ConeStatement`, the paper's "on `𝒢_N(S)`" is `IsGood`, and the statement is
deterministic. The paper's `M` is `Ms`, since `M` is the model. "Form a chain" is the two clauses of
the conjunct: the first coordinates, so that `x_i` is `tuplePoint u n y i` for `y_i` the transverse
parts, and `IsAdmissibleTuple` (`ChainsExistStatement` says why tuples); `Paper.hitPoint` is `u` at
`i = 0`, `v` at `i = M`, and the first vertex on the hyperplane otherwise, and the first clause says
that this vertex exists. The increments are bounded by `n^{3/4+δ/100}/16`, as in the paper. The
proof of (1) takes the aperture `1/(8d^{1/2})`, using `|t₀| ≤ (d−1)^{1/2}`. With `Bounds.T` general
the aperture depends on `T`, so `C` and the threshold depend on `T`. -/
def SlabsStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cg cg : ℝ, 0 < Cg → 0 < cg → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ S : ℝ, Real.log N ≤ S →
  ∀ ω : Config m, IsGood M Cg cg N S ω →
  ∀ (ℓ : ℕ) (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m),
    point v - point u = (ℓ : ℝ) • slopeVec t → 1 ≤ ℓ → (ℓ : ℝ) ≤ 3 * N →
    ‖t - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) →
    -- (1)
    (InBox ((N : ℝ) ^ 2) u → InBox ((N : ℝ) ^ 2) v → C * S ^ 2 ≤ ℓ →
      (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v ∧
        slabTime ω u.1 v.1 u v ≤ (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C * S ^ 2)) ∧
    -- (2)
    (∀ Ms n : ℕ, ℓ = Ms * n → 1 ≤ Ms → Real.sqrt N ≤ n →
      ‖t - M.t₀‖ ≤ 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) → S ≤ (N : ℝ) ^ (M.δ / 1000) →
      InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) u → InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) v →
      (∀ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ →
        (∀ i : ℕ, i ≤ Ms → (hitPoint γ n Ms i).1 = u.1 + (i : ℤ) * n) ∧
          IsAdmissibleTuple M n Ms t u v fun i => (hitPoint γ n Ms i).2) ∧
      (passageTime ω u v : ℝ≥0∞) ≤ slabMin M ω n Ms t u v ∧
        slabMin M ω n Ms t u v ≤ (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C * Ms * S ^ 2))

end CurvatureVariance.Paper.Contracts
