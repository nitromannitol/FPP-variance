/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The paper's internal objects: slabs, slab passage times and the slab minimum

Section `sec:prelim` of the lattice paper:

* `Paper.slabEdges p q`: the edges given to the slab `[p, q] × ℝ^{d-1}`: longitudinal edges
  `{x, x + e₁}` with `p ≤ x₁ < q`, transverse edges with `p < x₁ < q`.
* `Paper.restrictedTime ω E u v`: the infimum of the passage times of walks from `u` to `v` with all
  edges in `E` (`∞` if there is none); `Paper.slabTime ω p q u v = D_{p,q}(u, v)`.
* `Paper.IsGeodesic`, `Paper.IsSlabGeodesic`: simple paths attaining `T`, resp. `D_{p,q}` (the
  beginning of Section `sec:prelim`; Lemma `lem:localization`).
* `Paper.IsAdmissibleTuple`, `Paper.slabMin`: the chains and the minimum `F` of equation `eq:F`.
* `Paper.hitPoint`: the first vertex of a path in the hyperplane `{x₁ = u₁ + in}`, preceded by `u`
  and followed by `v` (Lemma `lem:slabs` (2)).
* `Paper.IsSubgradient`: `P` is a subgradient of `μ` at `x`, the paper's subgradient (the
  text before Lemma `lem:support`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper

variable {m : ℕ}

/-! ## Slabs -/

/-- The edges of the slab `[p, q] × ℝ^{d-1}` (Section `sec:prelim`): the longitudinal edges
`{x, x + e₁}` with `p ≤ x₁ < q` and the transverse edges `{x, x + e_j}`, `2 ≤ j ≤ d`, with
`p < x₁ < q`; the transverse edges in the two faces are omitted. -/
def slabEdges (p q : ℤ) : Set (Sym2 (Vertex m)) :=
  {e | ∃ x : Vertex m, (e = s(x, x + (1, 0)) ∧ p ≤ x.1 ∧ x.1 < q) ∨
    (∃ j : Fin m, e = s(x, x + (0, Pi.single j 1)) ∧ p < x.1 ∧ x.1 < q)}

/-- The passage time restricted to the edge set `E`: the infimum of the costs of the walks from `u`
to `v` with all edges in `E`, and `∞` if there is none. -/
noncomputable def restrictedTime (ω : Config m) (E : Set (Sym2 (Vertex m))) (u v : Vertex m) :
    ℝ≥0∞ :=
  ⨅ (γ : (latticeGraph m).Walk u v) (_ : ∀ e ∈ γ.edges, e ∈ E), (walkCost ω γ : ℝ≥0∞)

/-- The slab passage time `D_{p,q}(u, v)` (Section `sec:prelim`). -/
noncomputable def slabTime (ω : Config m) (p q : ℤ) (u v : Vertex m) : ℝ≥0∞ :=
  restrictedTime ω (slabEdges p q) u v

/-- The slab passage time as a real number (finite for two vertices of the slab). -/
noncomputable def slabTimeReal (ω : Config m) (p q : ℤ) (u v : Vertex m) : ℝ :=
  (slabTime ω p q u v).toReal

/-- A geodesic from `u` to `v`: a simple path whose passage time is `T(u, v)` (the beginning of
Section `sec:prelim`). -/
def IsGeodesic (ω : Config m) {u v : Vertex m} (γ : (latticeGraph m).Walk u v) : Prop :=
  γ.IsPath ∧ walkCost ω γ = passageTime ω u v

/-- A geodesic for the slab passage time `D_{p,q}`: a simple path in the slab whose passage time is
`D_{p,q}(u, v)` (Section `sec:prelim`, Lemma `lem:localization`). -/
def IsSlabGeodesic (ω : Config m) (p q : ℤ) {u v : Vertex m} (γ : (latticeGraph m).Walk u v) :
    Prop :=
  γ.IsPath ∧ (∀ e ∈ γ.edges, e ∈ slabEdges p q) ∧ (walkCost ω γ : ℝ≥0∞) = slabTime ω p q u v

/-! ## The slab minimum `F` of equation `eq:F` -/

/-- The constraint of equation `eq:F` on the transverse increments:
`|y_i − y_{i−1} − n t| ≤ n^{3/4+δ/100}/16`. -/
def IsAdmissibleTuple (M : Model m) (n K : ℕ) (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m)
    (y : Fin (K + 1) → Fin m → ℤ) : Prop :=
  y 0 = u.2 ∧ y (Fin.last K) = v.2 ∧
    ∀ i : Fin K, ‖transversePoint (y i.succ - y i.castSucc) - (n : ℝ) • t‖ ≤
      (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16

/-- The vertex `(u₁ + i n, y_i)` on the `i`-th hyperplane of the tuple. -/
def tuplePoint (u : Vertex m) (n : ℕ) {K : ℕ} (y : Fin (K + 1) → Fin m → ℤ) (i : Fin (K + 1)) :
    Vertex m :=
  (u.1 + (i : ℤ) * n, y i)

/-- The cost `∑ᵢ D_{u₁+(i−1)n, u₁+in}((u₁+(i−1)n, y_{i−1}), (u₁+in, y_i))` of a tuple. -/
noncomputable def tupleCost (ω : Config m) (u : Vertex m) (n : ℕ) {K : ℕ}
    (y : Fin (K + 1) → Fin m → ℤ) : ℝ≥0∞ :=
  ∑ i : Fin K, slabTime ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
    (tuplePoint u n y i.castSucc) (tuplePoint u n y i.succ)

/-- The minimum `F` of equation `eq:F` over `K` slabs of width `n` from `u` to `v`
(meant for `v − u = (Kn, Knt)`): the infimum of `tupleCost` over admissible tuples. -/
noncomputable def slabMin (M : Model m) (ω : Config m) (n K : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (u v : Vertex m) : ℝ≥0∞ :=
  ⨅ (y : Fin (K + 1) → Fin m → ℤ) (_ : IsAdmissibleTuple M n K t u v y), tupleCost ω u n y

/-- A minimizing tuple for `F`. -/
def IsMinTuple (M : Model m) (ω : Config m) (n K : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (u v : Vertex m) (y : Fin (K + 1) → Fin m → ℤ) : Prop :=
  IsAdmissibleTuple M n K t u v y ∧ tupleCost ω u n y = slabMin M ω n K t u v

/-! ## Hitting points (Lemma `lem:slabs` (2)) -/

/-- For `0 ≤ i ≤ K`: `u` for `i = 0`, `v` for `i = K`, and otherwise the first vertex of `γ` in the
hyperplane `{x₁ = u₁ + in}` (Lemma `lem:slabs` (2)); `v` if there is none. -/
def hitPoint {u v : Vertex m} (γ : (latticeGraph m).Walk u v) (n K : ℕ) (i : ℕ) : Vertex m :=
  if i = 0 then u else if i = K then v else
    (γ.support.find? fun z => decide (z.1 = u.1 + (i : ℤ) * n)).getD v

/-! ## Supporting hyperplanes (Section `sec:prelim`) -/

/-- `p` is a subgradient of the norm `μ` at `x`: `p · x = μ(x)` and `μ(z) ≥ p · z` for all `z`. -/
def IsSubgradient (μ : PtNorm m) (x p : Pt m) : Prop :=
  inner ℝ p x = μ.1 x ∧ ∀ z, inner ℝ p z ≤ μ.1 z

end CurvatureVariance.Paper
