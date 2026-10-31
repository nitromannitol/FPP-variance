/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Scales

/-!
# Coordinates, slabs, slab passage times, transverse cubes, 1-optimal curves

* Coordinates `x = (t, y)` of `ℝ^d = ℝ × ℝ^m` (the first paragraph of the proof of Lemma
  `lem:localization`).
* The passage time over curves in a closed set (equation `eq:slabtime`).
* Slabs: the closed region between two parallel hyperplanes at distance `s`, written as the
  image of the standard slab `[0, s] × ℝ^m` under a rigid motion; the slab density (the upper
  bound `b` within distance one of the faces, `ρ` elsewhere) and the slab passage time `D`;
  the slope (Section `sec:prelim`).
* Pairs of transverse cubes (Section `sec:exponential`), in the parallel form that every use
  needs: two `m`-dimensional cubes in the two faces of a slab, with the same orientation.
* The cubes `I_i(j)` of equation `eq:cubes`, translated by `τ`.
* 1-optimal curves (the near-geodesics of Section `ssec:overview`) and their largest distance from
  a segment (equation `eq:localization` and the radii `R_i(j, k)` of Section `sec:gain`).
* Rectangular boxes (Lemma `lem:tree`).
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace IsotropicVariance.Paper

/-! ## Coordinates -/

namespace Pt

/-- The coordinate along `e₁`. -/
def lon {m : ℕ} (x : Pt m) : ℝ := (WithLp.ofLp x).1

/-- The transverse coordinates. -/
def tr {m : ℕ} (x : Pt m) : EuclideanSpace ℝ (Fin m) := (WithLp.ofLp x).2

/-- The point `(t, y)`. -/
def mk {m : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin m)) : Pt m := WithLp.toLp 2 (t, y)

/-- The coordinates `(x · e₁, x · e₂, …, x · e_d)` of a point. -/
noncomputable def coords {m : ℕ} (x : Pt m) : Fin (m + 1) → ℝ :=
  Fin.cons (lon x) fun k => tr x k

end Pt

/-! ## Passage times over curves in a set -/

/-- The passage time over the rectifiable curves from `u` to `v` that stay in `S`, for the
density `σ` (equation `eq:slabtime`): the restricted passage times of the paper. For
`S = univ` it is `passageTime`. -/
noncomputable def restrictedPassageTime {m : ℕ} (σ : Pt m → ℝ) (S : Set (Pt m)) (u v : Pt m) :
    ℝ :=
  (⨅ (γ : RectifiableCurve (Pt m)) (_ : γ.toFun 0 = u) (_ : γ.toFun 1 = v)
      (_ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S),
    γ.cost (fun x => ENNReal.ofReal (σ x))).toReal

/-- A curve from `u` to `v` in `S` is 1-optimal for `(σ, S)` if its cost is at most the passage
time plus one (a near-geodesic, Section `ssec:overview`); for `S = univ` this is 1-optimality for
`T`. The comparison is in `[0, ∞]`. -/
def IsOneOptimal {m : ℕ} (σ : Pt m → ℝ) (S : Set (Pt m)) (u v : Pt m)
    (γ : RectifiableCurve (Pt m)) : Prop :=
  γ.toFun 0 = u ∧ γ.toFun 1 = v ∧ (∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S) ∧
    γ.cost (fun x => ENNReal.ofReal (σ x)) ≤
      ENNReal.ofReal (restrictedPassageTime σ S u v + 1)

/-- The largest distance from the segment `[p, q]` of the points of the 1-optimal curves for
`(σ, S)` between points of `I` and points of `I'` (equation `eq:localization` and the radii
`R_i(j, k)` of Section `sec:gain`). -/
noncomputable def maxDeviation {m : ℕ} (σ : Pt m → ℝ) (S I I' : Set (Pt m)) (p q : Pt m) : ℝ :=
  ⨆ (u : I) (v : I') (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ})
    (t : Icc (0 : ℝ) 1), infDist (γ.1.toFun t) (segment ℝ p q)

/-! ## Slabs -/

/-- A slab of width `width`: the image of `[0, width] × ℝ^m` under a rigid motion
(Section `ssec:overview`). -/
structure Slab (m : ℕ) where
  /-- The rigid motion placing the standard slab. -/
  motion : Pt m ≃ᵃⁱ[ℝ] Pt m
  /-- The width. -/
  width : ℝ

namespace Slab

variable {m : ℕ} (sl : Slab m)

/-- The closed slab. -/
def set : Set (Pt m) := sl.motion '' {x | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ sl.width}

/-- Its two faces. -/
def faces : Set (Pt m) := sl.motion '' {x | Pt.lon x = 0 ∨ Pt.lon x = sl.width}

/-- The first face. -/
def face₀ : Set (Pt m) := sl.motion '' {x | Pt.lon x = 0}

/-- The second face. -/
def face₁ : Set (Pt m) := sl.motion '' {x | Pt.lon x = sl.width}

/-- The slab density: the fixed upper bound `b` within distance one of the faces, `σ` elsewhere
(equation `eq:slabtime`). -/
noncomputable def density (b : ℝ) (σ : Pt m → ℝ) (x : Pt m) : ℝ :=
  if infDist x sl.faces ≤ 1 then b else σ x

/-- The slab passage time `D(u, v)` (equation `eq:slabtime`). -/
noncomputable def passTime (b : ℝ) (σ : Pt m → ℝ) (u v : Pt m) : ℝ :=
  restrictedPassageTime (sl.density b σ) sl.set u v

/-- The slope of two points on the two faces: `(|y − x|² − s²)^{1/2}/s` (Section
`sec:prelim`). -/
noncomputable def slope (x y : Pt m) : ℝ :=
  Real.sqrt (dist x y ^ 2 - sl.width ^ 2) / sl.width

end Slab

/-- The slab `[a, a + s] × ℝ^m`. -/
noncomputable def e1Slab {m : ℕ} (a s : ℝ) : Slab m :=
  ⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) (a • e₁), s⟩

/-! ## Transverse cubes -/

/-- A pair of transverse cubes at distance `dist` (Section `sec:exponential`): after the rigid
motion `motion`, the cube of side `side₁` centered at `0` in `{t = 0}` and the cube of side
`side₂` centered at `(dist, offset)` in `{t = dist}`, with the same orientation. The slope of
the centers is `‖offset‖ / dist`. -/
structure CubePair (m : ℕ) where
  /-- The rigid motion placing the standard pair. -/
  motion : Pt m ≃ᵃⁱ[ℝ] Pt m
  /-- The distance between the two hyperplanes. -/
  dist : ℝ
  /-- The side of the first cube. -/
  side₁ : ℝ
  /-- The side of the second cube. -/
  side₂ : ℝ
  /-- The transverse position of the center of the second cube. -/
  offset : EuclideanSpace ℝ (Fin m)

namespace CubePair

variable {m : ℕ} (p : CubePair m)

/-- The first cube `I`. -/
def first : Set (Pt m) :=
  p.motion '' {x | Pt.lon x = 0 ∧ ∀ k, |Pt.tr x k| ≤ p.side₁ / 2}

/-- The second cube `I'`. -/
def second : Set (Pt m) :=
  p.motion '' {x | Pt.lon x = p.dist ∧ ∀ k, |Pt.tr x k - p.offset k| ≤ p.side₂ / 2}

/-- The center of `I`. -/
def center₁ : Pt m := p.motion 0

/-- The center of `I'`. -/
def center₂ : Pt m := p.motion (Pt.mk p.dist p.offset)

/-- The slab between the two hyperplanes. -/
def slab : Slab m := ⟨p.motion, p.dist⟩

/-- The slope of the centers. -/
noncomputable def centerSlope : ℝ := ‖p.offset‖ / p.dist

/-- A pair of transverse cubes at distance `s` with sides at most `4W` whose centers have slope
at most `κ`. -/
def IsAdmissible (s W κ : ℝ) : Prop :=
  p.dist = s ∧ 0 ≤ p.side₁ ∧ p.side₁ ≤ 4 * W ∧ 0 ≤ p.side₂ ∧ p.side₂ ≤ 4 * W ∧
    p.centerSlope ≤ κ

end CubePair

/-- The cube `I_i(j) = {is} × W(j + [0,1]^m)` of equation `eq:cubes`, translated by `τ`. -/
def gridCube {m : ℕ} (s W : ℝ) (τ : Pt m) (i : ℕ) (j : Fin m → ℤ) : Set (Pt m) :=
  {x | Pt.lon (x - τ) = i * s ∧ ∀ k, W * j k ≤ Pt.tr (x - τ) k ∧ Pt.tr (x - τ) k ≤ W * (j k + 1)}

/-- The center of `I_i(j)`. -/
noncomputable def gridCubeCenter {m : ℕ} (s W : ℝ) (τ : Pt m) (i : ℕ) (j : Fin m → ℤ) : Pt m :=
  τ + Pt.mk (i * s) (WithLp.toLp 2 fun k => W * ((j k : ℝ) + 1 / 2))

/-! ## Cubes of `ℝ^d` -/

/-- The cube of half-side `r` centered at `z` (Lemma `lem:slab` and its proof). -/
noncomputable def cubeAround {m : ℕ} (z : Pt m) (r : ℝ) : Set (Pt m) :=
  {x | ∀ k, |Pt.coords (x - z) k| ≤ r}

/-! ## Rectangular boxes -/

/-- `B` is a rectangular box centered at `c`: the image under a rigid motion of a product of
centered intervals with nonnegative half-widths, with the motion sending `0` to `c`
(the proof of Lemma `lem:tree`; any orientation; zero widths allowed, as for
the tilted transverse cubes of the profile proof). -/
def IsRectBox {m : ℕ} (B : Set (Pt m)) (c : Pt m) : Prop :=
  ∃ (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (r₀ : ℝ) (r : Fin m → ℝ), 0 ≤ r₀ ∧ (∀ k, 0 ≤ r k) ∧ g 0 = c ∧
    B = g '' {x | |Pt.lon x| ≤ r₀ ∧ ∀ k, |Pt.tr x k| ≤ r k}

end IsotropicVariance.Paper
