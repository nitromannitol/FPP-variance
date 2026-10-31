/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The paper's internal objects: transverse cubes, rows, fine cubes, blocks and resampling

Sections `sec:cubes` and `sec:gain` of the lattice paper:

* `Paper.transverseCube`, `Paper.IsCubePair`, `Paper.thicken`: transverse cubes, pairs of them at
  distance `s` of side at most `b W_s` with slope `t`, whose centres differ from `(s, st)` by at
  most `2√d` (Section `sec:cubes`), and the thickening by `r` along `(1, t)`: as in the paper, all
  lattice points within `√d` of the points `u + τ(1, t)`. The paper's transverse cubes are nonempty;
  for an empty cube the statements are vacuous.
* `Paper.roundPoint`: the rounding map of the beginning of Section `sec:prelim`, for endpoints that
  are real points, and `Paper.halfOpenCube_subset_transverseCube`: the paper's half-open cube lies
  in the closed `Paper.transverseCube` with the same center and side.
* `Paper.rowIndex`, `Paper.rowCube`: the cubes `I_i(j)` of Section `sec:cubes` (the text before
  Lemma `lem:rowenergy`) and the index of the cube containing a point.
* `Paper.edgeMid`, `Paper.fineIndex`, `Paper.block`: fine-cube indices and blocks of a slab
  (the cells and blocks of Section `sec:gain`).
* `Paper.resample`, `Paper.esTerm`: resampling the weights of a set of edges and the Efron–Stein
  term `E(X − X^G)²`.
* `Paper.deviation`, `Paper.locRadius`, `Paper.locRadiusSlab`: the radius `R` of Lemma
  `lem:localization`, for `T` and for slab passage times; `Paper.slabRadius`, the radius
  `R_i(j,k)` for every pair, and `Paper.radiusArray`, its restriction to the retained pairs
  (`Paper.IsRetainedPair`, Section `sec:gain`); `Paper.tubeIndices`: the fine-cube indices
  within index distance `r` of the segment `[j, k]` (Section `sec:gain`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper

variable {m : ℕ}

/-! ## Transverse cubes (Section `sec:cubes`) -/

/-- The transverse cube in the hyperplane `{x₁ = p}` with centre `c ∈ ℝ^{d-1}` and side `a`: its
lattice points `(p, y)` with `|y_j − c_j| ≤ a/2` for every `j`. -/
def transverseCube (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) (a : ℝ) : Set (Vertex m) :=
  {x | x.1 = p ∧ ∀ j, |(x.2 j : ℝ) - c j| ≤ a / 2}

/-- A pair of transverse cubes `I ⊂ {x₁ = p}`, `I' ⊂ {x₁ = p + s}` at distance `s`, of side at most
`b W_s`, whose centres differ by `(s, s t)` up to the bounded error `2√d`; `t` is their slope
(Section `sec:cubes`). -/
def IsCubePair (M : Model m) (K : ℕ) (A : ℝ) (s : ℕ) (b : ℝ) (t : EuclideanSpace ℝ (Fin m))
    (I I' : Set (Vertex m)) : Prop :=
  ∃ (p : ℤ) (c c' : EuclideanSpace ℝ (Fin m)) (a a' : ℝ),
    I = transverseCube p c a ∧ I' = transverseCube (p + s) c' a' ∧
    0 ≤ a ∧ a ≤ b * W M K A s ∧ 0 ≤ a' ∧ a' ≤ b * W M K A s ∧
    ‖c' - c - (s : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1)

/-- `I` thickened by `r` along `(1, t)`: the lattice points within `√d` of
`{u + τ (1, t) : u ∈ I, |τ| ≤ r}` (Section `sec:cubes`; real endpoints are replaced by lattice
points at bounded distance). -/
def thicken (I : Set (Vertex m)) (t : EuclideanSpace ℝ (Fin m)) (r : ℝ) : Set (Vertex m) :=
  {x | ∃ u ∈ I, ∃ τ : ℝ, |τ| ≤ r ∧
    ‖point x - (point u + τ • slopeVec t)‖ ≤ Real.sqrt ((m : ℝ) + 1)}

/-- A vertex of a set lies in the set thickened by any `r ≥ 0`. -/
theorem mem_thicken_of_mem {I : Set (Vertex m)} {t : EuclideanSpace ℝ (Fin m)} {r : ℝ}
    (hr : 0 ≤ r) {u : Vertex m} (hu : u ∈ I) : u ∈ thicken I t r := by
  refine ⟨u, hu, 0, by simpa only [abs_zero] using hr, ?_⟩
  simp only [zero_smul, add_zero, sub_self, norm_zero]
  exact Real.sqrt_nonneg _

/-- **The paper's cube lies in the Lean cube**: the cube of side `σ` of Section `sec:cubes`, the
lattice points of `{p} × (z + [0, σ)^{d-1})`, lies in the closed `transverseCube` with the same
center, the center of `{p} × (z + [0, σ]^{d-1})`, and the same side. -/
theorem halfOpenCube_subset_transverseCube (p : ℤ) (z : EuclideanSpace ℝ (Fin m)) (σ : ℝ) :
    {x : Vertex m | x.1 = p ∧ ∀ j, z j ≤ (x.2 j : ℝ) ∧ (x.2 j : ℝ) < z j + σ} ⊆
      transverseCube p (WithLp.toLp 2 fun j => z j + σ / 2) σ := fun _ hx =>
  ⟨hx.1, fun j => abs_le.2 ⟨by linarith only [(hx.2 j).1], by linarith only [(hx.2 j).2]⟩⟩

/-! ## The rounding map (Section `sec:prelim`) -/

/-- **The rounding map** of the beginning of Section `sec:prelim`: "the point of `ℤ^d` with the
coordinates `⌈x·e_j − 1/2⌉`, a nearest point of `ℤ^d` to `x`", the paper's fixed map for a point of
`ℝ^d` used as an endpoint of a passage time. The statements of this library quantify over every
lattice point within `√d` of the real point (for instance `Paper.thicken`), and this map is an
instance of that, by `norm_point_roundPoint_sub_le`, so no statement needs it. -/
noncomputable def roundPoint (x : Pt m) : Vertex m :=
  (⌈x.fst - 1 / 2⌉, fun j => ⌈x.snd j - 1 / 2⌉)

/-- The rounding map, one coordinate: `|⌈a − 1/2⌉ − a| ≤ 1/2`. -/
theorem abs_ceil_sub_half_sub_le (a : ℝ) : |(⌈a - 1 / 2⌉ : ℝ) - a| ≤ 1 / 2 := by
  have h1 := Int.le_ceil (a - 1 / 2)
  have h2 := Int.ceil_lt_add_one (a - 1 / 2)
  exact abs_le.2 ⟨by linarith only [h1], by linarith only [h2]⟩

/-- The distance from a point of `ℝ^d` to its rounding is at most `√d / 2`. -/
theorem norm_point_roundPoint_sub_le (x : Pt m) :
    ‖point (roundPoint x) - x‖ ≤ Real.sqrt ((m : ℝ) + 1) / 2 := by
  set v := point (roundPoint x) - x with hv
  have h1 : |v.fst| ≤ 1 / 2 := abs_ceil_sub_half_sub_le x.fst
  have h2 : ‖v.snd‖ ^ 2 ≤ m / 4 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ k, ‖v.snd k‖ ^ 2 ≤ ∑ _k : Fin m, (1 / 2 : ℝ) ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _)
            (abs_ceil_sub_half_sub_le (x.snd k)) 2
      _ = m / 4 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  have h := WithLp.prod_norm_sq_eq_of_L2 v
  rw [Real.norm_eq_abs, sq_abs] at h
  have h3 : v.fst ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    have := pow_le_pow_left₀ (abs_nonneg v.fst) h1 2
    linarith only [this]
  have hsq : ‖v‖ ^ 2 ≤ ((m : ℝ) + 1) / 4 := by linarith only [h, h2, h3]
  rw [show Real.sqrt ((m : ℝ) + 1) / 2 = Real.sqrt (((m : ℝ) + 1) / 4) by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
  exact Real.le_sqrt_of_sq_le hsq

/-! ## The cubes `I_i(j)` of Section `sec:cubes` -/

/-- The index `j` of the cube `I_i(j)` containing the point `(is, y)`:
`y − ⌊ist⌋ ∈ w (j + [0,1)^{d-1})`, coordinatewise (Section `sec:cubes`). -/
noncomputable def rowIndex (s w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (y : Fin m → ℤ) :
    Fin m → ℤ :=
  fun k => ⌊((y k : ℝ) - ⌊(i : ℝ) * s * t k⌋) / w⌋

/-- The cube `I_i(j) = {is} × (⌊ist⌋ + w (j + [0,1)^{d-1})) ∩ ℤ^d` of Section `sec:cubes`. -/
def rowCube (s w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j : Fin m → ℤ) : Set (Vertex m) :=
  {x | x.1 = i * s ∧ rowIndex s w t i x.2 = j}

/-! ## Fine cubes and blocks (Section `sec:gain`) -/

/-- The midpoint of an edge, as a point of `ℝ^d`. -/
noncomputable def edgeMid : Sym2 (Vertex m) → Pt m :=
  Sym2.lift ⟨fun a b => (1 / 2 : ℝ) • (point a + point b), fun a b => by simp only [add_comm]⟩

/-- The fine-cube index of a point `(x₁, z)`: the `j` with `z − x₁ t ∈ w (j + [0,1)^{d-1})`. -/
noncomputable def fineIndex (w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (x : Pt m) : Fin m → ℤ :=
  fun k => ⌊(x.ofLp.2 k - x.ofLp.1 * t k) / w⌋

/-- The block of slab `i` with index `g ∈ ℤ^{d-1}` and offset `o` (Section `sec:gain`): the
union of the fine cubes with indices in `L g + o + {0, …, L−1}^{d-1}`. The blocks of a slab, over
`g ∈ ℤ^{d-1}`, partition its edges. -/
def block (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (o g : Fin m → ℤ) :
    Set (Sym2 (Vertex m)) :=
  {e | e ∈ slabEdges (((i : ℤ) - 1) * n) ((i : ℤ) * n) ∧
    ∀ k, (L : ℤ) * g k + o k ≤ fineIndex w t (edgeMid e) k ∧
      fineIndex w t (edgeMid e) k < (L : ℤ) * g k + o k + L}

/-! ## Resampling and Efron–Stein terms -/

open Classical in
/-- The configuration `ω` with the weights of the edges in `G` replaced by those of `ω'`. -/
noncomputable def resample (G : Set (Sym2 (Vertex m))) (ω ω' : Config m) : Config m :=
  fun e => if e.1 ∈ G then ω' e else ω e

/-- The Efron–Stein term `E(X − X^G)²`, `X^G` being `X` after the weights of `G` are resampled
independently from their law (Section `sec:gain`), as
`∫∫ (X(ω) − X(ω^{G,ω'}))² dP(ω') dP(ω)`. -/
noncomputable def esTerm (P : Measure (Config m)) (X : Config m → ℝ) (G : Set (Sym2 (Vertex m))) :
    ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal ((X ω - X (resample G ω ω')) ^ 2) ∂P ∂P

/-! ## The localization radius (Lemma `lem:localization`) -/

/-- The largest distance from a vertex of a path to the segment `[u, v]`, over `u ∈ I`, `v ∈ I'`
and the paths `γ` from `u` to `v` with `geo γ`. -/
noncomputable def deviation (geo : ∀ {u v : Vertex m}, (latticeGraph m).Walk u v → Prop)
    (I I' : Set (Vertex m)) : ℝ≥0∞ :=
  ⨆ (u : Vertex m) (_ : u ∈ I) (v : Vertex m) (_ : v ∈ I') (γ : (latticeGraph m).Walk u v)
    (_ : geo γ) (x : Vertex m) (_ : x ∈ γ.support),
    ENNReal.ofReal (Metric.infDist (point x) (segment ℝ (point u) (point v)))

/-- The radius `R` of Lemma `lem:localization` for `T`: one plus `W_ℓ⁻¹` times the largest
distance from a point of a geodesic between `I` and `I'` to the segment joining its endpoints. -/
noncomputable def locRadius (ω : Config m) (I I' : Set (Vertex m)) (Wl : ℝ) : ℝ≥0∞ :=
  1 + deviation (fun γ => IsGeodesic ω γ) I I' / ENNReal.ofReal Wl

/-- The radius `R` of Lemma `lem:localization` for the slab passage time `D_{p,q}`, the paths
being geodesics for `D_{p,q}` (within the slab). -/
noncomputable def locRadiusSlab (ω : Config m) (p q : ℤ) (I I' : Set (Vertex m)) (Wl : ℝ) :
    ℝ≥0∞ :=
  1 + deviation (fun γ => IsSlabGeodesic ω p q γ) I I' / ENNReal.ofReal Wl

/-- The radius `R_i(j,k) = C(1 + R)` of Section `sec:gain` (the paper writes `C R`; since `R ≥ 1`,
the two differ only in the constant), for the slab passage time `D_i` of slab `i` (the slab
`[(i−1)n, in]`) on `I_{i−1}(j) × I_i(k)`, with the cubes `I_i(j)` of Section `sec:cubes` at `s = n`;
`R` is the radius of Lemma `lem:localization`. The constant `C = Cd` dominates
the operator norm of the shear `(x₁, z) ↦ z − t x₁` on the slopes considered and the bounded
midpoint and face errors (`Contracts.TubeStatement`), so it depends on `t₀`. -/
noncomputable def slabRadius (M : Model m) (K : ℕ) (A : ℝ) (Cd : ℝ) (ω : Config m) (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (j k : Fin m → ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal Cd * (1 + locRadiusSlab ω (((i : ℤ) - 1) * n) ((i : ℤ) * n)
    (rowCube n (wInt M K A n) t ((i : ℤ) - 1) j) (rowCube n (wInt M K A n) t i k) (W M K A n))

/-- The pairs of cube indices retained in Section `sec:gain`: `8w|k − j| ≤ n^{3/4+δ/100}`. -/
def IsRetainedPair (M : Model m) (n w : ℕ) (j k : Fin m → ℤ) : Prop :=
  8 * (w : ℝ) * ‖transversePoint (k - j)‖ ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)

open Classical in
/-- The radius array `R_i(j,k)` of Section `sec:gain` (the text before Lemma `lem:blocks`): the
radius `slabRadius` on the retained pairs (`w = ⌈W_n⌉`) and `0` outside them, as in the paper. -/
noncomputable def radiusArray (M : Model m) (K : ℕ) (A : ℝ) (Cd : ℝ) (ω : Config m) (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (j k : Fin m → ℤ) : ℝ≥0∞ :=
  if IsRetainedPair M n (wInt M K A n) j k then slabRadius M K A Cd ω n t i j k else 0

/-- The fine-cube indices within index distance `r` of the segment `[j, k] ⊂ ℝ^{d-1}` (Section
`sec:gain`). -/
def tubeIndices (j k : Fin m → ℤ) (r : ℝ≥0∞) : Set (Fin m → ℤ) :=
  {j' | ENNReal.ofReal (Metric.infDist (transversePoint j')
    (segment ℝ (transversePoint j) (transversePoint k))) ≤ r}

end CurvatureVariance.Paper
