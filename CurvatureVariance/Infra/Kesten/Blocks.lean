/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Lattice.Edge
public import CurvatureVariance.Infra.Percolation.Lattice
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Blocks of `ℤ^d` for the renormalization behind Kesten's estimate

The geometry of the block argument for Kesten's estimate: `ℤ^d`, `d = m + 1`, is cut into the
blocks `B(z) = Lz + [0, L)^d`, `z ∈ ℤ^d`.

* The `ℓ^∞` norm `latticeSupNorm x = max (|s|, maxⱼ |yⱼ|)` of `x = (s, y)` (the body of the
  definition `CurvatureVariance.supNorm`): the triangle inequality and the bound along walks
  (`latticeSupNorm_sub_le_length`).
* `block L x`, the index `z` of the block containing `x` (`x ∈ B(z)`); the blocks of adjacent
  vertices are equal or adjacent (`block_eq_or_adj`), and vertices at `ℓ^∞` distance at most `L`
  have blocks at distance at most `1` (`latticeSupNorm_block_sub_le_one`).
* `blockFinset L z = B(z)`, with at most `L^d` vertices; `cubeFinset z r`, the cube of radius `r`,
  with at most `(2r+1)^d` vertices.
* `blockEdges L z`, the edges with an endpoint in the tripled block `⋃_{‖w‖_∞ ≤ 1} B(z + w)`;
  blocks at `ℓ^∞` distance at least `4` have disjoint edge sets (`disjoint_blockEdges`).
-/

@[expose] public section

open Finset
open CurvatureVariance.Infra.Percolation (latticeSupNorm latticeSupNorm_zero)

namespace CurvatureVariance.Infra.Kesten

variable {m : ℕ}

/-! ### The `ℓ^∞` norm -/

/-- `‖x‖_∞ ≤ r` iff every coordinate has absolute value at most `r`. -/
theorem latticeSupNorm_le_iff {x : Vertex m} {r : ℕ} :
    latticeSupNorm x ≤ r ↔ x.1.natAbs ≤ r ∧ ∀ j, (x.2 j).natAbs ≤ r := by
  simp [latticeSupNorm, Finset.sup_le_iff]

/-- The longitudinal coordinate is bounded by the `ℓ^∞` norm. -/
theorem natAbs_fst_le_latticeSupNorm (x : Vertex m) : x.1.natAbs ≤ latticeSupNorm x :=
  le_max_left _ _

/-- Each transverse coordinate is bounded by the `ℓ^∞` norm. -/
theorem natAbs_snd_le_latticeSupNorm (x : Vertex m) (j : Fin m) :
    (x.2 j).natAbs ≤ latticeSupNorm x :=
  (Finset.le_sup (f := fun j => (x.2 j).natAbs) (Finset.mem_univ j)).trans (le_max_right _ _)

/-- The triangle inequality for the `ℓ^∞` norm. -/
theorem latticeSupNorm_add_le (x y : Vertex m) :
    latticeSupNorm (x + y) ≤ latticeSupNorm x + latticeSupNorm y := by
  rw [latticeSupNorm_le_iff]
  refine ⟨(Int.natAbs_add_le _ _).trans
    (add_le_add (natAbs_fst_le_latticeSupNorm x) (natAbs_fst_le_latticeSupNorm y)), fun j => ?_⟩
  exact (Int.natAbs_add_le _ _).trans
    (add_le_add (natAbs_snd_le_latticeSupNorm x j) (natAbs_snd_le_latticeSupNorm y j))

/-- The `ℓ^∞` norm is symmetric. -/
@[simp] theorem latticeSupNorm_neg (x : Vertex m) : latticeSupNorm (-x) = latticeSupNorm x := by
  simp [latticeSupNorm]

/-- The `ℓ^∞` distance is symmetric. -/
theorem latticeSupNorm_sub_comm (x y : Vertex m) :
    latticeSupNorm (x - y) = latticeSupNorm (y - x) := by
  rw [← neg_sub, latticeSupNorm_neg]

/-- The triangle inequality for the `ℓ^∞` distance. -/
theorem latticeSupNorm_sub_le (x y z : Vertex m) :
    latticeSupNorm (x - z) ≤ latticeSupNorm (x - y) + latticeSupNorm (y - z) := by
  have h := latticeSupNorm_add_le (x - y) (y - z)
  rwa [sub_add_sub_cancel] at h

/-! ### Adjacency -/

/-- The unit vectors of the lattice graph: `(1, 0)` and `(0, eⱼ)`. -/
def IsUnitStep (v : Vertex m) : Prop :=
  v = (1, 0) ∨ ∃ j : Fin m, v = (0, Pi.single j 1)

/-- Adjacency in `ℤ^d`: the endpoints differ by a unit vector `(1, 0)` or `(0, eⱼ)`, in one of
the two orders. -/
theorem latticeGraph_adj_iff_isUnitStep {x y : Vertex m} :
    (latticeGraph m).Adj x y ↔ x ≠ y ∧ (IsUnitStep (y - x) ∨ IsUnitStep (x - y)) := by
  simp only [latticeGraph, SimpleGraph.fromRel_adj, IsUnitStep, sub_eq_iff_eq_add']

/-- Unit vectors have `ℓ^∞` norm at most one. -/
theorem latticeSupNorm_le_one_of_isUnitStep {v : Vertex m} (hv : IsUnitStep v) :
    latticeSupNorm v ≤ 1 := by
  rw [latticeSupNorm_le_iff]
  rcases hv with rfl | ⟨j, rfl⟩
  · simp
  · refine ⟨by simp, fun k => ?_⟩
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]

/-- Adjacent vertices are at `ℓ^∞` distance at most one. -/
theorem latticeSupNorm_sub_le_one_of_adj {x y : Vertex m} (h : (latticeGraph m).Adj x y) :
    latticeSupNorm (y - x) ≤ 1 := by
  rcases (latticeGraph_adj_iff_isUnitStep.1 h).2 with hv | hv
  · exact latticeSupNorm_le_one_of_isUnitStep hv
  · rw [latticeSupNorm_sub_comm]; exact latticeSupNorm_le_one_of_isUnitStep hv

/-- Along a walk, the `ℓ^∞` distance from the start grows by at most one per step. -/
theorem latticeSupNorm_sub_le_length {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    latticeSupNorm (v - u) ≤ p.length := by
  induction p with
  | nil => simp [latticeSupNorm_zero]
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    have := latticeSupNorm_sub_le c b a
    have := latticeSupNorm_sub_le_one_of_adj h
    omega

/-! ### Blocks -/

/-- Floor division by `L` moves at most one step when the dividend moves by at most `L`. -/
theorem natAbs_ediv_sub_ediv_le_one {L a b : ℤ} (hL : 0 < L) (h : (b - a).natAbs ≤ L) :
    (b / L - a / L).natAbs ≤ 1 := by
  have h1 := Int.ediv_mul_le a hL.ne'
  have h2 := Int.lt_ediv_add_one_mul_self a hL
  have h3 := Int.ediv_mul_le b hL.ne'
  have h4 := Int.lt_ediv_add_one_mul_self b hL
  have hab : |b - a| ≤ L := by rw [Int.abs_eq_natAbs]; exact_mod_cast h
  rw [abs_le] at hab
  have hu : b / L ≤ a / L + 1 := by
    by_contra hc
    have : (a / L + 2) * L ≤ b / L * L := by
      exact Int.mul_le_mul_of_nonneg_right (by omega) hL.le
    nlinarith
  have hl : a / L ≤ b / L + 1 := by
    by_contra hc
    have : (b / L + 2) * L ≤ a / L * L := by
      exact Int.mul_le_mul_of_nonneg_right (by omega) hL.le
    nlinarith
  omega

/-- The index `z` of the block `B(z) = Lz + [0, L)^d` containing `x` (floor division). -/
def block (L : ℕ) (x : Vertex m) : Vertex m :=
  (x.1 / (L : ℤ), fun j => x.2 j / (L : ℤ))

/-- Vertices at `ℓ^∞` distance at most `L` lie in blocks at `ℓ^∞` distance at most `1`. -/
theorem latticeSupNorm_block_sub_le_one {L : ℕ} (hL : 0 < L) {x y : Vertex m}
    (h : latticeSupNorm (y - x) ≤ L) : latticeSupNorm (block L y - block L x) ≤ 1 := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  rw [latticeSupNorm_le_iff] at h ⊢
  refine ⟨natAbs_ediv_sub_ediv_le_one hL' (by exact_mod_cast h.1), fun j => ?_⟩
  exact natAbs_ediv_sub_ediv_le_one hL' (by exact_mod_cast h.2 j)

private theorem ediv_add_one_cases {L : ℤ} (hL : 0 < L) (a : ℤ) :
    (a + 1) / L = a / L ∨ (a + 1) / L = a / L + 1 := by
  have h := natAbs_ediv_sub_ediv_le_one (a := a) (b := a + 1) hL (by simp; omega)
  have h1 := Int.ediv_le_ediv hL (show a ≤ a + 1 by omega)
  omega

private theorem block_add_unitStep {L : ℕ} (hL : 0 < L) (x v : Vertex m) (hv : IsUnitStep v) :
    block L (x + v) = block L x ∨ block L (x + v) = block L x + v := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  rcases hv with rfl | ⟨j, rfl⟩
  · rcases ediv_add_one_cases hL' x.1 with h | h
    · left; ext <;> simp [block, h]
    · right; ext <;> simp [block, h]
  · rcases ediv_add_one_cases hL' (x.2 j) with h | h
    · left
      ext k
      · simp [block]
      · by_cases hk : k = j
        · subst hk; simp [block, h]
        · simp [block, Pi.single_apply, hk]
    · right
      ext k
      · simp [block]
      · by_cases hk : k = j
        · subst hk; simp [block, h]
        · simp [block, Pi.single_apply, hk]

private theorem isUnitStep_ne_zero {v : Vertex m} (hv : IsUnitStep v) : v ≠ 0 := by
  rcases hv with rfl | ⟨j, rfl⟩
  · simp [Prod.ext_iff]
  · intro h
    have := congrFun (congrArg Prod.snd h) j
    simp at this

private theorem adj_add_of_isUnitStep (x v : Vertex m) (hv : IsUnitStep v) :
    (latticeGraph m).Adj x (x + v) := by
  rw [latticeGraph_adj_iff_isUnitStep]
  refine ⟨fun h => isUnitStep_ne_zero hv ?_, Or.inl (by simpa using hv)⟩
  simpa using h.symm

/-- **The blocks of adjacent vertices are equal or adjacent.** -/
theorem block_eq_or_adj {L : ℕ} (hL : 0 < L) {x y : Vertex m} (h : (latticeGraph m).Adj x y) :
    block L x = block L y ∨ (latticeGraph m).Adj (block L x) (block L y) := by
  rcases (latticeGraph_adj_iff_isUnitStep.1 h).2 with hv | hv
  · have hy : y = x + (y - x) := by abel
    rcases block_add_unitStep hL x (y - x) hv with h' | h' <;> rw [← hy] at h'
    · exact Or.inl h'.symm
    · right; rw [h']; exact adj_add_of_isUnitStep _ _ hv
  · have hx : x = y + (x - y) := by abel
    rcases block_add_unitStep hL y (x - y) hv with h' | h' <;> rw [← hx] at h'
    · exact Or.inl h'
    · right; rw [h']; exact (adj_add_of_isUnitStep _ _ hv).symm

/-- The blocks of adjacent vertices are at `ℓ^∞` distance at most one. -/
theorem latticeSupNorm_block_sub_le_one_of_adj {L : ℕ} (hL : 0 < L) {x y : Vertex m}
    (h : (latticeGraph m).Adj x y) : latticeSupNorm (block L y - block L x) ≤ 1 := by
  rcases block_eq_or_adj hL h with h' | h'
  · simp [h', latticeSupNorm_zero]
  · exact latticeSupNorm_sub_le_one_of_adj h'

/-- The block `B(z) = Lz + [0, L)^d`, as a finset. -/
def blockFinset (L : ℕ) (z : Vertex m) : Finset (Vertex m) :=
  ((Finset.range L) ×ˢ Fintype.piFinset fun _ : Fin m => Finset.range L).image
    fun a => ((L : ℤ) * z.1 + a.1, fun j => (L : ℤ) * z.2 j + a.2 j)

private theorem mul_add_ediv {L : ℤ} (hL : 0 < L) (z : ℤ) {a : ℕ} (ha : a < L) :
    (L * z + a) / L = z := by
  rw [add_comm, Int.add_mul_ediv_left _ _ hL.ne', Int.ediv_eq_zero_of_lt (by positivity) ha,
    zero_add]

/-- `blockFinset L z` is the set of vertices in the block of index `z`. -/
theorem mem_blockFinset {L : ℕ} (hL : 0 < L) {x z : Vertex m} :
    x ∈ blockFinset L z ↔ block L x = z := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  constructor
  · intro hx
    simp only [blockFinset, Finset.mem_image, Finset.mem_product, Finset.mem_range,
      Fintype.mem_piFinset] at hx
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
    ext k
    · exact mul_add_ediv hL' z.1 (by exact_mod_cast ha)
    · exact mul_add_ediv hL' (z.2 k) (by exact_mod_cast hb k)
  · rintro rfl
    simp only [blockFinset, Finset.mem_image, Finset.mem_product, Finset.mem_range,
      Fintype.mem_piFinset]
    refine ⟨((x.1 % L).toNat, fun j => (x.2 j % L).toNat), ⟨?_, fun j => ?_⟩, ?_⟩
    · have := Int.emod_lt_of_pos x.1 hL'
      omega
    · have := Int.emod_lt_of_pos (x.2 j) hL'
      dsimp only
      omega
    · have h1 := Int.emod_nonneg x.1 hL'.ne'
      ext k
      · simp only [block]
        rw [Int.toNat_of_nonneg h1, Int.mul_ediv_add_emod]
      · simp only [block]
        rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hL'.ne'), Int.mul_ediv_add_emod]

/-- A block has at most `L^d` vertices. -/
theorem card_blockFinset_le (L : ℕ) (z : Vertex m) : (blockFinset L z).card ≤ L ^ (m + 1) := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Fintype.card_piFinset_const, Finset.card_range, pow_succ, mul_comm]

/-- The cube `z + [-r, r]^d`, as a finset. -/
def cubeFinset (z : Vertex m) (r : ℕ) : Finset (Vertex m) :=
  ((Finset.Icc (-(r : ℤ)) r) ×ˢ Fintype.piFinset fun _ : Fin m => Finset.Icc (-(r : ℤ)) r).image
    (· + z)

/-- The vertices within `ℓ^∞` distance `r` of `z` lie in the cube `cubeFinset z r`. -/
theorem mem_cubeFinset {z y : Vertex m} {r : ℕ} (h : latticeSupNorm (y - z) ≤ r) :
    y ∈ cubeFinset z r := by
  rw [latticeSupNorm_le_iff] at h
  simp only [cubeFinset, Finset.mem_image, Finset.mem_product, Finset.mem_Icc,
    Fintype.mem_piFinset]
  refine ⟨y - z, ⟨?_, fun j => ?_⟩, by abel⟩
  · have := h.1; simp only [Prod.fst_sub] at this; omega
  · have := h.2 j; simp only [Prod.snd_sub, Pi.sub_apply] at this ⊢; omega

/-- The cube of radius `r` has at most `(2r+1)^d` vertices. -/
theorem card_cubeFinset_le (z : Vertex m) (r : ℕ) :
    (cubeFinset z r).card ≤ (2 * r + 1) ^ (m + 1) := by
  refine Finset.card_image_le.trans ?_
  have h : (Finset.Icc (-(r : ℤ)) r).card = 2 * r + 1 := by simp [Int.card_Icc]; omega
  rw [Finset.card_product, Fintype.card_piFinset_const, h, pow_succ, mul_comm]

/-- At most `(2r+1)^d` elements of a finset lie within `ℓ^∞` distance `r` of a vertex. -/
theorem card_filter_latticeSupNorm_sub_le (A : Finset (Vertex m)) (z : Vertex m) (r : ℕ) :
    (A.filter fun y => latticeSupNorm (y - z) ≤ r).card ≤ (2 * r + 1) ^ (m + 1) :=
  (Finset.card_le_card fun _ hy => mem_cubeFinset (Finset.mem_filter.1 hy).2).trans
    (card_cubeFinset_le z r)

/-! ### Edges near a block -/

/-- The edges with an endpoint in the tripled block `⋃_{‖w‖_∞ ≤ 1} B(z + w)`. -/
def blockEdges (L : ℕ) (z : Vertex m) : Set (Edge m) :=
  {e | ∃ u ∈ (e : Sym2 (Vertex m)), latticeSupNorm (block L u - z) ≤ 1}

/-- Two vertices of an edge are equal or adjacent. -/
theorem eq_or_adj_of_mem_edge (e : Edge m) {u w : Vertex m} (hu : u ∈ (e : Sym2 (Vertex m)))
    (hw : w ∈ (e : Sym2 (Vertex m))) : u = w ∨ (latticeGraph m).Adj u w := by
  by_cases huw : u = w
  · exact Or.inl huw
  · right
    have he : (e : Sym2 (Vertex m)) = s(u, w) := (Sym2.mem_and_mem_iff huw).1 ⟨hu, hw⟩
    have := e.2
    rw [he, SimpleGraph.mem_edgeSet] at this
    exact this

/-- **Blocks at `ℓ^∞` distance at least `4` have disjoint edge sets.** -/
theorem disjoint_blockEdges {L : ℕ} (hL : 0 < L) {z z' : Vertex m}
    (h : 4 ≤ latticeSupNorm (z - z')) :
    Disjoint (blockEdges L z) (blockEdges L z') := by
  refine Set.disjoint_left.2 fun e ⟨u, hu, huz⟩ ⟨w, hw, hwz⟩ => ?_
  have huw : latticeSupNorm (block L w - block L u) ≤ 1 := by
    rcases eq_or_adj_of_mem_edge e hu hw with rfl | had
    · simp [latticeSupNorm_zero]
    · exact latticeSupNorm_block_sub_le_one_of_adj hL had
  have h1 := latticeSupNorm_sub_le z (block L u) z'
  have h2 := latticeSupNorm_sub_le (block L u) (block L w) z'
  have h3 : latticeSupNorm (z - block L u) ≤ 1 := by rwa [latticeSupNorm_sub_comm]
  have h4 : latticeSupNorm (block L u - block L w) ≤ 1 := by rwa [latticeSupNorm_sub_comm]
  omega

end CurvatureVariance.Infra.Kesten
