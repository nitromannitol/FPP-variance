/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Labels.Geometry
public import IsotropicVariance.Paper.Proofs.Labels.BlockTime
import IsotropicVariance.Paper.Proofs.Labels.Region
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rounded points of Step 2 of the proof of Lemma `lem:labels`

The points `u_κ` and `v_κ` are obtained from
`u = ((i−1)n, (nQ_n)^{1/2}(z + w))` and `v = (in, (nQ_n)^{1/2}(z + w'))` by replacing `w` and `w'`
by `κ⌊w/κ⌋` and `κ⌊w'/κ⌋`. In Lean the slabs are 0-based and `(nQ_n)^{1/2}` is `W`.

* `gridIndex`, `gridCell`: the index `⌊w/κ⌋`, for `w ∈ [0, L)`; `gridRel`, `roundPt`: the rounded
  point, relative to the corner of the block and in absolute coordinates.
* `InBox`: the transverse coordinates lie in `W(z + [s, L − s]^m)`. The core of a face is the
  case `s = √L` (`coreFace_iff`); the rounded points of the core have `s = √L/2`, which is the
  paper's "at distance at least `(LnQ_n)^{1/2}/2` from the other blocks".
* `InBox.hasMargin_of_infDist_le`: a point near the segment between two such points has a margin.
* The Euclidean estimates of Step 2: `||v − u| − n| ≤ C L² Q_n` on the cores, and
  `|v − u|` changes by at most `C L κ Q_n` when `u`, `v` are replaced by `u_κ`, `v_κ`.
* `pairOf`: the at most `(L + 1)^{2m}` pairs of cubes of side `4W` covering the faces of the block.
-/

@[expose] public section

open Set Metric

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper

variable {m : ℕ}

/-! ### Rounding down to multiples of `κ` -/

/-- The largest index of a multiple of `κ` in `[0, L)`. -/
noncomputable def gridTop (L : ℕ) (κ : ℝ) : ℕ := ⌈(L : ℝ) / κ⌉₊ - 1

/-- The multiples of `κ` of the indices lie in `[0, L)`. -/
theorem gridTop_mul_lt {L : ℕ} (hL : 1 ≤ L) {κ : ℝ} (hκ : 0 < κ) :
    (gridTop L κ : ℝ) * κ < L := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hy : 0 < (L : ℝ) / κ := div_pos hL' hκ
  have h1 : (1 : ℝ) ≤ ⌈(L : ℝ) / κ⌉₊ := by exact_mod_cast Nat.ceil_pos.2 hy
  have h2 := Nat.ceil_lt_add_one hy.le
  have h3 : (gridTop L κ : ℝ) = ⌈(L : ℝ) / κ⌉₊ - 1 := by
    rw [gridTop, Nat.cast_sub (by exact_mod_cast h1), Nat.cast_one]
  rw [h3, ← lt_div_iff₀ hκ]
  linarith only [h2]

/-- The index `⌊t/κ⌋` of `t ∈ [0, L)`, clipped to the multiples of `κ` in `[0, L)`. -/
noncomputable def gridIndex (L : ℕ) (κ t : ℝ) : Fin (gridTop L κ + 1) :=
  ⟨min ⌊t / κ⌋₊ (gridTop L κ), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- On `[0, L)`, the index is `⌊t/κ⌋`. -/
theorem gridIndex_spec {L : ℕ} {κ t : ℝ} (hκ : 0 < κ) (ht0 : 0 ≤ t) (htL : t < L) :
    ((gridIndex L κ t : ℕ) : ℝ) * κ ≤ t ∧ t < (((gridIndex L κ t : ℕ) : ℝ) + 1) * κ := by
  have h0 : 0 ≤ t / κ := div_nonneg ht0 hκ.le
  have hfl : ⌊t / κ⌋₊ ≤ gridTop L κ := by
    have h1 : (⌊t / κ⌋₊ : ℝ) < (L : ℝ) / κ :=
      (Nat.floor_le h0).trans_lt (div_lt_div_of_pos_right htL hκ)
    have h2 : ⌊t / κ⌋₊ < ⌈(L : ℝ) / κ⌉₊ := Nat.lt_ceil.2 h1
    rw [gridTop]
    omega
  have hidx : (gridIndex L κ t : ℕ) = ⌊t / κ⌋₊ := min_eq_left hfl
  rw [hidx]
  exact ⟨(le_div_iff₀ hκ).1 (Nat.floor_le h0), (div_lt_iff₀ hκ).1 (Nat.lt_floor_add_one _)⟩

/-- The rounded relative coordinates of a point of a face of a block: one index per transverse
coordinate. -/
abbrev GridCell (m L : ℕ) (κ : ℝ) : Type := Fin m → Fin (gridTop L κ + 1)

/-- `⌊w/κ⌋`, coordinate by coordinate, of a point `y` relative to the corner of its block, for
`y = (s, W w)`. -/
noncomputable def gridCell (W : ℝ) (L : ℕ) (κ : ℝ) (y : Pt m) : GridCell m L κ :=
  fun k => gridIndex L κ (Pt.tr y k / W)

/-- The point `(s, W κ g)`, relative to the corner of a block. -/
noncomputable def gridRel {L : ℕ} (s W κ : ℝ) (g : GridCell m L κ) : Pt m :=
  Pt.mk s (WithLp.toLp 2 fun k => W * (κ * ((g k : ℕ) : ℝ)))

/-- **`u_κ` and `v_κ`** (Step 2 of the proof of Lemma `lem:labels`): the point `x` of a face of the
block `(i, z)` at height `s` above the corner, with its relative coordinates `w` replaced by
`κ⌊w/κ⌋`. -/
noncomputable def roundPt (n W : ℝ) (L : ℕ) (κ : ℝ) (i : ℕ) (z : Fin m → ℤ) (s : ℝ) (x : Pt m) :
    Pt m :=
  blockCorner n W i z + gridRel s W κ (gridCell W L κ (x - blockCorner n W i z))

theorem lon_roundPt (n W : ℝ) (L : ℕ) (κ : ℝ) (i : ℕ) (z : Fin m → ℤ) (s : ℝ) (x : Pt m) :
    Pt.lon (roundPt n W L κ i z s x) = (i : ℝ) * n + s := rfl

/-- The point of a grid relative to the corner of a block lies in the block, for a height
`0 ≤ s ≤ n`. -/
theorem corner_add_gridRel_mem_block {n W κ s : ℝ} (hW : 0 < W) (hκ : 0 < κ) {L : ℕ} (hL : 1 ≤ L)
    (hs0 : 0 ≤ s) (hsn : s ≤ n) (i : ℕ) (z : Fin m → ℤ) (g : GridCell m L κ) :
    blockCorner n W i z + gridRel s W κ g ∈ block n W L i z := by
  have hlon : Pt.lon (blockCorner n W i z + gridRel s W κ g) = (i : ℝ) * n + s := rfl
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [hlon]
    linarith only [hs0]
  · rw [hlon]
    linarith only [hsn]
  have htr : Pt.tr (blockCorner n W i z + gridRel s W κ g) k =
      W * z k + W * (κ * ((g k : ℕ) : ℝ)) := rfl
  have hg : ((g k : ℕ) : ℝ) ≤ gridTop L κ := by exact_mod_cast Nat.lt_succ_iff.1 (g k).isLt
  have h0 : 0 ≤ W * (κ * ((g k : ℕ) : ℝ)) := by positivity
  have h1 : κ * ((g k : ℕ) : ℝ) < L := by
    calc κ * ((g k : ℕ) : ℝ) ≤ κ * gridTop L κ := mul_le_mul_of_nonneg_left hg hκ.le
      _ = (gridTop L κ : ℝ) * κ := mul_comm _ _
      _ < L := gridTop_mul_lt hL hκ
  have h2 : W * (κ * ((g k : ℕ) : ℝ)) < W * L := mul_lt_mul_of_pos_left h1 hW
  have e : W * ((z k : ℝ) + L) = W * z k + W * L := by ring
  rw [htr, e]
  constructor <;> linarith only [h0, h2]

/-! ### Boxes of the faces -/

/-- The transverse coordinates of `x` lie in `W(z + [s, L − s]^m)`. -/
def InBox (W : ℝ) (L : ℕ) (z : Fin m → ℤ) (s : ℝ) (x : Pt m) : Prop :=
  ∀ k, W * ((z k : ℝ) + s) ≤ Pt.tr x k ∧ Pt.tr x k ≤ W * ((z k : ℝ) + L - s)

/-- The core of a face is the case `s = √L`. -/
theorem coreFace_iff {n W : ℝ} {L i : ℕ} {z : Fin m → ℤ} {x : Pt m} :
    x ∈ coreFace n W L i z ↔ Pt.lon x = (i : ℝ) * n ∧ InBox W L z (Real.sqrt L) x :=
  Iff.rfl

theorem InBox.mono {W : ℝ} (hW : 0 ≤ W) {L : ℕ} {z : Fin m → ℤ} {s s' : ℝ} {x : Pt m}
    (h : InBox W L z s x) (hs : s' ≤ s) : InBox W L z s' x := fun k => by
  have h1 : W * ((z k : ℝ) + s') ≤ W * ((z k : ℝ) + s) :=
    mul_le_mul_of_nonneg_left (by linarith only [hs]) hW
  have h2 : W * ((z k : ℝ) + L - s) ≤ W * ((z k : ℝ) + L - s') :=
    mul_le_mul_of_nonneg_left (by linarith only [hs]) hW
  exact ⟨h1.trans (h k).1, (h k).2.trans h2⟩

/-- Rounding moves a transverse coordinate down by at most `Wκ`. -/
theorem tr_roundPt_mem {n W κ s r : ℝ} (hW : 0 < W) (hκ : 0 < κ) (hr : 0 < r) {L i : ℕ}
    {z : Fin m → ℤ} {x : Pt m} (hx : InBox W L z r x) (k : Fin m) :
    Pt.tr x k - W * κ ≤ Pt.tr (roundPt n W L κ i z s x) k ∧
      Pt.tr (roundPt n W L κ i z s x) k ≤ Pt.tr x k := by
  have htr : Pt.tr (x - blockCorner n W i z) k = Pt.tr x k - W * z k :=
    Labels.tr_sub_blockCorner_apply n W i z x k
  obtain ⟨t, ht⟩ : ∃ t, t = Pt.tr (x - blockCorner n W i z) k / W := ⟨_, rfl⟩
  have hWt : W * t = Pt.tr x k - W * z k := by
    rw [ht, htr, mul_div_cancel₀ _ hW.ne']
  have hx1 : W * ((z k : ℝ) + r) ≤ Pt.tr x k := (hx k).1
  have hx2 : Pt.tr x k ≤ W * ((z k : ℝ) + L - r) := (hx k).2
  have hWr : 0 < W * r := mul_pos hW hr
  have e1 : W * ((z k : ℝ) + r) = W * z k + W * r := by ring
  have e2 : W * ((z k : ℝ) + L - r) = W * z k + W * L - W * r := by ring
  have ht0 : 0 ≤ t := by
    refine nonneg_of_mul_nonneg_right (a := W) ?_ hW
    linarith only [hWt, hx1, e1, hWr]
  have htL : t < L := by
    refine lt_of_mul_lt_mul_left ?_ hW.le
    linarith only [hWt, hx2, e2, hWr]
  obtain ⟨h1, h2⟩ := gridIndex_spec (L := L) hκ ht0 htL
  have hr : Pt.tr (roundPt n W L κ i z s x) k =
      W * z k + W * (κ * ((gridIndex L κ t : ℕ) : ℝ)) := by
    rw [ht]
    rfl
  rw [hr]
  obtain ⟨g, hg⟩ : ∃ g, g = ((gridIndex L κ t : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hg] at h1 h2 ⊢
  have h3 : W * (κ * g) ≤ W * t := mul_le_mul_of_nonneg_left (by linarith only [h1]) hW.le
  have h4 : W * t ≤ W * ((g + 1) * κ) := mul_le_mul_of_nonneg_left h2.le hW.le
  have h5 : W * ((g + 1) * κ) = W * (κ * g) + W * κ := by ring
  constructor <;> linarith only [h3, h4, h5, hWt]

/-- Rounding shrinks a box by `κ`. -/
theorem InBox.roundPt {n W κ s₀ : ℝ} (hW : 0 < W) (hκ : 0 < κ) {L i : ℕ} {z : Fin m → ℤ} {x : Pt m}
    {r : ℝ} (hr : 0 < r) (hx : InBox W L z r x) :
    InBox W L z (r - κ) (roundPt n W L κ i z s₀ x) := fun k => by
  obtain ⟨h1, h2⟩ := tr_roundPt_mem (n := n) (i := i) (s := s₀) hW hκ hr hx k
  have h3 := (hx k).1
  have h4 := (hx k).2
  have h5 : W * ((z k : ℝ) + (r - κ)) = W * ((z k : ℝ) + r) - W * κ := by ring
  have h6 : W * ((z k : ℝ) + L - r) ≤ W * ((z k : ℝ) + L - (r - κ)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hκ]) hW.le
  exact ⟨by linarith only [h1, h3, h5], by linarith only [h2, h4, h6]⟩

/-- A point on the hyperplane of height `s` above the corner is within `√m κ W` of its rounding. -/
theorem dist_roundPt_le {n W κ s r : ℝ} (hW : 0 < W) (hκ : 0 < κ) (hr : 0 < r) {L i : ℕ}
    {z : Fin m → ℤ} {x : Pt m} (hlon : Pt.lon x = (i : ℝ) * n + s) (hx : InBox W L z r x) :
    dist x (roundPt n W L κ i z s x) ≤ Real.sqrt m * κ * W := by
  rw [Labels.dist_eq_norm_tr_sub (hlon.trans (lon_roundPt n W L κ i z s x).symm), mul_assoc]
  refine Profiles.norm_le_of_abs_le (by positivity) fun k => ?_
  obtain ⟨h1, h2⟩ := tr_roundPt_mem (n := n) (i := i) (s := s) hW hκ hr hx k
  rw [PiLp.sub_apply, abs_le, mul_comm κ W]
  constructor <;> linarith only [h1, h2]

/-- A point of the face of the block in `W(z + [s, L − s]^m)`, `s ≥ 0`, has a transverse
displacement of at most `√m L W` from another. -/
theorem InBox.norm_tr_sub_le {W s : ℝ} (hW : 0 ≤ W) (hs : 0 ≤ s) {L : ℕ} {z : Fin m → ℤ}
    {u v : Pt m} (hu : InBox W L z s u) (hv : InBox W L z s v) :
    ‖Pt.tr v - Pt.tr u‖ ≤ Real.sqrt m * L * W := by
  rw [mul_assoc]
  refine Profiles.norm_le_of_abs_le (by positivity) fun k => ?_
  obtain ⟨hu₁, hu₂⟩ := (hu.mono hW hs) k
  obtain ⟨hv₁, hv₂⟩ := (hv.mono hW hs) k
  have e1 : W * ((z k : ℝ) + 0) = W * z k := by ring
  have e2 : W * ((z k : ℝ) + L - 0) = W * z k + L * W := by ring
  rw [PiLp.sub_apply, abs_le]
  constructor <;> linarith only [hu₁, hu₂, hv₁, hv₂, e1, e2]

/-- **A point near a segment has a margin**: within `√L W/2 − 2` of the segment between two points
of `W(z + [√L/2, L − √L/2]^m)`, its transverse coordinates are at distance at least `2` from the
sides of the block. -/
theorem InBox.hasMargin_of_infDist_le {W : ℝ} {L : ℕ} {z : Fin m → ℤ} {u v y : Pt m}
    (hu : InBox W L z (Real.sqrt L / 2) u) (hv : InBox W L z (Real.sqrt L / 2) v)
    (hy : infDist y (segment ℝ u v) ≤ Real.sqrt L * W / 2 - 2) : HasMargin W L z y := fun k => by
  have h := Labels.tr_mem_Icc_of_infDist_segment_le k (hu k) (hv k) hy
  have e1 : W * ((z k : ℝ) + Real.sqrt L / 2) - (Real.sqrt L * W / 2 - 2) = W * z k + 2 := by ring
  have e2 : W * ((z k : ℝ) + L - Real.sqrt L / 2) + (Real.sqrt L * W / 2 - 2) =
      W * ((z k : ℝ) + L) - 2 := by ring
  exact ⟨by linarith only [h.1, e1], by linarith only [h.2, e2]⟩

/-! ### The Euclidean estimates -/

/-- `|v − u|` changes by at most `2 m L κ Q` when `u` and `v` are moved by at most `√m κ W` (Step 2
of the proof of Lemma `lem:labels`), for `W² = nQ` and transverse displacements at most `√m L W`. -/
theorem abs_dist_sub_dist_le_of_mesh {u v u' v' : Pt m} {n W Q κ : ℝ} (hn : 0 < n) (hW : 0 ≤ W)
    (hWQ : W ^ 2 = n * Q) {L : ℕ} (huv : Pt.lon v - Pt.lon u = n)
    (huv' : Pt.lon v' - Pt.lon u' = n) (hR : ‖Pt.tr v - Pt.tr u‖ ≤ Real.sqrt m * L * W)
    (hR' : ‖Pt.tr v' - Pt.tr u'‖ ≤ Real.sqrt m * L * W)
    (hd : dist u u' ≤ Real.sqrt m * κ * W) (hd' : dist v v' ≤ Real.sqrt m * κ * W) :
    |dist u v - dist u' v'| ≤ 2 * m * L * κ * Q := by
  have h0 := Labels.abs_dist_sub_dist_le hn huv huv' hR hR'
  have hR0 : 0 ≤ Real.sqrt m * L * W / n := by positivity
  have h1 := mul_le_mul_of_nonneg_left (add_le_add hd hd') hR0
  have hm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (Nat.cast_nonneg m)
  have heq : Real.sqrt m * L * W / n * (Real.sqrt m * κ * W + Real.sqrt m * κ * W) =
      2 * m * L * κ * Q := by
    have e : Real.sqrt m * L * W / n * (Real.sqrt m * κ * W + Real.sqrt m * κ * W) =
        2 * (Real.sqrt m * Real.sqrt m) * L * κ * W ^ 2 / n := by ring
    rw [e, hm, hWQ]
    field_simp
  linarith only [h0, h1, heq]

/-- `|v − u| − n ≤ m L² Q/2` for transverse displacements at most `√m L W`, for `W² = nQ`
(Step 2 of the proof of Lemma `lem:labels`). -/
theorem dist_sub_le_of_tr {u v : Pt m} {n W Q : ℝ} (hn : 0 < n) (hWQ : W ^ 2 = n * Q)
    {L : ℕ} (huv : Pt.lon v - Pt.lon u = n) (hR : ‖Pt.tr v - Pt.tr u‖ ≤ Real.sqrt m * L * W) :
    dist u v - n ≤ m * L ^ 2 * Q / 2 := by
  have h0 := Labels.dist_sub_le_sq_div hn huv
  have hm : Real.sqrt m ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  have hsq : ‖Pt.tr v - Pt.tr u‖ ^ 2 ≤ (Real.sqrt m * L * W) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hR 2
  have e : (Real.sqrt m * L * W) ^ 2 / (2 * n) = m * L ^ 2 * Q / 2 := by
    rw [mul_pow, mul_pow, hm, hWQ]
    field_simp
  have h1 : ‖Pt.tr v - Pt.tr u‖ ^ 2 / (2 * n) ≤ (Real.sqrt m * L * W) ^ 2 / (2 * n) :=
    div_le_div_of_nonneg_right hsq (by positivity)
  linarith only [h0, h1, e]

/-! ### The cubes covering the faces of a block -/

/-- The index set of the pairs of cubes covering the faces of a block (Step 2 of the proof of Lemma
`lem:labels`). -/
abbrev PairIdx (m L : ℕ) : Type := (Fin m → Fin (L + 1)) × (Fin m → Fin (L + 1))

/-- The pair `ab` of cubes of side `4W` covering the faces of the block `(i, z)`. -/
noncomputable def pairOf (n W : ℝ) {L : ℕ} (i : ℕ) (z : Fin m → ℤ) (ab : PairIdx m L) :
    CubePair m :=
  Labels.coverPair n W i z (fun k => ((ab.1 k : ℕ) : ℤ)) (fun k => ((ab.2 k : ℕ) : ℤ))

/-- The number of pairs of cubes. -/
theorem card_pairIdx (m L : ℕ) : (Fintype.card (PairIdx m L) : ℝ) = ((L : ℝ) + 1) ^ (2 * m) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  push_cast
  ring

/-- The pairs of cubes are admissible at slope `1/2`, for `√m L W ≤ n/2`. -/
theorem pairOf_isAdmissible {n W : ℝ} {L : ℕ} (hn : 0 < n) (hW : 0 ≤ W) (i : ℕ) (z : Fin m → ℤ)
    (ab : PairIdx m L) (hslope : Real.sqrt m * L * W ≤ n / 2) :
    (pairOf n W i z ab).IsAdmissible n W (1 / 2) := by
  refine Labels.coverPair_isAdmissible hn hW i z (fun k => ?_) hslope
  have ha := (ab.1 k).isLt
  have hb := (ab.2 k).isLt
  rw [abs_le]
  constructor <;> omega

/-- The `W`-neighborhoods in the two faces of two points of the cores of a block lie in one of the
pairs of cubes. -/
theorem exists_pairOf {n W : ℝ} {L i : ℕ} {z : Fin m → ℤ} (hW : 0 < W) {u v : Pt m}
    (hu : u ∈ coreFace n W L i z) (hv : v ∈ coreFace n W L (i + 1) z) :
    ∃ ab : PairIdx m L,
      (∀ u' : Pt m, Pt.lon u' = (i : ℝ) * n → dist u u' ≤ W → u' ∈ (pairOf n W i z ab).first) ∧
      ∀ v' : Pt m, Pt.lon v' = ((i + 1 : ℕ) : ℝ) * n → dist v v' ≤ W →
        v' ∈ (pairOf n W i z ab).second := by
  obtain ⟨a, b, h1, h2, -⟩ := Labels.exists_coverPair hW hu hv
  exact ⟨(a, b), h1, h2⟩

end IsotropicVariance.Paper.Proofs.Labels
