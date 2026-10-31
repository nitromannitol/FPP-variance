/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
public import CurvatureVariance.Paper.Proofs.Gain.TubeGeodesics
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import CurvatureVariance.Paper.Proofs.Localization.ModulusSupport

/-!
# Geometry of the subcube of a block (the proof of Lemma `lem:labels`)

The deterministic geometry behind the finite approximation, equation `eq:labelprofile`, for the
block `g` (offset `o`) of slab `i`, fine-cube side `w` and slope `t`:

* `blockCoord`: the coordinate `z = y − x₁ t − w (L g + o)` of a point relative to the block; the
  subcube faces (`subcubeFace`) are the points with `z ∈ w [⌈√L⌉, L − ⌈√L⌉)^{d−1}`
  (`mem_subcubeFace_iff`).
* The mesh: `meshIndex` (`⌊z/(wτ)⌋`), the finite box `meshBox L τ` of the indices of face points
  (independent of `n`, `w`, the block and the offset), the representatives `meshRep`, within
  `m w τ` of every face point with the same index (`norm_sub_meshRep_le`).
* The cubes `I_i(j)` of Section `sec:cubes` of the face points: their indices lie in the box
  `rowBox L o g` (`rowIndex_mem_rowBox`); a row cube lies in a transverse cube of side `w`
  (`rowCube_subset_transverseCube`), and two of them form a pair at distance `n` of side `≤ 2W_n`
  (`isCubePair_rowCubes`) whose slope differs from `t` by at most `m (1 + L w)/n`
  (`norm_rowPairSlope_sub_le`).
* The fine-cube indices within `ρ < ⌈√L⌉` of a segment `[j, k]` of row indices of face points are
  indices of the block (`mem_blockIndices_of_mem_tubeIndices`): this is where the margin `⌈√L⌉`
  of the subcube is used.
* Each face lies in one transverse cube of side `L w` (`subcubeFace_subset_transverseCube`), and the
  two faces form a pair at distance `n` with slope exactly `t` (`isCubePair_blockCubes`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Norms from coordinates -/

/-- Two vertices of one hyperplane are at the distance of their transverse parts. -/
theorem norm_point_sub_of_fst_eq {u v : Vertex m} (h : u.1 = v.1) :
    ‖point u - point v‖ = ‖transversePoint u.2 - transversePoint v.2‖ := by
  rw [← point_sub, ← transversePoint_sub]
  have h1 := norm_point_sq (u - v)
  have h2 : ((u - v).1 : ℝ) = 0 := by simp [h]
  rw [h2, Prod.snd_sub] at h1
  have h3 : ‖point (u - v)‖ ^ 2 = ‖transversePoint (u.2 - v.2)‖ ^ 2 := by rw [h1]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-! ### Coordinates relative to a block -/

/-- The coordinate `z = y − x₁ t − w (L g + o)` of the point `x = (x₁, y)` relative to the block
`g` with offset `o`. -/
noncomputable def blockCoord (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ)
    (x : Vertex m) (k : Fin m) : ℝ :=
  (x.2 k : ℝ) - x.1 * t k - w * ((L : ℝ) * g k + o k)

/-- The points of a subcube face are those of the hyperplane with
`z ∈ w [⌈√L⌉, L − ⌈√L⌉)^{d−1}`. -/
theorem mem_subcubeFace_iff {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ} {h : ℤ}
    {x : Vertex m} :
    x ∈ subcubeFace w L t o g h ↔ x.1 = h ∧ ∀ k,
      (w : ℝ) * ⌈Real.sqrt L⌉₊ ≤ blockCoord w L t o g x k ∧
        blockCoord w L t o g x k < (w : ℝ) * (L - ⌈Real.sqrt L⌉₊) := by
  unfold subcubeFace blockCoord
  simp only [mem_ofPred_eq]
  refine and_congr_right fun _ => forall_congr' fun k => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- On a subcube face, `0 ≤ z < w L`. -/
theorem blockCoord_mem_Ico {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ} {h : ℤ}
    {x : Vertex m} (hx : x ∈ subcubeFace w L t o g h) (k : Fin m) :
    0 ≤ blockCoord w L t o g x k ∧ blockCoord w L t o g x k < (w : ℝ) * L := by
  obtain ⟨-, hk⟩ := mem_subcubeFace_iff.mp hx
  obtain ⟨h1, h2⟩ := hk k
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hs : (0 : ℝ) ≤ ⌈Real.sqrt L⌉₊ := Nat.cast_nonneg _
  constructor
  · exact (mul_nonneg hw hs).trans h1
  · exact h2.trans_le (by nlinarith)

/-! ### The mesh -/

/-- The mesh index `⌊z/(wτ)⌋` of a point. -/
noncomputable def meshIndex (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ) (τ : ℝ)
    (x : Vertex m) : Fin m → ℤ :=
  fun k => ⌊blockCoord w L t o g x k / (w * τ)⌋

/-- The box `{0, …, ⌊L/τ⌋}^{d−1}` containing the mesh indices of the face points. -/
noncomputable def meshBox (m : ℕ) (L : ℕ) (τ : ℝ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc 0 ⌊(L : ℝ) / τ⌋

/-- The mesh index of a face point lies in the mesh box. -/
theorem meshIndex_mem_meshBox {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ} {h : ℤ}
    {τ : ℝ} (hw : 0 < w) (hτ : 0 < τ) {x : Vertex m} (hx : x ∈ subcubeFace w L t o g h) :
    meshIndex w L t o g τ x ∈ meshBox m L τ := by
  refine Fintype.mem_piFinset.mpr fun k => Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · have h0 := (blockCoord_mem_Ico hx k).1
    exact Int.floor_nonneg.mpr (div_nonneg h0 (by positivity))
  · have h1 := (blockCoord_mem_Ico hx k).2
    have hw' : (0 : ℝ) < w := by exact_mod_cast hw
    refine Int.floor_mono ?_
    rw [div_le_div_iff₀ (by positivity) hτ]
    nlinarith

open Classical in
/-- A representative of the mesh cell `a` in the face at height `h`: a face point with mesh index
`a` if there is one. -/
noncomputable def meshRep (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ) (τ : ℝ)
    (h : ℤ) (a : Fin m → ℤ) : Vertex m :=
  if hex : ∃ x ∈ subcubeFace w L t o g h, meshIndex w L t o g τ x = a then hex.choose
  else (h, 0)

/-- The representative of the cell of a face point is a face point of the same cell. -/
theorem meshRep_spec {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ} {τ : ℝ} {h : ℤ}
    {x : Vertex m} (hx : x ∈ subcubeFace w L t o g h) :
    meshRep w L t o g τ h (meshIndex w L t o g τ x) ∈ subcubeFace w L t o g h ∧
      meshIndex w L t o g τ (meshRep w L t o g τ h (meshIndex w L t o g τ x)) =
        meshIndex w L t o g τ x := by
  have hex : ∃ y ∈ subcubeFace w L t o g h, meshIndex w L t o g τ y = meshIndex w L t o g τ x :=
    ⟨x, hx, rfl⟩
  unfold meshRep
  simp only [hex, dite_true]
  exact hex.choose_spec

/-- **Face points are close to their representatives**: `|x − rep(x)| ≤ m w τ`. -/
theorem norm_sub_meshRep_le {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ} {τ : ℝ}
    {h : ℤ} (hw : 0 < w) (hτ : 0 < τ) {x : Vertex m} (hx : x ∈ subcubeFace w L t o g h) :
    ‖point x - point (meshRep w L t o g τ h (meshIndex w L t o g τ x))‖ ≤ m * (w * τ) := by
  obtain ⟨hr, hidx⟩ := meshRep_spec (τ := τ) hx
  set r := meshRep w L t o g τ h (meshIndex w L t o g τ x)
  have hx1 := (mem_subcubeFace_iff.mp hx).1
  have hr1 := (mem_subcubeFace_iff.mp hr).1
  rw [norm_point_sub_of_fst_eq (hx1.trans hr1.symm)]
  have hwτ : (0 : ℝ) < w * τ := mul_pos (by exact_mod_cast hw) hτ
  refine Localization.Modulus.norm_le_of_forall_abs_le hwτ.le fun k => ?_
  have hk := congrFun hidx k
  simp only [meshIndex] at hk
  have a1 := Int.floor_le (blockCoord w L t o g x k / (w * τ))
  have a2 := Int.lt_floor_add_one (blockCoord w L t o g x k / (w * τ))
  have b1 := Int.floor_le (blockCoord w L t o g r k / (w * τ))
  have b2 := Int.lt_floor_add_one (blockCoord w L t o g r k / (w * τ))
  rw [hk] at b1 b2
  have hdiff : blockCoord w L t o g x k - blockCoord w L t o g r k =
      (x.2 k : ℝ) - (r.2 k : ℝ) := by
    simp only [blockCoord, hx1, hr1]
    ring
  have c1 : blockCoord w L t o g x k / (w * τ) - blockCoord w L t o g r k / (w * τ) < 1 := by
    linarith
  have c2 : blockCoord w L t o g r k / (w * τ) - blockCoord w L t o g x k / (w * τ) < 1 := by
    linarith
  rw [← sub_div, div_lt_one hwτ] at c1 c2
  simp only [PiLp.sub_apply, transversePoint_apply]
  rw [abs_le]
  constructor <;> linarith

/-! ### Row cubes of the face points -/

/-- The box of the indices `j` of the cubes `I_i(j)` meeting a subcube face:
`L g + o + [⌈√L⌉, L − ⌈√L⌉]`, coordinatewise. -/
noncomputable def rowBox (L : ℕ) (o g : Fin m → ℤ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun k =>
    Finset.Icc ((L : ℤ) * g k + o k + ⌈Real.sqrt L⌉₊) ((L : ℤ) * g k + o k + L - ⌈Real.sqrt L⌉₊)

/-- The row index of a face point lies in the row box. -/
theorem rowIndex_mem_rowBox {n w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ}
    (hw : 1 ≤ w) {i' : ℤ} {x : Vertex m} (hx : x ∈ subcubeFace w L t o g (i' * n)) :
    rowIndex n w t i' x.2 ∈ rowBox L o g := by
  obtain ⟨hx1, hk⟩ := mem_subcubeFace_iff.mp hx
  refine Fintype.mem_piFinset.mpr fun k => Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;>
    obtain ⟨h1, h2⟩ := hk k <;> simp only [blockCoord, hx1] at h1 h2 <;> push_cast at h1 h2 <;>
    unfold rowIndex
  · have hf := Int.floor_le ((i' : ℝ) * n * t k)
    have hw' : (0 : ℝ) < w := by exact_mod_cast hw
    refine Int.le_floor.mpr ?_
    rw [le_div_iff₀ hw']
    push_cast
    nlinarith
  · have hf := Int.lt_floor_add_one ((i' : ℝ) * n * t k)
    have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
    refine Int.floor_le_iff.mpr ?_
    rw [div_lt_iff₀ (by linarith)]
    push_cast
    nlinarith

/-- The centre of the transverse cube containing `I_{i'}(j)`. -/
noncomputable def rowCubeCenter (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i' : ℤ)
    (j : Fin m → ℤ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun k => (⌊(i' : ℝ) * n * t k⌋ : ℝ) + w * j k + w / 2

/-- **A row cube lies in a transverse cube of side `w`.** -/
theorem rowCube_subset_transverseCube {n w : ℕ} (hw : 0 < w) (t : EuclideanSpace ℝ (Fin m))
    (i' : ℤ) (j : Fin m → ℤ) :
    rowCube n w t i' j ⊆ transverseCube (i' * n) (rowCubeCenter n w t i' j) w := by
  rintro x ⟨hx1, hx2⟩
  refine ⟨hx1, fun k => ?_⟩
  have hk := congrFun hx2 k
  unfold rowIndex at hk
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have a1 := Int.floor_le (((x.2 k : ℝ) - ⌊(i' : ℝ) * n * t k⌋) / w)
  have a2 := Int.lt_floor_add_one (((x.2 k : ℝ) - ⌊(i' : ℝ) * n * t k⌋) / w)
  rw [hk, le_div_iff₀ hw'] at a1
  rw [hk, div_lt_iff₀ hw'] at a2
  simp only [rowCubeCenter, PiLp.toLp_apply]
  rw [abs_le]
  constructor <;> nlinarith

/-- The slope `(c' − c)/n` of the pair of transverse cubes containing `I_{i−1}(j)` and `I_i(k)`. -/
noncomputable def rowPairSlope (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ)
    (j k : Fin m → ℤ) : EuclideanSpace ℝ (Fin m) :=
  (n : ℝ)⁻¹ • (rowCubeCenter n w t i k - rowCubeCenter n w t ((i : ℤ) - 1) j)

/-- **The row cubes of slab `i` form a pair at distance `n`** of side `w ≤ 2 W_n`. -/
theorem isCubePair_rowCubes {M : Model m} {K : ℕ} {A : ℝ} {n w : ℕ} (hn : 0 < n)
    (hw : (w : ℝ) ≤ 2 * W M K A n) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (j k : Fin m → ℤ) :
    IsCubePair M K A n 2 (rowPairSlope n w t i j k)
      (transverseCube (((i : ℤ) - 1) * n) (rowCubeCenter n w t ((i : ℤ) - 1) j) w)
      (transverseCube (((i : ℤ) - 1) * n + n) (rowCubeCenter n w t i k) w) := by
  refine ⟨((i : ℤ) - 1) * n, _, _, w, w, rfl, rfl, Nat.cast_nonneg _, hw, Nat.cast_nonneg _, hw,
    ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [rowPairSlope, smul_smul, mul_inv_cancel₀ hn', one_smul, sub_self, norm_zero]
  positivity

/-- **The slope of a pair of row cubes of face points**: `|t_{jk} − t| ≤ m (1 + L w)/n`. -/
theorem norm_rowPairSlope_sub_le {n w L : ℕ} (hn : 0 < n) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ)
    {o g j k : Fin m → ℤ} (hj : j ∈ rowBox L o g) (hk : k ∈ rowBox L o g) :
    ‖rowPairSlope n w t i j k - t‖ ≤ m * (1 + L * w) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : rowPairSlope n w t i j k - t =
      (n : ℝ)⁻¹ • (rowCubeCenter n w t i k - rowCubeCenter n w t ((i : ℤ) - 1) j -
        (n : ℝ) • t) := by
    simp only [rowPairSlope, smul_sub, smul_smul, inv_mul_cancel₀ hn'.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn'), inv_mul_eq_div,
    div_le_div_iff_of_pos_right hn']
  refine Localization.Modulus.norm_le_of_forall_abs_le (by positivity) fun l => ?_
  have hjl := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hj l)
  have hkl := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk l)
  have hkj1 : ((k l : ℤ) : ℝ) - j l ≤ L := by
    have : k l - j l ≤ (L : ℤ) := by omega
    exact_mod_cast this
  have hkj2 : -(L : ℝ) ≤ ((k l : ℤ) : ℝ) - j l := by
    have : -(L : ℤ) ≤ k l - j l := by omega
    exact_mod_cast this
  simp only [rowCubeCenter, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  push_cast
  have f1 := Int.floor_le ((i : ℝ) * n * t l)
  have f2 := Int.lt_floor_add_one ((i : ℝ) * n * t l)
  have f3 := Int.floor_le (((i : ℝ) - 1) * n * t l)
  have f4 := Int.lt_floor_add_one (((i : ℝ) - 1) * n * t l)
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Tubes inside the block -/

/-- **Fine cubes near a segment of row indices of face points are in the block**: if `j, k` are in
the row box and `j'` is within `ρ < ⌈√L⌉` of the segment `[j, k]`, then `j'` is an index of the
block. -/
theorem mem_blockIndices_of_mem_tubeIndices {L : ℕ} {o g j k : Fin m → ℤ}
    (hj : j ∈ rowBox L o g) (hk : k ∈ rowBox L o g) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < ⌈Real.sqrt L⌉₊) {j' : Fin m → ℤ} (h : j' ∈ tubeIndices j k (ENNReal.ofReal ρ)) :
    j' ∈ blockIndices L o g := by
  have hd : Metric.infDist (transversePoint j')
      (segment ℝ (transversePoint j) (transversePoint k)) ≤ ρ :=
    (ENNReal.ofReal_le_ofReal_iff hρ0).mp h
  obtain ⟨p, hp, hdist⟩ := (Metric.infDist_lt_iff ⟨transversePoint j, left_mem_segment ℝ _ _⟩).mp
    (hd.trans_lt hρ)
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  intro l
  have hjl := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hj l)
  have hkl := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk l)
  have hcoord : |(j' l : ℝ) - (a * j l + b * k l)| < ⌈Real.sqrt L⌉₊ := by
    have h1 := PiLp.norm_apply_le (transversePoint j' - (a • transversePoint j +
      b • transversePoint k)) l
    rw [dist_eq_norm] at hdist
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, transversePoint_apply,
      smul_eq_mul, Real.norm_eq_abs] at h1
    exact h1.trans_lt hdist
  rw [abs_lt] at hcoord
  have e1 : ((L : ℤ) * g l + o l + ⌈Real.sqrt L⌉₊ : ℝ) ≤ a * j l + b * k l := by
    have h1 : ((L : ℤ) * g l + o l + ⌈Real.sqrt L⌉₊ : ℝ) ≤ j l := by exact_mod_cast hjl.1
    have h2 : ((L : ℤ) * g l + o l + ⌈Real.sqrt L⌉₊ : ℝ) ≤ k l := by exact_mod_cast hkl.1
    have h3 := mul_le_mul_of_nonneg_left h1 ha
    have h4 := mul_le_mul_of_nonneg_left h2 hb
    have h5 : a * ((L : ℤ) * g l + o l + ⌈Real.sqrt L⌉₊ : ℝ) +
        b * ((L : ℤ) * g l + o l + ⌈Real.sqrt L⌉₊ : ℝ) =
        ((L : ℤ) * g l + o l + ⌈Real.sqrt L⌉₊ : ℝ) := by rw [← add_mul, hab, one_mul]
    linarith
  have e2 : a * j l + b * k l ≤ ((L : ℤ) * g l + o l + L - ⌈Real.sqrt L⌉₊ : ℝ) := by
    have h1 : (j l : ℝ) ≤ ((L : ℤ) * g l + o l + L - ⌈Real.sqrt L⌉₊ : ℝ) := by
      exact_mod_cast hjl.2
    have h2 : (k l : ℝ) ≤ ((L : ℤ) * g l + o l + L - ⌈Real.sqrt L⌉₊ : ℝ) := by
      exact_mod_cast hkl.2
    have h3 := mul_le_mul_of_nonneg_left h1 ha
    have h4 := mul_le_mul_of_nonneg_left h2 hb
    have h5 : a * ((L : ℤ) * g l + o l + L - ⌈Real.sqrt L⌉₊ : ℝ) +
        b * ((L : ℤ) * g l + o l + L - ⌈Real.sqrt L⌉₊ : ℝ) =
        ((L : ℤ) * g l + o l + L - ⌈Real.sqrt L⌉₊ : ℝ) := by rw [← add_mul, hab, one_mul]
    linarith
  constructor
  · have : ((L : ℤ) * g l + o l : ℝ) < j' l := by push_cast at e1 ⊢; linarith
    exact_mod_cast this.le
  · have : (j' l : ℝ) < ((L : ℤ) * g l + o l + L : ℝ) := by push_cast at e2 ⊢; linarith
    exact_mod_cast this

/-! ### The faces in one pair of transverse cubes -/

/-- The centre of the transverse cube of side `L w` containing the face at height `h`. -/
noncomputable def blockCenter (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ)
    (h : ℤ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun k => (h : ℝ) * t k + w * ((L : ℝ) * g k + o k + L / 2)

/-- **A subcube face lies in a transverse cube of side `L w`.** -/
theorem subcubeFace_subset_transverseCube {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {o g : Fin m → ℤ} (h : ℤ) :
    subcubeFace w L t o g h ⊆ transverseCube h (blockCenter w L t o g h) ((L : ℝ) * w) := by
  intro x hx
  have hx1 := (mem_subcubeFace_iff.mp hx).1
  refine ⟨hx1, fun k => ?_⟩
  have hk := blockCoord_mem_Ico hx k
  simp only [blockCoord, hx1] at hk
  simp only [blockCenter, PiLp.toLp_apply]
  rw [abs_le]
  constructor <;> nlinarith [hk.1, hk.2]

/-- **The two faces of a block lie in a pair of transverse cubes** at distance `n`, of side
`L w ≤ (2L + 2) W_n`, with slope exactly `t`. -/
theorem isCubePair_blockCubes {M : Model m} {K : ℕ} {A : ℝ} {n w L : ℕ}
    (hw : (w : ℝ) ≤ 2 * W M K A n) (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ) (p : ℤ) :
    IsCubePair M K A n (2 * L + 2) t
      (transverseCube p (blockCenter w L t o g p) ((L : ℝ) * w))
      (transverseCube (p + n) (blockCenter w L t o g (p + n)) ((L : ℝ) * w)) := by
  have hW : 0 ≤ W M K A n := Real.sqrt_nonneg _
  refine ⟨p, _, _, (L : ℝ) * w, (L : ℝ) * w, rfl, rfl, by positivity, ?_, by positivity, ?_, ?_⟩
  · have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  · have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  · have heq : blockCenter w L t o g (p + n) - blockCenter w L t o g p - (n : ℝ) • t = 0 := by
      ext k
      simp only [blockCenter, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
      push_cast
      ring
    rw [heq, norm_zero]
    positivity

end CurvatureVariance.Paper.Gain
