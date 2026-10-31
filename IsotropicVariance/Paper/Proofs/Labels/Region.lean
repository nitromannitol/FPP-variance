/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Restricted
public import IsotropicVariance.Paper.Defs.Blocks
public import IsotropicVariance.Infra.Measurability.SlabTime
import IsotropicVariance.Paper.Proofs.Labels.Geometry

/-!
# The region of a block where the slab density is determined by the noise in the block

For the block `G = [in, (i+1)n] × W(z + [0, L)^m)` of the slab `i`, a point of the slab whose
transverse coordinates are at distance at least `2` from the sides of the block is within distance
one of the faces of the slab (where the slab density is the fixed bound `b`), or its closed unit
ball lies in the interior of `G` (where the density is determined by the noise in `G`). A point
within distance `d` of a segment between two points whose transverse coordinates lie in an
interval has its transverse coordinates in the interval enlarged by `d`. Together with equation
`eq:localization` this places the `1`-optimal curves between points of the cores of the faces of
`G` in that region (first paragraph of the proof of Lemma `lem:labels`).
-/

@[expose] public section

open Set Metric

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper

variable {m : ℕ}

/-! ### Coordinates -/

/-- A point on a segment has its transverse coordinates between those of the endpoints. -/
theorem tr_mem_Icc_of_mem_segment {u v s : Pt m} {lo hi : ℝ} (k : Fin m)
    (hu : Pt.tr u k ∈ Icc lo hi) (hv : Pt.tr v k ∈ Icc lo hi) (hs : s ∈ segment ℝ u v) :
    Pt.tr s k ∈ Icc lo hi := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hs
  simp only [Pt.tr_add, Pt.tr_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hlo : a * lo + b * lo = lo := by rw [← add_mul, hab, one_mul]
  have hhi : a * hi + b * hi = hi := by rw [← add_mul, hab, one_mul]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hu.1 ha, mul_le_mul_of_nonneg_left hv.1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hu.2 ha, mul_le_mul_of_nonneg_left hv.2 hb]

/-- **Near a segment.** A point within distance `d` of a segment between two points whose
transverse coordinate `k` lies in `[lo, hi]` has its coordinate `k` in `[lo − d, hi + d]`. -/
theorem tr_mem_Icc_of_infDist_segment_le {u v y : Pt m} {lo hi d : ℝ} (k : Fin m)
    (hu : Pt.tr u k ∈ Icc lo hi) (hv : Pt.tr v k ∈ Icc lo hi)
    (hy : infDist y (segment ℝ u v) ≤ d) : Pt.tr y k ∈ Icc (lo - d) (hi + d) := by
  have hcpt : IsCompact (segment ℝ u v) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨s, hs, hds⟩ := hcpt.exists_infDist_eq_dist
    ⟨u, left_mem_segment ℝ u v⟩ y
  have hsk := tr_mem_Icc_of_mem_segment k hu hv hs
  have hk := abs_tr_sub_le_dist y s k
  rw [← hds] at hk
  rw [abs_le] at hk
  constructor <;> linarith [hsk.1, hsk.2, hk.1, hk.2]

/-! ### The slab `i` and its block -/

theorem mem_chainSlab_set {n : ℝ} {i : ℕ} {x : Pt m} :
    x ∈ (chainSlab n 0 i).set ↔ (i : ℝ) * n ≤ Pt.lon x ∧ Pt.lon x ≤ ((i : ℝ) + 1) * n := by
  rw [Paper.mem_chainSlab_set, Pt.lon_zero, zero_add, add_mul, one_mul]

theorem mem_chainSlab_faces {n : ℝ} {i : ℕ} {x : Pt m}
    (hx : Pt.lon x = (i : ℝ) * n ∨ Pt.lon x = ((i : ℝ) + 1) * n) :
    x ∈ (chainSlab n 0 i).faces := by
  refine ⟨x - ((i : ℝ) * n) • e₁, ?_, ?_⟩
  · change Pt.lon (x - ((i : ℝ) * n) • e₁) = 0 ∨ Pt.lon (x - ((i : ℝ) * n) • e₁) = n
    rw [Pt.lon_sub, Pt.lon_smul, Pt.lon_e₁, mul_one]
    rcases hx with h | h
    · left; linarith
    · right; linarith
  · simp [chainSlab, e1Slab]

/-- A point at distance at most one from a face of the slab is within distance one of the
faces. -/
theorem infDist_faces_le_one_of_lon {n : ℝ} {i : ℕ} {x : Pt m} (c : ℝ)
    (hc : c = (i : ℝ) * n ∨ c = ((i : ℝ) + 1) * n) (h : |Pt.lon x - c| ≤ 1) :
    infDist x (chainSlab n 0 i).faces ≤ 1 := by
  set y : Pt m := Pt.mk c (Pt.tr x)
  have hy : y ∈ (chainSlab n 0 i).faces := mem_chainSlab_faces (by simpa [y] using hc)
  refine (infDist_le_dist_of_mem hy).trans ?_
  rw [Infra.Slab.dist_eq_abs_lon_sub (by simp [y])]
  simpa [y] using h

/-- The open box inside a block. -/
theorem isOpen_blockInterior (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    IsOpen {y : Pt m | (i : ℝ) * n < Pt.lon y ∧ Pt.lon y < ((i : ℝ) + 1) * n ∧
      ∀ k, W * z k < Pt.tr y k ∧ Pt.tr y k < W * (z k + L)} := by
  have hlon : Continuous (Pt.lon : Pt m → ℝ) := Pt.continuous_lon
  have htr : ∀ k : Fin m, Continuous fun y : Pt m => Pt.tr y k := fun k =>
    (PiLp.continuous_apply 2 _ k).comp
      ((WithLp.prod_continuous_ofLp 2 ℝ (EuclideanSpace ℝ (Fin m))).snd)
  have hset : {y : Pt m | (i : ℝ) * n < Pt.lon y ∧ Pt.lon y < ((i : ℝ) + 1) * n ∧
      ∀ k, W * z k < Pt.tr y k ∧ Pt.tr y k < W * (z k + L)} =
      {y | (i : ℝ) * n < Pt.lon y} ∩ ({y | Pt.lon y < ((i : ℝ) + 1) * n} ∩
        ⋂ k, ({y | W * z k < Pt.tr y k} ∩ {y | Pt.tr y k < W * (z k + L)})) := by
    ext y
    simp [Set.mem_iInter]
  rw [hset]
  exact (isOpen_lt continuous_const hlon).inter ((isOpen_lt hlon continuous_const).inter
    (isOpen_iInter_of_finite fun k =>
      (isOpen_lt continuous_const (htr k)).inter (isOpen_lt (htr k) continuous_const)))

/-- **The determined region.** A point of the slab `i` whose transverse coordinates are at
distance at least `2` from the sides of the block `(i, z)` is within distance one of the faces of
the slab, or its closed unit ball lies in the interior of the block. -/
theorem infDist_faces_le_one_or_closedBall_subset {n W : ℝ} {L i : ℕ} {z : Fin m → ℤ}
    {x : Pt m} (hx : x ∈ (chainSlab n 0 i).set)
    (htr : ∀ k, W * z k + 2 ≤ Pt.tr x k ∧ Pt.tr x k ≤ W * (z k + L) - 2) :
    infDist x (chainSlab n 0 i).faces ≤ 1 ∨ closedBall x 1 ⊆ interior (block n W L i z) := by
  rw [mem_chainSlab_set] at hx
  by_cases h : infDist x (chainSlab n 0 i).faces ≤ 1
  · exact Or.inl h
  right
  have h1 : (i : ℝ) * n + 1 < Pt.lon x := by
    by_contra hc
    exact h (infDist_faces_le_one_of_lon _ (Or.inl rfl)
      (abs_le.2 ⟨by linarith [hx.1], by linarith⟩))
  have h2 : Pt.lon x < ((i : ℝ) + 1) * n - 1 := by
    by_contra hc
    exact h (infDist_faces_le_one_of_lon _ (Or.inr rfl)
      (abs_le.2 ⟨by linarith, by linarith [hx.2]⟩))
  refine subset_trans ?_ (interior_maximal ?_ (isOpen_blockInterior n W L i z))
  · intro y hy
    rw [mem_closedBall] at hy
    have hl := Infra.Slab.abs_lon_sub_le y x
    refine ⟨by linarith [(abs_le.1 hl).1], by linarith [(abs_le.1 hl).2], fun k => ?_⟩
    have ht := abs_tr_sub_le_dist y x k
    constructor <;> linarith [(abs_le.1 ht).1, (abs_le.1 ht).2, (htr k).1, (htr k).2]
  · rintro y ⟨hy1, hy2, hy3⟩
    exact ⟨hy1.le, hy2.le, fun k => ⟨(hy3 k).1.le, (hy3 k).2⟩⟩

end IsotropicVariance.Paper.Proofs.Labels
