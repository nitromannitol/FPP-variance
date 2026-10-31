/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum
public import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
public import IsotropicVariance.Infra.Measurability.SlabTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# The plane geometry of the chain of slabs

Deterministic geometry behind the proof of Lemma `lem:smallmean`.

* The cubes `I_i(j)` of equation `eq:cubes` lie in the faces of the slab `i` of the chain, slabs
  have disjoint interiors, cubes are compact and nonempty.
* Displacement bounds: points of `I_i(j)` and `I_{i+1}(k)` are at distance at least `s`, at most
  `2s` for close cubes, and the excess of the distance over `s` is at least
  `W²(|k − j| − √m)₊²/(3s)`; the slope is at most `2`.
* Cell indices `⌊tr x / W⌋`, and admissible points of equation `eq:F`.
-/

@[expose] public section

open Set Metric
open IsotropicVariance.Paper.Proofs.Profiles
open IsotropicVariance.Infra.Slab

namespace IsotropicVariance.Paper.Proofs.SmallMean

variable {m : ℕ}

/-! ## Translations -/

lemma constVAdd_apply (c x : Pt m) : AffineIsometryEquiv.constVAdd ℝ (Pt m) c x = c + x := rfl

lemma constVAdd_symm_apply (c x : Pt m) :
    (AffineIsometryEquiv.constVAdd ℝ (Pt m) c).symm x = x - c := by
  rw [AffineIsometryEquiv.symm_apply_eq, constVAdd_apply]
  abel

/-- Membership in the image of a set under a translation. -/
lemma mem_image_constVAdd {c x : Pt m} {S : Set (Pt m)} :
    x ∈ (AffineIsometryEquiv.constVAdd ℝ (Pt m) c) '' S ↔ x - c ∈ S := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [constVAdd_apply] using hz
  · intro h
    exact ⟨x - c, h, by simp [constVAdd_apply]⟩

lemma slabCoord_constVAdd (c : Pt m) (w : ℝ) (x : Pt m) :
    slabCoord (⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) c, w⟩ : Slab m) x = Pt.lon x - Pt.lon c := by
  simp [slabCoord, constVAdd_symm_apply]

/-! ## Norms of coordinate vectors -/

lemma norm_toLp_int {W : ℝ} (hW : 0 ≤ W) (J : Fin m → ℤ) :
    ‖(WithLp.toLp 2 fun l => W * (J l : ℝ) : EuclideanSpace ℝ (Fin m))‖ = W * zNorm J := by
  rw [EuclideanSpace.norm_eq, zNorm, ← Real.sqrt_sq hW, ← Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hW]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Real.norm_eq_abs, sq_abs]
  ring

lemma abs_le_zNorm (J : Fin m → ℤ) (l : Fin m) : |(J l : ℝ)| ≤ zNorm J := by
  rw [zNorm]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun l => ((J l : ℝ)) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ l)

/-! ## Slabs of the chain -/

theorem chainSlab_width (s : ℝ) (i : ℕ) : (chainSlab (m := m) s 0 i).width = s := rfl

lemma chainSlab_eq (s : ℝ) (i : ℕ) : chainSlab (m := m) s 0 i =
    ⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) (((i : ℝ) * s) • e₁), s⟩ := by
  simp [chainSlab, e1Slab]

theorem gridCube_subset_face₀ (s W : ℝ) (i : ℕ) (j : Fin m → ℤ) :
    gridCube s W 0 i j ⊆ (chainSlab s 0 i).face₀ := by
  intro x hx
  rw [chainSlab_eq, Slab.face₀, mem_image_constVAdd]
  simp only [gridCube, mem_ofPred_eq, sub_zero] at hx
  simp [hx.1]

theorem gridCube_subset_face₁ (s W : ℝ) (i : ℕ) (k : Fin m → ℤ) :
    gridCube s W 0 (i + 1) k ⊆ (chainSlab s 0 i).face₁ := by
  intro x hx
  rw [chainSlab_eq, Slab.face₁, mem_image_constVAdd]
  simp only [gridCube, mem_ofPred_eq, sub_zero, Nat.cast_add, Nat.cast_one] at hx
  simp [hx.1]
  ring

theorem gridCube_subset_set {s : ℝ} (hs : 0 ≤ s) (W : ℝ) (i : ℕ) (j : Fin m → ℤ) :
    gridCube s W 0 i j ⊆ (chainSlab s 0 i).set := by
  intro x hx
  rw [chainSlab_eq, Slab.set]
  refine mem_image_constVAdd.mpr ?_
  simp only [gridCube, mem_ofPred_eq, sub_zero] at hx
  simp [hx.1, hs]

theorem gridCube_succ_subset_set {s : ℝ} (hs : 0 ≤ s) (W : ℝ) (i : ℕ) (k : Fin m → ℤ) :
    gridCube s W 0 (i + 1) k ⊆ (chainSlab s 0 i).set := by
  intro x hx
  rw [chainSlab_eq, Slab.set]
  refine mem_image_constVAdd.mpr ?_
  simp only [gridCube, mem_ofPred_eq, sub_zero, Nat.cast_add, Nat.cast_one] at hx
  simp only [mem_ofPred_eq, Pt.lon_sub, Pt.lon_smul, Pt.lon_e₁, hx.1]
  constructor <;> nlinarith

lemma lon_bounds_of_mem_interior {s : ℝ} {i : ℕ} {x : Pt m}
    (hx : x ∈ interior (chainSlab (m := m) s 0 i).set) :
    (i : ℝ) * s < Pt.lon x ∧ Pt.lon x < ((i : ℝ) + 1) * s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have key : ∀ y : Pt m, dist y x < ε → (i : ℝ) * s ≤ Pt.lon y ∧ Pt.lon y ≤ ((i : ℝ) + 1) * s := by
    intro y hy
    have := hball (mem_ball.mpr hy)
    rw [chainSlab_eq, Slab.set, mem_image_constVAdd] at this
    simp only [mem_ofPred_eq, Pt.lon_sub, Pt.lon_smul, Pt.lon_e₁] at this
    constructor <;> nlinarith [this.1, this.2]
  have hd : ∀ r : ℝ, |r| < ε → dist (x + r • (e₁ : Pt m)) x < ε := by
    intro r hr
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have : ‖(e₁ : Pt m)‖ = 1 := by
      have h : ‖(e₁ : Pt m)‖ ^ 2 = 1 := by rw [norm_sq_eq_lon_tr]; simp
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
    rw [this, mul_one]; exact hr
  have h1 := key _ (hd (ε / 2) (by rw [abs_of_pos (by positivity)]; linarith))
  have h2 := key _ (hd (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith))
  simp only [Pt.lon_add, Pt.lon_smul, Pt.lon_e₁] at h1 h2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem disjoint_interior_chainSlab {s : ℝ} (hs : 0 < s) {i i' : ℕ} (h : i ≠ i') :
    Disjoint (interior (chainSlab (m := m) s 0 i).set) (interior (chainSlab s 0 i').set) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have a := lon_bounds_of_mem_interior hx
  have b := lon_bounds_of_mem_interior hx'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hlt
    nlinarith [a.2, b.1]
  · have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hlt
    nlinarith [a.1, b.2]

/-! ## Compactness -/

lemma lipschitz_lon : LipschitzWith 1 (Pt.lon (m := m)) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [Real.dist_eq] using Infra.Slab.abs_lon_sub_le x y

lemma lipschitz_tr_apply (l : Fin m) : LipschitzWith 1 fun x : Pt m => Pt.tr x l :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    exact abs_tr_apply_le_norm (x - y) l

theorem isCompact_gridCube (s W : ℝ) (i : ℕ) (j : Fin m → ℤ) :
    IsCompact (gridCube (m := m) s W 0 i j) := by
  have hclosed : IsClosed (gridCube (m := m) s W 0 i j) := by
    have : gridCube (m := m) s W 0 i j = {x | Pt.lon x = i * s} ∩
        ⋂ k, ({x | W * j k ≤ Pt.tr x k} ∩ {x | Pt.tr x k ≤ W * (j k + 1)}) := by
      ext x; simp [gridCube]
    rw [this]
    refine (isClosed_eq lipschitz_lon.continuous continuous_const).inter
      (isClosed_iInter fun k => ?_)
    exact (isClosed_le continuous_const (lipschitz_tr_apply k).continuous).inter
      (isClosed_le (lipschitz_tr_apply k).continuous continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  rw [isBounded_iff_subset_closedBall (0 : Pt m)]
  refine ⟨Real.sqrt ((i * s) ^ 2 + ∑ k, (|W| * (|(j k : ℝ)| + 1)) ^ 2), ?_⟩
  intro x hx
  simp only [gridCube, mem_ofPred_eq, sub_zero] at hx
  rw [mem_closedBall, dist_zero_right]
  apply Real.le_sqrt_of_sq_le
  rw [norm_sq_eq_lon_tr, hx.1, EuclideanSpace.norm_sq_eq]
  gcongr with k
  have h1 := (hx.2 k).1
  have h2 := (hx.2 k).2
  have hW : 0 ≤ W := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg hW, abs_le]
  constructor
  · nlinarith [neg_abs_le (j k : ℝ), abs_nonneg (j k : ℝ)]
  · nlinarith [le_abs_self (j k : ℝ)]

theorem gridCube_nonempty (s : ℝ) {W : ℝ} (hW : 0 ≤ W) (i : ℕ) (j : Fin m → ℤ) :
    (gridCube (m := m) s W 0 i j).Nonempty := by
  refine ⟨Pt.mk (i * s) (WithLp.toLp 2 fun k => W * j k), ?_⟩
  simp only [gridCube, mem_ofPred_eq, Pt.lon_mk, Pt.tr_mk, sub_zero]
  refine ⟨trivial, fun k => ⟨le_refl _, ?_⟩⟩
  nlinarith

/-! ## Displacements -/

/-- The longitudinal and transverse displacement between the cubes. -/
lemma displacement {s W : ℝ} (hW : 0 ≤ W) {i : ℕ} {j k : Fin m → ℤ} {u v : Pt m}
    (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k) :
    Pt.lon (v - u) = s ∧ W * zNorm (k - j) - W * Real.sqrt m ≤ ‖Pt.tr (v - u)‖ ∧
      ‖Pt.tr (v - u)‖ ≤ W * zNorm (k - j) + W * Real.sqrt m := by
  simp only [gridCube, mem_ofPred_eq, sub_zero,
    Nat.cast_add, Nat.cast_one] at hu hv
  refine ⟨by simp only [Pt.lon_sub]; rw [hu.1, hv.1]; ring, ?_⟩
  set a : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun l => W * (((k - j) l : ℤ) : ℝ) with ha
  have hna : ‖a‖ = W * zNorm (k - j) := norm_toLp_int hW _
  have he : ‖Pt.tr (v - u) - a‖ ≤ W * Real.sqrt m := by
    rw [mul_comm]
    refine norm_le_of_abs_le hW fun l => ?_
    have h1 := hu.2 l
    have h2 := hv.2 l
    simp only [Pt.tr_sub, PiLp.sub_apply, ha, Pi.sub_apply, Int.cast_sub]
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have t1 := norm_sub_norm_le (Pt.tr (v - u)) a
  have t2 := norm_sub_norm_le a (Pt.tr (v - u))
  rw [norm_sub_rev] at t2
  constructor
  · linarith
  · linarith [norm_sub_rev (Pt.tr (v - u)) a]

theorem le_dist_gridCube {s W : ℝ} (hs : 0 ≤ s) {i : ℕ} {j k : Fin m → ℤ} {u v : Pt m}
    (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k) : s ≤ dist u v := by
  simp only [gridCube, mem_ofPred_eq, sub_zero, Nat.cast_add, Nat.cast_one] at hu hv
  have h := Profiles.abs_lon_le_norm (v - u)
  rw [dist_comm, dist_eq_norm]
  simp only [Pt.lon_sub] at h
  rw [hu.1, hv.1, show ((i : ℝ) + 1) * s - i * s = s by ring, abs_of_nonneg hs] at h
  exact h

lemma dist_sq_eq {s W : ℝ} (hW : 0 ≤ W) {i : ℕ} {j k : Fin m → ℤ} {u v : Pt m}
    (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k) :
    dist u v ^ 2 = s ^ 2 + ‖Pt.tr (v - u)‖ ^ 2 := by
  rw [dist_comm, dist_eq_norm, norm_sq_eq_lon_tr, (displacement hW hu hv).1]

theorem dist_gridCube_le {s W : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) {i : ℕ} {j k : Fin m → ℤ}
    {u v : Pt m} (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k)
    (hjk : W * (zNorm (k - j) + Real.sqrt m) ≤ s) : dist u v ≤ 2 * s := by
  obtain ⟨-, -, h3⟩ := displacement hW hu hv
  have hsq := dist_sq_eq hW hu hv
  have ht : ‖Pt.tr (v - u)‖ ≤ s := by linarith
  nlinarith [norm_nonneg (Pt.tr (v - u)), dist_nonneg (x := u) (y := v)]

end IsotropicVariance.Paper.Proofs.SmallMean
