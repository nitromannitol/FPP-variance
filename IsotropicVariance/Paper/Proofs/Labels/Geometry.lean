/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Labels
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
import IsotropicVariance.Paper.Proofs.Localization.Frame
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# The geometry of the label steps

Deterministic facts behind the proofs of Lemmas `lem:labels` and `lem:residual`.

* **Core faces.** In units of `W`, the transverse coordinates of a core face
  `{in} × W(z + [√L, L − √L]^m)` relative to the corner of its block lie in `[√L, L − √L]`.
* **Euclidean estimates** for two points on hyperplanes at distance `n`: the excess of their
  distance over `n` is at most the square of the transverse displacement over `2n`, and the
  distance moves by at most `R/n` times the displacement of the endpoints when the transverse
  displacements are at most `R`.
* **Cube pairs covering the cores.** Pairs of transverse cubes of side `4W` centered on the
  `W`-grid of the two faces of the slab, admissible for small slopes; the `W`-neighborhoods of
  any two points of the two cores of a block lie in one of finitely many such pairs, indexed by
  `Fin m → Fin (L + 1)` twice; and the slab of every such pair is the slab `i` of the chain, with
  the same passage time.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper

variable {m : ℕ}

/-! ## Coordinates -/

section Coordinates

/-- The squared distance of two points of `ℝ × ℝ^m`. -/
theorem dist_sq_eq_lon_tr (x y : Pt m) :
    dist x y ^ 2 = (Pt.lon x - Pt.lon y) ^ 2 + ‖Pt.tr x - Pt.tr y‖ ^ 2 := by
  rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rfl

/-- Each transverse coordinate is `1`-Lipschitz. -/
theorem abs_tr_sub_le_dist (x y : Pt m) (k : Fin m) : |Pt.tr x k - Pt.tr y k| ≤ dist x y := by
  refine le_trans ?_ (Localization.Pt.norm_tr_sub_le_dist x y)
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (Pt.tr x - Pt.tr y) k

/-- Two points with the same first coordinate are at the distance of their transverse
coordinates. -/
theorem dist_eq_norm_tr_sub {x y : Pt m} (h : Pt.lon x = Pt.lon y) :
    dist x y = ‖Pt.tr x - Pt.tr y‖ := by
  have h2 : dist x y ^ 2 = ‖Pt.tr x - Pt.tr y‖ ^ 2 := by
    rw [dist_sq_eq_lon_tr, h, sub_self]
    ring
  exact (pow_left_inj₀ dist_nonneg (norm_nonneg _) two_ne_zero).1 h2

end Coordinates

/-! ## Core faces -/

section FaceRep

/-- The transverse coordinates relative to the corner of a block. -/
theorem tr_sub_blockCorner_apply (n W : ℝ) (i : ℕ) (z : Fin m → ℤ) (x : Pt m) (k : Fin m) :
    Pt.tr (x - blockCorner n W i z) k = Pt.tr x k - W * z k := by
  rfl

/-- The relative coordinates of a point of a core face lie in `[√L, L − √L]`. -/
theorem div_sub_mem_of_mem_coreFace {n W : ℝ} {L i : ℕ} {z : Fin m → ℤ} (hW : 0 < W)
    {x : Pt m} (hx : x ∈ coreFace n W L i z) (k : Fin m) :
    Pt.tr x k / W - z k ∈ Icc (Real.sqrt L) (L - Real.sqrt L) := by
  obtain ⟨-, hx⟩ := hx
  obtain ⟨h₁, h₂⟩ := hx k
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hW]
    linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hW]
    linarith

end FaceRep

/-! ## Euclidean estimates -/

section Euclid

/-- Two points on hyperplanes at distance `n`: `|u − v|² = n² + |y|²`. -/
theorem dist_sq_of_lon_sub {u v : Pt m} {n : ℝ} (huv : Pt.lon v - Pt.lon u = n) :
    dist u v ^ 2 = n ^ 2 + ‖Pt.tr v - Pt.tr u‖ ^ 2 := by
  rw [dist_sq_eq_lon_tr, norm_sub_rev, ← huv]
  ring

/-- Two points on hyperplanes at distance `n` are at distance at least `n`. -/
theorem le_dist_of_lon_sub {u v : Pt m} {n : ℝ} (hn : 0 ≤ n) (huv : Pt.lon v - Pt.lon u = n) :
    n ≤ dist u v := by
  refine (pow_le_pow_iff_left₀ hn dist_nonneg two_ne_zero).1 ?_
  rw [dist_sq_of_lon_sub huv]
  nlinarith [sq_nonneg ‖Pt.tr v - Pt.tr u‖]

/-- The excess of the distance of two points on hyperplanes at distance `n` over `n` is at most
the square of their transverse displacement over `2n`. -/
theorem dist_sub_le_sq_div {u v : Pt m} {n : ℝ} (hn : 0 < n) (huv : Pt.lon v - Pt.lon u = n) :
    dist u v - n ≤ ‖Pt.tr v - Pt.tr u‖ ^ 2 / (2 * n) := by
  have h := dist_sq_of_lon_sub huv
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (dist u v - n)]

/-- The distance of two points on hyperplanes at distance `n` moves by at most `R/n` times the
displacement of the endpoints when both transverse displacements are at most `R`: the gradient
of `y ↦ √(n² + |y|²)` is at most `|y|/n`. -/
theorem abs_dist_sub_dist_le {u v u' v' : Pt m} {n R : ℝ} (hn : 0 < n)
    (huv : Pt.lon v - Pt.lon u = n) (huv' : Pt.lon v' - Pt.lon u' = n)
    (hR : ‖Pt.tr v - Pt.tr u‖ ≤ R) (hR' : ‖Pt.tr v' - Pt.tr u'‖ ≤ R) :
    |dist u v - dist u' v'| ≤ R / n * (dist u u' + dist v v') := by
  have hd := dist_sq_of_lon_sub huv
  have hd' := dist_sq_of_lon_sub huv'
  have hdn := le_dist_of_lon_sub hn.le huv
  have hdn' := le_dist_of_lon_sub hn.le huv'
  set d := dist u v
  set d' := dist u' v'
  set p := ‖Pt.tr v - Pt.tr u‖
  set q := ‖Pt.tr v' - Pt.tr u'‖
  set E := dist u u' + dist v v'
  have hp : 0 ≤ p := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have he : |p - q| ≤ E := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    have : Pt.tr v - Pt.tr u - (Pt.tr v' - Pt.tr u') =
        (Pt.tr v - Pt.tr v') - (Pt.tr u - Pt.tr u') := by abel
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    linarith [Localization.Pt.norm_tr_sub_le_dist v v', Localization.Pt.norm_tr_sub_le_dist u u']
  have key : |d - d'| * (d + d') = |p - q| * (p + q) := by
    have h1 : (d - d') * (d + d') = (p - q) * (p + q) := by linear_combination hd - hd'
    have h2 := congrArg abs h1
    rwa [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ d + d'),
      abs_of_nonneg (by linarith : 0 ≤ p + q)] at h2
  have h3 : |d - d'| * (2 * n) ≤ E * (2 * R) :=
    calc |d - d'| * (2 * n) ≤ |d - d'| * (d + d') :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |p - q| * (p + q) := key
      _ ≤ E * (2 * R) :=
          mul_le_mul he (by linarith) (by linarith) ((abs_nonneg _).trans he)
  rw [div_mul_eq_mul_div, le_div_iff₀ hn]
  nlinarith [h3]

end Euclid

/-! ## Cube pairs covering the cores -/

section Cover

/-- The pair of transverse cubes of side `4W` centered at `(in, W(z + a))` and
`((i + 1)n, W(z + b))`, in the faces of the slab `[in, (i + 1)n] × ℝ^m`. -/
noncomputable def coverPair (n W : ℝ) (i : ℕ) (z a b : Fin m → ℤ) : CubePair m where
  motion := AffineIsometryEquiv.constVAdd ℝ (Pt m)
    (Pt.mk ((i : ℝ) * n) (WithLp.toLp 2 fun k => W * ((z k : ℝ) + a k)))
  dist := n
  side₁ := 4 * W
  side₂ := 4 * W
  offset := WithLp.toLp 2 fun k => W * ((b k : ℝ) - a k)

/-- The pair of cubes is admissible at slope `1/2` when `|b − a|_∞ ≤ L` and `√m L W ≤ n/2`. -/
theorem coverPair_isAdmissible {n W : ℝ} {L : ℕ} (hn : 0 < n) (hW : 0 ≤ W) (i : ℕ)
    (z : Fin m → ℤ) {a b : Fin m → ℤ} (hab : ∀ k, |b k - a k| ≤ L)
    (hslope : Real.sqrt m * L * W ≤ n / 2) :
    (coverPair n W i z a b).IsAdmissible n W (1 / 2) := by
  have h4 : (0 : ℝ) ≤ 4 * W := by linarith
  refine ⟨rfl, h4, le_rfl, h4, le_rfl, ?_⟩
  change ‖(WithLp.toLp 2 fun k => W * ((b k : ℝ) - a k) : EuclideanSpace ℝ (Fin m))‖ / n ≤ 1 / 2
  rw [div_le_iff₀ hn]
  refine le_trans ?_ (by linarith : Real.sqrt m * L * W ≤ 1 / 2 * n)
  rw [mul_assoc]
  refine Profiles.norm_le_of_abs_le (by positivity) fun k => ?_
  rw [PiLp.toLp_apply, abs_mul, abs_of_nonneg hW, mul_comm (L : ℝ) W]
  refine mul_le_mul_of_nonneg_left ?_ hW
  have h : ((|b k - a k| : ℤ) : ℝ) ≤ ((L : ℤ) : ℝ) := Int.cast_le.2 (hab k)
  rwa [Int.cast_abs, Int.cast_sub, Int.cast_natCast] at h

theorem mem_coverPair_first {n W : ℝ} {i : ℕ} {z a b : Fin m → ℤ} {y : Pt m} :
    y ∈ (coverPair n W i z a b).first ↔
      Pt.lon y = (i : ℝ) * n ∧ ∀ k, |Pt.tr y k - W * ((z k : ℝ) + a k)| ≤ 2 * W := by
  simp only [CubePair.first, coverPair, SmallMean.mem_image_constVAdd, mem_ofPred_eq, Pt.lon_sub,
    Pt.lon_mk, Pt.tr_sub, Pt.tr_mk, PiLp.sub_apply, sub_eq_zero]
  refine and_congr Iff.rfl (forall_congr' fun k => ?_)
  rw [show 4 * W / 2 = 2 * W by ring]

/-- The second cube: the points of `{(i + 1)n}` within `2W` of `W(z + b)` in each transverse
coordinate. -/
theorem mem_coverPair_second {n W : ℝ} {i : ℕ} {z a b : Fin m → ℤ} {y : Pt m} :
    y ∈ (coverPair n W i z a b).second ↔
      Pt.lon y = ((i + 1 : ℕ) : ℝ) * n ∧ ∀ k, |Pt.tr y k - W * ((z k : ℝ) + b k)| ≤ 2 * W := by
  simp only [CubePair.second, coverPair, SmallMean.mem_image_constVAdd, mem_ofPred_eq, Pt.lon_sub,
    Pt.lon_mk, Pt.tr_sub, Pt.tr_mk, PiLp.sub_apply, PiLp.toLp_apply]
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ (forall_congr' fun k => ?_)
  · push_cast
    linarith
  · push_cast at h
    linarith
  · rw [show 4 * W / 2 = 2 * W by ring,
      show Pt.tr y k - W * ((z k : ℝ) + a k) - W * ((b k : ℝ) - a k) =
        Pt.tr y k - W * ((z k : ℝ) + b k) by ring]

/-- The index, relative to the block, of the `W`-grid cell containing the transverse
coordinates of a point, clipped to `{0, …, L}`. -/
noncomputable def coverIndex (W : ℝ) (L : ℕ) (z : Fin m → ℤ) (x : Pt m) : Fin m → Fin (L + 1) :=
  fun k => ⟨min ⌊Pt.tr x k / W - z k⌋₊ L, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- For a point of a core face, the grid cell of `coverIndex` contains its transverse
coordinates. -/
theorem coverIndex_spec {n W : ℝ} {L i : ℕ} {z : Fin m → ℤ} (hW : 0 < W) {x : Pt m}
    (hx : x ∈ coreFace n W L i z) (k : Fin m) :
    0 ≤ Pt.tr x k - W * ((z k : ℝ) + (coverIndex W L z x k : ℕ)) ∧
      Pt.tr x k - W * ((z k : ℝ) + (coverIndex W L z x k : ℕ)) < W := by
  obtain ⟨ht₁, ht₂⟩ := div_sub_mem_of_mem_coreFace hW hx k
  set t := Pt.tr x k / W - z k with ht
  have hs := Real.sqrt_nonneg (L : ℝ)
  have ht0 : 0 ≤ t := hs.trans ht₁
  have hfl : ⌊t⌋₊ ≤ L := Nat.floor_le_of_le (by linarith)
  have hidx' : ((coverIndex W L z x k : ℕ)) = ⌊t⌋₊ := min_eq_left hfl
  have hidx : ((coverIndex W L z x k : ℕ) : ℝ) = (⌊t⌋₊ : ℝ) := by rw [hidx']
  have hWt : W * t = Pt.tr x k - W * z k := by
    rw [ht, mul_sub, mul_div_cancel₀ _ hW.ne']
  have h₁ : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have h₂ : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  rw [hidx]
  have e : Pt.tr x k - W * ((z k : ℝ) + (⌊t⌋₊ : ℝ)) = W * (t - ⌊t⌋₊) := by
    rw [mul_sub, hWt]
    ring
  rw [e]
  exact ⟨mul_nonneg hW.le (by linarith), by nlinarith⟩

/-- A point within `W` of a point of the hyperplane `{in}` whose grid cell is that of the center
lies in the first cube. -/
theorem mem_coverPair_first_of_dist_le {n W : ℝ} {i : ℕ} {z a b : Fin m → ℤ} {u u' : Pt m}
    (hu : ∀ k, |Pt.tr u k - W * ((z k : ℝ) + a k)| ≤ W) (hu' : Pt.lon u' = (i : ℝ) * n)
    (hd : dist u u' ≤ W) : u' ∈ (coverPair n W i z a b).first := by
  refine mem_coverPair_first.2 ⟨hu', fun k => ?_⟩
  have h₁ := hu k
  have h₂ := (abs_tr_sub_le_dist u' u k).trans ((dist_comm u' u).trans_le hd)
  calc |Pt.tr u' k - W * ((z k : ℝ) + a k)|
      = |(Pt.tr u' k - Pt.tr u k) + (Pt.tr u k - W * ((z k : ℝ) + a k))| := by ring_nf
    _ ≤ |Pt.tr u' k - Pt.tr u k| + |Pt.tr u k - W * ((z k : ℝ) + a k)| := abs_add_le _ _
    _ ≤ 2 * W := by linarith

/-- A point within `W` of a point of the hyperplane `{(i + 1)n}` whose grid cell is that of the
center lies in the second cube. -/
theorem mem_coverPair_second_of_dist_le {n W : ℝ} {i : ℕ} {z a b : Fin m → ℤ} {v v' : Pt m}
    (hv : ∀ k, |Pt.tr v k - W * ((z k : ℝ) + b k)| ≤ W)
    (hv' : Pt.lon v' = ((i + 1 : ℕ) : ℝ) * n) (hd : dist v v' ≤ W) :
    v' ∈ (coverPair n W i z a b).second := by
  refine mem_coverPair_second.2 ⟨hv', fun k => ?_⟩
  have h₁ := hv k
  have h₂ := (abs_tr_sub_le_dist v' v k).trans ((dist_comm v' v).trans_le hd)
  calc |Pt.tr v' k - W * ((z k : ℝ) + b k)|
      = |(Pt.tr v' k - Pt.tr v k) + (Pt.tr v k - W * ((z k : ℝ) + b k))| := by ring_nf
    _ ≤ |Pt.tr v' k - Pt.tr v k| + |Pt.tr v k - W * ((z k : ℝ) + b k)| := abs_add_le _ _
    _ ≤ 2 * W := by linarith

/-- The `W`-neighborhoods in the two faces of two points of the cores of the block `(i, z)`
lie in one of the pairs of cubes `coverPair n W i z a b` with `a, b ∈ {0, …, L}^m`. -/
theorem exists_coverPair {n W : ℝ} {L i : ℕ} {z : Fin m → ℤ} (hW : 0 < W) {u v : Pt m}
    (hu : u ∈ coreFace n W L i z) (hv : v ∈ coreFace n W L (i + 1) z) :
    ∃ a b : Fin m → Fin (L + 1),
      (∀ u' : Pt m, Pt.lon u' = (i : ℝ) * n → dist u u' ≤ W →
        u' ∈ (coverPair n W i z (fun k => ((a k : ℕ) : ℤ)) (fun k => ((b k : ℕ) : ℤ))).first) ∧
      (∀ v' : Pt m, Pt.lon v' = ((i + 1 : ℕ) : ℝ) * n → dist v v' ≤ W →
        v' ∈ (coverPair n W i z (fun k => ((a k : ℕ) : ℤ)) (fun k => ((b k : ℕ) : ℤ))).second) ∧
      ∀ k, |((b k : ℕ) : ℤ) - ((a k : ℕ) : ℤ)| ≤ L := by
  refine ⟨coverIndex W L z u, coverIndex W L z v, fun u' hu' hd => ?_, fun v' hv' hd => ?_,
    fun k => ?_⟩
  · refine mem_coverPair_first_of_dist_le (fun k => ?_) hu' hd
    obtain ⟨h₁, h₂⟩ := coverIndex_spec hW hu k
    push_cast
    rw [abs_le]
    constructor <;> linarith
  · refine mem_coverPair_second_of_dist_le (fun k => ?_) hv' hd
    obtain ⟨h₁, h₂⟩ := coverIndex_spec hW hv k
    push_cast
    rw [abs_le]
    constructor <;> linarith
  · have ha := (coverIndex W L z u k).isLt
    have hb := (coverIndex W L z v k).isLt
    rw [abs_le]
    constructor <;> omega

/-! ### The slab of a pair of cubes -/

/-- The slab passage time depends only on the slab as a set and on its faces. -/
theorem Slab.passTime_congr {sl sl' : Slab m} (h₁ : sl.set = sl'.set)
    (h₂ : sl.faces = sl'.faces) (b : ℝ) (σ : Pt m → ℝ) :
    sl.passTime b σ = sl'.passTime b σ := by
  have hd : sl.density b σ = sl'.density b σ := by
    funext x
    simp only [Slab.density, h₂]
  funext u v
  simp only [Slab.passTime, h₁, hd]

/-- Two slabs given by translations with the same first coordinate are the same set. -/
theorem constVAdd_slab_set_eq {p q : Pt m} (h : Pt.lon p = Pt.lon q) (w : ℝ) :
    (⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) p, w⟩ : Slab m).set =
      (⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) q, w⟩ : Slab m).set := by
  ext y
  simp only [Slab.set, SmallMean.mem_image_constVAdd, mem_ofPred_eq, Pt.lon_sub, h]

/-- Two slabs given by translations with the same first coordinate have the same faces. -/
theorem constVAdd_slab_faces_eq {p q : Pt m} (h : Pt.lon p = Pt.lon q) (w : ℝ) :
    (⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) p, w⟩ : Slab m).faces =
      (⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) q, w⟩ : Slab m).faces := by
  ext y
  simp only [Slab.faces, SmallMean.mem_image_constVAdd, mem_ofPred_eq, Pt.lon_sub, h]

private theorem lon_coverPair_motion (n W : ℝ) (i : ℕ) (z a : Fin m → ℤ) :
    Pt.lon (Pt.mk ((i : ℝ) * n) (WithLp.toLp 2 fun k => W * ((z k : ℝ) + a k)) : Pt m) =
      Pt.lon (((Pt.lon (0 : Pt m)) + (i : ℝ) * n) • (e₁ : Pt m)) := by
  simp only [Pt.lon_mk, Pt.lon_smul, Pt.lon_zero, Pt.lon_e₁, zero_add, mul_one]

/-- The slab of the pair of cubes is the slab `i` of the chain. -/
theorem coverPair_slab_set (n W : ℝ) (i : ℕ) (z a b : Fin m → ℤ) :
    (coverPair n W i z a b).slab.set = (chainSlab n 0 i).set :=
  constVAdd_slab_set_eq (lon_coverPair_motion n W i z a) n

/-- The slab of the pair of cubes has the faces of the slab `i` of the chain. -/
theorem coverPair_slab_faces (n W : ℝ) (i : ℕ) (z a b : Fin m → ℤ) :
    (coverPair n W i z a b).slab.faces = (chainSlab n 0 i).faces :=
  constVAdd_slab_faces_eq (lon_coverPair_motion n W i z a) n

/-- The slab of the pair of cubes `coverPair n W i z a b` has the passage time of the slab `i`
of the chain. -/
theorem coverPair_slab_passTime (n W : ℝ) (i : ℕ) (z a b : Fin m → ℤ) (b' : ℝ)
    (σ : Pt m → ℝ) :
    (coverPair n W i z a b).slab.passTime b' σ = (chainSlab n 0 i).passTime b' σ :=
  Slab.passTime_congr (coverPair_slab_set n W i z a b) (coverPair_slab_faces n W i z a b) b' σ

/-- The same for the slab passage times of a configuration. -/
theorem slabTime_coverPair_slab (X : Setting m) (b' n W : ℝ) (i : ℕ) (z a b : Fin m → ℤ)
    (c : X.Ω) :
    X.slabTime b' (coverPair n W i z a b).slab c = X.slabTime b' (chainSlab n 0 i) c := by
  unfold Setting.slabTime
  rw [coverPair_slab_passTime]

end Cover

end IsotropicVariance.Paper.Proofs.Labels
