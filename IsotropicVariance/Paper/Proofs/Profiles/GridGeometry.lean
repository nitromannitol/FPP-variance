/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.ProfilesSlab
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry
import IsotropicVariance.Paper.Proofs.SmallMean.ChainSum

/-!
# The deterministic geometry of the proof of Lemma `lem:rowenergy`

The cubes `I_i(j) = {is} × W(j + [0,1]^m)` of equation `eq:cubes` (with `τ = 0`) and the indices
`J_i` of the minimizing points.

* `gridPair s W i j k`: the pair of transverse cubes `I_i(j)` and `I_{i+1}(k)`
  (`gridPair_first`, `gridPair_second`); it is admissible with slope at most `1/2` when
  `W|k − j| ≤ s/2` (`gridPair_isAdmissible_half`), and its slab is the chain slab
  `[is, (i+1)s] × ℝ^m` (`gridPair_slab_set`, `gridPair_slab_faces`, `slabTime_gridPair`).
* The curvature lower bound `|v − u| ≥ s + W²(|k − j|²/2 − m)/(3s)` for `u ∈ I_i(j)`,
  `v ∈ I_{i+1}(k)` (`dist_gridCube_ge`).
* The indices of the minimizer: `J_0 = 0`, `W|J_{i+1} − J_i| ≤ s/2` and
  `|J_i| ≤ Ms/(4W) + 1` coordinatewise (`J_zero`, `J_step`, `abs_J_le`).
-/

@[expose] public section

open Set Metric

namespace IsotropicVariance.Paper.Proofs.Profiles

open Infra.Slab

variable {m : ℕ}

/-! ## Integer vectors -/

lemma zNorm_sub_sq (k j : Fin m → ℤ) : zNorm (k - j) ^ 2 = ∑ l, ((k l : ℝ) - j l) ^ 2 := by
  rw [SmallMean.zNorm_sq]
  simp

lemma zNorm_nonneg (k : Fin m → ℤ) : 0 ≤ zNorm k := Real.sqrt_nonneg _

/-- `|⌊a⌋ − ⌊b⌋| ≤ |a − b| + 1`. -/
lemma abs_floor_sub_floor_le (a b : ℝ) : |((⌊a⌋ : ℤ) : ℝ) - ⌊b⌋| ≤ |a - b| + 1 := by
  have ha := Int.floor_le a
  have ha' := Int.lt_floor_add_one a
  have hb := Int.floor_le b
  have hb' := Int.lt_floor_add_one b
  rw [abs_le]
  constructor
  · have := neg_abs_le (a - b)
    linarith
  · have := le_abs_self (a - b)
    linarith

/-- `|⌊a⌋| ≤ |a| + 1`. -/
lemma abs_floor_le (a : ℝ) : |((⌊a⌋ : ℤ) : ℝ)| ≤ |a| + 1 := by
  simpa using abs_floor_sub_floor_le a 0

/-- `x² ≤ 2 y² + 2` for reals at distance at most one. -/
lemma sq_le_two_mul_sq_add_two {x y : ℝ} (h₁ : -1 ≤ x - y) (h₂ : x - y ≤ 1) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 := by
  nlinarith only [sq_nonneg (2 * y - x), mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂)]

/-- The difference of two floors is within one of the difference of the reals. -/
lemma floor_sub_floor_close (a b : ℝ) :
    -1 ≤ (b - a) - ((⌊b⌋ : ℝ) - ⌊a⌋) ∧ (b - a) - ((⌊b⌋ : ℝ) - ⌊a⌋) ≤ 1 := by
  have h₁ := Int.floor_le a
  have h₂ := Int.lt_floor_add_one a
  have h₃ := Int.floor_le b
  have h₄ := Int.lt_floor_add_one b
  constructor <;> linarith only [h₁, h₂, h₃, h₄]

/-! ## The pair of cubes of equation `eq:cubes` -/

/-- The pair of transverse cubes `(I_i(j), I_{i+1}(k))` of equation `eq:cubes`, with `τ = 0`. -/
noncomputable def gridPair (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) : CubePair m :=
  ⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) (gridCubeCenter s W 0 i j), s, W, W,
    WithLp.toLp 2 fun l => W * ((k l : ℝ) - j l)⟩

lemma norm_offset_gridPair {s W : ℝ} (hW : 0 ≤ W) (i : ℕ) (j k : Fin m → ℤ) :
    ‖(gridPair s W i j k).offset‖ = W * zNorm (k - j) := by
  have h : ‖(gridPair s W i j k).offset‖ ^ 2 = (W * zNorm (k - j)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, zNorm_sub_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [gridPair]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hW (zNorm_nonneg _)) two_ne_zero).mp h

/-- The pair is admissible with slope at most `1/2` when `W|k − j| ≤ s/2`. -/
lemma gridPair_isAdmissible_half {s W : ℝ} (hs : 0 < s) (hW : 0 ≤ W) {i : ℕ} {j k : Fin m → ℤ}
    (h : W * zNorm (k - j) ≤ s / 2) : (gridPair s W i j k).IsAdmissible s W (1 / 2) := by
  refine ⟨rfl, hW, (by change W ≤ 4 * W; linarith), hW, (by change W ≤ 4 * W; linarith), ?_⟩
  change ‖(gridPair s W i j k).offset‖ / s ≤ 1 / 2
  rw [norm_offset_gridPair hW, div_le_iff₀ hs]
  linarith

lemma gridPair_isAdmissible {s W : ℝ} (hs : 0 < s) (hW : 0 ≤ W) {i : ℕ} {j k : Fin m → ℤ}
    (h : W * zNorm (k - j) ≤ s / 2) : (gridPair s W i j k).IsAdmissible s W 1 :=
  have H := gridPair_isAdmissible_half hs hW h
  ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.trans (by norm_num)⟩

lemma lon_gridCubeCenter (s W : ℝ) (i : ℕ) (j : Fin m → ℤ) :
    Pt.lon (gridCubeCenter s W (0 : Pt m) i j) = i * s := by
  simp [gridCubeCenter]

lemma tr_gridCubeCenter_apply (s W : ℝ) (i : ℕ) (j : Fin m → ℤ) (l : Fin m) :
    Pt.tr (gridCubeCenter s W (0 : Pt m) i j) l = W * ((j l : ℝ) + 1 / 2) := by
  simp [gridCubeCenter]

lemma gridPair_first (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) :
    (gridPair s W i j k).first = gridCube s W 0 i j := by
  ext x
  have h : (gridPair s W i j k).motion = AffineIsometryEquiv.constVAdd ℝ (Pt m)
      (gridCubeCenter s W 0 i j) := rfl
  rw [CubePair.first, h, SmallMean.mem_image_constVAdd]
  simp only [gridPair, Pt.lon_sub, Pt.tr_sub, lon_gridCubeCenter, PiLp.sub_apply,
    tr_gridCubeCenter_apply, gridCube, mem_ofPred_eq, sub_zero]
  refine and_congr (by constructor <;> intro h <;> linarith only [h]) (forall_congr' fun l => ?_)
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]

lemma gridPair_second (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) :
    (gridPair s W i j k).second = gridCube s W 0 (i + 1) k := by
  ext x
  have h : (gridPair s W i j k).motion = AffineIsometryEquiv.constVAdd ℝ (Pt m)
      (gridCubeCenter s W 0 i j) := rfl
  rw [CubePair.second, h, SmallMean.mem_image_constVAdd]
  simp only [gridPair, Pt.lon_sub, Pt.tr_sub, lon_gridCubeCenter, PiLp.sub_apply,
    tr_gridCubeCenter_apply, gridCube, mem_ofPred_eq, sub_zero, Nat.cast_add, Nat.cast_one]
  refine and_congr (by constructor <;> intro h <;> linarith only [h]) (forall_congr' fun l => ?_)
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]
  · rintro ⟨h1, h2⟩; constructor <;> linarith only [h1, h2]

lemma gridCube_subset_first (s W : ℝ) (_hW : 0 ≤ W) (i : ℕ) (j k : Fin m → ℤ) :
    gridCube s W 0 i j ⊆ (gridPair s W i j k).first :=
  (gridPair_first s W i j k).symm.subset

lemma gridCube_subset_second (s W : ℝ) (_hW : 0 ≤ W) (i : ℕ) (j k : Fin m → ℤ) :
    gridCube s W 0 (i + 1) k ⊆ (gridPair s W i j k).second :=
  (gridPair_second s W i j k).symm.subset

lemma slabCoord_gridPair (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) (x : Pt m) :
    slabCoord (gridPair s W i j k).slab x = slabCoord (chainSlab s 0 i) x := by
  change slabCoord ⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) (gridCubeCenter s W 0 i j), s⟩ x =
    slabCoord ⟨AffineIsometryEquiv.constVAdd ℝ (Pt m) ((Pt.lon (0 : Pt m) + i * s) • e₁), s⟩ x
  rw [SmallMean.slabCoord_constVAdd, SmallMean.slabCoord_constVAdd]
  simp [gridCubeCenter]

/-- The slab of the pair is the chain slab `[is, (i+1)s] × ℝ^m` (same set and faces). -/
lemma gridPair_slab_set (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) :
    (gridPair s W i j k).slab.set = (chainSlab s 0 i).set := by
  ext x
  rw [mem_slab_set_iff, mem_slab_set_iff, slabCoord_gridPair]
  rfl

lemma gridPair_slab_faces (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) :
    (gridPair s W i j k).slab.faces = (chainSlab s 0 i).faces := by
  ext x
  rw [mem_slab_faces_iff, mem_slab_faces_iff, slabCoord_gridPair]
  rfl

lemma gridPair_slab_density (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) (b : ℝ) (σ : Pt m → ℝ) :
    (gridPair s W i j k).slab.density b σ = (chainSlab s 0 i).density b σ := by
  funext x
  simp only [Slab.density, gridPair_slab_faces]

lemma slabTime_gridPair (X : Setting m) (b s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) :
    X.slabTime b (gridPair s W i j k).slab = X.slabTime b (chainSlab s 0 i) := by
  funext ω u v
  simp only [Setting.slabTime, Slab.passTime, gridPair_slab_set, gridPair_slab_density]

/-! ## The curvature lower bound -/

private lemma sixteen_mul_sq_le {s W : ℝ} (hW : 0 ≤ W) (hWm : 4 * Real.sqrt m * W ≤ s) :
    16 * m * W ^ 2 ≤ s ^ 2 := by
  have := pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hW) hWm 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at this
  linarith only [this]

/-- `√(s² + a) ≥ s + a/(3s)` for `0 ≤ a ≤ s²`. -/
lemma add_div_le_sqrt {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (has : a ≤ s ^ 2) :
    s + a / (3 * s) ≤ Real.sqrt (s ^ 2 + a) := by
  set q := a / (3 * s) with hq_def
  have hq : a = 3 * s * q := by rw [hq_def]; field_simp
  have hq0 : 0 ≤ q := by positivity
  have hsq0 : 0 ≤ s * q := mul_nonneg hs.le hq0
  have hqs : q ≤ s := le_of_mul_le_mul_left (by linarith only [hsq0, hq, has] : s * q ≤ s * s) hs
  rw [Real.le_sqrt (by positivity) (by positivity)]
  linarith only [hq, mul_le_mul_of_nonneg_right hqs hq0]

/-- **The curvature lower bound of the proof of Lemma `lem:rowenergy`**: `|v − u| ≥ s + W²(|k−j|²/2
− m)/(3s)` for `u ∈ I_i(j)`, `v ∈ I_{i+1}(k)`. -/
lemma dist_gridCube_ge {s W : ℝ} (hs : 0 < s) (hW : 0 ≤ W) (hWm : 4 * Real.sqrt m * W ≤ s)
    {i : ℕ} {j k : Fin m → ℤ} (h : W * zNorm (k - j) ≤ s / 2) {u v : Pt m}
    (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k) :
    s + W ^ 2 * (zNorm (k - j) ^ 2 / 2 - m) / (3 * s) ≤ dist u v := by
  have hu1 : Pt.lon u = i * s := by simpa using hu.1
  have hv1 : Pt.lon v = ((i : ℝ) + 1) * s := by
    have := hv.1
    simp only [sub_zero] at this
    rw [this]
    push_cast
    ring
  set w := Pt.tr (v - u) with hw_def
  have hlon : Pt.lon (v - u) = s := by
    rw [Pt.lon_sub, hu1, hv1]
    ring
  have hnorm : ‖v - u‖ ^ 2 = s ^ 2 + ‖w‖ ^ 2 := by rw [norm_sq_eq_lon_tr, hlon]
  have hw2 : ‖w‖ ^ 2 = ∑ l, w l ^ 2 := EuclideanSpace.real_norm_sq_eq w
  -- Each coordinate of `w` is within `W` of `W (k_l − j_l)`.
  have he (l : Fin m) : (w l - W * ((k l : ℝ) - j l)) ^ 2 ≤ W ^ 2 := by
    have h1 := hu.2 l
    have h2 := hv.2 l
    simp only [sub_zero] at h1 h2
    have hwl : w l = Pt.tr v l - Pt.tr u l := by simp [hw_def]
    rw [hwl]
    exact sq_le_sq' (by linarith only [h1.1, h1.2, h2.1, h2.2])
      (by linarith only [h1.1, h1.2, h2.1, h2.2])
  have hlow (l : Fin m) : W ^ 2 * (((k l : ℝ) - j l) ^ 2 / 2 - 1) ≤ w l ^ 2 := by
    linarith only [he l, sq_nonneg (W * ((k l : ℝ) - j l) + 2 * (w l - W * ((k l : ℝ) - j l)))]
  have hup (l : Fin m) : w l ^ 2 ≤ 2 * W ^ 2 * ((k l : ℝ) - j l) ^ 2 + 2 * W ^ 2 := by
    linarith only [he l, sq_nonneg (W * ((k l : ℝ) - j l) - (w l - W * ((k l : ℝ) - j l)))]
  have hz := zNorm_sub_sq k j
  have hL : W ^ 2 * (zNorm (k - j) ^ 2 / 2 - m) ≤ ‖w‖ ^ 2 := by
    rw [hw2, hz]
    calc W ^ 2 * ((∑ l, ((k l : ℝ) - j l) ^ 2) / 2 - m)
        = ∑ l : Fin m, W ^ 2 * (((k l : ℝ) - j l) ^ 2 / 2 - 1) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      _ ≤ ∑ l, w l ^ 2 := Finset.sum_le_sum fun l _ => hlow l
  have hU : ‖w‖ ^ 2 ≤ s ^ 2 := by
    have hsum : ‖w‖ ^ 2 ≤ 2 * (W * zNorm (k - j)) ^ 2 + 2 * m * W ^ 2 := by
      rw [hw2, mul_pow, hz]
      calc ∑ l, w l ^ 2 ≤ ∑ l : Fin m, (2 * W ^ 2 * ((k l : ℝ) - j l) ^ 2 + 2 * W ^ 2) :=
            Finset.sum_le_sum fun l _ => hup l
        _ = 2 * (W ^ 2 * ∑ l, ((k l : ℝ) - j l) ^ 2) + 2 * m * W ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have h1 : (W * zNorm (k - j)) ^ 2 ≤ (s / 2) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hW (zNorm_nonneg _)) h 2
    linarith only [hsum, h1, sixteen_mul_sq_le hW hWm, sq_nonneg s]
  have ha0 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  rw [dist_comm, dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (v - u)), hnorm]
  calc s + W ^ 2 * (zNorm (k - j) ^ 2 / 2 - m) / (3 * s) ≤ s + ‖w‖ ^ 2 / (3 * s) :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hL (mul_nonneg (by norm_num) hs.le))
    _ ≤ Real.sqrt (s ^ 2 + ‖w‖ ^ 2) := add_div_le_sqrt hs ha0 hU

/-! ## The indices of the minimizer -/

section Indices

variable (X : Setting m)

omit X in
/-- The square of a move along `e₁` is the sum over the transverse coordinates. -/
lemma norm_sub_sub_smul_sq {x y : Pt m} {s : ℝ} (hlon : Pt.lon y - Pt.lon x = s) :
    ‖y - x - s • (e₁ : Pt m)‖ ^ 2 = ∑ l, (Pt.tr y l - Pt.tr x l) ^ 2 := by
  rw [norm_sq_eq_lon_tr, EuclideanSpace.real_norm_sq_eq]
  simp [hlon]

/-- Consecutive minimizing points are at distance `s` along `e₁`. -/
lemma lon_lexMinimizer_succ_sub {b : ℝ} {M : ℕ} {s : ℝ} (hs : 0 ≤ s) (ω : X.Ω) (i : Fin M) :
    Pt.lon (lexMinimizer b (X.ρ ω) M s 0 i.succ) -
      Pt.lon (lexMinimizer b (X.ρ ω) M s 0 i.castSucc) = s := by
  have hx := (Paper.isLexLeastMinimizer_lexMinimizer b (X.isValidChain ω hs) M 0).1
  have h₁ := hx.2.2.1 i.succ
  have h₂ := hx.2.2.1 i.castSucc
  simp only [sub_zero, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h₁ h₂
  rw [h₁, h₂]
  ring

lemma J_apply {b : ℝ} {M : ℕ} {s W : ℝ} (hW : 0 < W) (ω : X.Ω) (i : Fin (M + 1)) (l : Fin m) :
    X.J b M s W 0 ω i l = ⌊Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i) l / W⌋ := by
  change (if 0 < W then ⌊Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i - 0) l / W⌋ else 0) = _
  simp only [hW, ↓reduceIte, sub_zero]

/-- `J_0 = 0`: the first minimizing point is the origin. -/
lemma J_zero (b : ℝ) (M : ℕ) {s : ℝ} (hs : 0 ≤ s) (W : ℝ) (ω : X.Ω) : X.J b M s W 0 ω 0 = 0 := by
  funext l
  by_cases hW : 0 < W
  · rw [J_apply X hW]
    have h0 := (Paper.isLexLeastMinimizer_lexMinimizer b (X.isValidChain ω hs) M 0).1.1
    rw [h0]
    simp
  · change (if 0 < W then _ else 0) = (0 : Fin m → ℤ) l
    simp only [hW, ↓reduceIte]
    rfl

/-- The transverse displacement of consecutive minimizing points is at most `s/4`. -/
lemma abs_tr_lexMinimizer_succ_sub_le {b : ℝ} {M : ℕ} {s : ℝ} (hs : 0 ≤ s) (ω : X.Ω)
    (i : Fin M) (l : Fin m) :
    |Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i.succ) l -
      Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i.castSucc) l| ≤ s / 4 := by
  set x := lexMinimizer b (X.ρ ω) M s 0
  have hx := (Paper.isLexLeastMinimizer_lexMinimizer b (X.isValidChain ω hs) M 0).1.2.2.2 i
  have heq : Pt.tr (x i.succ) l - Pt.tr (x i.castSucc) l =
      Pt.tr (x i.succ - x i.castSucc - s • e₁) l := by simp
  rw [heq]
  exact (abs_tr_apply_le_norm _ l).trans hx

lemma norm_tr_lexMinimizer_succ_sub_le {b : ℝ} {M : ℕ} {s : ℝ} (hs : 0 ≤ s) (ω : X.Ω)
    (i : Fin M) :
    ‖Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i.succ) -
      Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i.castSucc)‖ ≤ s / 4 := by
  set x := lexMinimizer b (X.ρ ω) M s 0
  have hx := (Paper.isLexLeastMinimizer_lexMinimizer b (X.isValidChain ω hs) M 0).1.2.2.2 i
  have heq : Pt.tr (x i.succ) - Pt.tr (x i.castSucc) = Pt.tr (x i.succ - x i.castSucc - s • e₁) := by
    simp
  rw [heq]
  exact (norm_tr_le_norm _).trans hx

/-- Consecutive indices of the minimizer: `W|J_{i+1} − J_i| ≤ s/2`. -/
lemma J_step {b : ℝ} (_hb : X.IsUpperBound b) {M : ℕ} {s W : ℝ} (hs : 0 < s) (hW : 0 < W)
    (hWm : 4 * Real.sqrt m * W ≤ s) (ω : X.Ω) (i : Fin M) :
    W * zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ≤ s / 2 := by
  set x := lexMinimizer b (X.ρ ω) M s 0
  set d := Pt.tr (x i.succ) - Pt.tr (x i.castSucc)
  have hd : ‖d‖ ≤ s / 4 := norm_tr_lexMinimizer_succ_sub_le X hs.le ω i
  have hcoord (l : Fin m) : (W * ((X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) l : ℝ)) ^ 2
      ≤ 2 * d l ^ 2 + 2 * W ^ 2 := by
    have hfl := abs_floor_sub_floor_le (Pt.tr (x i.succ) l / W) (Pt.tr (x i.castSucc) l / W)
    rw [← sub_div, abs_div, abs_of_pos hW] at hfl
    have hdl : d l = Pt.tr (x i.succ) l - Pt.tr (x i.castSucc) l := by simp [d]
    have hJ : ((X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) l : ℝ) =
        ((⌊Pt.tr (x i.succ) l / W⌋ : ℤ) : ℝ) - ⌊Pt.tr (x i.castSucc) l / W⌋ := by
      simp only [Pi.sub_apply, Int.cast_sub, J_apply X hW]
      rfl
    rw [hJ, ← hdl] at *
    have h1 : |W * (((⌊Pt.tr (x i.succ) l / W⌋ : ℤ) : ℝ) - ⌊Pt.tr (x i.castSucc) l / W⌋)| ≤
        |d l| + W := by
      rw [abs_mul, abs_of_pos hW]
      have := mul_le_mul_of_nonneg_left hfl hW.le
      rw [mul_add, mul_one, mul_div_cancel₀ _ hW.ne'] at this
      exact this
    have h2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    linarith only [h2, sq_abs (d l), sq_nonneg (|d l| - W)]
  have hsq : (W * zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc)) ^ 2 ≤
      (s / 2) ^ 2 := by
    rw [mul_pow, SmallMean.zNorm_sq, Finset.mul_sum]
    have hd2 : ‖d‖ ^ 2 = ∑ l, d l ^ 2 := EuclideanSpace.real_norm_sq_eq d
    have hmW := sixteen_mul_sq_le hW.le hWm
    have hd2' : ‖d‖ ^ 2 ≤ (s / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    calc ∑ l, W ^ 2 * (((X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) l : ℤ) : ℝ) ^ 2
        ≤ ∑ l : Fin m, (2 * d l ^ 2 + 2 * W ^ 2) :=
          Finset.sum_le_sum fun l _ => by rw [← mul_pow]; exact hcoord l
      _ = 2 * ‖d‖ ^ 2 + 2 * m * W ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hd2]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ (s / 2) ^ 2 := by linarith only [hd2', hmW]
  exact (pow_le_pow_iff_left₀ (mul_nonneg hW.le (zNorm_nonneg _)) (half_pos hs).le
    two_ne_zero).mp hsq

/-- The minimizing points stay within `i s/4` of the axis, coordinatewise. -/
lemma abs_tr_lexMinimizer_le {b : ℝ} {M : ℕ} {s : ℝ} (hs : 0 ≤ s) (ω : X.Ω)
    (i : Fin (M + 1)) (l : Fin m) :
    |Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i) l| ≤ (i : ℕ) * (s / 4) := by
  induction i using Fin.induction with
  | zero =>
    have h0 := (Paper.isLexLeastMinimizer_lexMinimizer b (X.isValidChain ω hs) M 0).1.1
    rw [h0]
    simp
  | succ i ih =>
    have hstep := abs_tr_lexMinimizer_succ_sub_le X (b := b) hs ω i l
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
    have := abs_sub_abs_le_abs_sub (Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i.succ) l)
      (Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i.castSucc) l)
    linarith

/-- The indices of the minimizer are bounded: `|J_i| ≤ M s/(4W) + 1` coordinatewise. -/
lemma abs_J_le {b : ℝ} (_hb : X.IsUpperBound b) {M : ℕ} {s W : ℝ} (hs : 0 < s) (hW : 0 < W)
    (ω : X.Ω) (i : Fin (M + 1)) (l : Fin m) :
    |(X.J b M s W 0 ω i l : ℝ)| ≤ M * s / (4 * W) + 1 := by
  rw [J_apply X hW]
  refine (abs_floor_le _).trans ?_
  have h := abs_tr_lexMinimizer_le X (b := b) hs.le ω i l
  have hi : ((i : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp i.2
  have h' : |Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i) l| ≤ M * (s / 4) :=
    h.trans (mul_le_mul_of_nonneg_right hi (by positivity))
  rw [abs_div, abs_of_pos hW]
  have : |Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i) l| / W ≤ M * s / (4 * W) := by
    rw [div_le_div_iff₀ hW (by positivity)]
    linarith only [mul_le_mul_of_nonneg_right h' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hW.le)]
  exact add_le_add this le_rfl

end Indices

end IsotropicVariance.Paper.Proofs.Profiles
