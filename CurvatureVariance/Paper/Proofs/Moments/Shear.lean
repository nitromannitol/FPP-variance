/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# Sheared dyadic boxes for the chaining of equation `eq:tree`

The proof of Lemma `lem:tree`: a point `a` before a transverse cube `I` (thickened along
`(1, t)`) is joined to every point `u` of `I` through the points at distance `2^{-j} r` before the
centres, along `(1, t)`, of the dyadic subcubes of generation `j` containing `u`; subdividing the
longitudinal coordinate as well gives the bound for the thickening by `r/64`. This file sets up
that geometry.

* Sheared coordinates `(τ, w)` of a vertex `u` relative to `(p, c, t)`: `τ = u₁ − p`,
  `w = u₂ − c − τ t`, inverted by `unshear` (`unshear_shear`); `unshear` is affine
  (`unshear_sub_unshear`).
* One-dimensional dyadic cells `quantIdx`, `quantCtr` (`abs_sub_quantCtr_le`, `quantIdx_mem`).
* `shearBox p c t R₁ R₂`: the finite set of vertices with `|τ| < R₁` and `|w_k| < R₂`
  (`mem_shearBox`, `card_shearBox_le`).
* `boxIdx j u`, `boxCtr j β`: the generation-`j` box of `u` (cells of sides `2R₁/2^j`, `2R₂/2^j`)
  and its centre; at most `2^{j(m+1)}` boxes meet `shearBox` (`boxIdx_mem_idxBox`, `card_idxBox`).
* `roundVertex`: the nearest lattice point (`norm_point_roundVertex_sub_le`).
* `chainPoint`: the chain points `φ j u`, the base point `a` for `j = 0` and otherwise the rounded
  point at signed distance `sg · r/2^j` along `(1, t)` from the centre of the box of `u`
  (`sg = −1` before the cube, `sg = 1` after it); `exists_chain_step`, `norm_sub_chainPoint_le`
  and `card_image_chainPoint_le` are the facts the chaining uses.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ## Norms of points -/

theorem norm_le_abs_fst_add_norm_snd (z : Pt m) : ‖z‖ ≤ |z.fst| + ‖z.snd‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 z
  rw [Real.norm_eq_abs, sq_abs] at h
  have h0 : 0 ≤ |z.fst| + ‖z.snd‖ := by positivity
  have hsq : ‖z‖ ^ 2 ≤ (|z.fst| + ‖z.snd‖) ^ 2 := by
    rw [h]; nlinarith only [sq_abs z.fst, abs_nonneg z.fst, norm_nonneg z.snd]
  exact (pow_le_pow_iff_left₀ (norm_nonneg z) h0 two_ne_zero).mp hsq

theorem norm_slopeVec_le (t : E) : ‖slopeVec t‖ ≤ 1 + ‖t‖ := by
  refine (norm_le_abs_fst_add_norm_snd _).trans ?_
  simp [slopeVec]

/-! ## Rounding to the lattice -/

/-- The lattice point nearest to `z`, coordinatewise. -/
noncomputable def roundVertex (z : Pt m) : Vertex m :=
  (round z.fst, fun k => round (z.snd k))

theorem norm_point_roundVertex_sub_le (z : Pt m) :
    ‖point (roundVertex z) - z‖ ≤ Real.sqrt ((m : ℝ) + 1) / 2 := by
  set v := point (roundVertex z) - z with hv
  have h1 : |v.fst| ≤ 1 / 2 := by
    rw [hv, WithLp.sub_fst, Infra.FPP.point_fst, abs_sub_comm]
    exact abs_sub_round _
  have h2 : ‖v.snd‖ ^ 2 ≤ m / 4 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ k, ‖v.snd k‖ ^ 2 ≤ ∑ _k : Fin m, (1 / 2 : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [Real.norm_eq_abs]
          apply pow_le_pow_left₀ (abs_nonneg _)
          rw [hv, WithLp.sub_snd, Infra.FPP.point_snd, PiLp.sub_apply,
            Infra.FPP.transversePoint_apply, abs_sub_comm]
          exact abs_sub_round _
      _ = m / 4 := by simp; ring
  have h := WithLp.prod_norm_sq_eq_of_L2 v
  rw [Real.norm_eq_abs, sq_abs] at h
  have hsq : ‖v‖ ^ 2 ≤ ((m : ℝ) + 1) / 4 := by
    nlinarith only [h, h1, h2, abs_nonneg v.fst, sq_abs v.fst]
  rw [show Real.sqrt ((m : ℝ) + 1) / 2 = Real.sqrt (((m : ℝ) + 1) / 4) by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
  exact Real.le_sqrt_of_sq_le hsq

/-! ## One-dimensional dyadic cells -/

/-- The index `⌊(x + R)/h⌋` of the cell of side `h`, cells starting at `−R`, containing `x`. -/
noncomputable def quantIdx (h R x : ℝ) : ℤ := ⌊(x + R) / h⌋

/-- The centre `−R + (i + 1/2) h` of the cell of index `i`. -/
noncomputable def quantCtr (h R : ℝ) (i : ℤ) : ℝ := -R + ((i : ℝ) + 1 / 2) * h

theorem abs_sub_quantCtr_le {h : ℝ} (hh : 0 < h) (R x : ℝ) :
    |x - quantCtr h R (quantIdx h R x)| ≤ h / 2 := by
  unfold quantCtr quantIdx
  set y := (x + R) / h with hy
  have hxy : x + R = h * y := by rw [hy]; field_simp
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  rw [abs_le]
  constructor <;> nlinarith only [hxy, h1, h2, hh]

theorem quantIdx_mem {R x : ℝ} (hR : 0 < R) (j : ℕ) (hx : |x| < R) :
    0 ≤ quantIdx (2 * R / 2 ^ j) R x ∧ quantIdx (2 * R / 2 ^ j) R x ≤ 2 ^ j - 1 := by
  unfold quantIdx
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hval : (x + R) / (2 * R / 2 ^ j) = (x + R) * 2 ^ j / (2 * R) := by
    field_simp
  rw [abs_lt] at hx
  constructor
  · apply Int.floor_nonneg.mpr
    rw [hval]; apply div_nonneg _ (by linarith only [hR])
    exact mul_nonneg (by linarith only [hx.1]) hpow.le
  · have hlt : (x + R) / (2 * R / 2 ^ j) < ((2 ^ j : ℤ) : ℝ) := by
      rw [hval, div_lt_iff₀ (by linarith only [hR])]
      push_cast
      nlinarith only [hx.2, hpow]
    have := Int.floor_lt.mpr hlt
    omega

theorem quantIdx_zero {R x : ℝ} (hR : 0 < R) (hx : |x| < R) :
    quantIdx (2 * R / 2 ^ 0) R x = 0 := by
  obtain ⟨h1, h2⟩ := quantIdx_mem hR 0 hx
  rw [show ((2 : ℤ) ^ 0 - 1) = 0 by norm_num] at h2
  omega

theorem quantCtr_zero (R : ℝ) : quantCtr (2 * R / 2 ^ 0) R 0 = 0 := by
  unfold quantCtr; simp

/-! ## Sheared coordinates -/

/-- The longitudinal sheared coordinate `τ = u₁ − p`. -/
noncomputable def shearTau (p : ℤ) (u : Vertex m) : ℝ := (u.1 : ℝ) - p

/-- The transverse sheared coordinate `w = u₂ − c − τ t`. -/
noncomputable def shearW (p : ℤ) (c t : E) (u : Vertex m) : E :=
  transversePoint u.2 - c - shearTau p u • t

/-- The point with sheared coordinates `(τ, w)`: `(p + τ, c + w + τ t)`. -/
noncomputable def unshear (p : ℤ) (c t : E) (τ : ℝ) (w : E) : Pt m :=
  WithLp.toLp 2 ((p : ℝ) + τ, c + w + τ • t)

theorem unshear_shear (p : ℤ) (c t : E) (u : Vertex m) :
    unshear p c t (shearTau p u) (shearW p c t u) = point u := by
  apply Infra.FPP.pt_ext
  · simp [unshear, shearTau]
  · simp only [unshear, shearW, Infra.FPP.point_snd]
    change c + (transversePoint u.2 - c - shearTau p u • t) + shearTau p u • t = _
    abel

theorem unshear_sub_unshear (p : ℤ) (c t : E) (τ τ' : ℝ) (w w' : E) :
    unshear p c t τ' w' - unshear p c t τ w =
      (τ' - τ) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), w' - w) := by
  apply Infra.FPP.pt_ext
  · simp only [WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst, unshear, slopeVec]
    change (p : ℝ) + τ' - (p + τ) = (τ' - τ) * 1 + 0
    ring
  · simp only [WithLp.sub_snd, WithLp.add_snd, WithLp.smul_snd, unshear, slopeVec]
    change c + w' + τ' • t - (c + w + τ • t) = (τ' - τ) • t + (w' - w)
    rw [sub_smul]; abel

/-! ## Boxes -/

open Classical in
/-- The vertices with sheared coordinates `|τ| < R₁` and `|w_k| < R₂`, as a finite set. -/
noncomputable def shearBox (p : ℤ) (c t : E) (R₁ R₂ : ℝ) : Finset (Vertex m) :=
  ((Finset.Icc (p - ⌈R₁⌉) (p + ⌈R₁⌉)) ×ˢ (Fintype.piFinset fun k =>
      Finset.Icc ⌊c k - R₁ * ‖t‖ - R₂⌋ ⌈c k + R₁ * ‖t‖ + R₂⌉)).filter
    (fun u => |shearTau p u| < R₁ ∧ ∀ k, |shearW p c t u k| < R₂)

theorem mem_shearBox {p : ℤ} {c t : E} {R₁ R₂ : ℝ} {u : Vertex m} :
    u ∈ shearBox p c t R₁ R₂ ↔ |shearTau p u| < R₁ ∧ ∀ k, |shearW p c t u k| < R₂ := by
  classical
  unfold shearBox
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨hτ, hw⟩ := h
  rw [Finset.mem_product, Finset.mem_Icc, Fintype.mem_piFinset]
  have hR₁ : R₁ ≤ ⌈R₁⌉ := Int.le_ceil R₁
  have hτ' := abs_lt.mp hτ
  unfold shearTau at hτ'
  refine ⟨⟨?_, ?_⟩, fun k => ?_⟩
  · have : ((p - ⌈R₁⌉ : ℤ) : ℝ) ≤ u.1 := by push_cast; linarith only [hτ'.1, hR₁]
    exact_mod_cast this
  · have : (u.1 : ℝ) ≤ ((p + ⌈R₁⌉ : ℤ) : ℝ) := by push_cast; linarith only [hτ'.2, hR₁]
    exact_mod_cast this
  · rw [Finset.mem_Icc]
    have hk := abs_lt.mp (hw k)
    have hτt : |shearTau p u * t k| ≤ R₁ * ‖t‖ := by
      rw [abs_mul]
      have hR₁0 : 0 ≤ R₁ := (abs_nonneg _).trans hτ.le
      exact mul_le_mul hτ.le (ExpArray.abs_apply_le_norm t k) (abs_nonneg _) hR₁0
    have hu : (u.2 k : ℝ) = c k + shearTau p u * t k + shearW p c t u k := by
      simp only [shearW, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        Infra.FPP.transversePoint_apply]
      ring
    have hτt' := abs_le.mp hτt
    constructor
    · have : (⌊c k - R₁ * ‖t‖ - R₂⌋ : ℝ) ≤ u.2 k :=
        (Int.floor_le _).trans (by rw [hu]; linarith only [hτt'.1, hk.1])
      exact_mod_cast this
    · have : (u.2 k : ℝ) ≤ ⌈c k + R₁ * ‖t‖ + R₂⌉ :=
        le_trans (by rw [hu]; linarith only [hτt'.2, hk.2]) (Int.le_ceil _)
      exact_mod_cast this

theorem card_shearBox_le (p : ℤ) (c t : E) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    ((shearBox p c t R₁ R₂).card : ℝ) ≤ (2 * R₁ + 3) * (2 * R₁ * ‖t‖ + 2 * R₂ + 3) ^ m := by
  classical
  unfold shearBox
  have hcardInt : ∀ a b : ℤ, ((Finset.Icc a b).card : ℝ) ≤ max ((b : ℝ) + 1 - a) 0 := by
    intro a b
    rw [Int.card_Icc]
    rcases le_or_gt 0 (b + 1 - a) with h | h
    · rw [show ((b + 1 - a).toNat : ℝ) = ((b + 1 - a : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg h]
      push_cast; exact le_max_left _ _
    · rw [Int.toNat_of_nonpos h.le]; simp
  calc ((Finset.filter _ _).card : ℝ) ≤ (((Finset.Icc (p - ⌈R₁⌉) (p + ⌈R₁⌉)) ×ˢ
        (Fintype.piFinset fun k => Finset.Icc ⌊c k - R₁ * ‖t‖ - R₂⌋ ⌈c k + R₁ * ‖t‖ + R₂⌉)).card :
          ℝ) := by exact_mod_cast Finset.card_filter_le _ _
    _ = ((Finset.Icc (p - ⌈R₁⌉) (p + ⌈R₁⌉)).card : ℝ) *
          ∏ k, ((Finset.Icc ⌊c k - R₁ * ‖t‖ - R₂⌋ ⌈c k + R₁ * ‖t‖ + R₂⌉).card : ℝ) := by
        rw [Finset.card_product, Fintype.card_piFinset]; push_cast; rfl
    _ ≤ (2 * R₁ + 3) * ∏ _k : Fin m, (2 * R₁ * ‖t‖ + 2 * R₂ + 3) := by
        apply mul_le_mul _ _ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
          (by linarith only [hR₁])
        · refine (hcardInt _ _).trans (max_le ?_ (by linarith only [hR₁]))
          have := Int.ceil_lt_add_one R₁
          push_cast; linarith only [this]
        · refine Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun k _ => ?_
          refine (hcardInt _ _).trans (max_le ?_ (by positivity))
          have h1 := Int.ceil_lt_add_one (c k + R₁ * ‖t‖ + R₂)
          have h2 := Int.sub_one_lt_floor (c k - R₁ * ‖t‖ - R₂)
          linarith only [h1, h2]
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The generation-`j` box of `u`: the cell indices of its sheared coordinates for cells of sides
`2R₁/2^j` and `2R₂/2^j`. -/
noncomputable def boxIdx (p : ℤ) (c t : E) (R₁ R₂ : ℝ) (j : ℕ) (u : Vertex m) :
    ℤ × (Fin m → ℤ) :=
  (quantIdx (2 * R₁ / 2 ^ j) R₁ (shearTau p u),
    fun k => quantIdx (2 * R₂ / 2 ^ j) R₂ (shearW p c t u k))

/-- The centre of the generation-`j` box of index `β`, as a point of `ℝ^d`. -/
noncomputable def boxCtr (p : ℤ) (c t : E) (R₁ R₂ : ℝ) (j : ℕ) (β : ℤ × (Fin m → ℤ)) : Pt m :=
  unshear p c t (quantCtr (2 * R₁ / 2 ^ j) R₁ β.1)
    (WithLp.toLp 2 fun k => quantCtr (2 * R₂ / 2 ^ j) R₂ (β.2 k))

/-- The indices of the generation-`j` boxes inside `shearBox`. -/
def idxBox (m j : ℕ) : Finset (ℤ × (Fin m → ℤ)) :=
  Finset.Icc 0 (2 ^ j - 1) ×ˢ Fintype.piFinset fun _ => Finset.Icc 0 (2 ^ j - 1)

theorem card_idxBox (j : ℕ) : (idxBox m j).card = 2 ^ (j * (m + 1)) := by
  unfold idxBox
  rw [Finset.card_product, Fintype.card_piFinset, Int.card_Icc]
  simp only [sub_add_cancel, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ((2 : ℤ) ^ j).toNat = 2 ^ j by
    rw [show ((2 : ℤ) ^ j) = ((2 ^ j : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]]
  rw [← pow_succ', ← pow_mul, mul_comm]

theorem boxIdx_mem_idxBox {p : ℤ} {c t : E} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (j : ℕ)
    {u : Vertex m} (hu : u ∈ shearBox p c t R₁ R₂) : boxIdx p c t R₁ R₂ j u ∈ idxBox m j := by
  rw [mem_shearBox] at hu
  unfold idxBox boxIdx
  rw [Finset.mem_product, Finset.mem_Icc, Fintype.mem_piFinset]
  exact ⟨quantIdx_mem hR₁ j hu.1, fun k => Finset.mem_Icc.mpr (quantIdx_mem hR₂ j (hu.2 k))⟩

/-- The centre of the generation-zero box of every point of `shearBox` is `(p, c)`. -/
theorem boxCtr_zero {p : ℤ} {c t : E} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) {u : Vertex m}
    (hu : u ∈ shearBox p c t R₁ R₂) :
    boxCtr p c t R₁ R₂ 0 (boxIdx p c t R₁ R₂ 0 u) = WithLp.toLp 2 ((p : ℝ), c) := by
  rw [mem_shearBox] at hu
  unfold boxCtr boxIdx
  simp only [quantIdx_zero hR₁ hu.1, quantIdx_zero hR₂ (hu.2 _), quantCtr_zero]
  apply Infra.FPP.pt_ext
  · simp [unshear]
  · simp only [unshear]
    change c + WithLp.toLp 2 (fun _ => (0 : ℝ)) + (0 : ℝ) • t = c
    have h0 : (WithLp.toLp 2 (fun _ : Fin m => (0 : ℝ)) : E) = 0 := by ext; simp
    rw [zero_smul, add_zero, h0, add_zero]

/-- The sheared coordinates of a point of `shearBox` differ from those of its box centre by at
most half the cell sides, so the point is within `(R₁/2^j)|(1,t)| + √m R₂/2^j` of the centre. -/
theorem norm_point_sub_boxCtr_le {p : ℤ} {c t : E} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (j : ℕ) (u : Vertex m) :
    ‖point u - boxCtr p c t R₁ R₂ j (boxIdx p c t R₁ R₂ j u)‖ ≤
      R₁ / 2 ^ j * ‖slopeVec t‖ + Real.sqrt m * (R₂ / 2 ^ j) := by
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  rw [← unshear_shear p c t u]
  unfold boxCtr boxIdx
  rw [unshear_sub_unshear]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have := abs_sub_quantCtr_le (h := 2 * R₁ / 2 ^ j) (by positivity) R₁ (shearTau p u)
    rw [show 2 * R₁ / 2 ^ j / 2 = R₁ / 2 ^ j by ring] at this
    exact this
  · rw [WithLp.norm_toLp_snd]
    apply Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (by positivity)
    intro k
    rw [PiLp.sub_apply]
    have := abs_sub_quantCtr_le (h := 2 * R₂ / 2 ^ j) (by positivity) R₂ (shearW p c t u k)
    rw [show 2 * R₂ / 2 ^ j / 2 = R₂ / 2 ^ j by ring] at this
    exact this

/-- Consecutive box centres: the generation-`(j+1)` centre minus the generation-`j` centre is
`δτ (1, t) + (0, δw)` with `|δτ| ≤ (3/2) R₁/2^j` and `|δw_k| ≤ (3/2) R₂/2^j`. -/
theorem exists_boxCtr_succ_sub {p : ℤ} {c t : E} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (j : ℕ) (u : Vertex m) :
    ∃ (δτ : ℝ) (δw : E), |δτ| ≤ 3 / 2 * (R₁ / 2 ^ j) ∧ (∀ k, |δw k| ≤ 3 / 2 * (R₂ / 2 ^ j)) ∧
      boxCtr p c t R₁ R₂ (j + 1) (boxIdx p c t R₁ R₂ (j + 1) u) -
        boxCtr p c t R₁ R₂ j (boxIdx p c t R₁ R₂ j u) =
        δτ • slopeVec t + WithLp.toLp 2 ((0 : ℝ), δw) := by
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  unfold boxCtr boxIdx
  rw [unshear_sub_unshear]
  refine ⟨_, _, ?_, fun k => ?_, rfl⟩
  · have h1 := abs_sub_quantCtr_le (h := 2 * R₁ / 2 ^ (j + 1)) (by positivity) R₁ (shearTau p u)
    have h2 := abs_sub_quantCtr_le (h := 2 * R₁ / 2 ^ j) (by positivity) R₁ (shearTau p u)
    rw [pow_succ] at h1
    have e1 : 2 * R₁ / (2 ^ j * 2) / 2 = R₁ / 2 ^ j / 2 := by ring
    have e2 : 2 * R₁ / 2 ^ j / 2 = R₁ / 2 ^ j := by ring
    rw [e1] at h1; rw [e2] at h2
    rw [pow_succ]
    have := abs_sub_le (quantCtr (2 * R₁ / (2 ^ j * 2)) R₁
      (quantIdx (2 * R₁ / (2 ^ j * 2)) R₁ (shearTau p u))) (shearTau p u)
      (quantCtr (2 * R₁ / 2 ^ j) R₁ (quantIdx (2 * R₁ / 2 ^ j) R₁ (shearTau p u)))
    rw [abs_sub_comm (quantCtr _ _ _) (shearTau p u)] at this
    linarith only [this, h1, h2]
  · rw [PiLp.sub_apply]
    have h1 := abs_sub_quantCtr_le (h := 2 * R₂ / 2 ^ (j + 1)) (by positivity) R₂ (shearW p c t u k)
    have h2 := abs_sub_quantCtr_le (h := 2 * R₂ / 2 ^ j) (by positivity) R₂ (shearW p c t u k)
    rw [pow_succ] at h1
    have e1 : 2 * R₂ / (2 ^ j * 2) / 2 = R₂ / 2 ^ j / 2 := by ring
    have e2 : 2 * R₂ / 2 ^ j / 2 = R₂ / 2 ^ j := by ring
    rw [e1] at h1; rw [e2] at h2
    rw [pow_succ]
    have := abs_sub_le (quantCtr (2 * R₂ / (2 ^ j * 2)) R₂
      (quantIdx (2 * R₂ / (2 ^ j * 2)) R₂ (shearW p c t u k))) (shearW p c t u k)
      (quantCtr (2 * R₂ / 2 ^ j) R₂ (quantIdx (2 * R₂ / 2 ^ j) R₂ (shearW p c t u k)))
    rw [abs_sub_comm (quantCtr _ _ _) (shearW p c t u k)] at this
    linarith only [this, h1, h2]

/-! ## Chain points -/

/-- The chain point of generation `j` for the box of index `β`: the base point `a` for `j = 0`, and
otherwise the lattice point nearest to the box centre moved by `sg · r/2^j` along `(1, t)`. -/
noncomputable def chainPt (p : ℤ) (c t : E) (R₁ R₂ r sg : ℝ) (a : Vertex m) (j : ℕ)
    (β : ℤ × (Fin m → ℤ)) : Vertex m :=
  if j = 0 then a else roundVertex (boxCtr p c t R₁ R₂ j β + (sg * r / 2 ^ j) • slopeVec t)

/-- The chain points `φ j u` of equation `eq:tree`: `chainPt` at the generation-`j` box of `u`. -/
noncomputable def chainPoint (p : ℤ) (c t : E) (R₁ R₂ r sg : ℝ) (a : Vertex m) (j : ℕ)
    (u : Vertex m) : Vertex m :=
  chainPt p c t R₁ R₂ r sg a j (boxIdx p c t R₁ R₂ j u)

theorem chainPoint_zero (p : ℤ) (c t : E) (R₁ R₂ r sg : ℝ) (a u : Vertex m) :
    chainPoint p c t R₁ R₂ r sg a 0 u = a := by
  simp [chainPoint, chainPt]

/-- Each chain point is within `√d` of its real position, given that the base point `a` is within
`√d` of `(p, c) + sg · r (1, t)`. -/
theorem norm_chainPoint_sub_le {p : ℤ} {c t : E} {R₁ R₂ r sg : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    {a : Vertex m}
    (ha : ‖point a - (WithLp.toLp 2 ((p : ℝ), c) + (sg * r) • slopeVec t)‖ ≤
      Real.sqrt ((m : ℝ) + 1)) (j : ℕ) {u : Vertex m} (hu : u ∈ shearBox p c t R₁ R₂) :
    ‖point (chainPoint p c t R₁ R₂ r sg a j u) -
        (boxCtr p c t R₁ R₂ j (boxIdx p c t R₁ R₂ j u) + (sg * r / 2 ^ j) • slopeVec t)‖ ≤
      Real.sqrt ((m : ℝ) + 1) := by
  unfold chainPoint chainPt
  split_ifs with hj
  · subst hj
    rw [boxCtr_zero hR₁ hR₂ hu, pow_zero, div_one]
    exact ha
  · exact (norm_point_roundVertex_sub_le _).trans (by
      linarith only [Real.sqrt_nonneg ((m : ℝ) + 1)])

/-- **One chain step.** The displacement between consecutive chain points is
`(δτ − sg r/2^{j+1}) (1, t) + (0, δw)` up to `2√d`, with `|δτ| ≤ (3/2) R₁/2^j` and
`|δw_k| ≤ (3/2) R₂/2^j`. -/
theorem exists_chain_step {p : ℤ} {c t : E} {R₁ R₂ r sg : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    {a : Vertex m}
    (ha : ‖point a - (WithLp.toLp 2 ((p : ℝ), c) + (sg * r) • slopeVec t)‖ ≤
      Real.sqrt ((m : ℝ) + 1)) (j : ℕ) {u : Vertex m} (hu : u ∈ shearBox p c t R₁ R₂) :
    ∃ (δτ : ℝ) (δw : E), |δτ| ≤ 3 / 2 * (R₁ / 2 ^ j) ∧ (∀ k, |δw k| ≤ 3 / 2 * (R₂ / 2 ^ j)) ∧
      ‖(point (chainPoint p c t R₁ R₂ r sg a (j + 1) u) -
          point (chainPoint p c t R₁ R₂ r sg a j u)) -
        ((δτ - sg * r / 2 ^ (j + 1)) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), δw))‖ ≤
        2 * Real.sqrt ((m : ℝ) + 1) := by
  obtain ⟨δτ, δw, hτ, hw, heq⟩ := exists_boxCtr_succ_sub (p := p) (c := c) (t := t) hR₁ hR₂ j u
  refine ⟨δτ, δw, hτ, hw, ?_⟩
  have h1 := norm_chainPoint_sub_le hR₁ hR₂ ha (j + 1) hu
  have h0 := norm_chainPoint_sub_le hR₁ hR₂ ha j hu
  have ha0 : sg * r / 2 ^ j = sg * r / 2 ^ (j + 1) + sg * r / 2 ^ (j + 1) := by
    rw [pow_succ]; field_simp; ring
  have hb : boxCtr p c t R₁ R₂ (j + 1) (boxIdx p c t R₁ R₂ (j + 1) u) =
      δτ • slopeVec t + WithLp.toLp 2 ((0 : ℝ), δw) +
        boxCtr p c t R₁ R₂ j (boxIdx p c t R₁ R₂ j u) :=
    sub_eq_iff_eq_add.mp heq
  have hdecomp : (point (chainPoint p c t R₁ R₂ r sg a (j + 1) u) -
          point (chainPoint p c t R₁ R₂ r sg a j u)) -
        ((δτ - sg * r / 2 ^ (j + 1)) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), δw)) =
      (point (chainPoint p c t R₁ R₂ r sg a (j + 1) u) -
          (boxCtr p c t R₁ R₂ (j + 1) (boxIdx p c t R₁ R₂ (j + 1) u) +
            (sg * r / 2 ^ (j + 1)) • slopeVec t)) -
        (point (chainPoint p c t R₁ R₂ r sg a j u) -
          (boxCtr p c t R₁ R₂ j (boxIdx p c t R₁ R₂ j u) + (sg * r / 2 ^ j) • slopeVec t)) := by
    rw [hb, ha0, sub_smul, add_smul]
    abel
  rw [hdecomp]
  refine (norm_sub_le _ _).trans ?_
  linarith only [h0, h1]

/-- The last chain point is within `(R₁/2^J)|(1,t)| + √m R₂/2^J + (r/2^J)|(1,t)| + √d` of `u`
(for `|sg| ≤ 1`). -/
theorem norm_sub_chainPoint_le {p : ℤ} {c t : E} {R₁ R₂ r sg : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hr : 0 ≤ r) (hsg : |sg| ≤ 1) {a : Vertex m}
    (ha : ‖point a - (WithLp.toLp 2 ((p : ℝ), c) + (sg * r) • slopeVec t)‖ ≤
      Real.sqrt ((m : ℝ) + 1)) (J : ℕ) {u : Vertex m} (hu : u ∈ shearBox p c t R₁ R₂) :
    ‖point u - point (chainPoint p c t R₁ R₂ r sg a J u)‖ ≤
      R₁ / 2 ^ J * ‖slopeVec t‖ + Real.sqrt m * (R₂ / 2 ^ J) + r / 2 ^ J * ‖slopeVec t‖ +
        Real.sqrt ((m : ℝ) + 1) := by
  have h1 := norm_point_sub_boxCtr_le (p := p) (c := c) (t := t) hR₁ hR₂ J u
  have h2 := norm_chainPoint_sub_le hR₁ hR₂ ha J hu
  have hpow : (0 : ℝ) < 2 ^ J := by positivity
  have h3 : ‖(sg * r / 2 ^ J) • slopeVec t‖ ≤ r / 2 ^ J * ‖slopeVec t‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hpow, abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ hpow.le
    nlinarith only [hsg, hr, abs_nonneg sg]
  have hdecomp : point u - point (chainPoint p c t R₁ R₂ r sg a J u) =
      (point u - boxCtr p c t R₁ R₂ J (boxIdx p c t R₁ R₂ J u)) -
        (sg * r / 2 ^ J) • slopeVec t -
        (point (chainPoint p c t R₁ R₂ r sg a J u) -
          (boxCtr p c t R₁ R₂ J (boxIdx p c t R₁ R₂ J u) + (sg * r / 2 ^ J) • slopeVec t)) := by
    abel
  rw [hdecomp]
  have e1 := norm_sub_le (point u - boxCtr p c t R₁ R₂ J (boxIdx p c t R₁ R₂ J u) -
      (sg * r / 2 ^ J) • slopeVec t)
    (point (chainPoint p c t R₁ R₂ r sg a J u) -
      (boxCtr p c t R₁ R₂ J (boxIdx p c t R₁ R₂ J u) + (sg * r / 2 ^ J) • slopeVec t))
  have e2 := norm_sub_le (point u - boxCtr p c t R₁ R₂ J (boxIdx p c t R₁ R₂ J u))
    ((sg * r / 2 ^ J) • slopeVec t)
  linarith only [h1, h2, h3, e1, e2]

/-- At most `2^{j(m+1)} · 2^{(j+1)(m+1)}` distinct links of generation `j` occur. -/
theorem card_image_chainPoint_le (p : ℤ) (c t : E) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (r sg : ℝ) (a : Vertex m) (j : ℕ) :
    ((shearBox p c t R₁ R₂).image fun u =>
        (chainPoint p c t R₁ R₂ r sg a j u, chainPoint p c t R₁ R₂ r sg a (j + 1) u)).card ≤
      2 ^ (j * (m + 1)) * 2 ^ ((j + 1) * (m + 1)) := by
  classical
  have hsub : ((shearBox p c t R₁ R₂).image fun u =>
        (chainPoint p c t R₁ R₂ r sg a j u, chainPoint p c t R₁ R₂ r sg a (j + 1) u)) ⊆
      (idxBox m j ×ˢ idxBox m (j + 1)).image fun β =>
        (chainPt p c t R₁ R₂ r sg a j β.1, chainPt p c t R₁ R₂ r sg a (j + 1) β.2) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(boxIdx p c t R₁ R₂ j u, boxIdx p c t R₁ R₂ (j + 1) u),
      Finset.mem_product.mpr ⟨boxIdx_mem_idxBox hR₁ hR₂ j hu, boxIdx_mem_idxBox hR₁ hR₂ (j + 1) hu⟩,
      rfl⟩
  calc _ ≤ ((idxBox m j ×ˢ idxBox m (j + 1)).image fun β =>
        (chainPt p c t R₁ R₂ r sg a j β.1, chainPt p c t R₁ R₂ r sg a (j + 1) β.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (idxBox m j ×ˢ idxBox m (j + 1)).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product, card_idxBox, card_idxBox]

end CurvatureVariance.Paper.Moments
