/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The geometry of the dyadic tree (the proof of Lemma `lem:tree`)

Deterministic facts behind the dyadic tree bound, equation `eq:tree`.

* Coordinates: `Pt.lon` and `Pt.tr` are linear, and a point is determined by them.
* The excess of a vector over its component along a unit vector `e` is at most the square of
  its component orthogonal to `e` divided by twice its component along `e`; the orthogonal
  component of `z − x` is at most the distance from `z` to the line `x + ℝe`.
* The cells of the dyadic subdivision of a rectangular box: the centers of the `n^d` cells of
  the subdivision of `[−R, R]` into `n` intervals in each coordinate (`grid`), and every point of
  the box lies within `R/n` of one of them in each coordinate.
-/

@[expose] public section

open Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

variable {m : ℕ}

/-! ## Coordinates -/

lemma pt_ext {x y : Pt m} (h₁ : Pt.lon x = Pt.lon y) (h₂ : Pt.tr x = Pt.tr y) : x = y := by
  have : WithLp.ofLp x = WithLp.ofLp y := Prod.ext h₁ h₂
  simpa using congrArg (WithLp.toLp 2) this

lemma norm_sq_eq_lon_tr (x : Pt m) : ‖x‖ ^ 2 = Pt.lon x ^ 2 + ‖Pt.tr x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rfl

lemma abs_lon_le_norm (x : Pt m) : |Pt.lon x| ≤ ‖x‖ := by
  have h := norm_sq_eq_lon_tr x
  apply abs_le_of_sq_le_sq' _ (norm_nonneg x) |> fun h' => abs_le.mpr h'
  nlinarith [sq_nonneg (‖Pt.tr x‖), sq_abs (Pt.lon x)]

lemma norm_tr_le_norm (x : Pt m) : ‖Pt.tr x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_lon_tr x
  nlinarith [sq_nonneg (Pt.lon x), norm_nonneg x, norm_nonneg (Pt.tr x)]

lemma abs_tr_apply_le_norm (x : Pt m) (k : Fin m) : |Pt.tr x k| ≤ ‖x‖ := by
  refine le_trans ?_ (norm_tr_le_norm x)
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le (Pt.tr x) k

/-! ## Components along a unit vector -/

/-- The component of `v` orthogonal to `e`. -/
noncomputable def perp (e v : Pt m) : Pt m := v - ⟪v, e⟫ • e

lemma perp_add (e v w : Pt m) : perp e (v + w) = perp e v + perp e w := by
  simp only [perp, inner_add_left, add_smul]
  abel

lemma perp_sub (e v w : Pt m) : perp e (v - w) = perp e v - perp e w := by
  simp only [perp, inner_sub_left, sub_smul]
  abel

lemma perp_smul (e v : Pt m) (a : ℝ) : perp e (a • v) = a • perp e v := by
  simp only [perp, inner_smul_left, smul_sub, smul_smul, RCLike.conj_to_real]

lemma perp_self {e : Pt m} (he : ‖e‖ = 1) : perp e e = 0 := by
  simp [perp, he]

lemma inner_perp {e : Pt m} (he : ‖e‖ = 1) (v : Pt m) : ⟪perp e v, e⟫ = 0 := by
  simp [perp, inner_sub_left, inner_smul_left, he]

lemma norm_sq_eq_inner_sq_add {e : Pt m} (he : ‖e‖ = 1) (v : Pt m) :
    ‖v‖ ^ 2 = ⟪v, e⟫ ^ 2 + ‖perp e v‖ ^ 2 := by
  have hv : v = ⟪v, e⟫ • e + perp e v := by simp [perp]
  have h0 : ⟪⟪v, e⟫ • e, perp e v⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_comm (perp e v) e, inner_perp he, mul_zero]
  conv_lhs => rw [hv]
  rw [norm_add_sq_real, h0, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  ring

lemma inner_le_norm {e : Pt m} (he : ‖e‖ = 1) (v : Pt m) : ⟪v, e⟫ ≤ ‖v‖ := by
  have := real_inner_le_norm v e
  rwa [he, mul_one] at this

lemma norm_perp_le_norm {e : Pt m} (he : ‖e‖ = 1) (v : Pt m) : ‖perp e v‖ ≤ ‖v‖ := by
  have h := norm_sq_eq_inner_sq_add he v
  nlinarith [sq_nonneg ⟪v, e⟫, norm_nonneg v, norm_nonneg (perp e v)]

/-- The excess of a vector over its component along `e` is at most the square of its
orthogonal component divided by twice the component along `e`. -/
lemma norm_sub_inner_le {e : Pt m} (he : ‖e‖ = 1) {v : Pt m} (ha : 0 < ⟪v, e⟫) :
    ‖v‖ - ⟪v, e⟫ ≤ ‖perp e v‖ ^ 2 / (2 * ⟪v, e⟫) := by
  have h := norm_sq_eq_inner_sq_add he v
  have hle := inner_le_norm he v
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖v‖ - ⟪v, e⟫)]

/-- The component of `z − x` orthogonal to `e` is at most the distance from `z` to the line
`x + ℝe`. -/
lemma norm_perp_le_infDist {e : Pt m} (he : ‖e‖ = 1) (x z : Pt m) :
    ‖perp e (z - x)‖ ≤ infDist z (range fun r : ℝ => x + r • e) := by
  rw [le_infDist (range_nonempty _)]
  rintro _ ⟨r, rfl⟩
  have h1 := norm_sq_eq_inner_sq_add he (z - x - r • e)
  have hp : perp e (z - x - r • e) = perp e (z - x) := by
    rw [perp_sub, perp_smul, perp_self he, smul_zero, sub_zero]
  rw [hp] at h1
  rw [dist_eq_norm, show z - (x + r • e) = z - x - r • e by abel]
  nlinarith [sq_nonneg ⟪z - x - r • e, e⟫, norm_nonneg (z - x - r • e),
    norm_nonneg (perp e (z - x))]

/-! ## Dyadic cells -/

/-- The center of the `l`-th of `n` equal intervals of `[−R, R]`. -/
noncomputable def cellCenter (n : ℕ) (R : ℝ) (l : ℕ) : ℝ := -R + (2 * l + 1) * R / n

/-- Every point of `[−R, R]` lies within `R/n` of the center of one of the `n` intervals. -/
lemma exists_cell {n : ℕ} (hn : 0 < n) {R y : ℝ} (hR : 0 ≤ R) (hy : |y| ≤ R) :
    ∃ l : Fin n, |y - cellCenter n R l| ≤ R / n := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rcases hR.eq_or_lt with h0 | hpos
  · refine ⟨⟨0, hn⟩, ?_⟩
    subst h0
    have : y = 0 := abs_nonpos_iff.mp hy
    simp [cellCenter, this]
  set u : ℝ := (y + R) * n / (2 * R) with hu
  have hu0 : 0 ≤ u := by
    have : -R ≤ y := (abs_le.mp hy).1
    rw [hu]; apply div_nonneg (mul_nonneg (by linarith) hnr.le) (by linarith)
  have hun : u ≤ n := by
    have : y ≤ R := (abs_le.mp hy).2
    rw [hu, div_le_iff₀ (by linarith)]
    nlinarith
  let l : ℕ := min ⌊u⌋₊ (n - 1)
  have hl : l < n := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn one_pos)
  refine ⟨⟨l, hl⟩, ?_⟩
  have hlu : (l : ℝ) ≤ u := by
    have := Nat.floor_le hu0
    exact (Nat.cast_le.mpr (min_le_left _ _)).trans this
  have hul : u ≤ l + 1 := by
    rcases le_total ⌊u⌋₊ (n - 1) with h | h
    · have : l = ⌊u⌋₊ := min_eq_left h
      rw [this]; exact (Nat.lt_floor_add_one u).le
    · have : l = n - 1 := min_eq_right h
      rw [this, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne'), Nat.cast_one]
      linarith
  have hy' : y = 2 * R * u / n - R := by
    rw [hu]; field_simp; ring
  have key : 2 * R * u / n - R - cellCenter n R l = R * (2 * u - 2 * l - 1) / n := by
    simp only [cellCenter]; field_simp; ring
  rw [hy', key, abs_div, abs_mul, abs_of_pos hpos, abs_of_pos hnr]
  apply div_le_div_of_nonneg_right _ hnr.le
  exact mul_le_of_le_one_right hR (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- The center of a cell of the subdivision of the box `[−r₀, r₀] × ∏ₖ [−r k, r k]` into `n`
intervals in each coordinate. -/
noncomputable def gridPt (n : ℕ) (r₀ : ℝ) (r : Fin m → ℝ) (l : Fin (m + 1) → Fin n) : Pt m :=
  Pt.mk (cellCenter n r₀ (l 0)) (WithLp.toLp 2 fun k => cellCenter n (r k) (l k.succ))

/-- The centers of the `n^d` cells. -/
noncomputable def grid (n : ℕ) (r₀ : ℝ) (r : Fin m → ℝ) : Finset (Pt m) :=
  Finset.univ.image (gridPt n r₀ r)

lemma card_grid_le (n : ℕ) (r₀ : ℝ) (r : Fin m → ℝ) : (grid n r₀ r).card ≤ n ^ (m + 1) := by
  refine (Finset.card_image_le).trans ?_
  simp

lemma exists_mem_grid {n : ℕ} (hn : 0 < n) {r₀ : ℝ} {r : Fin m → ℝ} (hr₀ : 0 ≤ r₀)
    (hr : ∀ k, 0 ≤ r k) {y : Pt m} (hy₀ : |Pt.lon y| ≤ r₀) (hy : ∀ k, |Pt.tr y k| ≤ r k) :
    ∃ c ∈ grid n r₀ r, |Pt.lon (y - c)| ≤ r₀ / n ∧ ∀ k, |Pt.tr (y - c) k| ≤ r k / n := by
  obtain ⟨l₀, hl₀⟩ := exists_cell hn hr₀ hy₀
  choose l hl using fun k => exists_cell hn (hr k) (hy k)
  refine ⟨gridPt n r₀ r (Fin.cons l₀ l), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_, ?_⟩
  · simpa [gridPt] using hl₀
  · intro k
    simpa [gridPt] using hl k

/-! ## Rectangular boxes -/

/-- The standard box `[−r₀, r₀] × ∏ₖ [−r k, r k]`. -/
def stdBox (r₀ : ℝ) (r : Fin m → ℝ) : Set (Pt m) :=
  {x | |Pt.lon x| ≤ r₀ ∧ ∀ k, |Pt.tr x k| ≤ r k}

end IsotropicVariance.Paper.Proofs.Profiles
