/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Linarith
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry

/-!
# Deterministic geometry for the continuity estimate (Lemma `lem:modulus`)

The deterministic steps of the proof of Lemma `lem:modulus`, equation `eq:modulus`:

* a point of the hyperplane `{x₁ = p + L}` near the segment between two points of a pair of
  transverse cubes is near the line of slope `t` through the centre (`abs_offset_le`);
* transverse boxes are covered by a grid of transverse cubes (`exists_mem_gridIndices_cube`, with
  the rounding `exists_int_near`);
* a convex nonnegative function is Lipschitz on a ball where it is bounded
  (`abs_sub_le_of_convex`), the secant step of the proof.
-/

@[expose] public section

open Set
open scoped NNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-! ## Coordinates of points of `ℝ^d` -/

/-- A transverse coordinate of a point is bounded by its norm. -/
theorem abs_snd_apply_le_norm (z : Pt m) (j : Fin m) : |z.snd j| ≤ ‖z‖ := by
  have h₁ : ‖z.snd j‖ ≤ ‖z.snd‖ := PiLp.norm_apply_le z.snd j
  rw [Real.norm_eq_abs] at h₁
  exact h₁.trans (WithLp.norm_snd_le (x := z))

/-! ## Points near a segment between two transverse cubes -/

/-- Let `u ∈ transverseCube p c a` and `v ∈ transverseCube (p + ℓ) c' a'` with
`‖c' − c − ℓ t‖ ≤ e₀` and `‖t‖ ≤ T`, and let `x ∈ {x₁ = p + L}` be within `d` of a point of the
segment `[u, v]`. Then every transverse coordinate of `x` is within
`(1 + T) d + max a a' / 2 + e₀` of the line of slope `t` through the centre `c`. -/
theorem abs_offset_le {p : ℤ} {ℓ L : ℤ} {c c' t : EuclideanSpace ℝ (Fin m)} {a a' e₀ d T : ℝ}
    {u v x : Vertex m} (hu : u ∈ transverseCube p c a) (hv : v ∈ transverseCube (p + ℓ) c' a')
    (hcc : ‖c' - c - (ℓ : ℝ) • t‖ ≤ e₀) (ht : ‖t‖ ≤ T) (hx : x.1 = p + L) {y : Pt m}
    (hy : y ∈ segment ℝ (point u) (point v)) (hxy : ‖point x - y‖ ≤ d) (j : Fin m) :
    |(x.2 j : ℝ) - (c j + (L : ℝ) * t j)| ≤ (1 + T) * d + max a a' / 2 + e₀ := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hy
  have hfst := Proofs.Geometry.abs_fst_le_norm (point x - (α • point u + β • point v))
  have hsnd := abs_snd_apply_le_norm (point x - (α • point u + β • point v)) j
  simp only [WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst, WithLp.sub_snd, WithLp.add_snd,
    WithLp.smul_snd, Infra.FPP.point_fst, Infra.FPP.point_snd, smul_eq_mul, PiLp.sub_apply,
    PiLp.add_apply, PiLp.smul_apply, Infra.FPP.transversePoint_apply, hx, hu1, hv1,
    Int.cast_add] at hfst hsnd
  have hcj := (Moments.ExpArray.abs_apply_le_norm (c' - c - (ℓ : ℝ) • t) j).trans hcc
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hcj
  have htj := (Moments.ExpArray.abs_apply_le_norm t j).trans ht
  have hu' := hu2 j
  have hv' := hv2 j
  have hmax₁ : a ≤ max a a' := le_max_left _ _
  have hmax₂ : a' ≤ max a a' := le_max_right _ _
  -- the longitudinal defect `L − β ℓ`
  have hL : |(L : ℝ) - β * ℓ| ≤ d := by
    have : (p : ℝ) + L - (α * p + β * (p + ℓ)) = L - β * ℓ := by
      rw [show α = 1 - β by linarith only [hαβ]]; ring
    rw [this] at hfst; exact hfst.trans hxy
  have hLt : |((L : ℝ) - β * ℓ) * t j| ≤ T * d := by
    rw [abs_mul, mul_comm T d]
    exact mul_le_mul hL htj (abs_nonneg _) ((abs_nonneg _).trans hL)
  have hdecomp : (x.2 j : ℝ) - (c j + (L : ℝ) * t j) =
      ((x.2 j : ℝ) - (α * u.2 j + β * v.2 j)) + α * ((u.2 j : ℝ) - c j) +
        β * ((v.2 j : ℝ) - c' j) + β * (c' j - c j - ℓ * t j) - ((L : ℝ) - β * ℓ) * t j := by
    rw [show α = 1 - β by linarith only [hαβ]]; ring
  rw [hdecomp]
  have e1 : |α * ((u.2 j : ℝ) - c j)| ≤ α * (max a a' / 2) := by
    rw [abs_mul, abs_of_nonneg hα]
    exact mul_le_mul_of_nonneg_left (hu'.trans (by linarith only [hmax₁])) hα
  have e2 : |β * ((v.2 j : ℝ) - c' j)| ≤ β * (max a a' / 2) := by
    rw [abs_mul, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (hv'.trans (by linarith only [hmax₂])) hβ
  have e3 : |β * (c' j - c j - ℓ * t j)| ≤ e₀ := by
    rw [abs_mul, abs_of_nonneg hβ]
    have hb1 : β ≤ 1 := by linarith only [hα, hαβ]
    calc β * |c' j - c j - ℓ * t j| ≤ 1 * e₀ :=
          mul_le_mul hb1 hcj (abs_nonneg _) zero_le_one
      _ = e₀ := one_mul e₀
  have e4 : α * (max a a' / 2) + β * (max a a' / 2) = max a a' / 2 := by
    rw [← add_mul, hαβ, one_mul]
  have htri := abs_add_le (((x.2 j : ℝ) - (α * u.2 j + β * v.2 j)) + α * ((u.2 j : ℝ) - c j) +
        β * ((v.2 j : ℝ) - c' j) + β * (c' j - c j - ℓ * t j)) (-(((L : ℝ) - β * ℓ) * t j))
  have htri2 := abs_add_le (((x.2 j : ℝ) - (α * u.2 j + β * v.2 j)) + α * ((u.2 j : ℝ) - c j) +
        β * ((v.2 j : ℝ) - c' j)) (β * (c' j - c j - ℓ * t j))
  have htri3 := abs_add_le (((x.2 j : ℝ) - (α * u.2 j + β * v.2 j)) + α * ((u.2 j : ℝ) - c j))
        (β * ((v.2 j : ℝ) - c' j))
  have htri4 := abs_add_le ((x.2 j : ℝ) - (α * u.2 j + β * v.2 j)) (α * ((u.2 j : ℝ) - c j))
  rw [abs_neg] at htri
  rw [sub_eq_add_neg]
  linarith only [htri, htri2, htri3, htri4, e1, e2, e3, e4, hLt, hsnd, hxy]

/-! ## Covering transverse boxes by grids of transverse cubes -/

/-- Rounding to a grid of mesh `s₀`. -/
theorem exists_int_near (r : ℝ) {s₀ : ℝ} (hs : 0 < s₀) :
    ∃ k : ℤ, |r - s₀ * k| ≤ s₀ / 2 ∧ |(k : ℝ)| ≤ |r| / s₀ + 1 / 2 := by
  refine ⟨round (r / s₀), ?_, ?_⟩
  · have h := abs_sub_round (r / s₀)
    have : r - s₀ * (round (r / s₀) : ℝ) = s₀ * (r / s₀ - round (r / s₀)) := by
      field_simp
    rw [this, abs_mul, abs_of_pos hs]
    calc s₀ * |r / s₀ - round (r / s₀)| ≤ s₀ * (1 / 2) := mul_le_mul_of_nonneg_left h hs.le
      _ = s₀ / 2 := by ring
  · have h := abs_sub_round (r / s₀)
    have h2 : |(round (r / s₀) : ℝ)| ≤ |r / s₀| + |r / s₀ - round (r / s₀)| := by
      have := abs_sub_abs_le_abs_sub (round (r / s₀) : ℝ) (r / s₀)
      rw [abs_sub_comm (round (r / s₀) : ℝ)] at this
      linarith only [this]
    rw [abs_div, abs_of_pos hs] at h2
    linarith only [h2, h]

/-- The grid of indices `{-n, …, n}^m`. -/
def gridIndices (m n : ℕ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n

theorem gridIndices_nonempty (m n : ℕ) : (gridIndices m n).Nonempty :=
  ⟨0, Fintype.mem_piFinset.mpr fun _ => Finset.mem_Icc.mpr ⟨by simp, by simp⟩⟩

theorem card_gridIndices (m n : ℕ) : (gridIndices m n).card = (2 * n + 1) ^ m := by
  unfold gridIndices
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- A point of `{x₁ = q}` whose transverse coordinates are within `ρ` of `z` lies in one of the
transverse cubes of side `s₀` centred at `z + s₀ k`, `k ∈ {-n, …, n}^m`, if `ρ/s₀ + 1/2 ≤ n`. -/
theorem exists_mem_gridIndices_cube {q : ℤ} {z : EuclideanSpace ℝ (Fin m)} {ρ s₀ : ℝ}
    (hs : 0 < s₀) {n : ℕ} (hn : ρ / s₀ + 1 / 2 ≤ n) {x : Vertex m} (hx : x.1 = q)
    (hρ : ∀ j, |(x.2 j : ℝ) - z j| ≤ ρ) :
    ∃ k ∈ gridIndices m n, x ∈ transverseCube q (z + s₀ • transversePoint k) s₀ := by
  choose k hk hkn using fun j => exists_int_near ((x.2 j : ℝ) - z j) hs
  refine ⟨k, Fintype.mem_piFinset.mpr fun j => ?_, hx, fun j => ?_⟩
  · have h1 : |(k j : ℝ)| ≤ n := by
      refine (hkn j).trans ?_
      have : |(x.2 j : ℝ) - z j| / s₀ ≤ ρ / s₀ := div_le_div_of_nonneg_right (hρ j) hs.le
      linarith only [this, hn]
    have h2 : |k j| ≤ (n : ℤ) := by exact_mod_cast h1
    exact Finset.mem_Icc.mpr (abs_le.mp h2)
  · have := hk j
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Infra.FPP.transversePoint_apply]
    rwa [show (x.2 j : ℝ) - (z j + s₀ * k j) = (x.2 j : ℝ) - z j - s₀ * k j by ring]

/-- Every cube lies in each of its thickenings. -/
theorem subset_thicken (I : Set (Vertex m)) (t : EuclideanSpace ℝ (Fin m)) {r : ℝ}
    (hr : 0 ≤ r) : I ⊆ thicken I t r := fun x hx =>
  ⟨x, hx, 0, by rw [abs_zero]; exact hr, by
    rw [zero_smul, add_zero, sub_self, norm_zero]; exact Real.sqrt_nonneg _⟩

/-! ## The secant estimate for convex functions -/

/-- A nonnegative convex function bounded by `B` on the ball of radius `ρ + ‖w‖` around `y` has
`|f (y + w) − f y| ≤ ‖w‖ B / ρ` (the secant step in the proof of Lemma `lem:localization`). -/
theorem abs_sub_le_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hconv : ∀ x y : E, ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
      f ((1 - l) • x + l • y) ≤ (1 - l) * f x + l * f y)
    (hnn : ∀ x, 0 ≤ f x) {y w : E} {ρ B : ℝ} (hρ : 0 < ρ)
    (hB : ∀ z, ‖z - y‖ ≤ ρ + ‖w‖ → f z ≤ B) : |f (y + w) - f y| ≤ ‖w‖ / ρ * B := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  set s := ‖w‖ with hs_def
  have hs : 0 < s := norm_pos_iff.mpr hw
  have hB0 : 0 ≤ B := (hnn y).trans (hB y (by rw [sub_self, norm_zero]; positivity))
  set l := s / (s + ρ) with hl_def
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hρ])
  have hls : l * B ≤ s / ρ * B :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hs.le hρ (by linarith only [hs])) hB0
  -- upper bound: `y + w` lies between `y` and `y + ((s+ρ)/s) w`
  have hup : f (y + w) - f y ≤ l * B := by
    have hz : ‖(y + ((s + ρ) / s) • w) - y‖ ≤ ρ + s := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hs.ne']
      linarith only
    have hcomb : (1 - l) • y + l • (y + ((s + ρ) / s) • w) = y + w := by
      rw [smul_add, smul_smul, show l * ((s + ρ) / s) = 1 by
        rw [hl_def]; field_simp, one_smul, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
    have h := hconv y (y + ((s + ρ) / s) • w) l hl0 hl1
    rw [hcomb] at h
    have := hB _ hz
    nlinarith only [h, this, hl0, hnn y]
  -- lower bound: `y` lies between `y + w` and `y − (ρ/s) w`
  have hlow : f y - f (y + w) ≤ l * B := by
    have hz : ‖(y - (ρ / s) • w) - y‖ ≤ ρ + s := by
      rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hs.ne']
      linarith only [hs]
    have hcomb : (1 - l) • (y + w) + l • (y - (ρ / s) • w) = y := by
      have h1 : (1 - l) - l * (ρ / s) = 0 := by rw [hl_def]; field_simp; ring
      calc (1 - l) • (y + w) + l • (y - (ρ / s) • w)
          = ((1 - l) + l) • y + ((1 - l) - l * (ρ / s)) • w := by
            simp only [smul_add, smul_sub, smul_smul, add_smul, sub_smul]; abel
        _ = y := by rw [h1, zero_smul, add_zero, sub_add_cancel, one_smul]
    have h := hconv (y + w) (y - (ρ / s) • w) l hl0 hl1
    rw [hcomb] at h
    have := hB _ hz
    nlinarith only [h, this, hl0, hl1, hnn (y + w)]
  rw [abs_le]
  constructor <;> linarith only [hup, hlow, hls]

end CurvatureVariance.Paper.Localization.Modulus
