/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Slopes and angles in `ℝ^d`

Geometric facts about the directions `(1, t) = slopeVec t` used by the cone bounds, equation
`eq:cone`, of Lemma `lem:cone` and its proof:

* a vector with nonzero longitudinal coordinate `s` is `s (1, τ)` for its slope `τ`;
* `(1, t)` has norm at least one;
* a vector at angle at most `θ ≤ 1/(2(1 + T))` (`aperture T`) from `(1, t)`, with `‖t‖ ≤ T`, has
  positive longitudinal coordinate and slope within `2(1 + T)² θ` (`slopeFactor T · θ`) of `t`
  (`fst_pos_and_norm_slope_sub_le`). The bound `T` is a fixed-data constant: in use
  `T = ‖t₀‖ + 1`, which bounds the slopes within `1` of the slope `t₀` of the direction.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper InnerProductGeometry

variable {m : ℕ}

/-- The longitudinal coordinate is bounded by the norm. -/
theorem abs_fst_le_norm (w : Pt m) : |w.fst| ≤ ‖w‖ := by
  simpa [Real.norm_eq_abs] using WithLp.norm_fst_le (x := w)

/-- The transverse coordinate is bounded by the norm. -/
theorem norm_snd_le_norm (w : Pt m) : ‖w.snd‖ ≤ ‖w‖ :=
  WithLp.norm_snd_le (x := w)

@[simp] theorem slopeVec_fst (t : EuclideanSpace ℝ (Fin m)) : (slopeVec t).fst = 1 := rfl

@[simp] theorem slopeVec_snd (t : EuclideanSpace ℝ (Fin m)) : (slopeVec t).snd = t := rfl

/-- The direction `(1, t)` has norm at least one. -/
theorem one_le_norm_slopeVec (t : EuclideanSpace ℝ (Fin m)) : 1 ≤ ‖slopeVec t‖ := by
  simpa using abs_fst_le_norm (slopeVec t)

theorem slopeVec_ne_zero (t : EuclideanSpace ℝ (Fin m)) : slopeVec t ≠ 0 := by
  intro h
  have := one_le_norm_slopeVec t
  rw [h, norm_zero] at this
  linarith

/-- The squared norm of `(1, t)` is `1 + ‖t‖²`. -/
theorem norm_slopeVec_sq (t : EuclideanSpace ℝ (Fin m)) : ‖slopeVec t‖ ^ 2 = 1 + ‖t‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

/-- A vector with nonzero longitudinal coordinate `s` is `s • (1, τ)` for its slope
`τ = s⁻¹ y`. -/
theorem eq_smul_slopeVec (w : Pt m) (hw : w.fst ≠ 0) :
    w = w.fst • slopeVec (w.fst⁻¹ • w.snd) := by
  apply WithLp.ofLp_injective
  ext
  · simp [slopeVec, hw]
  · simp [slopeVec, smul_smul, hw]

/-- The direction `(1, t)` is at angle zero from its positive multiples. -/
theorem angle_smul_slopeVec_self {ℓ : ℝ} (hℓ : 0 < ℓ) (t : EuclideanSpace ℝ (Fin m)) :
    angle (ℓ • slopeVec t) (slopeVec t) = 0 := by
  rw [angle_smul_left_of_pos _ _ hℓ, angle_self (slopeVec_ne_zero t)]

/-- The aperture `1/(2(1 + T))` of the cones around the directions `(1, t)` with `‖t‖ ≤ T`. -/
noncomputable def aperture (T : ℝ) : ℝ := 1 / (2 * (1 + T))

/-- The slope factor `2(1 + T)²`: within the aperture, the slope moves by at most this multiple of
the angle (`fst_pos_and_norm_slope_sub_le`). -/
noncomputable def slopeFactor (T : ℝ) : ℝ := 2 * (1 + T) ^ 2

theorem aperture_pos {T : ℝ} (hT : 0 ≤ T) : 0 < aperture T := by
  unfold aperture; positivity

theorem two_le_slopeFactor {T : ℝ} (hT : 0 ≤ T) : 2 ≤ slopeFactor T := by
  unfold slopeFactor; nlinarith

theorem slopeFactor_pos {T : ℝ} (hT : 0 ≤ T) : 0 < slopeFactor T :=
  lt_of_lt_of_le two_pos (two_le_slopeFactor hT)

/-- The slope factor is monotone: a bound `T ≤ T'` on the slopes gives `slopeFactor T ≤
slopeFactor T'`. -/
theorem slopeFactor_le_slopeFactor {T T' : ℝ} (hT : 0 ≤ T) (h : T ≤ T') :
    slopeFactor T ≤ slopeFactor T' := by
  unfold slopeFactor
  have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + T) (by linarith : 1 + T ≤ 1 + T') 2
  linarith

/-- `(1, t)` has norm at most `1 + T` when `‖t‖ ≤ T`. -/
theorem norm_slopeVec_le {t : EuclideanSpace ℝ (Fin m)} {T : ℝ} (ht : ‖t‖ ≤ T) :
    ‖slopeVec t‖ ≤ 1 + T := by
  have h := norm_slopeVec_sq t
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith : (0 : ℝ) ≤ 1 + T) two_ne_zero).1 ?_
  rw [h]
  nlinarith [norm_nonneg t]

/-- **Slope from angle.** A vector at angle at most `θ ≤ 1/(2(1 + T))` from `(1, t)`, with
`‖t‖ ≤ T`, has positive longitudinal coordinate and slope within `2(1 + T)² θ` of `t`. -/
theorem fst_pos_and_norm_slope_sub_le {w : Pt m} {t : EuclideanSpace ℝ (Fin m)} {T θ : ℝ}
    (ht : ‖t‖ ≤ T) (hθ : θ ≤ aperture T) (hw : angle w (slopeVec t) ≤ θ) :
    0 < w.fst ∧ ‖w.fst⁻¹ • w.snd - t‖ ≤ slopeFactor T * θ := by
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  have hT1 : (0 : ℝ) < 1 + T := by linarith
  have hθ0 : 0 ≤ θ := (angle_nonneg _ _).trans hw
  have hθap : θ * (2 * (1 + T)) ≤ 1 := by
    unfold aperture at hθ
    rw [le_div_iff₀ (by positivity)] at hθ
    linarith
  have hπ := Real.pi_gt_three
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [angle_zero_left] at hw
    nlinarith
  set a := slopeVec t with ha
  have ha1 : 1 ≤ ‖a‖ := one_le_norm_slopeVec t
  have haT : ‖a‖ ≤ 1 + T := norm_slopeVec_le ht
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have han : 0 < ‖a‖ := by linarith
  set u : Pt m := ‖w‖⁻¹ • w with hu
  set e : Pt m := ‖a‖⁻¹ • a with he
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ han.ne']
  have hang : angle u e = angle w a := by
    rw [hu, he, angle_smul_left_of_pos _ _ (inv_pos.2 hwn),
      angle_smul_right_of_pos _ _ (inv_pos.2 han)]
  have hcos := cos_angle_mul_norm_mul_norm u e
  rw [hun, hen, hang] at hcos
  have hcos2 := Real.one_sub_sq_div_two_le_cos (x := angle w a)
  have hsq : ‖u - e‖ ^ 2 ≤ θ ^ 2 := by
    rw [norm_sub_sq_real, hun, hen, ← hcos]
    have h0 := angle_nonneg w a
    nlinarith
  have hue : ‖u - e‖ ≤ θ := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg (u - e)]
  have hefst : e.fst = ‖a‖⁻¹ := by simp [he, ha]
  have hesnd : e.snd = ‖a‖⁻¹ • t := by simp [he, ha]
  have hinv : (1 + T)⁻¹ ≤ ‖a‖⁻¹ := inv_anti₀ han haT
  have hdf : |u.fst - e.fst| ≤ θ := by
    have := abs_fst_le_norm (u - e)
    have h2 : (u - e).fst = u.fst - e.fst := rfl
    rw [h2] at this
    linarith
  -- `u₁ ≥ 1/(1 + T) − θ ≥ 1/(2(1 + T))`
  have hufst : (2 * (1 + T))⁻¹ ≤ u.fst := by
    have h1 := (abs_le.1 hdf).1
    have hθ' : θ ≤ (2 * (1 + T))⁻¹ := by unfold aperture at hθ; rwa [one_div] at hθ
    have h2 : (2 * (1 + T))⁻¹ + θ ≤ (1 + T)⁻¹ := by
      have e : (1 + T)⁻¹ = 2 * (2 * (1 + T))⁻¹ := by field_simp
      rw [e]; linarith
    linarith
  have hwf : w.fst = ‖w‖ * u.fst := by
    rw [hu]
    change w.fst = ‖w‖ * (‖w‖⁻¹ * w.fst)
    rw [mul_inv_cancel_left₀ hwn.ne']
  have hws : w.snd = ‖w‖ • u.snd := by
    rw [hu]
    change w.snd = ‖w‖ • ‖w‖⁻¹ • w.snd
    rw [smul_inv_smul₀ hwn.ne']
  have hupos : 0 < u.fst := lt_of_lt_of_le (by positivity) hufst
  refine ⟨by rw [hwf]; positivity, ?_⟩
  have hsl : w.fst⁻¹ • w.snd = u.fst⁻¹ • u.snd := by
    rw [hwf, hws, smul_smul]
    congr 1
    field_simp
  have hdiff : u.snd - u.fst • t = (u - e).snd - (u - e).fst • t := by
    have h2 : (u - e).fst = u.fst - e.fst := rfl
    have h3 : (u - e).snd = u.snd - e.snd := rfl
    rw [h2, h3, hesnd, hefst, sub_smul]
    abel
  have hn : ‖u.snd - u.fst • t‖ ≤ (1 + T) * θ := by
    rw [hdiff]
    calc _ ≤ ‖(u - e).snd‖ + ‖(u - e).fst • t‖ := norm_sub_le _ _
      _ ≤ ‖u - e‖ + ‖u - e‖ * T := by
        gcongr
        · exact norm_snd_le_norm _
        · rw [norm_smul, Real.norm_eq_abs]
          have := abs_fst_le_norm (u - e)
          gcongr
      _ ≤ (1 + T) * θ := by nlinarith [norm_nonneg (u - e)]
  have hcalc : u.fst⁻¹ • u.snd - t = u.fst⁻¹ • (u.snd - u.fst • t) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hupos.ne', one_smul]
  rw [hsl, hcalc, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hupos]
  have hinvu : u.fst⁻¹ ≤ 2 * (1 + T) := by
    rw [inv_le_comm₀ hupos (by positivity)]; exact hufst
  calc u.fst⁻¹ * ‖u.snd - u.fst • t‖ ≤ (2 * (1 + T)) * ((1 + T) * θ) :=
        mul_le_mul hinvu hn (norm_nonneg _) (by positivity)
    _ = slopeFactor T * θ := by unfold slopeFactor; ring

end CurvatureVariance.Paper.Proofs.Geometry
