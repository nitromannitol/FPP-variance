/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.Curves
public import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import IsotropicVariance.Infra.Measurability.SlabTime

/-!
# The frame of a pair of cubes

After a rigid motion `g` placing `0` and `r e₁` at the centers of the two cubes, a point `x` has
the coordinates `g⁻¹ x = (t, y)` (the first paragraph of the proof of Lemma `lem:localization`).
This file holds the coordinate facts in that frame, and two bounds on the distance from a point to a
segment (`infDist_segment_le`, `infDist_centerSegment_le`).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Localization

variable {m : ℕ}

/-- The passage time `passageTime σ` is at most the cost of any curve. -/
lemma passageTime_le_cost {σ : Pt m → ℝ} {B : ℝ} (hB : ∀ x, σ x ≤ B)
    (γ : RectifiableCurve (Pt m)) :
    passageTime σ (γ.toFun 0) (γ.toFun 1) ≤
      (γ.cost (fun x => ENNReal.ofReal (σ x))).toReal :=
  ENNReal.toReal_mono (cost_ne_top hB γ) <|
    (iInf_le _ γ).trans <| (iInf_le _ rfl).trans <| iInf_le _ rfl

lemma Pt.lon_tr_norm_le (x : Pt m) : ‖x‖ ≤ |Pt.lon x| + ‖Pt.tr x‖ := by
  have h := Profiles.norm_sq_eq_lon_tr x
  have h1 : ‖x‖ ^ 2 ≤ (|Pt.lon x| + ‖Pt.tr x‖) ^ 2 := by
    rw [h, add_sq, sq_abs]
    nlinarith [abs_nonneg (Pt.lon x), norm_nonneg (Pt.tr x)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

@[simp] lemma Pt.tr_smul_e₁ (c : ℝ) : Pt.tr (c • (e₁ : Pt m)) = 0 := by simp [Pt.tr, e₁]

lemma Pt.norm_eq_tr_of_lon_eq {x y : Pt m} (h : Pt.lon x = Pt.lon y) :
    ‖x - y‖ = ‖Pt.tr x - Pt.tr y‖ := by
  have := Profiles.norm_sq_eq_lon_tr (x - y)
  rw [Pt.lon_sub, h, sub_self, Pt.tr_sub] at this
  have h2 : ‖x - y‖ ^ 2 = ‖Pt.tr x - Pt.tr y‖ ^ 2 := by rw [this]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

lemma Pt.norm_tr_sub_le_dist (x y : Pt m) : ‖Pt.tr x - Pt.tr y‖ ≤ dist x y := by
  rw [dist_eq_norm, ← Pt.tr_sub]; exact Profiles.norm_tr_le_norm _

/-- Moving the endpoints of a segment moves the distance to it by at most their displacements. -/
lemma infDist_segment_le (x u v u' v' : Pt m) :
    infDist x (segment ℝ u v) ≤ infDist x (segment ℝ u' v') + (dist u u' + dist v v') := by
  have hne : (segment ℝ u' v').Nonempty := ⟨u', left_mem_segment ℝ u' v'⟩
  suffices h : infDist x (segment ℝ u v) - (dist u u' + dist v v') ≤
      infDist x (segment ℝ u' v') by linarith
  refine (le_infDist hne).2 fun w' hw' => ?_
  rw [sub_le_iff_le_add]
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hw'
  have hw : p • u + q • v ∈ segment ℝ u v := ⟨p, q, hp, hq, hpq, rfl⟩
  refine (infDist_le_dist_of_mem hw).trans ?_
  have : dist (p • u + q • v) (p • u' + q • v') ≤ dist u u' + dist v v' := by
    rw [dist_eq_norm, show p • u + q • v - (p • u' + q • v') = p • (u - u') + q • (v - v') by
      simp only [smul_sub]; abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hp, Real.norm_of_nonneg hq, ← dist_eq_norm,
      ← dist_eq_norm]
    nlinarith [dist_nonneg (x := u) (y := u'), dist_nonneg (x := v) (y := v')]
  linarith [dist_triangle x (p • u' + q • v') (p • u + q • v), dist_comm (p • u' + q • v')
    (p • u + q • v)]

variable (g : Pt m ≃ᵃⁱ[ℝ] Pt m)

/-- The distance to the segment between the centers, for a point whose longitudinal coordinate in
the frame lies between those of the centers. -/
lemma infDist_centerSegment_le {r : ℝ} (hr : 0 < r) {x : Pt m}
    (h0 : 0 ≤ Pt.lon (g.symm x)) (h1 : Pt.lon (g.symm x) ≤ r) :
    infDist x (segment ℝ (g 0) (g (r • e₁))) ≤ ‖Pt.tr (g.symm x)‖ := by
  set ζ := g.symm x
  set l₀ := Pt.lon ζ
  have hmem : g (l₀ • e₁) ∈ segment ℝ (g 0) (g (r • e₁)) := by
    have : l₀ • (e₁ : Pt m) ∈ segment ℝ (0 : Pt m) (r • e₁) := by
      refine ⟨1 - l₀ / r, l₀ / r, by
        rw [sub_nonneg, div_le_one hr]; exact h1, div_nonneg h0 hr.le, by ring, ?_⟩
      rw [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ hr.ne']
    have himg := image_segment ℝ (g.toAffineEquiv : Pt m →ᵃ[ℝ] Pt m) (0 : Pt m) (r • e₁)
    have hm := mem_image_of_mem (g.toAffineEquiv : Pt m →ᵃ[ℝ] Pt m) this
    rw [himg] at hm
    simpa using hm
  refine (infDist_le_dist_of_mem hmem).trans_eq ?_
  rw [show x = g ζ by simp [ζ], g.dist_map, dist_eq_norm]
  rw [Pt.norm_eq_tr_of_lon_eq (by simp [l₀])]
  simp [Pt.tr, e₁]

end IsotropicVariance.Paper.Proofs.Localization
