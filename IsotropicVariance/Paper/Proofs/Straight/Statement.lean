/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Slab
public import IsotropicVariance.Paper.Proofs.SlabComparison.GeometryScale
public import IsotropicVariance.Paper.Proofs.Straight.Angle
public import IsotropicVariance.Paper.Proofs.Straight.Scale

/-! # Lemma `lem:straight`: near-geodesics are straight

The paper's proof is one paragraph; the Lean proof has four steps.

1. Near-geodesics between points of the ball lie in a larger ball: `exists_containing_ball`.
2. The random scale `W` on the larger ball: `exists_metric_scale`.
3. For `u`, `v` in this order on a near-geodesic from `a` to `b`, with `|u − a| = R ≥ W²` and either
   `|v − a| = 2R` or, if `|b − a| < 2R`, `v = b`, the triangle excess is at most `C W R^{1/2}`, so
   the directions of `u − a` and `v − a` differ by at most `C (W²/R)^{1/4}`:
   `direction_step_fourth`.
4. The sum over the dyadic radii: `curve_direction_close_of_radius`, with
   `C₁ = geometryScale A`. The chain starts at the point `x` of the lemma, at radius
   `R₀ = |x − a| ≥ C₁ W²`, so the radii are `2^k R₀`, in place of the `2^k C₁ W²` of the paper.
   They are capped at `|b − a|` by `exists_dyadic_radial_hits`, so that the chain ends at `b`: this
   is the case `v = b` of Step 3. The case `|b − a| ≤ R₀` is one step.

Steps 3 and 4 are carried out on `‖u/|u| − v/|v|‖`, and `angle_le_of_direction_close` converts the
result to the angle.
-/

@[expose] public section
open Set Metric InnerProductGeometry
namespace IsotropicVariance.Paper.Proofs.Straight
open Paper Contracts SlabComparison
universe u
variable {m : ℕ}

/-- **Steps 3 and 4 of the list above**, on one outcome:
if `|T − |·|| ≤ A (S |·|^{1/2} + S²)` on the pairs of points of a near-geodesic from `a` to `b ≠ a`,
then every point `x` of the curve with `|x − a| ≥ geometryScale A · S²` has
`∠(x − a, b − a) ≤ 1/10`. -/
theorem angle_le_of_uniform_metric (X : Setting m) (ω : X.Ω)
    (γ : IsotropicVariance.RectifiableCurve (Pt m)) {a b : Pt m}
    (hγ : IsOneOptimal (X.ρ ω) univ a b γ) (hab : a ≠ b) {A S : ℝ} (hA : 0 ≤ A) (hS : 1 ≤ S)
    (hmetric : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |X.passTime ω (γ.toFun s) (γ.toFun t) - dist (γ.toFun s) (γ.toFun t)| ≤
        A * (S * Real.sqrt (dist (γ.toFun s) (γ.toFun t)) + S ^ 2))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hfar : geometryScale A * S ^ 2 ≤ ‖γ.toFun t - a‖) :
    angle (γ.toFun t - a) (b - a) ≤ 1 / 10 := by
  obtain ⟨h8, hS2, hNR, hsmall⟩ := geometryScale_properties hA hS
  have hγ0 : γ.toFun 0 = a := hγ.1
  have hγ1 : γ.toFun 1 = b := hγ.2.1
  have hdist : geometryScale A * S ^ 2 ≤ dist (γ.toFun 0) (γ.toFun t) := by
    rw [hγ0, dist_eq_norm']
    exact hfar
  have hdir := curve_direction_close_of_radius X ω γ hγ hA hS (by linarith only [h8]) hS2
    (ε := 1 / 192) (by norm_num) hNR hsmall hmetric le_rfl ht.1 ht.2 le_rfl hdist
  rw [hγ0, hγ1] at hdir
  have hne : γ.toFun t - a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hfar
    linarith only [hfar, h8]
  exact angle_le_of_direction_close hne (sub_ne_zero.mpr hab.symm)
    (hdir.trans (by norm_num))

/-- **Lemma `lem:straight`**, from Lemma `lem:classical`. -/
theorem straightStatement_of (h : ClassicalBoundsStatement.{u}) : StraightStatement.{u} := by
  intro m hm X hnorm
  obtain ⟨K, hK, hball⟩ := exists_containing_ball X
  obtain ⟨A, C, hA, hC, hscale⟩ := exists_metric_scale h hm X hnorm hK
  have hG := geometryScale_ge_eight hA
  refine ⟨geometryScale A + C, by linarith only [hG, hC], fun r hr => ?_⟩
  obtain ⟨W, hW1, hWlog, hOs, hmetric⟩ := hscale r hr
  have hlog : 0 < Real.log (2 + r) := Real.log_pos (by linarith only [hr])
  refine ⟨W, hWlog, ?_, fun ω a ha b hb hab γ hγ t ht hfar => ?_⟩
  · exact hOs.mono_scale (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith only [hG]) hlog.le)
  · refine angle_le_of_uniform_metric X ω γ hγ hab hA (hW1 ω) (fun s hs u hu => ?_) ht ?_
    · exact hmetric ω _ (hball r hr ω a ha b hb γ hγ s hs) _
        (hball r hr ω a ha b hb γ hγ u hu)
    · exact (mul_le_mul_of_nonneg_right (by linarith only [hC]) (sq_nonneg (W ω))).trans hfar

end IsotropicVariance.Paper.Proofs.Straight
