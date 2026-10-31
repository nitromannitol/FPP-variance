/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.RadiusBasics
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Shear

/-!
# Lemma `lem:localization`: deterministic geometry

Deterministic steps of the proof of Lemma `lem:localization`:

* `infDist_segment_le`: with `D` the transverse offset of `x` from the line through `a` of slope
  `t`, `|t| ≤ T`, `Γ` a bound for the offsets of `u` and `v`, and longitudinal overshoots beyond
  `v` and before `u` at most `Ω`, the distance from `x` to `[u, v]` is at most
  `D + Γ + (1 + T) Ω`.

`mem_thicken_of_coord`: a lattice point near a sheared box lies in a thickened transverse cube.
-/

@[expose] public section

open MeasureTheory Set InnerProductGeometry
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Radius

open CurvatureVariance.Paper

variable {m : ℕ}

theorem transOff_smul (t : EuclideanSpace ℝ (Fin m)) (r : ℝ) (z : Pt m) :
    transOff t (r • z) = r • transOff t z := by
  simp only [transOff, WithLp.smul_snd, WithLp.smul_fst, smul_sub, smul_smul, smul_eq_mul]

/-- **Distance to the segment.** With `D` the transverse offset of `X` from the line through `A`
of slope `t`, `‖t‖ ≤ T`, `Γ` a bound for the offsets of `U` and `V`, and longitudinal overshoots
at most `Ω`: `dist(X, [U, V]) ≤ D + Γ + (1 + T) Ω`. -/
theorem infDist_segment_le (t : EuclideanSpace ℝ (Fin m)) {T : ℝ} (ht : ‖t‖ ≤ T) {X U V A : Pt m}
    {Γ Ω : ℝ} (hUV : U.fst < V.fst) (hU : ‖transOff t (U - A)‖ ≤ Γ)
    (hV : ‖transOff t (V - A)‖ ≤ Γ) (hΩ : 0 ≤ Ω) (hXV : X.fst - V.fst ≤ Ω)
    (hUX : U.fst - X.fst ≤ Ω) :
    Metric.infDist X (segment ℝ U V) ≤ ‖transOff t (X - A)‖ + Γ + (1 + T) * Ω := by
  set ℓ := V.fst - U.fst with hℓ
  have hℓ0 : 0 < ℓ := sub_pos.mpr hUV
  set lam : ℝ := max 0 (min 1 ((X.fst - U.fst) / ℓ))
  have hlam0 : 0 ≤ lam := le_max_left _ _
  have hlam1 : lam ≤ 1 := max_le zero_le_one (min_le_left _ _)
  set q : Pt m := U + lam • (V - U)
  have hq : q ∈ segment ℝ U V := by
    refine ⟨1 - lam, lam, by linarith, hlam0, by ring, ?_⟩
    simp only [q, smul_sub, sub_smul, one_smul]; abel
  refine (Metric.infDist_le_dist_of_mem hq).trans ?_
  rw [dist_eq_norm]
  -- the longitudinal part
  set d₁ := (X - q).fst
  have hd₁ : d₁ = X.fst - U.fst - lam * ℓ := by
    simp only [d₁, q, WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst, smul_eq_mul, hℓ]; ring
  have hd₁b : |d₁| ≤ Ω := by
    rw [hd₁, abs_le]
    by_cases ha : (X.fst - U.fst) / ℓ ≤ 0
    · have : lam = 0 := by
        simp only [lam]; exact max_eq_left (min_le_of_right_le ha)
      rw [this]
      have : X.fst - U.fst ≤ 0 := by
        by_contra h; push Not at h; have := div_pos h hℓ0; linarith
      constructor <;> nlinarith
    by_cases hb : 1 ≤ (X.fst - U.fst) / ℓ
    · have : lam = 1 := by
        simp only [lam]; rw [min_eq_left hb, max_eq_right zero_le_one]
      rw [this]
      have : ℓ ≤ X.fst - U.fst := by rwa [le_div_iff₀ hℓ0, one_mul] at hb
      constructor <;> linarith
    · push Not at ha hb
      have : lam = (X.fst - U.fst) / ℓ := by
        simp only [lam]; rw [min_eq_right hb.le, max_eq_right ha.le]
      rw [this, div_mul_cancel₀ _ hℓ0.ne']
      constructor <;> linarith
  -- the transverse part
  have hsnd : (X - q).snd = transOff t (X - A) - ((1 - lam) • transOff t (U - A) +
      lam • transOff t (V - A)) + d₁ • t := by
    have h1 : transOff t (X - q) = transOff t (X - A) - ((1 - lam) • transOff t (U - A) +
        lam • transOff t (V - A)) := by
      have : X - q = (X - A) - ((1 - lam) • (U - A) + lam • (V - A)) := by
        simp only [q, smul_sub, sub_smul, one_smul]; abel
      rw [this, transOff_sub, transOff_add, transOff_smul, transOff_smul]
    rw [← h1]
    simp only [transOff, d₁]; abel
  have hconv : ‖(1 - lam) • transOff t (U - A) + lam • transOff t (V - A)‖ ≤ Γ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg hlam0]
    nlinarith
  have hsndb : ‖(X - q).snd‖ ≤ ‖transOff t (X - A)‖ + Γ + T * Ω := by
    rw [hsnd]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl hconv)) ?_
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg d₁, norm_nonneg t]
  refine (Moments.norm_le_abs_fst_add_norm_snd (X - q)).trans ?_
  linarith

/-! ## Membership in thickened cubes -/

/-- A lattice point `x` at longitudinal distance `τ ∈ [0, ρ]` after the hyperplane `{x₁ = q}`,
whose transverse coordinates are within `side/2 − 1/2` of `c + τ t'`, lies in the transverse cube
of side `side` and centre `c` in `{x₁ = q}`, thickened by `ρ` along `(1, t')`. -/
theorem mem_thicken_of_coord {q : ℤ} {c t' : EuclideanSpace ℝ (Fin m)} {side ρ : ℝ} {x : Vertex m}
    (hτ0 : q ≤ x.1) (hτρ : ((x.1 - q : ℤ) : ℝ) ≤ ρ)
    (hcoord : ∀ i, |(x.2 i : ℝ) - ((x.1 - q : ℤ) : ℝ) * t' i - c i| ≤ side / 2 - 1 / 2) :
    x ∈ thicken (transverseCube q c side) t' ρ := by
  set τ : ℝ := ((x.1 - q : ℤ) : ℝ)
  set y : EuclideanSpace ℝ (Fin m) := transversePoint x.2 - τ • t'
  refine ⟨roundVertex q y, ⟨rfl, fun i => ?_⟩, τ, ?_, ?_⟩
  · simp only [roundVertex]
    have h1 := abs_sub_round (y i)
    have h2 := hcoord i
    have hy : y i = (x.2 i : ℝ) - τ * t' i := by
      simp [y, transversePoint]
    calc |(round (y i) : ℝ) - c i| ≤ |(round (y i) : ℝ) - y i| + |y i - c i| := abs_sub_le _ _ _
      _ ≤ 1 / 2 + (side / 2 - 1 / 2) := by
          rw [abs_sub_comm] at h1; rw [hy]; exact add_le_add h1 h2
      _ = side / 2 := by ring
  · rw [abs_of_nonneg (by simp only [τ]; exact_mod_cast sub_nonneg.mpr hτ0)]; exact hτρ
  · have h := norm_point_roundVertex_sub_le q y
    have heq : point x - (point (roundVertex q y) + τ • slopeVec t') =
        -(point (roundVertex q y) - WithLp.toLp 2 ((q : ℝ), y)) := by
      refine Infra.FPP.pt_ext ?_ ?_
      · simp [roundVertex, τ, slopeVec]
      · simp [roundVertex, y, slopeVec]; abel
    rw [heq, norm_neg]; exact h

end CurvatureVariance.Paper.Localization.Radius
