/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
public import CurvatureVariance.Paper.Proofs.Geometry.HitsPieces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The increments between consecutive first hits: arithmetic

Elementary facts for the step of the proof of Lemma `lem:slabs` (2) that bounds the increments
`x_{i+1} − x_i` (`increment_of_coneAt`, `Proofs.Geometry.SlabsHits`): equation `eq:cone` at `x_i`,
and Lemma `lem:cone` with the slope `t_i'` of `v − x_i` for the part of the geodesic from `x_i`, at
`x_{i+1}`, "these two bounds give" the increments.

* `norm_snd_sub_smul_le`: if `w₁ = s > 0`, the slope of `w` is within `A` of `t'` and `t'` is
  within `B` of `t`, then `‖w⊥ − s t‖ ≤ s (A + B)`;
* `inBox_mono`, `fst_eq_of_point_sub`: boxes increase with the radius, and the longitudinal
  displacement of `v − u = ℓ (1, t)` is `ℓ`;
* `mul_le_aperture`: an angle `ε ρ` with `κ ε ≤ 1`, `κ = slopeFactor T`, and `0 ≤ ρ ≤ 1/3` is
  within the aperture `aperture T`.

The smallness of the cone bounds at distance `r ≥ n` and slope deviation `x ≤ 3ρ`,
`ρ = n^{δ/100−1/4}`, is `eventually_cone_small`.
-/

@[expose] public section

open InnerProductGeometry
open scoped NNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The transverse increment from two slope estimates: if `w₁ = s > 0`, the slope of `w` is within
`A` of `t'` and `t'` is within `B` of `t`, then `‖w⊥ − s t‖ ≤ s (A + B)`. -/
theorem norm_snd_sub_smul_le {w : Pt m} {s A B : ℝ} {t t' : EuclideanSpace ℝ (Fin m)}
    (hs : w.fst = s) (hs0 : 0 < s) (hA : ‖w.fst⁻¹ • w.snd - t'‖ ≤ A) (hB : ‖t' - t‖ ≤ B) :
    ‖w.snd - s • t‖ ≤ s * (A + B) := by
  rw [hs] at hA
  have e : w.snd - s • t = s • (s⁻¹ • w.snd - t) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  refine mul_le_mul_of_nonneg_left ?_ hs0.le
  calc ‖s⁻¹ • w.snd - t‖ = ‖(s⁻¹ • w.snd - t') + (t' - t)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖s⁻¹ • w.snd - t'‖ + ‖t' - t‖ := norm_add_le _ _
    _ ≤ A + B := add_le_add hA hB

/-- Boxes increase with the radius. -/
theorem inBox_mono {R R' : ℝ} (h : R ≤ R') {x : Vertex m} (hx : InBox R x) : InBox R' x :=
  ⟨hx.1.trans h, fun j => (hx.2 j).trans h⟩

/-- The longitudinal displacement of `v − u = ℓ (1, t)` is `ℓ`. -/
theorem fst_eq_of_point_sub {u v : Vertex m} {ℓ : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    (huv : point v - point u = (ℓ : ℝ) • slopeVec t) : v.1 = u.1 + ℓ := by
  have h := congrArg (fun w : Pt m => w.fst) huv
  have h' : (v.1 : ℝ) - u.1 = ℓ := by simpa using h
  have h'' : ((v.1 : ℤ) : ℝ) = ((u.1 + ℓ : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast h''

/-- An angle `ε ρ` with `κ ε ≤ 1`, `κ = slopeFactor T`, and `0 ≤ ρ ≤ 1/3` is within the aperture
`aperture T`. -/
theorem mul_le_aperture {T ε ρ : ℝ} (hT : 0 ≤ T) (hε0 : 0 ≤ ε) (hε : slopeFactor T * ε ≤ 1)
    (hρ : ρ ≤ 1 / 3) : ε * ρ ≤ aperture T := by
  have hT1 : (0 : ℝ) < 1 + T := by linarith
  have hερ : ε * ρ ≤ ε := by
    calc ε * ρ ≤ ε * 1 := mul_le_mul_of_nonneg_left (hρ.trans (by norm_num)) hε0
      _ = ε := mul_one ε
  refine hερ.trans ?_
  unfold aperture
  unfold slopeFactor at hε
  rw [le_div_iff₀ (by positivity)]
  nlinarith

variable {M : Model m} {C Cs S ε : ℝ} {N : ℕ} {ω : Config m}

end CurvatureVariance.Paper.Proofs.Geometry
