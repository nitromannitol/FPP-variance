/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Geometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Euclidean triangle excess under the uniform metric estimate

A deterministic step of the straightness argument of [HN, Theorem 2.6] and [HN, Lemma 2.7], which
the proof of Lemma `lem:straight` makes uniform. The near-geodesic input is the three-point
inequality obtained from ordered points of a 1-optimal curve.
No probabilistic hypothesis is used in these geometric estimates.
-/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison

variable {E : Type*} [PseudoMetricSpace E]

/-- The uniform bound `|T(x, y) − |y − x|| ≤ C(W |y − x|^{1/2} + W²)` of the proof of Lemma
`lem:straight` bounds the triangle excess of three ordered points whose near-geodesic defect is at
most one. -/
lemma triangle_excess_le {T : E → E → ℝ} {A S r : ℝ} (hA : 0 ≤ A) (hS : 1 ≤ S)
    {a u v : E}
    (hau : |T a u - dist a u| ≤ A * (S * Real.sqrt (dist a u) + S ^ 2))
    (huv : |T u v - dist u v| ≤ A * (S * Real.sqrt (dist u v) + S ^ 2))
    (hav : |T a v - dist a v| ≤ A * (S * Real.sqrt (dist a v) + S ^ 2))
    (hdefect : T a u + T u v ≤ T a v + 1)
    (h1 : dist a u ≤ r) (h2 : dist u v ≤ r) (h3 : dist a v ≤ r) :
    dist a u + dist u v - dist a v ≤ (3 * A + 1) * (S * Real.sqrt r + S ^ 2) := by
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have hsqr : 1 ≤ S ^ 2 := by nlinarith
  have hbound (d : ℝ) (hd : d ≤ r) :
      A * (S * Real.sqrt d + S ^ 2) ≤ A * (S * Real.sqrt r + S ^ 2) := by
    exact mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd) hS0) le_rfl) hA
  have hb1 := hbound _ h1
  have hb2 := hbound _ h2
  have hb3 := hbound _ h3
  have ha1 := (abs_le.mp hau).1
  have ha2 := (abs_le.mp huv).1
  have ha3 := (abs_le.mp hav).2
  have hnonneg : 0 ≤ S * Real.sqrt r := mul_nonneg hS0 (Real.sqrt_nonneg _)
  nlinarith

/-- The elementary absorption that turns the metric error into the `S²` no-return scale. -/
lemma radius_le_sq_scale {r A S : ℝ} (hr : 0 ≤ r)
    (h : r ≤ A * (S * Real.sqrt r + S ^ 2)) :
    r ≤ (A ^ 2 + 2 * A) * S ^ 2 := by
  nlinarith [sq_nonneg (Real.sqrt r - A * S), Real.sq_sqrt hr]

/-- Returning from radius `r` to radius at most `r/2` forces triangle excess at least `r`. -/
lemma radius_le_triangle_excess {a u v : E} {r : ℝ}
    (hu : r ≤ dist a u) (hv : dist a v ≤ r / 2) :
    r ≤ dist a u + dist u v - dist a v := by
  have h := dist_triangle a v u
  rw [dist_comm v u] at h
  linarith

/-- No-return constant for the Euclidean uniform metric error. -/
def noReturnScale (A : ℝ) : ℝ := (6 * A + 2) ^ 2 + 2 * (6 * A + 2)

/-- A near-geodesic cannot return to half its first-hit radius above the `S²` scale.
The first-hit point has distance exactly `r`, so all three metric errors are local to scale
`2r`, as in the paper. -/
theorem no_return_of_uniform_metric {T : E → E → ℝ} {A S r : ℝ}
    (hA : 0 ≤ A) (hS : 1 ≤ S) (hr : 0 ≤ r) {a u v : E}
    (hau : |T a u - dist a u| ≤ A * (S * Real.sqrt (dist a u) + S ^ 2))
    (huv : |T u v - dist u v| ≤ A * (S * Real.sqrt (dist u v) + S ^ 2))
    (hav : |T a v - dist a v| ≤ A * (S * Real.sqrt (dist a v) + S ^ 2))
    (hdefect : T a u + T u v ≤ T a v + 1)
    (hu : dist a u = r) (hlarge : noReturnScale A * S ^ 2 < r) :
    r / 2 < dist a v := by
  by_contra hv
  have hv : dist a v ≤ r / 2 := le_of_not_gt hv
  have huv' : dist u v ≤ 2 * r := by
    have h := dist_triangle u a v
    rw [dist_comm u a, hu] at h
    linarith
  have hex := triangle_excess_le hA hS hau huv hav hdefect
    (show dist a u ≤ 2 * r by rw [hu]; linarith) huv'
    (show dist a v ≤ 2 * r by linarith)
  have hlower := radius_le_triangle_excess hu.ge hv
  have hsqrt : Real.sqrt (2 * r) ≤ 2 * Real.sqrt r := by
    nlinarith [Real.sq_sqrt hr, Real.sq_sqrt (show 0 ≤ 2 * r by positivity),
      Real.sqrt_nonneg r, Real.sqrt_nonneg (2 * r)]
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have hreplace : (3 * A + 1) * (S * Real.sqrt (2 * r) + S ^ 2) ≤
      (6 * A + 2) * (S * Real.sqrt r + S ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt hS0
    nlinarith [sq_nonneg S]
  have h := radius_le_sq_scale hr (hlower.trans (hex.trans hreplace))
  exact (not_le_of_gt hlarge) h

end IsotropicVariance.Paper.Proofs.SlabComparison
