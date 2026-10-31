/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-!
# The convex shift in AKM Lemma A.4

For a positive exponent `s`, `exp((x+a)^s)` is convex on the positive half-line
as soon as `s a^s ≥ 1-s`. This is the analytic ingredient for `s < 1`.
-/

@[expose] public section

open Set
namespace IsotropicVariance.Infra.Os

/-- Convexity of the shifted exponential power used in AKM A.4. -/
theorem convexOn_exp_rpow_shift {s a : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hsa : 1 - s ≤ s * a ^ s) :
    ConvexOn ℝ (Ici 0) (fun x : ℝ => Real.exp ((x + a) ^ s)) := by
  let f := fun x : ℝ => Real.exp ((x + a) ^ s)
  let g := fun x : ℝ => Real.exp ((x + a) ^ s) * s * (x + a) ^ (s - 1)
  let h := fun x : ℝ =>
    (Real.exp ((x + a) ^ s) * (s * (x + a) ^ (s - 1)) * s) * (x + a) ^ (s - 1) +
      (Real.exp ((x + a) ^ s) * s) * ((s - 1) * (x + a) ^ (s - 2))
  have hd (x : ℝ) (hx : 0 < x + a) : HasDerivAt f (g x) x := by
    have hh := ((hasDerivAt_id x).add_const a).rpow_const (p := s) (Or.inl hx.ne')
    simpa only [f, g, one_mul, id_eq, mul_assoc] using hh.exp
  have hgd (x : ℝ) (hx : 0 < x + a) : HasDerivAt g (h x) x := by
    have hh := ((hasDerivAt_id x).add_const a).rpow_const (p := s) (Or.inl hx.ne')
    have hh' := ((hasDerivAt_id x).add_const a).rpow_const (p := s - 1) (Or.inl hx.ne')
    convert (hh.exp.mul_const s).mul hh' using 1 <;>
      simp only [g, h, one_mul, id_eq, sub_sub]
    · rfl
    · congr 2; norm_num
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := g) (f'' := h) (convex_Ici 0)
    ((Real.continuous_exp.comp ((Real.continuous_rpow_const hs.le).comp (continuous_id.add_const a))).continuousOn)
  · intro x hx
    exact (hd x (add_pos_of_nonneg_of_pos (interior_subset hx) ha)).hasDerivWithinAt
  · intro x hx
    exact (hgd x (add_pos_of_nonneg_of_pos (interior_subset hx) ha)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    have hu : 0 < x + a := add_pos_of_nonneg_of_pos hx0 ha
    have hpow : (x + a) ^ (s - 1) * (x + a) ^ (s - 1) =
        (x + a) ^ (s - 2) * (x + a) ^ s := by
      rw [← Real.rpow_add hu, ← Real.rpow_add hu]
      congr 1
      ring
    have hfactor : h x = Real.exp ((x + a) ^ s) * s * (x + a) ^ (s - 2) *
        (s * (x + a) ^ s + s - 1) := by
      dsimp only [h]
      calc
        _ = Real.exp ((x + a) ^ s) * s *
            (s * ((x + a) ^ (s - 1) * (x + a) ^ (s - 1)) + (s - 1) * (x + a) ^ (s - 2)) := by ring
        _ = _ := by rw [hpow]; ring
    rw [hfactor]
    apply mul_nonneg (by positivity)
    have hh := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le (le_add_of_nonneg_left hx0) hs.le) hs.le
    exact sub_nonneg.mpr (by linarith only [hsa, hh])

end IsotropicVariance.Infra.Os
