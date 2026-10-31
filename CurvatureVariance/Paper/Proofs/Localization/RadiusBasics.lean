/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Infra.FPP.Model
public import CurvatureVariance.Infra.FPP.Walks
public import CurvatureVariance.Infra.FPP.TimeConstantNorm
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes

/-!
# Lemma `lem:localization`: basic tools

Tools for the proof of `LocalizationStatement` (Lemma `lem:localization`):

* `transOff t z = z₂ − z₁ t`: the transverse offset of `z` from the line `ℝ (1, t)`, and the
  lower bound `‖transOff t z‖² / ((1 + T²)‖z‖) ≤ ‖z‖ ∠(z, (1,t))²` for `‖t‖ ≤ T`, which turns the
  angular bound (equation `eq:angular`) into a bound on transverse offsets. In use
  `T = T₀ + 1`, with `T₀ = bd.T` the bound for `|t₀|`.
* `roundVertex`: a lattice point in a hyperplane within `√(m+1)` of a given point.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set InnerProductGeometry
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Radius

open CurvatureVariance.Paper

variable {m : ℕ}

/-! ## Transverse offsets -/

/-- The transverse offset `z₂ − z₁ t` of `z = (z₁, z₂)` from the line `ℝ (1, t)`. -/
def transOff (t : EuclideanSpace ℝ (Fin m)) (z : Pt m) : EuclideanSpace ℝ (Fin m) :=
  z.snd - z.fst • t

theorem transOff_add (t : EuclideanSpace ℝ (Fin m)) (z z' : Pt m) :
    transOff t (z + z') = transOff t z + transOff t z' := by
  simp only [transOff, WithLp.add_snd, WithLp.add_fst, add_smul]; abel

theorem transOff_sub (t : EuclideanSpace ℝ (Fin m)) (z z' : Pt m) :
    transOff t (z - z') = transOff t z - transOff t z' := by
  simp only [transOff, WithLp.sub_snd, WithLp.sub_fst, sub_smul]; abel

/-- The point `(0, y)`. -/
def transVec (y : EuclideanSpace ℝ (Fin m)) : Pt m := WithLp.toLp 2 ((0 : ℝ), y)

@[simp] theorem transVec_fst (y : EuclideanSpace ℝ (Fin m)) : (transVec y).fst = 0 := rfl

@[simp] theorem transVec_snd (y : EuclideanSpace ℝ (Fin m)) : (transVec y).snd = y := rfl

theorem norm_transVec (y : EuclideanSpace ℝ (Fin m)) : ‖transVec y‖ = ‖y‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (transVec y)
  simp only [transVec_fst, transVec_snd, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- `z = z₁ (1, t) + (0, transOff t z)`. -/
theorem eq_fst_smul_add_transVec (t : EuclideanSpace ℝ (Fin m)) (z : Pt m) :
    z = z.fst • slopeVec t + transVec (transOff t z) := by
  refine Infra.FPP.pt_ext ?_ ?_
  · simp
  · simp [transOff]

/-- A point is within `|z₁| ‖(1,t)‖ + ‖transOff t z‖` of the origin. -/
theorem norm_le_of_transOff (t : EuclideanSpace ℝ (Fin m)) (z : Pt m) :
    ‖z‖ ≤ |z.fst| * ‖slopeVec t‖ + ‖transOff t z‖ := by
  conv_lhs => rw [eq_fst_smul_add_transVec t z]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, norm_transVec]

/-! ## Lattice rounding -/

/-- The lattice point `(p, round c)` of the hyperplane `{x₁ = p}`. -/
noncomputable def roundVertex (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) : Vertex m :=
  (p, fun i => round (c i))

theorem norm_transversePoint_round_sub_le (c : EuclideanSpace ℝ (Fin m)) :
    ‖transversePoint (fun i => round (c i)) - c‖ ≤ Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(transversePoint (fun i => round (c i)) - c) i‖ ^ 2 ≤ ∑ _i : Fin m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [transversePoint, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
        have h := abs_sub_round (c i)
        rw [abs_sub_comm] at h
        nlinarith [abs_nonneg ((round (c i) : ℝ) - c i), sq_abs ((round (c i) : ℝ) - c i)]
    _ = m := by simp

/-- `roundVertex p c` is within `√(m+1)` of `(p, c)`. -/
theorem norm_point_roundVertex_sub_le (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) :
    ‖point (roundVertex p c) - WithLp.toLp 2 ((p : ℝ), c)‖ ≤ Real.sqrt ((m : ℝ) + 1) := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (point (roundVertex p c) - WithLp.toLp 2 ((p : ℝ), c))
  have hfst : (point (roundVertex p c) - WithLp.toLp 2 ((p : ℝ), c)).fst = 0 := by
    simp [roundVertex]
  have hsnd : (point (roundVertex p c) - WithLp.toLp 2 ((p : ℝ), c)).snd =
      transversePoint (fun i => round (c i)) - c := by
    simp [roundVertex]
  rw [hfst, hsnd, norm_zero] at h
  have h2 := norm_transversePoint_round_sub_le c
  rw [← Real.sqrt_sq (norm_nonneg (point (roundVertex p c) - WithLp.toLp 2 ((p : ℝ), c)))]
  apply Real.sqrt_le_sqrt
  have h3 : ‖transversePoint (fun i => round (c i)) - c‖ ^ 2 ≤ m := by
    calc _ ≤ (Real.sqrt m) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = m := Real.sq_sqrt (Nat.cast_nonneg m)
  nlinarith

end CurvatureVariance.Paper.Localization.Radius
