/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.RawRadii
public import CurvatureVariance.Paper.Proofs.Responses.Energy
import CurvatureVariance.Infra.FPP.Model
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The squared-radius occupation bound

Apply the independent-array estimate to the squared localization radii. The radius array is
zero outside the retained pairs, so the retained-pair moment extends to all entries. The estimate
holds simultaneously for all minimizing tuples, as the proof of Lemma `lem:blocks` requires.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- The raw radius is measurable. -/
theorem measurable_slabRadius (M : Model m) (K : ℕ) (A Cd : ℝ) (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (j k : Fin m → ℤ) :
    Measurable fun ω => slabRadius M K A Cd ω n t i j k :=
  measurable_const.mul (measurable_const.add (measurable_locRadiusSlab _ _ _ _ _))

/-- Zero extension to the retained pairs preserves measurability. -/
theorem measurable_radiusArray (M : Model m) (K : ℕ) (A Cd : ℝ) (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (j k : Fin m → ℤ) :
    Measurable fun ω => radiusArray M K A Cd ω n t i j k := by
  classical
  by_cases h : IsRetainedPair M n (wInt M K A n) j k
  · simpa only [radiusArray, h, ite_true] using measurable_slabRadius M K A Cd n t i j k
  · simpa only [radiusArray, h, ite_false] using
      (measurable_const : Measurable (fun _ : Config m => (0 : ℝ≥0∞)))

/-- The radius array reads only its own slab, including its zero extension. -/
theorem radiusArray_congr (M : Model m) (K : ℕ) (A Cd : ℝ) (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (j k : Fin m → ℤ) {ω ω' : Config m}
    (h : ∀ e : Edge m, e.1 ∈ slabEdges (((i : ℤ) - 1) * n) ((i : ℤ) * n) → ω e = ω' e) :
    radiusArray M K A Cd ω n t i j k = radiusArray M K A Cd ω' n t i j k := by
  classical
  by_cases hr : IsRetainedPair M n (wInt M K A n) j k
  · simp only [radiusArray, hr, ite_true, slabRadius]
    rw [locRadiusSlab_congr _ _ _ _ _ h]
  · simp only [radiusArray, hr, ite_false]

/-- The squared radius arrays are independent over the slabs. -/
theorem iIndepFun_radiusArrays {M : Model m} (hM : M.Standing) (K n : ℕ) (A Cd : ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    iIndepFun (fun (i : Fin K) ω => fun j k : Fin m → ℤ =>
      radiusArray M K A Cd ω n t ((i : ℕ) + 1) j k ^ 2) M.P := by
  let : IsProbabilityMeasure M.F := hM.probF
  apply iIndepFun_slab_functions hM.iid
  · intro i
    exact measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k =>
      (measurable_radiusArray M K A Cd n t ((i : ℕ) + 1) j k).pow_const 2
  · intro i ω ω' hlocal
    funext j k
    rw [radiusArray_congr M K A Cd n t ((i : ℕ) + 1) j k (fun e he =>
      hlocal e (by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using he))]

end CurvatureVariance.Paper.Responses
