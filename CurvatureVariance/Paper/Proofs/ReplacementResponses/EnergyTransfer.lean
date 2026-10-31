/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.RRReplacement
public import CurvatureVariance.Paper.Proofs.Responses.Energy
import CurvatureVariance.Paper.Proofs.Responses.Basic

/-!
# Transferring the occupation bound to a replacement space

The minimizing-tuple predicate is measurable, hence so is the countable supremum of the
energies of all minimizers. Its expectation transfers exactly through the law of the old weights.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CurvatureVariance.Paper.ReplacementResponses

variable {m : ℕ}

/-- Attainment of the slab minimum by a fixed tuple is a measurable event. -/
theorem measurableSet_isMinTuple (M : Model m) (n K : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m) (Y : Fin (K + 1) → Fin m → ℤ) :
    MeasurableSet {ω : Config m | IsMinTuple M ω n K t u v Y} := by
  classical
  by_cases h : IsAdmissibleTuple M n K t u v Y
  · simpa only [IsMinTuple, h, true_and] using
      measurableSet_eq_fun (Responses.measurable_tupleCost u n Y)
        (Responses.measurable_slabMin M n K t u v)
  · simp only [IsMinTuple, h, false_and, Set.ofPred_false, MeasurableSet.empty]

end CurvatureVariance.Paper.ReplacementResponses
