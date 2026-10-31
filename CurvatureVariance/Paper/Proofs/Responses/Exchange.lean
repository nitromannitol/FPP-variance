/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.Basic
import CurvatureVariance.Infra.FPP.Model
import CurvatureVariance.Infra.EfronStein.Coordinates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exchangeability of block responses

The exchangeability step of the proof of Lemma `lem:blocks`, as in the proof of
[AB26, Lemma 6.1]: independent resampling from the original law gives
`E(F − F^G)² = 2 E(F^G − F)₊²`. The coordinate exchange is applied directly to `resample`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- Resampling a fixed set is jointly measurable in the two configurations. -/
theorem measurable_resample (G : Set (Sym2 (Vertex m))) :
    Measurable fun p : Config m × Config m => resample G p.1 p.2 := by
  classical
  refine measurable_pi_iff.mpr fun e => ?_
  by_cases he : e.1 ∈ G
  · simpa only [resample, he, ite_true, Function.comp_def] using (show Measurable (fun ω : Config m => ω e) from measurable_pi_apply e).comp measurable_snd
  · simpa only [resample, he, ite_false, Function.comp_def] using (show Measurable (fun ω : Config m => ω e) from measurable_pi_apply e).comp measurable_fst

/-- Exchanging the weights in the same set twice recovers the old configuration. -/
theorem resample_resample (G : Set (Sym2 (Vertex m))) (ω ω' : Config m) :
    resample G (resample G ω ω') (resample G ω' ω) = ω := by
  classical
  funext e
  by_cases he : e.1 ∈ G <;> simp only [resample, he, ite_true, ite_false]

/-- The joint exchange of the two samples in a block preserves the product law. -/
theorem measurePreserving_exchange {P : Measure (Config m)} {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] (hP : IsIIDWeights P F) (G : Set (Sym2 (Vertex m))) :
    MeasurePreserving (fun p : Config m × Config m =>
      (resample G p.1 p.2, resample G p.2 p.1)) (P.prod P) (P.prod P) := by
  classical
  rw [Infra.FPP.IsIIDWeights.eq_infinitePi hP]
  convert Infra.EfronStein.measurePreserving_swap_outside (fun _ : Edge m => F)
    {e : Edge m | e.1 ∉ G} using 1
  · (funext p; apply Prod.ext <;> funext e <;>
      by_cases he : e.1 ∈ G <;> simp [resample, Infra.EfronStein.resample, he])

end CurvatureVariance.Paper.Responses
