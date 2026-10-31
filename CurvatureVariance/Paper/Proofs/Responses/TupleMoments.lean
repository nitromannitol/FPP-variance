/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.FixedPaths
public import CurvatureVariance.Infra.FPP.Walks
import CurvatureVariance.Infra.FPP.Model
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Fourth-moment bounds for deterministic competitors

Fixed coordinate paths dominate slab passage times, so a deterministic admissible tuple bounds
the fourth norm of the minimum. These estimates do not use the induction premise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

open Infra.FPP

variable {m : ℕ}

/-- Fourth norm of a slab distance, from a coordinate path in the slab. -/
theorem eLpNorm_slabTimeReal_four_le {P : Measure (Config m)} {F : Measure ℝ≥0}
    (hP : IsIIDWeights P F) {p q : ℤ} (hpq : p + 2 ≤ q) {u v : Vertex m}
    (hu : p ≤ u.1 ∧ u.1 ≤ q) (hv : p ≤ v.1 ∧ v.1 ≤ q) :
    eLpNorm (fun ω => slabTimeReal ω p q u v) 4 P ≤
      ENNReal.ofReal ((|u.1 - v.1| : ℤ) + ∑ j, |u.2 j - v.2 j| + 2) *
        eLpNorm (fun x : ℝ≥0 => (x : ℝ)) 4 F := by
  obtain ⟨γ, hγ, hlen⟩ := exists_walk_slabEdges_length_le hpq hu hv
  have hmono : eLpNorm (fun ω => slabTimeReal ω p q u v) 4 P ≤
      eLpNorm (fun ω => (walkCost ω γ : ℝ)) 4 P := by
    apply eLpNorm_mono_ae ((measurable_restrictedTime _ _ _).ennreal_toReal.aestronglyMeasurable)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (NNReal.coe_nonneg _)]
    exact ENNReal.toReal_mono ENNReal.coe_ne_top (iInf₂_le γ hγ)
  refine hmono.trans ((eLpNorm_walkCost_four_le hP γ).trans (mul_le_mul' ?_ le_rfl))
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast hlen

/-- Fourth norm of the real passage time, from an unrestricted coordinate path. -/
theorem eLpNorm_passageTimeReal_four_le {P : Measure (Config m)} {F : Measure ℝ≥0}
    (hP : IsIIDWeights P F) (u v : Vertex m) :
    eLpNorm (fun ω => passageTimeReal ω u v) 4 P ≤
      (l1Dist u v : ℝ≥0∞) * eLpNorm (fun x : ℝ≥0 => (x : ℝ)) 4 F := by
  obtain ⟨γ, -, hlen⟩ := exists_isPath_length_eq_l1Dist u v
  have hmono : eLpNorm (fun ω => passageTimeReal ω u v) 4 P ≤
      eLpNorm (fun ω => (walkCost ω γ : ℝ)) 4 P := by
    apply eLpNorm_mono_ae (measurable_passageTime_real u v).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
        (NNReal.coe_le_coe.mpr (Infra.FPP.passageTime_le_walkCost ω γ))
  exact hmono.trans (by simpa only [hlen] using eLpNorm_walkCost_four_le hP γ)

/-- For a fixed admissible tuple, the fourth norm of the minimum is bounded by the sum of the
fourth norms of its slab terms. -/
theorem eLpNorm_slabMin_four_le_tuple {M : Model m} {n K : ℕ}
    (hn : 2 ≤ n) {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m}
    {Y : Fin (K + 1) → Fin m → ℤ} (hY : IsAdmissibleTuple M n K t u v Y) :
    eLpNorm (fun ω => (slabMin M ω n K t u v).toReal) 4 M.P ≤
      ∑ i : Fin K, eLpNorm (fun ω => slabTimeReal ω
        (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
        (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ)) 4 M.P := by
  have hmono : eLpNorm (fun ω => (slabMin M ω n K t u v).toReal) 4 M.P ≤
      eLpNorm (fun ω => (tupleCost ω u n Y).toReal) 4 M.P := by
    apply eLpNorm_mono_ae (measurable_slabMin M n K t u v).ennreal_toReal.aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono
      (ENNReal.sum_ne_top.mpr fun i _ => tuple_slabTime_ne_top ω u hn Y i)
      (slabMin_le_tupleCost hY ω)
  refine hmono.trans ?_
  have heq : (fun ω => (tupleCost ω u n Y).toReal) =
      ∑ i : Fin K, fun ω => slabTimeReal ω (u.1 + (i : ℤ) * n)
        (u.1 + ((i : ℤ) + 1) * n) (tuplePoint u n Y i.castSucc)
          (tuplePoint u n Y i.succ) := by
    funext ω
    simp only [Finset.sum_apply, tupleCost, slabTimeReal,
      ENNReal.toReal_sum fun i _ => tuple_slabTime_ne_top ω u hn Y i]
  rw [heq]
  exact eLpNorm_sum_le (by norm_num)

end CurvatureVariance.Paper.Responses
