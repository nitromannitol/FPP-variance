/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import CurvatureVariance.Infra.FPP.Model
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Fixed-path fourth moments for the slab comparison

The exceptional-event part of the proof of equation `eq:fixedcomparison` needs only a polynomial
fourth-moment bound. No independence among the fixed paths is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

open Infra.FPP

variable {m : ℕ}

/-- A coordinate walk within a slab, with its length bound retained. -/
theorem exists_walk_slabEdges_length_le {p q : ℤ} (hpq : p + 2 ≤ q) {u v : Vertex m}
    (hu : p ≤ u.1 ∧ u.1 ≤ q) (hv : p ≤ v.1 ∧ v.1 ≤ q) :
    ∃ γ : (latticeGraph m).Walk u v, (∀ e ∈ γ.edges, e ∈ slabEdges p q) ∧
      (γ.length : ℤ) ≤ |u.1 - v.1| + ∑ j, |u.2 j - v.2 j| + 2 := by
  let c := max (p + 1) (min (q - 1) u.1)
  have hc₁ : p < c := by dsimp only [c]; omega
  have hc₂ : c < q := by dsimp only [c]; omega
  have hc₃ : |u.1 - c| ≤ 1 := by dsimp only [c]; exact abs_le.mpr ⟨by omega, by omega⟩
  obtain ⟨a, hla, ha⟩ := exists_longitudinal_walk u c
  obtain ⟨b, hlb, hb⟩ := exists_longitudinal_walk v c
  have hnn : 0 ≤ ∑ j, |u.2 j - v.2 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨d, hld, hd⟩ := exists_transverse_walk v.2 (∑ j, |u.2 j - v.2 j|).toNat
    ((c, u.2) : Vertex m) (by simpa using (Int.toNat_of_nonneg hnn).symm)
  refine ⟨a.append (d.append b.reverse), ?_, ?_⟩
  · intro e he
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_append, List.mem_reverse] at he
    rcases he with he | he | he
    · exact walk_mem_slabEdges_of_snd_eq a
        (fun x hx => by have h := ha x hx; exact ⟨by constructor <;> omega, h.1⟩) e he
    · exact walk_mem_slabEdges_of_fst_eq hc₁ hc₂ d hd e he
    · exact walk_mem_slabEdges_of_snd_eq b
        (fun x hx => by have h := hb x hx; exact ⟨by constructor <;> omega, h.1⟩) e he
  · rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse]
    push_cast
    rw [hla, hlb, hld, Int.toNat_of_nonneg hnn]
    have htri := abs_sub_le v.1 u.1 c
    rw [abs_sub_comm v.1 u.1] at htri
    linarith only [htri, hc₃]

/-- An exponential moment of a nonnegative weight gives its fourth moment. -/
theorem memLp_four_weight {F : Measure ℝ≥0} [IsFiniteMeasure F]
    {α : ℝ} (hα : 0 < α) (hexp : Integrable (fun x : ℝ≥0 => Real.exp (α * x)) F) :
    MemLp (fun x : ℝ≥0 => (x : ℝ)) 4 F := by
  have hnexp := Infra.FPP.integrable_exp_mul_of_le (F := F) (neg_le_self hα.le) hexp
  have hi := integrable_rpow_abs_of_integrable_exp_mul hα.ne' hexp hnexp
    (show (0 : ℝ) ≤ 4 by norm_num)
  rw [← integrable_norm_rpow_iff measurable_coe_nnreal_real.aestronglyMeasurable
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofNat] using hi

/-- The fourth norm of a walk cost is bounded by its length times the fourth norm of one
weight. Repetitions of an edge cause no difficulty. -/
theorem eLpNorm_walkCost_four_le {P : Measure (Config m)} {F : Measure ℝ≥0}
    (hP : IsIIDWeights P F) {u v : Vertex m} (γ : (latticeGraph m).Walk u v) :
    eLpNorm (fun ω => (walkCost ω γ : ℝ)) 4 P ≤
      γ.length * eLpNorm (fun x : ℝ≥0 => (x : ℝ)) 4 F := by
  rw [walkCost_eq_sum_fun]
  calc
    _ ≤ ∑ i : Fin γ.darts.length,
        eLpNorm (fun ω : Config m => (ω (dartEdge γ i) : ℝ)) 4 P :=
      eLpNorm_sum_le (by norm_num)
    _ = _ := by
      simp only [(Infra.FPP.IsIIDWeights.identDistrib hP _).eLpNorm_eq,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        SimpleGraph.Walk.length_darts]

end CurvatureVariance.Paper.Responses
