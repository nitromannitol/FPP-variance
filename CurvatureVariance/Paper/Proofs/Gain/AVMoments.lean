/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.Common
public import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import CurvatureVariance.Infra.FPP.Model
import Mathlib.Analysis.SpecialFunctions.Exponential
import CurvatureVariance.Paper.Proofs.Moments.Basic

/-!
# Square integrability of the minima

The minimum `F` of equation `eq:F` over `K` slabs (`targetMin`) and the averaged minimum `F̄`
(`averagedMin`) are square integrable for slabs of width `n ≥ 2` (`memLp_targetMin`,
`memLp_averagedMin`), so that their variances in Section `sec:gain` are finite. If an admissible
tuple exists, `F` is at most the cost of a fixed coordinate path through it, slab by slab, a finite
sum of weights, each square integrable by the exponential moment of Assumption (W); otherwise
`F = ∞` and `targetMin = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- Under (W) the weight law has a finite second moment. -/
theorem memLp_two_weightLaw {M : Model m} (hM : M.Standing) :
    MemLp (fun x : ℝ≥0 => (x : ℝ)) 2 M.F := by
  have := hM.probF
  obtain ⟨α, hα, hint⟩ := hM.assumptionW.1
  rw [memLp_two_iff_integrable_sq measurable_coe_nnreal_real.aestronglyMeasurable]
  refine (hint.const_mul (2 / α ^ 2)).mono'
    (measurable_coe_nnreal_real.pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hx : 0 ≤ α * (x : ℝ) := mul_nonneg hα.le (NNReal.coe_nonneg x)
  have h := Real.pow_div_factorial_le_exp _ hx 2
  rw [Nat.factorial_two, Nat.cast_ofNat] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (x : ℝ) ^ 2 = 2 / α ^ 2 * ((α * x) ^ 2 / 2) := by field_simp
    _ ≤ 2 / α ^ 2 * Real.exp (α * x) := mul_le_mul_of_nonneg_left h (by positivity)

/-- Each weight is square integrable under the law of the model. -/
theorem memLp_two_weight {M : Model m} (hM : M.Standing) (e : Edge m) :
    MemLp (fun ω : Config m => (ω e : ℝ)) 2 M.P :=
  ((IsIIDWeights.identDistrib hM.iid e).memLp_iff).2 (memLp_two_weightLaw hM)

/-- The cost of a fixed walk is square integrable. -/
theorem memLp_two_walkCost {M : Model m} (hM : M.Standing) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) : MemLp (fun ω => (walkCost ω γ : ℝ)) 2 M.P := by
  simp_rw [coe_walkCost_eq_sum]
  exact memLp_finsetSum _ fun i _ => memLp_two_weight hM (dartEdge γ i)

/-- If an admissible tuple exists and its slab passages are realized by walks in the slabs, the
minimum `F` is at most the total cost of these walks. -/
theorem targetMin_le_sum_walkCost {M : Model m} {n K ℓ : ℕ} {y : Fin m → ℤ}
    {Y : Fin (K + 1) → Fin m → ℤ}
    (hY : IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y)
    (γ : ∀ i : Fin K, (latticeGraph m).Walk (tuplePoint 0 n Y i.castSucc)
      (tuplePoint 0 n Y i.succ))
    (hγ : ∀ i, ∀ e ∈ (γ i).edges, e ∈ slabEdges ((0 : Vertex m).1 + (i : ℤ) * n)
      ((0 : Vertex m).1 + ((i : ℤ) + 1) * n)) (ω : Config m) :
    targetMin M ω n K ℓ y ≤ ∑ i : Fin K, (walkCost ω (γ i) : ℝ) := by
  have hle : slabMin M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) ≤
      ∑ i : Fin K, ((walkCost ω (γ i) : ℝ≥0) : ℝ≥0∞) := by
    refine (Responses.slabMin_le_tupleCost hY ω).trans ?_
    unfold tupleCost
    exact Finset.sum_le_sum fun i _ => iInf₂_le (γ i) (hγ i)
  have hfin : (∑ i : Fin K, ((walkCost ω (γ i) : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.coe_ne_top
  have h := ENNReal.toReal_mono hfin hle
  rwa [ENNReal.toReal_sum fun i _ => ENNReal.coe_ne_top] at h

/-- Without an admissible tuple the minimum `F` is `∞`, so `targetMin = 0`. -/
theorem targetMin_eq_zero_of_not_exists {M : Model m} {n K ℓ : ℕ} {y : Fin m → ℤ}
    (h : ¬ ∃ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y) (ω : Config m) :
    targetMin M ω n K ℓ y = 0 := by
  simp only [not_exists] at h
  have htop : slabMin M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) = ⊤ := by
    unfold slabMin
    simp [h]
  simp [targetMin, htop]

/-- **The minimum `F` of equation `eq:F` is square integrable** for slabs of width
`n ≥ 2`. -/
theorem memLp_targetMin {M : Model m} (hM : M.Standing) {n : ℕ} (hn : 2 ≤ n) (K ℓ : ℕ)
    (y : Fin m → ℤ) : MemLp (fun ω => targetMin M ω n K ℓ y) 2 M.P := by
  have := hM.probP
  by_cases hex : ∃ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y
  · obtain ⟨Y, hY⟩ := hex
    have hwalk : ∀ i : Fin K, ∃ γ : (latticeGraph m).Walk (tuplePoint 0 n Y i.castSucc)
        (tuplePoint 0 n Y i.succ), ∀ e ∈ γ.edges, e ∈ slabEdges ((0 : Vertex m).1 + (i : ℤ) * n)
          ((0 : Vertex m).1 + ((i : ℤ) + 1) * n) := by
      intro i
      have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
      apply Responses.exists_walk_slabEdges
      · nlinarith only [hn']
      · simp only [tuplePoint, Fin.val_castSucc]
        constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n]
      · simp only [tuplePoint, Fin.val_succ, Nat.cast_add, Nat.cast_one]
        constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n]
    choose γ hγ using hwalk
    refine (memLp_finsetSum (Finset.univ : Finset (Fin K))
      fun i _ => memLp_two_walkCost hM (γ i)).mono
      (Responses.measurable_targetMin M n K ℓ y).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have h0 : 0 ≤ targetMin M ω n K ℓ y := ENNReal.toReal_nonneg
    have hb := targetMin_le_sum_walkCost hY γ hγ ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (h0.trans hb)]
    exact hb
  · simp_rw [targetMin_eq_zero_of_not_exists hex]
    exact memLp_const 0

/-- The translated minimum `F_τ` is square integrable for `n ≥ 2`. -/
theorem memLp_translatedMin {M : Model m} (hM : M.Standing) {n : ℕ} (hn : 2 ≤ n) (K ℓ : ℕ)
    (y τ : Fin m → ℤ) : MemLp (fun ω => translatedMin M ω n K ℓ y τ) 2 M.P := by
  simp_rw [translatedMin_eq_targetMin]
  exact (memLp_targetMin hM hn K ℓ y).comp_measurePreserving (Moments.standing_measurePreserving_translate hM _)

/-- **The averaged minimum `F̄` is square integrable** for slabs of width `n ≥ 2`. -/
theorem memLp_averagedMin {M : Model m} (hM : M.Standing) {n : ℕ} (hn : 2 ≤ n) (K : ℕ) (A : ℝ)
    (L ℓ : ℕ) (y : Fin m → ℤ) : MemLp (fun ω => averagedMin M K A L ω n ℓ y) 2 M.P := by
  unfold averagedMin
  exact (memLp_finsetSum _ fun v _ => memLp_translatedMin hM hn K ℓ y _).const_mul _

end CurvatureVariance.Paper.Gain
