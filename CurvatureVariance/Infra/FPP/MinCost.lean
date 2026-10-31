/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.ConcentrationEntropy
public import CurvatureVariance.Infra.FPP.ConcentrationHerbst

/-!
# Concentration of a minimum of edge-set costs

`minCost 𝓕 ω` is the least total weight `∑_{e ∈ F} ω_e` over a finite nonempty family `𝓕` of
finite sets of coordinates. A coordinate is *pivotal* for `ω` when every optimal set contains it
(`minCostPiv`). Pivotal coordinates lie in one optimal set, so there are at most `K` of them when
every set has at most `K` elements, and `minCost` has pivots in the sense of `HasPivots`.

For independent weights with an exponential moment, the symmetrized entropy bound and Herbst's
argument then give a Gaussian lower tail at every level (`measure_minCost_le_integral_sub`) and an
upper tail, Gaussian up to a level and exponential beyond (`measure_integral_add_le_minCost`); both
are in `CurvatureVariance.Infra.FPP.MinCostTails`. The restricted passage time, the minimum of the
costs of the self-avoiding paths of bounded length, is one such minimum.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

open Infra.Entropy

section General

variable {ι : Type*} (𝓕 : Finset (Finset ι)) (h𝓕 : 𝓕.Nonempty)

/-- Least total weight over a finite nonempty family of finite edge sets. -/
noncomputable def minCost (ω : ι → ℝ≥0) : ℝ :=
  𝓕.inf' h𝓕 fun F => ∑ e ∈ F, (ω e : ℝ)

/-- The coordinates contained in every optimal set. -/
def minCostPiv (i : ι) : Set (ι → ℝ≥0) :=
  {ω | ∀ F ∈ 𝓕, ∑ e ∈ F, (ω e : ℝ) = minCost 𝓕 h𝓕 ω → i ∈ F}

variable {𝓕 h𝓕}

theorem minCost_le {ω : ι → ℝ≥0} {F : Finset ι} (hF : F ∈ 𝓕) :
    minCost 𝓕 h𝓕 ω ≤ ∑ e ∈ F, (ω e : ℝ) :=
  Finset.inf'_le _ hF

theorem exists_minCost_eq (ω : ι → ℝ≥0) :
    ∃ F ∈ 𝓕, minCost 𝓕 h𝓕 ω = ∑ e ∈ F, (ω e : ℝ) :=
  Finset.exists_mem_eq_inf' h𝓕 _

theorem minCost_nonneg (ω : ι → ℝ≥0) : 0 ≤ minCost 𝓕 h𝓕 ω := by
  obtain ⟨F, -, hF⟩ := exists_minCost_eq (h𝓕 := h𝓕) ω
  rw [hF]
  exact Finset.sum_nonneg fun e _ => NNReal.coe_nonneg _

theorem measurable_minCost : Measurable (minCost 𝓕 h𝓕) := by
  have hsum : ∀ F : Finset ι, Measurable fun ω : ι → ℝ≥0 => ∑ e ∈ F, (ω e : ℝ) := fun F =>
    Finset.measurable_sum _ fun e _ => (measurable_pi_apply e).coe_nnreal_real
  unfold minCost
  refine Finset.Nonempty.cons_induction
    (motive := fun 𝓖 h𝓖 => Measurable fun ω : ι → ℝ≥0 => 𝓖.inf' h𝓖 fun F => ∑ e ∈ F, (ω e : ℝ))
    (fun F => by simpa using hsum F) (fun F 𝓖 hF h𝓖 ih => ?_) h𝓕
  simp only [Finset.inf'_cons h𝓖]
  exact (hsum F).inf ih

variable [DecidableEq ι]

theorem measurableSet_minCostPiv (i : ι) : MeasurableSet (minCostPiv 𝓕 h𝓕 i) := by
  have hsum : ∀ F : Finset ι, Measurable fun ω : ι → ℝ≥0 => ∑ e ∈ F, (ω e : ℝ) := fun F =>
    Finset.measurable_sum _ fun e _ => (measurable_pi_apply e).coe_nnreal_real
  have h : minCostPiv 𝓕 h𝓕 i =
      ⋂ F ∈ 𝓕, {ω | ∑ e ∈ F, (ω e : ℝ) = minCost 𝓕 h𝓕 ω → i ∈ F} := by
    ext ω; simp [minCostPiv]
  rw [h]
  refine Finset.measurableSet_biInter _ fun F _ => ?_
  by_cases hi : i ∈ F
  · simp [hi]
  · simp only [hi, imp_false]
    exact (measurableSet_eq_fun (hsum F) measurable_minCost).compl

/-- Raising one weight raises `minCost` only through pivotal coordinates, and by at most the new
weight. -/
theorem hasPivots_minCost : HasPivots (minCost 𝓕 h𝓕) (minCostPiv 𝓕 h𝓕) := by
  intro x i y hlt
  have hcost : ∀ F : Finset ι, i ∉ F →
      ∑ e ∈ F, (Function.update x i y e : ℝ) = ∑ e ∈ F, (x e : ℝ) := fun F hi =>
    Finset.sum_congr rfl fun e he => by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem he hi)]
  refine ⟨fun F hF hopt => ?_, ?_⟩
  · by_contra hi
    have := minCost_le (h𝓕 := h𝓕) (ω := Function.update x i y) hF
    rw [hcost F hi, hopt] at this
    exact absurd hlt this.not_gt
  · obtain ⟨F, hF, hopt⟩ := exists_minCost_eq (h𝓕 := h𝓕) x
    refine (minCost_le hF).trans ?_
    rw [hopt]
    by_cases hi : i ∈ F
    · rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hi, Function.update_self,
        hcost _ (Finset.notMem_erase i F)]
      linarith [NNReal.coe_nonneg (x i)]
    · rw [hcost F hi]
      linarith [NNReal.coe_nonneg y]

/-- At most `K` coordinates are pivotal when every set has at most `K` elements. -/
theorem tsum_indicator_minCostPiv_le {K : ℕ} (hK : ∀ F ∈ 𝓕, F.card ≤ K) (x : ι → ℝ≥0) :
    ∑' i, (minCostPiv 𝓕 h𝓕 i).indicator (1 : (ι → ℝ≥0) → ℝ≥0∞) x ≤ K := by
  obtain ⟨F, hF, hopt⟩ := exists_minCost_eq (h𝓕 := h𝓕) x
  have hsub : ∀ i, (minCostPiv 𝓕 h𝓕 i).indicator (1 : (ι → ℝ≥0) → ℝ≥0∞) x ≤
      if i ∈ F then 1 else 0 := by
    intro i
    by_cases hx : x ∈ minCostPiv 𝓕 h𝓕 i
    · rw [Set.indicator_of_mem hx, ite_eq_left_iff.2 (fun h => absurd (hx F hF hopt.symm) h)]
      rfl
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc _ ≤ ∑' i, (if i ∈ F then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_le_tsum hsub
    _ = F.card := by
        rw [tsum_eq_sum (s := F) fun i hi => by simp [hi], Finset.sum_boole]
        simp
    _ ≤ K := by exact_mod_cast hK F hF

end General

end CurvatureVariance.Infra.FPP
