/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanConvexHull
public import CurvatureVariance.Infra.FPP.TimeConstantNorm

/-!
# The mean rate, from its inputs

`E T(0, x) ≤ μ(x) + C (|x| log(2 + |x|))^{1/2}` for `|x| ≥ 1` ([ADH, Thm 3.33]), for a law with:
- translation invariance;
- integrable passage times and weights;
- linear growth of the mean;
- the time-constant property for a norm `μ`;
- the cheap-path estimate;
- the Gaussian lower tail of least costs over bounded edge sets.

The proof is Alexander's method:
- the convex-hull approximation property (`convexHullApprox_meanTime`);
- general approximation from it (`le_add_meanRate_of_convexHullApprox`);
- `E T ≥ μ` (`le_meanTime`).

The cheap-path estimate is `CheapPaths P a c`, of decay `e^{-ck}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ} {P : Measure (Config m)}

/-- **The mean rate** under the hypotheses of Alexander's method. -/
theorem meanTime_le_add_meanRate [IsProbabilityMeasure P]
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    (hE : ∀ e : Edge m, Integrable (fun ω : Config m => (ω e : ℝ)) P)
    {A : ℝ} (hA : 0 ≤ A) (hlin : ∀ x, meanTime P x ≤ A * ‖point x‖)
    {μ : PtNorm m} (hμ : IsTimeConstant P μ)
    {a c₀ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hc₀ : 0 < c₀) (hcheap : CheapPaths P a c₀)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hlow : MinCostLowerTail P C c) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ x : Vertex m, 1 ≤ ‖point x‖ →
      meanTime P x ≤ μ.1 (point x) + C' * meanRate ‖point x‖ := by
  obtain ⟨lo, hi, hlo0, hhi0, hb⟩ := PtNorm.exists_bounds μ
  obtain ⟨M, C₁, r₀, hM, hC₁, hr₀, hchap⟩ := convexHullApprox_meanTime hT hI hE hμ hlo0 hhi0
    (fun x => (hb x).1) (fun x => (hb x).2) ha ha1 hc₀ hcheap hC hc hlow
  exact le_add_meanRate_of_convexHullApprox (meanTime_add_le hT hI) meanTime_zero hlin
    (le_meanTime hT hI hμ) hA hM hC₁ hr₀ hchap

end CurvatureVariance.Infra.FPP
