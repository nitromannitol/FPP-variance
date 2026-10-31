/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.CheapPaths

/-!
# The probabilistic inputs shared by the concentration, mean-rate and time-constant chains

The time-constant and mean-rate chains use two consequences of the concentration chain, stated
here as properties of a law `P` so that the chains can be developed separately and composed at the
end:

* `MinCostLowerTail P C c`: the Gaussian lower tail of least costs over bounded edge sets;
* `PassageTimeConcentration P C c`: an exponential tail of `|T(0,x) − E T(0,x)|` at the scale
  `|x|^{1/2}`, which gives the almost-sure convergence of `T(0, n x)/n` by Borel–Cantelli.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- **The Gaussian lower tail of least costs over bounded edge sets** with constants `C, c`: for
every finite nonempty family `𝓕` of edge sets of at most `K` edges, the least total weight
`min_{F ∈ 𝓕} ∑_F ω` falls `t` below its mean with probability at most `C exp(-c t²/(K + 1))`. -/
def MinCostLowerTail (P : Measure (Config m)) (C c : ℝ) : Prop :=
  ∀ (𝓕 : Finset (Finset (Edge m))) (h𝓕 : 𝓕.Nonempty) (K : ℕ), (∀ F ∈ 𝓕, F.card ≤ K) →
    ∀ t : ℝ, 0 ≤ t →
      P {ω | 𝓕.inf' h𝓕 (fun F => ∑ e ∈ F, (ω e : ℝ)) ≤
          (∫ ω', 𝓕.inf' h𝓕 (fun F => ∑ e ∈ F, (ω' e : ℝ)) ∂P) - t} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (t ^ 2 / ((K : ℝ) + 1)))))

/-- **Concentration of the passage time at the scale `|x|^{1/2}`**, exponential form, with
constants `C, c`: `P(|T(0,x) − E T(0,x)| > u |x|^{1/2}) ≤ C e^{-c u}` for `|x| ≥ 2` and `u ≥ 0`
(`|x|` the Euclidean norm). -/
def PassageTimeConcentration (P : Measure (Config m)) (C c : ℝ) : Prop :=
  ∀ x : Vertex m, 2 ≤ ‖point x‖ → ∀ u : ℝ, 0 ≤ u →
    P {ω | u * Real.sqrt ‖point x‖ <
      |(passageTime ω 0 x : ℝ) - ∫ ω', (passageTime ω' 0 x : ℝ) ∂P|} ≤
      ENNReal.ofReal (C * Real.exp (-(c * u)))

end CurvatureVariance.Infra.FPP
