/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.FALocalize
public import CurvatureVariance.Paper.Proofs.Gain.FALabel
import CurvatureVariance.Paper.Proofs.Gain.FAMoments
import CurvatureVariance.Paper.Proofs.Responses.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The finite approximation in one block (the proof of Lemma `lem:labels`)

Elementary facts for the finite approximation in one block, from the conclusions of Proposition
`prop:profiles` and of Lemmas `lem:localization` and `lem:modulus`:

* `eLpNorm_add_le_ofReal`, `eLpNorm_const_le_ofReal`: Minkowski's inequality with real bounds, and
  the `L^k` norm of a constant on a probability space;
* `meshPairs`: the pairs of mesh cells of the two faces of a block.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Minkowski for bounded pieces -/

/-- Minkowski's inequality with real bounds. -/
theorem eLpNorm_add_le_ofReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    {k : ℕ} (hk : 1 ≤ k)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : eLpNorm f k P ≤ ENNReal.ofReal a)
    (h2 : eLpNorm g k P ≤ ENNReal.ofReal b) :
    eLpNorm (fun ω => f ω + g ω) k P ≤ ENNReal.ofReal (a + b) := by
  rw [ENNReal.ofReal_add ha hb]
  exact (eLpNorm_add_le (f := f) (g := g) (μ := P) (p := k) (by exact_mod_cast hk)).trans
    (add_le_add h1 h2)

/-- The `L^k` norm of a constant on a probability space. -/
theorem eLpNorm_const_le_ofReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {c : ℝ} (hc : 0 ≤ c) {k : ℕ} (hk : 1 ≤ k) :
    eLpNorm (fun _ : Ω => c) k P ≤ ENNReal.ofReal c := by
  refine eLpNorm_le_ofReal_of_lintegral_le aestronglyMeasurable_const hk hc ?_
  rw [lintegral_const, measure_univ, mul_one, abs_of_nonneg hc]

/-! ### The block-level construction -/

/-- The pairs of mesh cells of the two faces. -/
noncomputable def meshPairs (m L : ℕ) (τ : ℝ) : Finset ((Fin m → ℤ) × (Fin m → ℤ)) :=
  meshBox m L τ ×ˢ meshBox m L τ

end CurvatureVariance.Paper.Gain
