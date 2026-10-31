/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Mean
import CurvatureVariance.Infra.FPP.TimeConstant
import CurvatureVariance.Paper.Proofs.Mean.Domain
import CurvatureVariance.Paper.Proofs.Chart.Rounding
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Four crossings and the mean at the induction length

The triangle-inequality argument of the proof of Proposition `prop:induction`. The lattice
approximation rounds inward in the ball centred at `s t₀`, as required by the exact hypothesis of
Lemma `lem:smallmean`. The connector constant uses `bd.T`, and the thresholds use only the common
law and bounds, before the fitting model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

/-- Quarter lengths lie in the interval used by Lemma `lem:smallmean`. -/
theorem quarter_length_bounds {N : ℕ} (hN : 8 ≤ N) :
    (N : ℝ) / 8 ≤ (N / 4 : ℕ) ∧ ((N / 4 : ℕ) : ℝ) ≤ N / 4 ∧
      0 ≤ (N : ℝ) - 4 * (N / 4 : ℕ) ∧ (N : ℝ) - 4 * (N / 4 : ℕ) < 4 := by
  have h₁ : 4 * (N / 4) ≤ N := Nat.mul_div_le N 4
  have h₂ : N < 4 * (N / 4) + 4 := by omega
  have h₃ : 2 ≤ N / 4 := by omega
  have h₁' : 4 * ((N / 4 : ℕ) : ℝ) ≤ N := by exact_mod_cast h₁
  have h₂' : (N : ℝ) < 4 * ((N / 4 : ℕ) : ℝ) + 4 := by exact_mod_cast h₂
  have h₃' : (2 : ℝ) ≤ (N / 4 : ℕ) := by exact_mod_cast h₃
  exact ⟨by linarith only [h₂', h₃'], by linarith only [h₁'],
    by linarith only [h₁'], by linarith only [h₂']⟩

end CurvatureVariance.Paper.Contracts
