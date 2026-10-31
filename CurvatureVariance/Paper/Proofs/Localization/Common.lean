/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Infra.FPP.Translation
public import CurvatureVariance.Infra.Os.Sum
import CurvatureVariance.Infra.FPP.Model
import CurvatureVariance.Infra.FPP.Walks
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry
import CurvatureVariance.Paper.Proofs.Moments.ParentBounds
import CurvatureVariance.Paper.Proofs.Moments.Shear
import CurvatureVariance.Paper.Proofs.Localization.RadiusBasics
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# Lemma `lem:localization`: common tools

Tools for the proof of Lemma `lem:localization`: components and lattice roundings of points of
`ℝ^d`, the scales `Q_s` of Section `sec:induction` and `W_s = (sQ_s)^{1/2}`, elementary `O₁` facts,
translation invariance of `O_s` bounds for passage times, and the deterministic cost bound from the
upper half of equation `eq:support`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Localization

variable {m : ℕ}

/-! ## Components of points of `ℝ^d` -/

/-! ## The scales `Q_s` and `W_s` -/

section Scales

variable {M : Model m} {K : ℕ} {A : ℝ}

theorem Q_nonneg (hA : 0 ≤ A) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Q M K A s :=
  mul_nonneg hA (Real.rpow_nonneg hs _)

theorem Q_pos (hA : 0 < A) {s : ℝ} (hs : 0 < s) : 0 < Q M K A s :=
  mul_pos hA (Real.rpow_pos_of_pos hs _)

theorem W_nonneg (s : ℝ) : 0 ≤ W M K A s := Real.sqrt_nonneg _

/-- The exponent `1/2 − δ/K` of `Q` lies in `[1/3, 1/2]` for `K ≥ 10⁴`. -/
theorem Q_exponent_bounds (hM : M.Standing) (hK : 10 ^ 4 ≤ K) :
    (1 : ℝ) / 3 ≤ 1 / 2 - M.δ / K ∧ 1 / 2 - M.δ / K ≤ 1 / 2 := by
  have hK' : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have h1 : M.δ / K ≤ 1 / 10 ^ 4 := by
    rw [div_le_div_iff₀ hKpos (by norm_num)]
    nlinarith [hM.delta_le_one, hM.delta_pos]
  have h2 : 0 ≤ M.δ / K := div_nonneg hM.delta_pos.le hKpos.le
  constructor <;> linarith

/-- `Q` is nondecreasing in the length. -/
theorem Q_le_Q (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 0 ≤ A) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') : Q M K A s ≤ Q M K A s' := by
  have he := (Q_exponent_bounds hM hK).1
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hss' (by linarith)) hA

/-- `Q_s ≥ 1` for `s ≥ 1` and `A ≥ 1`. -/
theorem one_le_Q (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 1 ≤ A) {s : ℝ} (hs : 1 ≤ s) :
    1 ≤ Q M K A s :=
  (Real.one_le_rpow hs (by norm_num)).trans (Moments.Parent.rpow_third_le_Q hM hK hA hs)

end Scales

end CurvatureVariance.Paper.Localization
