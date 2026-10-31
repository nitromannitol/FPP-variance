/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Moments.ParentCombine
public import CurvatureVariance.Paper.Proofs.Moments.ExpArrayBounds
import CurvatureVariance.Paper.Proofs.Moments.Weights
import CurvatureVariance.Paper.Proofs.Chart.Rounding
import CurvatureVariance.Paper.Proofs.Moments.WidthMargin
import CurvatureVariance.Infra.FPP.TimeConstantNorm
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet

/-!
# Lemma `lem:parent`: lengths comparable to `N`

Facts for the proof of Lemma `lem:parent` (`ParentLemma`), from equation `eq:rowenergy`
(`Contracts.ExpArrayStatement`), Lemma `lem:slabs` (`Contracts.SlabsStatement`, part (2) with
`S = N^{δ/1000}`) and the classical estimates (`Contracts.ClassicalStatement`, for `μ ≤ E T`);
the lower Gaussian bound at all scales is the input `measure_abs_passageTime_sub_integral_le`
([ADH, Theorem 3.13]).

Fix `M ≥ 128` with `C M^{−1/3} ≤ 1/200`, where the paper has the exponent `2/5`, for the `C` of
equation `eq:rowenergy` and `s = ⌊ℓ/M⌋`;
then `parent_combine` with the scale comparisons gives `|T − μ| ≤ C Q_ℓ + O₁(Q_ℓ/100)` with
`C = M/200 + hi · pathBound m M |t₀| + 1`, independent of `κ, K, A, N`. Every constant and
threshold comes from the bounds `bd` before the model: `hi` from `μ`, `θ₀` and `C₁` from the law,
and `T = bd.T ≥ |t₀|` in place of `|t₀|`, so the constant is `M/200 + hi · pathBound m M T + 1`.

* `floorTuple_adm'`, `norm_targetSlope_le`: the floor tuple is admissible, and the slope of the
  target is within `2 s^{δ/100−1/4}` of `t₀`;
* `abs_mu_sub_le`: `|μ(a) − μ(b)| ≤ C |a − b|₁`;
* `eventually_parent`: the conditions on `N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

namespace Parent

/-- The floor tuple is admissible once `s ≥ 256 m`. -/
theorem floorTuple_adm' {M : Model m} (hM : M.Standing) {s Ms : ℕ} (hs : (256 * m : ℝ) ≤ s)
    (hs1 : 1 ≤ s) (hMs : 0 < Ms * s) (z : Fin m → ℤ) :
    IsAdmissibleTuple M s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)
      (ExpArray.floorTuple s (targetSlope (Ms * s) z) Ms) := by
  refine ⟨?_, ?_, fun i => ?_⟩
  · funext k; simp [ExpArray.floorTuple, ExpArray.floorPt]
  · simp only [ExpArray.floorTuple, Fin.val_last]
    exact ExpArray.floorPt_last hMs z
  · rw [ExpArray.floorTuple_step]
    refine (ExpArray.norm_floorPt_sub_le s _ _).trans ?_
    have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    have h1 : Real.sqrt s ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hs1' (by linarith [hM.delta_pos])
    have h2 : 16 * Real.sqrt m = Real.sqrt (256 * m) := by
      rw [Real.sqrt_mul (by norm_num), show (256 : ℝ) = 16 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have h3 : Real.sqrt (256 * m) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
    linarith

/-- The slope of the target: `|t − t₀| ≤ 2 s^{δ/100−1/4}`. -/
theorem norm_targetSlope_le {M : Model m} (hM : M.Standing) {s Ms : ℕ} (hs : 1 ≤ s)
    (hMs : 1 ≤ Ms) {z : Fin m → ℤ}
    (hz : ‖transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
      2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4))) :
    ‖targetSlope (Ms * s) z - M.t₀‖ ≤ 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hMs' : (1 : ℝ) ≤ Ms := by exact_mod_cast hMs
  have hL : (0 : ℝ) < ((Ms * s : ℕ) : ℝ) := by push_cast; positivity
  have hsL : (s : ℝ) ≤ ((Ms * s : ℕ) : ℝ) := by push_cast; nlinarith
  have he : M.δ / 100 - 1 / 4 ≤ 0 := by linarith [hM.delta_le_one]
  have heq : targetSlope (Ms * s) z - M.t₀ =
      (((Ms * s : ℕ) : ℝ))⁻¹ • (transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀) := by
    rw [targetSlope, smul_sub, inv_smul_smul₀ hL.ne']
  rw [heq, norm_smul, norm_inv, Real.norm_of_nonneg hL.le, inv_mul_le_iff₀ hL]
  calc ‖transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
        2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := hz
    _ = ((Ms * s : ℕ) : ℝ) * (2 * ((Ms * s : ℕ) : ℝ) ^ (M.δ / 100 - 1 / 4)) := by
        rw [Real.rpow_add hL, Real.rpow_one]; ring
    _ ≤ ((Ms * s : ℕ) : ℝ) * (2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4)) := by
        have h1 : ((Ms * s : ℕ) : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hsL he
        have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
        exact mul_le_mul_of_nonneg_left h2 hL.le

/-- `|μ(a) − μ(b)| ≤ C |a − b|₁` for `μ ≤ C|·|`. -/
theorem abs_mu_sub_le {M : Model m} {hi : ℝ} (hhi : 0 ≤ hi)
    (hb : ∀ x : Pt m, M.μ.1 x ≤ hi * ‖x‖) (a b : Vertex m) :
    |M.μ.1 (point a) - M.μ.1 (point b)| ≤ hi * Infra.FPP.l1Dist b a := by
  obtain ⟨p, -, hp⟩ := Infra.FPP.exists_isPath_length_eq_l1Dist a b
  have h1 := Infra.FPP.norm_point_sub_le_length p
  rw [hp, Infra.FPP.l1Dist_comm] at h1
  calc |M.μ.1 (point a) - M.μ.1 (point b)| ≤ M.μ.1 (point a - point b) :=
        abs_sub_map_le_sub M.μ.1 _ _
    _ ≤ hi * ‖point a - point b‖ := hb _
    _ ≤ hi * Infra.FPP.l1Dist b a := mul_le_mul_of_nonneg_left h1 hhi

/-- The conditions on `N` of the proof. -/
theorem eventually_parent (M : Law m) (hM : M.Valid) {κ : ℝ} (hκ : 0 < κ) (B₂ B₅ B₆ : ℝ) :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ N ∧ B₂ ≤ Real.sqrt N ∧ 32 ≤ κ * N ∧
      Real.log N ≤ (N : ℝ) ^ (M.δ / 1000) ∧
      B₅ ≤ κ ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3 - M.δ / 500) ∧
      B₆ ≤ (N : ℝ) ^ (9 * M.δ / 10000) := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hκ3 : 0 < κ ^ ((1 : ℝ) / 3) := by positivity
  have e1 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ N :=
    (eventually_ge_atTop 1).mono fun N h => by exact_mod_cast h
  have e2 := eventually_le_rpow B₂ (p := 1 / 2) (by norm_num)
  have e3 := eventually_le_rpow (32 / κ) (p := 1) one_pos
  have e4 := eventually_log_two_add_le_rpow (r := M.δ / 1000) (c := 1) (by positivity) one_pos
  have e5 := eventually_le_rpow (B₅ / κ ^ ((1 : ℝ) / 3)) (p := 1 / 3 - M.δ / 500)
    (by linarith)
  have e6 := eventually_le_rpow B₆ (p := 9 * M.δ / 10000) (by positivity)
  filter_upwards [e1, e2, e3, e4, e5, e6] with N h1 h2 h3 h4 h5 h6
  refine ⟨h1, by rwa [Real.sqrt_eq_rpow], ?_, ?_, ?_, h6⟩
  · rw [Real.rpow_one, div_le_iff₀ hκ] at h3; linarith
  · have : Real.log N ≤ Real.log (2 + N) := Real.log_le_log (by linarith) (by linarith)
    linarith
  · rw [div_le_iff₀ hκ3] at h5; linarith


end Parent

open Parent

end CurvatureVariance.Paper.Moments
