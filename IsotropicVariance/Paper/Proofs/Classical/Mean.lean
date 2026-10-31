/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.SphereComparison
public import IsotropicVariance.Paper.Proofs.Classical.SphereGeometry
public import IsotropicVariance.Paper.Proofs.Classical.MeanFromDoubling
import Mathlib.Tactic.Linarith

/-!
# The mean half of Lemma `lem:classical`

The second bound of `eq:classical` follows from the first as in Howard and Newman
[HN, Lemmas 4.1 and 4.2] (proof of Lemma `lem:classical`).

`mean_doubling_of_concentration` is the argument of [HN, Lemma 4.1]. A curve from `0` to `2s e₁`
crosses the spheres of radius `s` around its two endpoints, and the first bound, at the points of
a net of each sphere, controls the minimum of the passage time from the center to the sphere. This
gives `E[T_{2s}] ≥ 2 E[T_s] − K (s log(2+s))^{1/2}`. The density being bounded, the net has mesh
`2`, and the exceptional event of [HN] is not needed.

`meanBound_of_concentration` applies [HN, Lemma 4.2] to the doubling inequality, with
`a(ℓ) = E[T_ℓ]` and `g(ℓ) = K (ℓ log(2+ℓ))^{1/2}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Classical

/-- The doubling inequality of [HN, Lemma 4.1] (proof of Lemma `lem:classical`): two ordered
endpoint spheres turn concentration into near-superadditive doubling. -/
theorem mean_doubling_of_concentration {m : ℕ} (hm : 1 ≤ m) (X : Setting.{u} m)
    (hconc : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 ≤ s →
      Cited.IsOs X.P 2 (C * Real.sqrt s) (fun ω => |X.TRV s ω - X.mean s|)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 1 ≤ s →
      2 * X.mean s - K * errorScale s ≤ X.mean (2 * s) := by
  obtain ⟨K, hK, herr⟩ := exists_sphere_lower_error hm X hconc
  refine ⟨2 * K, by positivity, ?_⟩
  intro s hs
  let b : Pt m := (2 * s) • e₁
  obtain ⟨Y₀, hY₀i, _hY₀0, hY₀E, hY₀⟩ := herr s hs 0
  obtain ⟨Y₁, hY₁i, _hY₁0, hY₁E, hY₁⟩ := herr s hs b
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hd : dist (0 : Pt m) b = 2 * s := by
    rw [dist_eq_norm, zero_sub, norm_neg, norm_smul,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s), Paper.norm_e₁, mul_one]
  have hpoint (ω : X.Ω) : 2 * X.mean s ≤ X.TRV (2 * s) ω + Y₀ ω + Y₁ ω := by
    have hh := passTime_ge_of_sphere_lower X ω 0 b hs0 (by rw [hd])
      (hY₀ ω) (hY₁ ω)
    change (X.mean s - Y₀ ω) + (X.mean s - Y₁ ω) ≤ X.TRV (2 * s) ω at hh
    linarith only [hh]
  have hTi := Infra.TimeConstant.integrable_TRV X (2 * s)
  have hmean := integral_mono (integrable_const (2 * X.mean s)) ((hTi.add hY₀i).add hY₁i) hpoint
  change (∫ _ : X.Ω, 2 * X.mean s ∂X.P) ≤
    ∫ ω, X.TRV (2 * s) ω + Y₀ ω + Y₁ ω ∂X.P at hmean
  rw [integral_const, probReal_univ, one_smul,
    integral_add (f := fun ω => X.TRV (2 * s) ω + Y₀ ω) (g := Y₁)
      (hTi.add hY₀i) hY₁i,
    integral_add (f := X.TRV (2 * s)) (g := Y₀) hTi hY₀i] at hmean
  change 2 * X.mean s ≤ X.mean (2 * s) + (∫ ω, Y₀ ω ∂X.P) + (∫ ω, Y₁ ω ∂X.P) at hmean
  linarith only [hmean, hY₀E, hY₁E]

/-- **The second bound of Lemma `lem:classical`**, from the first as in [HN, Lemmas 4.1 and 4.2]
(proof of Lemma `lem:classical`). There are no extra geometric, doubling, mean-rate or contract
premises. -/
theorem meanBound_of_concentration {m : ℕ} (hm : 1 ≤ m) (X : Setting.{u} m)
    (hX : X.IsNormalized)
    (hconc : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      Cited.IsOs X.P 2 (C * Real.sqrt t) (fun ω => |X.TRV t ω - X.mean t|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      0 ≤ X.mean t - t ∧ X.mean t - t ≤ C * Real.sqrt (t * Real.log (2 + t)) := by
  obtain ⟨K, hK, hdouble⟩ := mean_doubling_of_concentration hm X hconc
  exact classical_mean_bound_of_doubling X hX hK hdouble

end IsotropicVariance.Paper.Proofs.Classical
