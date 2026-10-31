/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.NetScale
public import IsotropicVariance.Paper.Proofs.Profiles.Basic
public import IsotropicVariance.Statements.Cited.IsOs
import IsotropicVariance.Infra.Os.Maximum
import IsotropicVariance.Infra.Os.Moments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Comparing passage times to endpoint spheres

The bound [HN, (4.6)] of the proof of [HN, Lemma 4.1], which the proof of Lemma `lem:classical`
cites. Proper-motion invariance transfers the given directional concentration
estimate to each point of the sphere net. A finite maximum and the endpoint Lipschitz bound
give a common lower error for every point on the sphere. Its expectation has the
classical square-root-log scale, uniformly in the center of the sphere.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Classical

/-- The sphere infimum is bounded below by the directional mean minus an integrable
error whose expectation is at most the classical error scale. -/
theorem exists_sphere_lower_error {m : ℕ} (hm : 1 ≤ m) (X : Setting m)
    (hconc : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 ≤ s →
      Cited.IsOs X.P 2 (C * Real.sqrt s) (fun ω => |X.TRV s ω - X.mean s|)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 1 ≤ s → ∀ a : Pt m,
      ∃ Y : X.Ω → ℝ, Integrable Y X.P ∧ (∀ ω, 0 ≤ Y ω) ∧
        (∫ ω, Y ω ∂X.P) ≤ K * errorScale s ∧
        ∀ (ω : X.Ω) (z : Pt m), dist a z = s → X.mean s - Y ω ≤ X.passTime ω a z := by
  classical
  obtain ⟨C, hC, hconc⟩ := hconc
  obtain ⟨B, hB, hbound⟩ := Profiles.exists_upperBound X
  obtain ⟨D, hD, hscale⟩ := sphere_net_scale_bound m
  have he1 : 0 < errorScale 1 := errorScale_pos zero_lt_one
  let K := 4 * C * D + 2 * B / errorScale 1
  refine ⟨K, by positivity, ?_⟩
  intro s hs a
  have hspos : 0 < s := zero_lt_one.trans_le hs
  obtain ⟨H, hH, hcard, hsphere, hcover⟩ := exists_sphere_net (m := m) hs
  let F : Pt m → X.Ω → ℝ := fun q ω => |X.passTime ω a (a + q) - X.mean s|
  let Z : X.Ω → ℝ := H.sup' hH F
  let θ : ℝ := (Real.log (2 * (H.card : ℝ)) / Real.log 2) ^ (1 / (2 : ℝ)) *
    (C * Real.sqrt s)
  have hcard1 : (1 : ℝ) ≤ H.card := by exact_mod_cast hH.card_pos
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hθ : 0 < θ := by
    have hlogN : 0 < Real.log (2 * (H.card : ℝ)) := Real.log_pos (by linarith only [hcard1])
    exact mul_pos (Real.rpow_pos_of_pos (div_pos hlogN hlog2) _)
      (mul_pos hC (Real.sqrt_pos.mpr hspos))
  have hFs (q : Pt m) (hq : q ∈ H) : Cited.IsOs X.P 2 (C * Real.sqrt s) (F q) := by
    have hd : dist a (a + q) = s := by
      rw [dist_eq_norm, show a - (a + q) = -q by abel, norm_neg, hsphere q hq]
    have hh := Profiles.isOs_passTime_of_TRV (X := X) hm (s := 2) (θ := C * Real.sqrt s)
      (continuous_abs.measurable.comp (measurable_id.sub_const (X.mean s))) a (a + q)
    rw [hd] at hh
    exact hh (hconc s hs)
  have hZ : Cited.IsOs X.P 2 θ Z := Infra.Os.isOs_finset_sup' (by norm_num)
    (mul_pos hC (Real.sqrt_pos.mpr hspos)) H hH F hFs
  have hle (q : Pt m) (hq : q ∈ H) (ω : X.Ω) : F q ω ≤ Z ω := by
    change F q ω ≤ (H.sup' hH F) ω
    rw [Finset.sup'_apply]
    exact Finset.le_sup' (fun q => F q ω) hq
  have hZ0 (ω : X.Ω) : 0 ≤ Z ω := by
    obtain ⟨q, hq⟩ := hH
    exact (abs_nonneg _).trans (hle q hq ω)
  have hZi : Integrable Z X.P := hZ.integrable (by norm_num) hθ (Eventually.of_forall hZ0)
  have hZE : (∫ ω, Z ω ∂X.P) ≤ 4 * θ := by
    have hh := hZ.integral_pos_rpow_le (by norm_num : (0 : ℝ) < 2) hθ
      (show (0 : ℝ) ≤ 1 by norm_num)
    simp only [max_eq_left (hZ0 _), Real.rpow_one] at hh
    have hceil : Nat.ceil ((1 : ℝ) / 2) = 1 := (Nat.ceil_eq_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩
    norm_num only [hceil, Nat.factorial_one, Nat.cast_one] at hh
    exact hh
  have hθbound : θ ≤ C * D * errorScale s := by
    have hh := mul_le_mul_of_nonneg_left (hscale s hs H hH hcard) hC.le
    dsimp only [θ]
    nlinarith only [hh]
  refine ⟨fun ω => Z ω + 2 * B, hZi.add (integrable_const _),
    fun ω => add_nonneg (hZ0 ω) (by positivity), ?_, ?_⟩
  · rw [integral_add hZi (integrable_const _), integral_const, probReal_univ, one_smul]
    have hconst : 2 * B ≤ (2 * B / errorScale 1) * errorScale s := by
      calc
        2 * B = (2 * B / errorScale 1) * errorScale 1 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (errorScale_mono zero_le_one hs) (by positivity)
    have hh := mul_le_mul_of_nonneg_left hθbound (by norm_num : (0 : ℝ) ≤ 4)
    dsimp only [K]
    nlinarith only [hZE, hh, hconst]
  · intro ω z hz
    have hza : ‖z - a‖ = s := by simpa only [dist_eq_norm'] using hz
    obtain ⟨q, hq, hnear⟩ := hcover (z - a) hza
    have hnear' : dist z (a + q) ≤ 2 := by
      convert hnear using 1
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    have hLip := Profiles.abs_passTime_sub_le hbound hB.le ω a z a (a + q)
    rw [dist_self, zero_add] at hLip
    have hLip' := hLip.trans (mul_le_mul_of_nonneg_left hnear' hB.le)
    have hmesh := hle q hq ω
    have htriangle := abs_sub_le (X.passTime ω a z) (X.passTime ω a (a + q)) (X.mean s)
    have hneg := neg_le_abs (X.passTime ω a z - X.mean s)
    dsimp only [F] at hmesh
    linarith only [hLip', hmesh, htriangle, hneg]

end IsotropicVariance.Paper.Proofs.Classical
