/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.ProfilesShort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proposition `prop:profiles`: the statement `ProfilesStatement`

The proof in the paper: for `N/4 < s ≤ N`, the proof for `s ≤ N/4` applies, with
equation `eq:parent` in place of equation `eq:premise` at the lengths `r ± s/8 ∈ [N/8, 2N]`.
-/

@[expose] public section

open MeasureTheory Set Metric

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os

variable {m : ℕ}

/-- The input of `profile_bounds_of` on the line for `N/4 < s ≤ N`: equation `eq:parent` at lengths
between `7s/8 ≥ N/8` and `2s ≤ 2N`. -/
lemma line_of_parent {X : Setting.{u} m} (hm : 1 ≤ m) {K : ℕ} (hK : 10 ≤ K) {A N CP : ℝ}
    (hA : 1 ≤ A) (hCP : 0 ≤ CP)
    (hpar : ∀ ℓ : ℝ, 1 / 8 * N ≤ ℓ → ℓ ≤ 2 * N →
      IsOs X.P 1 (Q K A ℓ / 100) fun ω => |X.TRV ℓ ω - ℓ| - CP * Q K A ℓ)
    {s : ℝ} (hs : 8 ≤ s) (hNs : N / 4 ≤ s) (hsN : s ≤ N) (a c : Pt m)
    (h1 : 7 / 8 * s ≤ dist a c) (h2 : dist a c ≤ 2 * s) :
    IsOs X.P 1 (2 * parentStepConst CP * Q K A s) fun ω => |X.passTime ω a c - dist a c| := by
  have hspos : 0 < s := by linarith only [hs]
  have hPC := one_le_parentStepConst hCP
  have hQd : 0 < Q K A (dist a c) :=
    Q_pos (by linarith only [hA]) (by linarith only [h1, hspos])
  have H := lineAbs_of_parent hm hK hA hCP hpar a c (by linarith only [h1, hs])
    (by linarith only [h1, hNs, hs, hsN]) (by linarith only [h2, hsN])
  refine H.mono_scale zero_le_one (by positivity) ?_
  calc parentStepConst CP * Q K A (dist a c) ≤ parentStepConst CP * (2 * Q K A s) :=
        mul_le_mul_of_nonneg_left
          (Q_le_two_mul hK (by linarith only [hA]) hspos dist_nonneg h2) (by linarith only [hPC])
    _ = 2 * parentStepConst CP * Q K A s := by ring

/-- **Proposition `prop:profiles`, equation `eq:profiles`**, from Lemma `lem:tree`, Lemma
`lem:slab`, the part `s ≤ N/4` of the proposition, and Lemma `lem:parent`. -/
theorem profilesStatement_of (hT : Contracts.TreeStatement.{u})
    (hS : Contracts.SlabStatement.{u}) (hPs : Contracts.ProfilesShortStatement.{u})
    (hPa : Contracts.ParentStatement.{u}) : Contracts.ProfilesStatement.{u} := by
  intro m hm X hX b hb Cstar hCstar
  obtain ⟨Bd, hBd0, hBd⟩ := exists_upperBound X
  obtain ⟨Ct, hCt, hT'⟩ := hT m hm X hX
  obtain ⟨CS, hCS, hS', -⟩ := hS m hm X hX b hb
  obtain ⟨C₁, hC₁, hPs'⟩ := hPs m hm X hX b hb Cstar hCstar
  obtain ⟨CP, hCP, hPa'⟩ := hPa m hm X hX Cstar hCstar 2 two_pos
  have hCl : 0 < 2 * parentStepConst CP := by
    have := one_le_parentStepConst hCP.le
    linarith only [this]
  have hC₂ : 0 < profileConst m Ct (2 * parentStepConst CP) := by
    unfold profileConst
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  set C₂ := profileConst m Ct (2 * parentStepConst CP) with hC₂def
  refine ⟨C₁ + C₂ + 1, by positivity, fun c₁ hc₁ K => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hPs' c₁ hc₁ K
  obtain ⟨N₂, hN₂⟩ := hPa' (1 / 8) (by norm_num) K
  obtain ⟨N₃, hN₃⟩ := exists_profile_thresholds m Cstar CS c₁ hc₁
  refine ⟨max N₁ (max N₂ N₃), fun A N hN hst s hs1 hs2 p hp => ?_⟩
  obtain ⟨hNa, hN4⟩ := max_le_iff.mp hN
  obtain ⟨hNb, hNc⟩ := max_le_iff.mp hN4
  obtain ⟨hK, hA, hN2, hP, hReg⟩ := id hst
  have hA0 : 0 < A := by linarith only [hA]
  obtain ⟨hs256, hW, hlog⟩ := hN₃ K hK A N hA hNc hReg s hs1 hs2
  have hQ : 0 < Q K A s := Q_pos hA0 (by linarith only [hs256])
  by_cases hsN : s ≤ N / 4
  · obtain ⟨H1, H2⟩ := hN₁ A N hNa hst s hs1 hsN p hp
    have hle : C₁ * Q K A s ≤ (C₁ + C₂ + 1) * Q K A s :=
      mul_le_mul_of_nonneg_right (by linarith only [hC₂]) hQ.le
    exact ⟨IsOs.mono_scale H1 zero_le_one (by positivity) hle,
      IsOs.mono_scale H2 zero_le_one (by positivity) hle⟩
  · obtain ⟨HT, HD⟩ := profile_bounds_of X hb hBd hBd0.le hCS hS' hK hA hs256 hCt hCl hW hlog
      (fun x e he B hB hdiam hline => hT' K A N hK hA hN2 hP (s / 16) (by linarith only [hs256])
        (by linarith only [hs2, hN2]) x e he B hB hdiam hline)
      (line_of_parent hm hK hA hCP.le (hN₂ A N hNb hst) (by linarith only [hs256])
        (by linarith only [not_le.mp hsN]) hs2) p hp
    have h1 : C₂ * Q K A s ≤ (C₁ + C₂ + 1) * Q K A s :=
      mul_le_mul_of_nonneg_right (by linarith only [hC₁]) hQ.le
    have h2 : (C₂ + 1) * Q K A s ≤ (C₁ + C₂ + 1) * Q K A s :=
      mul_le_mul_of_nonneg_right (by linarith only [hC₁]) hQ.le
    exact ⟨HT.mono_scale zero_le_one (by positivity) h1,
      HD.mono_scale zero_le_one (by positivity) h2⟩

end IsotropicVariance.Paper.Proofs.Profiles
