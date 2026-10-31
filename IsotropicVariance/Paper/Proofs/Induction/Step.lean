/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Induction.Improvement
public import IsotropicVariance.Paper.Proofs.Induction.Main
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The induction step, Proposition `prop:induction`

`improvementStatement_of_contracts` proves `ImprovementStatement` as the paper does, from the
statements of Lemma `lem:classical`, equation `eq:parent`, Proposition `prop:gain` and Lemma
`lem:smallmean`.

* **The classical case** (Section `sec:induction`). By equation `eq:classical`,
  `|T_N − N| ≤ O_1(C (N log(2+N))^{1/2})` (`exists_isOs_abs_TRV_sub`). This gives equation
  `eq:improvement` if `Q_N ≥ 2C (N log(2+N))^{1/2}`. Otherwise equation `eq:regime` holds with
  this constant, `C_* = 2C`, which is chosen before `K`.
* **The regime** (the proof of Proposition `prop:induction`, `improvement_of_regime`). Let
  `t ∈ [N/8, N]`.
  - Equation `eq:parent` bounds `E exp(8|T_t − E T_t|/Q_t)` independently of `A` and `K`, and
    Cauchy–Schwarz bounds `E exp(4|T_t − E T_t|/Q_t)` by `1 + C Var(T_t/Q_t)^{1/2}`
    (`isOs_abs_TRV_sub_mean`).
  - Proposition `prop:gain` with `n = t/K` fixes `K`, so that the right side is at most two and
    `Var(T_t/Q_t)` is as small as Lemma `lem:smallmean` requires.
  - With `t = N`, `|T_N − E T_N| ≤ O_1(Q_N/4)`.
  - Lemma `lem:smallmean` at `s = N/4` and subadditivity give `0 ≤ E T_N − N ≤ Q_N/25`
    (`mean_sub_le_of_quarter`).
  - Equation `eq:sum` gives equation `eq:improvement`.

`mainSettingStatement_of_contracts` and `mainSettingExpStatement_of_contracts` compose the theorem
with the induction on the length, as in the proof of Theorem `thm:general`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

open IsotropicVariance.Paper.Proofs.Profiles (Q_pos)
namespace IsotropicVariance.Paper.Proofs.Induction

open Infra.TimeConstant

/-- **The classical bound on `|T_N − N|`** (Section `sec:induction`): by equation `eq:classical`,
there is `C > 0` with `|T_N − N| ≤ O_1(C (N log(2+N))^{1/2})` for every `N ≥ 1`. In terms of the
constant `C₀` of equation `eq:classical`, `C = 4C₀`. -/
theorem exists_isOs_abs_TRV_sub (hCl : Contracts.ClassicalBoundsStatement.{u}) {m : ℕ}
    (hm : 1 ≤ m) (X : Setting.{u} m) (hX : X.IsNormalized) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      Cited.IsOs X.P 1 (C * Real.sqrt (N * Real.log (2 + N))) (fun ω => |X.TRV N ω - N|) := by
  obtain ⟨C₀, hC₀, hcl⟩ := hCl m hm X hX
  refine ⟨4 * C₀, by positivity, fun N hN => ?_⟩
  obtain ⟨hO2, hmean0, hmeanle⟩ := hcl N hN
  have hN0 : 0 < N := by linarith only [hN]
  have hlog : 1 ≤ Real.log (2 + N) := Profiles.one_le_log_two_add hN
  set R : ℝ := Real.sqrt (N * Real.log (2 + N)) with hR_def
  have hR : 0 < R := Real.sqrt_pos.2 (mul_pos hN0 (by linarith only [hlog]))
  have hsqrt : Real.sqrt N ≤ R := Real.sqrt_le_sqrt (le_mul_of_one_le_right hN0.le hlog)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith only [this]
  have hθ : 0 < 8 * C₀ * R := by positivity
  have h₁ : 2 * (C₀ * Real.sqrt N) ≤ 8 * C₀ * R / 4 := by
    have := mul_le_mul_of_nonneg_left hsqrt hC₀.le
    linarith only [this]
  have h₃ : X.mean N - N ≤ 8 * C₀ * R / 4 * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hlog2 (mul_pos hC₀ hR).le
    linarith only [this, hmeanle]
  have h := isOs_abs_sub_of_parts (integrable_TRV X N).aemeasurable hθ
    (isOs_one_of_isOs_two (by positivity) h₁ hO2) hmean0 h₃
  rwa [show 8 * C₀ * R / 2 = 4 * C₀ * R by ring] at h

/-- **The fluctuation at `t`** (proof of Proposition `prop:induction`): if
`|T_t − t| ≤ Cθ + O_1(θ/100)`, then `E exp(8|T_t − E T_t|/θ) ≤ 2e^{16C + 1}`, and Cauchy–Schwarz
bounds `E exp(4|T_t − E T_t|/θ)` by `1 + 4 (v · 2e^{16C + 1})^{1/2}` if `Var T_t ≤ vθ²`. If `v` is
small, depending on `C`, this is at most two, that is, `|T_t − E T_t| ≤ O_1(θ/4)`. -/
theorem isOs_abs_TRV_sub_mean {m : ℕ} (X : Setting.{u} m) {t θ C v : ℝ} (hθ : 0 < θ)
    (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hpar : Cited.IsOs X.P 1 (θ / 100) (fun ω => |X.TRV t ω - t| - C * θ))
    (hvar : evariance (X.TRV t) X.P ≤ ENNReal.ofReal (v * θ ^ 2))
    (hvB : 16 * v * (2 * Real.exp (16 * C + 1)) ≤ 1) :
    Cited.IsOs X.P 1 (θ / 4) (fun ω => |X.TRV t ω - X.mean t|) :=
  isOs_abs_sub_integral_of_evariance_le (memLp_TRV X t) hθ hv
    (lintegral_exp_abs_sub_integral_le (integrable_TRV X t) hθ hC hpar) hvar hvB

/-- **The mean at `N`** (proof of Proposition `prop:induction`): subadditivity gives
`E T_N − N ≤ 4 (E T_{N/4} − N/4)`, which is at most `Q_N/25` if `E T_{N/4} − N/4 ≤ Q_{N/4}/100`. -/
theorem mean_sub_le_of_quarter {m : ℕ} (X : Setting.{u} m) {K : ℕ} (hK : 10 ≤ K) {A N : ℝ}
    (hA : 0 < A) (hN : 0 < N) (h : X.mean (N / 4) - N / 4 ≤ Q K A (N / 4) / 100) :
    X.mean N - N ≤ Q K A N / 25 := by
  have hsub1 := mean_subadditive X (N / 2) (N / 2)
  have hsub2 := mean_subadditive X (N / 4) (N / 4)
  rw [add_halves] at hsub1
  rw [show N / 4 + N / 4 = N / 2 by ring] at hsub2
  have hQ : Q K A (N / 4) ≤ Q K A N :=
    Profiles.Q_mono hK hA.le (by linarith only [hN]) (by linarith only [hN])
  linarith only [hsub1, hsub2, hQ, h]

/-- **The proof of Proposition `prop:induction` in the regime**: the
bounds of equation `eq:parent` and Proposition `prop:gain` for `t ∈ [N/8, N]`, with `v` small, and
Lemma `lem:smallmean` at `s = N/4`, give equation `eq:improvement`. -/
theorem improvement_of_regime {m : ℕ} {X : Setting.{u} m} (hX : X.IsNormalized) {K : ℕ}
    (hK : 10 ≤ K) {A N C v δ : ℝ} (hA : 1 ≤ A) (hN : 2 ≤ N) (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hvB : 16 * v * (2 * Real.exp (16 * C + 1)) ≤ 1) (hvδ : v ≤ δ)
    (hpar : ∀ t : ℝ, N / 8 ≤ t → t ≤ N →
      Cited.IsOs X.P 1 (Q K A t / 100) (fun ω => |X.TRV t ω - t| - C * Q K A t))
    (hvar : ∀ t : ℝ, N / 8 ≤ t → t ≤ N →
      evariance (X.TRV t) X.P ≤ ENNReal.ofReal (v * Q K A t ^ 2))
    (hsm : (∀ r : ℝ, N / 4 ≤ r → r ≤ 2 * (N / 4) →
      evariance (fun ω => X.TRV r ω / Q K A r) X.P ≤ ENNReal.ofReal δ) →
      X.mean (N / 4) - N / 4 ≤ Q K A (N / 4) / 100) :
    Cited.IsOs X.P 1 (Q K A N / 2) (fun ω => |X.TRV N ω - N|) := by
  have hN0 : 0 < N := by linarith only [hN]
  have hA0 : 0 < A := by linarith only [hA]
  have hQ : 0 < Q K A N := Q_pos hA0 hN0
  have hN8 : N / 8 ≤ N := by linarith only [hN0]
  -- `t = N`
  have hfl : Cited.IsOs X.P 1 (Q K A N / 4) (fun ω => |X.TRV N ω - X.mean N|) :=
    isOs_abs_TRV_sub_mean X hQ hC hv (hpar N hN8 le_rfl) (hvar N hN8 le_rfl) hvB
  -- `Var(T_r/Q_r)` is small for `r ∈ [N/4, N/2]`
  have hsN := hsm fun r hr₁ hr₂ =>
    (evariance_div_le (Q_pos hA0 (by linarith only [hr₁, hN0]))
      (hvar r (by linarith only [hr₁, hN0]) (by linarith only [hr₂, hN0]))).trans
      (ENNReal.ofReal_le_ofReal hvδ)
  have hmean := mean_sub_le_of_quarter X hK hA0 hN0 hsN
  have hlog2 : (4 : ℝ) / 25 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith only [this]
  have h25 : Q K A N / 25 ≤ Q K A N / 4 * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hlog2 (div_pos hQ four_pos).le
    linarith only [this]
  exact isOs_abs_sub_of_parts (integrable_TRV X N).aemeasurable hQ hfl
    (sub_nonneg.2 (mean_ge_of_isNormalized X hX hN0.le)) (hmean.trans h25)

/-- **Proposition `prop:induction`**, from
equation `eq:classical` (Lemma `lem:classical`), equation `eq:parent` (Lemma `lem:parent`),
Proposition `prop:gain` and Lemma `lem:smallmean`. Equation `eq:regime` is read with
`C_* = 2C`, for the constant `C` of `|T_N − N| ≤ O_1(C (N log(2+N))^{1/2})`. -/
theorem improvementStatement_of_contracts (hCl : Contracts.ClassicalBoundsStatement.{u})
    (hPar : Contracts.ParentStatement.{u}) (hGain : Contracts.GainStatement.{u})
    (hSmall : Contracts.SmallMeanStatement.{u}) : Contracts.ImprovementStatement.{u} := by
  intro m hm X hX
  obtain ⟨C, hC, hcl⟩ := exists_isOs_abs_TRV_sub hCl hm X hX
  have hCstar : 0 < 2 * C := by positivity
  obtain ⟨δ, hδ, hsm⟩ := hSmall m hm X hX (2 * C) hCstar
  obtain ⟨Cp, hCp, hpar⟩ := hPar m hm X hX (2 * C) hCstar 1 one_pos
  obtain ⟨o, ho, K₀, hgain⟩ := hGain m hm X hX (2 * C) hCstar
  set B : ℝ := 2 * Real.exp (16 * Cp + 1) with hB_def
  have hB : 0 < B := by positivity
  -- the choice of `K`
  have hsmall_o : ∀ᶠ K in atTop, o K < min δ (1 / (16 * B)) :=
    ho.eventually (gt_mem_nhds (lt_min hδ (by positivity)))
  obtain ⟨K, hoK, hKge⟩ := (hsmall_o.and (eventually_ge_atTop (max 10 K₀))).exists
  have hK10 : 10 ≤ K := (le_max_left _ _).trans hKge
  have hKK₀ : K₀ ≤ K := (le_max_right _ _).trans hKge
  have hv0 : 0 ≤ max (o K) 0 := le_max_right _ _
  have hvδ : max (o K) 0 ≤ δ := max_le (hoK.le.trans (min_le_left _ _)) hδ.le
  have hvB : 16 * max (o K) 0 * B ≤ 1 := by
    have h1 : max (o K) 0 ≤ 1 / (16 * B) :=
      max_le (hoK.le.trans (min_le_right _ _)) (by positivity)
    calc 16 * max (o K) 0 * B = (16 * B) * max (o K) 0 := by ring
      _ ≤ (16 * B) * (1 / (16 * B)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp
  -- the thresholds on `N`, which depend only on `K`
  obtain ⟨Ng, hg⟩ := hgain K hKK₀ hK10
  obtain ⟨Np, hp⟩ := hpar (1 / 8) (by norm_num) K
  obtain ⟨Ns, hs⟩ := hsm K hK10
  refine ⟨K, hK10, max 2 (max Ng (max Np Ns)), le_max_left _ _, fun A N hA hN hprem => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNg : Ng ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNp : Np ≤ N :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hNs : Ns ≤ N :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  by_cases hreg : Regime (2 * C) K A N
  · have hst : Standing X (2 * C) K A N := ⟨hK10, hA, hN2, hprem, hreg⟩
    refine improvement_of_regime hX hK10 hA hN2 hCp.le hv0 hvB hvδ (fun t ht₁ ht₂ => ?_)
      (fun t ht₁ ht₂ => ?_) (hs A N hNs hst (N / 4) (by linarith only [hN2]) le_rfl)
    · exact hp A N hNp hst t (by linarith only [ht₁]) (by linarith only [ht₂])
    · exact (hg A N hNg hst t ht₁ ht₂).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)))
  · -- the classical case: `Q_N ≥ 2C (N log(2+N))^{1/2}`
    have hreg' : 2 * C * Real.sqrt (N * Real.log (2 + N)) < Q K A N := lt_of_not_ge hreg
    have hN1 : (1 : ℝ) ≤ N := by linarith only [hN2]
    have hlog := Profiles.one_le_log_two_add hN1
    have hR : 0 < Real.sqrt (N * Real.log (2 + N)) :=
      Real.sqrt_pos.2 (mul_pos (by linarith only [hN2]) (by linarith only [hlog]))
    exact Cited.IsOs.mono_scale (s := 1) (hcl N hN1) zero_le_one (mul_pos hC hR)
      (by linarith only [hreg'])

/-- **Theorem `thm:general` over the noise interface**, with the variance bound, from Proposition
`prop:induction` and the induction on the length. -/
theorem mainSettingStatement_of_contracts (hCl : Contracts.ClassicalBoundsStatement.{u})
    (hPar : Contracts.ParentStatement.{u}) (hGain : Contracts.GainStatement.{u})
    (hSmall : Contracts.SmallMeanStatement.{u}) : Contracts.MainSettingStatement.{u} :=
  mainSettingStatement_of (improvementStatement_of_contracts hCl hPar hGain hSmall)
    inductionStatement_holds

/-- **Theorem `thm:general` over the noise interface**, with its conclusion, from Proposition
`prop:induction` and the induction on the length. -/
theorem mainSettingExpStatement_of_contracts (hCl : Contracts.ClassicalBoundsStatement.{u})
    (hPar : Contracts.ParentStatement.{u}) (hGain : Contracts.GainStatement.{u})
    (hSmall : Contracts.SmallMeanStatement.{u}) : Contracts.MainSettingExpStatement.{u} :=
  mainSettingExpStatement_of (improvementStatement_of_contracts hCl hPar hGain hSmall)
    inductionStatement_holds

end IsotropicVariance.Paper.Proofs.Induction
