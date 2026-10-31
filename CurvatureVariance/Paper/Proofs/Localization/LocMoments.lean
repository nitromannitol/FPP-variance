/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Basic
public import CurvatureVariance.Infra.Os.Moments
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:localization`: the third change, the moments

The proof of Lemma `lem:localization`: from `R 1_𝒢 ≤ O₂(C(b))`, and, off
`𝒢`, `R ≤ Cℓ + O₁(C log ℓ)` with `1_{𝒢ᶜ} ≤ O₂(C/log N)`, Hölder's inequality bounds `E[R^p 1_{𝒢ᶜ}]`
by `1` for `N` large, so `E[R^p] ≤ C(b, p)`. `R` has values in `[0, ∞]` and the lower integral needs
no measurability: the bounds are by the measurable majorants.

* `add_rpow_le`: `(a + b)^p ≤ 2^p (a^p + b^p)` in `[0, ∞]`;
* `lintegral_indicator_compl_le`: `P(𝒢ᶜ) ≤ 2 e^{−1/θ²}` from `1_{𝒢ᶜ} ≤ O₂(θ)`;
* `lintegral_rpow_of_good_bad`: the lemma.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Infra.Os

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `(a + b)^p ≤ 2^p (a^p + b^p)` in `[0, ∞]`, `p ≥ 0`. -/
theorem add_rpow_le (a b : ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) :
    (a + b) ^ p ≤ ENNReal.ofReal (2 ^ p) * (a ^ p + b ^ p) := by
  have h1 : a + b ≤ 2 * max a b := by
    rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have h2 : (2 * max a b) ^ p = 2 ^ p * (max a b) ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp
  have h3 : (2 : ℝ≥0∞) ^ p = ENNReal.ofReal (2 ^ p) := by
    rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos (by norm_num)]
  have h4 : (max a b) ^ p ≤ a ^ p + b ^ p := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_self_add
  calc (a + b) ^ p ≤ (2 * max a b) ^ p := ENNReal.rpow_le_rpow h1 hp
    _ = ENNReal.ofReal (2 ^ p) * (max a b) ^ p := by rw [h2, h3]
    _ ≤ _ := mul_le_mul_right h4 _

/-- `1_{𝒢ᶜ} ≤ O₂(θ)` gives `E[1_{𝒢ᶜ}] ≤ 2 e^{−1/θ²}`. -/
theorem lintegral_indicator_compl_le {G : Set Ω} {θ : ℝ}
    (hG : IsOs P 2 θ (Gᶜ.indicator fun _ => (1 : ℝ))) :
    ∫⁻ ω, ENNReal.ofReal (Gᶜ.indicator (fun _ => (1 : ℝ)) ω) ∂P ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / θ) ^ 2)) := by
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (Gᶜ.indicator (fun _ => (1 : ℝ)) ω)) P :=
    hG.1.ennreal_ofReal
  set c := Real.exp ((1 / θ) ^ 2) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hpt : ∀ ω, ENNReal.ofReal (Gᶜ.indicator (fun _ => (1 : ℝ)) ω) * ENNReal.ofReal c ≤
      ENNReal.ofReal (Real.exp ((max (Gᶜ.indicator (fun _ => (1 : ℝ)) ω) 0 / θ) ^ (2 : ℝ))) := by
    intro ω
    by_cases hω : ω ∈ Gᶜ
    · rw [Set.indicator_of_mem hω, ENNReal.ofReal_one, one_mul, max_eq_left zero_le_one,
        Real.rpow_two]
    · rw [Set.indicator_of_notMem hω, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
  have h1 : (∫⁻ ω, ENNReal.ofReal (Gᶜ.indicator (fun _ => (1 : ℝ)) ω) ∂P) * ENNReal.ofReal c ≤ 2 :=
    (lintegral_mul_const'' _ hm).symm.le.trans ((lintegral_mono hpt).trans hG.2)
  have hc' : ENNReal.ofReal c ≠ 0 := by simpa using hc0
  have hc'' : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← ENNReal.le_div_iff_mul_le (Or.inl hc') (Or.inl hc'')] at h1
  refine h1.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos hc0, hc, Real.exp_neg]
  rfl

/-- **The third change.** Let `R` have values in `[0, ∞]`, with `R ≤ Φ` almost surely on `𝒢`, for
`Φ ≤ O₂(θ)`, and `R ≤ L + Λ₊` almost surely, for `Λ ≤ O₁(η)`, and let `1_{𝒢ᶜ} ≤ O₂(τ)`. If the
Hölder product of the bound off `𝒢` is at most `1`, then
`E[R^p] ≤ 2^p (2(1 + ⌈p/2⌉!) θ^p + 1)`. -/
theorem lintegral_rpow_of_good_bad [IsProbabilityMeasure P] {R : Ω → ℝ≥0∞} {G : Set Ω}
    {Φ Λ : Ω → ℝ} {θ η τ L p : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hL : 0 ≤ L)
    (hp : 1 ≤ p) (hΦ : IsOs P 2 θ Φ) (hΛ : IsOs P 1 η Λ)
    (hG : IsOs P 2 τ (Gᶜ.indicator fun _ => (1 : ℝ)))
    (hgood : ∀ᵐ ω ∂P, ω ∈ G → R ω ≤ ENNReal.ofReal (Φ ω))
    (hall : ∀ᵐ ω ∂P, R ω ≤ ENNReal.ofReal (L + max (Λ ω) 0))
    (hnum : 2 ^ (2 * p) * (L ^ (2 * p) + 2 * (1 + ((Nat.ceil (2 * p / 1)).factorial : ℝ)) *
        η ^ (2 * p)) * (2 * Real.exp (-(1 / τ) ^ 2)) ≤ 1) :
    ∫⁻ ω, R ω ^ p ∂P ≤
      ENNReal.ofReal (2 ^ p * (2 * (1 + ((Nat.ceil (p / 2)).factorial : ℝ)) * θ ^ p + 1)) := by
  have hp0 : 0 ≤ p := by linarith only [hp]
  have h2p0 : 0 ≤ 2 * p := by linarith only [hp]
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Gᶜ.indicator (fun _ => (1 : ℝ)) ω) with hgdef
  set H : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (L + max (Λ ω) 0) with hHdef
  have hHm : AEMeasurable H P :=
    (aemeasurable_const.add (hΛ.1.max aemeasurable_const)).ennreal_ofReal
  have hgm : AEMeasurable g P := hG.1.ennreal_ofReal
  -- `R ≤ Φ₊ + H 1_{𝒢ᶜ}`
  have hpt : ∀ᵐ ω ∂P, R ω ^ p ≤ ENNReal.ofReal (2 ^ p) *
      (ENNReal.ofReal (max (Φ ω) 0 ^ p) + H ω ^ p * g ω) := by
    filter_upwards [hgood, hall] with ω h1 h2
    have hsplit : R ω ≤ ENNReal.ofReal (max (Φ ω) 0) + H ω * g ω := by
      by_cases hω : ω ∈ G
      · refine (h1 hω).trans (le_trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_self_add)
      · have : g ω = 1 := by
          simp only [hgdef]
          rw [Set.indicator_of_mem (show ω ∈ Gᶜ from hω), ENNReal.ofReal_one]
        rw [this, mul_one]
        exact h2.trans le_add_self
    refine (ENNReal.rpow_le_rpow hsplit hp0).trans ((add_rpow_le _ _ hp0).trans ?_)
    refine mul_le_mul_right (add_le_add ?_ ?_) _
    · rw [ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hp0]
    · rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
      refine mul_le_mul_right ?_ _
      by_cases hω : ω ∈ Gᶜ
      · simp only [hgdef]
        rw [Set.indicator_of_mem hω, ENNReal.ofReal_one, ENNReal.one_rpow]
      · simp only [hgdef]
        rw [Set.indicator_of_notMem hω, ENNReal.ofReal_zero,
          ENNReal.zero_rpow_of_pos (by linarith only [hp])]
  -- the first term
  have h1 := hΦ.lintegral_pos_rpow_le two_pos hθ hp0
  -- the second term, by the Cauchy–Schwarz inequality
  have hH2 : ∫⁻ ω, (H ω ^ p) ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (2 ^ (2 * p) * (L ^ (2 * p) +
      2 * (1 + ((Nat.ceil (2 * p / 1)).factorial : ℝ)) * η ^ (2 * p))) := by
    have hpt2 : ∀ ω, (H ω ^ p) ^ (2 : ℝ) ≤ ENNReal.ofReal (2 ^ (2 * p)) *
        (ENNReal.ofReal (L ^ (2 * p)) + ENNReal.ofReal (max (Λ ω) 0 ^ (2 * p))) := by
      intro ω
      rw [← ENNReal.rpow_mul, mul_comm p 2]
      have e : H ω = ENNReal.ofReal L + ENNReal.ofReal (max (Λ ω) 0) := by
        simp only [hHdef]
        exact ENNReal.ofReal_add hL (le_max_right _ _)
      rw [e]
      refine (add_rpow_le _ _ h2p0).trans (mul_le_mul_right (add_le_add ?_ ?_) _)
      · rw [ENNReal.ofReal_rpow_of_nonneg hL h2p0]
      · rw [ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) h2p0]
    have h2 := hΛ.lintegral_pos_rpow_le one_pos hη h2p0
    have hmΛ : AEMeasurable (fun ω => ENNReal.ofReal (max (Λ ω) 0 ^ (2 * p))) P :=
      ((hΛ.1.max aemeasurable_const).pow_const _).ennreal_ofReal
    calc ∫⁻ ω, (H ω ^ p) ^ (2 : ℝ) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ (2 * p)) *
          (ENNReal.ofReal (L ^ (2 * p)) + ENNReal.ofReal (max (Λ ω) 0 ^ (2 * p))) ∂P :=
          lintegral_mono hpt2
      _ = ENNReal.ofReal (2 ^ (2 * p)) * (ENNReal.ofReal (L ^ (2 * p)) +
            ∫⁻ ω, ENNReal.ofReal (max (Λ ω) 0 ^ (2 * p)) ∂P) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (2 ^ (2 * p)) * (ENNReal.ofReal (L ^ (2 * p)) +
            ENNReal.ofReal (2 * (1 + ((Nat.ceil (2 * p / 1)).factorial : ℝ)) * η ^ (2 * p))) :=
          mul_le_mul_right (add_le_add le_rfl h2) _
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
  have hg2 : ∫⁻ ω, g ω ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (2 * Real.exp (-(1 / τ) ^ 2)) := by
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) (lintegral_indicator_compl_le hG)
    by_cases hω : ω ∈ Gᶜ
    · simp only [hgdef]
      rw [Set.indicator_of_mem hω, ENNReal.ofReal_one, ENNReal.one_rpow]
    · simp only [hgdef]
      rw [Set.indicator_of_notMem hω, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos two_pos]
  have hHp : AEMeasurable (fun ω => H ω ^ p) P := hHm.pow_const p
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hHp hgm
  simp only [Pi.mul_apply] at hCS
  set A := 2 ^ (2 * p) * (L ^ (2 * p) + 2 * (1 + ((Nat.ceil (2 * p / 1)).factorial : ℝ)) *
    η ^ (2 * p)) with hA
  set E := 2 * Real.exp (-(1 / τ) ^ 2) with hE
  have hA0 : 0 ≤ A := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hsecond : ∫⁻ ω, H ω ^ p * g ω ∂P ≤ 1 := by
    refine hCS.trans ?_
    calc (∫⁻ ω, (H ω ^ p) ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) * (∫⁻ ω, g ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal A) ^ (1 / (2 : ℝ)) * (ENNReal.ofReal E) ^ (1 / (2 : ℝ)) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hH2 (by norm_num))
            (ENNReal.rpow_le_rpow hg2 (by norm_num))
      _ = (ENNReal.ofReal (A * E)) ^ (1 / (2 : ℝ)) := by
          rw [ENNReal.ofReal_mul hA0, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ ≤ (ENNReal.ofReal 1) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hnum) (by norm_num)
      _ = 1 := by simp
  have hm1 : AEMeasurable (fun ω => ENNReal.ofReal (max (Φ ω) 0 ^ p)) P :=
    ((hΦ.1.max aemeasurable_const).pow_const _).ennreal_ofReal
  calc ∫⁻ ω, R ω ^ p ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ p) *
          (ENNReal.ofReal (max (Φ ω) 0 ^ p) + H ω ^ p * g ω) ∂P := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 ^ p) * (∫⁻ ω, ENNReal.ofReal (max (Φ ω) 0 ^ p) ∂P +
          ∫⁻ ω, H ω ^ p * g ω ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hm1]
    _ ≤ ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (2 * (1 + ((Nat.ceil (p / 2)).factorial : ℝ)) *
          θ ^ p) + 1) := mul_le_mul_right (add_le_add h1 hsecond) _
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ p),
          ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one]

end CurvatureVariance.Paper.Localization.Loc
