/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Conditional Jensen for powers, in `[0, ∞]`

If `ψ ∘ old` is a conditional expectation of `G` given the information `a` pulled back by a
measure-preserving map `old` (expressed by the identity `hid` on `a`-measurable sets), then
`∫ ψ ^ p ≤ ∫ G ^ p` for every natural `p ≥ 1`.  This is used for the moments of the conditional
rewards in the proof of Lemma `lem:blocks`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.BlockReplacement

variable {Ω' E : Type*} [mΩ' : MeasurableSpace Ω'] [mE : MeasurableSpace E]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {P : Measure E} [IsProbabilityMeasure P]
  {old : Ω' → E}

omit [IsProbabilityMeasure P'] [IsProbabilityMeasure P] in
/-- Integrating an `a`-measurable function against the identity `hid`. -/
private lemma lintegral_mul_eq_of_setLIntegral_eq (hold : MeasurePreserving old P' P)
    (A : {m : MeasurableSpace E // m ≤ mE}) {ψ : E → ℝ≥0∞} (hψ : Measurable[A.1] ψ)
    {G : Ω' → ℝ≥0∞} (hG : AEMeasurable G P')
    (hid : ∀ S : Set E, MeasurableSet[A.1] S → ∫⁻ x in S, ψ x ∂P = ∫⁻ ω in old ⁻¹' S, G ω ∂P')
    {h : E → ℝ≥0∞} (hh : Measurable[A.1] h) :
    ∫⁻ x, h x * ψ x ∂P = ∫⁻ ω, h (old ω) * G ω ∂P' := by
  have hψm : Measurable[mE] ψ := hψ.mono A.2 le_rfl
  have holdm : Measurable[mΩ', mE] old := hold.measurable
  have hcomp : ∀ {f : E → ℝ≥0∞}, Measurable[A.1] f →
      AEMeasurable (fun ω => f (old ω) * G ω) P' := fun hf =>
    ((hf.mono A.2 le_rfl).comp holdm).aemeasurable.mul hG
  refine @Measurable.ennreal_induction E A.1
    (fun h => ∫⁻ x, h x * ψ x ∂P = ∫⁻ ω, h (old ω) * G ω ∂P') ?_ ?_ ?_ h hh
  · intro c s hs
    have hs' : MeasurableSet s := A.2 _ hs
    have e1 : (fun x => s.indicator (fun _ => c) x * ψ x) = s.indicator (fun x => c * ψ x) := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    have e2 : (fun ω => s.indicator (fun _ => c) (old ω) * G ω) =
        (old ⁻¹' s).indicator (fun ω => c * G ω) := by
      ext ω; by_cases hx : old ω ∈ s <;> simp [hx]
    rw [e1, e2, lintegral_indicator hs', lintegral_indicator (holdm hs'),
      lintegral_const_mul _ hψm, lintegral_const_mul'' _ hG.restrict, hid s hs]
  · intro f g _ hf hg ihf ihg
    have hfm : Measurable f := hf.mono A.2 le_rfl
    have hgm : Measurable g := hg.mono A.2 le_rfl
    have e : ∀ x, (f + g) x * ψ x = f x * ψ x + g x * ψ x := fun x => by
      simp [add_mul]
    have e' : ∀ ω, (f + g) (old ω) * G ω = f (old ω) * G ω + g (old ω) * G ω := fun ω => by
      simp [add_mul]
    simp only [e, e']
    rw [lintegral_add_left (f := fun x => f x * ψ x) (hfm.mul hψm),
      lintegral_add_left' (f := fun ω => f (old ω) * G ω) (hcomp hf), ihf, ihg]
  · intro f hf hmono ih
    have e : ∀ x, (⨆ n, f n x) * ψ x = ⨆ n, f n x * ψ x := fun x => by rw [ENNReal.iSup_mul]
    have e' : ∀ ω, (⨆ n, f n (old ω)) * G ω = ⨆ n, f n (old ω) * G ω := fun ω => by
      rw [ENNReal.iSup_mul]
    simp only [e, e']
    rw [lintegral_iSup (f := fun n x => f n x * ψ x) (fun n => ((hf n).mono A.2 le_rfl).mul hψm)
        (fun m n hmn x => mul_le_mul' (hmono hmn x) le_rfl),
      lintegral_iSup' (f := fun n ω => f n (old ω) * G ω) (fun n => hcomp (hf n))
        (Eventually.of_forall fun ω m n hmn => mul_le_mul' (hmono hmn _) le_rfl)]
    exact iSup_congr ih

omit [IsProbabilityMeasure P'] in
private lemma core (hold : MeasurePreserving old P' P)
    (A : {m : MeasurableSpace E // m ≤ mE}) {ψ : E → ℝ≥0∞} (hψ : Measurable[A.1] ψ)
    {G : Ω' → ℝ≥0∞} (hG : AEMeasurable G P')
    (hid : ∀ S : Set E, MeasurableSet[A.1] S → ∫⁻ x in S, ψ x ∂P = ∫⁻ ω in old ⁻¹' S, G ω ∂P')
    (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ x, ψ x ^ p ∂P ≤ ∫⁻ ω, G ω ^ p ∂P' := by
  have key := fun {h : E → ℝ≥0∞} (hh : Measurable[A.1] h) =>
    lintegral_mul_eq_of_setLIntegral_eq hold A hψ hG hid hh
  rcases Nat.eq_or_lt_of_le hp with rfl | hp2
  · have := key (h := fun _ => 1) measurable_const
    simp only [pow_one]
    exact (by simpa using this : ∫⁻ x, ψ x ∂P = ∫⁻ ω, G ω ∂P').le
  -- truncation
  have hψm : Measurable[mE] ψ := hψ.mono A.2 le_rfl
  have hold_lint : ∀ f : E → ℝ≥0∞, Measurable f → ∫⁻ ω, f (old ω) ∂P' = ∫⁻ x, f x ∂P :=
    fun f hf => by rw [← lintegral_map hf hold.measurable, hold.map_eq]
  have trunc : ∀ n : ℕ, ∫⁻ x, (min (ψ x) n) ^ p ∂P ≤ ∫⁻ ω, G ω ^ p ∂P' := by
    intro n
    set ψn : E → ℝ≥0∞ := fun x => min (ψ x) n with hψn
    have hψn_a : Measurable[A.1] ψn := hψ.min measurable_const
    have hψn_m : Measurable ψn := hψn_a.mono A.2 le_rfl
    set X := ∫⁻ x, ψn x ^ p ∂P with hX
    set B := ∫⁻ ω, G ω ^ p ∂P' with hB
    have hXtop : X ≠ ⊤ := by
      have : X ≤ ∫⁻ _x, (n : ℝ≥0∞) ^ p ∂P := lintegral_mono fun x =>
        pow_le_pow_left' (min_le_right _ _) p
      refine ne_top_of_le_ne_top ?_ this
      simp [ENNReal.pow_eq_top_iff]
    by_cases hX0 : X = 0
    · simp [hX0]
    set q : ℕ := p - 1 with hq
    have hpq : p = q + 1 := by omega
    have step1 : X ≤ ∫⁻ x, ψn x ^ q * ψ x ∂P := by
      refine lintegral_mono fun x => ?_
      rw [hpq, pow_succ]
      exact mul_le_mul' le_rfl (min_le_left _ _)
    have step2 := (key (h := fun x => ψn x ^ q) (hψn_a.pow_const q))
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp2
    have hc := (Real.HolderConjugate.conjExponent hp1).symm
    set r : ℝ := Real.conjExponent p with hr
    have hf : AEMeasurable (fun ω => ψn (old ω) ^ q) P' :=
      ((hψn_m.pow_const q).comp hold.measurable).aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P' hc hf hG
    have hrq : (q : ℝ) * r = p := by
      rw [hr, Real.conjExponent]
      have : (p : ℝ) - 1 = q := by rw [hq]; push_cast [Nat.cast_sub hp]; ring
      have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [this]; field_simp
    have e1 : ∫⁻ ω, (ψn (old ω) ^ q) ^ r ∂P' = X := by
      have : ∀ ω, (ψn (old ω) ^ q) ^ r = ψn (old ω) ^ p := fun ω => by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, hrq, ENNReal.rpow_natCast]
      simp only [this]
      exact hold_lint (fun x => ψn x ^ p) (hψn_m.pow_const p)
    have e2 : ∫⁻ ω, G ω ^ (p : ℝ) ∂P' = B := by simp [hB]
    simp only [Pi.mul_apply] at hH
    rw [e1, e2] at hH
    have hr1 : 1 / r = 1 - 1 / (p : ℝ) := by
      have := hc.symm.inv_add_inv_eq_one
      rw [one_div]; linarith [one_div (p : ℝ), one_div r]
    have hpos : (0 : ℝ) < 1 / p := one_div_pos.2 (by linarith)
    have hr0 : (0 : ℝ) ≤ 1 / r := by
      exact (one_div_pos.2 hc.pos).le
    have hX0' : X ≠ 0 := hX0
    have hsplit : X = X ^ (1 / r) * X ^ (1 / (p : ℝ)) := by
      rw [← ENNReal.rpow_add _ _ hX0' hXtop, hr1]; simp
    have hchain : X ^ (1 / r) * X ^ (1 / (p : ℝ)) ≤ X ^ (1 / r) * B ^ (1 / (p : ℝ)) := by
      rw [← hsplit]
      exact step1.trans (step2.trans_le hH)
    have hne0 : X ^ (1 / r) ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hX0') hXtop).ne'
    have hnetop : X ^ (1 / r) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0 hXtop
    have := (ENNReal.mul_le_mul_iff_right hne0 hnetop).1 hchain
    exact (ENNReal.rpow_le_rpow_iff hpos).1 this
  have hpt : ∀ x, ψ x ^ p ≤ ⨆ n : ℕ, (min (ψ x) n) ^ p := by
    intro x
    by_cases hx : ψ x = ⊤
    · rw [hx, ENNReal.top_pow (by omega), top_le_iff]
      refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
      refine le_iSup_of_le (⌈r⌉₊ + 1) ?_
      rw [min_eq_right le_top, ← Nat.cast_pow]
      have h1 : (r : ℝ≥0∞) ≤ ((⌈r⌉₊ + 1 : ℕ) : ℝ≥0∞) := by
        have : r ≤ ((⌈r⌉₊ + 1 : ℕ) : NNReal) := by
          push_cast; exact (Nat.le_ceil r).trans (le_add_of_nonneg_right zero_le_one)
        exact_mod_cast this
      refine h1.trans ?_
      exact_mod_cast Nat.le_self_pow (by omega) _
    · lift ψ x to NNReal using hx with r hr
      refine le_iSup_of_le ⌈r⌉₊ ?_
      rw [min_eq_left]
      exact_mod_cast Nat.le_ceil r
  calc ∫⁻ x, ψ x ^ p ∂P ≤ ∫⁻ x, ⨆ n : ℕ, (min (ψ x) n) ^ p ∂P := lintegral_mono hpt
    _ = ⨆ n : ℕ, ∫⁻ x, (min (ψ x) n) ^ p ∂P := by
        refine lintegral_iSup (fun n => ?_) (fun m n hmn x => ?_)
        · exact (hψm.min measurable_const).pow_const p
        · exact pow_le_pow_left' (min_le_min le_rfl (by exact_mod_cast hmn)) p
    _ ≤ _ := iSup_le trunc

omit [IsProbabilityMeasure P'] in
/-- **Conditional Jensen for powers** in `[0, ∞]`: if `ψ ∘ old` is a conditional expectation of
`G` given the pulled-back `σ`-algebra `a`, then `∫ ψ ^ p ≤ ∫ G ^ p` for `p ≥ 1`. -/
theorem lintegral_pow_le_of_setLIntegral_eq (hold : MeasurePreserving old P' P)
    {a : MeasurableSpace E} (ha : a ≤ mE) {ψ : E → ℝ≥0∞} (hψ : Measurable[a] ψ)
    {G : Ω' → ℝ≥0∞} (hG : AEMeasurable G P')
    (hid : ∀ A : Set E, MeasurableSet[a] A → ∫⁻ x in A, ψ x ∂P = ∫⁻ ω in old ⁻¹' A, G ω ∂P')
    (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ x, ψ x ^ p ∂P ≤ ∫⁻ ω, G ω ^ p ∂P' := by
  exact core (mE := mE) hold ⟨a, ha⟩ hψ hG hid p hp

end IsotropicVariance.Paper.Proofs.BlockReplacement
