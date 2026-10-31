/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Entropy.Basic
public import IsotropicVariance.Infra.Entropy.Splice
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Tensorization of entropy

For the product `P = Measure.infinitePi μ` of probability measures over a countable index set
and a measurable integrable `g ≥ 0`,
`Ent_P g ≤ ∑ᵢ E_P [Ent_{μ i} g]`, where `Ent_{μ i} g` is the entropy of `g` in the coordinate `i`
with the other coordinates fixed (`coordEntropy`). The inequality is stated for the extended
entropy `eentropy` with values in `[0, ∞]`, so that no integrability of `g log g` is assumed.

The proof is the standard martingale argument (see Ledoux, *The concentration of measure
phenomenon*, 2001, Proposition 5.6, cited for this step by Benaïm–Rossignol). Enumerate the
coordinates by an injection `e : ι → ℕ` and let `g_n` integrate out all coordinates outside the
first `n`. The chain rule (`lintegral_entropyDensity_eq`) splits
`∫ ψ_m(g_{n+1})` into the entropy of `g_{n+1}` in the `n`-th coordinate plus `∫ ψ_m(g_n)`, and
convexity of the entropy under averaging (`eentropy_integral_le`) bounds that coordinate entropy
by the coordinate entropy of `g`. Summing gives the bound for `g_n`, and Lévy's upward theorem
with Fatou's lemma passes to `g`.

## Main results

* `lintegral_entropyDensity_eq`: the chain rule `∫ ψ_m(s) = Ent s + ψ_m(∫ s)`.
* `eentropy_integral_le`: `Ent_ν (∫ s_z dρ(z)) ≤ ∫ Ent_ν (s_z) dρ(z)`.
* `eentropy_le_tsum_coordEntropy`: tensorization over a countable product.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace IsotropicVariance.Infra.Entropy

/-! ### Two scalar facts -/

/-- The supporting-plane inequality for the Bregman integrand: `ψ_m(a) ≥ a log r + m - r m`. -/
theorem entropyDensity_ge {a m r : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) (hr : 0 < r)
    (h0 : m = 0 → a = 0) : a * log r + m - r * m ≤ entropyDensity m a := by
  rcases hm.eq_or_lt with rfl | hm
  · simp [h0 rfl, entropyDensity]
  have h := mul_log_ge a ha (mul_pos hr hm)
  rw [log_mul hr.ne' hm.ne'] at h
  unfold entropyDensity
  linarith

theorem continuous_entropyDensity (m : ℝ) : Continuous (entropyDensity m) := by
  unfold entropyDensity
  have := Real.continuous_mul_log
  fun_prop

theorem measurable_entropyDensity : Measurable fun p : ℝ × ℝ => entropyDensity p.1 p.2 := by
  unfold entropyDensity
  have h1 : Measurable fun p : ℝ × ℝ => p.2 * log p.2 :=
    Real.continuous_mul_log.measurable.comp measurable_snd
  have h2 : Measurable fun p : ℝ × ℝ => p.2 * log p.1 :=
    measurable_snd.mul (Real.measurable_log.comp measurable_fst)
  exact ((h1.sub h2).sub measurable_snd).add measurable_fst

/-! ### The chain rule and convexity on a probability space -/

section General

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

theorem ofReal_integral_le_lintegral_ofReal {f : Y → ℝ} (hf : Integrable f ν) :
    ENNReal.ofReal (∫ y, f y ∂ν) ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂ν := by
  calc ENNReal.ofReal (∫ y, f y ∂ν) ≤ ENNReal.ofReal (∫ y, max (f y) 0 ∂ν) :=
        ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part fun y => le_max_left _ _)
    _ = ∫⁻ y, ENNReal.ofReal (max (f y) 0) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part (ae_of_all _ fun y => le_max_right _ _)
    _ = ∫⁻ y, ENNReal.ofReal (f y) ∂ν := by
        congr 1; funext y; rcases le_total (f y) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]

/-- If the integral of the Bregman integrand is finite then `s log s` is integrable. -/
theorem integrable_mul_log_of_lintegral_ne_top {s : Y → ℝ} {m : ℝ} [IsFiniteMeasure ν]
    (hm : 0 < m) (hs0 : 0 ≤ᵐ[ν] s) (hs : Integrable s ν)
    (h : ∫⁻ y, ENNReal.ofReal (entropyDensity m (s y)) ∂ν ≠ ∞) :
    Integrable (fun y => s y * log (s y)) ν := by
  have h1 : AEStronglyMeasurable (fun y => s y * log (s y)) ν :=
    (hs.aestronglyMeasurable.aemeasurable.mul
      (Real.measurable_log.comp_aemeasurable hs.aestronglyMeasurable.aemeasurable))
      |>.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun y => entropyDensity m (s y)) ν := by
    unfold entropyDensity
    exact ((h1.sub (hs.aestronglyMeasurable.mul_const _)).sub hs.aestronglyMeasurable).add
      aestronglyMeasurable_const
  have hint : Integrable (fun y => entropyDensity m (s y)) ν :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (hs0.mono fun y hy => entropyDensity_nonneg hm hy)).1 h
  have : (fun y => s y * log (s y)) = fun y => entropyDensity m (s y) + s y * log m + s y - m := by
    funext y; unfold entropyDensity; ring
  rw [this]
  exact ((hint.add (hs.mul_const _)).add hs).sub (integrable_const m)

variable [IsProbabilityMeasure ν]

/-- **Chain rule** on one factor: `∫ ψ_m(s) dν = Ent_ν s + ψ_m(∫ s dν)` for `m > 0`. -/
theorem lintegral_entropyDensity_eq {s : Y → ℝ} {m : ℝ} (hm : 0 < m) (hs0 : ∀ y, 0 ≤ s y)
    (hs : Integrable s ν) :
    ∫⁻ y, ENNReal.ofReal (entropyDensity m (s y)) ∂ν =
      eentropy ν s + ENNReal.ofReal (entropyDensity m (∫ y, s y ∂ν)) := by
  have hs0' : 0 ≤ᵐ[ν] s := ae_of_all _ hs0
  by_cases hlog : Integrable (fun y => s y * log (s y)) ν
  · rw [eentropy_eq_ofReal_entropy hs0' hs hlog, ← ENNReal.ofReal_add (entropy_nonneg hs0' hs hlog)
      (entropyDensity_nonneg hm (integral_nonneg hs0)),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_entropyDensity m hs hlog)
        (ae_of_all _ fun y => entropyDensity_nonneg hm (hs0 y)),
      integral_entropyDensity m hs hlog]
    congr 1
    unfold Cited.entropy entropyDensity
    ring
  · rw [eentropy_eq_top_of_not_integrable hs0' hs hlog, top_add]
    by_contra h
    exact hlog (integrable_mul_log_of_lintegral_ne_top hm hs0' hs h)

variable {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z} [IsProbabilityMeasure ρ]

/-- **Convexity of entropy under averaging**: `Ent_ν (∫ s_z dρ(z)) ≤ ∫ Ent_ν (s_z) dρ(z)`. -/
theorem eentropy_integral_le {s : Z → Y → ℝ} (hs0 : ∀ z y, 0 ≤ s z y)
    (hsm : Measurable (Function.uncurry s)) (hsi : Integrable (Function.uncurry s) (ρ.prod ν)) :
    eentropy ν (fun y => ∫ z, s z y ∂ρ) ≤ ∫⁻ z, eentropy ν (s z) ∂ρ := by
  set G : Y → ℝ := fun y => ∫ z, s z y ∂ρ with hG_def
  set m : Z → ℝ := fun z => ∫ y, s z y ∂ν with hm_def
  have hG0 : ∀ y, 0 ≤ G y := fun y => integral_nonneg fun z => hs0 z y
  have hGi : Integrable G ν := hsi.integral_prod_right
  have hmi : Integrable m ρ := hsi.integral_prod_left
  have hm0 : ∀ z, 0 ≤ m z := fun z => integral_nonneg fun y => hs0 z y
  have hmm : Measurable m := hsm.stronglyMeasurable.integral_prod_right'.measurable
  set M := ∫ y, G y ∂ν with hM_def
  have hMm : ∫ z, m z ∂ρ = M :=
    (integral_prod _ hsi).symm.trans (integral_prod_symm _ hsi)
  rcases (integral_nonneg hG0 : 0 ≤ M).eq_or_lt with hM | hM
  · have hz := integral_eq_zero_imp_ae_zero (ae_of_all _ hG0) hGi hM.symm
    have hM0 : M = 0 := hM.symm
    have : eentropy ν G = 0 := by
      rw [eentropy, ← hM_def, hM0]
      refine (lintegral_congr_ae (hz.mono fun y hy => ?_)).trans lintegral_zero
      simp [hy]
    rw [this]; exact bot_le
  -- the right side, as an iterated integral in the other order
  have hF : Measurable fun p : Z × Y => ENNReal.ofReal (entropyDensity (m p.1) (s p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_entropyDensity.comp ((hmm.comp measurable_fst).prodMk hsm))
  have hswap : ∫⁻ z, eentropy ν (s z) ∂ρ =
      ∫⁻ y, ∫⁻ z, ENNReal.ofReal (entropyDensity (m z) (s z y)) ∂ρ ∂ν :=
    lintegral_lintegral_swap hF.aemeasurable
  rw [hswap, eentropy, ← hM_def]
  -- the null set where `m z = 0` but `s z y ≠ 0`
  have hnull : ∀ᵐ y ∂ν, ∀ᵐ z ∂ρ, m z = 0 → s z y = 0 := by
    have hmeasSet : MeasurableSet {p : Z × Y | m p.1 = 0 → s p.1 p.2 = 0} := by
      have h1 : MeasurableSet {p : Z × Y | m p.1 ≠ 0} :=
        (measurableSet_singleton 0).compl.preimage (hmm.comp measurable_fst)
      have h2 : MeasurableSet {p : Z × Y | s p.1 p.2 = 0} :=
        (measurableSet_singleton 0).preimage hsm
      have e : {p : Z × Y | m p.1 = 0 → s p.1 p.2 = 0} =
          {p : Z × Y | m p.1 ≠ 0} ∪ {p : Z × Y | s p.1 p.2 = 0} := by
        ext p; simp only [Set.mem_union]; exact imp_iff_not_or
      rw [e]; exact h1.union h2
    refine (Measure.ae_ae_comm hmeasSet).1 ?_
    filter_upwards [hsi.prod_right_ae] with z hz
    by_cases hmz0 : m z = 0
    · filter_upwards [integral_eq_zero_imp_ae_zero (ae_of_all _ (hs0 z)) hz hmz0] with y hy _
      simpa using hy
    · exact ae_of_all _ fun y h => absurd h hmz0
  refine lintegral_mono_ae ?_
  filter_upwards [hnull, hsi.prod_left_ae] with y hy hyi
  rcases (hG0 y).eq_or_lt with hGy | hGy
  · -- `G y = 0`: then `s z y = 0` for almost every `z`
    have hz := integral_eq_zero_imp_ae_zero (ae_of_all _ fun z => hs0 z y) hyi hGy.symm
    rw [← hGy, entropyDensity_zero_right]
    refine le_of_eq ?_
    calc ENNReal.ofReal M = ENNReal.ofReal (∫ z, m z ∂ρ) := by rw [hMm]
      _ = ∫⁻ z, ENNReal.ofReal (m z) ∂ρ :=
          ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all _ hm0)
      _ = ∫⁻ z, ENNReal.ofReal (entropyDensity (m z) (s z y)) ∂ρ := by
          refine lintegral_congr_ae (hz.mono fun z hzy => ?_)
          have h0 : s z y = 0 := by simpa using hzy
          simp only [h0, entropyDensity_zero_right]
  · set r := G y / M with hr_def
    have hr : 0 < r := div_pos hGy hM
    have i1 : Integrable (fun z => s z y * log r) ρ := hyi.mul_const _
    have i2 : Integrable (fun z => s z y * log r + m z) ρ := i1.add hmi
    have i3 : Integrable (fun z => r * m z) ρ := hmi.const_mul _
    have hlow : Integrable (fun z => s z y * log r + m z - r * m z) ρ := i2.sub i3
    calc ENNReal.ofReal (entropyDensity M (G y))
        = ENNReal.ofReal (∫ z, (s z y * log r + m z - r * m z) ∂ρ) := by
          congr 1
          rw [integral_sub i2 i3, integral_add i1 hmi, integral_mul_const, integral_const_mul, hMm]
          have hGd : ∫ z, s z y ∂ρ = G y := rfl
          have hM' : M ≠ 0 := hM.ne'
          rw [hGd, hr_def, log_div hGy.ne' hM', div_mul_cancel₀ _ hM']
          unfold entropyDensity
          ring
      _ ≤ ∫⁻ z, ENNReal.ofReal (s z y * log r + m z - r * m z) ∂ρ :=
          ofReal_integral_le_lintegral_ofReal hlow
      _ ≤ ∫⁻ z, ENNReal.ofReal (entropyDensity (m z) (s z y)) ∂ρ := by
          refine lintegral_mono_ae (hy.mono fun z hz => ?_)
          exact ENNReal.ofReal_le_ofReal (entropyDensity_ge (hs0 z y) (hm0 z) hr hz)

end General

/-! ### Coordinate entropies on a product space -/

section Product

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)] [DecidableEq ι]

variable (μ) in
/-- `Ent_{μ i} g (x)`: the extended entropy of `g` in the coordinate `i`, the other coordinates
fixed at those of `x`. -/
noncomputable def coordEntropy (i : ι) (g : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ≥0∞ :=
  eentropy (μ i) (fun y => g (Function.update x i y))

theorem measurable_coordEntropy (i : ι) {g : (∀ j, X j) → ℝ} (hg : Measurable g) :
    Measurable (coordEntropy μ i g) := by
  have hF : Measurable fun p : (∀ j, X j) × X i =>
      ENNReal.ofReal (entropyDensity (coordAvg μ i g p.1) (g (Function.update p.1 i p.2))) :=
    ENNReal.measurable_ofReal.comp (measurable_entropyDensity.comp
      (((measurable_coordAvg i hg).comp measurable_fst).prodMk (hg.comp (measurable_update i))))
  exact hF.lintegral_prod_right'

/-- **Chain rule** on a product: integrating out the coordinate `i` splits the integral of the
Bregman integrand into the coordinate entropy and the integral for `E_i h`. -/
theorem lintegral_entropyDensity_eq_coordEntropy {m : ℝ} (hm : 0 < m) (i : ι)
    {h : (∀ j, X j) → ℝ} (h0 : ∀ x, 0 ≤ h x) (hmeas : Measurable h)
    (hint : Integrable h (Measure.infinitePi μ)) :
    ∫⁻ x, ENNReal.ofReal (entropyDensity m (h x)) ∂Measure.infinitePi μ =
      ∫⁻ x, coordEntropy μ i h x ∂Measure.infinitePi μ +
        ∫⁻ x, ENNReal.ofReal (entropyDensity m (coordAvg μ i h x)) ∂Measure.infinitePi μ := by
  have hF : Measurable fun x => ENNReal.ofReal (entropyDensity m (h x)) :=
    ENNReal.measurable_ofReal.comp ((continuous_entropyDensity m).measurable.comp hmeas)
  rw [← lintegral_lintegral_glue (EfronStein.measurePreserving_update_infinitePi μ i)
    hF.aemeasurable,
    ← lintegral_add_left (measurable_coordEntropy i hmeas)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_integrable_update i hint] with x hx
  exact lintegral_entropyDensity_eq hm (fun y => h0 _) hx

/-- The gluing map `(x, (z, y)) ↦ update (splice T x z) i y` preserves the product measure. -/
theorem measurePreserving_update_splice (T : Set ι) (i : ι) :
    MeasurePreserving
      (fun p : (∀ j, X j) × ((∀ j, X j) × X i) => Function.update (splice T p.1 p.2.1) i p.2.2)
      ((Measure.infinitePi μ).prod ((Measure.infinitePi μ).prod (μ i))) (Measure.infinitePi μ) := by
  have h1 := (measurePreserving_prodAssoc (Measure.infinitePi μ) (Measure.infinitePi μ)
    (μ i)).symm
  have h2 := (measurePreserving_splice μ T).prod (MeasurePreserving.id (μ i))
  have h3 := EfronStein.measurePreserving_update_infinitePi μ i
  exact (h3.comp (h2.comp h1))

/-- **Convexity** on a product: integrating out coordinates other than `i` does not increase the
integrated coordinate entropy in `i`. -/
theorem lintegral_coordEntropy_integrateOut_le {T : Set ι} {i : ι} (hi : i ∉ T)
    {g : (∀ j, X j) → ℝ} (g0 : ∀ x, 0 ≤ g x) (gm : Measurable g)
    (gi : Integrable g (Measure.infinitePi μ)) :
    ∫⁻ x, coordEntropy μ i (integrateOut μ T g) x ∂Measure.infinitePi μ ≤
      ∫⁻ x, coordEntropy μ i g x ∂Measure.infinitePi μ := by
  have hφ := measurePreserving_update_splice (μ := μ) T i
  have hae := ae_integrable_glue hφ gi
  calc ∫⁻ x, coordEntropy μ i (integrateOut μ T g) x ∂Measure.infinitePi μ
      ≤ ∫⁻ x, ∫⁻ z, coordEntropy μ i g (splice T x z) ∂Measure.infinitePi μ
          ∂Measure.infinitePi μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with x hx
        have hslice : (fun y => integrateOut μ T g (Function.update x i y)) =
            fun y => ∫ z, g (Function.update (splice T x z) i y) ∂Measure.infinitePi μ := by
          funext y; simp only [integrateOut, splice_update hi]
        rw [coordEntropy, hslice]
        refine eentropy_integral_le (s := fun z y => g (Function.update (splice T x z) i y))
          (fun z y => g0 _) ?_ hx
        exact gm.comp ((measurable_update i).comp
          (((measurable_splice_right T x).comp measurable_fst).prodMk measurable_snd))
    _ = ∫⁻ x, coordEntropy μ i g x ∂Measure.infinitePi μ :=
        lintegral_lintegral_glue (measurePreserving_splice μ T)
          (measurable_coordEntropy i gm).aemeasurable

omit [∀ i, IsProbabilityMeasure (μ i)] [DecidableEq ι] in
theorem integrateOut_univ (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    integrateOut μ Set.univ f x = ∫ y, f y ∂Measure.infinitePi μ := by
  simp [integrateOut]

/-- **Tensorization of entropy** over a countable product of probability spaces:
`Ent_P g ≤ ∑ᵢ E_P [Ent_{μ i} g]`, in `[0, ∞]`. -/
theorem eentropy_le_tsum_coordEntropy [Countable ι] {g : (∀ j, X j) → ℝ} (g0 : ∀ x, 0 ≤ g x)
    (gm : Measurable g) (gi : Integrable g (Measure.infinitePi μ)) :
    eentropy (Measure.infinitePi μ) g ≤
      ∑' i, ∫⁻ x, coordEntropy μ i g x ∂Measure.infinitePi μ := by
  set P := Measure.infinitePi μ
  set m := ∫ y, g y ∂P with hm_def
  rcases (integral_nonneg g0 : 0 ≤ m).eq_or_lt with hm | hm
  · have hz := integral_eq_zero_imp_ae_zero (ae_of_all _ g0) gi hm.symm
    have hm0 : m = 0 := hm.symm
    have : eentropy P g = 0 := by
      show ∫⁻ x, ENNReal.ofReal (entropyDensity m (g x)) ∂P = 0
      rw [hm0]
      refine (lintegral_congr_ae (hz.mono fun y hy => ?_)).trans lintegral_zero
      simp [hy]
    rw [this]; exact bot_le
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  set c : ι → ℝ≥0∞ := fun i => ∫⁻ x, coordEntropy μ i g x ∂P
  set gn : ℕ → (∀ j, X j) → ℝ := fun n => integrateOut μ (tailSet e n) g
  have gn0 : ∀ n x, 0 ≤ gn n x := fun n x => integral_nonneg fun y => g0 _
  have gnm : ∀ n, Measurable (gn n) := fun n => measurable_integrateOut gm
  have gni : ∀ n, Integrable (gn n) P := fun n => integrable_integrateOut gi
  have hstep : ∀ n, ∫⁻ x, ENNReal.ofReal (entropyDensity m (gn n x)) ∂P ≤
      ∑' i, if e i < n then c i else 0 := by
    intro n
    induction n with
    | zero =>
      have : ∀ x, gn 0 x = m := fun x => by
        simp only [gn, tailSet, zero_le, Set.ofPred_true, integrateOut_univ, P, m]
      simp [this, entropyDensity_self]
    | succ n ih =>
      by_cases hn : ∃ i, e i = n
      · obtain ⟨i₀, hi₀⟩ := hn
        have hW : i₀ ∉ tailSet e (n + 1) := by simp [tailSet, hi₀]
        have hU : tailSet e (n + 1) ∪ {i₀} = tailSet e n := by
          ext j
          simp only [tailSet, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          constructor
          · rintro (h | rfl) <;> omega
          · intro h
            rcases h.lt_or_eq with h | h
            · left; omega
            · right; exact he (h.symm.trans hi₀.symm) |>.symm ▸ rfl
        have hcoord : coordAvg μ i₀ (gn (n + 1)) =ᵐ[P] gn n := by
          rw [coordAvg_eq_integrateOut i₀ (gnm (n + 1))]
          filter_upwards [integrateOut_integrateOut (S := {i₀}) (T := tailSet e (n + 1)) gi]
            with x hx
          rw [hx, hU]
        have hsum : (∑' i, if e i < n + 1 then c i else 0) =
            (∑' i, if e i < n then c i else 0) + c i₀ := by
          have : (fun i => if e i < n + 1 then c i else 0) =
              fun i => (if e i < n then c i else 0) + (if i = i₀ then c i else 0) := by
            funext i
            by_cases h1 : i = i₀
            · subst h1; simp [hi₀]
            · have : e i ≠ n := fun h => h1 (he (h.trans hi₀.symm))
              by_cases h2 : e i < n
              · simp [h2, h1, show e i < n + 1 by omega]
              · simp [h2, h1, show ¬ e i < n + 1 by omega]
          rw [this, ENNReal.tsum_add, tsum_ite_eq]
        have hcongr : ∫⁻ x, ENNReal.ofReal (entropyDensity m (coordAvg μ i₀ (gn (n + 1)) x)) ∂P =
            ∫⁻ x, ENNReal.ofReal (entropyDensity m (gn n x)) ∂P :=
          lintegral_congr_ae (hcoord.mono fun x hx => by simp only [hx])
        rw [lintegral_entropyDensity_eq_coordEntropy hm i₀ (gn0 (n + 1)) (gnm (n + 1))
          (gni (n + 1)), hcongr, hsum, add_comm]
        exact add_le_add ih (lintegral_coordEntropy_integrateOut_le hW g0 gm gi)
      · push Not at hn
        have hT : tailSet e (n + 1) = tailSet e n := by
          ext j; simp only [tailSet, Set.mem_ofPred_eq]
          have := hn j; omega
        have hgn : gn (n + 1) = gn n := by simp only [gn, hT]
        have hsum : (fun i => if e i < n + 1 then c i else 0) =
            fun i => if e i < n then c i else 0 := by
          funext i; have := hn i
          by_cases h : e i < n
          · simp [h, show e i < n + 1 by omega]
          · simp [h, show ¬ e i < n + 1 by omega]
        rw [hgn, hsum]; exact ih
  have hbound : ∀ n, ∫⁻ x, ENNReal.ofReal (entropyDensity m (gn n x)) ∂P ≤ ∑' i, c i :=
    fun n => (hstep n).trans (ENNReal.tsum_le_tsum fun i => by
      split_ifs <;> simp)
  -- Lévy's upward theorem and Fatou's lemma
  have hlim : ∀ᵐ x ∂P, Tendsto (fun n => ENNReal.ofReal (entropyDensity m (gn n x))) atTop
      (𝓝 (ENNReal.ofReal (entropyDensity m (g x)))) := by
    filter_upwards [tendsto_integrateOut_ae μ e gm gi] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((continuous_entropyDensity m).tendsto _).comp hx)
  calc eentropy P g = ∫⁻ x, ENNReal.ofReal (entropyDensity m (g x)) ∂P := rfl
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (entropyDensity m (gn n x))) atTop ∂P :=
        lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (entropyDensity m (gn n x)) ∂P) atTop :=
        lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp
          ((continuous_entropyDensity m).measurable.comp (gnm n))
    _ ≤ ∑' i, c i := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

end Product

end IsotropicVariance.Infra.Entropy
