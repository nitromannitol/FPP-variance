/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Entropy.Tensorization

/-!
# A symmetrized entropy bound for functions with pivotal coordinates

Let `P = ∏_i ν` be a countable product of one law `ν` on `ℝ≥0`, and let `Z` be a function of the
coordinates with *pivotal sets* `piv i`: if raising coordinate `i` from `x i` to `y` raises `Z`,
then `x ∈ piv i` and `Z` rises by at most `y` (`HasPivots`). Then, for every real `θ`,

  `Ent_P e^{θZ} ≤ (∫ θ² y² e^{θ₊ y} dν(y)) · E[e^{θZ} #{i : x ∈ piv i}]`

(`eentropy_exp_le_lintegral`), and so `≤ (∫ θ² y² e^{θ₊ y} dν) R E e^{θZ}` when at most `R`
coordinates are pivotal (`eentropy_exp_le`).

The proof tensorizes the entropy (`eentropy_le_tsum_coordEntropy`) and bounds each coordinate
entropy by the variational formula with the reference value `e^{θZ}` at an independent copy `y'`
of the coordinate. Symmetrizing in `(y, y')` turns the integrand into
`(b - a)(e^b - e^a) / 2`, where `a, b` are the values of `θZ` at `y, y'`. On the side where `Z`
is larger at `y'`, the configuration at `y` is pivotal and the increment is at most `y'`, the
*independent* weight. So the weights of the current configuration never enter the bound
(compare [ADH, Lemma 3.14] and Boucheron–Lugosi–Massart, Theorem 6.15). The bound holds for every
law `ν` on `ℝ≥0`.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

open Infra.Entropy

/-! ### Elementary inequalities -/

/-- `v (e^v - 1) ≤ v² e^{v₊}`. -/
theorem mul_exp_sub_one_le (v : ℝ) : v * (exp v - 1) ≤ v ^ 2 * exp (max v 0) := by
  rcases le_or_gt 0 v with hv | hv
  · rw [max_eq_left hv]
    have h1 : exp v - 1 ≤ v * exp v := by
      have h := add_one_le_exp (-v)
      have h2 : exp (-v) * exp v = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
      nlinarith [exp_pos v]
    calc v * (exp v - 1) ≤ v * (v * exp v) := mul_le_mul_of_nonneg_left h1 hv
      _ = v ^ 2 * exp v := by ring
  · rw [max_eq_right hv.le, exp_zero, mul_one]
    have h := add_one_le_exp v
    nlinarith

/-- The increment bound behind the symmetrized inequality: if `s ≤ s' ≤ s + c`, then
`(θs' - θs)(e^{θs'} - e^{θs}) ≤ θ² c² e^{θ₊ c} e^{θs}`. -/
theorem mul_sub_exp_sub_le (θ : ℝ) {s s' c : ℝ} (h : s ≤ s') (hc : s' - s ≤ c) :
    (θ * s' - θ * s) * (exp (θ * s') - exp (θ * s)) ≤
      θ ^ 2 * c ^ 2 * exp (max θ 0 * c) * exp (θ * s) := by
  set v := θ * (s' - s) with hv
  have hD : 0 ≤ s' - s := sub_nonneg.2 h
  have hc0 : 0 ≤ c := hD.trans hc
  have hexp : exp (θ * s') = exp (θ * s) * exp v := by
    rw [← exp_add, hv]; ring_nf
  have hl : (θ * s' - θ * s) * (exp (θ * s') - exp (θ * s)) =
      v * (exp v - 1) * exp (θ * s) := by rw [hexp, hv]; ring
  have hv2 : v ^ 2 ≤ θ ^ 2 * c ^ 2 := by
    rw [hv, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hc 2) (sq_nonneg θ)
  have hmax : max v 0 ≤ max θ 0 * c := by
    rcases le_or_gt 0 θ with hθ | hθ
    · rw [max_eq_left hθ]
      exact max_le (mul_le_mul_of_nonneg_left hc hθ) (mul_nonneg hθ hc0)
    · rw [max_eq_right hθ.le, zero_mul]
      exact max_le (mul_nonpos_of_nonpos_of_nonneg hθ.le hD) le_rfl
  rw [hl]
  refine mul_le_mul_of_nonneg_right ((mul_exp_sub_one_le v).trans ?_) (exp_pos _).le
  exact mul_le_mul hv2 (exp_le_exp.2 hmax) (exp_pos _).le (by positivity)

/-- The entropy densities at two exponentials add up to `(b - a)(e^b - e^a)`. -/
theorem entropyDensity_exp_add_entropyDensity_exp (a b : ℝ) :
    entropyDensity (exp b) (exp a) + entropyDensity (exp a) (exp b) =
      (b - a) * (exp b - exp a) := by
  simp only [entropyDensity, log_exp]
  ring

/-! ### Pivotal coordinates -/

section Pivots

variable {ι : Type*} [DecidableEq ι]

/-- `Z` has *pivotal sets* `piv i`: if setting coordinate `i` of `x` to `y` raises `Z`, then
`x ∈ piv i` and `Z` rises by at most `y`. -/
def HasPivots (Z : (ι → ℝ≥0) → ℝ) (piv : ι → Set (ι → ℝ≥0)) : Prop :=
  ∀ x i (y : ℝ≥0), Z x < Z (Function.update x i y) →
    x ∈ piv i ∧ Z (Function.update x i y) ≤ Z x + y

variable {Z : (ι → ℝ≥0) → ℝ} {piv : ι → Set (ι → ℝ≥0)}

/-- The integrand of the symmetrized bound at the configuration `x` with coordinate `i` set to
`y`, the independent copy being `y'`. -/
noncomputable def pivotTerm (θ : ℝ) (Z : (ι → ℝ≥0) → ℝ) (piv : ι → Set (ι → ℝ≥0)) (x : ι → ℝ≥0)
    (i : ι) (y y' : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (θ ^ 2 * (y' : ℝ) ^ 2 * exp (max θ 0 * y')) *
    (ENNReal.ofReal (exp (θ * Z (Function.update x i y))) *
      (piv i).indicator 1 (Function.update x i y))

/-- The integrand at a pivotal configuration. -/
theorem pivotTerm_eq_of_mem {θ : ℝ} {x : ι → ℝ≥0} {i : ι} {y : ℝ≥0}
    (hpiv : Function.update x i y ∈ piv i) (y' : ℝ≥0) :
    pivotTerm θ Z piv x i y y' = ENNReal.ofReal (θ ^ 2 * (y' : ℝ) ^ 2 * exp (max θ 0 * y') *
      exp (θ * Z (Function.update x i y))) := by
  rw [pivotTerm, Set.indicator_of_mem hpiv, Pi.one_apply, mul_one,
    ← ENNReal.ofReal_mul (by positivity)]

/-- **The pointwise symmetrized bound.** -/
theorem ofReal_mul_sub_exp_le (hZ : HasPivots Z piv) (θ : ℝ) (x : ι → ℝ≥0) (i : ι)
    (y y' : ℝ≥0) :
    ENNReal.ofReal ((θ * Z (Function.update x i y') - θ * Z (Function.update x i y)) *
        (exp (θ * Z (Function.update x i y')) - exp (θ * Z (Function.update x i y)))) ≤
      pivotTerm θ Z piv x i y y' + pivotTerm θ Z piv x i y' y := by
  set w := Function.update x i y
  set w' := Function.update x i y'
  have hww' : Function.update w i y' = w' := by simp [w, w']
  have hw'w : Function.update w' i y = w := by simp [w, w']
  rcases lt_trichotomy (Z w) (Z w') with h | h | h
  · obtain ⟨hpiv, hle⟩ := hZ w i y' (by rwa [hww'])
    rw [hww'] at hle
    refine le_add_right ?_
    have hb := mul_sub_exp_sub_le θ h.le (c := y') (by linarith)
    calc _ ≤ ENNReal.ofReal (θ ^ 2 * (y' : ℝ) ^ 2 * exp (max θ 0 * y') * exp (θ * Z w)) :=
          ENNReal.ofReal_le_ofReal hb
      _ = pivotTerm θ Z piv x i y y' := (pivotTerm_eq_of_mem hpiv y').symm
  · rw [h, sub_self, zero_mul, ENNReal.ofReal_zero]
    exact zero_le
  · obtain ⟨hpiv, hle⟩ := hZ w' i y (by rwa [hw'w])
    rw [hw'w] at hle
    refine le_add_left ?_
    have hb := mul_sub_exp_sub_le θ h.le (c := y) (by linarith)
    have hsymm : (θ * Z w' - θ * Z w) * (exp (θ * Z w') - exp (θ * Z w)) =
        (θ * Z w - θ * Z w') * (exp (θ * Z w) - exp (θ * Z w')) := by ring
    calc _ = ENNReal.ofReal ((θ * Z w - θ * Z w') * (exp (θ * Z w) - exp (θ * Z w'))) := by
          rw [hsymm]
      _ ≤ ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y) * exp (θ * Z w')) :=
          ENNReal.ofReal_le_ofReal hb
      _ = pivotTerm θ Z piv x i y' y := (pivotTerm_eq_of_mem hpiv y).symm

end Pivots

/-! ### One coordinate -/

section Coordinate

variable {ν : Measure ℝ≥0} [IsProbabilityMeasure ν]

/-- The extended entropy is at most the integral of any Bregman integrand `ψ_m`, `m > 0`. -/
theorem eentropy_le_lintegral_entropyDensity {s : ℝ≥0 → ℝ} {m : ℝ} (hm : 0 < m)
    (hs0 : ∀ y, 0 ≤ s y) (hs : Integrable s ν) :
    eentropy ν s ≤ ∫⁻ y, ENNReal.ofReal (entropyDensity m (s y)) ∂ν := by
  rw [lintegral_entropyDensity_eq hm hs0 hs]
  exact le_self_add

/-- **Symmetrization**: for a measurable `f : ℝ≥0 × ℝ≥0 → ℝ≥0∞`,
`2 ∫∫ f(y', y) = ∫∫ (f(y', y) + f(y, y'))`. -/
theorem two_mul_lintegral_lintegral_eq {f : ℝ≥0 → ℝ≥0 → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    2 * ∫⁻ y', ∫⁻ y, f y' y ∂ν ∂ν = ∫⁻ y', ∫⁻ y, (f y' y + f y y') ∂ν ∂ν := by
  have hswap : ∫⁻ y', ∫⁻ y, f y y' ∂ν ∂ν = ∫⁻ y', ∫⁻ y, f y' y ∂ν ∂ν :=
    lintegral_lintegral_swap (hf.comp measurable_swap).aemeasurable
  have hm1 : ∀ y', Measurable fun y => f y' y := fun y' => hf.comp measurable_prodMk_left
  have hm2 : ∀ y', Measurable fun y => f y y' := fun y' =>
    (hf.comp measurable_swap).comp measurable_prodMk_left
  have hi1 : Measurable fun y' => ∫⁻ y, f y' y ∂ν := hf.lintegral_prod_right'
  simp_rw [lintegral_add_left (hm1 _)]
  rw [lintegral_add_left hi1, hswap, two_mul]

end Coordinate

/-! ### The product -/

section Product

variable {ι : Type*} [DecidableEq ι] {ν : Measure ℝ≥0} [IsProbabilityMeasure ν]
  {Z : (ι → ℝ≥0) → ℝ} {piv : ι → Set (ι → ℝ≥0)}

/-- **One coordinate.** The expected coordinate entropy of `e^{θZ}` in the coordinate `i` is at
most `(∫ θ² y² e^{θ₊ y} dν) E[e^{θZ}; piv i]`. -/
theorem lintegral_coordEntropy_exp_le (hZm : Measurable Z) (hpm : ∀ i, MeasurableSet (piv i))
    (hZ : HasPivots Z piv) (θ : ℝ) (i : ι)
    (hint : Integrable (fun x => exp (θ * Z x)) (Measure.infinitePi fun _ : ι => ν)) :
    ∫⁻ x, coordEntropy (fun _ : ι => ν) i (fun x => exp (θ * Z x)) x
        ∂Measure.infinitePi (fun _ : ι => ν) ≤
      (∫⁻ y, ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y)) ∂ν) *
        ∫⁻ x, ENNReal.ofReal (exp (θ * Z x)) * (piv i).indicator 1 x
          ∂Measure.infinitePi (fun _ : ι => ν) := by
  set P := Measure.infinitePi fun _ : ι => ν
  set M := ∫⁻ y, ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y)) ∂ν
  set F : (ι → ℝ≥0) → ℝ≥0∞ := fun x => ENNReal.ofReal (exp (θ * Z x)) * (piv i).indicator 1 x
  have hupd : Measurable fun p : (ι → ℝ≥0) × ℝ≥0 => Function.update p.1 i p.2 :=
    measurable_update (X := fun _ : ι => ℝ≥0) i
  have hupd1 : ∀ x : ι → ℝ≥0, Measurable fun y : ℝ≥0 => Function.update x i y := fun x =>
    hupd.comp measurable_prodMk_left
  have hF : Measurable F :=
    (ENNReal.measurable_ofReal.comp ((hZm.const_mul θ).exp)).mul
      ((measurable_const.indicator (hpm i)))
  -- the bound at a fixed configuration with an integrable section
  have hx : ∀ x : ι → ℝ≥0, Integrable (fun y => exp (θ * Z (Function.update x i y))) ν →
      coordEntropy (fun _ : ι => ν) i (fun x => exp (θ * Z x)) x ≤
        M * ∫⁻ y, F (Function.update x i y) ∂ν := by
    intro x hxi
    set g : ℝ≥0 → ℝ := fun y => θ * Z (Function.update x i y)
    have hg : Measurable g := (hZm.comp (hupd1 x)).const_mul θ
    set S : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun y' y =>
      ENNReal.ofReal (entropyDensity (exp (g y')) (exp (g y)))
    have hS : Measurable (Function.uncurry S) := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact measurable_entropyDensity.comp
        (((hg.comp measurable_fst).exp).prodMk ((hg.comp measurable_snd).exp))
    -- variational formula, averaged over the reference `y'`
    have h1 : coordEntropy (fun _ : ι => ν) i (fun x => exp (θ * Z x)) x ≤
        ∫⁻ y', ∫⁻ y, S y' y ∂ν ∂ν := by
      have hle : ∀ y', coordEntropy (fun _ : ι => ν) i (fun x => exp (θ * Z x)) x ≤
          ∫⁻ y, S y' y ∂ν := fun y' =>
        eentropy_le_lintegral_entropyDensity (exp_pos _) (fun _ => (exp_pos _).le) hxi
      calc _ = ∫⁻ _y', coordEntropy (fun _ : ι => ν) i (fun x => exp (θ * Z x)) x ∂ν := by
            rw [lintegral_const, measure_univ, mul_one]
        _ ≤ _ := lintegral_mono hle
    -- symmetrization and the pointwise bound
    set G : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun y' y => pivotTerm θ Z piv x i y y'
    have hG : Measurable (Function.uncurry G) := by
      have hc : Measurable fun y' : ℝ≥0 =>
          ENNReal.ofReal (θ ^ 2 * (y' : ℝ) ^ 2 * exp (max θ 0 * y')) := by fun_prop
      exact (hc.comp measurable_fst).mul (hF.comp ((hupd1 x).comp measurable_snd))
    have hSG : ∀ y' y, S y' y + S y y' ≤ G y' y + G y y' := by
      intro y' y
      have hnn : ∀ a b : ℝ, 0 ≤ entropyDensity (exp b) (exp a) := fun a b =>
        entropyDensity_nonneg (exp_pos _) (exp_pos _).le
      simp only [S, G]
      rw [← ENNReal.ofReal_add (hnn _ _) (hnn _ _), entropyDensity_exp_add_entropyDensity_exp]
      exact ofReal_mul_sub_exp_le hZ θ x i y y'
    have h2 : ∫⁻ y', ∫⁻ y, S y' y ∂ν ∂ν ≤ ∫⁻ y', ∫⁻ y, G y' y ∂ν ∂ν := by
      have h := two_mul_lintegral_lintegral_eq (ν := ν) hS
      have h' := two_mul_lintegral_lintegral_eq (ν := ν) hG
      have hle : 2 * ∫⁻ y', ∫⁻ y, S y' y ∂ν ∂ν ≤ 2 * ∫⁻ y', ∫⁻ y, G y' y ∂ν ∂ν := by
        rw [h, h']
        exact lintegral_mono fun y' => lintegral_mono fun y => hSG y' y
      exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 hle
    have h3 : ∫⁻ y', ∫⁻ y, G y' y ∂ν ∂ν = M * ∫⁻ y, F (Function.update x i y) ∂ν := by
      set c : ℝ≥0 → ℝ≥0∞ := fun y' => ENNReal.ofReal (θ ^ 2 * (y' : ℝ) ^ 2 * exp (max θ 0 * y'))
      have hc : Measurable c := by fun_prop
      have hGc : ∀ y' y, G y' y = c y' * F (Function.update x i y) := fun _ _ => rfl
      have hFm : Measurable fun y => F (Function.update x i y) := hF.comp (hupd1 x)
      calc ∫⁻ y', ∫⁻ y, G y' y ∂ν ∂ν = ∫⁻ y', c y' * ∫⁻ y, F (Function.update x i y) ∂ν ∂ν :=
            lintegral_congr fun y' => by simp_rw [hGc]; exact lintegral_const_mul _ hFm
        _ = M * ∫⁻ y, F (Function.update x i y) ∂ν := lintegral_mul_const _ hc
    exact h1.trans (h2.trans h3.le)
  have hae := ae_integrable_update (μ := fun _ : ι => ν) i hint
  calc ∫⁻ x, coordEntropy (fun _ : ι => ν) i (fun x => exp (θ * Z x)) x ∂P
      ≤ ∫⁻ x, M * ∫⁻ y, F (Function.update x i y) ∂ν ∂P :=
        lintegral_mono_ae (hae.mono fun x hxi => hx x hxi)
    _ = M * ∫⁻ x, ∫⁻ y, F (Function.update x i y) ∂ν ∂P := by
        refine lintegral_const_mul _ ?_
        exact (hF.comp hupd).lintegral_prod_right'
    _ = M * ∫⁻ x, F x ∂P := by
        rw [lintegral_lintegral_glue (measurePreserving_update (fun _ : ι => ν) i) hF]

/-- **Tensorized symmetrized bound.** For every real `θ`,
`Ent_P e^{θZ} ≤ (∫ θ² y² e^{θ₊ y} dν) E[e^{θZ} #{i : x ∈ piv i}]`. -/
theorem eentropy_exp_le_lintegral [Countable ι] (hZm : Measurable Z)
    (hpm : ∀ i, MeasurableSet (piv i)) (hZ : HasPivots Z piv) (θ : ℝ)
    (hint : Integrable (fun x => exp (θ * Z x)) (Measure.infinitePi fun _ : ι => ν)) :
    eentropy (Measure.infinitePi fun _ : ι => ν) (fun x => exp (θ * Z x)) ≤
      (∫⁻ y, ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y)) ∂ν) *
        ∫⁻ x, ENNReal.ofReal (exp (θ * Z x)) * ∑' i, (piv i).indicator 1 x
          ∂Measure.infinitePi (fun _ : ι => ν) := by
  set P := Measure.infinitePi fun _ : ι => ν
  set M := ∫⁻ y, ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y)) ∂ν
  have hE : Measurable fun x => ENNReal.ofReal (exp (θ * Z x)) :=
    ENNReal.measurable_ofReal.comp (hZm.const_mul θ).exp
  have hind : ∀ i, Measurable ((piv i).indicator (1 : (ι → ℝ≥0) → ℝ≥0∞)) := fun i =>
    measurable_const.indicator (hpm i)
  calc eentropy P (fun x => exp (θ * Z x))
      ≤ ∑' i, ∫⁻ x, coordEntropy (fun _ : ι => ν) i (fun x => exp (θ * Z x)) x ∂P :=
        eentropy_le_tsum_coordEntropy (fun _ => (exp_pos _).le) (hZm.const_mul θ).exp hint
    _ ≤ ∑' i, M * ∫⁻ x, ENNReal.ofReal (exp (θ * Z x)) * (piv i).indicator 1 x ∂P :=
        ENNReal.tsum_le_tsum fun i => lintegral_coordEntropy_exp_le hZm hpm hZ θ i hint
    _ = M * ∫⁻ x, ENNReal.ofReal (exp (θ * Z x)) * ∑' i, (piv i).indicator 1 x ∂P := by
        have h : ∀ x, ENNReal.ofReal (exp (θ * Z x)) * ∑' i, (piv i).indicator 1 x =
            ∑' i, ENNReal.ofReal (exp (θ * Z x)) * (piv i).indicator 1 x := fun x =>
          ENNReal.tsum_mul_left.symm
        simp_rw [h]
        rw [ENNReal.tsum_mul_left, lintegral_tsum
          (f := fun i x => ENNReal.ofReal (exp (θ * Z x)) * (piv i).indicator 1 x)
          fun i => (hE.mul (hind i)).aemeasurable]

/-- **Tensorized symmetrized bound**, with at most `R` pivotal coordinates:
`Ent_P e^{θZ} ≤ (∫ θ² y² e^{θ₊ y} dν) R E e^{θZ}`. -/
theorem eentropy_exp_le [Countable ι] (hZm : Measurable Z) (hpm : ∀ i, MeasurableSet (piv i))
    (hZ : HasPivots Z piv) {R : ℝ≥0∞} (hR : ∀ x, ∑' i, (piv i).indicator 1 x ≤ R) (θ : ℝ)
    (hint : Integrable (fun x => exp (θ * Z x)) (Measure.infinitePi fun _ : ι => ν)) :
    eentropy (Measure.infinitePi fun _ : ι => ν) (fun x => exp (θ * Z x)) ≤
      (∫⁻ y, ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y)) ∂ν) * R *
        ∫⁻ x, ENNReal.ofReal (exp (θ * Z x)) ∂Measure.infinitePi (fun _ : ι => ν) := by
  have hE : Measurable fun x => ENNReal.ofReal (exp (θ * Z x)) :=
    ENNReal.measurable_ofReal.comp (hZm.const_mul θ).exp
  refine (eentropy_exp_le_lintegral hZm hpm hZ θ hint).trans ?_
  calc _ ≤ (∫⁻ y, ENNReal.ofReal (θ ^ 2 * (y : ℝ) ^ 2 * exp (max θ 0 * y)) ∂ν) *
        ∫⁻ x, ENNReal.ofReal (exp (θ * Z x)) * R ∂Measure.infinitePi (fun _ : ι => ν) :=
        by gcongr with x; exact hR x
    _ = _ := by rw [lintegral_mul_const R hE]; ring

end Product

end CurvatureVariance.Infra.FPP
