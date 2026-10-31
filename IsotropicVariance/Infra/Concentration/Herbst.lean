/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Entropy.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Herbst's argument and sub-Gaussian tail bounds

On an abstract probability space, an entropy bound `Ent(e^{θZ}) ≤ A θ² E e^{θZ}` for
`θ ∈ (0, θ₀]` (`mgf_sub_integral_le_of_eentropy_le`) integrates to the sub-Gaussian moment
generating function bound `E e^{θ(Z - EZ)} ≤ e^{A θ²}` on `[0, θ₀]` (Herbst's argument); the
case `θ ∈ [-θ₀, 0)` is `mgf_sub_integral_le_of_eentropy_le_neg`. Chernoff's inequality then
gives the upper tail (`measure_integral_add_le_of_mgf_le`), and the lower tail when applied to
`-Z`.

Two hypotheses are needed beyond the informal statements. The entropy argument needs `0 ≤ A`
(a constant `Z` shows the conclusion fails for `A < 0`). The tail bounds need the exponential
moments to be integrable, since `mgf` of a non-integrable function is `0`, so a bound on `mgf`
alone says nothing about the tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal

namespace IsotropicVariance.Infra.Concentration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : Ω → ℝ}

/-- **Herbst's argument**, upper side: if `Ent(e^{θZ}) ≤ A θ² E e^{θZ}` for `θ ∈ (0, θ₀]`, then
`E e^{θ(Z - EZ)} ≤ e^{A θ²}` on `[0, θ₀]`. -/
theorem mgf_sub_integral_le_of_eentropy_le {A θ₀ : ℝ} (hA : 0 ≤ A) (hZ : Measurable Z)
    (hint : Set.Icc 0 θ₀ ⊆ interior (integrableExpSet Z P))
    (hent : ∀ θ ∈ Set.Ioc 0 θ₀, IsotropicVariance.Infra.Entropy.eentropy P (fun ω => exp (θ * Z ω)) ≤
      ENNReal.ofReal (A * θ ^ 2 * mgf Z P θ)) :
    ∀ θ ∈ Set.Icc 0 θ₀, mgf (fun ω => Z ω - ∫ ω', Z ω' ∂P) P θ ≤ exp (A * θ ^ 2) := by
  intro θ hθ
  have _ := hZ
  have hθ₀ : 0 ≤ θ₀ := hθ.1.trans hθ.2
  set m : ℝ := ∫ ω', Z ω' ∂P with hm
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet Z P) := hint ⟨le_rfl, hθ₀⟩
  have hIe : ∀ t ∈ Set.Icc 0 θ₀, Integrable (fun ω => exp (t * Z ω)) P := fun t ht =>
    integrable_of_mem_integrableExpSet (interior_subset (hint ht))
  have hHpos : ∀ t ∈ Set.Icc 0 θ₀, 0 < mgf Z P t := fun t ht => mgf_pos (hIe t ht)
  set D : ℝ → ℝ := fun t => P[fun ω => Z ω * exp (t * Z ω)] with hD
  have hHd : ∀ t ∈ Set.Icc 0 θ₀, HasDerivAt (mgf Z P) (D t) t := fun t ht =>
    hasDerivAt_mgf (hint ht)
  set ψ : ℝ → ℝ := fun t => log (mgf Z P t) - t * m - A * t ^ 2 with hψ
  have hψd : ∀ t ∈ Set.Icc 0 θ₀,
      HasDerivAt ψ (D t / mgf Z P t - m - A * (2 * t)) t := by
    intro t ht
    have h1 := (((hHd t ht).log (hHpos t ht).ne').sub ((hasDerivAt_id t).mul_const m)).sub
      ((hasDerivAt_pow 2 t).const_mul A)
    refine HasDerivAt.congr_deriv (f := ψ) h1 ?_
    simp
  -- the entropy inequality
  have hkey : ∀ t ∈ Set.Ioc 0 θ₀,
      t * D t - mgf Z P t * log (mgf Z P t) ≤ A * t ^ 2 * mgf Z P t := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 θ₀ := ⟨ht.1.le, ht.2⟩
    have hpos := hHpos t ht'
    have hg : Integrable (fun ω => exp (t * Z ω)) P := hIe t ht'
    have hlog : Integrable (fun ω => exp (t * Z ω) * log (exp (t * Z ω))) P := by
      have := (integrable_pow_mul_exp_of_mem_interior_integrableExpSet (hint ht') 1).const_mul t
      refine this.congr (ae_of_all _ fun ω => ?_)
      simp only [pow_one, log_exp]
      ring
    have h := hent t ht
    rw [IsotropicVariance.Infra.Entropy.eentropy_eq_ofReal_entropy (ae_of_all _ fun ω => (exp_pos _).le) hg hlog,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    have hE : ∫ ω, exp (t * Z ω) * log (exp (t * Z ω)) ∂P = t * D t := by
      rw [hD, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [log_exp]
      ring
    have hH : ∫ ω, exp (t * Z ω) ∂P = mgf Z P t := rfl
    simpa only [IsotropicVariance.Cited.entropy, hE, hH] using h
  -- the monotone quotient
  set G : ℝ → ℝ := fun t => ψ t / t with hG
  have hGd : ∀ t ∈ Set.Ioc 0 θ₀, HasDerivAt G
      ((( D t / mgf Z P t - m - A * (2 * t)) * t - ψ t * 1) / t ^ 2) t := fun t ht =>
    (hψd t ⟨ht.1.le, ht.2⟩).div (hasDerivAt_id t) ht.1.ne'
  have hanti : AntitoneOn G (Set.Ioc 0 θ₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 θ₀)
      (fun t ht => (hGd t ht).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ioc]
      exact fun t ht => (hGd t ⟨ht.1, ht.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [interior_Ioc]
      intro t ht
      have ht' : t ∈ Set.Ioc 0 θ₀ := ⟨ht.1, ht.2.le⟩
      rw [(hGd t ht').deriv]
      refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg t)
      have hpos := hHpos t ⟨ht.1.le, ht.2.le⟩
      have h := hkey t ht'
      have h2 : t * D t / mgf Z P t - log (mgf Z P t) ≤ A * t ^ 2 := by
        rw [sub_le_iff_le_add, div_le_iff₀ hpos]
        linarith
      have h3 : D t / mgf Z P t * t = t * D t / mgf Z P t := by ring
      simp only [hψ]
      nlinarith [h2, h3]
  -- the limit at `0`
  have hH0 : mgf Z P 0 = 1 := by simp [mgf_zero']
  have hD0 : D 0 = m := by simp [hD, hm]
  have hψ0 : ψ 0 = 0 := by simp [hψ, hH0]
  have hψ0d : HasDerivAt ψ 0 0 := by
    have := hψd 0 ⟨le_rfl, hθ₀⟩
    convert this using 1
    simp [hD0, hH0]
  have hlim : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    have := (hasDerivAt_iff_tendsto_slope_zero.1 hψ0d).mono_left
      (nhdsGT_le_nhdsNE (0 : ℝ))
    refine this.congr fun t => ?_
    simp [hG, hψ0, div_eq_inv_mul]
  -- conclusion
  rcases hθ.1.eq_or_lt with h | h
  · subst h
    simp [mgf_zero']
  · have hθ' : θ ∈ Set.Ioc 0 θ₀ := ⟨h, hθ.2⟩
    have hGle : G θ ≤ 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsGT h] with ε hε
      exact hanti ⟨hε.1, hε.2.le.trans hθ.2⟩ hθ' hε.2.le
    have hψle : ψ θ ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos h.le hGle
      simpa [hG, mul_div_cancel₀ _ h.ne'] using this
    have hlogle : log (mgf Z P θ) ≤ θ * m + A * θ ^ 2 := by
      simp only [hψ] at hψle
      linarith
    have hHle : mgf Z P θ ≤ exp (θ * m + A * θ ^ 2) :=
      (le_exp_log _ |>.trans (exp_le_exp.2 hlogle) : _)
    have hmgf : mgf (fun ω => Z ω - m) P θ = exp (-(θ * m)) * mgf Z P θ := by
      have := mgf_add_const (X := Z) (μ := P) (t := θ) (-m)
      simp only [← sub_eq_add_neg] at this
      rw [this, mul_comm]
      congr 2
      ring
    rw [hmgf]
    calc exp (-(θ * m)) * mgf Z P θ ≤ exp (-(θ * m)) * exp (θ * m + A * θ ^ 2) :=
          mul_le_mul_of_nonneg_left hHle (exp_pos _).le
      _ = exp (A * θ ^ 2) := by rw [← exp_add]; congr 1; ring

omit [IsProbabilityMeasure P] in
/-- The exponential-moment set of `-Z` is the reflection of that of `Z`; consequently so is its
interior. -/
private lemma integrableExpSet_neg_eq :
    integrableExpSet (-Z) P = (fun x : ℝ => -x) ⁻¹' integrableExpSet Z P := by
  ext t
  simp [integrableExpSet]

omit [IsProbabilityMeasure P] in
private lemma interior_integrableExpSet_neg :
    interior (integrableExpSet (-Z) P) = (fun x : ℝ => -x) ⁻¹' interior (integrableExpSet Z P) := by
  rw [integrableExpSet_neg_eq]
  exact ((Homeomorph.neg ℝ).preimage_interior _).symm

/-- Herbst's argument, lower side. -/
theorem mgf_sub_integral_le_of_eentropy_le_neg {A θ₀ : ℝ} (hA : 0 ≤ A) (hZ : Measurable Z)
    (hint : Set.Icc (-θ₀) 0 ⊆ interior (integrableExpSet Z P))
    (hent : ∀ θ ∈ Set.Ico (-θ₀) 0, IsotropicVariance.Infra.Entropy.eentropy P (fun ω => exp (θ * Z ω)) ≤
      ENNReal.ofReal (A * θ ^ 2 * mgf Z P θ)) :
    ∀ θ ∈ Set.Icc (-θ₀) 0, mgf (fun ω => Z ω - ∫ ω', Z ω' ∂P) P θ ≤ exp (A * θ ^ 2) := by
  have h := mgf_sub_integral_le_of_eentropy_le (P := P) (Z := -Z) (A := A) (θ₀ := θ₀) hA hZ.neg
    (fun t ht => by
      rw [interior_integrableExpSet_neg]
      exact hint ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    (fun t ht => by
      have h1 := hent (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have e : (fun ω => exp (t * (-Z) ω)) = fun ω => exp (-t * Z ω) := by
        funext ω
        simp
      rw [e, mgf_neg]
      simpa [neg_sq] using h1)
  intro θ hθ
  have h2 := h (-θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have e : (fun ω => (-Z) ω - ∫ ω', (-Z) ω' ∂P) = -(fun ω => Z ω - ∫ ω', Z ω' ∂P) := by
    funext ω
    simp [integral_neg]
    ring
  rw [e, mgf_neg, neg_neg] at h2
  simpa [neg_sq] using h2

/-- Upper tail from a sub-Gaussian mgf bound on `[0, θ₀]`. This needs the exponential moments on
`[0, θ₀]` to be integrable: `mgf` of a non-integrable function is `0`. -/
theorem measure_integral_add_le_of_mgf_le {A θ₀ : ℝ} (hA : 0 < A) (hθ₀ : 0 < θ₀)
    (hexp : ∀ θ ∈ Set.Icc 0 θ₀, Integrable (fun ω => exp (θ * Z ω)) P)
    (hmgf : ∀ θ ∈ Set.Icc 0 θ₀, mgf (fun ω => Z ω - ∫ ω', Z ω' ∂P) P θ ≤ exp (A * θ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    P {ω | (∫ ω', Z ω' ∂P) + t ≤ Z ω} ≤
      ENNReal.ofReal (exp (-min (t ^ 2 / (4 * A)) (θ₀ * t / 2))) := by
  set m : ℝ := ∫ ω', Z ω' ∂P with hm
  set θ : ℝ := min (t / (2 * A)) θ₀ with hθdef
  have hθ : θ ∈ Set.Icc 0 θ₀ :=
    ⟨le_min (by positivity) hθ₀.le, min_le_right _ _⟩
  have hint : Integrable (fun ω => exp (θ * (Z ω - m))) P := by
    have := (hexp θ hθ).const_mul (exp (-(θ * m)))
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only
    rw [← exp_add]
    congr 1
    ring
  have hc := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => Z ω - m) t hθ.1 hint
  have hset : {ω | m + t ≤ Z ω} = {ω | t ≤ Z ω - m} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset, ← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (hc.trans ?_)
  have h2 := mul_le_mul_of_nonneg_left (hmgf θ hθ) (exp_pos (-θ * t)).le
  refine h2.trans ?_
  rw [← exp_add, exp_le_exp]
  rcases le_total (t / (2 * A)) θ₀ with h | h
  · have hθe : θ = t / (2 * A) := min_eq_left h
    have : -θ * t + A * θ ^ 2 = -(t ^ 2 / (4 * A)) := by
      rw [hθe]
      field_simp
      ring
    rw [this]
    exact neg_le_neg (min_le_left _ _)
  · have hθe : θ = θ₀ := min_eq_right h
    have h3 : A * θ₀ ≤ t / 2 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * A)).1 h
      linarith
    have : -θ * t + A * θ ^ 2 ≤ -(θ₀ * t / 2) := by
      rw [hθe]
      nlinarith [mul_le_mul_of_nonneg_left h3 hθ₀.le]
    exact this.trans (neg_le_neg (min_le_right _ _))

end IsotropicVariance.Infra.Concentration
