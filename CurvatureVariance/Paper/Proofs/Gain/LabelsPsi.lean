/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.AVEnergy
public import CurvatureVariance.Paper.Proofs.Gain.FALocalize
import CurvatureVariance.Paper.Proofs.Moments.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The conditional expectation `Ψ` of Lemma `lem:labels`

Step 1 of the proof of [AB26, Lemma 6.2], as the proof of Lemma `lem:labels` changes it.

The paper sets `Φ = (T^{(i)}(u,v) − ζ_t·(v−u))/Q_n` on `Γ_G`, and `Ψ = E[Φ | τ|_G]`. Here `Ψ` is an
actual function on the configurations, an integral over an independent copy of the weights outside
`G` (`labelPsi`): `Ψ ω = ∫ ω', Φ (resample Gᶜ ω ω') dP`. So "determined by `τ|_G`" is a congruence
(`labelPsi_congr`), the translation property holds at every `ω` by the change of variables
`ω' ↦ θ ω'` (`labelPsi_translate`), and the conditional Jensen inequality is Jensen's inequality for
the integral:

* `lintegral_pow_le`: `(∫ f)^k ≤ ∫ f^k` on a probability space.
* `lintegral_ofReal_fiberIntegral_pow_le`: the `k`-th moment of `ω ↦ ∫ ω', Z (ω', ω)` is at most the
  `k`-th moment of `Z` on the product.
* `ae_abs_fiberIntegral_le`: an almost sure bound `|F i| ≤ Z` on the product, for all `i` at once,
  gives `|∫ ω', F i (ω', ω)| ≤ ∫ ω', Z (ω', ω)` for almost every `ω`.

The order of the product is that of `Gain.outsideSplice`: a pair is `z = (ω', ω)`, and
`outsideSplice G (ω', ω) = resample Gᶜ ω ω'` (`resample_compl_eq_outsideSplice`) has the weights of
`ω` on `G` and those of `ω'` off `G`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Jensen's inequality for the integral -/

section Jensen

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Jensen's inequality for a power**: `(∫ f)^k ≤ ∫ f^k` on a probability space, for `k ≥ 1`. -/
theorem lintegral_pow_le {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {k : ℕ} (hk : 1 ≤ k) :
    (∫⁻ ω, f ω ∂P) ^ k ≤ ∫⁻ ω, f ω ^ k ∂P := by
  rcases hk.eq_or_lt with rfl | hk1
  · simp
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hconj := Real.HolderConjugate.conjExponent hk'
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have hpow : ∀ ω, f ω ^ (k : ℝ) = f ω ^ k := fun ω => ENNReal.rpow_natCast _ _
  simp only [hpow] at h
  have h' : ∫⁻ ω, f ω ∂P ≤ (∫⁻ ω, f ω ^ k ∂P) ^ (1 / (k : ℝ)) := by
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) h
    simp
  calc (∫⁻ ω, f ω ∂P) ^ k
      ≤ ((∫⁻ ω, f ω ^ k ∂P) ^ (1 / (k : ℝ))) ^ k := by gcongr
    _ = ∫⁻ ω, f ω ^ k ∂P := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel hk0.ne', ENNReal.rpow_one]

/-- A property of almost every pair holds for almost every second coordinate, for almost every first
coordinate. -/
theorem ae_ae_swap {Q : Ω × Ω → Prop} (h : ∀ᵐ z ∂(P.prod P), Q z) :
    ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, Q (ω', ω) := by
  have hswap : ∀ᵐ z ∂(P.prod P), Q z.swap :=
    (Measure.measurePreserving_swap (μ := P) (ν := P)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod hswap

/-- **The conditional Jensen inequality, for the moments**: the `k`-th moment of
`ω ↦ ∫ ω', Z (ω', ω)` is at most that of `Z` on the product. -/
theorem lintegral_ofReal_fiberIntegral_pow_le {Z : Ω × Ω → ℝ} (hZ : Measurable Z) {k : ℕ}
    (hk : 1 ≤ k) :
    ∫⁻ ω, ENNReal.ofReal (|∫ ω', Z (ω', ω) ∂P| ^ k) ∂P ≤
      ∫⁻ z, ENNReal.ofReal (|Z z| ^ k) ∂(P.prod P) := by
  have hm : Measurable fun z => ENNReal.ofReal (|Z z| ^ k) :=
    ((_root_.continuous_abs.measurable.comp hZ).pow_const k).ennreal_ofReal
  rw [lintegral_prod_symm' _ hm]
  refine lintegral_mono fun ω => ?_
  have hmω : Measurable fun ω' => ‖Z (ω', ω)‖ₑ :=
    (hZ.comp (measurable_id.prodMk measurable_const)).enorm
  calc ENNReal.ofReal (|∫ ω', Z (ω', ω) ∂P| ^ k)
      = ‖∫ ω', Z (ω', ω) ∂P‖ₑ ^ k := by
        rw [ENNReal.ofReal_pow (abs_nonneg _), Real.enorm_eq_ofReal_abs]
    _ ≤ (∫⁻ ω', ‖Z (ω', ω)‖ₑ ∂P) ^ k := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ ω', ‖Z (ω', ω)‖ₑ ^ k ∂P := lintegral_pow_le hmω.aemeasurable hk
    _ = ∫⁻ ω', ENNReal.ofReal (|Z (ω', ω)| ^ k) ∂P := by
        refine lintegral_congr fun ω' => ?_
        rw [ENNReal.ofReal_pow (abs_nonneg _), Real.enorm_eq_ofReal_abs]

/-- **The conditional Jensen inequality, pointwise**: an almost sure bound `|F i| ≤ Z` on the
product, for all `i ∈ A` at once, passes to the integrals over the first coordinate. -/
theorem ae_abs_fiberIntegral_le {ι : Type*} {A : Set ι} {F : ι → Ω × Ω → ℝ} {Z : Ω × Ω → ℝ}
    (hZ : Integrable Z (P.prod P)) (hF : ∀ᵐ z ∂(P.prod P), ∀ i ∈ A, |F i z| ≤ Z z) :
    ∀ᵐ ω ∂P, ∀ i ∈ A, |∫ ω', F i (ω', ω) ∂P| ≤ ∫ ω', Z (ω', ω) ∂P := by
  filter_upwards [hZ.prod_left_ae, ae_ae_swap hF] with ω hint hb i hi
  have h := norm_integral_le_of_norm_le (f := fun ω' => F i (ω', ω)) hint
    (hb.mono fun ω' hω' => hω' i hi)
  simpa only [Real.norm_eq_abs] using h

/-- A function with a finite moment of order `k ≥ 1` on the product is integrable. -/
theorem integrable_of_lintegral_ofReal_pow_lt {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → ℝ}
    (hZ : AEStronglyMeasurable Z μ) {k : ℕ} (hk : 1 ≤ k) {c : ℝ}
    (h : ∫⁻ z, ENNReal.ofReal (|Z z| ^ k) ∂μ ≤ ENNReal.ofReal c) : Integrable Z μ := by
  have hk0 : k ≠ 0 := by omega
  have hk0' : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk0
  have hMem : MemLp Z k μ := by
    refine lt_of_le_of_lt (le_of_eq ?_) (ENNReal.rpow_lt_top_of_nonneg (y := 1 / (k : ℝ))
      (by positivity) (h.trans_lt ENNReal.ofReal_lt_top).ne)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hk0' (ENNReal.natCast_ne_top k) hZ,
      ENNReal.toReal_natCast]
    have heq : ∀ z, ‖Z z‖ₑ ^ (k : ℝ) = ENNReal.ofReal (|Z z| ^ k) := fun z => by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_natCast, ENNReal.ofReal_pow (abs_nonneg _)]
    simp_rw [heq]
  exact hMem.integrable (by exact_mod_cast hk)

end Jensen

/-! ### The function `Ψ` -/

/-- The normalized slab passage time is measurable in the configuration. -/
theorem measurable_normSlabTime (M : Model m) (K : ℕ) (A : ℝ) (n : ℕ) (P : Pt m) (i : ℕ)
    (u v : Vertex m) : Measurable fun ω => normSlabTime M K A ω n P i u v :=
  (((Responses.measurable_restrictedTime _ u v).ennreal_toReal).sub_const _).div_const _

/-- **The function `Ψ`** of the proof of Lemma `lem:labels`: `Ψ ω = ∫ ω', Φ (resample Gᶜ ω ω') dP`,
the normalized slab passage time `Φ` integrated over an independent copy of the weights outside `G`.
-/
noncomputable def labelPsi (M : Model m) (K : ℕ) (A : ℝ) (n : ℕ) (P : Pt m) (i : ℕ)
    (G : Set (Sym2 (Vertex m))) (ω : Config m) (u v : Vertex m) : ℝ :=
  ∫ ω', normSlabTime M K A (resample Gᶜ ω ω') n P i u v ∂M.P

/-- `Ψ` in the order of `outsideSplice`: `resample Gᶜ ω ω'` has the weights of `ω` on `G` and those
of `ω'` off `G`. -/
theorem resample_compl_eq_outsideSplice (G : Set (Sym2 (Vertex m))) (ω ω' : Config m) :
    resample Gᶜ ω ω' = outsideSplice G (ω', ω) := by
  classical
  funext e
  by_cases he : e.1 ∈ G <;> simp [outsideSplice, resample, he]

/-- `Ψ` is the integral of `Φ` at the splice. -/
theorem labelPsi_eq (M : Model m) (K : ℕ) (A : ℝ) (n : ℕ) (P : Pt m) (i : ℕ)
    (G : Set (Sym2 (Vertex m))) (ω : Config m) (u v : Vertex m) :
    labelPsi M K A n P i G ω u v =
      ∫ ω', normSlabTime M K A (outsideSplice G (ω', ω)) n P i u v ∂M.P := by
  simp only [labelPsi, resample_compl_eq_outsideSplice]

/-- **`Ψ` is determined by `τ|_G`.** -/
theorem labelPsi_congr (M : Model m) (K : ℕ) (A : ℝ) (n : ℕ) (P : Pt m) (i : ℕ)
    (G : Set (Sym2 (Vertex m))) {ω ω₁ : Config m} (h : ∀ e : Edge m, e.1 ∈ G → ω e = ω₁ e) :
    labelPsi M K A n P i G ω = labelPsi M K A n P i G ω₁ := by
  have hσ : ∀ ω', outsideSplice G (ω', ω) = outsideSplice G (ω', ω₁) := fun ω' => by
    classical
    funext e
    by_cases he : e.1 ∈ G
    · simp only [outsideSplice, resample, he, ite_true]
      exact h e he
    · simp only [outsideSplice, resample, he, ite_false]
  funext u v
  simp only [labelPsi_eq, hσ]

/-- `Ψ` is measurable. -/
theorem measurable_labelPsi (M : Model m) (K : ℕ) (A : ℝ) (n : ℕ) (P : Pt m) (i : ℕ)
    (G : Set (Sym2 (Vertex m))) (u v : Vertex m) (hP : IsProbabilityMeasure M.P) :
    Measurable fun ω => labelPsi M K A n P i G ω u v := by
  have hf : Measurable fun z : Config m × Config m =>
      normSlabTime M K A (resample Gᶜ z.1 z.2) n P i u v :=
    (measurable_normSlabTime M K A n P i u v).comp (Responses.measurable_resample Gᶜ)
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

/-- The normalized slab passage times are invariant under transverse translations. -/
theorem normSlabTime_translate_neg' (M : Model m) (K : ℕ) (A : ℝ) (ω : Config m) (n : ℕ)
    (P : Pt m) (i : ℕ) {a : Vertex m} (ha : a.1 = 0) (u v : Vertex m) :
    normSlabTime M K A (translate (-a) ω) n P i (u + a) (v + a) =
      normSlabTime M K A ω n P i u v := by
  unfold normSlabTime
  rw [slabTimeReal_translate]
  simp only [Prod.fst_neg, ha, neg_zero, add_zero, add_neg_cancel_right, point_add,
    add_sub_add_right_eq_sub]

/-- **The translation property of `Ψ`, at every `ω`** (the proof of Lemma `lem:labels`): if the
transverse vector `a` moves `G` onto `G'`, then `Ψ` of `G'` at the weights `(τ_{e−a})_e` and the
points `u + a`, `v + a` is `Ψ` of `G` at `(τ_e)_e` and `u`, `v`. This is the change of variables by
the translation, which preserves the law of the weights. -/
theorem labelPsi_translate {M : Model m} (hM : M.Standing) (K : ℕ) (A : ℝ) (n : ℕ) (P : Pt m)
    (i : ℕ) {G G' : Set (Sym2 (Vertex m))} {a : Vertex m} (ha : a.1 = 0)
    (hG : ∀ e : Sym2 (Vertex m), Sym2.map (· + a) e ∈ G' ↔ e ∈ G) (ω : Config m) (u v : Vertex m) :
    labelPsi M K A n P i G' (translate (-a) ω) (u + a) (v + a) =
      labelPsi M K A n P i G ω u v := by
  have hmp : MeasurePreserving (translateEquiv (-a)) M.P M.P :=
    Moments.standing_measurePreserving_translate hM (-a)
  have hset : {s : Sym2 (Vertex m) | Sym2.map (· + -a) s ∈ Gᶜ} = G'ᶜ := by
    ext s
    have hid : ((fun x : Vertex m => x + a) ∘ fun x => x + -a) = id := by
      funext x
      simp
    have h := hG (Sym2.map (· + -a) s)
    rw [Sym2.map_map, hid, Sym2.map_id, id] at h
    simp only [mem_ofPred_eq, mem_compl_iff]
    exact not_congr h.symm
  unfold labelPsi
  rw [← hmp.integral_comp' (fun ω' => normSlabTime M K A (resample G'ᶜ (translate (-a) ω) ω') n P i
    (u + a) (v + a))]
  refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
  change normSlabTime M K A (resample G'ᶜ (translate (-a) ω) (translate (-a) ω')) n P i
    (u + a) (v + a) = _
  rw [← hset, ← translate_resample, normSlabTime_translate_neg' M K A _ n P i ha]

end CurvatureVariance.Paper.Gain
