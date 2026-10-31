/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
Ported from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability) at
99cfc20, LatticeProb/Prob/EfronSteinCountable.lean (sections `Energy`, the finite inequality read
on the field, and the countable inequality); modified: heterogeneous coordinate spaces and laws,
the finite step from `efronStein_fin`, `MemLp` hypotheses, and the one-sided and
coordinate-average forms.
-/
module

public import CurvatureVariance.Infra.EfronStein.PartialIntegral
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The Efron–Stein inequality on a countable product

Let `(X i, μ i)`, `i ∈ I`, be probability spaces with `I` countable, `P = Measure.infinitePi μ`,
and `F` a measurable square-integrable function on `Π i, X i`. With the resampling energies

`resampleEnergy μ F i = ∫⁻ x, ∫⁻ y, ofReal ((F x - F (x[i ↦ y]))²) dμᵢ(y) dP(x)`

in `ℝ≥0∞` (so that no junk value can make them small):

* `evariance_le_half_tsum_resampleEnergy`: `evariance F P ≤ (∑' i, resampleEnergy μ F i) / 2`;
* `evariance_le_half_sum_resampleEnergy_of_dependsOn`: the finite inequality for a function of
  the coordinates in a finite set, read on the countable product;
* `efronStein_fin` (in `CurvatureVariance.Infra.EfronStein.Finite`): the inequality on a finite
  product `Measure.pi μ`.

The countable inequality is proved as in Lattice-Probability: average out the coordinates outside
a finite set (`partialIntegral`), apply the finite inequality, bound the energies of the average by
those of `F` (Jensen), converge along an exhaustion (Lévy), and transfer the variance by Fatou.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CurvatureVariance.Infra.EfronStein

variable {I : Type*} [DecidableEq I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]

/-- The resampling energy of the coordinate `i`: the mean square change of `F` when `xᵢ` is
replaced by an independent sample of `μ i`, under the product law `Measure.infinitePi μ`. -/
def resampleEnergy (μ : (i : I) → Measure (X i)) (F : ((i : I) → X i) → ℝ) (i : I) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((F x - F (Function.update x i y)) ^ 2) ∂μ i
    ∂Measure.infinitePi μ

/-- The average `Eᵢ F x = ∫ F (x[i ↦ y]) dμᵢ(y)` of `F` over the coordinate `i`, the others fixed.
-/
def coordAverage (μ : (i : I) → Measure (X i)) (F : ((i : I) → X i) → ℝ) (i : I)
    (x : (i : I) → X i) : ℝ :=
  ∫ y, F (Function.update x i y) ∂μ i

omit [DecidableEq I] [∀ i, MeasurableSpace (X i)] in
theorem enorm_sub_sq_eq_ofReal (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg a), sq_abs]

theorem measurable_resampleSq {F : ((i : I) → X i) → ℝ} (hFm : Measurable F) (i : I) :
    Measurable (fun q : ((j : I) → X j) × X i => (F q.1 - F (Function.update q.1 i q.2)) ^ 2) :=
  ((hFm.comp measurable_fst).sub (hFm.comp measurable_update')).pow_const 2

variable (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem resampleEnergy_eq_lintegral_prod {F : ((i : I) → X i) → ℝ} (hFm : Measurable F)
    (i : I) :
    resampleEnergy μ F i =
      ∫⁻ q : ((j : I) → X j) × X i, ENNReal.ofReal ((F q.1 - F (Function.update q.1 i q.2)) ^ 2)
        ∂((Measure.infinitePi μ).prod (μ i)) :=
  (lintegral_prod _ (measurable_resampleSq hFm i).ennreal_ofReal.aemeasurable).symm

/-! ### The finite inequality, read on the countable product -/

omit [DecidableEq I] in
/-- The restriction `x ↦ (x (e j))_j` along an enumeration `e : Fin k ≃ S` of a finite set of
coordinates maps the product law to the finite product law. -/
theorem measurePreserving_restrict_fin (S : Finset I) :
    MeasurePreserving (fun (x : (i : I) → X i) (j : Fin S.card) => x (S.equivFin.symm j))
      (Measure.infinitePi μ) (Measure.pi fun j : Fin S.card => μ (S.equivFin.symm j)) := by
  have h₁ : MeasurePreserving (S.restrict (π := X)) (Measure.infinitePi μ)
      (Measure.pi fun i : S => μ i) :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict μ⟩
  have h₂ := (measurePreserving_piCongrLeft (fun i : S => μ i) S.equivFin.symm).symm
  exact h₂.comp h₁

/-! ### Jensen for the partial integral -/

/-- **The resampling energies of the partial integral are bounded by those of the function**:
averaging out the coordinates off `S` can only decrease the energy at a coordinate of `S`. -/
theorem resampleEnergy_partialIntegral_le {S : Set I} {i : I} (hi : i ∈ S)
    {F : ((i : I) → X i) → ℝ} (hFm : Measurable F) (hF : Integrable F (Measure.infinitePi μ)) :
    resampleEnergy μ (partialIntegral μ S F) i ≤ resampleEnergy μ F i := by
  set P := Measure.infinitePi μ with hP
  set Φ := partialIntegral μ S F with hΦ
  set D : ((j : I) → X j) × X i → ℝ := fun q => F q.1 - F (Function.update q.1 i q.2) with hD
  have h1 : ∀ᵐ ω ∂P, Integrable (fun η => F (resample S ω η)) P :=
    (integrable_comp_resample μ S hF).prod_right_ae
  have h1' : ∀ᵐ q ∂(P.prod (μ i)), Integrable (fun η => F (resample S q.1 η)) P :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h2 : ∀ᵐ q ∂(P.prod (μ i)),
      Integrable (fun η => F (resample S (Function.update q.1 i q.2) η)) P :=
    (measurePreserving_update_infinitePi μ i).quasiMeasurePreserving.ae h1
  have hae : ∀ᵐ q ∂(P.prod (μ i)),
      Φ q.1 - Φ (Function.update q.1 i q.2) = ∫ η, D (resample S q.1 η, q.2) ∂P := by
    filter_upwards [h1', h2] with q hq1 hq2
    have : Φ q.1 - Φ (Function.update q.1 i q.2)
        = ∫ η, (F (resample S q.1 η) - F (resample S (Function.update q.1 i q.2) η)) ∂P :=
      (integral_sub hq1 hq2).symm
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    simp only [hD, resample_update_of_mem hi]
  have hR : Measurable (fun r : ((j : I) → X j) × X i =>
      ENNReal.ofReal ((F r.1 - F (Function.update r.1 i r.2)) ^ 2)) :=
    (measurable_resampleSq hFm i).ennreal_ofReal
  have hjensen : ∀ q : ((j : I) → X j) × X i,
      ENNReal.ofReal ((∫ η, D (resample S q.1 η, q.2) ∂P) ^ 2)
        ≤ ∫⁻ η, ENNReal.ofReal ((D (resample S q.1 η, q.2)) ^ 2) ∂P := by
    intro q
    refine ofReal_sq_integral_le_lintegral P ?_
    have : Measurable (fun η : (j : I) → X j => D (resample S q.1 η, q.2)) :=
      ((hFm.comp measurable_fst).sub (hFm.comp measurable_update')).comp
        (((measurable_resample S).comp (measurable_const.prodMk measurable_id)).prodMk
          measurable_const)
    exact this.aestronglyMeasurable
  calc resampleEnergy μ Φ i
      = ∫⁻ q : ((j : I) → X j) × X i,
          ENNReal.ofReal ((Φ q.1 - Φ (Function.update q.1 i q.2)) ^ 2) ∂(P.prod (μ i)) :=
        resampleEnergy_eq_lintegral_prod μ (measurable_partialIntegral μ S hFm) i
    _ = ∫⁻ q : ((j : I) → X j) × X i,
          ENNReal.ofReal ((∫ η, D (resample S q.1 η, q.2) ∂P) ^ 2) ∂(P.prod (μ i)) :=
        lintegral_congr_ae (by filter_upwards [hae] with q hq; rw [hq])
    _ ≤ ∫⁻ q : ((j : I) → X j) × X i,
          (∫⁻ η, ENNReal.ofReal ((D (resample S q.1 η, q.2)) ^ 2) ∂P) ∂(P.prod (μ i)) :=
        lintegral_mono hjensen
    _ = resampleEnergy μ F i := by
        set Gf : ((j : I) → X j) → ℝ≥0∞ := fun ζ =>
          ∫⁻ t, ENNReal.ofReal ((F ζ - F (Function.update ζ i t)) ^ 2) ∂μ i with hGf
        have hGmeas : Measurable Gf := hR.lintegral_prod_right'
        have hHmeas : Measurable (fun p : (((j : I) → X j) × X i) × ((j : I) → X j) =>
            ENNReal.ofReal ((D (resample S p.1.1 p.2, p.1.2)) ^ 2)) :=
          hR.comp (((measurable_resample S).comp
            ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
              (measurable_snd.comp measurable_fst))
        have hstep1 : ∫⁻ q : ((j : I) → X j) × X i,
              (∫⁻ η, ENNReal.ofReal ((D (resample S q.1 η, q.2)) ^ 2) ∂P) ∂(P.prod (μ i))
            = ∫⁻ ω, ∫⁻ t, (∫⁻ η, ENNReal.ofReal ((D (resample S ω η, t)) ^ 2) ∂P) ∂μ i ∂P :=
          lintegral_prod _ (hHmeas.lintegral_prod_right').aemeasurable
        have hstep2 : ∀ ω : (j : I) → X j,
            ∫⁻ t, (∫⁻ η, ENNReal.ofReal ((D (resample S ω η, t)) ^ 2) ∂P) ∂μ i
              = ∫⁻ η, Gf (resample S ω η) ∂P := by
          intro ω
          have hswap : AEMeasurable (Function.uncurry
              (fun (t : X i) (η : (j : I) → X j) => ENNReal.ofReal ((D (resample S ω η, t)) ^ 2)))
              ((μ i).prod P) :=
            (hR.comp (((measurable_resample S).comp
              (measurable_const.prodMk measurable_snd)).prodMk measurable_fst)).aemeasurable
          exact lintegral_lintegral_swap hswap
        have hstep3 : ∫⁻ ω, (∫⁻ η, Gf (resample S ω η) ∂P) ∂P
            = ∫⁻ p : ((j : I) → X j) × ((j : I) → X j), Gf (resample S p.1 p.2) ∂(P.prod P) :=
          (lintegral_prod _ (hGmeas.comp (measurable_resample S)).aemeasurable).symm
        have hstep4 : ∫⁻ p : ((j : I) → X j) × ((j : I) → X j), Gf (resample S p.1 p.2)
              ∂(P.prod P) = ∫⁻ ζ, Gf ζ ∂P :=
          (measurePreserving_resample μ S).lintegral_comp hGmeas
        rw [hstep1, lintegral_congr fun ω => hstep2 ω, hstep3, hstep4]
        rfl

/-! ### The coordinate-average form -/

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- Averaging over the coordinate `i` does not see the coordinate `i`. -/
theorem coordAverage_update (F : ((i : I) → X i) → ℝ) (i : I) (x : (j : I) → X j) (a : X i) :
    coordAverage μ F i (Function.update x i a) = coordAverage μ F i x := by
  simp only [coordAverage, Function.update_idem]

omit [DecidableEq I] [∀ i, MeasurableSpace (X i)] [∀ i, IsProbabilityMeasure (μ i)] in
/-- On one probability space, the mean square difference of two independent copies is twice the
variance, in `ℝ≥0∞`. -/
theorem lintegral_lintegral_ofReal_sub_sq {A : Type*} [MeasurableSpace A] {ν : Measure A}
    [IsProbabilityMeasure ν] {g : A → ℝ} (hgm : Measurable g) (hg : MemLp g 2 ν) :
    ∫⁻ a, ∫⁻ b, ENNReal.ofReal ((g a - g b) ^ 2) ∂ν ∂ν =
      2 * ∫⁻ a, ENNReal.ofReal ((g a - ∫ b, g b ∂ν) ^ 2) ∂ν := by
  have hd : MemLp (fun q : A × A => g q.1 - g q.2) 2 (ν.prod ν) :=
    (hg.comp_measurePreserving (measurePreserving_fst (μ := ν) (ν := ν))).sub
      (hg.comp_measurePreserving (measurePreserving_snd (μ := ν) (ν := ν)))
  have hdi := hd.integrable_sq
  have hdm : Measurable (fun q : A × A => ENNReal.ofReal ((g q.1 - g q.2) ^ 2)) :=
    (((hgm.comp measurable_fst).sub (hgm.comp measurable_snd)).pow_const 2).ennreal_ofReal
  have hc : MemLp (fun a => g a - ∫ b, g b ∂ν) 2 ν := hg.sub (memLp_const _)
  rw [← lintegral_prod _ hdm.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal hdi (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hc.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _), integral_prod _ hdi]
  have h1 := integral_sq_sub_sq_integral_eq_half hg
  have h2 := integral_sub_integral_sq hg
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  simp only at h1 ⊢
  linarith

/-- The resampling energy of a coordinate is twice the squared `L²` norm of `F - Eᵢ F`:
`E ∫ (F x - F (x[i ↦ y]))² dμᵢ(y) = 2 ‖F - Eᵢ F‖₂²`. -/
theorem resampleEnergy_eq_two_mul_lintegral_sub_coordAverage {F : ((i : I) → X i) → ℝ}
    (hFm : Measurable F) (hF : MemLp F 2 (Measure.infinitePi μ)) (i : I) :
    resampleEnergy μ F i =
      2 * ∫⁻ x, ENNReal.ofReal ((F x - coordAverage μ F i x) ^ 2) ∂Measure.infinitePi μ := by
  set P := Measure.infinitePi μ with hP
  have hu := measurePreserving_update_infinitePi μ i
  -- the sections `a ↦ F (x[i ↦ a])` are in `L²(μ i)` for almost every `x`
  have hsec : MemLp (fun q : ((j : I) → X j) × X i => F (Function.update q.1 i q.2)) 2
      (P.prod (μ i)) := hF.comp_measurePreserving hu
  have hsec_ae : ∀ᵐ x ∂P, MemLp (fun a => F (Function.update x i a)) 2 (μ i) := by
    filter_upwards [hsec.integrable_sq.prod_right_ae] with x hx
    exact (memLp_two_iff_integrable_sq
      (hFm.comp (measurable_update x)).aestronglyMeasurable).mpr hx
  have hmE : Measurable (fun x : (j : I) → X j =>
      ∫⁻ y, ENNReal.ofReal ((F x - F (Function.update x i y)) ^ 2) ∂μ i) :=
    (measurable_resampleSq hFm i).ennreal_ofReal.lintegral_prod_right'
  have hmA : Measurable (coordAverage μ F i) :=
    (hFm.comp measurable_update').stronglyMeasurable.integral_prod_right'.measurable
  have hmV : Measurable (fun x : (j : I) → X j =>
      ENNReal.ofReal ((F x - coordAverage μ F i x) ^ 2)) :=
    ((hFm.sub hmA).pow_const 2).ennreal_ofReal
  have hE : resampleEnergy μ F i = ∫⁻ x, ∫⁻ a, ∫⁻ y,
      ENNReal.ofReal ((F (Function.update x i a) - F (Function.update x i y)) ^ 2)
        ∂μ i ∂μ i ∂P := by
    rw [resampleEnergy, ← hu.lintegral_comp hmE, lintegral_prod]
    · simp only [Function.update_idem]
      rfl
    · exact (hmE.comp measurable_update').aemeasurable
  have hV : ∫⁻ x, ENNReal.ofReal ((F x - coordAverage μ F i x) ^ 2) ∂P = ∫⁻ x, ∫⁻ a,
      ENNReal.ofReal ((F (Function.update x i a) - coordAverage μ F i x) ^ 2) ∂μ i ∂P := by
    rw [← hu.lintegral_comp hmV, lintegral_prod]
    · simp only [coordAverage_update]
      rfl
    · exact (hmV.comp measurable_update').aemeasurable
  rw [hE, hV, ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_congr_ae ?_
  filter_upwards [hsec_ae] with x hx
  exact lintegral_lintegral_ofReal_sub_sq (hFm.comp (measurable_update x)) hx

/-! ### Square-integrable functions

The energies do not see a modification of `F` on a null set, because resampling one coordinate
preserves the product law. So the inequalities hold for every `F ∈ L²`, measurable or not. -/

/-- Almost everywhere, `F` and `G` agree at `x` and at almost every resampling of the coordinate
`i` of `x`. -/
theorem ae_ae_update_eq {F G : ((i : I) → X i) → ℝ} (h : F =ᵐ[Measure.infinitePi μ] G) (i : I) :
    ∀ᵐ x ∂Measure.infinitePi μ, F x = G x ∧
      ∀ᵐ y ∂μ i, F (Function.update x i y) = G (Function.update x i y) := by
  have h2 : ∀ᵐ q ∂((Measure.infinitePi μ).prod (μ i)),
      F (Function.update q.1 i q.2) = G (Function.update q.1 i q.2) :=
    (measurePreserving_update_infinitePi μ i).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [h, Measure.ae_ae_of_ae_prod h2] with x hx hy
  exact ⟨hx, hy⟩

theorem resampleEnergy_congr_ae {F G : ((i : I) → X i) → ℝ}
    (h : F =ᵐ[Measure.infinitePi μ] G) (i : I) : resampleEnergy μ F i = resampleEnergy μ G i := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ae_update_eq μ h i] with x hx
  refine lintegral_congr_ae ?_
  filter_upwards [hx.2] with y hy
  rw [hx.1, hy]

end CurvatureVariance.Infra.EfronStein
