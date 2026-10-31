/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
Ported from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability) at
99cfc20, LatticeProb/Prob/Splice.lean and LatticeProb/Prob/EfronSteinCountable.lean
(sections `Cond` and `Converge`); modified: heterogeneous coordinates,
splicing through `resample`, conditioning through `condExp_coordinateSigma_ae_eq`.
-/
module

public import IsotropicVariance.Infra.EfronStein.Coordinates
public import IsotropicVariance.Infra.EfronStein.Finite
public import Mathlib.Probability.Martingale.Convergence

/-!
# The partial integral over the coordinates outside a set

For a product law `P = Measure.infinitePi μ` and a set `S` of coordinates,
`partialIntegral μ S F ω = ∫ F (resample S ω η) dP(η)` averages `F` over the coordinates outside
`S`. It reads only the coordinates in `S` (`partialIntegral_congr`), has the mean of `F`
(`integral_partialIntegral`), is a version of the conditional expectation on the coordinates in
`S` (`partialIntegral_ae_eq_condExp`), and along an increasing exhaustion of the index set it
converges almost everywhere to `F` (`tendsto_partialIntegral`, Lévy's upward theorem).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace IsotropicVariance.Infra.EfronStein

/-- Jensen's inequality for the square, for an integrable function with integrable square. -/
theorem sq_integral_le_of_integrable {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {g : α → ℝ} (hg : Integrable g P)
    (hg2 : Integrable (fun x => g x ^ 2) P) :
    (∫ x, g x ∂P) ^ 2 ≤ ∫ x, g x ^ 2 ∂P :=
  sq_integral_le_integral_sq ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hg2)

/-- **Jensen's inequality for the square of an average, in `ℝ≥0∞`.** No integrability is
assumed: if the upper integral of the square is infinite the bound is vacuous. -/
theorem ofReal_sq_integral_le_lintegral {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {g : α → ℝ} (hg : AEStronglyMeasurable g P) :
    ENNReal.ofReal ((∫ x, g x ∂P) ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂P := by
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂P = ⊤
  · simp [hfin]
  · have hnn : (0 : α → ℝ) ≤ᵐ[P] fun x => g x ^ 2 :=
      Filter.Eventually.of_forall fun x => sq_nonneg _
    have hg2 : Integrable (fun x => g x ^ 2) P := by
      refine ⟨hg.pow 2, ?_⟩
      have henorm : ∀ x : α, ‖g x ^ 2‖ₑ = ENNReal.ofReal (g x ^ 2) := fun x =>
        Real.enorm_eq_ofReal (sq_nonneg _)
      unfold HasFiniteIntegral
      simp only [henorm]
      exact lt_of_le_of_ne le_top hfin
    have hgi : Integrable g P := by
      refine Integrable.mono ((integrable_const (1 : ℝ)).add hg2) hg ?_
      filter_upwards with x
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + g x ^ 2)]
      nlinarith [sq_abs (g x), abs_nonneg (g x), sq_nonneg (|g x| - 1)]
    calc ENNReal.ofReal ((∫ x, g x ∂P) ^ 2)
        ≤ ENNReal.ofReal (∫ x, g x ^ 2 ∂P) :=
          ENNReal.ofReal_le_ofReal (sq_integral_le_of_integrable P hgi hg2)
      _ = ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂P :=
          ofReal_integral_eq_lintegral_ofReal hg2 hnn

variable {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)]

/-- The average of `F` over the coordinates outside `S`, a functional of the coordinates in `S`
alone. -/
def partialIntegral (μ : (i : I) → Measure (X i)) (S : Set I)
    (F : ((i : I) → X i) → ℝ) (ω : (i : I) → X i) : ℝ :=
  ∫ η, F (resample S ω η) ∂Measure.infinitePi μ

variable (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- The partial integral reads only the coordinates in `S`. -/
theorem partialIntegral_congr (S : Set I) (F : ((i : I) → X i) → ℝ)
    {ω ω' : (i : I) → X i} (h : ∀ i ∈ S, ω i = ω' i) :
    partialIntegral μ S F ω = partialIntegral μ S F ω' := by
  unfold partialIntegral
  simp only [resample_congr_left h]

theorem measurable_partialIntegral (S : Set I) {F : ((i : I) → X i) → ℝ}
    (hF : Measurable F) : Measurable (partialIntegral μ S F) :=
  ((hF.comp (measurable_resample S)).stronglyMeasurable.integral_prod_right' (ν :=
    Measure.infinitePi μ)).measurable

/-- Splicing carries an integrable functional to an integrable functional of the pair. -/
theorem integrable_comp_resample (S : Set I) {F : ((i : I) → X i) → ℝ}
    (hF : Integrable F (Measure.infinitePi μ)) :
    Integrable (fun p : ((i : I) → X i) × ((i : I) → X i) => F (resample S p.1 p.2))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) :=
  (measurePreserving_resample μ S).integrable_comp_of_integrable hF

/-- The partial integral of an integrable functional is integrable. -/
theorem integrable_partialIntegral (S : Set I) {F : ((i : I) → X i) → ℝ}
    (hF : Integrable F (Measure.infinitePi μ)) :
    Integrable (partialIntegral μ S F) (Measure.infinitePi μ) :=
  (integrable_comp_resample μ S hF).integral_prod_left

/-- The partial integral has the same mean as the functional. -/
theorem integral_partialIntegral (S : Set I) {F : ((i : I) → X i) → ℝ}
    (hF : Integrable F (Measure.infinitePi μ)) :
    ∫ ω, partialIntegral μ S F ω ∂Measure.infinitePi μ = ∫ ω, F ω ∂Measure.infinitePi μ := by
  have hmap := (measurePreserving_resample μ S).map_eq
  have hasm : AEStronglyMeasurable F
      (Measure.map (fun p : ((i : I) → X i) × ((i : I) → X i) => resample S p.1 p.2)
        ((Measure.infinitePi μ).prod (Measure.infinitePi μ))) := by
    rw [hmap]; exact hF.aestronglyMeasurable
  have h : ∫ p, F (resample S p.1 p.2) ∂((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      = ∫ ω, F ω ∂Measure.infinitePi μ := by
    rw [← integral_map (measurable_resample S).aemeasurable hasm, hmap]
  rw [← h, integral_prod _ (integrable_comp_resample μ S hF)]
  rfl

/-- Jensen for the partial integral: the square of the average is at most the average of the
square. -/
theorem sq_partialIntegral_le (S : Set I) {F : ((i : I) → X i) → ℝ}
    (hF : Integrable F (Measure.infinitePi μ))
    (hF2 : Integrable (fun ω => F ω ^ 2) (Measure.infinitePi μ)) :
    ∀ᵐ ω ∂Measure.infinitePi μ,
      (partialIntegral μ S F ω) ^ 2 ≤ partialIntegral μ S (fun x => F x ^ 2) ω := by
  filter_upwards [(integrable_comp_resample μ S hF).prod_right_ae,
    (integrable_comp_resample μ S hF2).prod_right_ae] with ω hω1 hω2
  exact sq_integral_le_of_integrable _ hω1 hω2

/-- The partial integral of a square-integrable functional is square integrable. -/
theorem integrable_sq_partialIntegral (S : Set I) {F : ((i : I) → X i) → ℝ}
    (hFm : Measurable F) (hF : Integrable F (Measure.infinitePi μ))
    (hF2 : Integrable (fun ω => F ω ^ 2) (Measure.infinitePi μ)) :
    Integrable (fun ω => (partialIntegral μ S F ω) ^ 2) (Measure.infinitePi μ) := by
  refine Integrable.mono (integrable_partialIntegral μ S hF2)
    (((measurable_partialIntegral μ S hFm).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [sq_partialIntegral_le μ S hF hF2] with ω hω
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [abs_of_nonneg (show (0:ℝ) ≤ partialIntegral μ S (fun ω => F ω ^ 2) ω from
    integral_nonneg fun _ => sq_nonneg _)]
  exact hω

/-- **The partial integral is the conditional expectation on the coordinates in `S`.** -/
theorem partialIntegral_ae_eq_condExp (S : Set I) {F : ((i : I) → X i) → ℝ}
    (hFm : Measurable F) (hF : Integrable F (Measure.infinitePi μ)) :
    partialIntegral μ S F =ᵐ[Measure.infinitePi μ]
      (Measure.infinitePi μ)[F | coordinateSigma X S] :=
  (condExp_coordinateSigma_ae_eq μ S hFm hF).symm

/-- **The partial integrals converge to the functional** along an increasing exhaustion of the
index set (Lévy's upward theorem). -/
theorem tendsto_partialIntegral {S : ℕ → Set I} (hmono : Monotone S)
    (hcov : ∀ i : I, ∃ n, i ∈ S n) {F : ((i : I) → X i) → ℝ} (hFm : Measurable F)
    (hF : Integrable F (Measure.infinitePi μ)) :
    ∀ᵐ ω ∂Measure.infinitePi μ,
      Tendsto (fun n => partialIntegral μ (S n) F ω) atTop (𝓝 (F ω)) := by
  set ℱ := coordinateFiltration X S hmono with hℱ
  have hsup : (⨆ n, ℱ n) = (MeasurableSpace.pi : MeasurableSpace ((i : I) → X i)) :=
    iSup_coordinateSigma_eq_pi X S hcov
  have hgmeas : StronglyMeasurable[⨆ n, ℱ n] F := by
    rw [hsup]; exact hFm.stronglyMeasurable
  have hlim := hF.tendsto_ae_condExp (ℱ := ℱ) hgmeas
  have heq' : ∀ᵐ ω ∂Measure.infinitePi μ, ∀ n,
      partialIntegral μ (S n) F ω = ((Measure.infinitePi μ)[F | ℱ n]) ω :=
    ae_all_iff.2 fun n => partialIntegral_ae_eq_condExp μ (S n) hFm hF
  filter_upwards [hlim, heq'] with ω hω hωeq
  exact hω.congr fun n => (hωeq n).symm

end IsotropicVariance.Infra.EfronStein
