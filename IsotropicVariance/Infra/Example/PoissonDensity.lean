/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Statements.Assumption.IsLocalDensity
public import IsotropicVariance.Statements.Configurations.PoissonConfigAgreeOn
public import IsotropicVariance.Statements.Configurations.PoissonConfigIsMovedBy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The convolution density of a Poisson configuration

The sentence after Theorem `thm:general` says that `ψ(χ∗ω)` satisfies Assumption `ass:local` also
when `ω` is a Poisson process. A Poisson configuration is a measure `ν`, and here `χ∗ν` is the
integral `x ↦ ∫ χ(x − y) dν(y)`. For a configuration `∑ᵢ δ_{pᵢ}` it is the sum `∑ᵢ χ(x − pᵢ)`
(`integral_sum_dirac_eq_sum`).

The density has to be jointly measurable on all of `Measure (Pt m)`, with no finiteness of `ν`, so
the kernel and Fubini lemmas do not apply. For `f` uniformly continuous, the positive part of
`∫ f(x − y) dν(y)` is a countable supremum of terms which are products of a measurable function of
`x` and a measurable function of `ν` (`measurable_lintegral_ofReal_sub`): if `|x − z| < δ` then
`f(z − ·) − ε ≤ f(x − ·)`, and monotone convergence as `ε ↓ 0` holds for every measure.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace Filter
open scoped Distributions ENNReal Topology

namespace IsotropicVariance.Infra.Example

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SeparableSpace E]

/-- For `f` uniformly continuous, `(ν, x) ↦ ∫⁻ y, (f (x - y))₊ ∂ν` is jointly measurable on the
space of all measures. With `δ n` a modulus of continuity at the scale `ε n = 1 / (n + 1)` and `z`
ranging over a dense sequence, it is the supremum over `n` and `z` of the term which is
`∫⁻ y, (f (z - y) - ε n)₊ ∂ν` where `dist x z < δ n`, and `0` elsewhere. -/
theorem measurable_lintegral_ofReal_sub {f : E → ℝ} (hf : UniformContinuous f) :
    Measurable fun p : Measure E × E => ∫⁻ y, ENNReal.ofReal (f (p.2 - y)) ∂p.1 := by
  have hmeas (z : E) (c : ℝ) : Measurable fun y => ENNReal.ofReal (f (z - y) - c) :=
    (ENNReal.continuous_ofReal.comp
      ((hf.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const)).measurable
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := Nat.one_div_pos_of_nat
  choose δ hδ hfδ using fun n => Metric.uniformContinuous_iff.1 hf (ε n) (hε n)
  have hsup : (fun p : Measure E × E => ∫⁻ y, ENNReal.ofReal (f (p.2 - y)) ∂p.1) = fun p =>
      ⨆ n : ℕ, ⨆ k : ℕ, if dist p.2 (denseSeq E k) < δ n then
        ∫⁻ y, ENNReal.ofReal (f (denseSeq E k - y) - ε n) ∂p.1 else 0 := by
    funext ⟨ν, x⟩
    apply le_antisymm
    · have hlim : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (f (x - y) - 2 * ε n) ∂ν) atTop
          (𝓝 (∫⁻ y, ENNReal.ofReal (f (x - y)) ∂ν)) := by
        refine lintegral_tendsto_of_tendsto_of_monotone (fun n => (hmeas x _).aemeasurable)
          (ae_of_all _ fun y i j hij => ENNReal.ofReal_le_ofReal ?_) (ae_of_all _ fun y => ?_)
        · have : ε j ≤ ε i := Nat.one_div_le_one_div hij
          linarith
        · have h0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          have h1 : Tendsto (fun n => f (x - y) - 2 * ε n) atTop (𝓝 (f (x - y) - 2 * 0)) :=
            tendsto_const_nhds.sub (h0.const_mul 2)
          rw [mul_zero, sub_zero] at h1
          exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp h1
      refine le_of_tendsto' hlim fun n => ?_
      obtain ⟨k, hk⟩ := (denseRange_denseSeq E).exists_dist_lt x (hδ n)
      refine le_trans ?_ (le_iSup₂ (f := fun (n k : ℕ) => if dist x (denseSeq E k) < δ n then
        ∫⁻ y, ENNReal.ofReal (f (denseSeq E k - y) - ε n) ∂ν else 0) n k)
      simp only [ite_eq_left hk]
      refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
      have h := hfδ n (a := x - y) (b := denseSeq E k - y) (by rwa [dist_sub_right])
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.1, h.2]
    · refine iSup_le fun n => iSup_le fun k => ?_
      split_ifs with hk
      · refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
        have h := hfδ n (a := x - y) (b := denseSeq E k - y) (by rwa [dist_sub_right])
        rw [Real.dist_eq, abs_lt] at h
        linarith [h.1, h.2]
      · exact zero_le
  rw [hsup]
  refine Measurable.iSup fun n => Measurable.iSup fun k => Measurable.ite ?_ ?_ measurable_const
  · exact measurable_snd Metric.isOpen_ball.measurableSet
  · exact (Measure.measurable_lintegral (hmeas _ _)).comp measurable_fst

/-- For `f` uniformly continuous, `(ν, x) ↦ ∫ y, f (x - y) ∂ν` is jointly measurable on the space
of all measures: it is the difference of the two lintegrals of the positive and negative parts
where they are finite, and `0` elsewhere. -/
theorem measurable_integral_sub {f : E → ℝ} (hf : UniformContinuous f) :
    Measurable fun p : Measure E × E => ∫ y, f (p.2 - y) ∂p.1 := by
  have hc (x : E) : Continuous fun y => f (x - y) :=
    hf.continuous.comp (continuous_const.sub continuous_id)
  have heq : (fun p : Measure E × E => ∫ y, f (p.2 - y) ∂p.1) = fun p =>
      if ∫⁻ y, ENNReal.ofReal ‖f (p.2 - y)‖ ∂p.1 < ∞ then
        (∫⁻ y, ENNReal.ofReal (f (p.2 - y)) ∂p.1).toReal -
          (∫⁻ y, ENNReal.ofReal (-f (p.2 - y)) ∂p.1).toReal
      else 0 := by
    funext ⟨ν, x⟩
    have hint : Integrable (fun y => f (x - y)) ν ↔ ∫⁻ y, ENNReal.ofReal ‖f (x - y)‖ ∂ν < ∞ := by
      simp only [ofReal_norm]
      exact ⟨fun h => h.2, fun h => ⟨(hc x).aestronglyMeasurable, h⟩⟩
    split_ifs with h
    · exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint.2 h)
    · exact integral_undef (mt hint.1 h)
  rw [heq]
  exact Measurable.ite
    (measurableSet_lt (measurable_lintegral_ofReal_sub (uniformContinuous_norm.comp hf))
      measurable_const)
    ((measurable_lintegral_ofReal_sub hf).ennreal_toReal.sub
      (measurable_lintegral_ofReal_sub (f := fun z => -f z) hf.neg).ennreal_toReal)
    measurable_const

end Measurability

/-- The density `ρ = ψ(χ∗ν)` of a Poisson configuration `ν`, with the argument of
`convolutionDensity` for white noise: `ρ(ν, x) = ψ(∫ χ(x − y) dν(y))`. -/
noncomputable def poissonConvolutionDensity {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ)) (ψ : ℝ → ℝ)
    (ν : Measure (Pt m)) (x : Pt m) : ℝ :=
  ψ (∫ y, χ (x - y) ∂ν)

/-- `y ↦ χ(x − y)` vanishes off the closed unit ball around `x`. -/
theorem apply_sub_eq_zero {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) {x y : Pt m} (hy : y ∉ Metric.closedBall x 1) :
    χ (x - y) = 0 := by
  refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
  simpa [dist_eq_norm, norm_sub_rev] using hχ hmem

/-- For a configuration `∑ᵢ δ_{pᵢ}` with finitely many points in the closed unit ball around `x`,
the integral of the density is the finite sum `(χ∗ω)(x) = ∑ᵢ χ(x − pᵢ)`. -/
theorem integral_sum_dirac_eq_sum {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) {ι : Type*} [Countable ι] (p : ι → Pt m) (x : Pt m)
    (hp : {i | p i ∈ Metric.closedBall x 1}.Finite) :
    ∫ y, χ (x - y) ∂(Measure.sum fun i => Measure.dirac (p i)) =
      ∑ i ∈ hp.toFinset, χ (x - p i) := by
  have h := integral_sum_dirac (f := fun y => χ (x - y)) (x := p) (c := fun _ => 1)
    (fun _ => ENNReal.one_ne_top)
  simp only [one_smul, ENNReal.toReal_one] at h
  rw [h]
  refine tsum_eq_sum fun i hi => apply_sub_eq_zero χ hχ ?_
  simpa using hi

/-- The density `ψ(χ∗ν)` satisfies Assumption `ass:local` (1): the integral sees `ν` only on the
closed unit ball around `x`. -/
theorem poissonConvolutionDensity_determined {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (x : Pt m) (ν ν' : Measure (Pt m))
    (h : PoissonConfig.AgreeOn (Metric.closedBall x 1) ν ν') :
    poissonConvolutionDensity χ ψ ν x = poissonConvolutionDensity χ ψ ν' x := by
  have hint (μ : Measure (Pt m)) :
      ∫ y in Metric.closedBall x 1, χ (x - y) ∂μ = ∫ y, χ (x - y) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => apply_sub_eq_zero χ hχ hy
  simp only [poissonConvolutionDensity]
  rw [← hint ν, ← hint ν', show ν.restrict _ = ν'.restrict _ from h]

/-- The density `ψ(χ∗ν)` satisfies Assumption `ass:local` (3), for every rigid motion (proper or
not). -/
theorem poissonConvolutionDensity_covariant {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y) (ψ : ℝ → ℝ) (g : Pt m ≃ᵃⁱ[ℝ] Pt m)
    (ν ν' : Measure (Pt m)) (h : PoissonConfig.IsMovedBy g ν ν') (x : Pt m) :
    poissonConvolutionDensity χ ψ ν' (g x) = poissonConvolutionDensity χ ψ ν x := by
  have hg : MeasurableEmbedding g := g.toHomeomorph.measurableEmbedding
  simp only [poissonConvolutionDensity]
  rw [show ν' = ν.map g from h, hg.integral_map]
  congr 2
  funext y
  refine hχ _ _ ?_
  rw [← dist_eq_norm, ← dist_eq_norm, g.dist_map]

/-- The density `ψ(χ∗ν)` is jointly measurable on the space of all measures. -/
theorem measurable_poissonConvolutionDensity {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ)) (ψ : ℝ → ℝ)
    (hψ : Continuous ψ) : Measurable (Function.uncurry (poissonConvolutionDensity χ ψ)) :=
  hψ.measurable.comp (measurable_integral_sub
    (χ.hasCompactSupport.uniformContinuous_of_continuous χ.contDiff.continuous))

/-- The Poisson convolution example satisfies all of Assumption `ass:local`, under the hypotheses
of `isLocalDensity_convolutionDensity`, for the literal definitions of the model. No probabilistic
property of the configuration is needed. -/
theorem isLocalDensity_poissonConvolutionDensity {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (a b : ℝ) (ha : 0 < a)
    (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy
      (poissonConvolutionDensity χ ψ) where
  measurable := measurable_poissonConvolutionDensity χ ψ hψ
  determined := poissonConvolutionDensity_determined χ hχ_support ψ
  bounds := ⟨a, b, ha, fun _ _ => hψ_bounds _⟩
  covariant g _ ν ν' h x := poissonConvolutionDensity_covariant χ hχ_radial ψ g ν ν' h x

end IsotropicVariance.Infra.Example
