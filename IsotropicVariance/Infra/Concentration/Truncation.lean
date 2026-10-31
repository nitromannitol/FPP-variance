/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.Tails
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Truncation for BLM Corollary 3

Symmetric clips decrease positive refresh differences and converge in integral
to every integrable function. Strict tail events survive this limit.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal
namespace IsotropicVariance.Infra.Concentration

/-- Symmetric truncation to `[-R,R]`. -/
noncomputable def clip (R x : ℝ) : ℝ := max (min x R) (-R)

/-- A scalar clip is monotone. -/
theorem monotone_clip (R : ℝ) : Monotone (clip R) :=
  fun _ _ h => max_le_max (min_le_min h le_rfl) le_rfl

/-- Clipping contracts absolute differences. -/
theorem abs_clip_sub_clip_le (R a b : ℝ) : |clip R a - clip R b| ≤ |a - b| := by
  calc
    _ ≤ |min a R - min b R| := abs_max_sub_max_le_abs _ _ _
    _ ≤ max |a - b| |R - R| := abs_min_sub_min_le_max _ _ _ _
    _ = _ := by simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))]

/-- Clipping contracts positive differences. -/
theorem positive_clip_sub_le (R a b : ℝ) :
    max (clip R a - clip R b) 0 ≤ max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.mpr (monotone_clip R h))]
    exact le_max_right _ _
  · rw [max_eq_left (sub_nonneg.mpr h)]
    exact max_le ((le_abs_self _).trans ((abs_clip_sub_clip_le R a b).trans_eq
      (abs_of_nonneg (sub_nonneg.mpr h)))) (sub_nonneg.mpr h)

/-- Clipping fixes points in its interval. -/
theorem clip_eq_self {R x : ℝ} (h₁ : -R ≤ x) (h₂ : x ≤ R) : clip R x = x := by
  simp only [clip, min_eq_left h₂, max_eq_left h₁]

/-- A nonnegative-radius clip fixes zero. -/
theorem clip_zero {R : ℝ} (hR : 0 ≤ R) : clip R 0 = 0 :=
  clip_eq_self (neg_nonpos.mpr hR) hR

/-- Symmetric clipping decreases absolute values. -/
theorem abs_clip_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clip R x| ≤ |x| := by
  simpa only [clip_zero hR, sub_zero] using abs_clip_sub_clip_le R x 0

/-- A clip is bounded by its radius. -/
theorem abs_clip_le_radius {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clip R x| ≤ R := by
  apply abs_le.mpr
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith only [hR])⟩

/-- Scalar clipping is measurable. -/
theorem measurable_clip (R : ℝ) : Measurable (clip R) :=
  (measurable_id.min measurable_const).max measurable_const

/-- Integer clips converge pointwise, eventually identically. -/
theorem tendsto_clip (x : ℝ) : Tendsto (fun k : ℕ => clip k x) atTop (𝓝 x) := by
  have hR : ∀ᶠ k : ℕ in atTop, |x| ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop |x|
  apply tendsto_const_nhds.congr'
  filter_upwards [hR] with k hk
  exact (clip_eq_self (by linarith only [(abs_le.mp hk).1]) (abs_le.mp hk).2).symm

/-- Every positive variance proxy decreases under symmetric clipping. -/
theorem vPlus_clip_le {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) (f : (Fin n → A) → ℝ) (R : ℝ) (x : Fin n → A) :
    vPlus μ (fun z => clip R (f z)) x ≤ vPlus μ f x := by
  apply Finset.sum_le_sum
  intro i _
  apply lintegral_mono
  intro y
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (le_max_right _ _)
    (positive_clip_sub_le R (f x) (f (Function.update x i y))) 2)

/-- Clipped functions have all exponential moments. -/
theorem integrable_exp_clip {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    Integrable (fun x => exp (θ * clip R (f x))) P := by
  apply Integrable.mono' (integrable_const (exp (|θ| * R)))
    (((measurable_clip R).comp hf).const_mul θ).exp.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  calc
    θ * clip R (f x) ≤ |θ * clip R (f x)| := le_abs_self _
    _ = |θ| * |clip R (f x)| := abs_mul _ _
    _ ≤ |θ| * R := mul_le_mul_of_nonneg_left (abs_clip_le_radius hR _) (abs_nonneg _)

/-- Integrals of symmetric clips converge to the original mean. -/
theorem tendsto_integral_clip {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f : Ω → ℝ} (hf : Measurable f) (hfi : Integrable f P) :
    Tendsto (fun k : ℕ => ∫ x, clip k (f x) ∂P) atTop (𝓝 (∫ x, f x ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (F := fun k x => clip k (f x)) (f := f) (fun x => |f x|)
    (fun k => ((measurable_clip k).comp hf).aestronglyMeasurable) hfi.abs
  · intro k
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using abs_clip_le (Nat.cast_nonneg k) (f x)
  · exact Eventually.of_forall fun x => tendsto_clip (f x)

/-- A set whose points eventually belong to uniformly measure-bounded sets
inherits the same bound. No measurability assumption is needed. -/
theorem measure_le_of_eventually_mem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {s : Set Ω} {S : ℕ → Set Ω} {C : ℝ≥0∞}
    (h : ∀ x ∈ s, ∀ᶠ k in atTop, x ∈ S k) (hS : ∀ k, P (S k) ≤ C) : P s ≤ C := by
  let U : ℕ → Set Ω := fun N => ⋂ k ≥ N, S k
  have hU : Monotone U := by
    intro N M hNM x hx
    exact mem_iInter₂.mpr fun k hk => mem_iInter₂.mp hx k (hNM.trans hk)
  have hs : s ⊆ ⋃ N, U N := by
    intro x hx
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h x hx)
    exact mem_iUnion.mpr ⟨N, mem_iInter₂.mpr hN⟩
  refine (measure_mono hs).trans ?_
  rw [hU.measure_iUnion]
  apply iSup_le
  intro N
  exact (measure_mono (fun x hx => mem_iInter₂.mp hx N le_rfl)).trans (hS N)

end IsotropicVariance.Infra.Concentration
