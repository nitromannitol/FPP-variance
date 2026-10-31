/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
/- The proof of `measurePreserving_splice` is adapted from Critical2DKPZ at commit f1c98da,
`Critical2DKPZ/Gaussian/Harris.lean` (`infinitePi_prod_map_piecewise`), Copyright (c) 2026
Ahmed Bou-Rabee and the formal-math contributors, Apache License 2.0; modified. -/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Moments.Variance
public import CurvatureVariance.Infra.EfronStein.Coordinates

/-!
# Integrating out coordinates of a product probability space

Let `P = Measure.infinitePi μ` be the product of probability measures `μ i` on spaces `X i`, for an
arbitrary index type `ι`. For a set `T` of coordinates, `splice T x y` takes the coordinates in `T`
from `y` and the others from `x`, and `integrateOut μ T f x = ∫ f (splice T x y) dP(y)` integrates
`f` over the coordinates in `T` with the others fixed. For one coordinate `i`,
`coordAvg μ i f x = ∫ f (update x i y) dμ_i(y)`; it agrees with `integrateOut μ {i} f`.

Both are averages along a measure-preserving gluing map `φ : Ω × B → Ω`; the Fubini facts are
proved once for such maps (`MeasurePreserving` of `(x, y) ↦ φ (x, y)` from `P ⊗ ν` to `P`).

## Main results

* `measurePreserving_splice`, `measurePreserving_update`: the gluing maps preserve the product
  measure.
* `integral_integrateOut`, `integrable_integrateOut`, `integral_sq_integrateOut_le`: Fubini and
  Jensen for `integrateOut`.
* `integrateOut_integrateOut`: the tower property `E_S (E_T f) = E_{S ∪ T} f` a.e.
* `integrateOut_ae_eq_condExp`: `E_T f` is the conditional expectation given the coordinates
  outside `T`.
* `tendsto_integrateOut_ae`: Lévy's upward theorem along an enumeration of a countable index set.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CurvatureVariance.Infra.Entropy

open CurvatureVariance.Infra.EfronStein (coordinateSigma coordinateSigma_le coordinateSigma_mono)

/-! ### Averages along a measure-preserving gluing map -/

section Gluing

variable {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B] {P : Measure Ω} {ν : Measure B}
  {φ : Ω × B → Ω}

theorem integrable_comp_glue (hφ : MeasurePreserving φ (P.prod ν) P) {f : Ω → ℝ}
    (hf : Integrable f P) : Integrable (fun p => f (φ p)) (P.prod ν) :=
  hφ.integrable_comp_of_integrable hf

theorem ae_integrable_glue [SFinite P] [SFinite ν] (hφ : MeasurePreserving φ (P.prod ν) P) {f : Ω → ℝ}
    (hf : Integrable f P) : ∀ᵐ x ∂P, Integrable (fun y => f (φ (x, y))) ν :=
  (integrable_comp_glue hφ hf).prod_right_ae

theorem integrable_integral_glue [SFinite P] [SFinite ν] (hφ : MeasurePreserving φ (P.prod ν) P)
    {f : Ω → ℝ} (hf : Integrable f P) : Integrable (fun x => ∫ y, f (φ (x, y)) ∂ν) P :=
  (integrable_comp_glue hφ hf).integral_prod_left

theorem integral_integral_glue [SFinite P] [SFinite ν] (hφ : MeasurePreserving φ (P.prod ν) P)
    {f : Ω → ℝ} (hf : Integrable f P) : ∫ x, ∫ y, f (φ (x, y)) ∂ν ∂P = ∫ x, f x ∂P := by
  rw [← integral_prod (fun p => f (φ p)) (integrable_comp_glue hφ hf)]
  have hae : AEStronglyMeasurable f (Measure.map φ (P.prod ν)) := by
    rw [hφ.map_eq]; exact hf.aestronglyMeasurable
  rw [← integral_map hφ.aemeasurable hae, hφ.map_eq]

theorem lintegral_lintegral_glue [SFinite ν] (hφ : MeasurePreserving φ (P.prod ν) P)
    {F : Ω → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x, ∫⁻ y, F (φ (x, y)) ∂ν ∂P = ∫⁻ x, F x ∂P := by
  rw [← lintegral_prod (fun p => F (φ p)) (hF.comp hφ.measurable).aemeasurable]
  conv_rhs => rw [← hφ.map_eq]
  rw [lintegral_map hF hφ.measurable]

theorem measurable_integral_glue [SFinite ν] (hφ : MeasurePreserving φ (P.prod ν) P)
    {f : Ω → ℝ} (hf : Measurable f) : Measurable fun x => ∫ y, f (φ (x, y)) ∂ν :=
  (hf.comp hφ.measurable).stronglyMeasurable.integral_prod_right'.measurable

/-- Jensen for the square, slicewise and then integrated. -/
theorem integral_sq_integral_glue_le [SFinite P] [IsProbabilityMeasure ν]
    (hφ : MeasurePreserving φ (P.prod ν) P) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ x, (∫ y, f (φ (x, y)) ∂ν) ^ 2 ∂P ≤ ∫ x, f x ^ 2 ∂P := by
  have hf2 : MemLp (fun p => f (φ p)) 2 (P.prod ν) := hf.comp_measurePreserving hφ
  have hsq : Integrable (fun x => f x ^ 2) P := hf.integrable_sq
  have hslice : ∀ᵐ x ∂P, MemLp (fun y => f (φ (x, y))) 2 ν := by
    have h := ae_integrable_glue hφ hsq
    filter_upwards [h, hf2.aestronglyMeasurable.prodMk_left] with x hx hxm
    exact (memLp_two_iff_integrable_sq hxm).2 hx
  calc ∫ x, (∫ y, f (φ (x, y)) ∂ν) ^ 2 ∂P ≤ ∫ x, ∫ y, f (φ (x, y)) ^ 2 ∂ν ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          (integrable_integral_glue hφ hsq) ?_
        filter_upwards [hslice] with x hx
        have := ProbabilityTheory.variance_nonneg (fun y => f (φ (x, y))) ν
        rw [ProbabilityTheory.variance_eq_sub hx] at this
        simp only [Pi.pow_apply] at this
        linarith
    _ = ∫ x, f x ^ 2 ∂P := integral_integral_glue hφ hsq

end Gluing

/-! ### Splicing and updating coordinates -/

section Splice

variable {ι : Type*} {X : ι → Type*}

open Classical in
/-- `splice T x y` takes the coordinates in `T` from `y` and the others from `x`. -/
noncomputable def splice (T : Set ι) (x y : ∀ i, X i) : ∀ i, X i :=
  fun i => if i ∈ T then y i else x i

variable {T S : Set ι} {x y z : ∀ i, X i} {i : ι}

theorem splice_apply_of_mem (h : i ∈ T) : splice T x y i = y i := by
  simp [splice, h]

theorem splice_apply_of_notMem (h : i ∉ T) : splice T x y i = x i := by
  simp [splice, h]

@[simp] theorem splice_splice_left : splice T (splice T x z) y = splice T x y := by
  funext j; by_cases hj : j ∈ T <;> simp [splice, hj]

@[simp] theorem splice_univ : splice (Set.univ : Set ι) x y = y := by
  funext j; simp [splice]

/-- Splicing twice is splicing along the union. -/
theorem splice_splice : splice S (splice T x z) y = splice (S ∪ T) x (splice S z y) := by
  funext j; by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [splice, hS, hT]

theorem splice_update [DecidableEq ι] (h : i ∉ T) (a : X i) :
    splice T (Function.update x i a) z = Function.update (splice T x z) i a := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [splice, h]
  · by_cases hT : j ∈ T <;> simp [splice, hT, hj]

theorem splice_singleton [DecidableEq ι] : splice {i} x y = Function.update x i (y i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [splice]
  · simp [splice, hj]

variable [∀ i, MeasurableSpace (X i)]

theorem measurable_splice (T : Set ι) :
    Measurable fun p : (∀ i, X i) × (∀ i, X i) => splice T p.1 p.2 := by
  classical
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : j ∈ T
  · simp only [splice, hj, ite_true]; fun_prop
  · simp only [splice, hj, ite_false]; fun_prop

theorem measurable_splice_right (T : Set ι) (x : ∀ i, X i) :
    Measurable fun y : ∀ i, X i => splice T x y :=
  (measurable_splice T).comp measurable_prodMk_left

variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Gluing two independent samples along a set of coordinates gives a sample of the product. -/
theorem measurePreserving_splice (T : Set ι) :
    MeasurePreserving (fun p : (∀ i, X i) × (∀ i, X i) => splice T p.1 p.2)
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) (Measure.infinitePi μ) := by
  classical
  refine ⟨measurable_splice T, ?_⟩
  refine Measure.eq_infinitePi μ fun I t ht => ?_
  rw [Measure.map_apply (measurable_splice T) (.pi I.countable_toSet fun j _ => ht j)]
  have : (fun p : (∀ i, X i) × (∀ i, X i) => splice T p.1 p.2) ⁻¹' Set.pi ↑I t =
      Set.pi ↑(I.filter (· ∉ T)) t ×ˢ Set.pi ↑(I.filter (· ∈ T)) t := by
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · simpa [splice_apply_of_notMem hj.2] using h j hj.1
      · simpa [splice_apply_of_mem hj.2] using h j hj.1
    · rintro ⟨h1, h2⟩ j hj
      by_cases hjT : j ∈ T
      · rw [splice_apply_of_mem hjT]; exact h2 j ⟨hj, hjT⟩
      · rw [splice_apply_of_notMem hjT]; exact h1 j ⟨hj, hjT⟩
  rw [this, Measure.prod_prod, Measure.infinitePi_pi _ (fun j _ => ht j),
    Measure.infinitePi_pi _ (fun j _ => ht j), mul_comm, Finset.prod_filter_mul_prod_filter_not]

theorem measurable_update [DecidableEq ι] (i : ι) :
    Measurable fun p : (∀ j, X j) × X i => Function.update p.1 i p.2 := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; fun_prop
  · simp only [Function.update_of_ne hj]; fun_prop

/-- Resampling one coordinate preserves the product measure. -/
theorem measurePreserving_update [DecidableEq ι] (i : ι) :
    MeasurePreserving (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2)
      ((Measure.infinitePi μ).prod (μ i)) (Measure.infinitePi μ) := by
  have h1 : MeasurePreserving (fun p : (∀ j, X j) × (∀ j, X j) => (p.1, p.2 i))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) ((Measure.infinitePi μ).prod (μ i)) :=
    (MeasurePreserving.id _).prod (measurePreserving_eval_infinitePi μ i)
  have h2 := measurePreserving_splice μ {i}
  refine ⟨measurable_update i, ?_⟩
  calc Measure.map (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2)
        ((Measure.infinitePi μ).prod (μ i))
      = Measure.map ((fun p : (∀ j, X j) × X i => Function.update p.1 i p.2) ∘
          (fun p : (∀ j, X j) × (∀ j, X j) => (p.1, p.2 i)))
          ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) := by
        rw [← Measure.map_map (measurable_update i) h1.measurable, h1.map_eq]
    _ = Measure.map (fun p : (∀ i, X i) × (∀ i, X i) => splice {i} p.1 p.2)
          ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) := by
        congr 1
        funext p
        simp [splice_singleton]
    _ = Measure.infinitePi μ := h2.map_eq

end Splice

/-! ### Integrating out coordinates -/

section IntegrateOut

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- `E_T f`: integrate `f` over the coordinates in `T`, the others fixed. -/
noncomputable def integrateOut (T : Set ι) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  ∫ y, f (splice T x y) ∂Measure.infinitePi μ

/-- `E_i f`: integrate `f` over the coordinate `i`, the others fixed. -/
noncomputable def coordAvg [DecidableEq ι] (i : ι) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  ∫ y, f (Function.update x i y) ∂μ i

/-- `D_i f = f - E_i f`, the coordinate difference. -/
noncomputable def coordDiff [DecidableEq ι] (i : ι) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  f x - coordAvg μ i f x

variable {μ} {T S : Set ι} {f g : (∀ i, X i) → ℝ}

omit [∀ i, IsProbabilityMeasure (μ i)] in
@[simp] theorem integrateOut_splice (x z : ∀ i, X i) :
    integrateOut μ T f (splice T x z) = integrateOut μ T f x := by
  simp [integrateOut]

theorem measurable_integrateOut (hf : Measurable f) : Measurable (integrateOut μ T f) :=
  measurable_integral_glue (measurePreserving_splice μ T) hf

theorem measurable_coordAvg [DecidableEq ι] (i : ι) (hf : Measurable f) :
    Measurable (coordAvg μ i f) :=
  measurable_integral_glue (measurePreserving_update μ i) hf

theorem integrable_integrateOut (hf : Integrable f (Measure.infinitePi μ)) :
    Integrable (integrateOut μ T f) (Measure.infinitePi μ) :=
  integrable_integral_glue (measurePreserving_splice μ T) hf

theorem integrable_coordAvg [DecidableEq ι] (i : ι) (hf : Integrable f (Measure.infinitePi μ)) :
    Integrable (coordAvg μ i f) (Measure.infinitePi μ) :=
  integrable_integral_glue (measurePreserving_update μ i) hf

theorem integral_integrateOut (hf : Integrable f (Measure.infinitePi μ)) :
    ∫ x, integrateOut μ T f x ∂Measure.infinitePi μ = ∫ x, f x ∂Measure.infinitePi μ :=
  integral_integral_glue (measurePreserving_splice μ T) hf

theorem ae_integrable_splice (hf : Integrable f (Measure.infinitePi μ)) :
    ∀ᵐ x ∂Measure.infinitePi μ, Integrable (fun y => f (splice T x y)) (Measure.infinitePi μ) :=
  ae_integrable_glue (measurePreserving_splice μ T) hf

theorem ae_integrable_update [DecidableEq ι] (i : ι) (hf : Integrable f (Measure.infinitePi μ)) :
    ∀ᵐ x ∂Measure.infinitePi μ, Integrable (fun y => f (Function.update x i y)) (μ i) :=
  ae_integrable_glue (measurePreserving_update μ i) hf

theorem aestronglyMeasurable_integrateOut
    (hf : AEStronglyMeasurable f (Measure.infinitePi μ)) :
    AEStronglyMeasurable (integrateOut μ T f) (Measure.infinitePi μ) :=
  (hf.comp_measurePreserving (measurePreserving_splice μ T)).integral_prod_right'

theorem aestronglyMeasurable_coordAvg [DecidableEq ι] (i : ι)
    (hf : AEStronglyMeasurable f (Measure.infinitePi μ)) :
    AEStronglyMeasurable (coordAvg μ i f) (Measure.infinitePi μ) :=
  (hf.comp_measurePreserving (measurePreserving_update μ i)).integral_prod_right'

/-- Jensen: `E (E_T f)² ≤ E f²`. -/
theorem integral_sq_integrateOut_le (hf : MemLp f 2 (Measure.infinitePi μ)) :
    ∫ x, integrateOut μ T f x ^ 2 ∂Measure.infinitePi μ ≤ ∫ x, f x ^ 2 ∂Measure.infinitePi μ :=
  integral_sq_integral_glue_le (measurePreserving_splice μ T) hf

theorem memLp_integrateOut (hf : MemLp f 2 (Measure.infinitePi μ)) :
    MemLp (integrateOut μ T f) 2 (Measure.infinitePi μ) := by
  have hm := aestronglyMeasurable_integrateOut (T := T) hf.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hsq := hf.integrable_sq
  refine (integrable_integrateOut (T := T) hsq).mono' (hm.pow 2) ?_
  filter_upwards [ae_integrable_splice (T := T) hsq,
    (hf.comp_measurePreserving (measurePreserving_splice μ T)).aestronglyMeasurable.prodMk_left]
    with x hx hxm
  have hL2 : MemLp (fun y => f (splice T x y)) 2 (Measure.infinitePi μ) :=
    (memLp_two_iff_integrable_sq hxm).2 hx
  have := ProbabilityTheory.variance_nonneg (fun y => f (splice T x y)) (Measure.infinitePi μ)
  rw [ProbabilityTheory.variance_eq_sub hL2] at this
  simp only [Pi.pow_apply] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold integrateOut
  linarith

theorem memLp_coordAvg [DecidableEq ι] (i : ι) (hf : MemLp f 2 (Measure.infinitePi μ)) :
    MemLp (coordAvg μ i f) 2 (Measure.infinitePi μ) := by
  have hm := aestronglyMeasurable_coordAvg i hf.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hsq := hf.integrable_sq
  refine (integrable_coordAvg i hsq).mono' (hm.pow 2) ?_
  filter_upwards [ae_integrable_update i hsq,
    (hf.comp_measurePreserving (measurePreserving_update μ i)).aestronglyMeasurable.prodMk_left]
    with x hx hxm
  have hL2 : MemLp (fun y => f (Function.update x i y)) 2 (μ i) :=
    (memLp_two_iff_integrable_sq hxm).2 hx
  have := ProbabilityTheory.variance_nonneg (fun y => f (Function.update x i y)) (μ i)
  rw [ProbabilityTheory.variance_eq_sub hL2] at this
  simp only [Pi.pow_apply] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold coordAvg
  linarith

omit [∀ i, IsProbabilityMeasure (μ i)] in
theorem abs_integrateOut_le (x : ∀ i, X i) :
    |integrateOut μ T f x| ≤ integrateOut μ T (fun y => |f y|) x :=
  abs_integral_le_integral_abs

/-- Jensen in `L¹`: `E |E_T f| ≤ E |f|`. -/
theorem integral_abs_integrateOut_le (hf : Integrable f (Measure.infinitePi μ)) :
    ∫ x, |integrateOut μ T f x| ∂Measure.infinitePi μ ≤ ∫ x, |f x| ∂Measure.infinitePi μ := by
  calc ∫ x, |integrateOut μ T f x| ∂Measure.infinitePi μ
      ≤ ∫ x, integrateOut μ T (fun y => |f y|) x ∂Measure.infinitePi μ :=
        integral_mono (integrable_integrateOut hf).abs (integrable_integrateOut hf.abs)
          fun x => abs_integrateOut_le x
    _ = ∫ x, |f x| ∂Measure.infinitePi μ := integral_integrateOut hf.abs

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- A factor that does not depend on the coordinates in `T` comes out of `E_T`. -/
theorem integrateOut_mul_left {u : (∀ i, X i) → ℝ} (hu : ∀ x y, u (splice T x y) = u x)
    (x : ∀ i, X i) :
    integrateOut μ T (fun z => u z * f z) x = u x * integrateOut μ T f x := by
  simp only [integrateOut, hu, integral_const_mul]

/-- `E[u · E_T f] = E[u · f]` when `u` does not depend on the coordinates in `T`. -/
theorem integral_mul_integrateOut {u : (∀ i, X i) → ℝ} (hu : ∀ x y, u (splice T x y) = u x)
    (huf : Integrable (fun z => u z * f z) (Measure.infinitePi μ)) :
    ∫ x, u x * integrateOut μ T f x ∂Measure.infinitePi μ =
      ∫ x, u x * f x ∂Measure.infinitePi μ := by
  simp_rw [← integrateOut_mul_left hu]
  exact integral_integrateOut huf

/-- **Tower property**: `E_S (E_T f) = E_{T ∪ S} f` almost everywhere. -/
theorem integrateOut_integrateOut (hf : Integrable f (Measure.infinitePi μ)) :
    integrateOut μ S (integrateOut μ T f) =ᵐ[Measure.infinitePi μ] integrateOut μ (T ∪ S) f := by
  filter_upwards [ae_integrable_splice (T := T ∪ S) hf] with x hx
  simp only [integrateOut, splice_splice]
  exact integral_integral_glue (measurePreserving_splice μ T) (f := fun v => f (splice (T ∪ S) x v)) hx

/-- The coordinate average is the integral out of the singleton. -/
theorem coordAvg_eq_integrateOut [DecidableEq ι] (i : ι) (hf : Measurable f) :
    coordAvg μ i f = integrateOut μ {i} f := by
  funext x
  have hm : Measurable fun a : X i => f (Function.update x i a) :=
    hf.comp ((measurable_update i).comp measurable_prodMk_left)
  simp only [integrateOut, splice_singleton, coordAvg]
  rw [← (measurePreserving_eval_infinitePi μ i).map_eq,
    integral_map (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable]

/-- Integrating out one coordinate commutes with integrating out a set of coordinates. -/
theorem coordAvg_integrateOut [DecidableEq ι] (i : ι) (hf : Measurable f)
    (hfi : Integrable f (Measure.infinitePi μ)) :
    coordAvg μ i (integrateOut μ T f) =ᵐ[Measure.infinitePi μ]
      integrateOut μ T (coordAvg μ i f) := by
  rw [coordAvg_eq_integrateOut i (measurable_integrateOut hf), coordAvg_eq_integrateOut i hf]
  filter_upwards [integrateOut_integrateOut (S := {i}) (T := T) hfi,
    integrateOut_integrateOut (S := T) (T := {i}) hfi] with x h1 h2
  rw [h1, h2, Set.union_comm]

end IntegrateOut

/-! ### Coordinate σ-algebras, conditional expectations and Lévy's upward theorem -/

section CondExp

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

omit [∀ i, MeasurableSpace (X i)] in
/-- `measurable_pi_iff` for a measurable space on the domain that is not an instance. -/
theorem measurable_pi_iff' {Ω κ : Type*} {m : MeasurableSpace Ω} {Y : κ → Type*}
    [∀ a, MeasurableSpace (Y a)] {g : Ω → ∀ a, Y a} :
    Measurable[m] g ↔ ∀ a, Measurable[m] fun x => g x a :=
  measurable_pi_iff

theorem measurable_eval_coordinateSigma {S : Set ι} {j : ι} (hj : j ∈ S) :
    Measurable[coordinateSigma X S] (fun x : ∀ i, X i => x j) := by
  unfold coordinateSigma
  exact (measurable_pi_apply (X := fun k : S => X k) (⟨j, hj⟩ : S)).comp (comap_measurable _)

theorem splice_mem_iff_of_coordinateSigma {T : Set ι} {s : Set (∀ i, X i)}
    (hs : MeasurableSet[coordinateSigma X Tᶜ] s) (x y : ∀ i, X i) : splice T x y ∈ s ↔ x ∈ s := by
  obtain ⟨t, -, rfl⟩ := hs
  have : (fun j : (Tᶜ : Set ι) => splice T x y j) = fun j : (Tᶜ : Set ι) => x j := by
    funext j; exact splice_apply_of_notMem j.2
  simp only [Set.mem_preimage, this]

theorem measurable_splice_left_coordinateSigma (T : Set ι) (z : ∀ i, X i) :
    Measurable[coordinateSigma X Tᶜ] (fun x : ∀ i, X i => splice T x z) := by
  classical
  refine measurable_pi_iff'.2 fun j => ?_
  by_cases hj : j ∈ T
  · simp only [splice, hj, ite_true]; exact measurable_const
  · simp only [splice, hj, ite_false]; exact measurable_eval_coordinateSigma hj

variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] {f : (∀ i, X i) → ℝ}

theorem stronglyMeasurable_integrateOut_coordinateSigma (T : Set ι) (hf : Measurable f) :
    StronglyMeasurable[coordinateSigma X Tᶜ] (integrateOut μ T f) := by
  have : Nonempty (∀ i, X i) := nonempty_of_isProbabilityMeasure (Measure.infinitePi μ)
  obtain ⟨z⟩ := this
  have h : integrateOut μ T f = integrateOut μ T f ∘ fun x => splice T x z := by
    funext x; simp
  rw [h]
  exact ((measurable_integrateOut hf).comp
    (measurable_splice_left_coordinateSigma T z)).stronglyMeasurable

/-- `E_T f` is the conditional expectation of `f` given the coordinates outside `T`. -/
theorem integrateOut_ae_eq_condExp (T : Set ι) (hf : Measurable f)
    (hfi : Integrable f (Measure.infinitePi μ)) :
    integrateOut μ T f =ᵐ[Measure.infinitePi μ]
      (Measure.infinitePi μ)[f | coordinateSigma X Tᶜ] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq (coordinateSigma_le _ _) hfi
    (fun s _ _ => (integrable_integrateOut hfi).integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_integrateOut_coordinateSigma μ T hf).aestronglyMeasurable
  have hsm : MeasurableSet s := coordinateSigma_le _ _ s hs
  rw [← integral_indicator hsm, ← integral_indicator hsm]
  have hu : ∀ x y, s.indicator (fun _ => (1 : ℝ)) (splice T x y) = s.indicator (fun _ => 1) x := by
    intro x y
    have h := splice_mem_iff_of_coordinateSigma hs x y
    by_cases hx : x ∈ s
    · simp [Set.indicator, hx, h.2 hx]
    · simp [Set.indicator, hx, mt h.1 hx]
  have h1 : s.indicator (integrateOut μ T f) =
      fun x => s.indicator (fun _ => (1 : ℝ)) x * integrateOut μ T f x := by
    funext x; by_cases hx : x ∈ s <;> simp [hx]
  have h2 : s.indicator f = fun x => s.indicator (fun _ => (1 : ℝ)) x * f x := by
    funext x; by_cases hx : x ∈ s <;> simp [hx]
  rw [h1, h2, integral_mul_integrateOut hu]
  rw [← h2]
  exact hfi.indicator hsm

/-- `tailSet e n = {j | n ≤ e j}`: the coordinates not among the first `n` of the enumeration
`e`. -/
def tailSet (e : ι → ℕ) (n : ℕ) : Set ι := {j | n ≤ e j}

theorem compl_tailSet (e : ι → ℕ) (n : ℕ) : (tailSet e n)ᶜ = {j | e j < n} := by
  ext j; simp [tailSet]

theorem tailSet_antitone (e : ι → ℕ) : Antitone (tailSet e) :=
  fun _ _ h _ hj => le_trans h hj

/-- The filtration of the first `n` coordinates of the enumeration `e`. -/
def headFiltration (e : ι → ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (∀ i, X i)) where
  seq n := coordinateSigma X {j | e j < n}
  mono' _ _ h := coordinateSigma_mono _ fun _ hj => lt_of_lt_of_le hj h
  le' _ := coordinateSigma_le _ _

theorem pi_le_iSup_headFiltration (e : ι → ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (∀ i, X i)) ≤ ⨆ n, headFiltration e n := by
  refine iSup_le fun j => ?_
  refine le_trans ?_ (le_iSup (fun n => headFiltration (X := X) e n) (e j + 1))
  exact Measurable.comap_le (show Measurable[coordinateSigma X {k | e k < e j + 1}]
    (fun x : ∀ i, X i => x j) from measurable_eval_coordinateSigma (Nat.lt_succ_self _))

/-- **Lévy's upward theorem** along an enumeration of the coordinates: integrating out all but the
first `n` coordinates converges almost everywhere. -/
theorem tendsto_integrateOut_ae (e : ι → ℕ) (hf : Measurable f)
    (hfi : Integrable f (Measure.infinitePi μ)) :
    ∀ᵐ x ∂Measure.infinitePi μ,
      Tendsto (fun n => integrateOut μ (tailSet e n) f x) atTop (𝓝 (f x)) := by
  have hlevy := hfi.tendsto_ae_condExp (ℱ := headFiltration e)
    (hf.stronglyMeasurable.mono (pi_le_iSup_headFiltration e))
  have hce : ∀ᵐ x ∂Measure.infinitePi μ, ∀ n, integrateOut μ (tailSet e n) f x =
      (Measure.infinitePi μ)[f | headFiltration e n] x := by
    refine ae_all_iff.2 fun n => ?_
    have := integrateOut_ae_eq_condExp μ (tailSet e n) hf hfi
    rw [compl_tailSet] at this
    exact this
  filter_upwards [hlevy, hce] with x hx hcx
  simp_rw [hcx]
  exact hx

end CondExp

end CurvatureVariance.Infra.Entropy
