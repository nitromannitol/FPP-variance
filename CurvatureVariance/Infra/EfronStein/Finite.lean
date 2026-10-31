/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
Ported from subdiffusive-process (https://github.com/nitromannitol/subdiffusive-process) at
4c6b8fa60357a07fd5713e5104a6cc70f8e432dc, SubdiffusiveProcess/Paper/aux_lem_15_bblm.lean
(lines 1–710); modified.
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance

/-!
# The Efron–Stein inequality on a finite product

For independent coordinates `x = (x₀, …, x_{m-1})` of arbitrary measurable types `X i` with laws
`μ i`, and a square-integrable measurable `F` on the product `Measure.pi μ`,
`Var F ≤ ½ ∑ᵢ E ∫ (F x - F (x with xᵢ replaced by y))² dμᵢ(y)` (`efronStein_fin`).
Only `MemLp F 2` is assumed, no boundedness and no integrability of the energies. The proof is by
induction on `m`, splitting off the coordinate `0` with `MeasurableEquiv.piFinSuccAbove`.

The countable form, under `Measure.infinitePi`, is in
`CurvatureVariance.Infra.EfronStein.Countable`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace CurvatureVariance.Infra.EfronStein

/-! ### Elementary facts on one probability space -/

/-- The centered second moment is the second moment minus the squared mean. -/
theorem integral_sub_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) =
      (∫ x, (F x) ^ 2 ∂μ) - (∫ x, F x ∂μ) ^ 2 := by
  let c := ∫ x, F x ∂μ
  have hi : Integrable F μ := hF.integrable (by norm_num)
  have hs : Integrable (fun x => (F x) ^ 2) μ := hF.integrable_sq
  have heq : (fun x => (F x - c) ^ 2) =
      fun x => (F x) ^ 2 - (2 * c) * F x + c ^ 2 := by
    funext x
    ring
  have hconst : (∫ _ : Ω, c ^ 2 ∂μ) = c ^ 2 := by simp
  change (∫ x, (F x - c) ^ 2 ∂μ) = (∫ x, (F x) ^ 2 ∂μ) - c ^ 2
  have h1 : Integrable (fun x => (F x) ^ 2 - (2 * c) * F x) μ :=
    hs.sub (hi.const_mul (2 * c))
  rw [heq, integral_add h1 (integrable_const (c ^ 2)),
    integral_sub hs (hi.const_mul (2 * c)), integral_const_mul, hconst]
  change (∫ x, (F x) ^ 2 ∂μ) - (2 * c) * c + c ^ 2 =
    (∫ x, (F x) ^ 2 ∂μ) - c ^ 2
  ring

/-- Jensen's inequality for the square: `(E f)² ≤ E f²`. -/
theorem sq_integral_le_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂μ := by
  have h : 0 ≤ ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  rw [integral_sub_integral_sq hf] at h
  linarith only [h]

/-- The variance is half the mean square difference of two independent copies. -/
theorem integral_sq_sub_sq_integral_eq_half
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsProbabilityMeasure μ]
    {f : A → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 =
      (1 / 2 : ℝ) * ∫ x, ∫ y, (f x - f y) ^ 2 ∂μ ∂μ := by
  have hi : Integrable f μ := hf.integrable (by norm_num)
  have hs : Integrable (fun x => (f x) ^ 2) μ := hf.integrable_sq
  have hinner : ∀ x,
      (∫ y, (f x - f y) ^ 2 ∂μ) =
        (f x) ^ 2 - 2 * f x * (∫ y, f y ∂μ) + ∫ y, (f y) ^ 2 ∂μ := by
    intro x
    calc
      (∫ y, (f x - f y) ^ 2 ∂μ) =
          ∫ y, (f x) ^ 2 - (2 * f x) * f y + (f y) ^ 2 ∂μ := by
        congr 1
        funext y
        ring
      _ = (f x) ^ 2 - 2 * f x * (∫ y, f y ∂μ) + ∫ y, (f y) ^ 2 ∂μ := by
        have h1 : Integrable (fun y => (f x) ^ 2 - (2 * f x) * f y) μ :=
          (integrable_const _).sub (hi.const_mul _)
        rw [integral_add h1 hs,
          integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul]
        simp
  simp_rw [hinner]
  have h2 : Integrable (fun x => (f x) ^ 2 - 2 * f x * (∫ y, f y ∂μ)) μ :=
    hs.sub ((hi.const_mul 2).mul_const _)
  rw [integral_add h2 (integrable_const _),
    integral_sub hs ((hi.const_mul 2).mul_const _), integral_mul_const,
    integral_const_mul]
  simp
  ring

/-! ### Two factors -/

section TwoFactors

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Averaging a square-integrable function of two independent variables over the first one
gives a measurable square-integrable function of the second. -/
theorem memLp_two_integral_left
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : A × B → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 (μ.prod ν)) :
    Measurable (fun b => ∫ a, f (a, b) ∂μ) ∧
      MemLp (fun b => ∫ a, f (a, b) ∂μ) 2 ν := by
  have hm : Measurable (fun b => ∫ a, f (a, b) ∂μ) :=
    hf.stronglyMeasurable.integral_prod_left'.measurable
  refine ⟨hm, (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_⟩
  have hs := hf2.integrable_sq
  apply hs.integral_prod_right.mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards [hs.prod_left_ae] with b hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply sq_integral_le_integral_sq
  exact (memLp_two_iff_integrable_sq
    (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hb

/-- The map `((a, b), a') ↦ ((a', b), a)` preserves `(μ ⊗ ν) ⊗ μ`. -/
theorem measurePreserving_outerSwap
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : (A × B) × A => ((z.2, z.1.2), z.1.1))
      ((μ.prod ν).prod μ) ((μ.prod ν).prod μ) := by
  have h₁ := measurePreserving_prodAssoc μ ν μ
  have h₂ := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := μ))
  have h₃ := Measure.measurePreserving_swap (μ := μ) (ν := μ.prod ν)
  exact h₃.comp (h₂.comp h₁)

/-- Jensen for the difference of two averages over the first variable. -/
theorem integral_sq_integral_sub_le
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f g : A × B → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν)) :
    (∫ b, ((∫ a, f (a, b) ∂μ) - ∫ a, g (a, b) ∂μ) ^ 2 ∂ν) ≤
      ∫ b, ∫ a, (f (a, b) - g (a, b)) ^ 2 ∂μ ∂ν := by
  have hfbar := (memLp_two_integral_left hfm hf).2
  have hgbar := (memLp_two_integral_left hgm hg).2
  have hd := (hf.sub hg).integrable_sq
  apply integral_mono_ae (hfbar.sub hgbar).integrable_sq hd.integral_prod_right
  filter_upwards [(hf.integrable (by norm_num)).prod_left_ae,
    (hg.integrable (by norm_num)).prod_left_ae, hd.prod_left_ae] with b hfb hgb hdb
  simp only [Pi.sub_apply] at hdb ⊢
  rw [← integral_sub hfb hgb]
  apply sq_integral_le_integral_sq
  apply (memLp_two_iff_integrable_sq
    ((hfm.sub hgm).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr
  exact hdb

/-- The law of total variance on a product of two probability spaces, with the conditional
variance written as half the mean square difference of two copies of the first variable. -/
theorem integral_sq_sub_sq_integral_prod
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : A × B → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (μ.prod ν)) :
    (∫ z, (f z) ^ 2 ∂μ.prod ν) - (∫ z, f z ∂μ.prod ν) ^ 2 =
      (1 / 2 : ℝ) * (∫ a, ∫ b, ∫ a', (f (a, b) - f (a', b)) ^ 2 ∂μ ∂ν ∂μ) +
        (∫ b, (∫ a, f (a, b) ∂μ) ^ 2 ∂ν) -
          (∫ b, ∫ a, f (a, b) ∂μ ∂ν) ^ 2 := by
  have hi := hf.integrable (by norm_num)
  have hs := hf.integrable_sq
  have hh := (memLp_two_integral_left hfm hf).2
  have hf₁ : MemLp (fun z : (A × B) × A => f z.1) 2 ((μ.prod ν).prod μ) :=
    hf.comp_measurePreserving (measurePreserving_fst (μ := μ.prod ν) (ν := μ))
  have hf₂ : MemLp (fun z : (A × B) × A => f (z.2, z.1.2)) 2
      ((μ.prod ν).prod μ) :=
    hf₁.comp_measurePreserving (measurePreserving_outerSwap μ ν)
  have hd := (hf₁.sub hf₂).integrable_sq
  have hswap :
      (∫ a, ∫ b, ∫ a', (f (a, b) - f (a', b)) ^ 2 ∂μ ∂ν ∂μ) =
        ∫ b, ∫ a, ∫ a', (f (a, b) - f (a', b)) ^ 2 ∂μ ∂μ ∂ν :=
    integral_integral_swap hd.integral_prod_left
  have hpair :
      (1 / 2 : ℝ) * (∫ a, ∫ b, ∫ a', (f (a, b) - f (a', b)) ^ 2 ∂μ ∂ν ∂μ) =
        (∫ z, (f z) ^ 2 ∂μ.prod ν) - (∫ b, (∫ a, f (a, b) ∂μ) ^ 2 ∂ν) := by
    rw [hswap, ← integral_const_mul]
    calc
      (∫ b, (1 / 2 : ℝ) * ∫ a, ∫ a',
          (f (a, b) - f (a', b)) ^ 2 ∂μ ∂μ ∂ν) =
          ∫ b, (∫ a, (f (a, b)) ^ 2 ∂μ) - (∫ a, f (a, b) ∂μ) ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards [hs.prod_left_ae] with b hb
        symm
        apply integral_sq_sub_sq_integral_eq_half
        exact (memLp_two_iff_integrable_sq
          (hfm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hb
      _ = (∫ z, (f z) ^ 2 ∂μ.prod ν) - (∫ b, (∫ a, f (a, b) ∂μ) ^ 2 ∂ν) := by
        rw [integral_sub hs.integral_prod_right hh.integrable_sq,
          ← integral_prod_symm _ hs]
  rw [integral_prod_symm f hi]
  linarith only [hpair]

end TwoFactors

/-! ### Resampling one coordinate of a finite product -/

section FinProduct

variable {m : ℕ} {X : Fin m → Type*} [∀ i, MeasurableSpace (X i)]

/-- Replace the coordinate `i` of `x` by `y` and remember the old value: `(x, y) ↦ (x[i ↦ y], xᵢ)`.
It is an involution. -/
def swapCoordinate (i : Fin m) :
    (((j : Fin m) → X j) × X i) ≃ᵐ (((j : Fin m) → X j) × X i) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv := by
    intro z
    rcases z with ⟨x, y⟩
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  right_inv := by
    intro z
    rcases z with ⟨x, y⟩
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  measurable_toFun := measurable_update'.prodMk ((measurable_pi_apply i).comp measurable_fst)
  measurable_invFun := measurable_update'.prodMk ((measurable_pi_apply i).comp measurable_fst)

variable (μ : (i : Fin m) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Exchangeability of `(x, x[i ↦ y])` under `Measure.pi μ ⊗ μ i`. -/
theorem measurePreserving_swapCoordinate (i : Fin m) :
    MeasurePreserving (swapCoordinate i)
      ((Measure.pi μ).prod (μ i)) ((Measure.pi μ).prod (μ i)) := by
  classical
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove X i
    let ν := Measure.pi (fun j : Fin n => μ (i.succAbove j))
    have he : MeasurePreserving e (Measure.pi μ) ((μ i).prod ν) :=
      measurePreserving_piFinSuccAbove μ i
    have hes : MeasurePreserving e.symm ((μ i).prod ν) (Measure.pi μ) := he.symm
    have ht : MeasurePreserving
        (fun z : (X i × ((j : Fin n) → X (i.succAbove j))) × X i =>
          ((z.2, z.1.2), z.1.1))
        (((μ i).prod ν).prod (μ i)) (((μ i).prod ν).prod (μ i)) :=
      measurePreserving_outerSwap (μ i) ν
    have h := (hes.prod (MeasurePreserving.id (μ i))).comp
      (ht.comp (he.prod (MeasurePreserving.id (μ i))))
    convert h using 1
    funext z
    rcases z with ⟨x, y⟩
    change (Function.update x i y, x i) =
      (Fin.insertNth i y (Fin.removeNth i x), x i)
    rw [Fin.insertNth_removeNth]

/-- Resampling one coordinate preserves the product law. -/
theorem measurePreserving_update_fin (i : Fin m) :
    MeasurePreserving
      (fun z : ((j : Fin m) → X j) × X i => Function.update z.1 i z.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) :=
  (measurePreserving_fst (μ := Measure.pi μ) (ν := μ i)).comp
    (measurePreserving_swapCoordinate μ i)

/-- The resampling increment `F x - F (x[i ↦ y])` of an `L²` function is in `L²`. -/
theorem memLp_resampleDiff_fin {F : ((i : Fin m) → X i) → ℝ} (hF : MemLp F 2 (Measure.pi μ))
    (i : Fin m) :
    MemLp (fun z : ((j : Fin m) → X j) × X i =>
      F z.1 - F (Function.update z.1 i z.2)) 2 ((Measure.pi μ).prod (μ i)) :=
  (hF.comp_measurePreserving
    (measurePreserving_fst (μ := Measure.pi μ) (ν := μ i))).sub
      (hF.comp_measurePreserving (measurePreserving_update_fin μ i))

/-- The local energy `x ↦ ∫ (F x - F (x[i ↦ y]))² dμᵢ(y)` is integrable. -/
theorem integrable_resampleSq_fin {F : ((i : Fin m) → X i) → ℝ}
    (hF : MemLp F 2 (Measure.pi μ)) (i : Fin m) :
    Integrable (fun x => ∫ y : X i,
      (F x - F (Function.update x i y)) ^ 2 ∂μ i) (Measure.pi μ) :=
  (memLp_resampleDiff_fin μ hF i).integrable_sq.integral_prod_left

/-- Fubini along the coordinate `i` of a product indexed by `Fin (n + 1)`. -/
theorem integral_pi_fin_split
    {n : ℕ} {X : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : Fin (n + 1)) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin (n + 1)) {F : ((i : Fin (n + 1)) → X i) → ℝ}
    (hF : Integrable F (Measure.pi μ)) :
    (∫ x, F x ∂Measure.pi μ) =
      ∫ a : X i, ∫ x : (j : Fin n) → X (i.succAbove j),
        F (Fin.insertNth i a x)
          ∂Measure.pi (fun j => μ (i.succAbove j)) ∂μ i := by
  let e := MeasurableEquiv.piFinSuccAbove X i
  have he : MeasurePreserving e.symm
      ((μ i).prod (Measure.pi (fun j : Fin n => μ (i.succAbove j))))
      (Measure.pi μ) :=
    (measurePreserving_piFinSuccAbove μ i).symm
  calc
    (∫ x, F x ∂Measure.pi μ) = ∫ z, F (e.symm z)
        ∂((μ i).prod (Measure.pi (fun j : Fin n => μ (i.succAbove j)))) :=
      (he.integral_comp' F).symm
    _ = ∫ a : X i, ∫ x : (j : Fin n) → X (i.succAbove j),
        F (Fin.insertNth i a x)
          ∂Measure.pi (fun j => μ (i.succAbove j)) ∂μ i :=
      integral_prod _ ((he.integrable_comp hF.aestronglyMeasurable).mpr hF)

/-- Averaging over an independent variable decreases the resampling energies (Jensen). -/
theorem integral_resampleSq_integral_left_le
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]
    {f : A × ((i : Fin m) → X i) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (ν.prod (Measure.pi μ)))
    (i : Fin m) :
    (∫ x, ∫ y : X i,
      ((∫ a, f (a, x) ∂ν) - (∫ a, f (a, Function.update x i y) ∂ν)) ^ 2
        ∂μ i ∂Measure.pi μ) ≤
      ∫ a, ∫ x, ∫ y : X i,
        (f (a, x) - f (a, Function.update x i y)) ^ 2
          ∂μ i ∂Measure.pi μ ∂ν := by
  let P := Measure.pi μ
  let f₁ : A × (((j : Fin m) → X j) × X i) → ℝ := fun z => f (z.1, z.2.1)
  let f₂ : A × (((j : Fin m) → X j) × X i) → ℝ :=
    fun z => f (z.1, Function.update z.2.1 i z.2.2)
  have hf₁m : Measurable f₁ :=
    hfm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hf₂m : Measurable f₂ :=
    hfm.comp (measurable_fst.prodMk (measurable_update'.comp measurable_snd))
  have hf₁ : MemLp f₁ 2 (ν.prod (P.prod (μ i))) :=
    hf.comp_measurePreserving ((MeasurePreserving.id ν).prod
      (measurePreserving_fst (μ := P) (ν := μ i)))
  have hf₂ : MemLp f₂ 2 (ν.prod (P.prod (μ i))) :=
    hf.comp_measurePreserving ((MeasurePreserving.id ν).prod (measurePreserving_update_fin μ i))
  have havg := memLp_two_integral_left hfm hf
  have hdavg := (memLp_resampleDiff_fin μ havg.2 i).integrable_sq
  have hd := (hf₁.sub hf₂).integrable_sq
  calc
    (∫ x, ∫ y : X i,
      ((∫ a, f (a, x) ∂ν) - (∫ a, f (a, Function.update x i y) ∂ν)) ^ 2
        ∂μ i ∂Measure.pi μ) =
        ∫ z, ((∫ a, f₁ (a, z) ∂ν) - ∫ a, f₂ (a, z) ∂ν) ^ 2
          ∂P.prod (μ i) := (integral_prod _ hdavg).symm
    _ ≤ ∫ z, ∫ a, (f₁ (a, z) - f₂ (a, z)) ^ 2 ∂ν ∂P.prod (μ i) :=
      integral_sq_integral_sub_le hf₁m hf₂m hf₁ hf₂
    _ = ∫ a, ∫ z, (f₁ (a, z) - f₂ (a, z)) ^ 2 ∂P.prod (μ i) ∂ν :=
      (integral_integral_swap hd).symm
    _ = ∫ a, ∫ x, ∫ y : X i,
        (f (a, x) - f (a, Function.update x i y)) ^ 2
          ∂μ i ∂Measure.pi μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hd.prod_right_ae] with a ha
      exact integral_prod _ ha

end FinProduct

/-! ### The two-sided inequality -/

/-- **Efron–Stein inequality** on a finite product of arbitrary probability spaces: the variance
of a square-integrable measurable `F` is at most half the sum over the coordinates of the mean
square change of `F` when that coordinate is resampled independently. -/
theorem efronStein_fin :
    ∀ (m : ℕ) (X : Fin m → Type*) [∀ i, MeasurableSpace (X i)]
      (μ : (i : Fin m) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
      (F : ((i : Fin m) → X i) → ℝ),
      Measurable F → MemLp F 2 (Measure.pi μ) →
      (∫ x, (F x) ^ 2 ∂Measure.pi μ) - (∫ x, F x ∂Measure.pi μ) ^ 2 ≤
        (1 / 2 : ℝ) * ∑ i : Fin m,
          ∫ x, ∫ y : X i, (F x - F (Function.update x i y)) ^ 2
            ∂μ i ∂Measure.pi μ := by
  intro m
  induction m with
  | zero =>
    intro X _ μ _ F hFm hF
    let x₀ : (i : Fin 0) → X i := fun i => Fin.elim0 i
    have hc : F = fun _ => F x₀ := by
      funext x
      exact congrArg F (Subsingleton.elim x x₀)
    rw [hc]
    simp
  | succ n ih =>
    intro X _ μ _ F hFm hF
    let i₀ : Fin (n + 1) := 0
    let Y : Fin n → Type _ := fun j => X (i₀.succAbove j)
    let ν : (j : Fin n) → Measure (Y j) := fun j => μ (i₀.succAbove j)
    let P := Measure.pi μ
    let Q := Measure.pi ν
    let e := MeasurableEquiv.piFinSuccAbove X i₀
    have he : MeasurePreserving e.symm ((μ i₀).prod Q) P :=
      (measurePreserving_piFinSuccAbove μ i₀).symm
    let f : X i₀ × ((j : Fin n) → Y j) → ℝ := fun z => F (e.symm z)
    have hfm : Measurable f := hFm.comp e.symm.measurable
    have hf : MemLp f 2 ((μ i₀).prod Q) := hF.comp_measurePreserving he
    let h : ((j : Fin n) → Y j) → ℝ := fun x => ∫ a, f (a, x) ∂μ i₀
    have hh := memLp_two_integral_left hfm hf
    have hind := ih Y ν h hh.1 hh.2
    let D : Fin (n + 1) → ℝ := fun i =>
      ∫ x, ∫ y : X i, (F x - F (Function.update x i y)) ^ 2 ∂μ i ∂P
    have hD (i : Fin (n + 1)) : D i =
        ∫ a : X i₀, ∫ x : (j : Fin n) → Y j, ∫ y : X i,
          (F (e.symm (a, x)) - F (Function.update (e.symm (a, x)) i y)) ^ 2
            ∂μ i ∂Q ∂μ i₀ :=
      integral_pi_fin_split μ i₀ (integrable_resampleSq_fin μ hF i)
    have hu₀ (a y : X i₀) (x : (j : Fin n) → Y j) :
        Function.update (e.symm (a, x)) i₀ y = e.symm (y, x) := by
      change Function.update (Fin.insertNth i₀ a x) i₀ y = Fin.insertNth i₀ y x
      simp only [Fin.update_insertNth]
    have hu (j : Fin n) (a : X i₀) (x : (k : Fin n) → Y k) (y : Y j) :
        Function.update (e.symm (a, x)) (i₀.succAbove j) y =
          e.symm (a, Function.update x j y) := by
      change Function.update (Fin.insertNth i₀ a x) (i₀.succAbove j) y =
        Fin.insertNth i₀ a (Function.update x j y)
      simp only [Fin.insertNth_update]
    have hD₀ : D i₀ =
        ∫ a, ∫ x, ∫ y, (f (a, x) - f (y, x)) ^ 2 ∂μ i₀ ∂Q ∂μ i₀ := by
      simpa only [hu₀] using hD i₀
    have hDj (j : Fin n) : D (i₀.succAbove j) =
        ∫ a, ∫ x, ∫ y : Y j, (f (a, x) - f (a, Function.update x j y)) ^ 2
          ∂ν j ∂Q ∂μ i₀ := by
      simpa only [hu] using hD (i₀.succAbove j)
    have htail :
        (∑ j : Fin n, ∫ x, ∫ y : Y j,
          (h x - h (Function.update x j y)) ^ 2 ∂ν j ∂Q) ≤
          ∑ j : Fin n, D (i₀.succAbove j) := by
      apply Finset.sum_le_sum
      intro j _
      rw [hDj]
      exact integral_resampleSq_integral_left_le ν (μ i₀) hfm hf j
    have hsum : (∑ i : Fin (n + 1), D i) =
        D i₀ + ∑ j : Fin n, D (i₀.succAbove j) := by
      simpa only [i₀, Fin.zero_succAbove] using Fin.sum_univ_succ D
    have hmean : (∫ z, f z ∂(μ i₀).prod Q) = ∫ x, F x ∂P :=
      he.integral_comp' F
    have hsquare : (∫ z, (f z) ^ 2 ∂(μ i₀).prod Q) = ∫ x, (F x) ^ 2 ∂P :=
      he.integral_comp' (fun x => (F x) ^ 2)
    have hsplit := integral_sq_sub_sq_integral_prod hfm hf
    rw [hmean, hsquare, ← hD₀] at hsplit
    change (∫ x, (F x) ^ 2 ∂P) - (∫ x, F x ∂P) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i : Fin (n + 1), D i
    rw [hsum]
    change (∫ x, (h x) ^ 2 ∂Q) - (∫ x, h x ∂Q) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ j : Fin n,
        ∫ x, ∫ y : Y j, (h x - h (Function.update x j y)) ^ 2 ∂ν j ∂Q at hind
    nlinarith only [hsplit, hind, htail]

end CurvatureVariance.Infra.EfronStein
