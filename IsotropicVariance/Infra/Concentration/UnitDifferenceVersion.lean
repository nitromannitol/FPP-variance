/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.Basic
public import IsotropicVariance.Infra.Entropy.Splice
public import Mathlib.MeasureTheory.Function.EssSup

/-! # A version with unit differences at every point

Let `P` be a finite product of probability measures and `f` a bounded measurable function with
`|f x - f (x[i ↦ y])| ≤ 1` for almost every `(x, y)` under `P ⊗ μᵢ`, for each coordinate `i`. Then
`f` agrees almost everywhere with a measurable `g` satisfying the same bound at every `x`, `i`, `y`
(`exists_version_abs_sub_update_le`). So the hypothesis `|Z - Z^{(i)}| ≤ 1` of
`IsotropicVariance.Cited.blm_theorem7` at every point costs nothing against the almost-sure bound.

Points at Hamming distance one are null for a diffuse law, and a set of full measure need not
contain a product set, so a Lipschitz extension from a set of full measure is not available.
Instead the coordinates are treated one at a time. With `L x` the essential infimum of `g` along the
line of the coordinate `i` through `x`, the function `g' = max L (min g (L + 1))` satisfies:

* `L ≤ g' ≤ L + 1` at every point, and `L` does not read `xᵢ`, which is the bound for `i` at every
  point (`lineClamp_mem`, `lineInf_update_self`);
* `L ≤ g ≤ L + 1` almost everywhere, by the hypothesis on the lines of `i`, so `g' = g` almost
  everywhere and the almost-sure bounds for the other coordinates persist (`ae_lineClamp_eq`);
* a bound at every point for another coordinate `j` passes to `L`, since `update` at `i` and at `j`
  commute and the essential infimum is monotone, and then to `g'`, since the clamp is `1`-Lipschitz
  in the sup norm (`abs_lineInf_sub_update_le`, `clamp_le_add_one`).
-/

@[expose] public section
open MeasureTheory Filter
namespace IsotropicVariance.Infra.Concentration

variable {n : ℕ} {A : Type*} [MeasurableSpace A]

/-- The clamp is `1`-Lipschitz in the sup norm. -/
theorem clamp_le_add_one {a a' b b' : ℝ} (ha : a ≤ a' + 1) (hb : b ≤ b' + 1) :
    max b (min a (b + 1)) ≤ max b' (min a' (b' + 1)) + 1 := by
  refine max_le (hb.trans (by linarith only [le_max_left b' (min a' (b' + 1))])) ?_
  rcases le_total a' (b' + 1) with h | h
  · have hh : a' ≤ max b' (min a' (b' + 1)) := (le_min le_rfl h).trans (le_max_right _ _)
    linarith only [min_le_left a (b + 1), hh, ha]
  · have hh : b' + 1 ≤ max b' (min a' (b' + 1)) := (le_min h le_rfl).trans (le_max_right _ _)
    linarith only [min_le_right a (b + 1), hh, hb]

/-- The essential infimum of `g` along the line of the coordinate `i` through `x`. -/
noncomputable def lineInf (ν : Measure A) (g : (Fin n → A) → ℝ) (i : Fin n)
    (x : Fin n → A) : ℝ :=
  essInf (fun y => g (Function.update x i y)) ν

/-- The function `g` clamped to `[L, L + 1]`, with `L` its essential infimum on the lines of `i`. -/
noncomputable def lineClamp (ν : Measure A) (g : (Fin n → A) → ℝ) (i : Fin n)
    (x : Fin n → A) : ℝ :=
  max (lineInf ν g i x) (min (g x) (lineInf ν g i x + 1))

/-- The line infimum does not read the coordinate of the line. -/
theorem lineInf_update_self (ν : Measure A) (g : (Fin n → A) → ℝ) (i : Fin n) (x : Fin n → A)
    (a : A) : lineInf ν g i (Function.update x i a) = lineInf ν g i x := by
  simp only [lineInf, Function.update_idem]

/-- The clamped function lies in `[L, L + 1]` at every point. -/
theorem lineClamp_mem (ν : Measure A) (g : (Fin n → A) → ℝ) (i : Fin n) (x : Fin n → A) :
    lineInf ν g i x ≤ lineClamp ν g i x ∧ lineClamp ν g i x ≤ lineInf ν g i x + 1 :=
  ⟨le_max_left _ _, max_le (by linarith only) (min_le_right _ _)⟩

section Line

variable {ν : Measure A} [IsProbabilityMeasure ν] {g : (Fin n → A) → ℝ} {B : ℝ}

omit [IsProbabilityMeasure ν] in
theorem ae_lineInf_le (hB : ∀ x, |g x| ≤ B) (i : Fin n) (x : Fin n → A) :
    ∀ᵐ y ∂ν, lineInf ν g i x ≤ g (Function.update x i y) :=
  ae_essInf_le (isBoundedUnder_of ⟨-B, fun _ => (abs_le.mp (hB _)).1⟩)

theorem le_lineInf (hB : ∀ x, |g x| ≤ B) (i : Fin n) (x : Fin n → A) {c : ℝ}
    (hc : ∀ᵐ y ∂ν, c ≤ g (Function.update x i y)) : c ≤ lineInf ν g i x :=
  le_essInf_of_ae_le c hc
    ((isBoundedUnder_of ⟨B, fun _ => (abs_le.mp (hB _)).2⟩).isCoboundedUnder_ge)

theorem abs_lineInf_le (hB : ∀ x, |g x| ≤ B) (i : Fin n) (x : Fin n → A) :
    |lineInf ν g i x| ≤ B := by
  obtain ⟨y, hy⟩ := (ae_lineInf_le (ν := ν) hB i x).exists
  refine abs_le.mpr ⟨le_lineInf hB i x (Eventually.of_forall fun y => (abs_le.mp (hB _)).1), ?_⟩
  exact hy.trans (abs_le.mp (hB _)).2

theorem measurable_lineInf (hg : Measurable g) (hB : ∀ x, |g x| ≤ B) (i : Fin n) :
    Measurable (lineInf ν g i) := by
  have hSet (q : ℝ) : MeasurableSet {p : (Fin n → A) × A | g (Function.update p.1 i p.2) < q} :=
    measurableSet_lt (hg.comp (Entropy.measurable_update i)) measurable_const
  refine measurable_of_Ioi fun c => ?_
  have hEq : lineInf ν g i ⁻¹' Set.Ioi c = ⋃ q : {q : ℚ // c < q},
      (fun x => ν (Prod.mk x ⁻¹' {p : (Fin n → A) × A |
        g (Function.update p.1 i p.2) < (q : ℚ)})) ⁻¹' {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion, Set.mem_singleton_iff, Subtype.exists,
      exists_prop]
    constructor
    · intro hx
      obtain ⟨q, hcq, hqL⟩ := exists_rat_btwn hx
      refine ⟨q, hcq, ?_⟩
      have hAe := ae_lineInf_le (ν := ν) hB i x
      refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hAe)
      change g (Function.update x i y) < q at hy
      exact not_le.mpr (hy.trans hqL)
    · rintro ⟨q, hcq, hq⟩
      refine hcq.trans_le (le_lineInf hB i x ?_)
      have hq' : ν {y | ¬(q : ℝ) ≤ g (Function.update x i y)} = 0 := by
        simp only [not_le]
        exact hq
      exact ae_iff.mpr hq'
  rw [hEq]
  exact MeasurableSet.iUnion fun q =>
    measurable_measure_prodMk_left (hSet (q : ℚ)) (measurableSet_singleton 0)

theorem measurable_lineClamp (hg : Measurable g) (hB : ∀ x, |g x| ≤ B) (i : Fin n) :
    Measurable (lineClamp ν g i) :=
  (measurable_lineInf hg hB i).max (hg.min ((measurable_lineInf hg hB i).add_const 1))

/-- The clamped function has the bound of `g`. -/
theorem abs_lineClamp_le (hB : ∀ x, |g x| ≤ B) (i : Fin n) (x : Fin n → A) :
    |lineClamp ν g i x| ≤ B := by
  have hL := abs_le.mp (abs_lineInf_le (ν := ν) hB i x)
  have hg := abs_le.mp (hB x)
  refine abs_le.mpr ⟨hL.1.trans (lineClamp_mem ν g i x).1, max_le hL.2 ?_⟩
  exact (min_le_left _ _).trans hg.2

/-- A bound at every point for a coordinate `j ≠ i` passes to the infimum on the lines of `i`. -/
theorem abs_lineInf_sub_update_le (hB : ∀ x, |g x| ≤ B) {i j : Fin n} (hij : i ≠ j)
    (hg : ∀ u a, |g u - g (Function.update u j a)| ≤ 1) (x : Fin n → A) (a : A) :
    |lineInf ν g i x - lineInf ν g i (Function.update x j a)| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hh : lineInf ν g i (Function.update x j a) - 1 ≤ lineInf ν g i x := by
      refine le_lineInf hB i x
        ((ae_lineInf_le (ν := ν) hB i (Function.update x j a)).mono fun y hy => ?_)
      rw [Function.update_comm hij.symm] at hy
      linarith only [(abs_le.mp (hg (Function.update x i y) a)).1, hy]
    linarith only [hh]
  · have hh : lineInf ν g i x - 1 ≤ lineInf ν g i (Function.update x j a) := by
      refine le_lineInf hB i _ ((ae_lineInf_le hB i x).mono fun y hy => ?_)
      rw [Function.update_comm hij.symm]
      linarith only [(abs_le.mp (hg (Function.update x i y) a)).2, hy]
    linarith only [hh]

/-- The clamp keeps a bound at every point for a coordinate `j ≠ i`. -/
theorem abs_lineClamp_sub_update_le (hB : ∀ x, |g x| ≤ B) {i j : Fin n} (hij : i ≠ j)
    (hg : ∀ u a, |g u - g (Function.update u j a)| ≤ 1) (x : Fin n → A) (a : A) :
    |lineClamp ν g i x - lineClamp ν g i (Function.update x j a)| ≤ 1 := by
  have h1 := abs_le.mp (hg x a)
  have h2 := abs_le.mp (abs_lineInf_sub_update_le (ν := ν) hB hij hg x a)
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hh := clamp_le_add_one (a := g (Function.update x j a)) (a' := g x)
      (b := lineInf ν g i (Function.update x j a)) (b' := lineInf ν g i x)
      (by linarith only [h1.1]) (by linarith only [h2.1])
    unfold lineClamp
    linarith only [hh]
  · have hh := clamp_le_add_one (a := g x) (a' := g (Function.update x j a))
      (b := lineInf ν g i x) (b' := lineInf ν g i (Function.update x j a))
      (by linarith only [h1.2]) (by linarith only [h2.2])
    unfold lineClamp
    linarith only [hh]

end Line

section Product

variable (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]

/-- What holds at almost every point holds after resampling a coordinate. -/
theorem ae_ae_update_of_ae {p : (Fin n → A) → Prop} (i : Fin n)
    (hp : ∀ᵐ x ∂Measure.pi μ, p x) :
    ∀ᵐ x ∂Measure.pi μ, ∀ᵐ y ∂μ i, p (Function.update x i y) := by
  have hmp := EfronStein.measurePreserving_update_infinitePi μ i
  rw [Measure.infinitePi_eq_pi] at hmp
  exact Measure.ae_ae_of_ae_prod (hmp.quasiMeasurePreserving.ae hp)

/-- Under the almost-sure unit bound for `i`, the clamp changes `g` on a null set only. -/
theorem ae_lineClamp_eq {g : (Fin n → A) → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (i : Fin n) (hDiff : ∀ᵐ p : (Fin n → A) × A ∂(Measure.pi μ).prod (μ i),
      |g p.1 - g (Function.update p.1 i p.2)| ≤ 1) :
    lineClamp (μ i) g i =ᵐ[Measure.pi μ] g := by
  have hmp := EfronStein.measurePreserving_update_infinitePi μ i
  rw [Measure.infinitePi_eq_pi] at hmp
  have hUpper : ∀ᵐ x ∂Measure.pi μ, g x ≤ lineInf (μ i) g i x + 1 := by
    refine (Measure.ae_ae_of_ae_prod hDiff).mono fun x hx => ?_
    rw [← sub_le_iff_le_add]
    refine le_lineInf hB i x (hx.mono fun y hy => ?_)
    linarith only [(abs_le.mp hy).2]
  have hLower : ∀ᵐ x ∂Measure.pi μ, lineInf (μ i) g i x ≤ g x := by
    have hSet : MeasurableSet {x | lineInf (μ i) g i x ≤ g x} :=
      measurableSet_le (measurable_lineInf hg hB i) hg
    rw [← hmp.map_eq]
    refine (ae_map_iff hmp.aemeasurable hSet).mpr ?_
    refine (Measure.ae_prod_iff_ae_ae (hmp.measurable hSet)).mpr
      (Eventually.of_forall fun x => (ae_lineInf_le hB i x).mono fun y hy => ?_)
    change lineInf (μ i) g i (Function.update x i y) ≤ _
    rwa [lineInf_update_self]
  filter_upwards [hUpper, hLower] with x h1 h2
  exact (congrArg (max _) (min_eq_left h1)).trans (max_eq_right h2)

/-- **A version with unit differences at every point.** A bounded measurable function with
almost-sure unit differences agrees almost everywhere with a measurable function with unit
differences at every point. -/
theorem exists_version_abs_sub_update_le {f : (Fin n → A) → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B)
    (hDiff : ∀ i, ∀ᵐ p : (Fin n → A) × A ∂(Measure.pi μ).prod (μ i),
      |f p.1 - f (Function.update p.1 i p.2)| ≤ 1) :
    ∃ g : (Fin n → A) → ℝ, Measurable g ∧ g =ᵐ[Measure.pi μ] f ∧
      ∀ x i y, |g x - g (Function.update x i y)| ≤ 1 := by
  have hAll : ∀ S : Finset (Fin n), ∃ g : (Fin n → A) → ℝ, Measurable g ∧ (∀ x, |g x| ≤ B) ∧
      g =ᵐ[Measure.pi μ] f ∧ ∀ i ∈ S, ∀ x y, |g x - g (Function.update x i y)| ≤ 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨f, hf, hB, ae_eq_refl f, by simp⟩
    | insert i S hi ih =>
      obtain ⟨g, hg, hgB, hgf, hgS⟩ := ih
      have hgD : ∀ᵐ p : (Fin n → A) × A ∂(Measure.pi μ).prod (μ i),
          |g p.1 - g (Function.update p.1 i p.2)| ≤ 1 := by
        have hOld := (Measure.quasiMeasurePreserving_fst (μ := Measure.pi μ) (ν := μ i)).ae hgf
        have hmp := EfronStein.measurePreserving_update_infinitePi μ i
        rw [Measure.infinitePi_eq_pi] at hmp
        filter_upwards [hOld, hmp.quasiMeasurePreserving.ae hgf, hDiff i] with p h1 h2 h3
        rw [h1, h2]
        exact h3
      refine ⟨lineClamp (μ i) g i, measurable_lineClamp hg hgB i, abs_lineClamp_le hgB i,
        (ae_lineClamp_eq μ hg hgB i hgD).trans hgf, ?_⟩
      intro j hj x y
      rcases Finset.mem_insert.mp hj with rfl | hjS
      · have h1 := lineClamp_mem (μ j) g j x
        have h2 := lineClamp_mem (μ j) g j (Function.update x j y)
        rw [lineInf_update_self] at h2
        exact abs_le.mpr ⟨by linarith only [h1.1, h2.2], by linarith only [h1.2, h2.1]⟩
      · have hij : i ≠ j := fun h => hi (h ▸ hjS)
        exact abs_lineClamp_sub_update_le hgB hij (hgS j hjS) x y
  obtain ⟨g, hg, -, hgf, hgd⟩ := hAll Finset.univ
  exact ⟨g, hg, hgf, fun x i y => hgd i (Finset.mem_univ i) x y⟩

/-- The proxy `V₊` does not see a change of `f` on a null set. -/
theorem ae_vPlus_eq_of_ae_eq {f g : (Fin n → A) → ℝ} (hfg : g =ᵐ[Measure.pi μ] f) :
    ∀ᵐ x ∂Measure.pi μ, vPlus μ g x = vPlus μ f x := by
  filter_upwards [hfg, ae_all_iff.mpr fun i => ae_ae_update_of_ae μ i hfg] with x hx hxi
  refine Finset.sum_congr rfl fun i _ => lintegral_congr_ae ((hxi i).mono fun y hy => ?_)
  simp only [hx, hy]

end Product

end IsotropicVariance.Infra.Concentration
