/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Logic.Function.DependsOn
import CurvatureVariance.Infra.EfronStein.Coordinates

/-!
# Bernoulli product measures

`bernoulliProduct ι p` is the law of independent coordinates `ω i ∈ Bool`, each `true` with
probability `p`: the configuration space of Bernoulli percolation on the index type `ι` (the edges
of a graph), with `ω i = true` meaning that `i` is open. Main facts:

* `bernoulliProduct_coord`: one coordinate is `true` with probability `p` and `false` with
  probability `1 - p`;
* `extendFalse`, `eq_preimage_restrict_of_dependsOn`: an event that depends only on the coordinates
  in `D` is a cylinder over `D`;
* `measure_inter_eq_mul_of_dependsOn`: events depending on disjoint sets of coordinates are
  independent;
* `setBernoulli_univ_eq_map`: Mathlib's `setBer(univ, p)`, the law of the random set of open
  coordinates, is the image of `bernoulliProduct ι p` under `ω ↦ {i | ω i = true}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {ι : Type*}

/-- **The Bernoulli product measure**: the coordinates `ω i ∈ Bool` are independent, each `true`
with probability `p`. -/
noncomputable def bernoulliProduct (ι : Type*) (p : I) : Measure (ι → Bool) :=
  Measure.infinitePi fun _ : ι => bernoulliMeasure true false p

instance (p : I) : IsProbabilityMeasure (bernoulliProduct ι p) := by
  unfold bernoulliProduct; infer_instance

/-- The Bernoulli law gives mass `p` to `true`. -/
theorem bernoulliMeasure_true (p : I) :
    bernoulliMeasure true false p {true} = ENNReal.ofReal p := by
  rw [← bernoulliMeasure_real_apply_of_mem_of_notMem (x := true) (y := false) p
    (measurableSet_singleton true) rfl (by simp), measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The Bernoulli law gives mass `1 - p` to `false`. -/
theorem bernoulliMeasure_false (p : I) :
    bernoulliMeasure true false p {false} = ENNReal.ofReal (1 - p) := by
  rw [← bernoulliMeasure_real_apply_of_notMem_of_mem (x := true) (y := false) p
    (measurableSet_singleton false) (by simp) rfl, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The law of one coordinate. -/
theorem bernoulliProduct_coord (p : I) (i : ι) (b : Bool) :
    bernoulliProduct ι p {ω | ω i = b} = bernoulliMeasure true false p {b} := by
  have h := (measurePreserving_eval_infinitePi (fun _ : ι => bernoulliMeasure true false p)
    i).measure_preimage (measurableSet_singleton b).nullMeasurableSet
  exact h

/-- One coordinate is open with probability `p`. -/
theorem bernoulliProduct_coord_true (p : I) (i : ι) :
    bernoulliProduct ι p {ω | ω i = true} = ENNReal.ofReal p := by
  rw [bernoulliProduct_coord, bernoulliMeasure_true]

/-- One coordinate is closed with probability `1 - p`. -/
theorem bernoulliProduct_coord_false (p : I) (i : ι) :
    bernoulliProduct ι p {ω | ω i = false} = ENNReal.ofReal (1 - p) := by
  rw [bernoulliProduct_coord, bernoulliMeasure_false]

/-! ### Cylinder events -/

open Classical in
/-- Extend a configuration on `D` by closed coordinates outside `D`. -/
noncomputable def extendFalse (D : Set ι) (η : D → Bool) : ι → Bool :=
  fun i => if h : i ∈ D then η ⟨i, h⟩ else false

theorem measurable_extendFalse (D : Set ι) : Measurable (extendFalse D) := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ D
  · simp only [extendFalse, h, dite_true]
    exact measurable_pi_apply _
  · simp only [extendFalse, h, dite_false]
    exact measurable_const

theorem extendFalse_domRestrict_of_mem (D : Set ι) (ω : ι → Bool) {i : ι} (hi : i ∈ D) :
    extendFalse D (D.domRestrict ω) i = ω i := by
  simp [extendFalse, hi, Set.domRestrict]

/-- An event depending only on the coordinates in `D` is the cylinder over its trace on `D`. -/
theorem eq_preimage_restrict_of_dependsOn {A : Set (ι → Bool)} {D : Set ι}
    (h : DependsOn (· ∈ A) D) : A = D.domRestrict ⁻¹' (extendFalse D ⁻¹' A) := by
  ext ω
  simp only [Set.mem_preimage]
  exact (h fun i hi => (extendFalse_domRestrict_of_mem D ω hi).symm).to_iff

/-- **Independence of events depending on disjoint sets of coordinates.** -/
theorem measure_inter_eq_mul_of_dependsOn {A B : Set (ι → Bool)} {D₁ D₂ : Set ι}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAD : DependsOn (· ∈ A) D₁)
    (hBD : DependsOn (· ∈ B) D₂) (hD : Disjoint D₁ D₂) (p : I) :
    bernoulliProduct ι p (A ∩ B) = bernoulliProduct ι p A * bernoulliProduct ι p B := by
  have hind := Infra.EfronStein.indepFun_restrict_infinitePi
    (fun _ : ι => bernoulliMeasure true false p) D₁ D₂ hD
  rw [eq_preimage_restrict_of_dependsOn hAD, eq_preimage_restrict_of_dependsOn hBD]
  exact hind.measure_inter_preimage_eq_mul _ _ (measurable_extendFalse D₁ hA)
    (measurable_extendFalse D₂ hB)

/-! ### Updating one coordinate -/

/-- The event that `A` occurs after coordinate `i` is set to `b`. -/
def updateEvent [DecidableEq ι] (A : Set (ι → Bool)) (i : ι) (b : Bool) : Set (ι → Bool) :=
  {ω | Function.update ω i b ∈ A}

theorem measurableSet_updateEvent [DecidableEq ι] {A : Set (ι → Bool)} (hA : MeasurableSet A)
    (i : ι) (b : Bool) : MeasurableSet (updateEvent A i b) :=
  measurable_update' (a := i) |>.comp (measurable_id.prodMk measurable_const) hA

/-- After setting coordinate `i`, an event depending on `D` depends only on `D \ {i}`. -/
theorem dependsOn_updateEvent [DecidableEq ι] {A : Set (ι → Bool)} {D : Set ι}
    (h : DependsOn (· ∈ A) D) (i : ι) (b : Bool) :
    DependsOn (· ∈ updateEvent A i b) (D \ {i}) := by
  intro ω ω' hω
  refine h fun j hj => ?_
  by_cases hji : j = i
  · subst hji; simp
  · simp [Function.update_of_ne hji, hω j ⟨hj, hji⟩]

/-- The coordinate event `{ω i = b}` depends only on `{i}`. -/
theorem dependsOn_coord (i : ι) (b : Bool) : DependsOn (· ∈ {ω : ι → Bool | ω i = b}) {i} := by
  intro ω ω' h
  simp [h i rfl]

/-- An upper set's update events are nested: closing coordinate `i` can only destroy it. -/
theorem updateEvent_false_subset_true [DecidableEq ι] {A : Set (ι → Bool)} (hA : IsUpperSet A)
    (i : ι) : updateEvent A i false ⊆ updateEvent A i true := by
  intro ω hω
  refine hA (fun j => ?_) hω
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-! ### Mathlib's `setBernoulli` -/

/-- The set of open coordinates. -/
def openSet (ω : ι → Bool) : Set ι := {i | ω i = true}

theorem measurable_openSet : Measurable (openSet (ι := ι)) := by
  rw [measurable_set_iff]
  intro a
  exact (Measurable.of_discrete (f := fun b : Bool => b = true)).comp (measurable_pi_apply a)

/-- **Mathlib's `setBernoulli` on all coordinates** is the law of the set of open coordinates under
`bernoulliProduct`. -/
theorem setBernoulli_univ_eq_map (p : I) :
    setBer((Set.univ : Set ι), p) = (bernoulliProduct ι p).map openSet := by
  rw [setBernoulli_eq_map]
  have hf : Measurable (fun (ω : ι → Bool) (i : ι) => ω i = true) :=
    measurable_pi_iff.2 fun a =>
      (Measurable.of_discrete (f := fun b : Bool => b = true)).comp (measurable_pi_apply a)
  have h1 : (bernoulliProduct ι p).map (fun ω i => ω i = true) =
      Measure.infinitePi fun i : ι => bernoulliMeasure (i ∈ (Set.univ : Set ι)) False p := by
    refine (Measure.infinitePi_map_pi (fun _ : ι => bernoulliMeasure true false p)
      (f := fun _ (b : Bool) => b = true) (fun _ => Measurable.of_discrete)).trans ?_
    congr 1
    funext i
    rw [map_bernoulliMeasure' _ _ Measurable.of_discrete]
    simp
  have h2 : (openSet : (ι → Bool) → Set ι) =
      (fun P : ι → Prop => {i | P i}) ∘ (fun ω i => ω i = true) := rfl
  rw [h2, ← Measure.map_map (μ := bernoulliProduct ι p) measurable_setOfPred hf, h1]

end CurvatureVariance.Infra.Percolation
