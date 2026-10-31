/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Product
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Russo's formula and monotonicity for Bernoulli product measures

For an event `A` depending on the finite set `D` of coordinates, the probability
`bernoulliProduct ι p A` is the polynomial `cylinderPoly D A p` in `p`
(`toReal_bernoulliProduct_eq_cylinderPoly`). Differentiating this polynomial gives

* `hasDerivAt_cylinderPoly_eq_sum`: **Russo's formula**, the derivative is
  `∑ i ∈ D, (P(A with i open) - P(A with i closed))`;
* `hasDerivAt_cylinderPoly_eq_sum_pivotal`: for increasing events, the derivative is the sum of the
  probabilities that the coordinates are pivotal;
* `monotone_bernoulliProduct_of_isUpperSet`: increasing events have increasing probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {ι : Type*} [DecidableEq ι]

/-- The weight of one coordinate value: `p` for `true`, `1 - p` for `false`. -/
def coordWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

open Classical in
/-- Extend a configuration on the finite set `D` by closed coordinates. -/
noncomputable def finExtend (D : Finset ι) (η : D → Bool) : ι → Bool :=
  fun i => if h : i ∈ D then η ⟨i, h⟩ else false

/-- The probability polynomial of an event, summed over the configurations on `D`. -/
noncomputable def cylinderPoly (D : Finset ι) (A : Set (ι → Bool)) (p : ℝ) : ℝ :=
  ∑ η : D → Bool, A.indicator (fun _ => (1 : ℝ)) (finExtend D η) * ∏ i : D, coordWeight p (η i)

theorem coordWeight_nonneg {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (b : Bool) :
    0 ≤ coordWeight p b := by
  cases b <;> simp [coordWeight] <;> linarith [hp.1, hp.2]

theorem bernoulliMeasure_singleton (p : I) (b : Bool) :
    bernoulliMeasure true false p {b} = ENNReal.ofReal (coordWeight p b) := by
  cases b
  · simpa [coordWeight] using bernoulliMeasure_false p
  · simpa [coordWeight] using bernoulliMeasure_true p

theorem restrict_finExtend_dependsOn {A : Set (ι → Bool)} {D : Finset ι}
    (hdep : DependsOn (· ∈ A) (D : Set ι)) :
    A = D.restrict ⁻¹' (finExtend D ⁻¹' A) := by
  ext ω
  simp only [Set.mem_preimage]
  refine (hdep fun i hi => ?_).to_iff
  simp [finExtend, Finset.restrict, Finset.mem_coe.1 hi]

/-- An event depending only on `D` has probability `cylinderPoly D A p`. -/
theorem toReal_bernoulliProduct_eq_cylinderPoly (D : Finset ι) {A : Set (ι → Bool)}
    (_hA : MeasurableSet A) (hdep : DependsOn (· ∈ A) (D : Set ι)) (p : unitInterval) :
    (bernoulliProduct ι p A).toReal = cylinderPoly D A p := by
  classical
  have hB : MeasurableSet (finExtend D ⁻¹' A) := (Set.toFinite _).measurableSet
  have h1 : bernoulliProduct ι p A = Measure.pi (fun _ : D => bernoulliMeasure true false p)
      (finExtend D ⁻¹' A) := by
    have hm : (bernoulliProduct ι p).map D.restrict =
        Measure.pi (fun _ : D => bernoulliMeasure true false p) :=
      Measure.infinitePi_map_restrict (fun _ : ι => bernoulliMeasure true false p)
    rw [← hm, Measure.map_apply (Finset.measurable_restrict _) hB, ← restrict_finExtend_dependsOn hdep]
  have h2 : Measure.pi (fun _ : D => bernoulliMeasure true false p) (finExtend D ⁻¹' A) =
      ∑ η ∈ (Set.toFinite (finExtend D ⁻¹' A)).toFinset,
        Measure.pi (fun _ : D => bernoulliMeasure true false p) {η} := by
    rw [MeasureTheory.sum_measure_singleton]; simp [Set.preimage]
  rw [h1, h2, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), cylinderPoly]
  simp only [Measure.pi_singleton, bernoulliMeasure_singleton]
  have hp : (p : ℝ) ∈ Set.Icc (0 : ℝ) 1 := p.2
  have h3 : ∀ η : D → Bool, (∏ i : D, ENNReal.ofReal (coordWeight p (η i))).toReal =
      ∏ i : D, coordWeight p (η i) := fun η => by
    rw [ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (coordWeight_nonneg hp _)
  simp only [h3]
  have h4 : ∀ η : D → Bool, A.indicator (fun _ => (1 : ℝ)) (finExtend D η) *
      ∏ i : D, coordWeight p (η i) =
      if η ∈ (Set.toFinite (finExtend D ⁻¹' A)).toFinset then ∏ i : D, coordWeight p (η i)
      else 0 := fun η => by
    by_cases h : finExtend D η ∈ A <;> simp [Set.indicator, h]
  simp only [h4]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-! ### The derivative of the probability polynomial -/

theorem finExtend_update (D : Finset ι) (η : D → Bool) (i : D) (b : Bool) :
    finExtend D (Function.update η i b) = Function.update (finExtend D η) (i : ι) b := by
  funext j
  by_cases hji : j = (i : ι)
  · subst hji; simp [finExtend]
  · by_cases hj : j ∈ D
    · have : (⟨j, hj⟩ : D) ≠ i := fun h => hji (congrArg Subtype.val h)
      simp [finExtend, hj, Function.update_of_ne hji, Function.update_of_ne this]
    · simp [finExtend, hj, Function.update_of_ne hji]

theorem hasDerivAt_coordWeight (b : Bool) (p : ℝ) :
    HasDerivAt (fun p => coordWeight p b) (if b then 1 else -1) p := by
  cases b
  · simpa [coordWeight] using (hasDerivAt_id' p).const_sub 1
  · simpa [coordWeight] using hasDerivAt_id' p

/-- Summing a function invariant under updates of coordinate `i` over the configurations with
`η i = false` or over those with `η i = true` gives the same value. -/
theorem sum_ite_not_eq {D : Finset ι} (i : D) (h : (D → Bool) → ℝ)
    (hinv : ∀ η b, h (Function.update η i b) = h η) :
    ∑ η : D → Bool, (if η i then 0 else h η) = ∑ η : D → Bool, (if η i then h η else 0) := by
  let swp : Equiv.Perm (D → Bool) := Function.Involutive.toPerm
    (fun η => Function.update η i (!η i)) (by
      intro η; funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj])
  rw [← Equiv.sum_comp swp]
  refine Finset.sum_congr rfl fun η _ => ?_
  have hswp : swp η = Function.update η i (!η i) := rfl
  rw [hswp, hinv]
  cases h : η i <;> simp

theorem sum_mul_ite_eq {D : Finset ι} (i : D) (h : (D → Bool) → ℝ)
    (hinv : ∀ η b, h (Function.update η i b) = h η) (a b : ℝ) :
    ∑ η : D → Bool, h η * (if η i then a else b) =
      (a + b) * ∑ η : D → Bool, (if η i then h η else 0) := by
  have h1 : ∀ η : D → Bool, h η * (if η i then a else b) =
      (if η i then h η * a else 0) + (if η i then 0 else h η * b) := fun η => by
    cases η i <;> simp
  simp only [h1, Finset.sum_add_distrib]
  rw [sum_ite_not_eq i (fun η => h η * b) (fun η c => by simp [hinv]), ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  cases η i <;> simp
  ring

theorem sum_key {D : Finset ι} (A : Set (ι → Bool)) (p : ℝ) (i : D) :
    ∑ η : D → Bool, A.indicator (fun _ => (1 : ℝ)) (finExtend D η) *
        ((∏ j ∈ Finset.univ.erase i, coordWeight p (η j)) * (if η i then 1 else -1)) =
      cylinderPoly D (updateEvent A i true) p - cylinderPoly D (updateEvent A i false) p := by
  set K : (D → Bool) → ℝ := fun η => ∏ j ∈ Finset.univ.erase i, coordWeight p (η j) with hK
  set g : Bool → (D → Bool) → ℝ :=
    fun b η => A.indicator (fun _ => (1 : ℝ)) (finExtend D (Function.update η i b)) with hg
  have hKinv : ∀ η b, K (Function.update η i b) = K η := fun η b => by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hginv : ∀ b b' η, g b (Function.update η i b') = g b η := fun b b' η => by
    simp [hg, Function.update_idem]
  have hc : ∀ η, A.indicator (fun _ => (1 : ℝ)) (finExtend D η) = g (η i) η := fun η => by
    simp [hg]
  have hupd : ∀ (b : Bool) η, (updateEvent A i b).indicator (fun _ => (1 : ℝ)) (finExtend D η) =
      g b η := fun b η => by
    have hmem : finExtend D η ∈ updateEvent A i b ↔ finExtend D (Function.update η i b) ∈ A := by
      rw [finExtend_update]; rfl
    by_cases h : finExtend D (Function.update η i b) ∈ A <;> simp [hg, Set.indicator, hmem, h]
  have hprod : ∀ η : D → Bool, ∏ j, coordWeight p (η j) = coordWeight p (η i) * K η :=
    fun η => (Finset.mul_prod_erase Finset.univ (fun j => coordWeight p (η j))
      (Finset.mem_univ i)).symm
  have hF : ∀ η b, (g true (Function.update η i b) - g false (Function.update η i b)) *
      K (Function.update η i b) = (g true η - g false η) * K η := fun η b => by
    rw [hginv, hginv, hKinv]
  have hR : cylinderPoly D (updateEvent A i true) p - cylinderPoly D (updateEvent A i false) p =
      ∑ η : D → Bool, ((g true η - g false η) * K η) * (if η i then p else 1 - p) := by
    unfold cylinderPoly
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [hupd, hupd, hprod]
    simp only [coordWeight]
    ring
  have hL : ∀ η : D → Bool, A.indicator (fun _ => (1 : ℝ)) (finExtend D η) *
      (K η * (if η i then 1 else -1)) =
      (g true η * K η) * (if η i then 1 else 0) + (g false η * K η) * (if η i then 0 else -1) :=
    fun η => by
    rw [hc]; cases η i <;> simp
  simp only [hK] at hL hR hF
  rw [hR]
  simp only [hL, Finset.sum_add_distrib]
  rw [sum_mul_ite_eq i (fun η => g true η * K η) (fun η b => by simp only [hginv, hKinv]),
    sum_mul_ite_eq i (fun η => g false η * K η) (fun η b => by simp only [hginv, hKinv]),
    sum_mul_ite_eq i (fun η => (g true η - g false η) * K η) (fun η b => hF η b), ← sub_eq_add_neg]
  have hsub : ∑ η : D → Bool, (if η i then (g true η - g false η) * K η else 0) =
      ∑ η : D → Bool, (if η i then g true η * K η else 0) -
        ∑ η : D → Bool, (if η i then g false η * K η else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun η _ => ?_
    cases η i <;> simp [sub_mul]
  rw [hsub]
  ring

/-- The derivative of the probability polynomial (algebraic Russo formula). -/
theorem hasDerivAt_cylinderPoly (D : Finset ι) (A : Set (ι → Bool)) (p : ℝ) :
    HasDerivAt (cylinderPoly D A)
      (∑ i ∈ D, (cylinderPoly D (updateEvent A i true) p -
        cylinderPoly D (updateEvent A i false) p)) p := by
  have hprod : ∀ η : D → Bool, HasDerivAt (fun p => ∏ i : D, coordWeight p (η i))
      (∑ i : D, (∏ j ∈ Finset.univ.erase i, coordWeight p (η j)) * (if η i then 1 else -1)) p :=
    fun η => by
    simpa using HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun (i : D) p => coordWeight p (η i)) (f' := fun i => if η i then (1 : ℝ) else -1)
      (x := p) (fun i _ => hasDerivAt_coordWeight (η i) p)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun η _ =>
    (hprod η).const_mul (A.indicator (fun _ => (1 : ℝ)) (finExtend D η))
  refine hsum.congr_deriv ?_
  rw [← Finset.sum_coe_sort D]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_key A p i

theorem continuous_cylinderPoly (D : Finset ι) (A : Set (ι → Bool)) :
    Continuous (cylinderPoly D A) :=
  continuous_iff_continuousAt.2 fun p => (hasDerivAt_cylinderPoly D A p).continuousAt

/-- **Russo's formula**, for an event depending on finitely many coordinates. -/
theorem hasDerivAt_cylinderPoly_eq_sum (D : Finset ι) {A : Set (ι → Bool)}
    (hA : MeasurableSet A) (hdep : DependsOn (· ∈ A) (D : Set ι)) (p : unitInterval) :
    HasDerivAt (cylinderPoly D A)
      (∑ i ∈ D, ((bernoulliProduct ι p (updateEvent A i true)).toReal -
        (bernoulliProduct ι p (updateEvent A i false)).toReal)) p := by
  refine (hasDerivAt_cylinderPoly D A p).congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  rw [toReal_bernoulliProduct_eq_cylinderPoly D (measurableSet_updateEvent hA i true)
      ((dependsOn_updateEvent hdep i true).mono Set.sdiff_subset) p,
    toReal_bernoulliProduct_eq_cylinderPoly D (measurableSet_updateEvent hA i false)
      ((dependsOn_updateEvent hdep i false).mono Set.sdiff_subset) p]

/-- The pivotal event of coordinate `i` for `A`: opening `i` makes `A` occur, closing it does
not. -/
def pivotalEvent (A : Set (ι → Bool)) (i : ι) : Set (ι → Bool) :=
  updateEvent A i true \ updateEvent A i false

/-- For an increasing event, the probability of the pivotal event is the difference of the
probabilities of the two update events. -/
theorem toReal_bernoulliProduct_pivotalEvent {A : Set (ι → Bool)} (hA : MeasurableSet A)
    (hup : IsUpperSet A) (i : ι) (p : unitInterval) :
    (bernoulliProduct ι p (pivotalEvent A i)).toReal =
      (bernoulliProduct ι p (updateEvent A i true)).toReal -
        (bernoulliProduct ι p (updateEvent A i false)).toReal := by
  unfold pivotalEvent
  rw [measure_sdiff (updateEvent_false_subset_true hup i)
    (measurableSet_updateEvent hA i false).nullMeasurableSet (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le (measure_mono (updateEvent_false_subset_true hup i))
      (measure_ne_top _ _)]

/-- **Russo's formula for increasing events**: the derivative is the sum of the probabilities that
the coordinates are pivotal. -/
theorem hasDerivAt_cylinderPoly_eq_sum_pivotal (D : Finset ι) {A : Set (ι → Bool)}
    (hA : MeasurableSet A) (hdep : DependsOn (· ∈ A) (D : Set ι)) (hup : IsUpperSet A)
    (p : unitInterval) :
    HasDerivAt (cylinderPoly D A) (∑ i ∈ D, (bernoulliProduct ι p (pivotalEvent A i)).toReal) p :=
  (hasDerivAt_cylinderPoly_eq_sum D hA hdep p).congr_deriv
    (Finset.sum_congr rfl fun i _ => (toReal_bernoulliProduct_pivotalEvent hA hup i p).symm)

/-- Whether coordinate `i` is pivotal does not depend on `ω i`: being pivotal and closed has
probability `(1 - p)` times the probability of being pivotal. -/
theorem bernoulliProduct_pivotalEvent_inter_false {A : Set (ι → Bool)} (hA : MeasurableSet A)
    (i : ι) (p : unitInterval) :
    bernoulliProduct ι p (pivotalEvent A i ∩ {ω | ω i = false}) =
      ENNReal.ofReal (1 - p) * bernoulliProduct ι p (pivotalEvent A i) := by
  have hT := dependsOn_updateEvent (dependsOn_univ (· ∈ A)) i true
  have hF := dependsOn_updateEvent (dependsOn_univ (· ∈ A)) i false
  have hpiv : DependsOn (· ∈ pivotalEvent A i) (Set.univ \ {i}) := fun ω ω' h => by
    have h1 := hT h
    have h2 := hF h
    simp only [pivotalEvent, Set.mem_sdiff] at h1 h2 ⊢
    rw [h1, h2]
  have hmeas : MeasurableSet {ω : ι → Bool | ω i = false} :=
    (measurableSet_singleton false).preimage (measurable_pi_apply i)
  have hpm : MeasurableSet (pivotalEvent A i) :=
    (measurableSet_updateEvent hA i true).diff (measurableSet_updateEvent hA i false)
  rw [measure_inter_eq_mul_of_dependsOn hpm hmeas
    hpiv (dependsOn_coord i false) Set.disjoint_sdiff_left p, bernoulliProduct_coord_false,
    mul_comm]

/-- **Increasing events have increasing probability**, for events depending on finitely many
coordinates. -/
theorem monotone_bernoulliProduct_of_isUpperSet (D : Finset ι) {A : Set (ι → Bool)}
    (hA : MeasurableSet A) (hdep : DependsOn (· ∈ A) (D : Set ι)) (hup : IsUpperSet A) :
    Monotone fun p : unitInterval => bernoulliProduct ι p A := by
  have hmono : MonotoneOn (cylinderPoly D A) (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_cylinderPoly D A).continuousOn
      (fun x _ => (hasDerivAt_cylinderPoly D A x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    rw [(hasDerivAt_cylinderPoly_eq_sum_pivotal D hA hdep hup (⟨x, hx'⟩ : unitInterval)).deriv]
    exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  intro p q hpq
  have h := hmono p.2 q.2 hpq
  rw [← toReal_bernoulliProduct_eq_cylinderPoly D hA hdep,
    ← toReal_bernoulliProduct_eq_cylinderPoly D hA hdep] at h
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 h

end CurvatureVariance.Infra.Percolation
