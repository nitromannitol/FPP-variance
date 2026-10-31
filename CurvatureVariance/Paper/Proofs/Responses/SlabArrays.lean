/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.Slabs
public import CurvatureVariance.Infra.EfronStein.Coordinates
import CurvatureVariance.Infra.FPP.Model

/-!
# Measurability, locality and independence of slab radii

The arrays of Lemma `lem:blocks` are independent across slabs because their entries read only
the owned slab edges. The countable supremum defining the localization radius is measurable,
including its predicates asserting that a path attains the restricted distance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- Being a slab geodesic is a measurable predicate in the configuration. -/
theorem measurableSet_isSlabGeodesic (p q : ℤ) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) : MeasurableSet {ω : Config m | IsSlabGeodesic ω p q γ} := by
  classical
  by_cases hp : γ.IsPath
  · by_cases he : ∀ e ∈ γ.edges, e ∈ slabEdges p q
    · have hs : {ω : Config m | IsSlabGeodesic ω p q γ} =
          {ω : Config m | (walkCost ω γ : ℝ≥0∞) = slabTime ω p q u v} := by
        ext ω
        exact ⟨fun h => h.2.2, fun h => ⟨hp, he, h⟩⟩
      rw [hs]
      exact measurableSet_eq_fun (Infra.FPP.measurable_walkCost γ).coe_nnreal_ennreal
        (measurable_restrictedTime (slabEdges p q) u v)
    · simp only [IsSlabGeodesic, he, and_false, false_and, Set.ofPred_false, MeasurableSet.empty]
  · simp only [IsSlabGeodesic, hp, false_and, Set.ofPred_false, MeasurableSet.empty]

/-- The supremum of path deviations is measurable if the path predicate is measurable. -/
theorem measurable_deviation
    (geo : Config m → ∀ {u v : Vertex m}, (latticeGraph m).Walk u v → Prop)
    (hgeo : ∀ (u v : Vertex m) (γ : (latticeGraph m).Walk u v),
      MeasurableSet {ω : Config m | geo ω γ}) (I I' : Set (Vertex m)) :
    Measurable fun ω => deviation (geo ω) I I' := by
  classical
  unfold deviation
  refine Measurable.iSup fun u => Measurable.iSup fun _ => Measurable.iSup fun v =>
    Measurable.iSup fun _ => Measurable.iSup fun γ => ?_
  let c : ℝ≥0∞ := ⨆ (x : Vertex m) (_ : x ∈ γ.support),
    ENNReal.ofReal (Metric.infDist (point x) (segment ℝ (point u) (point v)))
  have heq : (fun ω : Config m => ⨆ (_ : geo ω γ), c) =
      {ω : Config m | geo ω γ}.indicator (fun _ => c) := by
    funext ω
    by_cases h : geo ω γ <;> simp only [h, iSup_true, iSup_false, Set.indicator_of_mem,
      Set.indicator_of_notMem, Set.mem_ofPred_eq, not_false_eq_true, bot_eq_zero]
  change Measurable (fun ω : Config m => ⨆ (_ : geo ω γ), c)
  rw [heq]
  exact measurable_const.indicator (hgeo u v γ)

/-- Slab localization radii are measurable extended random variables. -/
theorem measurable_locRadiusSlab (p q : ℤ) (I I' : Set (Vertex m)) (W : ℝ) :
    Measurable fun ω : Config m => locRadiusSlab ω p q I I' W := by
  exact measurable_const.add ((measurable_deviation (fun ω _ _ γ => IsSlabGeodesic ω p q γ)
    (fun _ _ γ => measurableSet_isSlabGeodesic p q γ) I I').div_const _)

/-- Slab localization radii depend only on the weights owned by that slab. -/
theorem locRadiusSlab_congr {ω ω' : Config m} (p q : ℤ) (I I' : Set (Vertex m)) (W : ℝ)
    (h : ∀ e : Edge m, e.1 ∈ slabEdges p q → ω e = ω' e) :
    locRadiusSlab ω p q I I' W = locRadiusSlab ω' p q I I' W := by
  have htime : ∀ u v, slabTime ω p q u v = slabTime ω' p q u v :=
    fun u v => restrictedTime_congr _ u v h
  have hgeo : ∀ (u v : Vertex m) (γ : (latticeGraph m).Walk u v),
      IsSlabGeodesic ω p q γ = IsSlabGeodesic ω' p q γ := by
    intro u v γ
    apply propext
    constructor
    · rintro ⟨hp, he, hc⟩
      refine ⟨hp, he, ?_⟩
      rw [← htime u v, ← Infra.FPP.walkCost_congr ω γ (fun e he' => h e (he e he'))]
      exact hc
    · rintro ⟨hp, he, hc⟩
      refine ⟨hp, he, ?_⟩
      rw [htime u v, Infra.FPP.walkCost_congr ω γ (fun e he' => h e (he e he'))]
      exact hc
  simp only [locRadiusSlab, deviation, hgeo]

/-- Measurable functions of disjoint slabs are independent under the model's iid law. -/
theorem iIndepFun_slab_functions {P : Measure (Config m)} {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] (hP : IsIIDWeights P F) {K n : ℕ}
    {β : Fin K → Type*} [∀ i, MeasurableSpace (β i)] (Z : (i : Fin K) → Config m → β i)
    (hZ : ∀ i, Measurable (Z i))
    (hlocal : ∀ (i : Fin K) (ω ω' : Config m), (∀ e : Edge m,
      e.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n) → ω e = ω' e) → Z i ω = Z i ω') :
    iIndepFun Z P := by
  classical
  let E : Fin K → Set (Edge m) := fun i =>
    {e | e.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n)}
  let ext : (i : Fin K) → (E i → ℝ≥0) → Config m := fun i ξ e =>
    if h : e ∈ E i then ξ ⟨e, h⟩ else 0
  have hext : ∀ i, Measurable (ext i) := by
    intro i
    refine measurable_pi_iff.mpr fun e => ?_
    by_cases he : e ∈ E i
    · simpa only [ext, he, dite_true] using measurable_pi_apply (⟨e, he⟩ : E i)
    · simpa only [ext, he, dite_false] using (measurable_const : Measurable (fun _ : E i → ℝ≥0 => (0 : ℝ≥0)))
  have hdisj : Pairwise fun i j => Disjoint (E i) (E j) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun e hi hj => ?_
    have hd := pairwise_disjoint_slabEdges (m := m) 0 n
      (show (i : ℕ) ≠ (j : ℕ) from fun h => hij (Fin.ext h))
    simp only [zero_add] at hd
    exact Set.disjoint_left.mp hd hi hj
  rw [Infra.FPP.IsIIDWeights.eq_infinitePi hP]
  have hind := Infra.EfronStein.iIndepFun_comp_restrict_infinitePi
    (fun _ : Edge m => F) E hdisj (fun i ξ => Z i (ext i ξ)) (fun i => (hZ i).comp (hext i))
  convert hind using 1
  funext i ω
  exact hlocal i ω (ext i fun e => ω e.1) (fun e he => by simp only [ext, show e ∈ E i from he, dite_true])

end CurvatureVariance.Paper.Responses
