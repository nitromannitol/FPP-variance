/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FunProp

/-!
# A jointly measurable version with simultaneous agreement

Choose measurable versions on a countable dense set and remove one measurable null set.
Continuity then recovers measurable evaluations everywhere, without taking an uncountable
union of exceptional sets. The resulting random function agrees with the original one at
all points on a single full-measure event.
-/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace IsotropicVariance.Infra.Measurability

/-- Continuous random functions with a.e.-measurable evaluations have jointly measurable
versions agreeing simultaneously everywhere. -/
theorem exists_jointlyMeasurable_version {Ω Z : Type*} [MeasurableSpace Ω]
    [MetricSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure Ω) (f : Ω → Z → ℝ) (hc : ∀ ω, Continuous (f ω))
    (hf : ∀ z, AEMeasurable (fun ω => f ω z) μ) :
    ∃ g : Ω → Z → ℝ, Measurable (Function.uncurry g) ∧
      (∀ ω, Continuous (g ω)) ∧ ∀ᵐ ω ∂μ, ∀ z, g ω z = f ω z := by
  classical
  cases isEmpty_or_nonempty Z with
  | inl h =>
    exact ⟨fun _ _ => 0, measurable_const, fun _ => continuous_const,
      Filter.Eventually.of_forall fun _ z => isEmptyElim z⟩
  | inr h =>
    let d := denseSeq Z
    let v (n : ℕ) := (hf (d n)).mk (fun ω => f ω (d n))
    have hv (n : ℕ) : Measurable (v n) := (hf (d n)).measurable_mk
    have hgood : ∀ᵐ ω ∂μ, ∀ n, f ω (d n) = v n ω :=
      ae_all_iff.mpr fun n => (hf (d n)).ae_eq_mk
    obtain ⟨N, hNsub, hNm, hNμ⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
    let g : Ω → Z → ℝ := fun ω z => if ω ∈ N then 0 else f ω z
    have hgc (ω : Ω) : Continuous (g ω) := by
      by_cases hω : ω ∈ N
      · simpa only [g, hω, ↓reduceIte] using (continuous_const : Continuous (fun _ : Z => (0 : ℝ)))
      · simpa only [g, hω, ↓reduceIte] using hc ω
    have hgd (n : ℕ) : Measurable (fun ω => g ω (d n)) := by
      have heq : (fun ω => g ω (d n)) = fun ω => if ω ∈ N then 0 else v n ω := by
        funext ω
        by_cases hω : ω ∈ N
        · simp [g, hω]
        · have hh : ∀ n, f ω (d n) = v n ω := by
            by_contra hh
            exact hω (hNsub hh)
          simp [g, hω, hh n]
      rw [heq]
      exact Measurable.ite hNm measurable_const (hv n)
    have hgz (z : Z) : Measurable (fun ω => g ω z) := by
      obtain ⟨s, hs, hsz⟩ := mem_closure_iff_seq_limit.mp (denseRange_denseSeq Z z)
      choose n hn using hs
      have hseq : Tendsto (fun k => d (n k)) atTop (𝓝 z) := by
        simpa only [d, hn] using hsz
      apply measurable_of_tendsto_metrizable (fun k => hgd (n k))
      rw [tendsto_pi_nhds]
      exact fun ω => ((hgc ω).tendsto z).comp hseq
    have hgm : Measurable (Function.uncurry g) := by
      have h := measurable_uncurry_of_continuous_of_measurable hgc hgz
      exact h.comp measurable_swap
    refine ⟨g, hgm, hgc, ?_⟩
    filter_upwards [show ∀ᵐ ω ∂μ, ω ∉ N from (by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hNμ)] with ω hω
    intro z
    simp [g, hω]

end IsotropicVariance.Infra.Measurability
