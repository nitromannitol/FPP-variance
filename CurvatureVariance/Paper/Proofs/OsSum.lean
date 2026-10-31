/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Inputs.IsOs
public import CurvatureVariance.Statements.Inputs.ExistsIsOsIntegral
import CurvatureVariance.Infra.Os.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Count

/-!
# Equation `eq:sum` for `s ≥ 1`, from [AKM, Lemma A.4]

Equation `eq:sum` (Section `ssec:notation`): "by [AKM, Lemma A.4] applied to the positive parts".
The cited `CurvatureVariance.exists_isOs_integral` is applied with `E` the finite index set, with
the top σ-algebra, and `ν` the counting measure, so that its integrals are finite sums. It asks for
a jointly measurable family, and `IsOs` gives only a.e.-measurability, so each variable is replaced
by a measurable version (finitely many a.e. equalities).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set

namespace CurvatureVariance.Paper

/-- **[AKM, Lemma A.4] for finite sums, `s ≥ 1`** (equation `eq:sum`): the scales add, with
constant `1`, for signed variables. -/
theorem isOs_sum_of_one_le {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : ℝ} (hs : 1 ≤ s) (T : Finset ι) (hT : T.Nonempty)
    (θ : ι → ℝ) (hθ : ∀ i ∈ T, 0 < θ i) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ T, CurvatureVariance.IsOs P s (θ i) (X i)) :
    CurvatureVariance.IsOs P s (∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω) := by
  classical
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  obtain ⟨C, -, hC, h⟩ := CurvatureVariance.exists_isOs_integral hs0
  rw [hC hs] at h
  -- measurable positive parts
  let Y : T → Ω → ℝ := fun i ω => max ((hX i.1 i.2).1.mk (X i.1) ω) 0
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    ((hX i.1 i.2).1.measurable_mk).max measurable_const
  have hYae : ∀ i : T, X i.1 ≤ᵐ[P] Y i := fun i => by
    filter_upwards [(hX i.1 i.2).1.ae_eq_mk] with ω hω
    simp only [Y, ← hω]
    exact le_max_left _ _
  have hYos : ∀ i : T, CurvatureVariance.IsOs P s (θ i.1) (Y i) := by
    intro i
    have h1 := (hX i.1 i.2).congr (hX i.1 i.2).1.ae_eq_mk
    refine ⟨(hYm i).aemeasurable, ?_⟩
    simpa only [Y, max_assoc, max_self] using h1.2
  let _ : MeasurableSpace T := ⊤
  have : MeasurableSingletonClass T := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hun : Measurable (Function.uncurry Y) :=
    measurable_from_prod_countable_right (fun i => hYm i)
  have hθm : Measurable (fun i : T => θ i.1) := measurable_of_countable _
  have hθi : Integrable (fun i : T => θ i.1) (Measure.count : Measure T) :=
    Integrable.of_finite
  have key := h P (Measure.count : Measure T) (fun i : T => θ i.1) (fun i => hθ i.1 i.2) hθm hθi Y
    hun (fun i ω => le_max_right _ _) hYos
  have e1 : ∫ i : T, θ i.1 ∂(Measure.count : Measure T) = ∑ i ∈ T, θ i := by
    rw [integral_fintype hθi]
    simpa using Finset.sum_coe_sort T θ
  have e2 : ∀ ω, ∫ i : T, Y i ω ∂(Measure.count : Measure T) = ∑ i : T, Y i ω := by
    intro ω
    rw [integral_fintype Integrable.of_finite]
    simp
  simp only [e1, e2, one_mul] at key
  refine key.mono hs0.le (Finset.sum_pos hθ hT) ?_ ?_
  · exact Finset.aemeasurable_fun_sum T fun i hi => (hX i hi).1
  · have : ∀ᵐ ω ∂P, ∀ i : T, X i.1 ω ≤ Y i ω := ae_all_iff.2 hYae
    filter_upwards [this] with ω hω
    calc ∑ i ∈ T, X i ω = ∑ i : T, X i.1 ω := (Finset.sum_coe_sort T (fun i => X i ω)).symm
      _ ≤ ∑ i : T, Y i ω := Finset.sum_le_sum fun i _ => hω i

end CurvatureVariance.Paper
