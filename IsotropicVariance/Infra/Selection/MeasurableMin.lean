/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Selection.CompactMin
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Measurable compact minima and measurable finite-constraint minima -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace IsotropicVariance.Infra.Selection
open CompactFamily
variable {K Ω : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
  [SeparableSpace K] [MeasurableSpace Ω]

/-- Taking a continuous compact minimum preserves measurability in an arbitrary parameter. -/
lemma measurable_minValue {f : Ω → K → ℝ}
    (hc : ∀ ω, Continuous (f ω)) (hm : ∀ x, Measurable (fun ω => f ω x)) :
    Measurable (fun ω => (whole K).minValue (f ω)) := by
  have h : Measurable (fun ω => ⨅ x : K, (f ω x : EReal)) :=
    by
      convert (measurable_iInf_of_upperSemicontinuous
        (fun x => (hm x).coe_real_ereal)
        (fun ω => (continuous_coe_real_ereal.comp (hc ω)).upperSemicontinuous)) using 1
      funext ω
      exact (iInf_apply (f := fun x : K => fun ω : Ω => (f ω x : EReal)) (a := ω)).symm
  have heq (ω : Ω) : (⨅ x : K, (f ω x : EReal)) = ((whole K).minValue (f ω) : EReal) := by
    apply le_antisymm
    · rw [(whole K).minValue_eq _ (hc ω)]
      exact iInf_le _ _
    · exact le_iInf fun x => EReal.coe_le_coe_iff.mpr
        ((whole K).minValue_le _ (hc ω) (mem_univ x))
  have := h.ereal_toReal
  simpa only [heq, EReal.toReal_coe] using this

/-- Minima over a measurable zero constraint are measurable, by integer penalties. -/
lemma measurable_minValue_zero {g f : Ω → K → ℝ}
    (hg : ∀ ω, Continuous (g ω)) (hf : ∀ ω, Continuous (f ω))
    (hgm : ∀ x, Measurable (fun ω => g ω x))
    (hfm : ∀ x, Measurable (fun ω => f ω x))
    (hpos : ∀ ω x, 0 ≤ g ω x) (S : Ω → CompactFamily K)
    (hS : ∀ ω, (S ω).carrier = {x | g ω x = 0}) :
    Measurable (fun ω => (S ω).minValue (f ω)) := by
  have heq : (fun ω => (S ω).minValue (f ω)) =
      fun ω => ⨆ n : ℕ, (whole K).minValue (fun x => f ω x + n * g ω x) := by
    funext ω
    exact (S ω).minValue_zero_penalty (g ω) (f ω) (hg ω) (hf ω) (hpos ω) (hS ω)
  rw [heq]
  apply Measurable.iSup
  intro n
  exact measurable_minValue (fun ω => (hf ω).add (continuous_const.mul (hg ω)))
    (fun x => (hfm x).add (measurable_const.mul (hgm x)))

end IsotropicVariance.Infra.Selection
