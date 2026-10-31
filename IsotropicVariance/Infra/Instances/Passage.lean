/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Classical
public import IsotropicVariance.Infra.TimeConstant.SettingBounds

/-!
# Measurability and exact passage identities for realizations

The noise-law predicates `Paper.Noise.IsLaw` give measurable configuration maps. The universal
passage-time theorem therefore applies to every source realization before an interface
carrier is chosen.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Instances

/-- Either noise-law predicate implies measurability of the configuration map. -/
theorem measurable_config_of_isLaw {m : ℕ} {k : Paper.Noise} {Ω : Type*} [MeasurableSpace Ω]
    {ν : Ω → k.Config m} {P : Measure Ω} (h : k.IsLaw ν P) : Measurable ν := by
  cases k with
  | white => exact h.1
  | poisson lam => exact h.2.1

/-- The passage times `T(u, v)` of every realization are a.e. measurable. -/
theorem realization_passageTime_aemeasurable {m : ℕ} (X : Paper.Realization m) (u v : Pt m) :
    AEMeasurable (fun ω => passageTime (X.ρ (X.config ω)) u v) X.P := by
  have hm : Measurable (fun p : X.Ω × Pt m => ENNReal.ofReal (X.ρ (X.config p.1) p.2)) :=
    (X.isLocalDensity.measurable.comp
      ((measurable_config_of_isLaw X.isLaw).prodMap measurable_id)).ennreal_ofReal
  have hh := (Measurability.nullMeasurable_passageTime X.P hm u v).aemeasurable.ennreal_toReal
  have heq : (fun ω => passageTime (X.ρ (X.config ω)) u v) = (fun ω =>
      (Measurability.passageTime (fun x => ENNReal.ofReal (X.ρ (X.config ω) x)) u v).toReal) := by
    funext ω
    rw [← TimeConstant.passage_eq_surface]
    rfl
  rw [heq]
  exact hh

end IsotropicVariance.Infra.Instances
