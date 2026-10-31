/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.TimeConstant.Isometry
public import IsotropicVariance.Paper.Defs.Model
public import IsotropicVariance.Infra.Measurability.PassageVersion

/-! # Passage bounds over the paper's setting

The infrastructure passage time `Infra.Measurability.passageTime` and the passage time
`IsotropicVariance.passageTime` are infima over the same curves
`IsotropicVariance.RectifiableCurve`, so they agree by unfolding.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace IsotropicVariance.Infra.TimeConstant
open Paper

/-- The infrastructure rectifiable infimum `passage` is exactly the passage time
`IsotropicVariance.passageTime`. -/
theorem passage_eq_surface {m : ℕ} (σ : Pt m → ℝ) (u v : Pt m) :
    passage σ u v = IsotropicVariance.passageTime σ u v := by
  unfold passage IsotropicVariance.passageTime
  congr 1

/-- Uniform ellipticity gives deterministic bounds for every outcome and every
pair of endpoints in the paper's setting. -/
theorem setting_passTime_bounds {m : ℕ} (X : Setting m) :
    ∃ a b : ℝ, 0 < a ∧ ∀ ω u v,
      a * dist u v ≤ X.passTime ω u v ∧ X.passTime ω u v ≤ b * dist u v := by
  obtain ⟨a, b, ha, hab⟩ := X.bounds
  refine ⟨a, b, ha, fun ω u v => ?_⟩
  simpa only [Setting.passTime, ← passage_eq_surface] using passage_bounds ha.le (hab ω) u v

/-- The literal passage random variable is a.e. measurable. -/
theorem aestronglyMeasurable_passTime {m : ℕ} (X : Setting m) (u v : Pt m) :
    AEStronglyMeasurable (fun ω => X.passTime ω u v) X.P := by
  have hm : Measurable (fun p : X.Ω × Pt m => ENNReal.ofReal (X.ρ p.1 p.2)) :=
    X.measurable_ρ.ennreal_ofReal
  have hh := (Measurability.nullMeasurable_passageTime X.P hm u v).aemeasurable.ennreal_toReal
  simpa only [Setting.passTime, ← passage_eq_surface, passage] using hh.aestronglyMeasurable

/-- Bounded densities make every fixed-endpoint passage time integrable. -/
theorem integrable_passTime {m : ℕ} (X : Setting m) (u v : Pt m) :
    Integrable (fun ω => X.passTime ω u v) X.P := by
  obtain ⟨a, b, ha, hab⟩ := setting_passTime_bounds X
  apply Integrable.mono' (integrable_const (b * dist u v)) (aestronglyMeasurable_passTime X u v)
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg ((mul_nonneg ha.le dist_nonneg).trans (hab ω u v).1)]
  exact (hab ω u v).2

/-- Endpoint Lipschitz estimates for a setting, with one deterministic constant. -/
theorem setting_passTime_endpoint_bound {m : ℕ} (X : Setting m) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ ω u v u' v',
      |X.passTime ω u v - X.passTime ω u' v'| ≤ b * (dist u u' + dist v v') := by
  obtain ⟨a, b, ha, hab⟩ := X.bounds
  obtain ⟨ω, _⟩ := (Filter.Eventually.of_forall (fun _ : X.Ω => True.intro) : ∀ᵐ _ω ∂X.P, True).exists
  have hb : 0 ≤ b := ha.le.trans ((hab ω 0).1.trans (hab ω 0).2)
  refine ⟨b, hb, fun ω u v u' v' => ?_⟩
  have hm : Measurable (X.ρ ω) := X.measurable_ρ.comp measurable_prodMk_left
  simpa only [Setting.passTime, ← passage_eq_surface] using
    abs_passage_sub_le hm hb (fun x => (hab ω x).2) u v u' v'

end IsotropicVariance.Infra.TimeConstant
