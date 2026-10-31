/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonCarrier
public import IsotropicVariance.Infra.Instances.PoissonPointConfigurations
public import IsotropicVariance.Infra.Instances.PoissonModel

/-! # Exact measurable rigid-motion actions on canonical Poisson configurations -/

@[expose] public section
open MeasureTheory
namespace IsotropicVariance.Infra.Instances
variable {m : ℕ}

/-- A physical rigid motion in the Euclidean coordinates used for the cube partition. -/
noncomputable def poissonCoordinateMotion (g : Pt m ≃ᵃⁱ[ℝ] Pt m) :
    Poisson.E (Module.finrank ℝ (Pt m)) ≃ᵃⁱ[ℝ] Poisson.E (Module.finrank ℝ (Pt m)) :=
  ((poissonCoordinates m).symm.toAffineIsometryEquiv.trans g).trans
    (poissonCoordinates m).toAffineIsometryEquiv

/-- Exact pushforward stays in the canonical carrier, with no exceptional outcomes. -/
theorem exists_poissonCarrier_pushforward (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (c : PoissonCarrier m) :
    ∃ c' : PoissonCarrier m, poissonCarrierDecode c' = (poissonCarrierDecode c).map g := by
  let h := poissonCoordinateMotion g
  obtain ⟨c', hc'⟩ := exists_poissonConfiguration_map c h.continuous.measurable
    (fun _ hb => h.isometry.antilipschitzWith.isBounded_preimage hb)
  refine ⟨c', ?_⟩
  rw [poissonCarrierDecode, hc', Measure.map_map (poissonCoordinates m).symm.continuous.measurable
    h.continuous.measurable, poissonCarrierDecode,
    Measure.map_map g.continuous.measurable (poissonCoordinates m).symm.continuous.measurable]
  congr 1
  funext x
  simp [h, poissonCoordinateMotion]

/-- The unique canonical representation of the pushforward configuration. -/
noncomputable def poissonCarrierAction (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (c : PoissonCarrier m) :
    PoissonCarrier m := Classical.choose (exists_poissonCarrier_pushforward g c)

@[simp] theorem poissonCarrierDecode_action (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (c : PoissonCarrier m) :
    poissonCarrierDecode (poissonCarrierAction g c) = (poissonCarrierDecode c).map g :=
  Classical.choose_spec (exists_poissonCarrier_pushforward g c)

end IsotropicVariance.Infra.Instances
