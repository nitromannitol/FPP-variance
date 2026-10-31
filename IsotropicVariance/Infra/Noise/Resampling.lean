/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Model
public import IsotropicVariance.Infra.Resampling.Sigma

/-!
# Resampling on the paper's noise interface

`Paper.NoiseModel` is the sole noise interface. The coupled noise space is `N.Ω × N.Ω`;
both draws have law `N.P`, their pair is exchangeable, and the retained outside information
agrees almost surely. Conditioning on a block label as well retains that label.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
namespace IsotropicVariance.Infra.Noise
open IsotropicVariance.Paper
open IsotropicVariance.Infra.Resampling
universe u
variable {m : ℕ} (N : NoiseModel.{u} m)
local instance : Nonempty N.Ω := nonempty_of_isProbabilityMeasure N.P

/-- Resample in `S` by two independent draws given the information outside `S`. -/
noncomputable def resampleLaw (S : Set (Pt m)) : Measure (N.Ω × N.Ω) :=
  sigmaPairLaw (N.info Sᶜ) N.P

instance (S : Set (Pt m)) : IsProbabilityMeasure (resampleLaw N S) := by
  unfold resampleLaw
  infer_instance

/-- Old noise retains its original distribution. -/
theorem resampleLaw_old (S : Set (Pt m)) :
    MeasurePreserving Prod.fst (resampleLaw N S) N.P :=
  ⟨measurable_fst, sigmaPairLaw_map_fst _ _ (N.info_le _)⟩

/-- New noise retains its original distribution. -/
theorem resampleLaw_new (S : Set (Pt m)) :
    MeasurePreserving Prod.snd (resampleLaw N S) N.P :=
  ⟨measurable_snd, sigmaPairLaw_map_snd _ _ (N.info_le _)⟩

/-- A standard Borel code for the complete outside restriction is preserved on one
full-measure event. -/
theorem resampleLaw_ae_variable_eq (S : Set (Pt m)) {Z : Type*}
    [MeasurableSpace Z] [StandardBorelSpace Z] {F : N.Ω → Z}
    (hF : Measurable[N.info Sᶜ] F) :
    ∀ᵐ p ∂resampleLaw N S, F p.1 = F p.2 :=
  sigmaPairLaw_ae_variable_eq _ _ (N.info_le _) hF

end IsotropicVariance.Infra.Noise
