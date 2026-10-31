/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.SlabVersion
public import IsotropicVariance.Infra.Noise.Resampling

/-! # Joint locality and simultaneous agreement under regional resampling

The new joint-locality field is essential: it permits a countable code for the
whole density field on a region. Retaining that code gives agreement at every
point on one full-measure event, rather than pointwise almost-sure agreement.
-/

@[expose] public section
open MeasureTheory Set Filter
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra
open IsotropicVariance.Infra.Slab

/-- Resampling an arbitrary region retains the entire density field determined
by any open subset of its complement. This applies to half-open grid cells. -/
theorem resampleLaw_ae_density_eq_on_open {m : ℕ} (X : Setting m)
    {K U : Set (Pt m)} (hU : IsOpen U) (hUK : U ⊆ Kᶜ) :
    ∀ᵐ p ∂Noise.resampleLaw X.toNoiseModel K, ∀ x : Pt m,
      Metric.closedBall x 1 ⊆ U → X.ρ p.1 x = X.ρ p.2 x := by
  obtain ⟨Φ, hΦ, h, _hh, hfh⟩ := exists_factor_of_measurable_prod
    (X.determined_joint U hU)
  have hΦ' : Measurable[X.info Kᶜ] Φ := hΦ.mono (X.info_mono hUK) le_rfl
  have hEq := Noise.resampleLaw_ae_variable_eq X.toNoiseModel K hΦ'
  filter_upwards [hEq] with p hp x hx
  have hOld := hfh p.1 (⟨x, hx⟩ : {x : Pt m // Metric.closedBall x 1 ⊆ U})
  have hNew := hfh p.2 (⟨x, hx⟩ : {x : Pt m // Metric.closedBall x 1 ⊆ U})
  exact hOld.trans ((congrArg (fun z => h (z, ⟨x, hx⟩)) hp).trans hNew.symm)

end IsotropicVariance.Paper.Proofs.Classical
