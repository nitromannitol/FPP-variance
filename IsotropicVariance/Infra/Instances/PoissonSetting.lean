/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonCanonicalLaw
public import IsotropicVariance.Infra.Instances.PoissonLocality

/-! # Local densities on the canonical Poisson noise model -/

@[expose] public section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace IsotropicVariance.Infra.Instances
variable {m : ℕ}

/-- The actual Poisson setting, including pointwise and joint regional density measurability. -/
noncomputable def poissonSetting (lam : ℝ≥0) (ρ : Measure (Pt m) → Pt m → ℝ)
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) : Paper.Setting m where
  toNoiseModel := poissonNoiseModel m lam
  ρ c x := ρ (poissonCarrierDecode c) x
  measurable_ρ := hρ.measurable.comp (measurable_poissonCarrierDecode.prodMap measurable_id)
  determined x := by
    have hd : @Measurable (PoissonCarrier m) (Measure (Pt m))
        ((Paper.Noise.info (Paper.Noise.poisson lam) (Metric.closedBall x 1)).comap poissonCarrierDecode)
        (Paper.Noise.info (Paper.Noise.poisson lam) (Metric.closedBall x 1)) poissonCarrierDecode :=
      Measurable.of_comap_le le_rfl
    exact (measurable_poisson_density hρ x).comp hd
  determined_joint U hU := by
    have hd : @Measurable (PoissonCarrier m) (Measure (Pt m))
        ((Paper.Noise.info (Paper.Noise.poisson lam) U).comap poissonCarrierDecode)
        (Paper.Noise.info (Paper.Noise.poisson lam) U) poissonCarrierDecode :=
      Measurable.of_comap_le le_rfl
    exact (measurable_poisson_density_joint hρ U hU).comp (hd.prodMap measurable_id)
  bounds := by
    obtain ⟨a, b, ha, hab⟩ := hρ.bounds
    exact ⟨a, b, ha, fun c x => hab (poissonCarrierDecode c) x⟩
  covariant g hg c x := hρ.covariant g hg (poissonCarrierDecode c)
    (poissonCarrierDecode (poissonCarrierAction g c)) (poissonCarrierDecode_action g c) x

end IsotropicVariance.Infra.Instances
