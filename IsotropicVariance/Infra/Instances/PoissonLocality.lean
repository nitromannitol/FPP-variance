/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Model

/-!
# Exact Poisson locality for the setting interface

Borel restriction is measurable for regional configuration information. The density's
pointwise dependence therefore gives both the pointwise and joint locality fields, including
the open-region `Setting.determined_joint` field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace IsotropicVariance.Infra.Instances

/-- Restriction to a Borel region is measurable using only the Poisson information in that
region. -/
theorem measurable_poisson_restrict {m : ℕ} {lam : ℝ≥0} {S : Set (Pt m)}
    (hS : MeasurableSet S) :
    Measurable[Paper.Noise.info (Paper.Noise.poisson lam) S]
      (fun μ : Measure (Pt m) => μ.restrict S) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  have heq : (fun μ : Measure (Pt m) => μ.restrict S B) = (fun μ => μ (B ∩ S)) := by
    funext μ
    exact Measure.restrict_apply hB
  rw [heq]
  apply Measurable.of_comap_le
  exact le_iSup_of_le (B ∩ S) (le_iSup_of_le (hB.inter hS)
    (le_iSup_of_le inter_subset_right le_rfl))

/-- Exact pointwise locality permits replacing a Poisson configuration by its regional
restriction. -/
theorem poisson_density_restrict_eq {m : ℕ} {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ)
    (μ : Measure (Pt m)) (x : Pt m) {S : Set (Pt m)}
    (hball : Metric.closedBall x 1 ⊆ S) : ρ μ x = ρ (μ.restrict S) x := by
  apply hρ.determined x μ (μ.restrict S)
  exact (Measure.restrict_restrict_of_subset hball).symm

/-- The pointwise locality field for the Poisson setting, on configuration space. -/
theorem measurable_poisson_density {m : ℕ} {lam : ℝ≥0}
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) (x : Pt m) :
    Measurable[Paper.Noise.info (Paper.Noise.poisson lam) (Metric.closedBall x 1)]
      (fun μ => ρ μ x) := by
  have hmap : Measurable[Paper.Noise.info (Paper.Noise.poisson lam) (Metric.closedBall x 1)]
      (fun μ : Measure (Pt m) => (μ.restrict (Metric.closedBall x 1), x)) :=
    (measurable_poisson_restrict (lam := lam) Metric.isClosed_closedBall.measurableSet).prodMk measurable_const
  have hm : Measurable[Paper.Noise.info (Paper.Noise.poisson lam) (Metric.closedBall x 1)]
      (fun μ : Measure (Pt m) => ρ (μ.restrict (Metric.closedBall x 1)) x) := hρ.measurable.comp hmap
  have heq : (fun μ : Measure (Pt m) => ρ (μ.restrict (Metric.closedBall x 1)) x) =
      (fun μ => ρ μ x) := by
    funext μ
    exact (poisson_density_restrict_eq hρ μ x Subset.rfl).symm
  rwa [heq] at hm

/-- Joint locality over an open region, with exactly the carrier of `Setting.determined_joint`. -/
theorem measurable_poisson_density_joint {m : ℕ} {lam : ℝ≥0}
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ)
    (U : Set (Pt m)) (hU : IsOpen U) :
    Measurable[(Paper.Noise.info (Paper.Noise.poisson lam) U).prod inferInstance]
      (fun p : Measure (Pt m) × {x : Pt m // Metric.closedBall x 1 ⊆ U} => ρ p.1 p.2) := by
  have hmap : Measurable[(Paper.Noise.info (Paper.Noise.poisson lam) U).prod inferInstance]
      (fun p : Measure (Pt m) × {x : Pt m // Metric.closedBall x 1 ⊆ U} =>
        (p.1.restrict U, p.2.val)) :=
    (measurable_poisson_restrict (lam := lam) hU.measurableSet).prodMap measurable_subtype_coe
  have hm : Measurable[(Paper.Noise.info (Paper.Noise.poisson lam) U).prod inferInstance]
      (fun p : Measure (Pt m) × {x : Pt m // Metric.closedBall x 1 ⊆ U} => ρ (p.1.restrict U) p.2.val) :=
    hρ.measurable.comp hmap
  have heq : (fun p : Measure (Pt m) × {x : Pt m // Metric.closedBall x 1 ⊆ U} =>
      ρ (p.1.restrict U) p.2.val) = (fun p => ρ p.1 p.2.val) := by
    funext p
    exact (poisson_density_restrict_eq hρ p.1 p.2.val p.2.property).symm
  rwa [heq] at hm

end IsotropicVariance.Infra.Instances
