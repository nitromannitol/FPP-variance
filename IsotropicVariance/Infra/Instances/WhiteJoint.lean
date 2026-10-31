/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.WhiteLocalization
public import IsotropicVariance.Infra.Instances.LocalMeasurability
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Exact joint white-noise locality over open regions

A compact closed unit ball inside an open region has a smooth cutoff equal to one on all
nearby unit balls. Fixed-cutoff localizations give local measurable representatives, and
second countability patches them into the joint locality field `Setting.determined_joint`.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped Distributions

namespace IsotropicVariance.Infra.Instances

/-- A smooth cutoff in an open region is one on the closed unit balls of nearby centers. -/
theorem exists_local_unitBall_cutoff {m : ℕ} {U : Set (Pt m)} (hU : IsOpen U)
    (x : Pt m) (hx : closedBall x 1 ⊆ U) :
    ∃ χ : 𝓓((⊤ : Opens (Pt m)), ℝ), tsupport ⇑χ ⊆ U ∧
      ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x r, Set.EqOn χ 1 (closedBall y 1) := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall x 1).exists_cthickening_subset_open hU hx
  rw [cthickening_closedBall hδ.le (by norm_num : (0 : ℝ) ≤ 1) x] at hsub
  let b : ContDiffBump x :=
    { rIn := 1 + δ / 3
      rOut := 1 + 2 * δ / 3
      rIn_pos := by linarith only [hδ]
      rIn_lt_rOut := by linarith only [hδ] }
  let χ : 𝓓((⊤ : Opens (Pt m)), ℝ) :=
    ⟨b, b.contDiff, b.hasCompactSupport, by simp⟩
  refine ⟨χ, ?_, δ / 3, by positivity, ?_⟩
  · change tsupport ⇑b ⊆ U
    rw [b.tsupport_eq]
    exact (closedBall_subset_closedBall (by dsimp [b]; linarith only [hδ])).trans hsub
  · intro y hy z hz
    change b z = 1
    apply b.one_of_mem_closedBall
    have hyx : dist y x < δ / 3 := mem_ball.mp hy
    have hzy : dist z y ≤ 1 := mem_closedBall.mp hz
    have hzbound := dist_triangle z y x
    change dist z x ≤ 1 + δ / 3
    linarith only [hyx, hzy, hzbound]

/-- Exact joint locality of a white-noise density, with the open-set hypothesis and center
subtype of the field `Setting.determined_joint`. No noise-law assumption or almost-sure
modification is used. -/
theorem measurable_white_density_joint {m : ℕ}
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ)
    (U : Set (Pt m)) (hU : IsOpen U) :
    Measurable[(Paper.Noise.info Paper.Noise.white U).prod inferInstance]
      (fun p : WhiteNoiseConfig (Pt m) × {x : Pt m // closedBall x 1 ⊆ U} => ρ p.1 p.2) := by
  apply @measurable_of_locally_eq (WhiteNoiseConfig (Pt m)) {x : Pt m // closedBall x 1 ⊆ U}
    (Paper.Noise.info Paper.Noise.white U) _ _ _ _
  intro x
  obtain ⟨χ, hχ, r, hr, hplateau⟩ := exists_local_unitBall_cutoff hU x.val x.property
  refine ⟨Subtype.val ⁻¹' ball x.val r, isOpen_ball.preimage continuous_subtype_val,
    mem_ball_self hr, (fun p => ρ (localizeWhite χ p.1) p.2.val), ?_, ?_⟩
  · have hmap : Measurable[(Paper.Noise.info Paper.Noise.white U).prod inferInstance]
        (fun p : WhiteNoiseConfig (Pt m) × {x : Pt m // closedBall x 1 ⊆ U} =>
          (localizeWhite χ p.1, p.2.val)) :=
      (measurable_localizeWhite χ hχ).prodMap measurable_subtype_coe
    exact hρ.measurable.comp hmap
  · intro ν y hy
    exact white_density_localize_eq hρ χ ν y.val (hplateau y.val hy)

end IsotropicVariance.Infra.Instances
