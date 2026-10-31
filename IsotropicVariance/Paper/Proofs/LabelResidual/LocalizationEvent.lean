/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.RewardAtScale
import IsotropicVariance.Statements.Cited.IsOsMeasureGeLe
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A measurable exceptional event for the old localization radius

The localization radius is only almost everywhere measurable. We choose its measurable
version and pull back its upper tail through the actual old marginal. Outside that event,
every old 1-optimal curve between the two grid cubes lies in a tube of radius `RW`.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

open Responses

variable {m : ℕ}

/-- A measurable Gaussian-tail event controls every old curve for any correct old marginal. -/
theorem exists_localization_event {X : Setting m} {b s W Cr R : ℝ}
    (hb : X.IsUpperBound b) (hW : 0 < W) (hCr : 0 < Cr) (hR : 0 ≤ R)
    (i : ℕ) (j k : Fin m → ℤ)
    (hloc : Cited.IsOs X.P 2 Cr (pairLocalizationRadius X b s W i j k))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {old : Ω → X.Ω} (ho : MeasurePreserving old P X.P) :
    ∃ B : Set Ω, MeasurableSet B ∧
      P B ≤ ENNReal.ofReal (2 * Real.exp (-(R / Cr) ^ 2)) ∧
      ∀ᵐ ω ∂P, ω ∉ B →
        ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 (i+1) k,
          ∀ γ : RectifiableCurve (Pt m),
            IsOneOptimal ((chainSlab s 0 i).density b (X.ρ (old ω)))
              (chainSlab s 0 i).set u v γ → ∀ t ∈ Icc (0 : ℝ) 1,
                infDist (γ.toFun t) (segment ℝ u v) ≤ R * W := by
  let r : X.Ω → ℝ := hloc.1.mk (pairLocalizationRadius X b s W i j k)
  have hrm : Measurable r := hloc.1.measurable_mk
  have hrae : pairLocalizationRadius X b s W i j k =ᵐ[X.P] r := hloc.1.ae_eq_mk
  have hrOs : Cited.IsOs X.P 2 Cr r := Cited.IsOs.congr hloc hrae
  have hOldOs := Infra.Os.isOs_comp_measurePreserving ho hrOs
  let B : Set Ω := {ω | R < r (old ω)}
  refine ⟨B, measurableSet_lt measurable_const (hrm.comp ho.measurable), ?_, ?_⟩
  · have ht := Cited.IsOs.measure_ge_le (by norm_num : (0 : ℝ) < 2) hCr hOldOs _
      (div_nonneg hR hCr.le)
    have heq : Cr * (R / Cr) = R := by field_simp
    rw [heq, Real.rpow_two] at ht
    apply le_trans (measure_mono (s := B) (t := {ω | R ≤ (r ∘ old) ω}) ?_) ht
    intro ω h
    exact (show R < r (old ω) from h).le
  · filter_upwards [ho.quasiMeasurePreserving.ae hrae] with ω hω hωB u hu v hv γ hγ t ht
    have hrle : r (old ω) ≤ R := le_of_not_gt hωB
    let δ := Contracts.maxSegmentDeviation
      ((Profiles.gridPair s W i j k).slab.density b (X.ρ (old ω)))
      (Profiles.gridPair s W i j k).slab.set (Profiles.gridPair s W i j k).first
        (Profiles.gridPair s W i j k).second
    have hδ : infDist (γ.toFun t) (segment ℝ u v) ≤ δ :=
      le_maxSegmentDeviation_slab X hb _
        (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_first _ hW.le)).isBounded
        (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_second _ hW.le)).isBounded
        (old ω) (Profiles.gridCube_subset_first s W hW.le i j k hu)
        (Profiles.gridCube_subset_second s W hW.le i j k hv)
        (by simpa only [Profiles.gridPair_slab_density, Profiles.gridPair_slab_set] using hγ) ht
    change 1 + W⁻¹ * δ = r (old ω) at hω
    have hδ' : δ ≤ W * R := by
      have hmul := mul_le_mul_of_nonneg_left (hω.le.trans hrle) hW.le
      rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hW.ne', one_mul] at hmul
      linarith
    exact hδ.trans (hδ'.trans_eq (mul_comm W R))

end IsotropicVariance.Paper.Proofs.LabelResidual
