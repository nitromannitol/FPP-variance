/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.ProfileResponse
public import IsotropicVariance.Paper.Proofs.Responses.OsMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniform moments of a normalized block response

The profile estimate and the two marginal laws give the response moments used for Lemma
`lem:blocks`, uniformly in the replaced block and its coupling.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

/-- Every fixed response moment is uniform in the block, using only its two correct marginals. -/
theorem eLpNorm_blockGain_div_le {X : Setting m} {b : ℝ} (hb : X.IsUpperBound b)
    {s W Qn C p : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) (hQ : 0 < Qn) (hC : 0 < C)
    (hp : 1 ≤ p) (i : ℕ) (j k : Fin m → ℤ)
    (hprof : Cited.IsOs X.P 1 (C * Qn) (slabProfile X b (Profiles.gridPair s W i j k)))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (ho : MeasurePreserving old P' X.P) (hn : MeasurePreserving new P' X.P) :
    eLpNorm (fun ω => ENNReal.ofReal (X.blockGain b s W i j k (old ω) (new ω) / Qn))
      (ENNReal.ofReal p) P' ≤ ENNReal.ofReal (2 * osMomentConst p * C) := by
  have hM := osMomentConst_pos p
  let f : X.Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (slabProfile X b (Profiles.gridPair s W i j k) ω)
  have hfm : AEMeasurable f X.P := hprof.1.ennreal_ofReal
  have hnorm : eLpNorm f (ENNReal.ofReal p) X.P ≤
      ENNReal.ofReal (osMomentConst p * (C * Qn)) :=
    eLpNorm_ofReal_le_of_isOs (by linarith) (mul_pos hC hQ) hprof
      (slabProfile_nonneg X b _)
  have hnew : eLpNorm (f ∘ new) (ENNReal.ofReal p) P' = eLpNorm f (ENNReal.ofReal p) X.P :=
    eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable hn
  have hold : eLpNorm (f ∘ old) (ENNReal.ofReal p) P' = eLpNorm f (ENNReal.ofReal p) X.P :=
    eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable ho
  have hgm : AEMeasurable (fun ω => ENNReal.ofReal
      (X.blockGain b s W i j k (old ω) (new ω) / Qn)) P' :=
    ((aemeasurable_blockGain hb hs hW i j k ho hn).div_const Qn).ennreal_ofReal
  have hpt : ∀ ω, ENNReal.ofReal (X.blockGain b s W i j k (old ω) (new ω) / Qn) ≤
      ENNReal.ofReal Qn⁻¹ * ((f ∘ old + f ∘ new) ω) := by
    intro ω
    dsimp only [f, Pi.add_apply, Function.comp_apply]
    rw [← ENNReal.ofReal_add (slabProfile_nonneg X b _ _) (slabProfile_nonneg X b _ _),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hQ.le)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (blockGain_le_slabProfiles X hb hs hW i j k _ _)
      (inv_nonneg.mpr hQ.le)
  calc
    _ ≤ ENNReal.ofReal Qn⁻¹ * eLpNorm (f ∘ old + f ∘ new) (ENNReal.ofReal p) P' :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ hgm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by simpa only [enorm_eq_self] using hpt ω)
    _ ≤ ENNReal.ofReal Qn⁻¹ * (eLpNorm (f ∘ old) (ENNReal.ofReal p) P' +
        eLpNorm (f ∘ new) (ENNReal.ofReal p) P') :=
      mul_le_mul' le_rfl (eLpNorm_add_le (by simpa using ENNReal.ofReal_le_ofReal hp))
    _ ≤ ENNReal.ofReal Qn⁻¹ * (ENNReal.ofReal (osMomentConst p * (C * Qn)) +
        ENNReal.ofReal (osMomentConst p * (C * Qn))) := by
      rw [hold, hnew]
      exact mul_le_mul' le_rfl (add_le_add hnorm hnorm)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring

end IsotropicVariance.Paper.Proofs.Responses
