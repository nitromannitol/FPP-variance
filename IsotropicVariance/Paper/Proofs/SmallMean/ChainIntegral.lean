/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# From the chain bound to an inequality of means

The end of the third paragraph of the proof of Lemma `lem:smallmean`.

`le_integral_add_of_ae`: integrating `L ≤ F + c Sup` with `F ≤ T + C S²` gives
`L ≤ E T + C B₂ + c B₃` from `E S² ≤ B₂` and `E Sup ≤ B₃`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.Paper.Proofs.SmallMean

variable {m : ℕ}

/-- **Integrating the chain bound.** -/
theorem le_integral_add_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {L c C B₂ B₃ : ℝ} {F T S : Ω → ℝ} {Sup : Ω → ℝ≥0∞}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (h : ∀ᵐ ω ∂P, ENNReal.ofReal L ≤ ENNReal.ofReal (F ω) + ENNReal.ofReal c * Sup ω)
    (hF : ∀ ω, F ω ≤ T ω + C * S ω ^ 2) (hT : Integrable T P) (hT0 : ∀ ω, 0 ≤ T ω)
    (hS : AEMeasurable S P) (hS2 : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂P ≤ ENNReal.ofReal B₂)
    (hSup : ∫⁻ ω, Sup ω ∂P ≤ ENNReal.ofReal B₃) :
    L ≤ ∫ ω, T ω ∂P + C * B₂ + c * B₃ := by
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal L ≤
      ENNReal.ofReal (T ω) + (ENNReal.ofReal C * ENNReal.ofReal (S ω ^ 2) +
        ENNReal.ofReal c * Sup ω) := by
    filter_upwards [h] with ω hω
    refine hω.trans ?_
    rw [← add_assoc]
    gcongr
    calc ENNReal.ofReal (F ω) ≤ ENNReal.ofReal (T ω + C * S ω ^ 2) :=
          ENNReal.ofReal_le_ofReal (hF ω)
      _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal (C * S ω ^ 2) := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (T ω) + ENNReal.ofReal C * ENNReal.ofReal (S ω ^ 2) := by
          rw [ENNReal.ofReal_mul hC]
  have hint : ENNReal.ofReal L ≤ ENNReal.ofReal (∫ ω, T ω ∂P) +
      (ENNReal.ofReal C * ENNReal.ofReal B₂ + ENNReal.ofReal c * ENNReal.ofReal B₃) := by
    calc ENNReal.ofReal L = ∫⁻ _ω, ENNReal.ofReal L ∂P := by simp
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (T ω) + (ENNReal.ofReal C * ENNReal.ofReal (S ω ^ 2) +
            ENNReal.ofReal c * Sup ω)) ∂P := lintegral_mono_ae hpt
      _ = ∫⁻ ω, ENNReal.ofReal (T ω) ∂P + (ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂P +
            ENNReal.ofReal c * ∫⁻ ω, Sup ω ∂P) := by
          rw [lintegral_add_left' hT.aemeasurable.ennreal_ofReal,
            lintegral_add_left' ((hS.pow_const 2).ennreal_ofReal.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (∫ ω, T ω ∂P) + (ENNReal.ofReal C * ENNReal.ofReal B₂ +
            ENNReal.ofReal c * ENNReal.ofReal B₃) := by
          rw [ofReal_integral_eq_lintegral_ofReal hT (Eventually.of_forall hT0)]
          gcongr
  have hrhs : ENNReal.ofReal (∫ ω, T ω ∂P) + (ENNReal.ofReal C * ENNReal.ofReal B₂ +
      ENNReal.ofReal c * ENNReal.ofReal B₃) =
      ENNReal.ofReal (∫ ω, T ω ∂P + C * B₂ + c * B₃) := by
    have hT' : 0 ≤ ∫ ω, T ω ∂P := integral_nonneg hT0
    rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hc,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add hT' (by positivity), add_assoc]
  rw [hrhs] at hint
  exact (ENNReal.ofReal_le_ofReal_iff (by
    have hT' : 0 ≤ ∫ ω, T ω ∂P := integral_nonneg hT0
    positivity)).1 hint

end IsotropicVariance.Paper.Proofs.SmallMean
