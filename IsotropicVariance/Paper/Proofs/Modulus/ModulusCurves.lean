/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.Curves
public import IsotropicVariance.Paper.Proofs.Localization.Frame
public import IsotropicVariance.Infra.Measurability.SlabTime
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Curves cut at two hyperplanes (the proof of Lemma `lem:modulus`)

`exists_hits`: a continuous coordinate going from `0` to `w` along the curve takes the values
`ℓ₁ ≤ ℓ₂` at times `t₁ ≤ t₂` (intermediate values; no first or last visit is needed).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace IsotropicVariance.Paper.Proofs.Modulus

open Proofs.Localization

variable {m : ℕ}

/-- **Hits of two levels**: a continuous coordinate going from `0` to `w` along a curve takes the
values `ℓ₁ ≤ ℓ₂` in `[0, w]` at times `t₁ ≤ t₂`. -/
theorem exists_hits (γ : RectifiableCurve (Pt m)) {f : Pt m → ℝ} (hf : Continuous f) {w ℓ₁ ℓ₂ : ℝ}
    (h0 : f (γ.toFun 0) = 0) (h1 : f (γ.toFun 1) = w) (hℓ₁ : 0 ≤ ℓ₁) (hℓ : ℓ₁ ≤ ℓ₂)
    (hℓ₂ : ℓ₂ ≤ w) :
    ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ t₂ ∧ t₂ ≤ 1 ∧ f (γ.toFun t₁) = ℓ₁ ∧ f (γ.toFun t₂) = ℓ₂ := by
  have hc : ContinuousOn (fun t => f (γ.toFun t)) (Icc 0 1) := hf.comp_continuousOn γ.continuousOn
  obtain ⟨t₁, ⟨ht₁0, ht₁1⟩, hft₁⟩ := intermediate_value_Icc zero_le_one hc
    (show ℓ₁ ∈ Icc (f (γ.toFun 0)) (f (γ.toFun 1)) by rw [h0, h1]; exact ⟨hℓ₁, hℓ.trans hℓ₂⟩)
  simp only at hft₁
  obtain ⟨t₂, ⟨ht₂0, ht₂1⟩, hft₂⟩ := intermediate_value_Icc ht₁1
    (hc.mono (Icc_subset_Icc ht₁0 le_rfl))
    (show ℓ₂ ∈ Icc (f (γ.toFun t₁)) (f (γ.toFun 1)) by rw [hft₁, h1]; exact ⟨hℓ, hℓ₂⟩)
  exact ⟨t₁, t₂, ht₁0, ht₂0, ht₂1, hft₁, by simpa using hft₂⟩

end IsotropicVariance.Paper.Proofs.Modulus
