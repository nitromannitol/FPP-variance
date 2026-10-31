/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.LocalPair
public import IsotropicVariance.Paper.Contracts.Localization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:localization`: from the deviation bound to the Gaussian tail

* `isOs_two_of_le_sqrt`: `Φ ≤ α₀ + α₁ √(H₊/λ)` with `H ≤ O_1(θ)` gives `Φ ≤ O_2(·)` (the proof of
  Lemma `lem:localization`: "`Y² ≤ O_1(CnQ_n)`, that is, `Y ≤ O_2(C(nQ_n)^{1/2})`").
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Localization

open Contracts Cited Infra.Os

variable {m : ℕ}

/-- **From `O_1` to `O_2` through a square root.** -/
theorem isOs_two_of_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {H Φ : Ω → ℝ} {θ α₀ α₁ l : ℝ} (hθ : 0 < θ) (hl : 0 < l) (hH : IsOs P 1 θ H) (hΦ : AEMeasurable Φ P)
    (hle : ∀ ω, Φ ω ≤ α₀ + α₁ * Real.sqrt (max (H ω) 0 / l)) :
    IsOs P 2 (Real.sqrt ((2 * α₁ ^ 2 + 1) * (θ / l) + (2 * α₀ ^ 2 + 1) / Real.log 2)) Φ := by
  set c := 2 * α₁ ^ 2 + 1
  have hc : 0 < c := by positivity
  -- `H/l ≤ O_1(θ/l)`
  have h1 : IsOs P 1 (θ / l) (fun ω => H ω / l) := by
    have := (isOs_mul_iff (P := P) (s := 1) (θ := θ) (X := H) (a := 1 / l) (by positivity)).2 hH
    refine (this.congr (Filter.Eventually.of_forall fun ω => ?_)).mono_scale zero_le_one
      (by positivity) (le_of_eq (by ring))
    simp only; ring
  have h2 := Profiles.isOs_pos h1
  have h3 : IsOs P 1 (c * (θ / l)) (fun ω => c * max (H ω / l) 0) :=
    (isOs_mul_iff hc).2 h2
  have h4 := Profiles.isOs_add_const h3 (by positivity) (by positivity : 0 ≤ 2 * α₀ ^ 2)
  have h5 := isOs_sqrt (by positivity) h4
  refine h5.mono (by norm_num) (by positivity) hΦ (Filter.Eventually.of_forall fun ω => ?_)
  -- `Φ ≤ α₀ + α₁ √h ≤ √(2α₀² + 2α₁² h)`
  set h := max (H ω / l) 0
  have hh : max (H ω) 0 / l = h := by
    simp only [h]
    rcases le_total (H ω) 0 with hH0 | hH0
    · rw [max_eq_right hH0, zero_div, max_eq_right (div_nonpos_of_nonpos_of_nonneg hH0 hl.le)]
    · rw [max_eq_left hH0, max_eq_left (div_nonneg hH0 hl.le)]
  have hh0 : 0 ≤ h := le_max_right _ _
  have hZ0 : 0 ≤ c * h + 2 * α₀ ^ 2 := by positivity
  show Φ ω ≤ Real.sqrt (max (c * h + 2 * α₀ ^ 2) 0)
  rw [max_eq_left hZ0]
  refine (hle ω).trans ?_
  rw [hh]
  refine Real.le_sqrt_of_sq_le ?_
  have hs := Real.sq_sqrt hh0
  have hs0 := Real.sqrt_nonneg h
  nlinarith [sq_nonneg (α₀ - α₁ * Real.sqrt h)]

end IsotropicVariance.Paper.Proofs.Localization
