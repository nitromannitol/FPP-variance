/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.ProfileBounds
public import IsotropicVariance.Paper.Proofs.Profiles.Asymptotics
public import IsotropicVariance.Paper.Contracts.Profiles
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:parent`: the estimate at one length

The proof of Lemma `lem:parent`: for `ℓ` comparable to `N`, fix `M`, depending
only on the upper multiple and the constant `C` of equation `eq:rowenergy`, with
`s = ℓ/M ≤ N/4` and `C M^{−2/5} ≤ 1/200`. The column comparison (equation `eq:columns`), which
holds on every outcome, and equation `eq:rowenergy` give
`|T_ℓ − ℓ| ≤ C M Q_s + O_1(C Q_s + C M log²(2+N))`; since `Q_s ≤ M^{−2/5} Q_ℓ` and the
logarithmic term is at most `Q_ℓ/200` for `N` large, the sum rule gives equation `eq:parent`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os

variable {m : ℕ}

/-- The number of slabs of the proof of Lemma `lem:parent`: `M ≥ 4 c₂` and `C M^{−2/5} ≤ 1/200`. -/
noncomputable def parentSlabs (c₂ C : ℝ) : ℕ :=
  max ⌈4 * c₂⌉₊ ⌈(200 * C) ^ (5 / 2 : ℝ)⌉₊ + 1

lemma one_le_parentSlabs (c₂ C : ℝ) : 1 ≤ parentSlabs c₂ C := Nat.le_add_left 1 _

lemma le_parentSlabs (c₂ C : ℝ) : 4 * c₂ ≤ parentSlabs c₂ C := by
  unfold parentSlabs
  push_cast
  have := Nat.le_ceil (4 * c₂)
  have h2 : (⌈4 * c₂⌉₊ : ℝ) ≤ max (⌈4 * c₂⌉₊ : ℝ) ⌈(200 * C) ^ (5 / 2 : ℝ)⌉₊ := le_max_left _ _
  linarith

lemma rpow_parentSlabs (c₂ : ℝ) {C : ℝ} (hC : 0 < C) :
    C * (parentSlabs c₂ C : ℝ)⁻¹ ^ (2 / 5 : ℝ) ≤ 1 / 200 := by
  have hM : (200 * C) ^ (5 / 2 : ℝ) ≤ parentSlabs c₂ C := by
    unfold parentSlabs
    push_cast
    have := Nat.le_ceil ((200 * C) ^ (5 / 2 : ℝ))
    have h2 : (⌈(200 * C) ^ (5 / 2 : ℝ)⌉₊ : ℝ) ≤
        max (⌈4 * c₂⌉₊ : ℝ) ⌈(200 * C) ^ (5 / 2 : ℝ)⌉₊ := le_max_right _ _
    linarith
  have hMpos : (0 : ℝ) < parentSlabs c₂ C := by
    have := one_le_parentSlabs c₂ C; exact_mod_cast this
  have h1 : 200 * C ≤ (parentSlabs c₂ C : ℝ) ^ (2 / 5 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hM (by norm_num : (0 : ℝ) ≤ 2 / 5)
    rwa [← Real.rpow_mul (by positivity), show (5 / 2 : ℝ) * (2 / 5) = 1 by norm_num,
      Real.rpow_one] at this
  rw [Real.inv_rpow hMpos.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  linarith

/-- The estimate of the proof of Lemma `lem:parent` for one length `ℓ = M s`: from equation
`eq:rowenergy` at `s` and the column comparison `0 ≤ F − T_ℓ ≤ C M S²`. -/
lemma parent_core {X : Setting m} {Fv T E G : X.Ω → ℝ} {ℓ c c' θ₁ θ₂ : ℝ}
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (HR : IsOs X.P 1 θ₁ fun ω => |Fv ω - ℓ| + E ω - c)
    (hE : ∀ ω, 0 ≤ E ω) (HS : IsOs X.P 1 θ₂ G) (hT : AEMeasurable T X.P)
    (hcol : ∀ ω, 0 ≤ Fv ω - T ω ∧ Fv ω - T ω ≤ G ω) (hc : c ≤ c') {η : ℝ}
    (hη : θ₁ + θ₂ ≤ η) :
    IsOs X.P 1 η fun ω => |T ω - ℓ| - c' := by
  refine (IsOs.mono (isOs_add HR HS hθ₁ hθ₂) zero_le_one (by positivity)
    ((continuous_abs.measurable.comp_aemeasurable (hT.sub_const _)).sub_const _)
    (ae_of_all _ fun ω => ?_)).mono_scale zero_le_one (by positivity) hη
  obtain ⟨h1, h2⟩ := hcol ω
  have := abs_sub_le (T ω) (Fv ω) ℓ
  rw [abs_sub_comm (T ω) (Fv ω), abs_of_nonneg h1] at this
  simp only [Function.comp_apply]
  linarith [hE ω]

end IsotropicVariance.Paper.Proofs.Profiles

