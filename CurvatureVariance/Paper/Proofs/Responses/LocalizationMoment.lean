/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
import Mathlib.Tactic.Positivity

/-!
# The moment of the radius used in Lemma `lem:blocks`

The proof of [AB26, Lemma 6.1] with the changes of the proof of Lemma `lem:blocks` uses the moment
`E[R^{128d²}] ≤ C` of Lemma `lem:localization`, at side `1`. `exists_radius_moments_of` is that
moment, with the natural exponent `128d²`, `d = m + 1`: the real exponent of the contract is a
natural one, and the constant `max Cb 1` makes `Cb ≤ Cb ^ p`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- Lemma `lem:localization` at side `1` and `p = 128d²`, with a natural exponent. -/
theorem exists_radius_moments_of (h : LocalizationStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ κ : ℝ, 0 < κ → ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
    ∀ M : Model m, M.Standing → M.Fits bd →
    ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
    Premise M K A N → RangeA M K A N Cstar →
    ∀ ℓ : ℕ, κ * N ≤ ℓ → ℓ ≤ N → ∀ (t : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
      IsCubePair M K A ℓ 1 t I I' → ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) →
      (∫⁻ ω, locRadius ω I I' (W M K A ℓ) ^ (128 * (m + 1) ^ 2) ∂M.P ≤
          ENNReal.ofReal (Cb ^ (128 * (m + 1) ^ 2))) ∧
      ∀ p : ℤ, (∀ u ∈ I, u.1 = p) →
        ∫⁻ ω, locRadiusSlab ω p (p + ℓ) I I' (W M K A ℓ) ^ (128 * (m + 1) ^ 2) ∂M.P ≤
          ENNReal.ofReal (Cb ^ (128 * (m + 1) ^ 2)) := by
  have hp1 : (1 : ℝ) ≤ ((128 * (m + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨Cb, hCb, H⟩ := h bd hbd Cstar 1 le_rfl ((128 * (m + 1) ^ 2 : ℕ) : ℝ) hp1
  refine ⟨max Cb 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun κ hκ K hK => ?_⟩
  obtain ⟨N₀, hN₀⟩ := H κ hκ K hK
  refine ⟨N₀, fun M hM hfit N hN A hA hprem hrange ℓ hℓ1 hℓ2 t I I' hpair ht => ?_⟩
  obtain ⟨h1, h2⟩ := hN₀ M hM hfit N hN A hA hprem hrange ℓ hℓ1 hℓ2 t I I' hpair ht
  have hle : ENNReal.ofReal Cb ≤ ENNReal.ofReal (max Cb 1 ^ (128 * (m + 1) ^ 2)) :=
    ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans
      (le_self_pow₀ (le_max_right _ _) (by positivity)))
  simp only [ENNReal.rpow_natCast] at h1 h2
  exact ⟨h1.trans hle, fun q hq => (h2 q hq).trans hle⟩

end CurvatureVariance.Paper.Contracts
