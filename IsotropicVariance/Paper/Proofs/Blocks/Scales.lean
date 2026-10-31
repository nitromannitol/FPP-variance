/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Scales
public import IsotropicVariance.Paper.Defs.Minimum
import IsotropicVariance.Paper.Proofs.Profiles.Scales
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The length `n = ℓ/K` of Section `sec:gain`

In Section `sec:gain`, `Kn ∈ [N/8, N]`, with `K ≥ 10` as in Section `sec:induction`. So
`n ∈ [N/(8K), N/4]`, the range of the lemmas of Section `sec:exponential` and of `sec:localization`
at the lower multiple `1/(8K)`, and `n`, `Q_n`, `W_n` are positive.
-/

@[expose] public section

namespace IsotropicVariance.Paper.Proofs.Blocks

/-- The length `n = ℓ/K`: `N/(8K) ≤ n ≤ N/4`, and `n`, `Q_n`, `W_n` are positive. -/
theorem scales_of_standing {m : ℕ} {X : Setting m} {Cstar : ℝ} {K : ℕ} {A N ℓ : ℝ}
    (hS : Standing X Cstar K A N) (hℓ₁ : N / 8 ≤ ℓ) (hℓ₂ : ℓ ≤ N) :
    1 / (8 * (K : ℝ)) * N ≤ ℓ / K ∧ ℓ / K ≤ N / 4 ∧ 0 < ℓ / K ∧ 0 < Q K A (ℓ / K) ∧
      0 < W K A (ℓ / K) := by
  obtain ⟨hK, hA, hN, -, -⟩ := hS
  have hK10 : (10 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith only [hK10]
  have hℓ : 0 < ℓ := by linarith only [hN, hℓ₁]
  have hn : 0 < ℓ / K := div_pos hℓ hKpos
  have hQ : 0 < Q K A (ℓ / K) := Profiles.Q_pos (by linarith only [hA]) hn
  refine ⟨?_, ?_, hn, hQ, Real.sqrt_pos.mpr (mul_pos hn hQ)⟩
  · rw [le_div_iff₀ hKpos]
    have e : 1 / (8 * (K : ℝ)) * N * K = N / 8 := by field_simp
    rw [e]
    exact hℓ₁
  · rw [div_le_iff₀ hKpos]
    have h := mul_le_mul_of_nonneg_left hK10 (by linarith only [hN] : 0 ≤ N / 4)
    linarith only [h, hℓ₂, hN]

/-- `W ≤ n/(4(√m + 1))` gives `4√m W ≤ n`. -/
theorem four_sqrt_mul_le {m : ℕ} {W n : ℝ} (hn : 0 < n)
    (h : W ≤ 1 / (4 * (Real.sqrt m + 1)) * n) : 4 * Real.sqrt m * W ≤ n := by
  have hsq := Real.sqrt_nonneg (m : ℝ)
  calc 4 * Real.sqrt m * W
      ≤ 4 * Real.sqrt m * (1 / (4 * (Real.sqrt m + 1)) * n) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = n * (Real.sqrt m / (Real.sqrt m + 1)) := by field_simp
    _ ≤ n * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one (by positivity)).mpr (by linarith only [hsq])) hn.le
    _ = n := mul_one _

end IsotropicVariance.Paper.Proofs.Blocks
