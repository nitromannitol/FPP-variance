/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Moments
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.Positivity

/-!
# `L^k` norms of `O_s` bounds

[AKM, Lemma A.1] in the form used for equation `eq:modulus`: a nonnegative `X ≤ O_s(θ)` has
`‖X‖_k ≤ (2(1 + ⌈k/s⌉!))^{1/k} θ` (`eLpNorm_le_of_isOs`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Modulus

open Cited Infra.Os

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The moment constant `(2(1 + ⌈k/s⌉!))^{1/k}`. -/
noncomputable def momentConst (s : ℝ) (k : ℕ) : ℝ :=
  (2 * (1 + ((Nat.ceil (k / s)).factorial : ℝ))) ^ (1 / (k : ℝ))

lemma momentConst_pos (s : ℝ) (k : ℕ) : 0 < momentConst s k := by
  unfold momentConst; positivity

/-- **The `L^k` norm of a nonnegative `O_s(θ)` variable.** -/
theorem eLpNorm_le_of_isOs {s θ : ℝ} {X : Ω → ℝ} (hX : IsOs P s θ X) (hs : 0 < s)
    (hθ : 0 < θ) (hX0 : ∀ ω, 0 ≤ X ω) {k : ℕ} (hk : 1 ≤ k) :
    eLpNorm X k P ≤ ENNReal.ofReal (momentConst s k * θ) := by
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hk0 (ENNReal.natCast_ne_top k)
    hX.1.aestronglyMeasurable]
  have hm := IsOs.lintegral_pos_rpow_le hX hs hθ hkr.le
  have heq : (fun ω => ‖X ω‖ₑ ^ ((k : ℝ≥0∞).toReal)) =
      fun ω => ENNReal.ofReal (max (X ω) 0 ^ (k : ℝ)) := by
    funext ω
    rw [ENNReal.toReal_natCast, max_eq_left (hX0 ω), Real.enorm_of_nonneg (hX0 ω),
      ENNReal.ofReal_rpow_of_nonneg (hX0 ω) hkr.le]
  rw [heq, ENNReal.toReal_natCast]
  calc (∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ (k : ℝ)) ∂P) ^ (1 / (k : ℝ))
      ≤ (ENNReal.ofReal (2 * (1 + ((Nat.ceil (k / s)).factorial : ℝ)) * θ ^ (k : ℝ))) ^
          (1 / (k : ℝ)) := ENNReal.rpow_le_rpow hm (by positivity)
    _ = ENNReal.ofReal (momentConst s k * θ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), Real.mul_rpow
        (by positivity) (by positivity), ← Real.rpow_mul hθ.le, mul_one_div_cancel hkr.ne',
        Real.rpow_one]
      rfl

end IsotropicVariance.Paper.Proofs.Modulus
