/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.Basic
import CurvatureVariance.Paper.Proofs.Responses.PositiveResponse
import CurvatureVariance.Paper.Proofs.Gain.RREfronStein
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Equation `eq:blocksum`

The proof of Lemma `lem:blocks`, which is the proof of [AB26, Lemma 6.1]: evaluate `F^G` at a
minimizing chain of the old weights. After the replacement of a block `G` of the `i`th slab the
chain `(x_i)` remains admissible with only its `i`th term changed (the display before [AB26, (6.3)],
`Gain.ofReal_posPart_sq_targetMin_new_le`), so `(F^G − F)₊² ≤ Q_n² Y_i-term`; the exchangeability of
`(F, F^G)` (`Gain.IsSlabReplacement.lintegral_sq_sub_eq`) turns `E(F^G − F)²` into `2E(F^G − F)₊²`.
Equation `eq:scales` places every pair of an admissible chain among the retained pairs (the width
margin, `Gain.isRetainedPair_tupleIndex`). The chain is any almost sure selection `x`, as the
contract says; the proof needs no measurability of it, since the pointwise bound at `x ω` is a bound
of the integrands (`lintegral_mono_ae`).

This is the selection form, with no factor `½`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- **Equation `eq:blocksum` for a selection `x` of a minimizing chain**: if every adjacent pair of
an admissible tuple is retained, `∑_{i,G} E(F^G − F)² ≤ 2 Q_n² E ∑ᵢ Y_i(x_{i−1}, x_i)`. -/
theorem sum_lintegral_sq_sub_le_selected {M : Model m} {K : ℕ} {A : ℝ} {n L ℓ : ℕ}
    {y : Fin m → ℤ} {o : ℕ → Fin m → ℤ} {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {old : Ω → Config m} {new : ℕ → (Fin m → ℤ) → Ω → Config m}
    (hR : IsSlabReplacement M Pr n K (wInt M K A n) L (targetSlope ℓ y) o old new)
    (hn : 2 ≤ n) (hQ : 0 < Q M K A n) (x : Ω → Fin (K + 1) → Fin m → ℤ)
    (hx : ∀ᵐ ω ∂Pr, IsMinTuple M (old ω) n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) (x ω))
    (hret : ∀ Y : Fin (K + 1) → Fin m → ℤ,
      IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y → ∀ i : Fin K,
      IsRetainedPair M n (wInt M K A n) (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
        (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ)) :
    ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        ∫⁻ ω, ENNReal.ofReal ((targetMin M (new (i + 1) g ω) n K ℓ y -
          targetMin M (old ω) n K ℓ y) ^ 2) ∂Pr ≤
      ENNReal.ofReal (2 * Q M K A n ^ 2) *
        ∫⁻ ω, ∑ i : Fin K, reward M K A n (targetSlope ℓ y) old new ((i : ℕ) + 1)
          (tupleIndex n (wInt M K A n) (targetSlope ℓ y) (x ω) i.castSucc)
          (tupleIndex n (wInt M K A n) (targetSlope ℓ y) (x ω) i.succ) ω ∂Pr := by
  set t := targetSlope ℓ y
  set w := wInt M K A n
  have hF := Responses.measurable_targetMin M n K ℓ y
  set pos : ℕ → (Fin m → ℤ) → Ω → ℝ≥0∞ := fun i g ω =>
    ENNReal.ofReal (max (targetMin M (new (i + 1) g ω) n K ℓ y -
      targetMin M (old ω) n K ℓ y) 0 ^ 2) with hpos
  have hposm : ∀ i g, Measurable (pos i g) := fun i g =>
    ((((hF.comp (hR.measurable_new (i + 1) g)).sub (hF.comp hR.measurable_old)).max
      measurable_const).pow_const 2).ennreal_ofReal
  -- exchangeability: `E (F^G − F)² = 2 E (F^G − F)₊²`
  have hex : ∀ i g, ∫⁻ ω, ENNReal.ofReal ((targetMin M (new (i + 1) g ω) n K ℓ y -
      targetMin M (old ω) n K ℓ y) ^ 2) ∂Pr = 2 * ∫⁻ ω, pos i g ω ∂Pr := fun i g => by
    rw [← IsSlabReplacement.lintegral_sq_sub_eq hR hF (i + 1) g]
    exact lintegral_congr fun ω => by congr 1; ring
  simp_rw [hex, ENNReal.tsum_mul_left, ← Finset.mul_sum]
  have h2 : ENNReal.ofReal (2 * Q M K A n ^ 2) = 2 * ENNReal.ofReal (Q M K A n ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [h2, mul_assoc]
  refine mul_le_mul' le_rfl ?_
  -- interchange
  rw [Finset.sum_congr rfl fun i _ => (lintegral_tsum fun g => (hposm i g).aemeasurable).symm,
    ← lintegral_finsetSum _ fun i _ => Measurable.tsum fun g => hposm i g]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae (hx.mono fun ω hY => ?_)
  rw [Finset.sum_range]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hQ2 : ENNReal.ofReal (Q M K A n ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hr : reward M K A n t old new ((i : ℕ) + 1) (tupleIndex n w t (x ω) i.castSucc)
      (tupleIndex n w t (x ω) i.succ) ω = rewardSum M K A n t old new ((i : ℕ) + 1)
      (tupleIndex n w t (x ω) i.castSucc) (tupleIndex n w t (x ω) i.succ) ω := by
    have hri := hret (x ω) hY.1 i
    rw [reward]
    exact ite_eq_left_of_eq_true _ _ (eq_true hri)
  rw [hr, rewardSum_eq, ← mul_assoc, ENNReal.mul_inv_cancel hQ2 ENNReal.ofReal_ne_top, one_mul]
  exact ENNReal.tsum_le_tsum fun g => ofReal_posPart_sq_targetMin_new_le hR hn hY i g

end CurvatureVariance.Paper.Gain

namespace CurvatureVariance.Paper.Contracts

universe u

/-- **Equation `eq:blocksum`** (the proof of Lemma `lem:blocks`): evaluate `F^G` at a minimizing
chain and use exchangeability; equation `eq:scales` places the pairs of a chain among
the retained pairs. -/
theorem blockSum {m : ℕ} (hscales : ScalesStatement m) : BlockSumStatement.{u} m := by
  intro bd hbd Cstar K hK
  obtain ⟨Nw, hNw⟩ := Responses.eventually_row_width_small hscales bd hbd Cstar K hK
  refine ⟨max ((9 * K) ^ 2) Nw, fun M hM hfit N hN A hA hprem hrange n ℓ y htar L hL o _ Ω _ Pr old
    new hR x hx => ?_⟩
  obtain ⟨hn, hsqrt, -, -⟩ := Responses.target_size_bounds (by omega : 1 ≤ K)
    ((le_max_left _ _).trans hN) htar
  have hwidth := hNw M hM hfit N ((le_max_right _ _).trans hN) A hA hrange n hsqrt
  have hwpos := Responses.one_le_wInt (M := M) (K := K) hA (by omega : 1 ≤ n)
  have hQ : 0 < Q M K A n := mul_pos (lt_of_lt_of_le zero_lt_one hA)
    (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _)
  exact Gain.sum_lintegral_sq_sub_le_selected hR hn hQ x hx
    (fun _ hY i => Gain.isRetainedPair_tupleIndex hY hwpos hwidth i)

end CurvatureVariance.Paper.Contracts
