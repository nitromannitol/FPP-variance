/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ConnectorPremise
import CurvatureVariance.Infra.FPP.TimeConstantNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chaining of Lemma `lem:tree`: constants and numerical facts

The facts used by the chaining in the proof of Lemma `lem:tree` (`exists_tree_premise`): for
`r ≥ r₀` with the transverse margin `b W_r ≤ ε r^{3/4+δ/100}` (which the first bound of equation
`eq:scales` gives for `r ≥ √N/16` and `N` large), a cube `I` of side at most `b W_r` with centre
`(p, c)`, a slope `|t − t₀| ≤ θ r^{δ/100−1/4}` (`θ < 1`; weaker than the contract's
`θ (16 r)^{δ/100−1/4}`, as every link has length at most `r`) and a subgradient `P_t`: for a
lattice point `a` within `√d` of `(p, c) + sg · r (1, t)`, `sg = ±1`,
`sup_u (T(a, u) − (−sg P_t)·(u − a)) ≤ O₁(C(b) Q_r)` over `I` thickened by `r/64`. For `sg = −1`
this is the first bound of equation `eq:tree`; for `sg = 1` it is the second bound
`sup_u (T(u, a') − P_t·(a' − u))`, from the forward dyadic centres.

The constants, chosen from the bounds `bd` before the model (`T = bd.T ≥ |t₀|`): `ρ = √d`, the
rounding slack `ε₁ = (2 + T)ρ` (`roundSlack`), `θ' = max θ 0`, the
minimal link length `L₁ = 2 max(2ε₁ + 1, (4ε₁/(1 − θ'))², (4/r₁)⁵)` (the chaining stops at this
fixed scale, so every rounded link keeps its strict margin in equation `eq:premise`), the number
of generations `J = ⌊log₂ ⌊r/L₁⌋⌋`, and the sheared box with `R₁ = r/64 + ρ + 1`,
`R₂ = a₀/2 + ρ(1 + |t|) + 1 ≤ a₀/2 + ε₁ + 1`. The slope satisfies `|t| ≤ 1 + |t₀| ≤ 1 + T`, so
`|(1, t)| ≤ 2 + T` and the remaining constants depend on `T` as well.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- `x^{−1/5} ≤ 1/c` when `x ≥ c⁵`. -/
theorem rpow_neg_fifth_le {x c : ℝ} (hc : 0 < c) (hx : c ^ 5 ≤ x) :
    x ^ (-(1 : ℝ) / 5) ≤ 1 / c := by
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h5 : c ≤ x ^ ((1 : ℝ) / 5) := by
    calc c = (c ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
      _ ≤ x ^ ((1 : ℝ) / 5) := Real.rpow_le_rpow (by positivity) hx (by norm_num)
  calc x ^ (-(1 : ℝ) / 5) = (x ^ ((1 : ℝ) / 5))⁻¹ := by
        rw [show (-(1 : ℝ) / 5) = -((1 : ℝ) / 5) by ring, Real.rpow_neg hxpos.le]
    _ ≤ c⁻¹ := inv_anti₀ hc h5
    _ = 1 / c := (one_div c).symm

/-- The slope facts: from `|t − t₀| ≤ θ r^{δ/100−1/4}`, `λ|t − t₀| ≤ θ' λ^{3/4+δ/100}` for
`0 < λ ≤ r` (every link of the chain has length at most `r`), and `|t − t₀| ≤ r^{δ/100−1/4}`. -/
theorem slope_facts {M : Model m} (hM : M.Standing) {θ r : ℝ} {t : E} (hr : 1 ≤ r)
    (ht : ‖t - M.t₀‖ ≤ θ * r ^ (M.δ / 100 - 1 / 4)) (hθ1 : θ < 1) :
    (∀ lam : ℝ, 0 < lam → lam ≤ r →
      lam * ‖t - M.t₀‖ ≤ max θ 0 * lam ^ ((3 : ℝ) / 4 + M.δ / 100)) ∧
      ‖t - M.t₀‖ ≤ r ^ (M.δ / 100 - 1 / 4) := by
  have hδ1 := hM.delta_le_one
  have hneg : M.δ / 100 - 1 / 4 ≤ 0 := by linarith only [hδ1]
  have ht' : ‖t - M.t₀‖ ≤ max θ 0 * r ^ (M.δ / 100 - 1 / 4) :=
    ht.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith only [hr]) _))
  refine ⟨fun lam hl hlr => ?_, ?_⟩
  · have h1 : r ^ (M.δ / 100 - 1 / 4) ≤ lam ^ (M.δ / 100 - 1 / 4) :=
      Real.rpow_le_rpow_of_nonpos hl hlr hneg
    have h2 : lam * lam ^ (M.δ / 100 - 1 / 4) = lam ^ ((3 : ℝ) / 4 + M.δ / 100) := by
      rw [show (3 : ℝ) / 4 + M.δ / 100 = (M.δ / 100 - 1 / 4) + 1 by ring,
        Real.rpow_add_one hl.ne']
      ring
    calc lam * ‖t - M.t₀‖ ≤ lam * (max θ 0 * lam ^ (M.δ / 100 - 1 / 4)) :=
          mul_le_mul_of_nonneg_left (ht'.trans (mul_le_mul_of_nonneg_left h1
            (le_max_right _ _))) hl.le
      _ = max θ 0 * lam ^ ((3 : ℝ) / 4 + M.δ / 100) := by rw [← h2]; ring
  · have hθ' : max θ 0 ≤ 1 := max_le hθ1.le zero_le_one
    calc ‖t - M.t₀‖ ≤ max θ 0 * r ^ (M.δ / 100 - 1 / 4) := ht'
      _ ≤ 1 * r ^ (M.δ / 100 - 1 / 4) :=
          mul_le_mul_of_nonneg_right hθ' (Real.rpow_nonneg (by linarith only [hr]) _)
      _ = _ := one_mul _

/-- The number of generations: `J = ⌊log₂ ⌊r/L₁⌋⌋` has `L₁ ≤ r/2^{j+1}` for `j < J` and
`r/2^J < 2 L₁`. -/
theorem generation_facts {r L₁ : ℝ} (hL₁ : 0 < L₁) (hrL : L₁ ≤ r) :
    (∀ j < Nat.log 2 ⌊r / L₁⌋₊, L₁ ≤ r / 2 ^ (j + 1)) ∧
      r / 2 ^ Nat.log 2 ⌊r / L₁⌋₊ < 2 * L₁ ∧ (2 : ℝ) ^ Nat.log 2 ⌊r / L₁⌋₊ ≤ r / L₁ := by
  set J := Nat.log 2 ⌊r / L₁⌋₊
  have hfl : 1 ≤ ⌊r / L₁⌋₊ := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hL₁]; linarith)
  have h1 : 2 ^ J ≤ ⌊r / L₁⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have h2 : ⌊r / L₁⌋₊ < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h1R : (2 : ℝ) ^ J ≤ r / L₁ :=
    le_trans (by exact_mod_cast h1) (Nat.floor_le (div_nonneg (by linarith only [hL₁, hrL])
      hL₁.le))
  have h2R : r / L₁ < (2 : ℝ) ^ (J + 1) := by
    have := Nat.lt_floor_add_one (r / L₁)
    have h2' : ((⌊r / L₁⌋₊ : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (J + 1) := by exact_mod_cast h2
    linarith only [this, h2']
  have hpos : (0 : ℝ) < 2 ^ J := by positivity
  refine ⟨fun j hj => ?_, ?_, h1R⟩
  · have hp : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
    rw [le_div_iff₀ (by positivity)]
    have := (le_div_iff₀ hL₁).mp (hp.trans h1R)
    linarith only [this]
  · rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hL₁, pow_succ] at h2R
    linarith only [h2R]

/-- The scale of the chain under the premise is at most `C Q_r`. -/
theorem premise_scale_le (M : Model m) (K : ℕ) {T A r b R₂ κ L₁ θf CS C₁ : ℝ} {J n : ℕ} {t : E}
    (hA : 1 ≤ A) (hr : 1 ≤ r) (he : (1 : ℝ) / 4 ≤ 1 / 2 - M.δ / K) (hb : 0 ≤ b) (hCS : 0 ≤ CS)
    (hθf : 0 ≤ θf) (hC₁ : 0 < C₁) (hn : 1 ≤ n) (hcard : (n : ℝ) ≤ (C₁ * r) ^ (m + 1))
    (hR₂0 : 0 ≤ R₂) (hR₂ : R₂ ≤ b * W M K A r / 2 + κ) (hL₁ : 1 ≤ L₁)
    (h2J : (2 : ℝ) ^ J ≤ r / L₁) (htt : r * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Q M K A r) :
    ∑ j ∈ Finset.range J, Real.log (2 * (linkCard m j : ℝ)) / Real.log 2 * Q M K A (r / 2 ^ j) +
        Real.log (2 * n) / Real.log 2 * θf +
        2 * ∑ j ∈ Finset.range J, linkCostBound M T CS R₂ r t j ≤
      (2 * ((m : ℝ) + 1) * (1 / (1 - ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹) ^ 2) +
        (1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * θf +
        2 * CS * (36 * m * b ^ 2 + 144 * m * κ ^ 2 +
          64 * roundSlack m T ^ 2 + 2)) * Q M K A r := by
  have hr0 : 0 < r := by linarith only [hr]
  have heQ0 : 0 ≤ (1 : ℝ) / 2 - M.δ / K := le_trans (by norm_num) he
  have hrQ : 1 ≤ r ^ ((1 : ℝ) / 2 - M.δ / K) := Real.one_le_rpow hr heQ0
  have hQ1 : 1 ≤ Q M K A r := by
    unfold Q; nlinarith only [hA, hrQ]
  have hr14 : r ^ ((1 : ℝ) / 4) ≤ Q M K A r := by
    unfold Q
    calc r ^ ((1 : ℝ) / 4) ≤ r ^ ((1 : ℝ) / 2 - M.δ / K) :=
          Real.rpow_le_rpow_of_exponent_le hr he
      _ ≤ A * r ^ ((1 : ℝ) / 2 - M.δ / K) := by nlinarith only [hA, hrQ]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the random errors
  have p1 := sum_link_scales_le M K (by linarith only [hA]) hr0.le he J (m := m)
  -- the final steps
  have p2 : Real.log (2 * n) / Real.log 2 * θf ≤
      (1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * θf * Q M K A r := by
    have h := log_two_mul_card_le hn hC₁ hr hcard
    have hL : 0 ≤ |Real.log C₁| := abs_nonneg _
    have h' : 1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4 * r ^ ((1 : ℝ) / 4)) / Real.log 2 ≤
        (1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * Q M K A r := by
      have h1 : |Real.log C₁| ≤ |Real.log C₁| * Q M K A r := by nlinarith only [hL, hQ1]
      have h2 : ((m : ℝ) + 1) * (|Real.log C₁| + 4 * r ^ ((1 : ℝ) / 4)) ≤
          ((m : ℝ) + 1) * (|Real.log C₁| + 4) * Q M K A r := by
        have : |Real.log C₁| + 4 * r ^ ((1 : ℝ) / 4) ≤ (|Real.log C₁| + 4) * Q M K A r := by
          nlinarith only [h1, hr14]
        calc ((m : ℝ) + 1) * (|Real.log C₁| + 4 * r ^ ((1 : ℝ) / 4)) ≤
            ((m : ℝ) + 1) * ((|Real.log C₁| + 4) * Q M K A r) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring
      have h3 := div_le_div_of_nonneg_right h2 hlog2.le
      have e : (1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * Q M K A r =
          Q M K A r + ((m : ℝ) + 1) * (|Real.log C₁| + 4) * Q M K A r / Real.log 2 := by ring
      rw [e]
      linarith only [h3, hQ1]
    calc Real.log (2 * n) / Real.log 2 * θf ≤
        ((1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * Q M K A r) * θf :=
          mul_le_mul_of_nonneg_right (h.trans h') hθf
      _ = _ := by ring
  -- the deterministic costs
  have p3 := sum_linkCostBound_le M T (R₂ := R₂) hCS hr0 t J
  have hW2 : W M K A r ^ 2 = r * Q M K A r := by
    unfold W; rw [Real.sq_sqrt (by unfold Q; positivity)]
  have hR₂sq : R₂ ^ 2 / r ≤ b ^ 2 / 2 * Q M K A r + 2 * κ ^ 2 * Q M K A r := by
    have h1 : R₂ ^ 2 ≤ 2 * (b * W M K A r / 2) ^ 2 + 2 * κ ^ 2 := by
      have hbW : 0 ≤ b * W M K A r / 2 := by unfold W; positivity
      nlinarith only [hR₂, hR₂0, hbW, sq_nonneg (b * W M K A r / 2 - κ)]
    have h2 : 2 * (b * W M K A r / 2) ^ 2 = b ^ 2 / 2 * (r * Q M K A r) := by
      rw [div_pow, mul_pow, hW2]; ring
    rw [h2] at h1
    rw [div_le_iff₀ hr0]
    have h3 : 2 * κ ^ 2 ≤ 2 * κ ^ 2 * Q M K A r * r := by
      have : 1 ≤ Q M K A r * r := by nlinarith only [hQ1, hr]
      nlinarith only [this, sq_nonneg κ]
    nlinarith only [h1, h3]
  have hJr : (2 : ℝ) ^ J / r ≤ 1 := by
    rw [div_le_one hr0]
    have := (le_div_iff₀ (by linarith only [hL₁])).mp h2J
    nlinarith only [this, hL₁, show (0 : ℝ) ≤ 2 ^ J by positivity]
  have p3' : CS * (72 * m * R₂ ^ 2 / r + 64 * roundSlack m T ^ 2 * 2 ^ J / r +
      2 * r * ‖t - M.t₀‖ ^ (2 + M.δ)) ≤
      CS * (36 * m * b ^ 2 + 144 * m * κ ^ 2 + 64 * roundSlack m T ^ 2 + 2) *
        Q M K A r := by
    rw [mul_assoc CS]
    apply mul_le_mul_of_nonneg_left _ hCS
    have e1 : 72 * m * R₂ ^ 2 / r ≤ (36 * m * b ^ 2 + 144 * m * κ ^ 2) * Q M K A r := by
      have := mul_le_mul_of_nonneg_left hR₂sq (show (0 : ℝ) ≤ 72 * m by positivity)
      rw [mul_div_assoc]
      linarith only [this]
    have e2 : 64 * roundSlack m T ^ 2 * 2 ^ J / r ≤
        64 * roundSlack m T ^ 2 * Q M K A r := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left (hJr.trans hQ1) (by positivity)
    have e3 : 2 * r * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 2 * Q M K A r := by linarith only [htt]
    linarith only [e1, e2, e3]
  calc _ ≤ 2 * ((m : ℝ) + 1) * (1 / (1 - ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹) ^ 2) * Q M K A r +
        (1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * θf * Q M K A r +
        2 * (CS * (36 * m * b ^ 2 + 144 * m * κ ^ 2 +
          64 * roundSlack m T ^ 2 + 2) * Q M K A r) := by
        linarith only [p1, p2, p3, p3']
    _ = _ := by ring

end CurvatureVariance.Paper.Moments
