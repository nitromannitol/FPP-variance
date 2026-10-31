/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Paper.Proofs.Moments.WidthMargin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Equation `eq:scales`

Equation `eq:regime` gives `A ≤ C N^{δ/K} (log(2+N))^{1/2}`, and the paper then computes the two
exponents. The first bound needs `1/(2K) ≤ 1/500` and the second `1/K ≤ 1/50`, and both hold for
`K ≥ 10⁴`, so `C` comes before `K`.

* `scales_first`, `scales_second`: the two bounds at one model. The first is the width
  margin (`Moments.WidthMargin`) with the rate kept, and the second is `mul_rpow_slope_le_Q` with
  the factor `3` and `s ≥ 1/16`.
* `scalesStatement_holds`: the contract `ScalesStatement`.
* `exists_width_margin`, `exists_slope_cost`: the two forms in which the proofs of Section
  `sec:cubes` use it: `W_s ≤ η s^{3/4+δ/100}` for `N` large, and `s|t − t₀|^{2+δ} ≤ Q_s` for `s`
  large.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper

variable {m : ℕ}

/-- The first bound of equation `eq:scales`. -/
theorem scales_first {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {N : ℕ} (hN : 2 ≤ N)
    {A Cstar C' : ℝ} (hR : RangeA M K A N Cstar) (hC' : Cstar ≤ C') (hC'0 : 0 ≤ C')
    {s : ℝ} (hs : Real.sqrt N / 16 ≤ s) :
    W M K A s / s ^ ((3 : ℝ) / 4 + M.δ / 100) ≤
      4 * Real.sqrt (C' + 1) * (N : ℝ) ^ (-M.δ / 250) * Real.log (2 + N) ^ ((1 : ℝ) / 4) := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hK' : (10000 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith only [hK']
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith only [hN2]
  have hN1 : (1 : ℝ) ≤ N := by linarith only [hN2]
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs
  set L := Real.log (2 + N) with hL
  have hL0 : 0 < L := Real.log_pos (by linarith only [hN2])
  set η := 4 * Real.sqrt (C' + 1) * (N : ℝ) ^ (-M.δ / 250) * L ^ ((1 : ℝ) / 4) with hηdef
  have hη : 0 < η := by positivity
  rw [div_le_iff₀ (by positivity)]
  apply W_le_of_le M K hspos hη.le
  -- the bound on `A` from the range
  have hsqrtN : Real.sqrt (N * L) = (N : ℝ) ^ ((1 : ℝ) / 2) * Real.sqrt L := by
    rw [Real.sqrt_mul hNpos.le, Real.sqrt_eq_rpow]
  have hA1 : A * (N : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤
      C' * ((N : ℝ) ^ ((1 : ℝ) / 2) * Real.sqrt L) := by
    have h := hR
    unfold RangeA Q at h
    rw [hsqrtN] at h
    exact h.trans (mul_le_mul_of_nonneg_right hC' (by positivity))
  have hsplit : (N : ℝ) ^ ((1 : ℝ) / 2) =
      (N : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) * (N : ℝ) ^ (M.δ / K) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hA2 : A ≤ C' * Real.sqrt L * (N : ℝ) ^ (M.δ / K) := by
    have hpos : 0 < (N : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) := by positivity
    rw [hsplit] at hA1
    refine le_of_mul_le_mul_right ?_ hpos
    calc A * (N : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ _ := hA1
      _ = _ := by ring
  -- the power of `s`
  have hα : 0 ≤ M.δ / 50 + M.δ / K := by positivity
  have hs16 : (N : ℝ) ^ ((1 : ℝ) / 2) / 16 ≤ s := by
    rw [← Real.sqrt_eq_rpow]; exact hs
  have hspow : ((N : ℝ) ^ ((1 : ℝ) / 2) / 16) ^ (M.δ / 50 + M.δ / K) ≤
      s ^ (M.δ / 50 + M.δ / K) :=
    Real.rpow_le_rpow (by positivity) hs16 hα
  have hsixteen : (16 : ℝ) ^ (M.δ / 50 + M.δ / K) ≤ 16 := by
    have hle : M.δ / 50 + M.δ / K ≤ 1 := by
      have h1 : M.δ / K ≤ 1 / 10000 := by
        rw [div_le_div_iff₀ hKpos (by norm_num)]; nlinarith only [hδ1, hK', hδ]
      linarith only [h1, hδ1]
    calc (16 : ℝ) ^ (M.δ / 50 + M.δ / K) ≤ (16 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 16 := Real.rpow_one 16
  have hlower : (N : ℝ) ^ (M.δ / 100 + M.δ / (2 * K)) / 16 ≤
      ((N : ℝ) ^ ((1 : ℝ) / 2) / 16) ^ (M.δ / 50 + M.δ / K) := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hNpos.le]
    have he : (1 : ℝ) / 2 * (M.δ / 50 + M.δ / K) = M.δ / 100 + M.δ / (2 * K) := by
      field_simp; ring
    rw [he]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsixteen
  -- the exponents: `1/(2K) ≤ 1/500`
  have hexp : M.δ / K ≤ -M.δ / 125 + (M.δ / 100 + M.δ / (2 * K)) := by
    have h1 : M.δ / (2 * K) ≤ M.δ / 500 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hδ, hK']
    have h2 : M.δ / K = M.δ / (2 * K) + M.δ / (2 * K) := by field_simp; ring
    linarith only [h1, h2]
  have hNexp : (N : ℝ) ^ (M.δ / K) ≤
      (N : ℝ) ^ (-M.δ / 125) * (N : ℝ) ^ (M.δ / 100 + M.δ / (2 * K)) := by
    rw [← Real.rpow_add hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have hηsq : η ^ 2 = 16 * (C' + 1) * (N : ℝ) ^ (-M.δ / 125) * Real.sqrt L := by
    have e1 : ((N : ℝ) ^ (-M.δ / 250)) ^ 2 = (N : ℝ) ^ (-M.δ / 125) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      congr 1
      push_cast
      ring
    have e2 : (L ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt L := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, Real.sqrt_eq_rpow]
      congr 1
      norm_num
    rw [hηdef, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith only [hC'0]), e1, e2]
    ring
  have hsqrtL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  calc A ≤ C' * Real.sqrt L * (N : ℝ) ^ (M.δ / K) := hA2
    _ ≤ (C' + 1) * Real.sqrt L * (N : ℝ) ^ (M.δ / K) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only) hsqrtL)
          (by positivity)
    _ ≤ (C' + 1) * Real.sqrt L *
          ((N : ℝ) ^ (-M.δ / 125) * (N : ℝ) ^ (M.δ / 100 + M.δ / (2 * K))) :=
        mul_le_mul_of_nonneg_left hNexp (by positivity)
    _ = η ^ 2 * ((N : ℝ) ^ (M.δ / 100 + M.δ / (2 * K)) / 16) := by rw [hηsq]; ring
    _ ≤ η ^ 2 * s ^ (M.δ / 50 + M.δ / K) :=
        mul_le_mul_of_nonneg_left (hlower.trans hspow) (by positivity)

/-- The second bound of equation `eq:scales`. The factor `16` pays for `s ≥ 1/16`, since the integer
`N` is only at least `2`. -/
theorem scales_second {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A s x : ℝ}
    (hA : 1 ≤ A) (hs : 1 / 16 ≤ s) (hx0 : 0 ≤ x) (hx : x ≤ 3 * s ^ (M.δ / 100 - 1 / 4)) :
    s * x ^ (2 + M.δ) / Q M K A s ≤ 432 * s ^ (-M.δ / 5) := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hK' : (10000 : ℝ) ≤ K := by exact_mod_cast hK
  have hspos : 0 < s := by linarith only [hs]
  set e := M.δ / 100 - 1 / 4 with he
  set q := (1 : ℝ) / 2 - M.δ / K with hq
  have hA0 : 0 < A := by linarith only [hA]
  have hQ : 0 < Q M K A s := by unfold Q; positivity
  have hQge : s ^ q ≤ Q M K A s := by
    unfold Q
    exact le_mul_of_one_le_left (by positivity) hA
  -- the slope term
  have h3 : (3 : ℝ) ^ (2 + M.δ) ≤ 27 := by
    calc (3 : ℝ) ^ (2 + M.δ) ≤ (3 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hδ1])
      _ = 27 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
  have h1 : x ^ (2 + M.δ) ≤ 27 * s ^ (e * (2 + M.δ)) := by
    calc x ^ (2 + M.δ) ≤ (3 * s ^ e) ^ (2 + M.δ) :=
          Real.rpow_le_rpow hx0 hx (by linarith only [hδ])
      _ = (3 : ℝ) ^ (2 + M.δ) * s ^ (e * (2 + M.δ)) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hspos.le]
      _ ≤ 27 * s ^ (e * (2 + M.δ)) := mul_le_mul_of_nonneg_right h3 (by positivity)
  -- the exponents: `1/K ≤ 1/50`
  set g : ℝ := 1 + e * (2 + M.δ) - q + M.δ / 5 with hg
  have hKinv : M.δ / K ≤ M.δ / 10000 := div_le_div_of_nonneg_left hδ.le (by norm_num) hK'
  have hδsq : M.δ ^ 2 ≤ M.δ := by nlinarith only [hδ, hδ1]
  have hδsq0 : 0 ≤ M.δ ^ 2 := sq_nonneg _
  have hKinv0 : 0 ≤ M.δ / K := by positivity
  have hg0 : g ≤ 0 := by
    rw [hg, he, hq]; nlinarith only [hKinv, hδsq, hδ]
  have hg1 : -1 ≤ g := by
    rw [hg, he, hq]; nlinarith only [hKinv0, hδsq0, hδ, hδ1]
  -- `s^g ≤ 16`, for `s ≥ 1/16`
  have hsg : s ^ g ≤ 16 := by
    calc s ^ g ≤ ((1 : ℝ) / 16) ^ g := Real.rpow_le_rpow_of_nonpos (by norm_num) hs hg0
      _ = (16 : ℝ) ^ (-g) := by
          rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
      _ ≤ (16 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hg1])
      _ = 16 := Real.rpow_one 16
  rw [div_le_iff₀ hQ]
  have hsplit : s * s ^ (e * (2 + M.δ)) = s ^ g * s ^ (-M.δ / 5) * s ^ q := by
    rw [← Real.rpow_add hspos, ← Real.rpow_add hspos]
    nth_rewrite 1 [← Real.rpow_one s]
    rw [← Real.rpow_add hspos]
    congr 1
    rw [hg]; ring
  have hsnn : 0 ≤ s ^ (-M.δ / 5) := by positivity
  calc s * x ^ (2 + M.δ) ≤ s * (27 * s ^ (e * (2 + M.δ))) :=
        mul_le_mul_of_nonneg_left h1 hspos.le
    _ = 27 * (s ^ g * s ^ (-M.δ / 5) * s ^ q) := by rw [← hsplit]; ring
    _ ≤ 27 * (16 * s ^ (-M.δ / 5) * s ^ q) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsg hsnn) (by positivity)
    _ = 432 * s ^ (-M.δ / 5) * s ^ q := by ring
    _ ≤ 432 * s ^ (-M.δ / 5) * Q M K A s := mul_le_mul_of_nonneg_left hQge (by positivity)

/-- **Equation `eq:scales`**. -/
theorem scalesStatement_holds (m : ℕ) : Contracts.ScalesStatement m := by
  intro bd _ Cstar
  set C' := max Cstar 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨4 * Real.sqrt (C' + 1) + 432, by positivity, fun K hK M hM _ N hN A hA hR s hs => ?_⟩
  have hδ := hM.delta_pos
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by linarith only [hN2])
  have hs16 : 1 / 16 ≤ s := by linarith only [hsqrt, hs]
  have hspos : 0 < s := by linarith only [hs16]
  have hsq0 := Real.sqrt_nonneg (C' + 1)
  refine ⟨?_, fun t ht => ?_⟩
  · refine (scales_first hM hK hN hR (le_max_left _ _) hC'0 hs).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      (Real.rpow_nonneg (Real.log_nonneg (by linarith only [hN2])) _)
    linarith only
  · refine (scales_second hM hK hA hs16 (norm_nonneg _) ht).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith only [hsq0]) (by positivity)

/-- **The width margin, from equation `eq:scales`**: for `η > 0` and `N` large, `W_s ≤ η
s^{3/4+δ/100}` for `s ≥ √N/16`. The threshold depends on `η`, on `Cstar` and on the bounds. -/
theorem exists_width_margin (hS : Contracts.ScalesStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → RangeA M K A N Cstar →
      ∀ s : ℝ, Real.sqrt N / 16 ≤ s → W M K A s ≤ η * s ^ ((3 : ℝ) / 4 + M.δ / 100) := by
  obtain ⟨C, hC, hSK⟩ := hS bd hbd Cstar
  have hδb := hbd.law.delta_pos
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((eventually_log_two_add_le_rpow (r := 4 * (bd.law.δ / 250)) (by positivity)
      (by positivity : 0 < (η / C) ^ 4)).and (eventually_ge_atTop 2))
  refine ⟨N₁, fun K hK M hM hfit N hN A hA hR s hs => ?_⟩
  obtain ⟨hlog, hN2⟩ := hN₁ N hN
  rw [← hfit.δ_eq] at hlog
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith only [hNr]
  have hsqrt : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by linarith only [hNr])
  have hspos : 0 < s := by linarith only [hsqrt, hs]
  have h := (hSK K hK M hM hfit N hN2 A hA hR s hs).1
  rw [div_le_iff₀ (by positivity)] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  -- `C N^{−δ/250} L^{1/4} ≤ η`
  have hL0 : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith only [hNr])
  have h1 : Real.log (2 + N) ^ ((1 : ℝ) / 4) ≤ η / C * (N : ℝ) ^ (M.δ / 250) := by
    calc Real.log (2 + N) ^ ((1 : ℝ) / 4)
        ≤ ((η / C) ^ 4 * (N : ℝ) ^ (4 * (M.δ / 250))) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hL0 hlog (by norm_num)
      _ = ((η / C * (N : ℝ) ^ (M.δ / 250)) ^ 4) ^ ((1 : ℝ) / 4) := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (M.δ / 250)), ← Real.rpow_mul hNpos.le]
          norm_num
          ring_nf
      _ = η / C * (N : ℝ) ^ (M.δ / 250) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
  have h2 : (N : ℝ) ^ (-M.δ / 250) * (N : ℝ) ^ (M.δ / 250) = 1 := by
    rw [← Real.rpow_add hNpos, show -M.δ / 250 + M.δ / 250 = 0 by ring, Real.rpow_zero]
  calc C * (N : ℝ) ^ (-M.δ / 250) * Real.log (2 + N) ^ ((1 : ℝ) / 4)
      ≤ C * (N : ℝ) ^ (-M.δ / 250) * (η / C * (N : ℝ) ^ (M.δ / 250)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = η * ((N : ℝ) ^ (-M.δ / 250) * (N : ℝ) ^ (M.δ / 250)) := by field_simp
    _ = η := by rw [h2, mul_one]

/-- **The slope term, from equation `eq:scales`**: for `s` large,
`s |t − t₀|^{2+δ} ≤ Q_s` when `|t − t₀| ≤ 3 s^{δ/100−1/4}`. -/
theorem exists_slope_cost (hS : Contracts.ScalesStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) :
    ∃ r₂ : ℝ, 1 ≤ r₂ ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, 2 ≤ N → ∀ A : ℝ, 1 ≤ A → RangeA M K A N Cstar →
      ∀ s : ℝ, Real.sqrt N / 16 ≤ s → r₂ ≤ s → ∀ t : EuclideanSpace ℝ (Fin m),
        ‖t - M.t₀‖ ≤ 3 * s ^ (M.δ / 100 - 1 / 4) → s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Q M K A s := by
  obtain ⟨C, hC, hSK⟩ := hS bd hbd Cstar
  have hδb := hbd.law.delta_pos
  set r₂ := max 1 (C ^ (5 / bd.law.δ)) with hr₂
  refine ⟨r₂, le_max_left _ _, fun K hK M hM hfit N hN A hA hR s hs hr t ht => ?_⟩
  have hδ := hM.delta_pos
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hr
  have hspos : 0 < s := by linarith only [hs1]
  have hA0 : 0 < A := by linarith only [hA]
  have hQ : 0 < Q M K A s := by unfold Q; positivity
  have h := (hSK K hK M hM hfit N hN A hA hR s hs).2 t ht
  have hCs : C ≤ s ^ (M.δ / 5) := by
    have h1 : C ^ (5 / M.δ) ≤ s := by
      rw [hfit.δ_eq]
      exact (le_max_right _ _).trans hr
    calc C = (C ^ (5 / M.δ)) ^ (M.δ / 5) := by
          rw [← Real.rpow_mul hC.le, show 5 / M.δ * (M.δ / 5) = 1 by field_simp, Real.rpow_one]
      _ ≤ s ^ (M.δ / 5) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h2 : C * s ^ (-M.δ / 5) ≤ 1 := by
    rw [show -M.δ / 5 = -(M.δ / 5) by ring, Real.rpow_neg hspos.le, ← div_eq_mul_inv,
      div_le_one (by positivity)]
    exact hCs
  have h3 := (div_le_iff₀ hQ).mp (h.trans h2)
  linarith only [h3]

end CurvatureVariance.Paper.Moments
