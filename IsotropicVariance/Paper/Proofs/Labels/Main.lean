/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Gain
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Proofs.Labels.Moments
public import IsotropicVariance.Paper.Proofs.Labels.Asymp

/-!
# Lemma `lem:labels`

`labelsStatement_of`: Lemma `lem:labels` from Lemma `lem:localization`, Lemma `lem:modulus` and
Proposition `prop:profiles`, by the paper's proof.

The parameters for `L`:
* the error of the moduli `η_L = ((L + 1)(L + 1)^{2m})⁻¹` (`etaL`), and the mesh `h_L` that equation
  `eq:modulus` gives for it;
* the mesh `κ_L = 1/(j + 1)` of the rounding, small depending on `L` (`exists_mesh`):
  `√m κ_L ≤ h_L` and `2 m L κ_L ≤ 1/(L + 1)`;
* the clip `L⁴`;
* `α_L = (#values · (1 + 2(L + 1)(L⁴ + κ_L))^{8d})⁻¹`.

The error `δ_L` is `labelError`: the first term of the second display of Step 2 of the proof gives
`2/(L + 1)`, and the second a constant times `log²(2 + (L + 1)^{2m})/L⁴` (plus a term that vanishes
for `L² ≥ m`), the third the term of `P[E]`, the rounding `1/(L + 1)` and Step 3 `1/(L + 1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper IsotropicVariance.Paper.Contracts

/-! ### The arithmetic of the parameters -/

/-- The error of the moduli. -/
noncomputable def etaL (m L : ℕ) : ℝ := 1 / (((L : ℝ) + 1) * ((L : ℝ) + 1) ^ (2 * m))

theorem etaL_pos (m L : ℕ) : 0 < etaL m L := by
  unfold etaL
  positivity

/-- The sum of the moduli over the pairs of cubes. -/
theorem card_mul_ofReal_etaL (m L : ℕ) :
    (Fintype.card (PairIdx m L) : ℝ≥0∞) * ENNReal.ofReal (etaL m L) ≤
      ENNReal.ofReal (1 / ((L : ℝ) + 1)) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_pairIdx]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold etaL
  field_simp

/-- **The mesh** of the rounding, small depending on `L` (Step 2 of the proof of Lemma
`lem:labels`), an inverse integer, so that the levels of the clip to `[−L⁴, L⁴]` are multiples of
it. -/
theorem exists_mesh {m : ℕ} (hm : 1 ≤ m) {h : ℝ} (hh : 0 < h) (L : ℕ) :
    ∃ κ : ℝ, (∃ j : ℕ, κ = 1 / ((j : ℝ) + 1)) ∧ 0 < κ ∧ κ ≤ 1 ∧ Real.sqrt m * κ ≤ 1 ∧
      Real.sqrt m * κ ≤ h ∧ 2 * m * L * κ ≤ 1 / ((L : ℝ) + 1) ∧ κ ≤ 1 / ((L : ℝ) + 1) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 (by linarith only [hm1])
  have hsqm : Real.sqrt m ≤ m := by
    have h1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.2 hm1
    have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ m by linarith only [hm1])
    nlinarith only [h1, h2]
  have hε : 0 < min (h / Real.sqrt m) (1 / (2 * m * ((L : ℝ) + 1) ^ 2)) :=
    lt_min (div_pos hh hsm) (by positivity)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  have hj1 : 1 / ((j : ℝ) + 1) ≤ h / Real.sqrt m := hj.le.trans (min_le_left _ _)
  have hj2 : 1 / ((j : ℝ) + 1) ≤ 1 / (2 * m * ((L : ℝ) + 1) ^ 2) := hj.le.trans (min_le_right _ _)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 1 / ((j : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hκ] at hj1 hj2
  have hκ0 : 0 < κ := by
    rw [hκ]
    positivity
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) j
    linarith only [this]
  have hLL : κ ≤ 1 / ((L : ℝ) + 1) := by
    refine hj2.trans (one_div_le_one_div_of_le (by positivity) ?_)
    have e : 2 * (m : ℝ) * ((L : ℝ) + 1) ^ 2 = (2 * m * ((L : ℝ) + 1)) * ((L : ℝ) + 1) := by ring
    rw [e]
    have h3 : 1 ≤ 2 * (m : ℝ) * ((L : ℝ) + 1) := by nlinarith only [hm1, hL0]
    exact le_mul_of_one_le_left (by positivity) h3
  refine ⟨κ, ⟨j, hκ⟩, hκ0, hκ1, ?_, ?_, ?_, hLL⟩
  · have h3 : Real.sqrt m * κ ≤ m * (1 / (2 * m * ((L : ℝ) + 1) ^ 2)) :=
      mul_le_mul hsqm hj2 hκ0.le (by linarith only [hm1])
    have h4 : (m : ℝ) * (1 / (2 * m * ((L : ℝ) + 1) ^ 2)) = 1 / (2 * ((L : ℝ) + 1) ^ 2) := by
      field_simp
    rw [h4] at h3
    refine h3.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith only [hL0]
  · have h3 := mul_le_mul_of_nonneg_left hj1 hsm.le
    rwa [mul_div_cancel₀ _ hsm.ne'] at h3
  · have h3 : 2 * m * L * κ ≤ 2 * m * L * (1 / (2 * m * ((L : ℝ) + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left hj2 (by positivity)
    have h4 : 2 * (m : ℝ) * L * (1 / (2 * m * ((L : ℝ) + 1) ^ 2)) = L / ((L : ℝ) + 1) ^ 2 := by
      field_simp
    rw [h4] at h3
    refine h3.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hL0]

/-- The merging term. -/
theorem merge_term_le {a c ℓ q : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hℓ : 0 ≤ ℓ) (hq : 0 < q) :
    a * (c * (1 / (c * (1 + (ℓ + 1) * a) ^ q))) ^ (1 / q) ≤ 1 / (ℓ + 1) := by
  have hB : 0 < 1 + (ℓ + 1) * a := by positivity
  have e1 : c * (1 / (c * (1 + (ℓ + 1) * a) ^ q)) = ((1 + (ℓ + 1) * a) ^ q)⁻¹ := by
    field_simp
  rw [e1, Real.inv_rpow (by positivity), one_div, Real.rpow_rpow_inv hB.le hq.ne']
  rw [← div_eq_mul_inv, div_le_div_iff₀ hB (by positivity)]
  nlinarith only [mul_nonneg hℓ ha, ha, hℓ]

/-- The merging threshold is at most the inverse of the number of values. -/
theorem merge_threshold_le {a c ℓ q : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hℓ : 0 ≤ ℓ) (hq : 0 ≤ q) :
    1 / (c * (1 + (ℓ + 1) * a) ^ q) ≤ 1 / c := by
  have hB : 1 ≤ 1 + (ℓ + 1) * a := by
    have : 0 ≤ (ℓ + 1) * a := by positivity
    linarith only [this]
  exact one_div_le_one_div_of_le hc (le_mul_of_one_le_right hc.le (Real.one_le_rpow hB hq))

/-- The sum of two bounds. -/
theorem add_le_ofReal_add {a b : ℝ≥0∞} {r s : ℝ} (ha : a ≤ ENNReal.ofReal r)
    (hb : b ≤ ENNReal.ofReal s) (hr : 0 ≤ r) (hs : 0 ≤ s) : a + b ≤ ENNReal.ofReal (r + s) := by
  rw [ENNReal.ofReal_add hr hs]
  exact add_le_add ha hb

/-- The third term: the bound of `(2L⁴) P[E]^{1/q}`. -/
theorem event_term_le {ℓ e q : ℝ} (hℓ : 0 ≤ ℓ) (he : 0 ≤ e) (hq : 0 ≤ q) (m : ℕ) :
    2 * ℓ ^ 4 * ((ℓ + 1) ^ (2 * m) * (2 * e)) ^ q ≤
      2 * (ℓ + 1) ^ (2 * m + 4) * (2 * (ℓ + 1) ^ (2 * m + 4) * e) ^ q := by
  have h1 : (1 : ℝ) ≤ ℓ + 1 := by linarith only [hℓ]
  have h2 : ℓ ^ 4 ≤ (ℓ + 1) ^ (2 * m + 4) :=
    (pow_le_pow_left₀ hℓ (by linarith only : ℓ ≤ ℓ + 1) 4).trans
      (pow_le_pow_right₀ h1 (by omega))
  have h3 : (ℓ + 1) ^ (2 * m) ≤ (ℓ + 1) ^ (2 * m + 4) := pow_le_pow_right₀ h1 (by omega)
  have h4 : (ℓ + 1) ^ (2 * m) * (2 * e) ≤ 2 * (ℓ + 1) ^ (2 * m + 4) * e := by
    have := mul_le_mul_of_nonneg_right h3 (mul_nonneg zero_le_two he)
    linarith only [this]
  exact mul_le_mul (by linarith only [h2]) (Real.rpow_le_rpow (by positivity) h4 hq)
    (by positivity) (by positivity)

/-- **The error of Lemma `lem:labels`.** -/
noncomputable def labelError (m : ℕ) (c Cl : ℝ) (L : ℕ) : ℝ :=
  4 * (1 / ((L : ℝ) + 1)) + c * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) ^ 2 / ((L : ℝ) ^ 4 / 2) +
    max ((m : ℝ) * (L : ℝ) ^ 2 / 2 - (L : ℝ) ^ 4 / 2) 0 +
    2 * ((L : ℝ) + 1) ^ (2 * m + 4) * (2 * ((L : ℝ) + 1) ^ (2 * m + 4) *
      Real.exp (-((Real.sqrt L - 1) / (2 * Cl)) ^ 2)) ^ (1 / (8 * ((m : ℝ) + 1)))

/-- The logarithm of the number of pairs of cubes grows at most linearly. -/
theorem log_two_add_le {m : ℕ} (hm : 1 ≤ m) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Real.log (2 + (ℓ + 1) ^ (2 * m)) ≤ 2 * m * (ℓ + 2) := by
  have hn : 2 * m ≠ 0 := by omega
  have h1 : (2 : ℝ) ≤ 2 ^ (2 * m) := le_self_pow₀ (by norm_num) hn
  have h2 : (ℓ + 1) ^ (2 * m) + 2 ^ (2 * m) ≤ (ℓ + 1 + 2) ^ (2 * m) :=
    pow_add_pow_le (by linarith only [hℓ]) (by norm_num) hn
  have h3 : 2 + (ℓ + 1) ^ (2 * m) ≤ (ℓ + 3) ^ (2 * m) := by
    rw [show ℓ + 3 = ℓ + 1 + 2 by ring]
    linarith only [h1, h2]
  have h4 : 0 < 2 + (ℓ + 1) ^ (2 * m) := by positivity
  have h5 : Real.log (ℓ + 3) ≤ ℓ + 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < ℓ + 3 by linarith only [hℓ])
    linarith only [this]
  calc Real.log (2 + (ℓ + 1) ^ (2 * m)) ≤ Real.log ((ℓ + 3) ^ (2 * m)) :=
        Real.log_le_log h4 h3
    _ = ((2 * m : ℕ) : ℝ) * Real.log (ℓ + 3) := Real.log_pow _ _
    _ ≤ ((2 * m : ℕ) : ℝ) * (ℓ + 2) := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _)
    _ = 2 * m * (ℓ + 2) := by push_cast; ring

/-- The second term tends to zero. -/
theorem tendsto_log_sq_div {c : ℝ} (hc : 0 ≤ c) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun L : ℕ => c * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) ^ 2 / ((L : ℝ) ^ 4 / 2))
      atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun L => ?_) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (18 * c * (2 * m) ^ 2))
  · have := sq_nonneg (Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)))
    positivity
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  have hm0 : (0 : ℝ) ≤ 2 * m := by positivity
  have h1 := log_two_add_le hm hL0.le
  have h0 : 0 ≤ Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ ((L : ℝ) + 1) ^ (2 * m) := by positivity
    linarith only [this]
  have h2 : Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) ≤ 3 * (2 * m) * L := by
    refine h1.trans ?_
    have : (L : ℝ) + 2 ≤ 3 * L := by linarith only [hL1]
    calc 2 * (m : ℝ) * ((L : ℝ) + 2) ≤ 2 * m * (3 * L) := mul_le_mul_of_nonneg_left this hm0
      _ = 3 * (2 * m) * L := by ring
  have h3 : Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) ^ 2 ≤ (3 * (2 * m) * L) ^ 2 :=
    pow_le_pow_left₀ h0 h2 2
  rw [div_le_div_iff₀ (by positivity) hL0]
  have h4 : c * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) ^ 2 * L ≤
      c * (3 * (2 * m) * L) ^ 2 * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hc) hL0.le
  have h5 : c * (3 * (2 * (m : ℝ)) * L) ^ 2 * L ≤ 18 * c * (2 * m) ^ 2 * (L ^ 4 / 2) := by
    have e1 : c * (3 * (2 * (m : ℝ)) * L) ^ 2 * L = 9 * (c * (2 * m) ^ 2) * L ^ 3 := by ring
    have e2 : 18 * c * (2 * (m : ℝ)) ^ 2 * (L ^ 4 / 2) = 9 * (c * (2 * m) ^ 2) * L ^ 4 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num)) (by positivity)
  exact h4.trans h5

/-- The term that vanishes for `L² ≥ m`. -/
theorem tendsto_max_sub_zero (m : ℕ) :
    Tendsto (fun L : ℕ => max ((m : ℝ) * (L : ℝ) ^ 2 / 2 - (L : ℝ) ^ 4 / 2) 0) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (max m 1)] with L hL
  have hm : (m : ℝ) ≤ L := by exact_mod_cast (le_max_left m 1).trans hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (le_max_right m 1).trans hL
  refine (max_eq_right ?_).symm
  have h1 : (m : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith only [hm, hL1]
  have e : (L : ℝ) ^ 2 * (L : ℝ) ^ 2 = (L : ℝ) ^ 4 := by ring
  linarith only [h1, e]

/-- **The error tends to zero.** -/
theorem tendsto_labelError {c Cl : ℝ} (hc : 0 ≤ c) (hCl : 0 < Cl) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (labelError m c Cl) atTop (𝓝 0) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 : ℝ)
  have h2 := tendsto_log_sq_div hc hm
  have h3 := tendsto_max_sub_zero m
  have h4 := tendsto_mul_pow_mul_rpow_exp_neg_sq (C := 2 * Cl) (c := 2) (q := 8 * ((m : ℝ) + 1))
    (by positivity) (by norm_num) (2 * m + 4) (by linarith only [hm0])
  have h5 := ((h1.add h2).add h3).add h4
  simp only [mul_zero, add_zero] at h5
  exact h5

/-- `4 ≤ W`, at the scale of the labels. -/
theorem four_le_W {W n Q s ℓ : ℝ} (hs : 1 ≤ s) (hℓ : 16 ≤ ℓ) (hW : 1 ≤ W) (hQ : ℓ + 1 ≤ Q)
    (hWQ : W ^ 2 = n * Q) (hslope : s * ℓ * W ≤ n / 2) : 4 ≤ W := by
  have h1 : 16 ≤ s * ℓ := by nlinarith only [hs, hℓ]
  have h2 : 16 ≤ s * ℓ * W := by nlinarith only [h1, hW]
  have hn : 32 ≤ n := by linarith only [h2, hslope]
  have hQ17 : 17 ≤ Q := by linarith only [hQ, hℓ]
  have h3 : 16 ≤ W ^ 2 := by
    rw [hWQ]
    nlinarith only [hn, hQ17]
  by_contra hcon
  rw [not_le] at hcon
  nlinarith only [h3, hW, hcon]

/-! ### Lemma `lem:labels` -/

/-- **Lemma `lem:labels`**, by the paper's proof, from Lemma `lem:localization`, Lemma `lem:modulus`
and Proposition `prop:profiles`: the labels `X_G` of `tgFamily`, built from `T_G` with the
parameters of the module docstring, are determined by the noise in their blocks, have bounded values
and atoms `0` or at least `α_L`, follow one translated rule almost surely, and satisfy equation
`eq:labelprofile` at the error `labelError`. -/
theorem labelsStatement_of (hL : LocalizationStatement.{u}) (hM : ModulusStatement.{u})
    (hP : ProfilesStatement.{u}) : LabelsStatement.{u} := by
  intro m hm X hX b hb Cstar hC
  obtain ⟨Cl, hCl, Hloc⟩ := hL m hm X hX b hb Cstar hC
  obtain ⟨Cp, hCp, Hprof⟩ := hP m hm X hX b hb Cstar hC
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 8 * ((m : ℝ) + 1) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  have Hmod' := fun L : ℕ => hM m hm X hX b hb Cstar hC (etaL m L) (etaL_pos m L)
  choose h hh Hmod using Hmod'
  choose κ _ hκ0 hκ1 hκW hκh hκ2 hκ3 using fun L : ℕ => exists_mesh hm (hh L) L
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ → ℝ, M = fun L : ℕ => (L : ℝ) ^ 4 := ⟨_, rfl⟩
  have hM0 : ∀ L, 0 ≤ M L := fun L : ℕ => by
    rw [hMdef]
    positivity
  obtain ⟨codes, hcodes⟩ : ∃ codes : ℕ → ℝ, codes = fun L : ℕ =>
      (Fintype.card (GridCode m L (κ L) (M L)) : ℝ) := ⟨_, rfl⟩
  have hcodespos : ∀ L, 0 < codes L := fun L : ℕ => by
    rw [hcodes]
    exact Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨α, hαdef⟩ : ∃ α : ℕ → ℝ, α = fun L : ℕ =>
      1 / (codes L * (1 + ((L : ℝ) + 1) * (2 * (M L + κ L))) ^ q) := ⟨_, rfl⟩
  have hαpos : ∀ L, 0 < α L := fun L : ℕ => by
    have := hcodespos L
    have := hM0 L
    have := hκ0 L
    rw [hαdef]
    positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = momentConst q ^ (1 / q) * (2 / Real.log 2 * Cp) ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    have := momentConst_pos q
    rw [hc]
    positivity
  refine ⟨α, labelError m c Cl, hαpos, tendsto_labelError hc0 hCl hm, ?_⟩
  intro K hK L hLL
  have hK10 : (10 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith only [hK10]
  have hc₁ : (0 : ℝ) < 1 / (8 * K) := by positivity
  have hc₁1 : 1 / (8 * (K : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith only [hK10]
  have hLreal : (16 : ℝ) ≤ L := by exact_mod_cast hLL
  have hL1 : 1 ≤ L := by omega
  obtain ⟨N₁, HN₁⟩ := Hloc (1 / (8 * K)) hc₁ hc₁1 K
  obtain ⟨N₂, HN₂⟩ := Hprof (1 / (8 * K)) hc₁ K
  obtain ⟨N₃, HN₃⟩ := Hmod L (1 / (8 * K)) hc₁ hc₁1 K
  obtain ⟨N₄, HN₄⟩ := exists_labelScale_bounds hK (Cstar := Cstar) (L + 1)
    (R := Real.sqrt m * L) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun A N hN hS ℓ hℓ₁ hℓ₂ => ?_⟩
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃ : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN₄ : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨-, hA, hN2, -, hReg⟩ := id hS
  have hℓ0 : 0 ≤ ℓ := le_trans (by linarith only [hN2]) hℓ₁
  have hn₁ : N / (8 * K) ≤ ℓ / K := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hℓ₁ hK0.le
  have hn₁' : 1 / (8 * K) * N ≤ ℓ / K := by
    rw [one_div_mul_eq_div]
    exact hn₁
  have hn₂ : ℓ / K ≤ N := (div_le_self hℓ0 (by linarith only [hK10])).trans hℓ₂
  set n := ℓ / K with hn_def
  obtain ⟨hn, hQ, hW, hWQ, hW1, hQL, hslope⟩ := HN₄ A N n hN₄ hA hN2 hReg hn₁ hn₂
  push_cast at hQL
  have hW4 : 4 ≤ W K A n :=
    four_le_W (Real.one_le_sqrt.2 hm1) hLreal hW1 hQL hWQ hslope
  -- the versions of `T_G`, determined by the noise in the blocks
  have hver : ∀ (i : ℕ) (z : Fin m → ℤ), ∃ V : X.Ω → Pt m × Pt m → ℝ,
      Measurable[X.info (block n (W K A n) L i z)] V ∧
      ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n (W K A n) L i z),
        ∀ v ∈ closure (block n (W K A n) L i z),
          V ω (u, v) = X.setTime b (closure (block n (W K A n) L i z)) ω u v := fun i z => by
    obtain ⟨V, -, -, hVinfo, hVae⟩ := Infra.Slab.exists_setTime_version X hb
      (isClosed_closure (s := block n (W K A n) L i z)) (convex_block _ _ _ _ _).closure
    exact ⟨V, hVinfo.mono (X.info_mono (interior_closure_block_subset hn hW hL1 i z)) le_rfl, hVae⟩
  choose V hVm hV using hver
  have hqreal : 1 / (8 * ((m : ℝ) + 1)) = 1 / q := by rw [hq]
  refine ⟨tgFamily X V n (W K A n) (Q K A n) L (κ L) (M L) (α L),
    tgFamily_isDetermined X _ _ _ _ hVm,
    tgFamily_hasBoundedValues X V _ _ _ _ (hκ0 L) (hM0 L) _,
    tgFamily_atomsGe X _ _ _ hVm ?_,
    tgFamily_isCovariantAE X hn.le hW _ hL1 (hκ0 L) _ _ hVm hV, ?_⟩
  · have hle := merge_threshold_le (a := 2 * (M L + κ L)) (ℓ := L) (q := q)
      (by have := hM0 L; have := hκ0 L; positivity) (hcodespos L) (Nat.cast_nonneg L) hq0.le
    simpa only [hαdef, hcodes] using hle
  intro i hi z
  have hadm : ∀ ab : PairIdx m L, (pairOf n (W K A n) i z ab).IsAdmissible n (W K A n) (1 / 2) :=
    fun ab => pairOf_isAdmissible hn hW.le i z ab hslope
  have hadm1 : ∀ ab : PairIdx m L, (pairOf n (W K A n) i z ab).IsAdmissible n (W K A n) 1 :=
    fun ab => by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hadm ab
      exact ⟨h1, h2, h3, h4, h5, h6.trans (by norm_num)⟩
  have hMpos : 0 < M L := by
    have : (0 : ℝ) < L := by linarith only [hLreal]
    rw [hMdef]
    positivity
  refine (eLpNorm_labelSup_le_terms X hb hn hW4 hQ hWQ hLL (hκ0 L) (hκ1 L) (hκW L) (hκh L) hMpos
    hCp hCl hVm i z (hV i z) (fun ab => HN₃ A N hN₃ hS n hn₁' hn₂ _ (hadm ab))
    (fun ab => (HN₂ A N hN₂ hS n hn₁' hn₂ _ (hadm1 ab)).2)
    (fun ab => HN₁ A N hN₁ hS n hn₁' hn₂ _ (hadm ab))).trans ?_
  -- the arithmetic
  have he : (0 : ℝ) ≤ 1 / ((L : ℝ) + 1) := by positivity
  have hMκ : 0 ≤ 2 * (M L + κ L) := by
    have := hM0 L
    have := hκ0 L
    positivity
  have T1 := card_mul_ofReal_etaL m L
  have T2 := ENNReal.ofReal_le_ofReal (hκ2 L)
  have hlog2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have T3 : ENNReal.ofReal (momentConst (8 * ((m : ℝ) + 1)) ^ (1 / (8 * ((m : ℝ) + 1))) *
      (2 / Real.log 2 * Cp * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m))) ^ 2 / (M L / 2)) ≤
      ENNReal.ofReal (c * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) ^ 2 / ((L : ℝ) ^ 4 / 2)) := by
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hc, ← hq, hMdef]
    ring
  have T4 : ENNReal.ofReal ((m : ℝ) * (L : ℝ) ^ 2 / 2 - M L / 2) ≤
      ENNReal.ofReal (max ((m : ℝ) * (L : ℝ) ^ 2 / 2 - (L : ℝ) ^ 4 / 2) 0) := by
    rw [hMdef]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have T5 : ENNReal.ofReal (2 * M L) * ENNReal.ofReal (Fintype.card (PairIdx m L) *
      (2 * Real.exp (-((Real.sqrt L - 1) / (2 * Cl)) ^ 2))) ^ (1 / (8 * ((m : ℝ) + 1))) ≤
      ENNReal.ofReal (2 * ((L : ℝ) + 1) ^ (2 * m + 4) * (2 * ((L : ℝ) + 1) ^ (2 * m + 4) *
        Real.exp (-((Real.sqrt L - 1) / (2 * Cl)) ^ 2)) ^ (1 / (8 * ((m : ℝ) + 1)))) := by
    have hexp := (Real.exp_pos (-((Real.sqrt L - 1) / (2 * Cl)) ^ 2)).le
    rw [card_pairIdx, hMdef, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (event_term_le (Nat.cast_nonneg L) hexp (by positivity) m)
  have T6 := ENNReal.ofReal_le_ofReal (hκ3 L)
  have T7 : ENNReal.ofReal (2 * (M L + κ L)) *
      ENNReal.ofReal (Fintype.card (GridCode m L (κ L) (M L)) * α L) ^
        (1 / (8 * ((m : ℝ) + 1))) ≤ ENNReal.ofReal (1 / ((L : ℝ) + 1)) := by
    have hα := hαpos L
    have hcards := hcodespos L
    have hcc : (Fintype.card (GridCode m L (κ L) (M L)) : ℝ) = codes L := by rw [hcodes]
    rw [hqreal, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.ofReal_mul hMκ, hcc]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hαdef]
    exact merge_term_le hMκ hcards (Nat.cast_nonneg L) hq0
  have hS2 : 0 ≤ c * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) ^ 2 / ((L : ℝ) ^ 4 / 2) := by
    have := sq_nonneg (Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)))
    positivity
  have hS3 : 0 ≤ max ((m : ℝ) * (L : ℝ) ^ 2 / 2 - (L : ℝ) ^ 4 / 2) 0 := le_max_right _ _
  have hS4 : 0 ≤ 2 * ((L : ℝ) + 1) ^ (2 * m + 4) * (2 * ((L : ℝ) + 1) ^ (2 * m + 4) *
      Real.exp (-((Real.sqrt L - 1) / (2 * Cl)) ^ 2)) ^ (1 / (8 * ((m : ℝ) + 1))) := by
    positivity
  have hsum := add_le_ofReal_add (add_le_ofReal_add (add_le_ofReal_add (add_le_ofReal_add
    (add_le_ofReal_add (add_le_ofReal_add T1 T2 he he) T3 (add_nonneg he he) hS2) T4
    (add_nonneg (add_nonneg he he) hS2) hS3) T5
    (add_nonneg (add_nonneg (add_nonneg he he) hS2) hS3) hS4) T6
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg he he) hS2) hS3) hS4) he) T7
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg he he) hS2) hS3) hS4) he) he
  refine hsum.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold labelError
  ring

end IsotropicVariance.Paper.Proofs.Labels
