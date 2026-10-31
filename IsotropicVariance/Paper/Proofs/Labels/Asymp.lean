/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Scales
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Elementary asymptotics for the label steps

Two elementary facts used by the proofs of Lemmas `lem:labels` and `lem:residual`.

* **The label scale** (`exists_labelScale_bounds`). For `K ≥ 10` fixed, every length `n` with
  `N/(8K) ≤ n ≤ N` has `Q_n ≥ L`, `W_n ≥ 1` and `R W_n ≤ n/2` once `N` is large, uniformly in
  `A ≥ 1` subject to the regime, equation `eq:regime`. Indeed `Q_n ≥ n^{2/5}`, while equation
  `eq:regime` gives `Q_n ≤ Q_N ≤ C_* √(N log(2+N)) = o(N)`.
* **Exponential beats polynomial** (`tendsto_mul_pow_mul_rpow_exp_neg_sq`). The sequence
  `c (L+1)^k (2 (L+1)^k e^{-((√L - 1)/C)²})^{1/q}` tends to `0`.

The sequence `1/L → 0` is Mathlib's `tendsto_one_div_atTop_nhds_zero_nat`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper

/-! ### The label scale -/

/-- Eventually `c log(2 + N) ≤ N`. -/
theorem eventually_mul_log_two_add_le (c : ℝ) :
    ∀ᶠ N : ℝ in atTop, c * Real.log (2 + N) ≤ N := by
  have h1 : Tendsto (fun N : ℝ => 2 + N) atTop atTop :=
    tendsto_atTop_add_const_left _ 2 tendsto_id
  have hε : (0 : ℝ) < 1 / (2 * (|c| + 1)) := by positivity
  have h2 := (Real.isLittleO_log_id_atTop.comp_tendsto h1).bound hε
  filter_upwards [h2, eventually_ge_atTop (2 : ℝ)] with N hN hN2
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at hN
  have hlog : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith only [hN2])
  have hN0 : (0 : ℝ) ≤ 2 + N := by linarith only [hN2]
  rw [abs_of_nonneg hlog, abs_of_nonneg hN0] at hN
  have hcε : |c| * (1 / (2 * (|c| + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith only [abs_nonneg c]
  calc c * Real.log (2 + N) ≤ |c| * Real.log (2 + N) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) hlog
    _ ≤ |c| * (1 / (2 * (|c| + 1)) * (2 + N)) := mul_le_mul_of_nonneg_left hN (abs_nonneg c)
    _ = |c| * (1 / (2 * (|c| + 1))) * (2 + N) := by ring
    _ ≤ 1 / 2 * (2 + N) := mul_le_mul_of_nonneg_right hcε hN0
    _ ≤ N := by linarith only [hN2]

/-- Eventually `c √(N log(2 + N)) ≤ N`. -/
theorem eventually_mul_sqrt_mul_log_le (c : ℝ) :
    ∀ᶠ N : ℝ in atTop, c * Real.sqrt (N * Real.log (2 + N)) ≤ N := by
  filter_upwards [eventually_mul_log_two_add_le (c ^ 2), eventually_ge_atTop (2 : ℝ)]
    with N hN hN2
  have hs := Real.sqrt_nonneg (N * Real.log (2 + N))
  have hN0 : (0 : ℝ) ≤ N := zero_le_two.trans hN2
  rcases le_or_gt c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc hs).trans hN0
  · have hlog : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith only [hN2])
    have hx : 0 ≤ N * Real.log (2 + N) := mul_nonneg hN0 hlog
    rw [← pow_le_pow_iff_left₀ (mul_nonneg hc.le hs) hN0 two_ne_zero, mul_pow, Real.sq_sqrt hx]
    have := mul_le_mul_of_nonneg_left hN hN0
    linarith only [this]

/-- **The label scale.** For `K ≥ 10`, any `C_*`, `L ∈ ℕ` and `R ≥ 0`, once `N` is large (uniformly
in `A ≥ 1` in the regime, equation `eq:regime`), every `n ∈ [N/(8K), N]` has `n > 0`, `Q_n > 0`,
`W_n > 0`, `W_n² = n Q_n`, `W_n ≥ 1`, `Q_n ≥ L` and `R W_n ≤ n/2`. -/
theorem exists_labelScale_bounds {K : ℕ} (hK : 10 ≤ K) {Cstar : ℝ} (L : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ N₀ : ℝ, ∀ A N n : ℝ, N₀ ≤ N → 1 ≤ A → 2 ≤ N → Regime Cstar K A N → N / (8 * K) ≤ n →
      n ≤ N → (0 < n ∧ 0 < Q K A n ∧ 0 < W K A n ∧ W K A n ^ 2 = n * Q K A n ∧
        1 ≤ W K A n ∧ (L : ℝ) ≤ Q K A n ∧ R * W K A n ≤ n / 2) := by
  have hK10 : (10 : ℝ) ≤ K := by exact_mod_cast hK
  have h8K : (0 : ℝ) < 8 * K := by linarith only [hK10]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / 2 - 1 / (K : ℝ) := ⟨_, rfl⟩
  have hQ : ∀ A s : ℝ, Q K A s = A * s ^ a := fun A s => by rw [ha]; rfl
  have ha25 : 2 / 5 ≤ a := by
    have : 1 / (K : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hK10
    linarith only [this, ha]
  have ha0 : 0 ≤ a := by linarith only [ha25]
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).eventually_ge_atTop (L : ℝ))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (eventually_mul_sqrt_mul_log_le (32 * K * R ^ 2 * Cstar))
  refine ⟨max N₁ (8 * K * max 1 M), ?_⟩
  intro A N n hN₀ hA hN hReg hnlo hnhi
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN₀
  have hNM : 8 * K * max 1 M ≤ N := le_trans (le_max_right _ _) hN₀
  have hNn : N ≤ 8 * K * n := by
    rw [div_le_iff₀ h8K] at hnlo
    linarith only [hnlo]
  have hn1M : max 1 M ≤ n := le_of_mul_le_mul_left (hNM.trans hNn) h8K
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn1M
  have hnM : M ≤ n := le_trans (le_max_right _ _) hn1M
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hpow1 : 1 ≤ n ^ a := Real.one_le_rpow hn1 ha0
  have hQ1 : 1 ≤ Q K A n := by
    rw [hQ]
    exact one_le_mul_of_one_le_of_one_le hA hpow1
  have hQ0 : 0 < Q K A n := zero_lt_one.trans_le hQ1
  have hnQ : 0 ≤ n * Q K A n := mul_nonneg hn0.le hQ0.le
  have hW2 : W K A n ^ 2 = n * Q K A n := Real.sq_sqrt hnQ
  have hW1 : 1 ≤ W K A n := Real.one_le_sqrt.2 (one_le_mul_of_one_le_of_one_le hn1 hQ1)
  have hW0 : 0 < W K A n := zero_lt_one.trans_le hW1
  refine ⟨hn0, hQ0, hW0, hW2, hW1, ?_, ?_⟩
  · calc (L : ℝ) ≤ n ^ (2 / 5 : ℝ) := hM n hnM
      _ ≤ n ^ a := Real.rpow_le_rpow_of_exponent_le hn1 ha25
      _ ≤ A * n ^ a := le_mul_of_one_le_left (zero_le_one.trans hpow1) hA
      _ = Q K A n := (hQ A n).symm
  · have hReg' : Q K A N ≤ Cstar * Real.sqrt (N * Real.log (2 + N)) := hReg
    have hQN : Q K A n ≤ Cstar * Real.sqrt (N * Real.log (2 + N)) := by
      refine le_trans ?_ hReg'
      rw [hQ, hQ]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnhi ha0) hA0
    have hc := hN₁ N hN1
    have hKR : (0 : ℝ) ≤ 32 * K * R ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg K)) (sq_nonneg R)
    have h32 := mul_le_mul_of_nonneg_left hQN hKR
    have key : 4 * (R ^ 2 * Q K A n) ≤ n := by
      refine le_of_mul_le_mul_left ?_ h8K
      linarith only [h32, hc, hNn]
    rw [← pow_le_pow_iff_left₀ (mul_nonneg hR hW0.le) (half_pos hn0).le two_ne_zero, mul_pow, hW2]
    linarith only [mul_le_mul_of_nonneg_left key hn0.le]

/-! ### Exponential beats polynomial -/

/-- **Exponential beats polynomial.** For `C > 0`, `c ≥ 0`, `k ∈ ℕ` and `q ≥ 1`,
`c (L+1)^k (2 (L+1)^k e^{-((√L - 1)/C)²})^{1/q} → 0` as `L → ∞`. -/
theorem tendsto_mul_pow_mul_rpow_exp_neg_sq {C c q : ℝ} (hC : 0 < C) (hc : 0 ≤ c) (k : ℕ)
    (hq : 1 ≤ q) :
    Tendsto (fun L : ℕ => c * ((L : ℝ) + 1) ^ k *
      (2 * ((L : ℝ) + 1) ^ k * Real.exp (-((Real.sqrt L - 1) / C) ^ 2)) ^ (1 / q))
      atTop (𝓝 0) := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / q := ⟨_, rfl⟩
  rw [← hp]
  have hp0 : 0 < p := by rw [hp]; exact one_div_pos.2 (by linarith)
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by linarith)]; exact hq
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = p / (2 * C ^ 2) := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; positivity
  have hshift : Tendsto (fun L : ℕ => (L : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun L : ℕ => 2 * c * Real.exp b *
      (((L : ℝ) + 1) ^ ((2 * k : ℕ) : ℝ) * Real.exp (-b * ((L : ℝ) + 1)))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2 * k : ℕ) : ℝ) b hb0).comp
      hshift).const_mul (2 * c * Real.exp b)
    rw [mul_zero] at this
    exact this
  refine squeeze_zero' (Eventually.of_forall fun L => by positivity) ?_ hg
  filter_upwards [eventually_ge_atTop 16] with L hL
  have hx16 : (16 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = L := ⟨_, rfl⟩
  rw [← hx]
  rw [← hx] at hx16
  have hs4 : 4 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith only [hx16])
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith only [hx16])
  have h1 : x ≤ 2 * (Real.sqrt x - 1) ^ 2 := by
    linarith only [hsq, mul_nonneg (sub_nonneg.2 hs4) (Real.sqrt_nonneg x)]
  have h2 : x / (2 * C ^ 2) ≤ ((Real.sqrt x - 1) / C) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg C)
    linarith only [this]
  have hE : Real.exp (-((Real.sqrt x - 1) / C) ^ 2) ≤ Real.exp (-(x / (2 * C ^ 2))) :=
    Real.exp_le_exp.2 (neg_le_neg h2)
  have hx1 : (1 : ℝ) ≤ x + 1 := by linarith only [hx16]
  have hxk : 0 ≤ (x + 1) ^ k := pow_nonneg (zero_le_one.trans hx1) k
  have h2k : 0 ≤ 2 * (x + 1) ^ k := mul_nonneg zero_le_two hxk
  have hY0 : 0 ≤ 2 * (x + 1) ^ k * Real.exp (-((Real.sqrt x - 1) / C) ^ 2) :=
    mul_nonneg h2k (Real.exp_pos _).le
  have hYZ : 2 * (x + 1) ^ k * Real.exp (-((Real.sqrt x - 1) / C) ^ 2) ≤
      2 * (x + 1) ^ k * Real.exp (-(x / (2 * C ^ 2))) :=
    mul_le_mul_of_nonneg_left hE h2k
  have hZp : (2 * (x + 1) ^ k * Real.exp (-(x / (2 * C ^ 2)))) ^ p =
      2 ^ p * ((x + 1) ^ k) ^ p * Real.exp (-(x / (2 * C ^ 2)) * p) := by
    rw [Real.mul_rpow h2k (Real.exp_pos _).le, Real.mul_rpow zero_le_two hxk, ← Real.exp_mul]
  have h2p : (2 : ℝ) ^ p ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp1
  have hkp : ((x + 1) ^ k) ^ p ≤ (x + 1) ^ k := by
    simpa using Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hx1 : (1 : ℝ) ≤ (x + 1) ^ k) hp1
  have hexp : Real.exp (-(x / (2 * C ^ 2)) * p) = Real.exp b * Real.exp (-b * (x + 1)) := by
    rw [← Real.exp_add, hb]
    congr 1
    field_simp
    ring
  have hpow : (x + 1) ^ ((2 * k : ℕ) : ℝ) = (x + 1) ^ k * (x + 1) ^ k := by
    rw [Real.rpow_natCast, two_mul, pow_add]
  have hck : 0 ≤ c * (x + 1) ^ k := mul_nonneg hc hxk
  have hkp0 : 0 ≤ ((x + 1) ^ k) ^ p := Real.rpow_nonneg hxk p
  have hexp0 : 0 ≤ Real.exp (-(x / (2 * C ^ 2)) * p) := (Real.exp_pos _).le
  calc c * (x + 1) ^ k * (2 * (x + 1) ^ k * Real.exp (-((Real.sqrt x - 1) / C) ^ 2)) ^ p
      ≤ c * (x + 1) ^ k * (2 * (x + 1) ^ k * Real.exp (-(x / (2 * C ^ 2)))) ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY0 hYZ hp0.le) hck
    _ = c * (x + 1) ^ k * (2 ^ p * ((x + 1) ^ k) ^ p * Real.exp (-(x / (2 * C ^ 2)) * p)) := by
        rw [hZp]
    _ ≤ c * (x + 1) ^ k * (2 * (x + 1) ^ k * Real.exp (-(x / (2 * C ^ 2)) * p)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hexp0) hck
        exact mul_le_mul h2p hkp hkp0 (by norm_num)
    _ = 2 * c * Real.exp b * ((x + 1) ^ ((2 * k : ℕ) : ℝ) * Real.exp (-b * (x + 1))) := by
        rw [hexp, hpow]
        ring

end IsotropicVariance.Paper.Proofs.Labels
