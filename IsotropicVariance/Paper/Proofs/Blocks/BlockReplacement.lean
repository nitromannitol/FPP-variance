/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Blocks
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Proofs.Blocks.Versions
public import IsotropicVariance.Paper.Proofs.Profiles.ChainSum
import IsotropicVariance.Paper.Proofs.Blocks.Scales
import IsotropicVariance.Paper.Proofs.Responses.SelectedMoments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:blocks`, the second bound of equation `eq:rewardmoment`

The last paragraph of the proof of Lemma `lem:blocks`, with the text before the lemma: the arrays
`Y_1, …, Y_K` are independent; the first bound of equation `eq:rewardmoment` gives
`E[(Y_i(j, k) − |j − k|²)₊^{4d}]^{1/(4d)} ≤ C|j − k|⁻²`; equation `eq:chainsum`, applied to a small
multiple of the arrays, gives `E[Σ_i Y_i(x_{i−1}, x_i)] ≤ CK`; and equation `eq:blocksum` gives the
bound.

* `lintegral_sub_sq_pow_le`: the display. Equation `eq:chainsum` asks for a moment bound at every
  pair, including `j = k`, where the paper's display has no content, so the bound here is
  `1 + (2C)^{16d}` for `|j − k| = 0` and for `|j − k| ≥ 1`.
* `lintegral_sum_Y_le`: `E[Σ_i Y_i(J_{i−1}, J_i)] ≤ DCK`, `D = 1 + (2C')^{16d}`, on the probability
  space of the resampling, from the versions `exists_Y_versions` of the arrays and equation
  `eq:chainsum` for the arrays `Y'_i/D`. The indices `J` depend only on the old noise: this is the
  map `π` of equation `eq:chainsum`.
* `blockReplacementStatement_of`: the bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Blocks

open Contracts

variable {m : ℕ}

/-- `(t − r²) r⁶ ≤ t⁴` for `t ≥ 0`, `r ≥ 1`: on `t ≥ r²` the factor `t³` is at least `r⁶`. -/
lemma sub_sq_mul_le {t r : ℝ} (ht : 0 ≤ t) (hr : 1 ≤ r) : (t - r ^ 2) * r ^ 6 ≤ t ^ 4 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  rcases le_total t (r ^ 2) with h | h
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith only [h]) (by positivity)).trans
      (by positivity)
  · have h6 : r ^ 6 ≤ t ^ 3 := by
      calc r ^ 6 = (r ^ 2) ^ 3 := by ring
        _ ≤ t ^ 3 := pow_le_pow_left₀ (sq_nonneg r) h 3
    calc (t - r ^ 2) * r ^ 6 ≤ t * t ^ 3 :=
          mul_le_mul (by linarith only [sq_nonneg r]) h6 (by positivity) ht
      _ = t ^ 4 := by ring

/-- `sub_sq_mul_le` in `[0, ∞]`, for the positive part. -/
lemma ennreal_sub_sq_mul_le (x : ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) :
    (x - ENNReal.ofReal (r ^ 2)) * ENNReal.ofReal (r ^ 6) ≤ x ^ 4 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  · have ht : 0 ≤ x.toReal := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_sub _ (sq_nonneg r),
      ← ENNReal.ofReal_mul' (by positivity), ← ENNReal.ofReal_pow ht]
    exact ENNReal.ofReal_le_ofReal (sub_sq_mul_le ht hr)

/-- `x ≤ 1 + x⁴` in `[0, ∞]`. -/
lemma le_one_add_pow_four (x : ℝ≥0∞) : x ≤ 1 + x ^ 4 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · exact (le_self_pow₀ h (by norm_num)).trans le_add_self

/-- **The moment of `(T − r²)₊` at `r = 0`.** -/
lemma lintegral_sub_sq_pow_le_of_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C) (d : ℕ)
    (hmom : ∫⁻ ω, T ω ^ (16 * d) ∂P ≤ ENNReal.ofReal (C ^ (16 * d))) :
    ∫⁻ ω, (T ω - ENNReal.ofReal (0 ^ 2)) ^ (4 * d) ∂P ≤
      ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) := by
  have hpt : ∀ ω, (T ω - ENNReal.ofReal (0 ^ 2)) ^ (4 * d) ≤ 1 + T ω ^ (16 * d) := fun ω => by
    have e : T ω ^ (16 * d) = (T ω ^ (4 * d)) ^ 4 := by
      rw [← pow_mul]
      congr 1
      ring
    rw [e]
    exact (pow_le_pow_left₀ bot_le tsub_le_self _).trans (le_one_add_pow_four _)
  have hmono : C ^ (16 * d) ≤ (2 * C) ^ (16 * d) :=
    pow_le_pow_left₀ hC (by linarith only [hC]) _
  calc ∫⁻ ω, (T ω - ENNReal.ofReal (0 ^ 2)) ^ (4 * d) ∂P
      ≤ ∫⁻ ω, (1 + T ω ^ (16 * d)) ∂P := lintegral_mono hpt
    _ = 1 + ∫⁻ ω, T ω ^ (16 * d) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (C ^ (16 * d)) := by
        rw [ENNReal.ofReal_one]
        gcongr
    _ ≤ ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) := by
        rw [← ENNReal.ofReal_add zero_le_one (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith only [hmono])

/-- **The moment of `(T − r²)₊` at `r ≥ 1`**: the display after equation `eq:blocksum` (proof of
Lemma `lem:blocks`), to the power `4d`, with `|j − k|⁻⁸ᵈ ≤ 1`. -/
lemma lintegral_sub_sq_pow_le_of_one_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} {C r : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) (d : ℕ)
    (hmom : ∫⁻ ω, T ω ^ (16 * d) ∂P ≤ ENNReal.ofReal ((C * (1 + r)) ^ (16 * d))) :
    ∫⁻ ω, (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) ∂P ≤
      ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hρ : 0 < (r ^ 6) ^ (4 * d) := by positivity
  set w : ℝ := ((r ^ 6) ^ (4 * d))⁻¹ with hw
  have hw0 : 0 ≤ w := (inv_pos.mpr hρ).le
  have hw1 : ENNReal.ofReal w * ENNReal.ofReal ((r ^ 6) ^ (4 * d)) = 1 := by
    rw [← ENNReal.ofReal_mul hw0, hw, inv_mul_cancel₀ hρ.ne', ENNReal.ofReal_one]
  have hpt : ∀ ω, (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) ≤ ENNReal.ofReal w * T ω ^ (16 * d) := by
    intro ω
    have h := pow_le_pow_left₀ bot_le (ennreal_sub_sq_mul_le (T ω) hr) (4 * d)
    have e : (T ω ^ 4) ^ (4 * d) = T ω ^ (16 * d) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [mul_pow, e, ← ENNReal.ofReal_pow (by positivity)] at h
    calc (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d)
        = ENNReal.ofReal w * ((T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) *
            ENNReal.ofReal ((r ^ 6) ^ (4 * d))) := by
          rw [mul_left_comm, hw1, mul_one]
      _ ≤ ENNReal.ofReal w * T ω ^ (16 * d) := by gcongr
  have hreal : w * (C * (1 + r)) ^ (16 * d) ≤ (2 * C) ^ (16 * d) := by
    have h₁ : (C * (1 + r)) ^ (16 * d) ≤ (2 * C) ^ (16 * d) * r ^ (16 * d) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have := mul_le_mul_of_nonneg_left hr hC
      linarith only [this]
    have h₂ : r ^ (16 * d) ≤ (r ^ 6) ^ (4 * d) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hr (by omega)
    calc w * (C * (1 + r)) ^ (16 * d)
        ≤ w * ((2 * C) ^ (16 * d) * (r ^ 6) ^ (4 * d)) := by
          refine mul_le_mul_of_nonneg_left (h₁.trans ?_) hw0
          exact mul_le_mul_of_nonneg_left h₂ (by positivity)
      _ = (2 * C) ^ (16 * d) := by
          rw [hw]
          field_simp
  calc ∫⁻ ω, (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal w * T ω ^ (16 * d) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal w * ∫⁻ ω, T ω ^ (16 * d) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal w * ENNReal.ofReal ((C * (1 + r)) ^ (16 * d)) := by gcongr
    _ = ENNReal.ofReal (w * (C * (1 + r)) ^ (16 * d)) := (ENNReal.ofReal_mul hw0).symm
    _ ≤ ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) :=
        ENNReal.ofReal_le_ofReal (by linarith only [hreal])

/-- **The moment of `(T − r²)₊`**, for `r = 0` or `r ≥ 1`, from `E[T^{16d}] ≤ (C(1 + r))^{16d}`. -/
theorem lintegral_sub_sq_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} {C r : ℝ} (hC : 0 ≤ C) (hr : r = 0 ∨ 1 ≤ r) (d : ℕ)
    (hmom : ∫⁻ ω, T ω ^ (16 * d) ∂P ≤ ENNReal.ofReal ((C * (1 + r)) ^ (16 * d))) :
    ∫⁻ ω, (T ω - ENNReal.ofReal (r ^ 2)) ^ (4 * d) ∂P ≤
      ENNReal.ofReal (1 + (2 * C) ^ (16 * d)) := by
  rcases hr with rfl | hr
  · simp only [add_zero, mul_one] at hmom
    exact lintegral_sub_sq_pow_le_of_zero hC d hmom
  · exact lintegral_sub_sq_pow_le_of_one_le hC hr d hmom

/-- The constant `1 + (2C)^{16d}` of the moment bound, `d = m + 1`. -/
noncomputable def arrayConst (m : ℕ) (C : ℝ) : ℝ := 1 + (2 * C) ^ (16 * (m + 1))

lemma one_le_arrayConst (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 1 ≤ arrayConst m C := by
  have : 0 ≤ (2 * C) ^ (16 * (m + 1)) := by positivity
  unfold arrayConst
  linarith only [this]

/-- **`E[Σ_i Y_i(x_{i−1}, x_i)] ≤ CK`** (proof of Lemma `lem:blocks`), at a fixed length: from the
independence of the arrays `Y_i`, the bound `hmom` on their moments and equation `eq:chainsum` for
the arrays `Y_i/D`, `D = 1 + (2C)^{16d}`, read on the probability space of the resampling, with
`π` the old noise. -/
theorem lintegral_sum_Y_le (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {K : ℕ}
    {n W Qn C CC : ℝ} (hn : 0 < n) (hW : 0 < W) (hC : 0 ≤ C) {L : ℕ}
    (σ : X.BlockInfo n W L) (o : Fin K → Fin m → Fin L)
    (hCC : Profiles.ChainSumBound X b K n W CC)
    (hmom : ∀ (i : Fin K) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ n / 2 →
      ∫⁻ p, X.Y b n W Qn i j k {z | IsBlockIndex L (o i) z} Prod.fst
          (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p ^ (16 * (m + 1))
        ∂X.blockResampling n W L σ.1 ≤
        ENNReal.ofReal ((C * (1 + zNorm (j - k))) ^ (16 * (m + 1)))) :
    ∫⁻ p, ∑ i : Fin K, X.Y b n W Qn i (X.J b K n W 0 p.1 i.castSucc) (X.J b K n W 0 p.1 i.succ)
        {z | IsBlockIndex L (o i) z} Prod.fst
        (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p
      ∂X.blockResampling n W L σ.1 ≤
      ENNReal.ofReal (arrayConst m C * (CC * K)) := by
  set μ := X.blockResampling n W L σ.1 with hμ
  let blocks : ℕ → Set (Fin m → ℤ) := fun i =>
    if h : i < K then {z | IsBlockIndex L (o ⟨i, h⟩) z} else ∅
  have hblocks : ∀ i : Fin K, blocks i = {z | IsBlockIndex L (o i) z} := fun i => by
    simp [blocks, i.2]
  obtain ⟨Y', hY'm, hY'ind, hY'ae⟩ := exists_Y_versions X hb hn hW Qn σ blocks
  let T : Fin K → X.Ω × (BlockIdx m → X.Ω) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ :=
    fun i p j k => Y' i p j k
  have hTm : ∀ i j k, Measurable fun p => T i p j k := fun i j k =>
    (show Measurable (fun f : (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ => f j k) from
      (measurable_pi_apply k).comp (measurable_pi_apply j)).comp
      ((hY'm i).mono (slabSigma_le X n i) le_rfl)
  have hind : iIndepFun T μ := hY'ind.precomp Fin.val_injective
  have hae : ∀ (i : Fin K) (j k : Fin m → ℤ), ∀ᵐ p ∂μ,
      X.Y b n W Qn i j k {z | IsBlockIndex L (o i) z} Prod.fst
        (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p = T i p j k := by
    intro i j k
    have h := hY'ae i j k
    rw [hblocks i] at h
    exact h
  have hmom' : ∀ i j k, ∫⁻ p, T i p j k ^ (16 * (m + 1)) ∂μ ≤
      ENNReal.ofReal ((C * (1 + zNorm (j - k))) ^ (16 * (m + 1))) := by
    intro i j k
    have e : ∫⁻ p, T i p j k ^ (16 * (m + 1)) ∂μ = ∫⁻ p, X.Y b n W Qn i j k
        {z | IsBlockIndex L (o i) z} Prod.fst
        (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p ^ (16 * (m + 1)) ∂μ :=
      lintegral_congr_ae ((hae i j k).mono fun p hp => by simp only [hp])
    rw [e]
    by_cases hjk : W * zNorm (k - j) ≤ n / 2
    · exact hmom i j k hjk
    · have h0 : ∀ p, X.Y b n W Qn i j k {z | IsBlockIndex L (o i) z} Prod.fst
          (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 ((i : ℕ), z)) p = 0 := fun p => by
        simp [Setting.Y, hjk]
      simp only [h0, zero_pow (by omega : 16 * (m + 1) ≠ 0), lintegral_zero]
      exact bot_le
  have hD : 1 ≤ arrayConst m C := one_le_arrayConst m hC
  have hmom'' : ∀ i j k, (j, k) ∈ (Set.univ : Set ((Fin m → ℤ) × (Fin m → ℤ))) →
      ∫⁻ p, (T i p j k - ENNReal.ofReal (arrayConst m C * zNorm (j - k) ^ 2)) ^ (4 * (m + 1)) ∂μ ≤
        ENNReal.ofReal (arrayConst m C ^ (4 * (m + 1))) := fun i j k _ => by
    have h := lintegral_sub_sq_pow_le hC (Responses.zNorm_eq_zero_or_one_le (j - k)) (m + 1)
      (hmom' i j k)
    have hle : ENNReal.ofReal (zNorm (j - k) ^ 2) ≤
        ENNReal.ofReal (arrayConst m C * zNorm (j - k) ^ 2) :=
      ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left (sq_nonneg _) hD)
    exact (lintegral_mono fun p => pow_le_pow_left₀ bot_le (tsub_le_tsub_left hle _) _).trans
      (h.trans (ENNReal.ofReal_le_ofReal (le_self_pow₀ hD (by omega))))
  have hold : MeasurePreserving Prod.fst μ X.P :=
    X.measurePreserving_old (fun p : BlockIdx m => block n W L p.1 p.2) σ.1
  have hsel := Profiles.lintegral_sum_le_of_chainSum hCC hold (by linarith only [hD]) T hTm hind
    Set.univ hmom'' fun _ _ => Set.mem_univ _
  refine le_of_eq_of_le (lintegral_congr_ae ?_) hsel
  have hall := ae_all_iff.2 fun i : Fin K => ae_all_iff.2 fun j => ae_all_iff.2 fun k => hae i j k
  filter_upwards [hall] with p hp
  exact Finset.sum_congr rfl fun i _ => hp i _ _

/-- **Lemma `lem:blocks`, the second bound of equation `eq:rewardmoment`**, from equation
`eq:blocksum`, the first bound of equation `eq:rewardmoment` and equation `eq:chainsum`. -/
theorem blockReplacementStatement_of (hS : BlockSumStatement.{u}) (hM : RewardMomentStatement.{u})
    (hC : ChainSumStatement.{u}) : BlockReplacementStatement.{u} := by
  intro m hm X hX b hb Cstar hCstar
  obtain ⟨CY, hCY, HY⟩ := hM m hm X hX b hb Cstar hCstar
  obtain ⟨CC, hCC, HC⟩ := hC m hm X hX b hb Cstar hCstar
  have hD0 : 0 < arrayConst m CY := zero_lt_one.trans_le (one_le_arrayConst m hCY.le)
  refine ⟨2 * (arrayConst m CY * CC), by positivity, fun K => ?_⟩
  by_cases hK : 10 ≤ K
  swap
  · exact ⟨0, fun A N _ hS' => absurd hS'.1 hK⟩
  have hc₁ : (0 : ℝ) < 1 / (8 * K) := by positivity
  obtain ⟨NS, HNS⟩ := hS m hm X hX b hb Cstar hCstar K
  obtain ⟨NY, HNY⟩ := HY K
  obtain ⟨NC, HNC⟩ := HC (1 / (8 * K)) hc₁ K
  refine ⟨max (max NY NC) NS, fun A N hN hS' ℓ hℓ₁ hℓ₂ L hL σ o => ?_⟩
  have hNY : NY ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNC : NC ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNS : NS ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hn₁, hn₄, hn, -, hW⟩ := scales_of_standing hS' hℓ₁ hℓ₂
  have hsel := lintegral_sum_Y_le X hb hn hW hCY.le σ o
    (HNC A N hNC hS' K (ℓ / K) (by omega) hn₁ hn₄)
    fun i j k hjk => HNY A N hNY hS' ℓ hℓ₁ hℓ₂ L hL σ (o i) i i.2 j k hjk
  refine (HNS A N hNS hS' ℓ hℓ₁ hℓ₂ L hL σ o).trans ((mul_le_mul_right hsel _).trans ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end IsotropicVariance.Paper.Proofs.Blocks
