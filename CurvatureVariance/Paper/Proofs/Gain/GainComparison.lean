/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.RemoveAverage
import CurvatureVariance.Paper.Proofs.Moments.WidthMargin

/-!
# The comparison of `F̄` with the passage time

The last sentences of the proof of Proposition `prop:gain`: "the translation vectors `mLwe₂` have
length at most `2K^{−1/24+δ/(2K)}(ℓQ_ℓ)^{1/2}`, so Lemma `lem:modulus` at the length `ℓ` and
equation `eq:fixedcomparison` give `E[(F̄ − T(0,(ℓ,y)))²]^{1/2} ≤ ω_K Q_ℓ`". They replace the last
paragraph of the proof of [AB26, Proposition 6.5], and the scale lemmas follow
`IsotropicVariance.Paper.Proofs.Gain.AverageComparison`, with the exponent `1/2 − δ/K` for the
continuum's `1/2 − 1/K`.

* `W_eq_rpow_mul`: `(nQ_n)^{1/2} = K^{−3/4+δ/(2K)} (ℓQ_ℓ)^{1/2}`, for `ℓ = Kn`.
* `side_le_rpow`: **the bound of the paper**: for `L ≤ K^{1/24}`, the side `(⌈K^{2/3}⌉ − 1) L w` of
  the cubes that contain the translation vectors is at most `2K^{−1/24+δ/(2K)} (ℓQ_ℓ)^{1/2}`.
* `eLpNorm_averagedMin_sub_le_of_modulus`: the bound of `‖F̄ − T‖₂` by that of `‖F − T‖₂` and the
  error of equation `eq:modulus` at the length `ℓ`, on the two cubes.
* `exists_log_sq_le`, `rpow_le_Q`: the error `C K log²N` of equation `eq:fixedcomparison` is at most
  `Q_ℓ/K`, for `N` large depending on `K`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology InnerProductSpace

namespace CurvatureVariance.Paper.Gain.Printed

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### The scales of the translates -/

/-- `(nQ_n)^{1/2} = K^{−3/4+δ/(2K)} (ℓQ_ℓ)^{1/2}` for `ℓ = Kn`. As
`IsotropicVariance.Paper.Proofs.Gain.W_div_eq` in the continuum library. -/
theorem W_eq_rpow_mul (M : Model m) {K n ℓ : ℕ} (hK : 1 ≤ K) (hℓ : ℓ = K * n) (A : ℝ) :
    W M K A n = (K : ℝ) ^ (-(3 / 4 : ℝ) + M.δ / (2 * K)) * W M K A ℓ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set a : ℝ := 1 / 2 - M.δ / (K : ℝ) with ha
  have hsq : (K : ℝ) ^ (-(3 / 4 : ℝ) + M.δ / (2 * K)) =
      Real.sqrt ((K : ℝ) ^ (-(1 + a))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hK0.le]
    congr 1
    rw [ha]
    ring
  unfold W Q
  rw [← ha, hsq, ← Real.sqrt_mul (Real.rpow_nonneg hK0.le _), hℓ, Nat.cast_mul]
  congr 1
  rw [Real.mul_rpow hK0.le hn0, Real.rpow_neg hK0.le, Real.rpow_add hK0, Real.rpow_one]
  have hKa0 : (K : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hK0 a).ne'
  field_simp

/-- **The translation vectors** (the proof of Proposition `prop:gain`): for `L ≤ K^{1/24}`, the
side `(⌈K^{2/3}⌉ − 1) L w` is at most `2K^{−1/24+δ/(2K)} (ℓQ_ℓ)^{1/2}`. As
`IsotropicVariance.Paper.Proofs.Gain.translate_le` in the continuum library. -/
theorem side_le_rpow {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {L n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : ℓ = K * n)
    (hL : (L : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 24)) :
    side M K A L n ≤ 2 * (K : ℝ) ^ (-(1 / 24 : ℝ) + M.δ / (2 * K)) * W M K A ℓ := by
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have he : 0 ≤ (1 : ℝ) / 2 - M.δ / K := le_trans (by norm_num) (exponent_ge hM hK)
  have hW1 : 1 ≤ W M K A n := one_le_W_of_exponent_nonneg hA (by exact_mod_cast hn) he
  have hw := wInt_le_two_mul hW1
  have hWℓ : 0 ≤ W M K A ℓ := Real.sqrt_nonneg _
  have hexp : (K : ℝ) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((1 : ℝ) / 24) *
      (K : ℝ) ^ (-(3 / 4 : ℝ) + M.δ / (2 * K)) = (K : ℝ) ^ (-(1 / 24 : ℝ) + M.δ / (2 * K)) := by
    rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
    congr 1
    ring
  have hV := numTranslates_sub_one_le K
  have hV0 : (0 : ℝ) ≤ ((numTranslates K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hK23 : 0 ≤ (K : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hK0.le _
  have hK24 : 0 ≤ (K : ℝ) ^ ((1 : ℝ) / 24) := Real.rpow_nonneg hK0.le _
  have hkW : 0 ≤ (K : ℝ) ^ (-(3 / 4 : ℝ) + M.δ / (2 * K)) * W M K A ℓ :=
    mul_nonneg (Real.rpow_nonneg hK0.le _) hWℓ
  unfold side
  push_cast
  calc ((numTranslates K - 1 : ℕ) : ℝ) * L * (wInt M K A n : ℝ)
      ≤ ((numTranslates K - 1 : ℕ) : ℝ) * L * (2 * W M K A n) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hV0 hL0)
    _ = ((numTranslates K - 1 : ℕ) : ℝ) * L *
          (2 * ((K : ℝ) ^ (-(3 / 4 : ℝ) + M.δ / (2 * K)) * W M K A ℓ)) := by
        rw [W_eq_rpow_mul M hK1 hℓ A]
    _ ≤ (K : ℝ) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((1 : ℝ) / 24) *
          (2 * ((K : ℝ) ^ (-(3 / 4 : ℝ) + M.δ / (2 * K)) * W M K A ℓ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hV hL hL0 hK23) (mul_nonneg zero_le_two hkW)
    _ = 2 * ((K : ℝ) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((1 : ℝ) / 24) *
          (K : ℝ) ^ (-(3 / 4 : ℝ) + M.δ / (2 * K))) * W M K A ℓ := by ring
    _ = _ := by rw [hexp]

/-- `K^{−1/24+δ/(2K)} ≤ K^{−1/48}` for `K ≥ 24` and `δ ≤ 1`. As
`IsotropicVariance.Paper.Proofs.Gain.rpow_translation_le` in the continuum library. -/
theorem rpow_translation_le {K : ℕ} (hK : 24 ≤ K) {δ : ℝ} (hδ : δ ≤ 1) :
    (K : ℝ) ^ (-(1 / 24 : ℝ) + δ / (2 * K)) ≤ (K : ℝ) ^ (-(1 / 48 : ℝ)) := by
  have hK24 : (24 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : δ / (2 * (K : ℝ)) ≤ 1 / 48 := by
    rw [div_le_div_iff₀ (by linarith only [hK24]) (by norm_num)]
    nlinarith only [hδ, hK24]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hK24]) (by linarith only [h1])

/-! ### The comparison -/

/-- **The comparison of `F̄` with the passage time** (the proof of Proposition `prop:gain`). If the
side of the cubes is at most the mesh `h (ℓQ_ℓ)^{1/2}` of equation `eq:modulus`, which holds on the
two cubes with the error `η Q_ℓ`, then `‖F̄ − T‖₂ ≤ ‖F − T‖₂ + η Q_ℓ`: the linear term of equation
`eq:modulus` vanishes, since the two endpoints move by the same vector. -/
theorem eLpNorm_averagedMin_sub_le_of_modulus {M : Model m} (hM : M.Standing) (hm : 1 ≤ m) {K : ℕ}
    (hV : 0 < numTranslates K) {A : ℝ} {L n ℓ : ℕ} {y : Fin m → ℤ} {h η : ℝ} {a : ℝ≥0∞}
    (hside : side M K A L n ≤ h * W M K A ℓ) {P : Pt m} {X : Config m → ℝ}
    (hX : eLpNorm X (8 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal (η * Q M K A ℓ))
    (hXae : ∀ᵐ ω ∂M.P,
      ∀ u ∈ transverseCube (0 : ℤ) (centre (side M K A L n)) (side M K A L n),
      ∀ u₂ ∈ transverseCube (0 : ℤ) (centre (side M K A L n)) (side M K A L n),
      ∀ v ∈ transverseCube ((0 : ℤ) + ℓ) (centre (side M K A L n) + transversePoint y)
        (side M K A L n),
      ∀ v₂ ∈ transverseCube ((0 : ℤ) + ℓ) (centre (side M K A L n) + transversePoint y)
        (side M K A L n),
        ‖point u - point u₂‖ ≤ h * W M K A ℓ → ‖point v - point v₂‖ ≤ h * W M K A ℓ →
        |passageTimeReal ω u v - passageTimeReal ω u₂ v₂ -
          inner ℝ P (point v - point u - point v₂ + point u₂)| ≤ X ω)
    (ha : eLpNorm (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P ≤ a) :
    eLpNorm (fun ω => averagedMin M K A L ω n ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P ≤
      a + ENNReal.ofReal (η * Q M K A ℓ) := by
  have := hM.probP
  refine eLpNorm_averagedMin_sub_le hM K A L n ℓ y hV ha fun v hv => ?_
  have hTm : AEStronglyMeasurable (fun ω => passageTimeReal ω ((0 : ℤ), tau M K A L n v)
      ((ℓ : ℤ), y + tau M K A L n v) - passageTimeReal ω 0 ((ℓ : ℤ), y)) M.P :=
    ((measurable_passageTime_real _ _).sub (measurable_passageTime_real _ _)).aestronglyMeasurable
  refine le_trans (eLpNorm_two_le_of_le hTm (by omega) ?_) hX
  have hle : ((v * L * wInt M K A n : ℕ) : ℝ) ≤ side M K A L n := by
    unfold side
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hv))
  have hdist : ‖point (((0 : ℤ), tau M K A L n v) : Vertex m) - point (0 : Vertex m)‖ ≤
      h * W M K A ℓ := by
    rw [Infra.FPP.point_zero, sub_zero, norm_point_tau hm]
    exact hle.trans hside
  have hdist' : ‖point (((ℓ : ℤ), y + tau M K A L n v) : Vertex m) -
      point (((ℓ : ℤ), y) : Vertex m)‖ ≤ h * W M K A ℓ := by
    rw [show (((ℓ : ℤ), y + tau M K A L n v) : Vertex m) =
      ((ℓ : ℤ), y) + ((0 : ℤ), tau M K A L n v) by simp [Prod.mk_add_mk], point_add,
      add_sub_cancel_left]
    simpa using hdist
  filter_upwards [hXae] with ω hω
  have h' := hω _ (mem_cube_tau K A L n v hv) 0 (zero_mem_cube K A L n hV) _
    (mem_cube'_tau K A L n v ℓ y hv) ((ℓ : ℤ), y) (target_mem_cube' K A L n ℓ y hV) hdist hdist'
  have hzero : point (((ℓ : ℤ), y + tau M K A L n v) : Vertex m) -
      point (((0 : ℤ), tau M K A L n v) : Vertex m) - point (((ℓ : ℤ), y) : Vertex m) +
      point (0 : Vertex m) = 0 := by
    rw [show (((ℓ : ℤ), y + tau M K A L n v) : Vertex m) =
      ((ℓ : ℤ), y) + ((0 : ℤ), tau M K A L n v) by simp [Prod.mk_add_mk], point_add,
      Infra.FPP.point_zero]
    abel
  rw [hzero, inner_zero_right, sub_zero] at h'
  exact h'

/-! ### Equation `eq:fixedcomparison` against `Q_ℓ` -/

/-- `c log²N ≤ (N/9)^{1/4}` for `N` large. -/
theorem exists_log_sq_le (c : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → c * Real.log N ^ 2 ≤ ((N : ℝ) / 9) ^ ((1 : ℝ) / 4) := by
  set c' : ℝ := max c 0 + 1 with hc'
  have hc'1 : 1 ≤ c' := by
    have := le_max_right c 0
    linarith only [this, hc']
  have hc'0 : 0 < c' := by linarith only [hc'1]
  have hε : 0 < 1 / (2 * c') := by positivity
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    ((Moments.eventually_log_two_add_le_rpow (r := 1 / 8) (by norm_num) hε).and
      (eventually_ge_atTop 1))
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨hlog, hN1⟩ := hN₁ N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) ≤ N := by linarith only [hNr]
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hl : Real.log N ≤ 1 / (2 * c') * (N : ℝ) ^ ((1 : ℝ) / 8) :=
    (Real.log_le_log (by linarith only [hNr]) (by linarith only [hNr])).trans hlog
  have hsq : (N : ℝ) ^ ((1 : ℝ) / 4) = ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    norm_num
  have h16 : (N : ℝ) ^ ((1 : ℝ) / 4) / 2 ≤ ((N : ℝ) / 9) ^ ((1 : ℝ) / 4) := by
    have e : ((16 : ℝ)) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (N : ℝ) ^ ((1 : ℝ) / 4) / 2 = ((N : ℝ) / 16) ^ ((1 : ℝ) / 4) := by
          rw [Real.div_rpow hN0 (by norm_num), e]
      _ ≤ ((N : ℝ) / 9) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity)
            (div_le_div_of_nonneg_left hN0 (by norm_num) (by norm_num)) (by norm_num)
  have hx : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hN0 _
  have hl2 : Real.log N ^ 2 ≤ (1 / (2 * c')) ^ 2 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hsq, ← mul_pow]
    exact pow_le_pow_left₀ hl0 hl 2
  have hcoef : c' * (1 / (2 * c')) ^ 2 ≤ 1 / 2 := by
    have e : c' * (1 / (2 * c')) ^ 2 = 1 / (4 * c') := by
      field_simp
      norm_num
    rw [e]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hc'1]
  have hNq : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hN0 _
  calc c * Real.log N ^ 2 ≤ c' * Real.log N ^ 2 :=
        mul_le_mul_of_nonneg_right
          ((le_max_left c 0).trans (by linarith only [hc'])) (sq_nonneg _)
    _ ≤ c' * ((1 / (2 * c')) ^ 2 * (N : ℝ) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hl2 hc'0.le
    _ = (c' * (1 / (2 * c')) ^ 2) * (N : ℝ) ^ ((1 : ℝ) / 4) := by ring
    _ ≤ 1 / 2 * (N : ℝ) ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_right hcoef hNq
    _ = (N : ℝ) ^ ((1 : ℝ) / 4) / 2 := by ring
    _ ≤ _ := h16

/-- `(N/9)^{1/4} ≤ Q_ℓ` for `ℓ ≥ N/9`, `ℓ ≥ 1` and `K ≥ 10⁴`. -/
theorem rpow_le_Q {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ} (hA : 1 ≤ A)
    {N ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : (N : ℝ) / 9 ≤ ℓ) :
    ((N : ℝ) / 9) ^ ((1 : ℝ) / 4) ≤ Q M K A ℓ := by
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have he := exponent_ge hM hK
  have h1 : ((N : ℝ) / 9) ^ ((1 : ℝ) / 4) ≤ (ℓ : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) hℓ (by norm_num)
  have h2 : (ℓ : ℝ) ^ ((1 : ℝ) / 4) ≤ (ℓ : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) :=
    Real.rpow_le_rpow_of_exponent_le hℓr (by linarith only [he])
  have h3 : (ℓ : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ Q M K A ℓ := by
    unfold Q
    exact le_mul_of_one_le_left (Real.rpow_nonneg (by linarith only [hℓr]) _) hA
  exact h1.trans (h2.trans h3)

end CurvatureVariance.Paper.Gain.Printed
