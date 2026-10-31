/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.SmallMeanCore
public import IsotropicVariance.Paper.Proofs.Induction.Improvement
public import IsotropicVariance.Paper.Contracts.Slab
import Mathlib.Analysis.Complex.ExponentialBounds
public import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry
public import IsotropicVariance.Paper.Proofs.Profiles.Scales

/-!
# Lemma `lem:smallmean`: helpers of the proof

The scales, the logarithms, the choice of the constants `κ`, `l`, `δ` in the order of the paper,
none depending on `K` (`exists_kappa`, `exists_l_delta`), and the inputs at the scales of the lemma:
`isOs_slabTime_sub_dist_pair` (equation `eq:profiles`), `lintegral_modulusSup_pair` (equation
`eq:modulus`) and `variance_TRV_le_pair`. The proof is
`IsotropicVariance.Paper.Proofs.SmallMean.smallMeanStatement_of_contracts`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.SmallMean

open Infra.Slab
open Profiles (gridPair gridPair_first gridPair_second gridPair_isAdmissible
  gridPair_isAdmissible_half slabTime_gridPair)

variable {m : ℕ}

/-! ### Scales -/

/-- `Q_s ≥ s^{2/5}` for `K ≥ 10`, `A ≥ 1`, `s ≥ 1`. -/
theorem rpow_le_Q {K : ℕ} (hK : 10 ≤ K) {A s : ℝ} (hA : 1 ≤ A) (hs : 1 ≤ s) :
    s ^ (2 / 5 : ℝ) ≤ Q K A s := by
  have hKr : (10 : ℝ) ≤ K := by exact_mod_cast hK
  have hα : (2 / 5 : ℝ) ≤ 1 / 2 - 1 / (K : ℝ) := by
    have : 1 / (K : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hKr
    linarith
  calc s ^ (2 / 5 : ℝ) ≤ s ^ ((1 : ℝ) / 2 - 1 / (K : ℝ)) := Real.rpow_le_rpow_of_exponent_le hs hα
    _ ≤ A * s ^ ((1 : ℝ) / 2 - 1 / (K : ℝ)) :=
        le_mul_of_one_le_left (Real.rpow_nonneg (by linarith) _) hA

/-- `Q_r² ≤ 2Q_s²` for `s ≤ r ≤ 2s`. -/
theorem Q_sq_le_two_mul {K : ℕ} (hK : 10 ≤ K) {A s r : ℝ} (hs : 0 < s)
    (hsr : s ≤ r) (hr : r ≤ 2 * s) : Q K A r ^ 2 ≤ 2 * Q K A s ^ 2 := by
  set α : ℝ := 1 / 2 - 1 / (K : ℝ) with hαdef
  have hα0 : 0 ≤ α := (Induction.exponent_pos hK).le
  have hα1 : 2 * α ≤ 1 := by
    have : 0 ≤ 1 / (K : ℝ) := by positivity
    linarith only [this, hαdef]
  have h1 : r ^ α ≤ (2 * s) ^ α := Real.rpow_le_rpow (by linarith) hr hα0
  rw [Real.mul_rpow (by norm_num) hs.le] at h1
  have h2 : (2 : ℝ) ^ α * (2 : ℝ) ^ α ≤ 2 := by
    rw [← Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ (α + α) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hr0 : 0 ≤ r ^ α := Real.rpow_nonneg (by linarith) _
  have hs0 : 0 ≤ s ^ α := Real.rpow_nonneg hs.le _
  have h2a : 0 ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  simp only [Q, ← hαdef]
  calc (A * r ^ α) ^ 2 = A ^ 2 * (r ^ α * r ^ α) := by ring
    _ ≤ A ^ 2 * ((2 ^ α * s ^ α) * (2 ^ α * s ^ α)) := by gcongr
    _ = A ^ 2 * s ^ α * s ^ α * (2 ^ α * 2 ^ α) := by ring
    _ ≤ A ^ 2 * s ^ α * s ^ α * 2 := by gcongr
    _ = 2 * (A * s ^ α) ^ 2 := by ring

/-- `W_s(1 + √(d−1)) ≤ s/4` from the regime, equation `eq:regime`, once
`128 C_*(1 + √(d−1))² √(N log(2+N)) ≤ N`. -/
theorem W_mul_le_of_regime {Cstar : ℝ} {K : ℕ} (hK : 10 ≤ K) {A N s : ℝ}
    (hA : 0 ≤ A) (hreg : Regime Cstar K A N) (hs : 0 < s) (hsN : s ≤ N) (hNs : N / 8 ≤ s)
    (hasym : 128 * Cstar * (1 + Real.sqrt m) ^ 2 * Real.sqrt (N * Real.log (2 + N)) ≤ N) :
    W K A s * (1 + Real.sqrt m) ≤ s / 4 := by
  have hQs : Q K A s ≤ Q K A N := Profiles.Q_mono hK hA hs.le hsN
  have hQ0 : 0 ≤ Q K A s := mul_nonneg hA (Real.rpow_nonneg hs.le _)
  have hm1 : 0 < 1 + Real.sqrt m := by positivity
  have hW2 : W K A s ^ 2 = s * Q K A s := Real.sq_sqrt (mul_nonneg hs.le hQ0)
  have hkey : (W K A s * (1 + Real.sqrt m)) ^ 2 ≤ (s / 4) ^ 2 := by
    rw [mul_pow, hW2]
    have h1 : Q K A s * (1 + Real.sqrt m) ^ 2 ≤ s / 16 := by
      have hreg' : Q K A N ≤ Cstar * Real.sqrt (N * Real.log (2 + N)) := hreg
      have h2 : Cstar * Real.sqrt (N * Real.log (2 + N)) * (1 + Real.sqrt m) ^ 2 ≤ N / 128 := by
        linarith only [hasym]
      calc Q K A s * (1 + Real.sqrt m) ^ 2 ≤ Q K A N * (1 + Real.sqrt m) ^ 2 := by gcongr
        _ ≤ Cstar * Real.sqrt (N * Real.log (2 + N)) * (1 + Real.sqrt m) ^ 2 := by gcongr
        _ ≤ N / 128 := h2
        _ ≤ s / 16 := by linarith
    calc s * Q K A s * (1 + Real.sqrt m) ^ 2 = s * (Q K A s * (1 + Real.sqrt m) ^ 2) := by ring
      _ ≤ s * (s / 16) := mul_le_mul_of_nonneg_left h1 hs.le
      _ = (s / 4) ^ 2 := by ring
  have hW0 : 0 ≤ W K A s := Real.sqrt_nonneg _
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hkey

/-- The variance hypothesis of Lemma `lem:smallmean`, unnormalized. -/
theorem variance_TRV_le_of_evariance_div {X : Setting m} {r q δ : ℝ} (hq : 0 < q) (hδ : 0 ≤ δ)
    (h : evariance (fun ω => X.TRV r ω / q) X.P ≤ ENNReal.ofReal δ) :
    variance (X.TRV r) X.P ≤ q ^ 2 * δ := by
  have heq : X.TRV r = fun ω => q * (X.TRV r ω / q) := by
    funext ω
    field_simp
  have hev : evariance (X.TRV r) X.P = ENNReal.ofReal (q ^ 2) *
      evariance (fun ω => X.TRV r ω / q) X.P := by
    conv_lhs => rw [heq]
    exact evariance_mul q _ X.P
  have hle : evariance (X.TRV r) X.P ≤ ENNReal.ofReal (q ^ 2 * δ) := by
    rw [hev, ENNReal.ofReal_mul (by positivity)]
    gcongr
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

/-! ### Logarithms -/

theorem log_two_add_two_mul_sq_le {s : ℝ} (hs : 0 ≤ s) :
    Real.log (2 + 2 * s ^ 2) ≤ 3 * Real.log (2 + s) := by
  rw [← Real.log_rpow (by linarith)]
  refine Real.log_le_log (by positivity) ?_
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  nlinarith [sq_nonneg s, mul_nonneg hs (sq_nonneg s)]

/-! ### Lemma `lem:smallmean` -/

/-- The constant `κ` (end of the proof of Lemma `lem:smallmean`): `κ ≤ 1` and
`κ(m/6 + C_arr/12) ≤ c/2`. -/
theorem exists_kappa {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ κ * d ≤ c / 2 := by
  refine ⟨min 1 (c / (2 * d + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  have h1 : min 1 (c / (2 * d + 1)) ≤ c / (2 * d + 1) := min_le_right _ _
  calc min 1 (c / (2 * d + 1)) * d ≤ c / (2 * d + 1) * d := mul_le_mul_of_nonneg_right h1 hd
    _ ≤ c / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

/-- The interpolation parameter `λ` and the variance threshold `δ` (second paragraph of the proof
of Lemma `lem:smallmean`): they make the bound of one array entry at most one. -/
theorem exists_l_delta {κ C₈ : ℝ} (nT : ℝ) (hκ : 0 < κ) (hC₈ : 0 ≤ C₈) {p : ℕ}
    (hp : 1 ≤ p) :
    ∃ l δ : ℝ, 0 < l ∧ 0 < δ ∧ (12 / κ) ^ p * (3 ^ (p - 1) *
      (nT ^ 2 * (l ^ (p - 2) * (5 * δ) + C₈ / l ^ p) + (κ / 36) ^ p + (κ / 36) ^ p)) ≤ 1 := by
  set η : ℝ := κ / 36 with hηdef
  have hη : 0 < η := by positivity
  have hηp : 0 < η ^ p := by positivity
  set l : ℝ := max 1 (2 * nT ^ 2 * C₈ / η ^ p) with hldef
  have hl1 : 1 ≤ l := le_max_left _ _
  have hl0 : 0 < l := by linarith
  refine ⟨l, η ^ p / (10 * (nT ^ 2 + 1) * l ^ (p - 2)), hl0, by positivity, ?_⟩
  have hA : nT ^ 2 * (l ^ (p - 2) * (5 * (η ^ p / (10 * (nT ^ 2 + 1) * l ^ (p - 2))))) ≤
      η ^ p / 2 := by
    have heq : nT ^ 2 * (l ^ (p - 2) * (5 * (η ^ p / (10 * (nT ^ 2 + 1) * l ^ (p - 2))))) =
        η ^ p / 2 * (nT ^ 2 / (nT ^ 2 + 1)) := by
      field_simp
      ring
    rw [heq]
    have : nT ^ 2 / (nT ^ 2 + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    exact mul_le_of_le_one_right (by positivity) this
  have hB : nT ^ 2 * (C₈ / l ^ p) ≤ η ^ p / 2 := by
    have hlp : l ≤ l ^ p := le_self_pow₀ hl1 (by omega)
    have h1 : C₈ / l ^ p ≤ C₈ / l := div_le_div_of_nonneg_left hC₈ hl0 hlp
    have h2 : 2 * nT ^ 2 * C₈ / η ^ p ≤ l := le_max_right _ _
    rw [div_le_iff₀ hηp] at h2
    calc nT ^ 2 * (C₈ / l ^ p) ≤ nT ^ 2 * (C₈ / l) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = nT ^ 2 * C₈ / l := by ring
      _ ≤ η ^ p / 2 := by
          rw [div_le_iff₀ hl0]
          linarith only [h2]
  have h3 : (12 / κ) ^ p * (3 ^ (p - 1) * (3 * η ^ p)) = 1 := by
    have h3p : (3 : ℝ) ^ (p - 1) * 3 = 3 ^ p := by
      rw [← pow_succ, Nat.sub_add_cancel hp]
    calc (12 / κ) ^ p * (3 ^ (p - 1) * (3 * η ^ p)) = (12 / κ) ^ p * (3 ^ p * η ^ p) := by
          rw [← h3p]
          ring
      _ = (12 / κ * 3 * η) ^ p := by rw [mul_pow, mul_pow]; ring
      _ = 1 := by
          rw [show 12 / κ * 3 * η = 1 by rw [hηdef]; field_simp; norm_num, one_pow]
  calc _ ≤ (12 / κ) ^ p * (3 ^ (p - 1) * (3 * η ^ p)) := by
        gcongr
        linarith only [hA, hB]
    _ = 1 := h3

/-! ### The inputs of the core at the scales of Lemma `lem:smallmean` -/

section Inputs

variable (X : Setting m) {b : ℝ}

/-- The profile bound, equation `eq:profiles`, for one pair of points of a pair of cubes. -/
theorem isOs_slabTime_sub_dist_pair (hb : X.IsUpperBound b) {s W Q Cpr : ℝ} (hs : 0 < s)
    (hW : 0 < W) (hQ : 0 < Q) (hCpr : 0 < Cpr) (hWs : W * (1 + Real.sqrt m) ≤ s / 4)
    (hP : ∀ p : CubePair m, p.IsAdmissible s W 1 → Cited.IsOs X.P 1 (Cpr * Q) (fun ω =>
      ⨆ (u : p.first) (v : p.second), |X.slabTime b p.slab ω u v - dist (u : Pt m) (v : Pt m)|))
    (i : ℕ) (j k : Fin m → ℤ) (hjk : W * zNorm (k - j) ≤ s / 2) :
    ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 (i + 1) k,
      Cited.IsOs X.P 1 (Cpr * Q) fun ω => |X.slabTime b (chainSlab s 0 i) ω u v - dist u v| := by
  intro u hu v hv
  have h1 : W * (zNorm (k - j) + Real.sqrt m) ≤ s := by linarith only [hWs, hjk, hW, hs]
  have hPp := hP _ (gridPair_isAdmissible hs hW.le (i := i) hjk)
  have hu' : u ∈ (gridPair s W i j k).first := by rw [gridPair_first]; exact hu
  have hv' : v ∈ (gridPair s W i j k).second := by rw [gridPair_second]; exact hv
  refine Cited.IsOs.mono hPp zero_le_one (mul_pos hCpr hQ)
    (continuous_abs.measurable.comp_aemeasurable
      ((aemeasurable_slabTime X hb _ u v).sub_const _)) (Eventually.of_forall fun ω => ?_)
  have hb0 : 0 ≤ b := upperBound_nonneg X hb ω
  rw [slabTime_gridPair]
  beta_reduce
  refine le_iSup_pair (f := fun a c => |X.slabTime b (chainSlab s 0 i) ω a c - dist a c|)
    (B := b * (2 * s) + 2 * s) (fun a ha c hc => ?_) hu' hv'
  rw [gridPair_first] at ha
  rw [gridPair_second] at hc
  have hd := dist_gridCube_le hs.le hW.le ha hc h1
  have hD0 := slabTime_nonneg X b (chainSlab s 0 i) ω a c
  have hD1 := slabTime_le_mul_dist X hb (chainSlab s 0 i) ω
    (gridCube_subset_set hs.le W i j ha) (gridCube_succ_subset_set hs.le W i k hc)
  have hdn := dist_nonneg (x := a) (y := c)
  have hbd := mul_le_mul_of_nonneg_left hd hb0
  have hb2 : 0 ≤ b * (2 * s) := mul_nonneg hb0 (by linarith)
  rw [abs_le]
  constructor <;> linarith only [hd, hD0, hD1, hdn, hbd, hb2, hs]

/-- The modulus bound, equation `eq:modulus`, for a pair of cubes, as the Lebesgue integral of its
power. -/
theorem lintegral_modulusSup_pair {s W Q η h : ℝ} (hs : 0 < s) (hW : 0 < W)
    (hM : ∀ p : CubePair m, p.IsAdmissible s W (1 / 2) →
      eLpNorm (fun ω => Contracts.modulusSup (X.slabTime b p.slab ω) p.first p.second
        (h * W)) (8 * (m + 1) : ℝ≥0∞) X.P ≤ ENNReal.ofReal (η * Q))
    (i : ℕ) (j k : Fin m → ℤ) (hjk : W * zNorm (k - j) ≤ s / 2) :
    ∫⁻ ω, ENNReal.ofReal (Contracts.modulusSup (X.slabTime b (chainSlab s 0 i) ω)
        (gridCube s W 0 i j) (gridCube s W 0 (i + 1) k) (h * W)) ^
          (2 * (4 * (m + 1)) : ℝ) ∂X.P ≤
      ENNReal.ofReal (η * Q) ^ (2 * (4 * (m + 1)) : ℝ) := by
  have hMp := hM _ (gridPair_isAdmissible_half hs hW.le (i := i) hjk)
  rw [slabTime_gridPair, gridPair_first, gridPair_second] at hMp
  have hnn : ∀ ω, 0 ≤ Contracts.modulusSup (X.slabTime b (chainSlab s 0 i) ω)
      (gridCube s W 0 i j) (gridCube s W 0 (i + 1) k) (h * W) := fun ω =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
      Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  have hcast : ((8 * (m + 1) : ℕ) : ℝ≥0∞) = (8 * (m + 1) : ℝ≥0∞) := by push_cast; ring
  rw [← hcast] at hMp
  have hq := lintegral_rpow_le_of_eLpNorm_le hnn (q := 8 * (m + 1)) (by omega) hMp
  have hexp : (((8 * (m + 1) : ℕ) : ℝ)) = (2 * (4 * (m + 1)) : ℝ) := by push_cast; ring
  rw [hexp] at hq
  exact hq

/-- The variance hypothesis of Lemma `lem:smallmean` at the scale `Q_s`. -/
theorem variance_TRV_le_pair {K : ℕ} (hK : 10 ≤ K) {A s δ : ℝ} (hA : 0 < A) (hs : 0 < s)
    (hδ : 0 ≤ δ)
    (hvar : ∀ r : ℝ, s ≤ r → r ≤ 2 * s →
      evariance (fun ω => X.TRV r ω / Q K A r) X.P ≤ ENNReal.ofReal δ) :
    ∀ r, s ≤ r → r ≤ 2 * s → variance (X.TRV r) X.P ≤ 2 * δ * Q K A s ^ 2 := by
  intro r hr1 hr2
  have hQr : 0 < Q K A r := Profiles.Q_pos hA (by linarith)
  have h1 := variance_TRV_le_of_evariance_div hQr hδ (hvar r hr1 hr2)
  have h2 := Q_sq_le_two_mul (A := A) hK hs hr1 hr2
  have h3 := mul_le_mul_of_nonneg_left h2 hδ
  linarith only [h1, h3]

end Inputs

end IsotropicVariance.Paper.Proofs.SmallMean
