/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusAssembly
public import IsotropicVariance.Paper.Proofs.Modulus.ModulusAnalysis
public import IsotropicVariance.Paper.Proofs.Profiles.Scales
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum

/-!
# The thresholds of equation `eq:modulus`

* `W_le_rpow_mul_W`: `W_n ≤ κ^{−3/4} W_{κn}`, so the index box of radius `boxRadius m h` covers
  the cut points and the endpoints at the side `W_{κn}` of the small cubes;
* `cutData_of`: the geometric thresholds `CutData` for an admissible pair, `κ = h^{1/3}`,
  `Λ = h^{−1/3}`, `n > 2`;
* `small_offset_le`: the small pairs are admissible at `κn` once `W_{κn} √m L ≤ κn/4`.
-/

@[expose] public section

open Set

open IsotropicVariance.Paper.Proofs.Profiles (Q_nonneg)
open IsotropicVariance.Paper.Proofs.Responses (transverseIntegerPoint)
namespace IsotropicVariance.Paper.Proofs.Modulus

variable {m : ℕ}

/-- `W_n ≤ κ^{−3/4} W_{κn}` for `0 < κ ≤ 1`. -/
lemma W_le_rpow_mul_W {K : ℕ} {A κ n : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hn : 0 ≤ n) : W K A n ≤ κ ^ (-(3 / 4 : ℝ)) * W K A (κ * n) := by
  have hQ := Profiles.Q_mul (K := K) (A := A) hκ.le hn
  have hpow : κ ^ (3 / 2 : ℝ) ≤ κ * κ ^ Profiles.qExp K := by
    have e : κ ^ (1 + Profiles.qExp K) = κ * κ ^ Profiles.qExp K := by
      rw [Real.rpow_add hκ, Real.rpow_one]
    rw [← e]
    exact Real.rpow_le_rpow_of_exponent_ge hκ hκ1 (by linarith [Profiles.qExp_le (K := K)])
  have h1 : κ ^ (3 / 4 : ℝ) * W K A n ≤ W K A (κ * n) := by
    have hs : κ ^ (3 / 4 : ℝ) = Real.sqrt (κ ^ (3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hκ.le]
      norm_num
    unfold W
    rw [hQ, hs, ← Real.sqrt_mul (Real.rpow_nonneg hκ.le _)]
    apply Real.sqrt_le_sqrt
    have hnQ : 0 ≤ n * Q K A n := mul_nonneg hn (Q_nonneg hA hn)
    calc κ ^ (3 / 2 : ℝ) * (n * Q K A n) ≤ (κ * κ ^ Profiles.qExp K) * (n * Q K A n) :=
          mul_le_mul_of_nonneg_right hpow hnQ
      _ = κ * n * (κ ^ Profiles.qExp K * Q K A n) := by ring
  calc W K A n = κ ^ (-(3 / 4 : ℝ)) * (κ ^ (3 / 4 : ℝ) * W K A n) := by
        rw [← mul_assoc, ← Real.rpow_add hκ]
        norm_num
    _ ≤ κ ^ (-(3 / 4 : ℝ)) * W K A (κ * n) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hκ.le _)

/-- **The geometric thresholds** for an admissible pair. -/
lemma cutData_of {p : CubePair m} {n Wn σ h : ℝ} (hp : p.IsAdmissible n Wn (1 / 2))
    (hn : 2 < n) (hh : 0 < h) (h8 : h ≤ 1 / 8) (hσ : 0 < σ)
    (hWσ : Wn ≤ cutRatio h ^ (-(3 / 4 : ℝ)) * σ) :
    CutData p (cutRatio h * n) σ (tubeRatio h * Wn) (boxRadius m h) := by
  obtain ⟨hd, h1, h1W, h2, h2W, hsl⟩ := hp
  have hκ := cutRatio_pos hh
  have hκ2 := cutRatio_le_half hh h8
  have hΛ := one_le_tubeRatio hh (h8.trans (by norm_num))
  have hWn : 0 ≤ Wn := by linarith only [h1, h1W]
  have hsq := Real.sqrt_nonneg (m : ℝ)
  have hΛ0 : 0 ≤ tubeRatio h := zero_le_one.trans hΛ
  have hA : 0 ≤ 3 / 2 * tubeRatio h + 4 * Real.sqrt m := by positivity
  set c := (3 / 2 * tubeRatio h + 4 * Real.sqrt m) * cutRatio h ^ (-(3 / 4 : ℝ)) with hcdef
  have hL : c + 1 ≤ (boxRadius m h : ℝ) := by
    simp only [boxRadius, Nat.cast_add, Nat.cast_one]
    exact add_le_add (Nat.le_ceil c) le_rfl
  have hkey : 3 / 2 * (tubeRatio h * Wn) + 4 * Real.sqrt m * Wn ≤ c * σ := by
    calc 3 / 2 * (tubeRatio h * Wn) + 4 * Real.sqrt m * Wn =
          (3 / 2 * tubeRatio h + 4 * Real.sqrt m) * Wn := by ring
      _ ≤ (3 / 2 * tubeRatio h + 4 * Real.sqrt m) * (cutRatio h ^ (-(3 / 4 : ℝ)) * σ) :=
          mul_le_mul_of_nonneg_left hWσ hA
      _ = c * σ := by rw [hcdef]; ring
  have hdiv : ∀ x, x ≤ 3 / 2 * (tubeRatio h * Wn) + 4 * Real.sqrt m * Wn →
      x / σ + 1 / 2 ≤ boxRadius m h := by
    intro x hx
    have : x / σ ≤ c := (div_le_iff₀ hσ).2 (hx.trans hkey)
    exact (add_le_add this (by norm_num)).trans hL
  have hnpos : 0 < n := zero_lt_two.trans hn
  have hn0 : 0 < p.dist := hd.symm ▸ hnpos
  have hκn : cutRatio h * n ≤ n / 2 :=
    (mul_le_mul_of_nonneg_right hκ2 hnpos.le).trans_eq (by ring)
  have hs1 : Real.sqrt m * (p.side₁ / 2) ≤ 2 * Real.sqrt m * Wn := by
    linarith only [mul_le_mul_of_nonneg_left h1W hsq]
  have hs2 : Real.sqrt m * (p.side₂ / 2) ≤ 2 * Real.sqrt m * Wn := by
    linarith only [mul_le_mul_of_nonneg_left h2W hsq]
  have hΛW : 0 ≤ tubeRatio h * Wn := mul_nonneg hΛ0 hWn
  have hsW : 0 ≤ Real.sqrt m * Wn := mul_nonneg hsq hWn
  refine ⟨hn0, ?_, h1, h2, mul_pos hκ hnpos, ?_, ?_, hσ, hΛW, hdiv _ ?_, hdiv _ ?_, hdiv _ ?_⟩
  · unfold CubePair.centerSlope at hsl
    rw [div_le_iff₀ hn0] at hsl
    exact hsl.trans_eq (by ring)
  · rw [hd]; linarith only [hκn]
  · rw [hd]; linarith only [hκn, hn]
  · linarith only [hs1, hΛW, hsW]
  · linarith only [hs2, hΛW, hsW]
  · linarith only [hs1, hs2]

/-- **The small pairs are admissible at `κn`**: the offsets are at most `κn`. -/
lemma small_offset_le {p : CubePair m} {κn σ : ℝ} {L : ℕ} (hn : 0 < p.dist)
    (hoff : ‖p.offset‖ ≤ p.dist / 2) (hκ0 : 0 < κn) (hσ : 0 ≤ σ)
    (hσL : σ * (Real.sqrt m * L) ≤ κn / 4) {a a' : Fin m → ℤ} (ha : a ∈ box m L)
    (ha' : a' ∈ box m L) :
    ‖(nearCenter p κn + σ • transverseIntegerPoint a') - σ • transverseIntegerPoint a‖ ≤ κn ∧
      ‖(p.offset + σ • transverseIntegerPoint a) -
          (farCenter p κn + σ • transverseIntegerPoint a')‖ ≤ κn := by
  have hc : ‖nearCenter p κn‖ ≤ κn / 2 := by
    rw [nearCenter, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc κn / p.dist * ‖p.offset‖ ≤ κn / p.dist * (p.dist / 2) :=
          mul_le_mul_of_nonneg_left hoff (by positivity)
      _ = κn / 2 := by field_simp
  have hb : ∀ b ∈ box m L, ‖σ • transverseIntegerPoint b‖ ≤ κn / 4 := by
    intro b hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    exact (mul_le_mul_of_nonneg_left (norm_intVec_le hb) hσ).trans hσL
  have hfar : (p.offset + σ • transverseIntegerPoint a) -
      (farCenter p κn + σ • transverseIntegerPoint a') =
      (nearCenter p κn + σ • transverseIntegerPoint a) - σ • transverseIntegerPoint a' := by
    have : farCenter p κn = p.offset - nearCenter p κn := by
      rw [farCenter, nearCenter, show (p.dist - κn) / p.dist = 1 - κn / p.dist by
        field_simp, sub_smul, one_smul]
    rw [this]
    abel
  have ha1 := hb a ha
  have ha2 := hb a' ha'
  constructor
  · calc ‖(nearCenter p κn + σ • transverseIntegerPoint a') - σ • transverseIntegerPoint a‖ ≤
          ‖nearCenter p κn + σ • transverseIntegerPoint a'‖ + ‖σ • transverseIntegerPoint a‖ :=
            norm_sub_le _ _
      _ ≤ ‖nearCenter p κn‖ + ‖σ • transverseIntegerPoint a'‖ + ‖σ • transverseIntegerPoint a‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ κn := by linarith only [hc, ha1, ha2]
  · rw [hfar]
    calc ‖(nearCenter p κn + σ • transverseIntegerPoint a) - σ • transverseIntegerPoint a'‖ ≤
          ‖nearCenter p κn + σ • transverseIntegerPoint a‖ + ‖σ • transverseIntegerPoint a'‖ :=
            norm_sub_le _ _
      _ ≤ ‖nearCenter p κn‖ + ‖σ • transverseIntegerPoint a‖ + ‖σ • transverseIntegerPoint a'‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ κn := by linarith only [hc, ha1, ha2]

end IsotropicVariance.Paper.Proofs.Modulus
