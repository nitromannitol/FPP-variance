/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Blocks
public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Proofs.Modulus.RadiusEnergy
public import IsotropicVariance.Paper.Proofs.Profiles.ChainSum
public import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry
import IsotropicVariance.Paper.Proofs.Blocks.Localization
import IsotropicVariance.Paper.Proofs.Blocks.Scales

/-!
# Lemma `lem:blocks`, equation `eq:radiusenergy`

The proof of Lemma `lem:blocks`: "Lemma `lem:localization` at the length `n ≥ N/(8K)` gives
`R_i(j, k) ≤ O_2(C)`. The arrays `R_i²` are independent over `i`, so equation `eq:chainsum`, applied
to a small multiple of `R_i²`, gives equation `eq:radiusenergy`."

`radius_energy_of_chainSum` is this argument at a fixed length: the moments of `R_i(j, k)`
(`Modulus.lintegral_radius_pow_le`), the independent versions of the arrays
(`Modulus.exists_radius_versions`), and equation `eq:chainsum` for `R̂_i²/λ`, `λ = 1 + C'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Blocks

open Contracts

variable {m : ℕ}

/-- **Equation `eq:radiusenergy` at a fixed length**, from the moments of the radii, given by
equation `eq:localization` for the pairs of cubes, and equation `eq:chainsum`. -/
theorem radius_energy_of_chainSum (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {K : ℕ}
    {n W CL C : ℝ} (hn : 0 < n) (hW : 0 < W) (hCL : 0 < CL)
    (hloc : ∀ (i : ℕ) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ n / 2 →
      Cited.IsOs X.P 2 CL (fun ω => 1 + W⁻¹ *
        maxSegmentDeviation ((Profiles.gridPair n W i j k).slab.density b (X.ρ ω))
          (Profiles.gridPair n W i j k).slab.set (Profiles.gridPair n W i j k).first
          (Profiles.gridPair n W i j k).second))
    (hC : Profiles.ChainSumBound X b K n W C) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin K,
        X.R b n W ω i (X.J b K n W 0 ω i.castSucc) (X.J b K n W 0 ω i.succ) ^ 2) ∂X.P ≤
      ENNReal.ofReal ((1 + Modulus.radiusMomentConst m CL) * (C * K)) := by
  have hC' : 0 ≤ Modulus.radiusMomentConst m CL := Modulus.radiusMomentConst_nonneg m hCL.le
  set lam : ℝ := 1 + Modulus.radiusMomentConst m CL with hlam
  have hlam1 : 1 ≤ lam := by linarith only [hC', hlam]
  obtain ⟨Rv, hRm, -, hRind, hRae⟩ := Modulus.exists_radius_versions X hb hn hW K
  -- the arrays `R̂_i²`
  set T : Fin K → X.Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ := fun i ω j k =>
    ENNReal.ofReal (Rv i ω j k ^ 2) with hT
  have hTm : ∀ i j k, Measurable fun ω => T i ω j k := fun i j k =>
    ((hRm i j k).pow_const 2).ennreal_ofReal
  have hind : iIndepFun T X.P := by
    have hg : Measurable fun r : (Fin m → ℤ) → (Fin m → ℤ) → ℝ =>
        fun j k => ENNReal.ofReal (r j k ^ 2) :=
      Measurable.of_eval fun j => Measurable.of_eval fun k =>
        (((measurable_pi_apply j).eval (a := k)).pow_const 2).ennreal_ofReal
    exact hRind.comp (fun _ r j k => ENNReal.ofReal (r j k ^ 2)) fun _ => hg
  have hmom : ∀ i j k, (j, k) ∈ (Set.univ : Set ((Fin m → ℤ) × (Fin m → ℤ))) →
      ∫⁻ ω, (T i ω j k - ENNReal.ofReal (lam * zNorm (j - k) ^ 2)) ^ (4 * (m + 1)) ∂X.P ≤
        ENNReal.ofReal (lam ^ (4 * (m + 1))) := fun i j k _ => by
    have hpt : ∀ᵐ ω ∂X.P, (T i ω j k - ENNReal.ofReal (lam * zNorm (j - k) ^ 2)) ^ (4 * (m + 1)) ≤
        ENNReal.ofReal (X.R b n W ω i j k ^ (8 * (m + 1))) := by
      filter_upwards [hRae] with ω hω
      refine (pow_le_pow_left₀ bot_le tsub_le_self _).trans_eq ?_
      rw [hT]
      simp only
      rw [hω i j k, ← ENNReal.ofReal_pow (sq_nonneg _), ← pow_mul]
      congr 2
      ring
    refine (lintegral_mono_ae hpt).trans
      ((Modulus.lintegral_radius_pow_le X hb hW hCL i j k (hloc i j k)).trans
        (ENNReal.ofReal_le_ofReal ?_))
    calc Modulus.radiusMomentConst m CL ≤ lam := by linarith only [hlam]
      _ ≤ lam ^ (4 * (m + 1)) := le_self_pow₀ hlam1 (by omega)
  have hsel := Profiles.lintegral_sum_le_of_chainSum hC (MeasurePreserving.id X.P)
    (by linarith only [hlam1]) T hTm hind Set.univ hmom fun _ _ => Set.mem_univ _
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hsel
  filter_upwards [hRae] with ω hω
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  exact Finset.sum_congr rfl fun i _ => by rw [hT]; simp only [hω, id]

/-- **Lemma `lem:blocks`, equation `eq:radiusenergy`**, from Lemma `lem:localization` and
equation `eq:chainsum`. -/
theorem radiusEnergyStatement_of (hL : LocalizationStatement.{u}) (hC : ChainSumStatement.{u}) :
    RadiusEnergyStatement.{u} := by
  intro m hm X hX b hb Cstar hCstar
  obtain ⟨CL, hCL, HL⟩ := hL m hm X hX b hb Cstar hCstar
  obtain ⟨CC, hCC, HC⟩ := hC m hm X hX b hb Cstar hCstar
  have hCL' : 0 < 2 + CL := by positivity
  have hC' := Modulus.radiusMomentConst_nonneg m hCL'.le
  refine ⟨(1 + Modulus.radiusMomentConst m (2 + CL)) * CC, by positivity, fun K => ?_⟩
  by_cases hK : 10 ≤ K
  swap
  · exact ⟨0, fun A N _ hS => absurd hS.1 hK⟩
  have hK8 : (1 : ℝ) ≤ 8 * K := by
    exact_mod_cast (by omega : 1 ≤ 8 * K)
  have hc₁ : (0 : ℝ) < 1 / (8 * K) := by positivity
  have hc₁' : 1 / (8 * (K : ℝ)) ≤ 1 := (div_le_one (by linarith only [hK8])).mpr hK8
  obtain ⟨NL, HNL⟩ := HL (1 / (8 * K)) hc₁ hc₁' K
  obtain ⟨NC, HNC⟩ := HC (1 / (8 * K)) hc₁ K
  refine ⟨max NL NC, fun A N hN hS ℓ hℓ₁ hℓ₂ => ?_⟩
  have hNL : NL ≤ N := le_trans (le_max_left _ _) hN
  have hNC : NC ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hn₁, hn₄, hn, -, hW⟩ := scales_of_standing hS hℓ₁ hℓ₂
  have hnN : ℓ / K ≤ N := hn₄.trans (by linarith only [hS.2.2.1])
  have h := radius_energy_of_chainSum X hb hn hW hCL'
    (fun i _ _ hjk => isOs_one_add_gridPair X hn hW hCL (HNL A N hNL hS _ hn₁ hnN) i hjk)
    (HNC A N hNC hS K (ℓ / K) (by omega) hn₁ hn₄)
  rwa [← mul_assoc] at h

end IsotropicVariance.Paper.Proofs.Blocks
