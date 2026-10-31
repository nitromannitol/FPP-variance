/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusMoments
public import IsotropicVariance.Paper.Proofs.Profiles.OsTools
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import IsotropicVariance.Statements.Cited.IsOsMeasureGeLe
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The event `E` and the Cauchy–Schwarz inequality

The first paragraph of the proof of Lemma `lem:modulus`. Let `Z ≥ 0` be the supremum inside
the expectation of equation `eq:modulus`, and `E` the event that the normalized deviation `Y` is at
least `θ_Y t`. Then `P[E] ≤ 2e^{−t²}`, and the Cauchy–Schwarz inequality bounds
`E[Z^{k} 1_E]^{1/k}` by `E[Z^{2k}]^{1/(2k)} P[E]^{1/(2k)}`. With the bound of `Z` off `E`, this
gives the `L^k` bound `eLpNorm_le_of_off_event`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Modulus

open Cited Infra.Os

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The exponents of the Cauchy–Schwarz inequality. -/
lemma holderTriple_two_mul {k : ℕ} (hk : k ≠ 0) :
    ENNReal.HolderTriple ((2 * k : ℕ) : ℝ≥0∞) ((2 * k : ℕ) : ℝ≥0∞) (k : ℝ≥0∞) := by
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk
  have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  refine ⟨?_⟩
  rw [Nat.cast_mul, Nat.cast_two, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
    ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]

/-- **The `L^k` bound from the bound off `E`**. Here `Z ≤ 2S`, `S ≤
O_1(θ_S)`, `Y ≤ O_2(θ_Y)`, and `Z ≤ 4U₊ + c` off the event `E = {θ_Y t ≤ Y}`. -/
theorem eLpNorm_le_of_off_event [IsProbabilityMeasure P] {Z U S Y : Ω → ℝ} {θU θS θY c t : ℝ}
    (hZ : AEMeasurable Z P) (hU : IsOs P 1 θU U) (hS : IsOs P 1 θS S) (hY : IsOs P 2 θY Y)
    (hθU : 0 < θU) (hθS : 0 < θS) (hθY : 0 < θY) (hc : 0 ≤ c) (ht : 0 ≤ t) (hS0 : ∀ ω, 0 ≤ S ω)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZS : ∀ ω, Z ω ≤ 2 * S ω)
    (hoff : ∀ ω, Y ω < θY * t → Z ω ≤ 4 * max (U ω) 0 + c) {k : ℕ} (hk : 1 ≤ k) :
    eLpNorm Z k P ≤ ENNReal.ofReal (4 * (momentConst 1 k * θU) + c +
      2 * (momentConst 1 (2 * k) * θS) * (2 * Real.exp (-t ^ 2)) ^ (1 / (2 * (k : ℝ)))) := by
  have hk1 : (1 : ℝ≥0∞) ≤ k := by exact_mod_cast hk
  have hk0 : k ≠ 0 := by omega
  have hk2 : 1 ≤ 2 * k := by omega
  have hk20 : ((2 * k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show 2 * k ≠ 0 by omega)
  have hr : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  set E : Set Ω := Y ⁻¹' Ici (θY * t) with hE
  have hEm : NullMeasurableSet E P := hY.1.nullMeasurable measurableSet_Ici
  -- `P[E] ≤ 2e^{−t²}`
  have hPE : P E ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2)) := by
    have h := Cited.IsOs.measure_ge_le two_pos hθY hY _ ht
    rwa [Real.rpow_two] at h
  -- the Cauchy–Schwarz inequality
  set g : Ω → ℝ := E.indicator fun _ => (1 : ℝ) with hg
  have hgm : AEStronglyMeasurable g P := aestronglyMeasurable_const.indicator₀ hEm
  have hgn : eLpNorm g ((2 * k : ℕ) : ℝ≥0∞) P ≤
      ENNReal.ofReal ((2 * Real.exp (-t ^ 2)) ^ (1 / (2 * (k : ℝ)))) := by
    rw [hg, eLpNorm_indicator_const₀ hEm hk20 (ENNReal.natCast_ne_top _), enorm_one, one_mul,
      ENNReal.toReal_natCast, hr,
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    exact ENNReal.rpow_le_rpow hPE (by positivity)
  have hZn : eLpNorm Z ((2 * k : ℕ) : ℝ≥0∞) P ≤
      ENNReal.ofReal (momentConst 1 (2 * k) * (2 * θS)) := by
    have hS2 : IsOs P 1 (2 * θS) (fun ω => 2 * S ω) := (isOs_mul_iff two_pos).mpr hS
    refine (eLpNorm_mono_real hZ.aestronglyMeasurable fun ω => ?_).trans
      (eLpNorm_le_of_isOs hS2 one_pos (by positivity) (fun ω => by have := hS0 ω; positivity) hk2)
    rw [Real.norm_of_nonneg (hZ0 ω)]
    exact hZS ω
  have hCS : eLpNorm (g • Z) k P ≤
      eLpNorm g ((2 * k : ℕ) : ℝ≥0∞) P * eLpNorm Z ((2 * k : ℕ) : ℝ≥0∞) P :=
    haveI := holderTriple_two_mul hk0
    eLpNorm_smul_le_mul_eLpNorm hgm hZ.aestronglyMeasurable
  have hmc := momentConst_pos 1 (2 * k)
  have htail : 0 ≤ (2 * Real.exp (-t ^ 2)) ^ (1 / (2 * (k : ℝ))) := by positivity
  have hbad : eLpNorm (g • Z) k P ≤ ENNReal.ofReal
      (2 * (momentConst 1 (2 * k) * θS) * (2 * Real.exp (-t ^ 2)) ^ (1 / (2 * (k : ℝ)))) := by
    refine hCS.trans ((mul_le_mul' hgn hZn).trans_eq ?_)
    rw [← ENNReal.ofReal_mul htail]
    congr 1
    ring
  -- the bound of `Z`
  have e1 := eLpNorm_le_of_isOs (Profiles.isOs_pos hU) one_pos hθU (fun ω => le_max_right _ _) hk
  have e3 : eLpNorm (fun _ : Ω => c) k P = ENNReal.ofReal c := by
    rw [eLpNorm_const c (by exact_mod_cast hk0) (IsProbabilityMeasure.ne_zero P), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg hc]
  set f₁ : Ω → ℝ := fun ω => max (U ω) 0 with hf₁
  have hle : eLpNorm Z k P ≤ eLpNorm ((4 : ℝ) • f₁ + (fun _ => c) + g • Z) k P := by
    refine eLpNorm_mono_real hZ.aestronglyMeasurable fun ω => ?_
    rw [Real.norm_of_nonneg (hZ0 ω)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, hf₁]
    have hU0 : 0 ≤ max (U ω) 0 := le_max_right _ _
    by_cases h : Y ω < θY * t
    · have hmem : ω ∉ E := fun h' => absurd (show θY * t ≤ Y ω from h') (not_le.mpr h)
      have hgω : g ω = 0 := indicator_of_notMem hmem _
      rw [hgω, zero_mul]
      linarith only [hoff ω h]
    · have hmem : ω ∈ E := not_lt.mp h
      have hgω : g ω = 1 := indicator_of_mem hmem _
      rw [hgω, one_mul]
      linarith only [hU0, hc]
  refine hle.trans ((eLpNorm_add_le hk1).trans ?_)
  refine (add_le_add_left (eLpNorm_add_le hk1) _).trans ?_
  rw [eLpNorm_const_smul, e3, Real.enorm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  have hm1 := momentConst_pos 1 k
  calc ENNReal.ofReal 4 * eLpNorm f₁ k P + ENNReal.ofReal c + eLpNorm (g • Z) k P
      ≤ ENNReal.ofReal 4 * ENNReal.ofReal (momentConst 1 k * θU) + ENNReal.ofReal c +
        ENNReal.ofReal
          (2 * (momentConst 1 (2 * k) * θS) * (2 * Real.exp (-t ^ 2)) ^ (1 / (2 * (k : ℝ)))) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) hc,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

end IsotropicVariance.Paper.Proofs.Modulus
