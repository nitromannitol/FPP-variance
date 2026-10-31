/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.Gain.InfluenceCS
public import CurvatureVariance.Paper.Proofs.Gain.InfluenceMeet
public import CurvatureVariance.Paper.Proofs.Gain.InfluenceCount
public import CurvatureVariance.Paper.Proofs.Gain.InfluenceTranslate
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Gain.RRTuples

/-!
# The `L¹` influence bound (Lemma `lem:fewtranslates`)

The ingredients of the second bound of Lemma `lem:fewtranslates`, for a block `G` of slab `i + 1`:
`measure_targetMin_ne_le` (the probability that resampling the block changes `F` is at most twice
the probability that every minimizing tube meets it), `inv_numTranslates_mul_le`, and
`averagedMin_eq_zero_of_forall_not`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- **Resampling a block changes `F` with probability at most twice that of every minimizing tube
meeting it** (the proof of [AB26, Lemma 6.4]: the tube for the old weights or the one for the new
weights). -/
theorem measure_targetMin_ne_le {M : Model m} (hM : M.Standing) {Cd T : ℝ}
    (hT : TubeBound M Cd T)
    {K : ℕ} {A : ℝ} (hA : 1 ≤ A) {n ℓ : ℕ} (hn : 1 ≤ n) {y : Fin m → ℤ}
    (ht : ‖targetSlope ℓ y‖ ≤ T) {L : ℕ} (i : Fin K) (o g : Fin m → ℤ) :
    (M.P.prod M.P) {p : Config m × Config m | targetMin M p.1 n K ℓ y ≠
        targetMin M (resample (block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) o g)
          p.1 p.2) n K ℓ y} ≤
      2 * M.P {z : Config m | AllTubesMeet M K A Cd n ℓ y L i o g z} := by
  have := hM.probP
  set G := block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) o g with hG
  set S := {z : Config m | AllTubesMeet M K A Cd n ℓ y L i o g z} with hSdef
  have hS : MeasurableSet S := measurableSet_allTubesMeet M K A Cd n ℓ y L i o g
  have hres := measurePreserving_resample hM G
  have hfst : MeasurePreserving (Prod.fst : Config m × Config m → Config m) (M.P.prod M.P) M.P :=
    measurePreserving_fst
  have hgood := Gain.ae_exists_isSlabGeodesic hM
  have h1 := hfst.quasiMeasurePreserving.ae hgood
  have h2 := hres.quasiMeasurePreserving.ae hgood
  have hsub : {p : Config m × Config m | targetMin M p.1 n K ℓ y ≠
      targetMin M (resample G p.1 p.2) n K ℓ y} ≤ᵐ[M.P.prod M.P]
      ((Prod.fst ⁻¹' S) ∪ ((fun p : Config m × Config m => resample G p.1 p.2) ⁻¹' S) :
        Set (Config m × Config m)) := by
    filter_upwards [h1, h2] with p hp1 hp2
    intro hne
    by_contra hcon
    have hcon' : ¬ p.1 ∈ S ∧ ¬ resample G p.1 p.2 ∈ S := by
      simpa only [Set.mem_union, Set.mem_preimage, not_or] using hcon
    exact hne (targetMin_resample_eq_of_not_allTubesMeet hT hA hn ht i o g hp1 hp2
      hcon'.1 hcon'.2).symm
  calc _ ≤ (M.P.prod M.P) ((Prod.fst ⁻¹' S) ∪
        ((fun p : Config m × Config m => resample G p.1 p.2) ⁻¹' S)) := measure_mono_ae hsub
    _ ≤ (M.P.prod M.P) (Prod.fst ⁻¹' S) +
        (M.P.prod M.P) ((fun p : Config m × Config m => resample G p.1 p.2) ⁻¹' S) :=
      measure_union_le _ _
    _ = M.P S + M.P S := by
      rw [hfst.measure_preimage hS.nullMeasurableSet, hres.measure_preimage hS.nullMeasurableSet]
    _ = 2 * M.P S := (two_mul _).symm

/-- `V⁻¹ · 2(3 + 3√(CK)) ≤ 6(1 + √C) K^{−1/6}` for `V = ⌈K^{2/3}⌉`, the bound of the second
paragraph of the proof of [AB26, Lemma 6.4]: "for an independent `m` uniform in
`{0, …, ⌈K^{2/3}⌉ − 1}`, the block `G` meets either tube of `F_m` with probability at most
`2CK^{1/2}/⌈K^{2/3}⌉ ≤ CK^{−1/6}`". -/
theorem inv_numTranslates_mul_le {K : ℕ} (hK : 1 ≤ K) {C : ℝ} (hC : 0 ≤ C) :
    (numTranslates K : ℝ≥0∞)⁻¹ * (2 * ENNReal.ofReal (3 + 3 * Real.sqrt (C * K))) ≤
      ENNReal.ofReal (6 * (1 + Real.sqrt C) * (K : ℝ) ^ (-(1 : ℝ) / 6)) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hVpos := Gain.numTranslates_pos hK
  have hV0 : (0 : ℝ) < (numTranslates K : ℝ) := by exact_mod_cast hVpos
  have hVge : (K : ℝ) ^ ((2 : ℝ) / 3) ≤ (numTranslates K : ℝ) := Nat.le_ceil _
  have hL : (numTranslates K : ℝ≥0∞)⁻¹ * (2 * ENNReal.ofReal (3 + 3 * Real.sqrt (C * K))) =
      ENNReal.ofReal ((numTranslates K : ℝ)⁻¹ * (2 * (3 + 3 * Real.sqrt (C * K)))) := by
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hV0.le), ENNReal.ofReal_inv_of_pos hV0,
      ENNReal.ofReal_natCast, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  rw [hL]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsK : 1 ≤ Real.sqrt K := Real.one_le_sqrt.2 hK1
  have hsC := Real.sqrt_nonneg C
  have hsCK : Real.sqrt (C * K) = Real.sqrt C * Real.sqrt K := Real.sqrt_mul hC _
  have hnum : 2 * (3 + 3 * Real.sqrt (C * K)) ≤ 6 * (1 + Real.sqrt C) * Real.sqrt K := by
    rw [hsCK]; nlinarith
  have hpow : Real.sqrt K * (K : ℝ) ^ (-(2 : ℝ) / 3) = (K : ℝ) ^ (-(1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hK0]; norm_num
  have hVinv : (numTranslates K : ℝ)⁻¹ ≤ (K : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [show (-(2 : ℝ) / 3) = -((2 : ℝ) / 3) by ring, Real.rpow_neg hK0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hK0 _) hVge
  calc (numTranslates K : ℝ)⁻¹ * (2 * (3 + 3 * Real.sqrt (C * K)))
      ≤ (K : ℝ) ^ (-(2 : ℝ) / 3) * (6 * (1 + Real.sqrt C) * Real.sqrt K) :=
        mul_le_mul hVinv hnum (by positivity) (by positivity)
    _ = 6 * (1 + Real.sqrt C) * (Real.sqrt K * (K : ℝ) ^ (-(2 : ℝ) / 3)) := by ring
    _ = 6 * (1 + Real.sqrt C) * (K : ℝ) ^ (-(1 : ℝ) / 6) := by rw [hpow]

/-- Without admissible tuples, the averaged minimum vanishes. -/
theorem averagedMin_eq_zero_of_forall_not {M : Model m} {K : ℕ} {A : ℝ} {L n ℓ : ℕ}
    {y : Fin m → ℤ} (h : ∀ Y, ¬ IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y)
    (ω : Config m) : averagedMin M K A L ω n ℓ y = 0 := by
  unfold averagedMin
  have hv : ∀ v ∈ Finset.range (numTranslates K), translatedMin M ω n K ℓ y
      (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m) = 0 := by
    intro v _
    rw [Gain.translatedMin_eq_targetMin, targetMin, Gain.slabMin_eq_top_of_forall_not h,
      ENNReal.toReal_top]
  rw [Finset.sum_eq_zero hv, mul_zero]

end CurvatureVariance.Paper.Gain
