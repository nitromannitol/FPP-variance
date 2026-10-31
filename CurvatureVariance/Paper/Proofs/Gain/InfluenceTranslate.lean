/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.AVEnergy
import CurvatureVariance.Paper.Proofs.Moments.Basic

/-!
# Translates and resampled weights

Translation covariance (stationarity, in the proofs of Lemmas `lem:residual` and
`lem:fewtranslates`) for the `L¹` influence bound. Here `F_v = translatedMin … (vLw e₂)` is the
minimum `F` translated by `vLw e₂`, and `G' = G − vLw e₂`.

* `measure_translatedMin_ne_eq`: resampling the block `G` changes `F_v` with the probability that
  resampling the block `G'` changes `F`. The translate of a block of index `g` is the block of
  index `g − v e₂`.
* `measurePreserving_resample`: the resampled weights `ω^{G,ω'}` have the law `P` under `P ⊗ P`.
* `tsum_average_esTerm_translatedMin_eq`: summed over the blocks of a slab, the average over
  `v` of the Efron–Stein terms of the `F_v` equals that of `F` (as in the step `htr` of the proof of
  `Gain.tsum_esTerm_averagedMin_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- **Translation covariance of the changes** (the proof of Lemma `lem:fewtranslates`):
resampling the block `g` changes `F_v` with the probability that resampling the block `g − v e₂`
changes `F`. -/
theorem measure_translatedMin_ne_eq {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {L n : ℕ}
    (hw : 0 < wInt M K A n) (ℓ : ℕ) (y : Fin m → ℤ) (i v : ℕ) (o g : Fin m → ℤ) :
    (M.P.prod M.P) {p : Config m × Config m |
      translatedMin M p.1 n K ℓ y (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m) ≠
        translatedMin M (resample (block n (wInt M K A n) L (targetSlope ℓ y) i o g) p.1 p.2)
          n K ℓ y (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m)} =
    (M.P.prod M.P) {p : Config m × Config m |
      targetMin M p.1 n K ℓ y ≠
        targetMin M (resample (block n (wInt M K A n) L (targetSlope ℓ y) i o
          (g - (v : ℤ) • transverseUnit m)) p.1 p.2) n K ℓ y} := by
  have := hM.probP
  set a : Vertex m := ((0 : ℤ), ((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m) with ha
  set G' := block n (wInt M K A n) L (targetSlope ℓ y) i o (g - (v : ℤ) • transverseUnit m)
  have hθ := Moments.standing_measurePreserving_translate hM a
  have hΘ := hθ.prod hθ
  have hF := Responses.measurable_targetMin M n K ℓ y
  have hS : MeasurableSet {p : Config m × Config m |
      targetMin M p.1 n K ℓ y ≠ targetMin M (resample G' p.1 p.2) n K ℓ y} :=
    (measurableSet_eq_fun (hF.comp measurable_fst)
      (hF.comp (Responses.measurable_resample G'))).compl
  rw [← hΘ.measure_preimage hS.nullMeasurableSet]
  congr 1
  ext p
  show _ ≠ _ ↔ targetMin M (translate a p.1) n K ℓ y ≠
    targetMin M (resample G' (translate a p.1) (translate a p.2)) n K ℓ y
  rw [Gain.translatedMin_eq_targetMin, Gain.translatedMin_eq_targetMin, Gain.translate_resample,
    Gain.setOf_map_add_mem_block hw]

/-- The resampled weights `ω^{G,ω'}` have the law `P` under `P ⊗ P`. -/
theorem measurePreserving_resample {M : Model m} (hM : M.Standing) (G : Set (Sym2 (Vertex m))) :
    MeasurePreserving (fun p : Config m × Config m => resample G p.1 p.2) (M.P.prod M.P) M.P := by
  have := hM.probP
  have := hM.probF
  exact measurePreserving_fst.comp (Responses.measurePreserving_exchange hM.iid G)

/-- Summed over the blocks of a slab, the Efron–Stein terms of `F_v` equal those of `F`
(translation covariance; the step `htr` of `Gain.tsum_esTerm_averagedMin_le`). -/
theorem tsum_esTerm_translatedMin_eq {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {L n : ℕ}
    (hw : 0 < wInt M K A n) (ℓ : ℕ) (y : Fin m → ℤ) (i : ℕ) (o : Fin m → ℤ) (v : ℕ) :
    ∑' g : Fin m → ℤ, esTerm M.P (fun ω => translatedMin M ω n K ℓ y
        (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
        (block n (wInt M K A n) L (targetSlope ℓ y) i o g) =
      ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) i o g) := by
  have hmp := Moments.standing_measurePreserving_translate hM
    (((0 : ℤ), ((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m) : Vertex m)
  simp_rw [Gain.translatedMin_eq_targetMin]
  simp_rw [Gain.esTerm_comp_translate hmp (fun ω => targetMin M ω n K ℓ y),
    Gain.setOf_map_add_mem_block hw (targetSlope ℓ y) i v o]
  exact (Equiv.subRight ((v : ℤ) • transverseUnit m)).tsum_eq
    (fun g => esTerm M.P (fun ω => targetMin M ω n K ℓ y)
      (block n (wInt M K A n) L (targetSlope ℓ y) i o g))

/-- Summed over the blocks of a slab, the average over the translates of the Efron–Stein terms of
the `F_v` equals the sum for `F`. -/
theorem tsum_average_esTerm_translatedMin_eq {M : Model m} (hM : M.Standing) {K : ℕ}
    (hK : 1 ≤ K) {A : ℝ} {L n : ℕ} (hw : 0 < wInt M K A n) (ℓ : ℕ) (y : Fin m → ℤ) (i : ℕ)
    (o : Fin m → ℤ) :
    ∑' g : Fin m → ℤ, (numTranslates K : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range (numTranslates K),
        esTerm M.P (fun ω => translatedMin M ω n K ℓ y
          (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
          (block n (wInt M K A n) L (targetSlope ℓ y) i o g) =
      ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) i o g) := by
  have hV := Gain.numTranslates_pos hK
  rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [tsum_esTerm_translatedMin_eq hM hw ℓ y i o]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hV.ne') (ENNReal.natCast_ne_top _), one_mul]

end CurvatureVariance.Paper.Gain
