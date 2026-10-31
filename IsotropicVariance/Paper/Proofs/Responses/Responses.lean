/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Deterministic response bounds and exchangeability

Two steps of the argument for Lemma `lem:blocks`: the change of a slab
profile is bounded by the sum of its two errors from Euclidean distance, and exchangeability
identifies the squared change with twice the squared positive change. All integrals are
nonnegative extended integrals, so these identities do not assume integrability in advance.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

/-- The positive response of a slab is nonnegative, including an empty endpoint family. -/
lemma blockGain_nonneg (X : Setting m) (b n W : ℝ) (i : ℕ) (j k : Fin m → ℤ)
    (c c' : X.Ω) : 0 ≤ X.blockGain b n W i j k c c' :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => le_max_right _ _

/-- Two uniform profile bounds give a uniform bound on the positive slab response. -/
lemma blockGain_le_of_profiles (X : Setting m) (b n W : ℝ) (i : ℕ) (j k : Fin m → ℤ)
    (c c' : X.Ω) {a a' : ℝ}
    (ha : ∀ u ∈ gridCube n W 0 i j, ∀ v ∈ gridCube n W 0 (i + 1) k,
      |X.slabTime b (chainSlab n 0 i) c u v - dist u v| ≤ a)
    (ha' : ∀ u ∈ gridCube n W 0 i j, ∀ v ∈ gridCube n W 0 (i + 1) k,
      |X.slabTime b (chainSlab n 0 i) c' u v - dist u v| ≤ a') :
    X.blockGain b n W i j k c c' ≤ max a 0 + max a' 0 := by
  refine Real.iSup_le (fun u => Real.iSup_le (fun v => ?_) (by positivity)) (by positivity)
  apply max_le _ (by positivity)
  have h := abs_le.1 (ha u u.2 v v.2)
  have h' := abs_le.1 (ha' u u.2 v v.2)
  linarith only [h.1, h'.2, le_max_left a 0, le_max_left a' 0]

/-- A real square is the sum of the squares of its positive and negative parts. -/
lemma sq_eq_pos_sq_add_neg_sq (x : ℝ) :
    x ^ 2 = max x 0 ^ 2 + max (-x) 0 ^ 2 := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    ring

/-- For an exchangeable block coupling, the two positive response energies agree. -/
lemma IsBlockCoupling.lintegral_pos_sub_eq {X : Setting m} {G : Set (Pt m)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hcpl : X.IsBlockCoupling G P' old new) {f : X.Ω → ℝ} (hf : Measurable f) :
    (∫⁻ ω, ENNReal.ofReal (max (f (new ω) - f (old ω)) 0 ^ 2) ∂P') =
      ∫⁻ ω, ENNReal.ofReal (max (f (old ω) - f (new ω)) 0 ^ 2) ∂P' := by
  let g : X.Ω × X.Ω → ℝ≥0∞ := fun p => ENNReal.ofReal (max (f p.2 - f p.1) 0 ^ 2)
  have hg : Measurable g := ((hf.comp measurable_snd).sub
    (hf.comp measurable_fst)).max measurable_const |>.pow_const 2 |>.ennreal_ofReal
  have ho := hcpl.measurePreserving_old.measurable
  have hn := hcpl.measurePreserving_new.measurable
  calc
    _ = ∫⁻ p, g p ∂P'.map (fun ω => (old ω, new ω)) :=
      (lintegral_map hg (ho.prodMk hn)).symm
    _ = ∫⁻ p, g p ∂P'.map (fun ω => (new ω, old ω)) := by rw [hcpl.exchangeable]
    _ = _ := lintegral_map hg (hn.prodMk ho)

/-- Exchangeability turns the full squared response into twice its positive-part energy,
without assuming that either integral is finite. -/
theorem IsBlockCoupling.lintegral_sq_sub_eq_two_mul {X : Setting m} {G : Set (Pt m)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hcpl : X.IsBlockCoupling G P' old new) {f : X.Ω → ℝ} (hf : AEMeasurable f X.P) :
    (∫⁻ ω, ENNReal.ofReal ((f (new ω) - f (old ω)) ^ 2) ∂P') =
      2 * ∫⁻ ω, ENNReal.ofReal (max (f (new ω) - f (old ω)) 0 ^ 2) ∂P' := by
  let f₀ := hf.mk f
  have hf₀ : Measurable f₀ := hf.measurable_mk
  have ho := hcpl.measurePreserving_old.quasiMeasurePreserving.ae hf.ae_eq_mk
  have hn := hcpl.measurePreserving_new.quasiMeasurePreserving.ae hf.ae_eq_mk
  have hleft : (∫⁻ ω, ENNReal.ofReal ((f (new ω) - f (old ω)) ^ 2) ∂P') =
      ∫⁻ ω, ENNReal.ofReal ((f₀ (new ω) - f₀ (old ω)) ^ 2) ∂P' := by
    apply lintegral_congr_ae
    filter_upwards [ho, hn] with ω hω hω'
    rw [hω, hω']
  have hright : (∫⁻ ω, ENNReal.ofReal (max (f (new ω) - f (old ω)) 0 ^ 2) ∂P') =
      ∫⁻ ω, ENNReal.ofReal (max (f₀ (new ω) - f₀ (old ω)) 0 ^ 2) ∂P' := by
    apply lintegral_congr_ae
    filter_upwards [ho, hn] with ω hω hω'
    rw [hω, hω']
  rw [hleft, hright]
  have hmeas : Measurable fun ω =>
      ENNReal.ofReal (max (f₀ (new ω) - f₀ (old ω)) 0 ^ 2) :=
    (((hf₀.comp hcpl.measurePreserving_new.measurable).sub
      (hf₀.comp hcpl.measurePreserving_old.measurable)).max measurable_const).pow_const 2 |>.ennreal_ofReal
  calc
    _ = (∫⁻ ω, ENNReal.ofReal (max (f₀ (new ω) - f₀ (old ω)) 0 ^ 2) +
        ENNReal.ofReal (max (f₀ (old ω) - f₀ (new ω)) 0 ^ 2) ∂P') := by
      apply lintegral_congr
      intro ω
      rw [sq_eq_pos_sq_add_neg_sq, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), neg_sub]
    _ = (∫⁻ ω, ENNReal.ofReal (max (f₀ (new ω) - f₀ (old ω)) 0 ^ 2) ∂P') +
        ∫⁻ ω, ENNReal.ofReal (max (f₀ (old ω) - f₀ (new ω)) 0 ^ 2) ∂P' :=
      lintegral_add_left hmeas _
    _ = _ := by rw [← IsBlockCoupling.lintegral_pos_sub_eq hcpl hf₀, two_mul]

end IsotropicVariance.Paper.Proofs.Responses
