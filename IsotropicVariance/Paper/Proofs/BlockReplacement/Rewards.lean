/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.BlockReplacement.Decoupling
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The conditional reward of a slab

`exists_condReward`: for the couplings of the blocks of a slab `i` on one probability space, an
array `y_i(j, k)` on the noise, with moments at most those of the rewards `Y_i(j, k)` of Section
`sec:gain`, measurable for the information of the slab. See the module docstring of
`IsotropicVariance.Paper.Proofs.BlockReplacement.Decoupling`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.BlockReplacement

variable {m : ℕ}

/-- An integral of `F` evaluated at a countably valued index, as a sum over the values. -/
theorem lintegral_comp_index {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [Countable Λ]
    [MeasurableSingletonClass Λ] {μ : Measure Ω} {ι : Ω → Λ} (hι : Measurable ι)
    {F : Λ → Ω → ℝ≥0∞} (hF : ∀ p, AEMeasurable (F p) μ) :
    ∫⁻ ω, F (ι ω) ω ∂μ = ∑' p, ∫⁻ ω in ι ⁻¹' {p}, F p ω ∂μ := by
  have h : ∀ ω, F (ι ω) ω = ∑' p, (ι ⁻¹' {p}).indicator (F p) ω := fun ω => by
    rw [tsum_eq_single (ι ω)]
    · rw [indicator_of_mem (by simp)]
    · intro p hp
      exact indicator_of_notMem (fun h => hp (by simpa using h.symm)) _
  simp_rw [h]
  rw [lintegral_tsum fun p => (hF p).indicator (hι (measurableSet_singleton p))]
  exact tsum_congr fun p => lintegral_indicator (hι (measurableSet_singleton p)) _

/-- The rewards are almost everywhere measurable. -/
theorem aemeasurable_Y (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {s W : ℝ} (hs : 0 < s)
    (hW : 0 < W) (Qn : ℝ) {L : ℕ} (i : ℕ) (blocks : Set (Fin m → ℤ))
    (fam : X.BlockCouplingFamily s W L i blocks) (j k : Fin m → ℤ) :
    AEMeasurable (X.Y b s W Qn i j k blocks fam.old fam.new) fam.P' := by
  by_cases hadm : W * zNorm (k - j) ≤ s / 2
  · have h : X.Y b s W Qn i j k blocks fam.old fam.new =
        fun ω => ∑' z : blocks, sqGain X b s W Qn i j k (fam.old ω) (fam.new z ω) := by
      funext ω
      simp only [Setting.Y, hadm, ↓reduceIte, sqGain]
    rw [h]
    refine AEMeasurable.tsum fun z => ?_
    have hcpl := fam.isBlockCoupling z.1 z.2
    exact aemeasurable_sqGain X hb hs hW Qn i j k hcpl.measurePreserving_old
      hcpl.measurePreserving_new
  · have h : X.Y b s W Qn i j k blocks fam.old fam.new = 0 := by
      funext ω
      simp [Setting.Y, hadm]
    rw [h]
    exact aemeasurable_const

/-- **The conditional reward of one slab**: arrays on the noise, measurable for the information
of the slab, whose integrals over the events of the slabs are those of the reward. -/
theorem exists_condReward (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {s W : ℝ} (hs : 0 < s)
    (hW : 0 < W) (Qn : ℝ) {L K : ℕ} (i : Fin K) (o : Fin m → Fin L)
    (fam : X.BlockCouplingFamily s W L i {z | IsBlockIndex L o z})
    (hfin : ∀ j k : Fin m → ℤ, W * zNorm (k - j) ≤ s / 2 →
      ∫⁻ ω, X.Y b s W Qn i j k {z | IsBlockIndex L o z} fam.old fam.new ω ∂fam.P' ≠ ∞) :
    ∃ y : (Fin m → ℤ) → (Fin m → ℤ) → X.Ω → ℝ≥0∞,
      (∀ j k, Measurable[X.info (chainSlab s 0 i).set] (y j k)) ∧
      ∀ j k (A : Set X.Ω), MeasurableSet[X.info (chainSlab s 0 i).set ⊔ otherSlabsInfo X s i] A →
        ∫⁻ x in A, y j k x ∂X.P =
          ∫⁻ ω in fam.old ⁻¹' A, X.Y b s W Qn i j k {z | IsBlockIndex L o z} fam.old fam.new ω
            ∂fam.P' := by
  have key : ∀ (z : {z | IsBlockIndex L o z}) (j k : Fin m → ℤ), ∃ φ : X.Ω → ℝ≥0∞,
      Measurable[X.info (chainSlab s 0 i).set] φ ∧ (W * zNorm (k - j) ≤ s / 2 →
        ∀ A : Set X.Ω, MeasurableSet[X.info (chainSlab s 0 i).set ⊔ otherSlabsInfo X s i] A →
          ∫⁻ x in A, φ x ∂X.P =
            ∫⁻ ω in fam.old ⁻¹' A, sqGain X b s W Qn i j k (fam.old ω) (fam.new z ω) ∂fam.P') := by
    intro z j k
    by_cases hadm : W * zNorm (k - j) ≤ s / 2
    · have hcpl := fam.isBlockCoupling z.1 z.2
      have hle : ∀ ω, sqGain X b s W Qn i j k (fam.old ω) (fam.new z ω) ≤
          X.Y b s W Qn i j k {z | IsBlockIndex L o z} fam.old fam.new ω := fun ω => by
        simp only [Setting.Y, hadm, ↓reduceIte]
        exact ENNReal.le_tsum (f := fun z : {z | IsBlockIndex L o z} =>
          ENNReal.ofReal ((X.blockGain b s W i j k (fam.old ω) (fam.new z ω) / Qn) ^ 2)) z
      have hf : ∫⁻ ω, sqGain X b s W Qn i j k (fam.old ω) (fam.new z ω) ∂fam.P' ≠ ∞ :=
        ne_top_of_le_ne_top (hfin j k hadm) (lintegral_mono hle)
      obtain ⟨φ, hφ, hid⟩ := exists_condGain X hb hs hW Qn i j k hcpl hf
      exact ⟨φ, hφ, fun _ => hid⟩
    · exact ⟨0, measurable_const, fun h => absurd h hadm⟩
  choose φ hφm hφid using key
  refine ⟨fun j k => if W * zNorm (k - j) ≤ s / 2 then fun x => ∑' z, φ z j k x else 0, ?_, ?_⟩
  · intro j k
    by_cases hadm : W * zNorm (k - j) ≤ s / 2
    · simp only [hadm, ↓reduceIte]
      let _ : MeasurableSpace X.Ω := X.info (chainSlab s 0 i).set
      exact Measurable.tsum fun z => hφm z j k
    · simp only [hadm, ↓reduceIte]
      exact measurable_const
  · intro j k A hA
    by_cases hadm : W * zNorm (k - j) ≤ s / 2
    · have hY : X.Y b s W Qn i j k {z | IsBlockIndex L o z} fam.old fam.new =
          fun ω => ∑' z : {z | IsBlockIndex L o z},
            sqGain X b s W Qn i j k (fam.old ω) (fam.new z ω) := by
        funext ω
        simp only [Setting.Y, hadm, ↓reduceIte, sqGain]
      have hφ' : ∀ z, AEMeasurable (φ z j k) (X.P.restrict A) := fun z =>
        ((hφm z j k).mono (X.info_le (chainSlab s 0 i).set) le_rfl).aemeasurable
      have hg' : ∀ z : {z | IsBlockIndex L o z}, AEMeasurable
          (fun ω => sqGain X b s W Qn i j k (fam.old ω) (fam.new z ω))
          (fam.P'.restrict (fam.old ⁻¹' A)) := fun z =>
        (aemeasurable_sqGain X hb hs hW Qn i j k
          (fam.isBlockCoupling z.1 z.2).measurePreserving_old
          (fam.isBlockCoupling z.1 z.2).measurePreserving_new).restrict
      have e1 := lintegral_tsum hφ'
      have e2 := lintegral_tsum hg'
      simp only [hadm, ↓reduceIte, hY]
      refine e1.trans (Eq.trans ?_ e2.symm)
      exact tsum_congr fun z => hφid z j k hadm A hA
    · simp [hadm, Setting.Y]

end IsotropicVariance.Paper.Proofs.BlockReplacement
