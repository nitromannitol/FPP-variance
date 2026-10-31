/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Resampling.Slabs
import IsotropicVariance.Paper.Proofs.BlockReplacement.GainVersion

/-!
# The arrays `Y_i` are independent

The text before Lemma `lem:blocks`: "The arrays `Y_1, …, Y_K` are independent."

The array `Y_i` is a function of the old noise and of the new noises of the blocks of the slab `i`,
all read in the slab `i`, and these are independent over `i` (`Setting.iIndep_blockResampling`).
The passage times are determined by the noise only almost surely, so the statement is for versions:
`exists_Y_versions` gives arrays `Y'_i`, measurable for `Setting.slabSigma`, independent over `i`,
with `Y_i(j, k) = Y'_i(j, k)` almost surely at each pair `j, k`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Blocks

variable {m : ℕ}

/-- `Setting.slabSigma` is below the σ-algebra of the resampling law. -/
theorem slabSigma_le (X : Setting.{u} m) (n : ℝ) (i : ℕ) :
    X.slabSigma n i ≤ (inferInstance : MeasurableSpace (X.Ω × (BlockIdx m → X.Ω))) :=
  sup_le ((MeasurableSpace.comap_mono (X.info_le _)).trans measurable_fst.comap_le)
    (iSup_le fun _ => (MeasurableSpace.comap_mono (X.info_le _)).trans
      ((measurable_pi_apply _).comp measurable_snd).comap_le)

/-- **The arrays `Y_i` are independent** (text before Lemma `lem:blocks`): they have versions
`Y'_i`, measurable for the information of the slab `i`, independent over the slabs. Here `blocks i`
is the set of the blocks of the slab `i`. -/
theorem exists_Y_versions (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {n W : ℝ}
    (hn : 0 < n) (hW : 0 < W) (Qn : ℝ) {L : ℕ} (σ : X.BlockInfo n W L)
    (blocks : ℕ → Set (Fin m → ℤ)) :
    ∃ Y' : ℕ → X.Ω × (BlockIdx m → X.Ω) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞,
      (∀ i, Measurable[X.slabSigma n i] (Y' i)) ∧
      iIndepFun Y' (X.blockResampling n W L σ.1) ∧
      ∀ i j k, ∀ᵐ p ∂(X.blockResampling n W L σ.1),
        X.Y b n W Qn i j k (blocks i) Prod.fst
          (fun z (p : X.Ω × (BlockIdx m → X.Ω)) => p.2 (i, z)) p = Y' i p j k := by
  have hold := X.measurePreserving_old (fun p : BlockIdx m => block n W L p.1 p.2) σ.1
  have hnew : ∀ c : BlockIdx m, MeasurePreserving (fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 c)
      (X.blockResampling n W L σ.1) X.P := fun c =>
    X.measurePreserving_new (G := fun p : BlockIdx m => block n W L p.1 p.2) (σ := σ.1) (i := c)
      ((σ.2 c).trans (X.info_le _))
  have hg := fun (i : ℕ) (j k : Fin m → ℤ) (z : Fin m → ℤ) =>
    BlockReplacement.exists_measurable_blockGain_ae X hb hn hW i j k hold (hnew (i, z))
  choose g hgm hgae using hg
  let Y' : ℕ → X.Ω × (BlockIdx m → X.Ω) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ :=
    fun i p j k => if W * zNorm (k - j) ≤ n / 2 then
      ∑' z : blocks i, ENNReal.ofReal ((g i j k z p / Qn) ^ 2) else 0
  have hmeas : ∀ i, Measurable[X.slabSigma n i] (Y' i) := by
    intro i
    let _ms : MeasurableSpace (X.Ω × (BlockIdx m → X.Ω)) := X.slabSigma n i
    refine Measurable.of_eval fun j => Measurable.of_eval fun k => ?_
    by_cases h : W * zNorm (k - j) ≤ n / 2
    · simp only [Y', h, ↓reduceIte]
      refine Measurable.tsum fun z => ?_
      have hle : (X.info (chainSlab n 0 i).set).comap (Prod.fst : X.Ω × (BlockIdx m → X.Ω) → X.Ω) ⊔
          (X.info (chainSlab n 0 i).set).comap (fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 (i, z)) ≤
          X.slabSigma n i :=
        sup_le le_sup_left (le_trans (le_iSup (fun z => (X.info (chainSlab n 0 i).set).comap
          (fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 (i, z))) z) le_sup_right)
      have := (hgm i j k z).mono hle le_rfl
      exact ENNReal.measurable_ofReal.comp ((this.div_const Qn).pow_const 2)
    · simp only [Y', h, ↓reduceIte]
      exact measurable_const
  refine ⟨Y', hmeas, X.iIndepFun_blockResampling hn W L σ.2 hmeas, fun i j k => ?_⟩
  have := ae_all_iff.2 fun z : blocks i => hgae i j k z
  filter_upwards [this] with p hp
  simp only [Setting.Y, Y']
  split_ifs with h
  · exact tsum_congr fun z => by rw [hp z]
  · rfl

end IsotropicVariance.Paper.Proofs.Blocks
