/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.BlockReplacement.Rewards

/-!
# Slab-measurable conditional rewards for averaging the offsets

`exists_conditional_rewards_info`: for the couplings of the blocks of each slab `i` on one
probability space, arrays `y_i(j, k)` on the noise, measurable for the information of the slab `i`,
hence independent over `i`, with moments at most those of the rewards `Y_i(j, k)` of Section
`sec:gain` and `Σ_i E Y_i(J_{i−1}, J_i) = E Σ_i y_i(J_{i−1}, J_i)`. See the module docstring
of `IsotropicVariance.Paper.Proofs.BlockReplacement.Decoupling`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

open BlockReplacement

variable {m : ℕ}

/-- The conditional rewards of the slabs, measurable for the information of each slab. -/
theorem exists_conditional_rewards_info (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {s W : ℝ}
    (hs : 0 < s) (hW : 0 < W) (Qn : ℝ) {K L : ℕ} (o : Fin K → Fin m → Fin L)
    (fam : (i : Fin K) → X.BlockCouplingFamily s W L i {z | IsBlockIndex L (o i) z})
    (hfin : ∀ (i : Fin K) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
      ∫⁻ ω, X.Y b s W Qn i j k {z | IsBlockIndex L (o i) z} (fam i).old (fam i).new ω
        ∂(fam i).P' ≠ ∞) :
    ∃ y : Fin K → (Fin m → ℤ) → (Fin m → ℤ) → X.Ω → ℝ≥0∞,
      (∀ (i : Fin K) j k, Measurable[X.info (chainSlab s 0 i).set] (y i j k)) ∧
      (∀ i j k, Measurable (y i j k)) ∧
      iIndepFun (fun i ω => fun j k => y i j k ω) X.P ∧
      (∀ i j k (p : ℕ), 1 ≤ p → ∫⁻ ω, y i j k ω ^ p ∂X.P ≤
        ∫⁻ ω, X.Y b s W Qn i j k {z | IsBlockIndex L (o i) z} (fam i).old (fam i).new ω ^ p
          ∂(fam i).P') ∧
      ∑ i : Fin K, ∫⁻ ω, X.Y b s W Qn i (X.J b K s W 0 ((fam i).old ω) i.castSucc)
          (X.J b K s W 0 ((fam i).old ω) i.succ) {z | IsBlockIndex L (o i) z} (fam i).old
          (fam i).new ω ∂(fam i).P' ≤
        ∫⁻ ω, ∑ i : Fin K, y i (X.J b K s W 0 ω i.castSucc) (X.J b K s W 0 ω i.succ) ω ∂X.P := by
  have hz₀ : ∀ i : Fin K, (fun k => ((o i k : ℕ) : ℤ)) ∈ {z | IsBlockIndex L (o i) z} :=
    fun i k => by simp
  have hold : ∀ i, MeasurePreserving (fam i).old (fam i).P' X.P := fun i =>
    ((fam i).isBlockCoupling _ (hz₀ i)).measurePreserving_old
  choose y hym hyid using fun i : Fin K => exists_condReward X hb hs hW Qn i (o i) (fam i) (hfin i)
  obtain ⟨J', hJ'm, hJ'ae⟩ := exists_chainInfo_measurable_J X hb hs K W
  have hchain : chainInfo X s K ≤ X.measurableSpace := iSup_le fun _ => X.info_le _
  refine ⟨y, hym, fun i j k => (hym i j k).mono (X.info_le _) le_rfl, ?_, ?_, ?_⟩
  · rw [iIndepFun_iff_iIndep]
    refine iIndep_of_iIndep_of_le (X.iIndep_info (Fin K) (fun i => (chainSlab s 0 i).set)
      (fun i => Infra.Slab.measurableSet_slab_set _)
      (fun i => Infra.Slab.volume_frontier_slab_set _)
      (Infra.Slab.pairwise_disjoint_interior_chainSlab hs 0 K)) fun i => ?_
    have hi : Measurable[X.info (chainSlab s 0 i).set] fun ω j k => y i j k ω := by
      let _ : MeasurableSpace X.Ω := X.info (chainSlab s 0 i).set
      exact Measurable.of_eval fun j => Measurable.of_eval fun k => hym i j k
    exact hi.comap_le
  · intro i j k p hp
    refine lintegral_pow_le_of_setLIntegral_eq (hold i) (X.info_le _) (hym i j k)
      (aemeasurable_Y X hb hs hW Qn i _ (fam i) j k) (fun A hA => ?_) p hp
    exact hyid i j k A ((le_sup_left : X.info (chainSlab s 0 i).set ≤ _ ⊔ otherSlabsInfo X s i) A hA)
  · let ι : Fin K → X.Ω → (Fin m → ℤ) × (Fin m → ℤ) := fun i x => (J' x i.castSucc, J' x i.succ)
    have hιm : ∀ i, Measurable[chainInfo X s K] (ι i) := fun i => by
      let _ : MeasurableSpace X.Ω := chainInfo X s K
      exact ((measurable_pi_apply _).comp hJ'm).prodMk ((measurable_pi_apply _).comp hJ'm)
    have hι : ∀ i, Measurable (ι i) := fun i => (hιm i).mono hchain le_rfl
    have hyF : ∀ i, Measurable fun x => y i (ι i x).1 (ι i x).2 x := fun i => by
      have h2 : Measurable fun q : X.Ω × ((Fin m → ℤ) × (Fin m → ℤ)) => y i q.2.1 q.2.2 q.1 :=
        measurable_from_prod_countable_left fun p =>
          ((hym i p.1 p.2).mono (X.info_le _) le_rfl)
      exact h2.comp (measurable_id.prodMk (hι i))
    have hslab : ∀ i : Fin K, ∫⁻ ω, X.Y b s W Qn i (X.J b K s W 0 ((fam i).old ω) i.castSucc)
          (X.J b K s W 0 ((fam i).old ω) i.succ) {z | IsBlockIndex L (o i) z} (fam i).old
          (fam i).new ω ∂(fam i).P' =
        ∫⁻ x, y i (ι i x).1 (ι i x).2 x ∂X.P := by
      intro i
      have h1 : ∫⁻ ω, X.Y b s W Qn i (X.J b K s W 0 ((fam i).old ω) i.castSucc)
            (X.J b K s W 0 ((fam i).old ω) i.succ) {z | IsBlockIndex L (o i) z} (fam i).old
            (fam i).new ω ∂(fam i).P' =
          ∫⁻ ω, X.Y b s W Qn i (ι i ((fam i).old ω)).1 (ι i ((fam i).old ω)).2
            {z | IsBlockIndex L (o i) z} (fam i).old (fam i).new ω ∂(fam i).P' := by
        refine lintegral_congr_ae ?_
        filter_upwards [(hold i).quasiMeasurePreserving.ae hJ'ae] with ω hω
        simp only [ι, hω]
      have e1 := lintegral_comp_index (μ := (fam i).P') ((hι i).comp (hold i).measurable)
          (F := fun p => X.Y b s W Qn i p.1 p.2 {z | IsBlockIndex L (o i) z} (fam i).old
            (fam i).new)
          (fun p => aemeasurable_Y X hb hs hW Qn i _ (fam i) p.1 p.2)
      have e2 := lintegral_comp_index (μ := X.P) (hι i) (F := fun p => y i p.1 p.2)
          (fun p => ((hym i p.1 p.2).mono (X.info_le (chainSlab s 0 i).set) le_rfl).aemeasurable)
      rw [h1]
      refine e1.trans (Eq.trans ?_ e2.symm)
      refine tsum_congr fun p => ?_
      exact (hyid i p.1 p.2 (ι i ⁻¹' {p})
        (chainInfo_le_sup X s i _ (hιm i (measurableSet_singleton p)))).symm
    rw [Finset.sum_congr rfl fun i _ => hslab i,
      ← lintegral_finsetSum _ fun i _ => hyF i]
    refine le_of_eq (lintegral_congr_ae ?_)
    filter_upwards [hJ'ae] with ω hω
    simp only [ι, hω]


end IsotropicVariance.Paper.Proofs.LabelResidual
