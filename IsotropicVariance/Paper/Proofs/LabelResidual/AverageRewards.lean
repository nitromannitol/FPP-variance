/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.LabelResidual.ConditionalRewards
public import IsotropicVariance.Paper.Proofs.LabelResidual.FiniteAverages

/-!
# Independent conditional reward arrays after averaging offsets

The conditional arrays are measurable for their own slab information. A finite average
preserves this property, hence their independence over slabs. Jensen and the uniform
coordinate marginal of the offset vector transfer moments. Linearity transfers the selected
reward integral. This implements the probabilistic averaging step of the proof of Lemma
`lem:residual`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.LabelResidual

variable {m : ℕ}

/-- Independent arrays on the original noise have the averaged reward's moments and dominate
its averaged selected sum, for arbitrary separately supplied common-old families. -/
theorem exists_average_conditional_rewards (X : Setting m) {b s W : ℝ}
    (hb : X.IsUpperBound b) (hs : 0 < s) (hW : 0 < W) (Qn : ℝ) {K : ℕ} (L : ℕ+)
    (fam : (i : Fin K) → (q : Fin m → Fin (L : ℕ)) →
      X.BlockCouplingFamily s W L i {z | IsBlockIndex L q z})
    (hfin : ∀ (i : Fin K) q (j k : Fin m → ℤ), W*zNorm (k-j) ≤ s/2 →
      ∫⁻ ω, X.Y b s W Qn i j k {z | IsBlockIndex L q z} (fam i q).old (fam i q).new ω
        ∂(fam i q).P' ≠ ∞) :
    ∃ y : Fin K → (Fin m → ℤ) → (Fin m → ℤ) → X.Ω → ℝ≥0∞,
      (∀ i j k, Measurable (y i j k)) ∧
      iIndepFun (fun i ω => fun j k => y i j k ω) X.P ∧
      (∀ i j k (p : ℕ), 1 ≤ p → ∫⁻ ω, y i j k ω^p ∂X.P ≤
        (Fintype.card (Fin m → Fin (L : ℕ)) : ℝ≥0∞)⁻¹ *
          ∑ q : Fin m → Fin (L : ℕ), ∫⁻ ω,
            X.Y b s W Qn i j k {z | IsBlockIndex L q z} (fam i q).old (fam i q).new ω^p
              ∂(fam i q).P') ∧
      (Fintype.card (Fin K → Fin m → Fin (L : ℕ)) : ℝ≥0∞)⁻¹ *
        ∑ o : Fin K → Fin m → Fin (L : ℕ), ∑ i : Fin K,
          ∫⁻ ω, X.Y b s W Qn i
            (X.J b K s W 0 ((fam i (o i)).old ω) i.castSucc)
            (X.J b K s W 0 ((fam i (o i)).old ω) i.succ)
            {z | IsBlockIndex L (o i) z} (fam i (o i)).old (fam i (o i)).new ω
              ∂(fam i (o i)).P' ≤
        ∫⁻ ω, ∑ i : Fin K, y i (X.J b K s W 0 ω i.castSucc) (X.J b K s W 0 ω i.succ) ω ∂X.P := by
  classical
  let Off := Fin m → Fin (L : ℕ)
  let Vec := Fin K → Off
  let _ : Nonempty Off := ⟨fun _ => ⟨0,L.pos⟩⟩
  choose v hvinfo hvm hvind hvmom hvsel using fun o : Vec =>
    exists_conditional_rewards_info X hb hs hW Qn o (fun i => fam i (o i))
      (fun i j k hjk => hfin i (o i) j k hjk)
  let w : ℝ≥0∞ := (Fintype.card Vec : ℝ≥0∞)⁻¹
  let y : Fin K → (Fin m → ℤ) → (Fin m → ℤ) → X.Ω → ℝ≥0∞ :=
    fun i j k ω => w * ∑ o : Vec, v o i j k ω
  have hyinfo (i : Fin K) (j k : Fin m → ℤ) :
      Measurable[X.info (chainSlab s 0 i).set] (y i j k) := by
    let _ : MeasurableSpace X.Ω := X.info (chainSlab s 0 i).set
    exact (Finset.measurable_sum _ fun o _ => hvinfo o i j k).const_mul w
  have hym (i : Fin K) (j k : Fin m → ℤ) : Measurable (y i j k) :=
    (hyinfo i j k).mono (X.info_le _) le_rfl
  refine ⟨y,hym,?_,?_,?_⟩
  · rw [iIndepFun_iff_iIndep]
    refine iIndep_of_iIndep_of_le (X.iIndep_info (Fin K) (fun i => (chainSlab s 0 i).set)
      (fun i => Infra.Slab.measurableSet_slab_set _)
      (fun i => Infra.Slab.volume_frontier_slab_set _)
      (Infra.Slab.pairwise_disjoint_interior_chainSlab hs 0 K)) fun i => ?_
    have hi : Measurable[X.info (chainSlab s 0 i).set] fun ω j k => y i j k ω := by
      let _ : MeasurableSpace X.Ω := X.info (chainSlab s 0 i).set
      exact Measurable.of_eval fun j => Measurable.of_eval fun k => hyinfo i j k
    exact hi.comap_le
  · intro i j k p hp
    calc
      _ ≤ w * ∑ o : Vec, ∫⁻ ω, v o i j k ω^p ∂X.P :=
        lintegral_average_pow_le (fun o => v o i j k) (fun o => (hvm o i j k).aemeasurable) hp
      _ ≤ w * ∑ o : Vec, ∫⁻ ω,
          X.Y b s W Qn i j k {z | IsBlockIndex L (o i) z}
            (fam i (o i)).old (fam i (o i)).new ω^p ∂(fam i (o i)).P' :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun o _ => hvmom o i j k p hp)
      _ = _ := average_apply (B := Off) i (fun q => ∫⁻ ω,
        X.Y b s W Qn i j k {z | IsBlockIndex L q z} (fam i q).old (fam i q).new ω^p
          ∂(fam i q).P')
  · have hJ (i : Fin K) :=
      (Infra.Slab.aemeasurable_J X hb hs 0 K W i.castSucc).prodMk
        (Infra.Slab.aemeasurable_J X hb hs 0 K W i.succ)
    have hm (o : Vec) (i : Fin K) : AEMeasurable
        (fun ω => v o i (X.J b K s W 0 ω i.castSucc) (X.J b K s W 0 ω i.succ) ω) X.P := by
      have hf : Measurable fun p : X.Ω × ((Fin m → ℤ) × (Fin m → ℤ)) =>
          v o i p.2.1 p.2.2 p.1 := measurable_from_prod_countable_left fun p => hvm o i p.1 p.2
      exact hf.comp_aemeasurable (aemeasurable_id.prodMk (hJ i))
    calc
      _ ≤ w * ∑ o : Vec, ∫⁻ ω, ∑ i : Fin K,
          v o i (X.J b K s W 0 ω i.castSucc) (X.J b K s W 0 ω i.succ) ω ∂X.P :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun o _ => hvsel o)
      _ = ∫⁻ ω, w * ∑ o : Vec, ∑ i : Fin K,
          v o i (X.J b K s W 0 ω i.castSucc) (X.J b K s W 0 ω i.succ) ω ∂X.P := by
        rw [lintegral_const_mul' _ _ (by dsimp [w]; simp),
          lintegral_finsetSum' _ fun o _ => Finset.aemeasurable_fun_sum _ fun i _ => hm o i]
      _ = _ := by
        apply lintegral_congr
        intro ω
        rw [Finset.sum_comm, Finset.mul_sum]

end IsotropicVariance.Paper.Proofs.LabelResidual
