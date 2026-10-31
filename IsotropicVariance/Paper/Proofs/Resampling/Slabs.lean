/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Resampling.Law
public import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry

/-!
# Independence of the resampling over slabs

The fact behind "The arrays `Y_1, …, Y_K` are independent" of Section `sec:gain`: the old noise and
all the new noises, read in the slab `S_i`, are independent over `i`.

* `Gain.Bridge.info_union_le_aeClosure`: the union law for two sets.
* `NoiseModel.exists_measurable_ae_resampleKernel_eq`: for `G ⊆ S` and `σ ≤ info G`, the
  conditional probability `resampleKernel G σ (·, B)` of an event `B` of `info S` is almost surely
  measurable for `info S`. Up to null sets `info Gᶜ` is `info (S \ G) ⊔ info Sᶜ` (`union_ae`), and
  `info Sᶜ` is independent of `info S`, which contains `B`, `σ` and `info (S \ G)` (`iIndep_info`).
* `NoiseModel.iIndep_resamplingLaw`: the independence over disjoint sets `S j`, from this and the
  generic `Proofs.Resampling.iIndep_groupSigma`.
* `Setting.iIndep_blockResampling`: **the independence over the slabs**, for `σ (i, z)` in the
  information of the block `(i, z)`; `Setting.iIndep_blockResampling_fin` over the first `K` slabs.
* `Setting.iIndepFun_blockResampling`: functions measurable for the σ-algebras `Setting.slabSigma`
  of the slabs are independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper

open Proofs.Resampling Proofs.Gain.Bridge

variable {m : ℕ}

namespace NoiseModel

variable (N : NoiseModel.{u} m)

/-- **The conditional probability of an event of a larger set.** For `G ⊆ S` Borel with null
frontiers and `σ ≤ info G`, the probability `resampleKernel G σ (·, B)` of an event `B` of the noise
in `S` is almost surely measurable for the noise in `S`. -/
theorem exists_measurable_ae_resampleKernel_eq {S G : Set (Pt m)} (hS : MeasurableSet S)
    (hSfr : volume (frontier S) = 0) (hG : MeasurableSet G) (hGfr : volume (frontier G) = 0)
    (hGS : G ⊆ S) {σ : MeasurableSpace N.Ω} (hσ : σ ≤ N.info G) {B : Set N.Ω}
    (hB : MeasurableSet[N.info S] B) :
    ∃ g : N.Ω → ℝ≥0∞, Measurable[N.info S] g ∧ ∀ᵐ ω ∂N.P, N.resampleKernel G σ ω B = g ω := by
  let := N.measurableSpace
  have hσle : σ ≤ N.measurableSpace := hσ.trans (N.info_le G)
  have hsS : N.info (S \ G) ⊔ σ ≤ N.info S :=
    sup_le (N.info_mono sdiff_subset) (hσ.trans (N.info_mono hGS))
  have hcompl : Gᶜ = (S \ G) ∪ Sᶜ := by
    ext x
    by_cases hx : x ∈ S <;> by_cases hxG : x ∈ G <;> simp [hx, hxG]
    exact hx (hGS hxG)
  have hle₁ : (N.info (S \ G) ⊔ σ) ⊔ N.info Sᶜ ≤ N.info Gᶜ ⊔ σ := by
    refine sup_le (sup_le ?_ le_sup_right) ?_
    · exact (N.info_mono fun x hx => hx.2).trans le_sup_left
    · exact (N.info_mono (compl_subset_compl.2 hGS)).trans le_sup_left
  have hle₂ : N.info Gᶜ ⊔ σ ≤ aeClosure ((N.info (S \ G) ⊔ σ) ⊔ N.info Sᶜ) N.P := by
    refine sup_le ?_ ((le_sup_right.trans le_sup_left).trans le_aeClosure)
    rw [hcompl]
    refine (info_union_le_aeClosure N (hS.diff hG) (null_frontier_diff hSfr hGfr) hS.compl
      (by rwa [frontier_compl]) (disjoint_compl_right.mono_left sdiff_subset)).trans
      (aeClosure_mono ?_)
    exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hB' := N.info_le S B hB
  have h₁ := condExpKernel_ae_eq_of_le_aeClosure (P := N.P) hle₁
    (N.info_compl_sup_le G hσle) hle₂ hB'
  have h₂ := condExpKernel_sup_ae_eq (P := N.P) (N.info_le S) (N.info_le Sᶜ) hsS
    (indep_info_compl N hS hSfr) hB
  refine ⟨fun ω => condExpKernel N.P (N.info (S \ G) ⊔ σ) ω B,
    (measurable_condExpKernel hB').mono hsS le_rfl, ?_⟩
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  rw [N.resampleKernel_apply G hσle, hω₁, hω₂]

/-- **Independence of the resampling over disjoint sets.** Let `S j` be Borel sets with null
frontiers and disjoint interiors, and `I j` disjoint sets of indices with `G c ⊆ S j` for `c` in
`I j`, Borel with null frontiers, and `σ c ≤ info (G c)`. Then the noise in `S j`, old or new of the
indices of `I j`, is independent over `j`. -/
theorem iIndep_resamplingLaw {J : Type} [Countable J] {ι : Type*} {G : ι → Set (Pt m)}
    {σ : ι → MeasurableSpace N.Ω} {S : J → Set (Pt m)} {I : J → Set ι}
    (hS : ∀ j, MeasurableSet (S j)) (hSfr : ∀ j, volume (frontier (S j)) = 0)
    (hSd : Pairwise (Function.onFun Disjoint fun j => interior (S j)))
    (hI : Pairwise (Function.onFun Disjoint I)) (hG : ∀ j, ∀ c ∈ I j, MeasurableSet (G c))
    (hGfr : ∀ j, ∀ c ∈ I j, volume (frontier (G c)) = 0) (hGS : ∀ j, ∀ c ∈ I j, G c ⊆ S j)
    (hσ : ∀ j, ∀ c ∈ I j, σ c ≤ N.info (G c)) :
    iIndep (fun j => groupSigma (N.info (S j)) (I j)) (N.resamplingLaw G σ) := by
  let := N.measurableSpace
  exact iIndep_groupSigma (N.resamplingKernel_apply G σ) (N.iIndep_info J S hS hSfr hSd)
    (fun j => N.info_le _) hI fun j c hc B hB => N.exists_measurable_ae_resampleKernel_eq (hS j)
      (hSfr j) (hG j c hc) (hGfr j c hc) (hGS j c hc) (hσ j c hc) hB

end NoiseModel

/-! ### The slabs of the chain -/

namespace Proofs.Resampling

/-- The σ-algebra of the indices `(i, z)`, for all `z`, is the supremum over `z`. -/
theorem groupSigma_fst_eq {Ω Z : Type*} (a₀ : MeasurableSpace Ω) (i : ℕ) :
    groupSigma a₀ {c : ℕ × Z | c.1 = i} =
      a₀.comap Prod.fst ⊔ ⨆ z, a₀.comap fun p : Ω × (ℕ × Z → Ω) => p.2 (i, z) := by
  unfold groupSigma
  refine congrArg (a₀.comap Prod.fst ⊔ ·) (le_antisymm (iSup₂_le fun c hc => ?_)
    (iSup_le fun z => ?_))
  · obtain ⟨i', z⟩ := c
    obtain rfl : i' = i := hc
    exact le_iSup (fun z => a₀.comap fun p : Ω × (ℕ × Z → Ω) => p.2 (i', z)) z
  · exact le_iSup₂_of_le (f := fun c (_ : c ∈ {c : ℕ × Z | c.1 = i}) =>
      a₀.comap fun p : Ω × (ℕ × Z → Ω) => p.2 c) (i, z) rfl le_rfl

/-- The slabs of the chain have pairwise disjoint interiors. -/
theorem pairwise_disjoint_interior_chainSlab_nat {n : ℝ} (hn : 0 < n) :
    Pairwise (Function.onFun Disjoint fun i : ℕ => interior (chainSlab (m := m) n 0 i).set) := by
  intro i j hij
  have h := Infra.Slab.pairwise_disjoint_interior_chainSlab (m := m) hn 0 (max i j + 1)
    (i := ⟨i, Nat.lt_succ_of_le (le_max_left i j)⟩) (j := ⟨j, Nat.lt_succ_of_le (le_max_right i j)⟩)
    (fun h => hij (Fin.mk.inj_iff.1 h))
  exact h

end Proofs.Resampling

namespace Setting

variable (X : Setting.{u} m)

/-- The information in the slab `i` of the old noise and of the new noises of the blocks of the
slab `i`. -/
@[instance_reducible]
def slabSigma (n : ℝ) (i : ℕ) : MeasurableSpace (X.Ω × (BlockIdx m → X.Ω)) :=
  (X.info (chainSlab n 0 i).set).comap Prod.fst ⊔
    ⨆ z, (X.info (chainSlab n 0 i).set).comap fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 (i, z)

/-- **Independence over the slabs** (the fact behind "The arrays `Y_1, …, Y_K` are independent",
Section `sec:gain`): for `σ (i, z)` determined by the noise in the block `(i, z)`, the information
in the slab `i` of the old noise and of the new noises of the blocks of the slab `i` are independent
over `i`, under the resampling law of the blocks. -/
theorem iIndep_blockResampling {n : ℝ} (hn : 0 < n) (W : ℝ) (L : ℕ)
    {σ : BlockIdx m → MeasurableSpace X.Ω}
    (hσ : ∀ c : BlockIdx m, σ c ≤ X.info (block n W L c.1 c.2)) :
    iIndep (fun i : ℕ => (X.info (chainSlab n 0 i).set).comap Prod.fst ⊔
      ⨆ z, (X.info (chainSlab n 0 i).set).comap fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 (i, z))
      (X.blockResampling n W L σ) := by
  have h := X.toNoiseModel.iIndep_resamplingLaw (J := ℕ)
    (G := fun c : BlockIdx m => block n W L c.1 c.2) (σ := σ)
    (S := fun i => (chainSlab n 0 i).set) (I := fun i => {c | c.1 = i})
    (fun i => Infra.Slab.measurableSet_slab_set _) (fun i => Infra.Slab.volume_frontier_slab_set _)
    (pairwise_disjoint_interior_chainSlab_nat hn)
    (fun i j hij => disjoint_left.2 fun c hci hcj => hij (hci.symm.trans hcj))
    (fun _ c _ => measurableSet_block n W L c.1 c.2)
    (fun _ c _ => volume_frontier_block n W L c.1 c.2)
    (fun i c hc => by
      obtain rfl : c.1 = i := hc
      exact block_subset_chainSlab n W L c.1 c.2)
    fun _ c _ => hσ c
  simp only [groupSigma_fst_eq] at h
  exact h

/-- **Independence over the first `K` slabs.** -/
theorem iIndep_blockResampling_fin {n : ℝ} (hn : 0 < n) (W : ℝ) (L K : ℕ)
    {σ : BlockIdx m → MeasurableSpace X.Ω}
    (hσ : ∀ c : BlockIdx m, σ c ≤ X.info (block n W L c.1 c.2)) :
    iIndep (fun i : Fin K => X.slabSigma n i) (X.blockResampling n W L σ) :=
  (X.iIndep_blockResampling hn W L hσ).precomp Fin.val_injective

/-- **Functions of the slabs are independent**: random variables `Y i` measurable for the
information `slabSigma n i` of the slab `i` are independent under the resampling law of the
blocks. -/
theorem iIndepFun_blockResampling {n : ℝ} (hn : 0 < n) (W : ℝ) (L : ℕ)
    {σ : BlockIdx m → MeasurableSpace X.Ω}
    (hσ : ∀ c : BlockIdx m, σ c ≤ X.info (block n W L c.1 c.2)) {β : ℕ → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)] {Y : ∀ i, X.Ω × (BlockIdx m → X.Ω) → β i}
    (hY : ∀ i, Measurable[X.slabSigma n i] (Y i)) :
    iIndepFun Y (X.blockResampling n W L σ) := by
  rw [iIndepFun_iff_iIndep mβ]
  exact iIndep_of_iIndep_of_le (X.iIndep_blockResampling hn W L hσ) fun i => (hY i).comap_le

end Setting

end IsotropicVariance.Paper
