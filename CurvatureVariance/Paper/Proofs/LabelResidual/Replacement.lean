/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.LabelResidual.Coupling
public import CurvatureVariance.Paper.Proofs.LabelResidual.Factor
public import CurvatureVariance.Paper.Proofs.Gain.AVLabels
import CurvatureVariance.Infra.FPP.Model
import CurvatureVariance.Paper.Proofs.Responses.Slabs
import Mathlib.Tactic.Ring

/-!
# The joint label resampling

The proof of Lemma `lem:residual` resamples every block `G` of the `K` slabs conditionally on its
label `λ_G` (`X_G` in the paper). This file builds one law of a pair (old weights, new weights) on
`Config m × Config m` that does this for all blocks at once, and shows that it is an exchangeable
replacement of the blocks.

For offsets `o` and a family of labels `lam i o' g : Config m → β`, write `G i g` for the block
`block n w L t i (o i) g` and `λ_{i,g} = lam i (o i) g`.

* `labelPairLaw M n w L K t o lam`: the pair law `pairLaw` over the cells `cellOf` of the blocks
  of the slabs `1 ≤ i ≤ K`. On the cell of `G i g` the pair is drawn from the label coupling of
  `λ_{i,g}` read through the weights of the cell (`cellLabel`; the label of the weights of the
  cell extended by `0`); on the rest of the edges the two members are independent. It is a
  probability law whenever `F` is (`isProbabilityMeasure_labelPairLaw`), whatever the labels.
* `IsLabelFamily`: the hypotheses on the labels of the blocks of the slabs `1 ≤ i ≤ K` (the
  `dep`, `finite` and `measurableSet` fields of `IsBlockLabel`).
* `isSlabReplacement_labelPairLaw`: with `old = Prod.fst` and `new = pairNew n w L t o`
  (`new i g x = resample (G i g) x.1 x.2`), `labelPairLaw` is an exchangeable replacement of the
  blocks (`IsSlabReplacement`), for `L ≥ 1`; no hypothesis on the labels is needed.
* `ae_lam_pairNew_eq`: the label of the resampled block is that of the old one, almost surely.
* `lintegral_labelPairLaw_pairNew`: the law of `(x.1, new i g x)` is the law of
  `(ω, ω^{G,ω'})`, `ω ∼ P`, `ω' ∼ P[· | λ_{i,g} = λ_{i,g}(ω)]`; hence
  `labelES_eq_lintegral_labelPairLaw`: `E(X − X^{G,λ_G})² = ∫ (X x.1 − X (new i g x))²`.
* `iIndepFun_slabPair_labelPairLaw`: the pairs of weights of the slabs `1, …, K` are independent;
  `map_slabPair_labelPairLaw_congr`: the law of the pair of weights of slab `i + 1` depends on the
  offsets only through `o (i + 1)` (for the mixture over offsets, `offsetMixture`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### The law -/

section Defs

variable (M : Model m) (n w L K : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o : ℕ → Fin m → ℤ)

/-- The block index of an edge (`cellOf`) with explicit parameters. -/
noncomputable abbrev cellMap : Edge m → Option (Fin K × (Fin m → ℤ)) :=
  cellOf (n := n) (w := w) (L := L) (K := K) (t := t) (o := o)

variable {β : Type*} (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β)

/-- The label of a cell, read from the weights of the cell: on the block `some (i, g)` of slab
`i + 1`, `some (lam (i + 1) (o (i + 1)) g ω)` for the configuration `ω` with the weights of the
cell and `0` elsewhere; `none` on the rest of the edges. -/
noncomputable def cellLabel (c : Option (Fin K × (Fin m → ℤ)))
    (y : {e : Edge m // cellMap n w L K t o e = c} → ℝ≥0) : Option β :=
  c.map fun c' => lam ((c'.1 : ℕ) + 1) (o ((c'.1 : ℕ) + 1)) c'.2
    (fiberExtend (cellMap n w L K t o) c y)

/-- **The joint label resampling** (in the proof of Lemma `lem:residual`): the law of the
pair (old weights, new weights) under which the cells of the blocks of the slabs `1 ≤ i ≤ K`
(offsets `o`) and the rest of the edges carry independent pairs; on the cell of the block `G` the
new weights are drawn from the law of the weights of `G` conditioned on the label `λ_G` of the old
ones (the label coupling), and on the rest the new weights are independent of the old ones. -/
noncomputable def labelPairLaw : Measure (Config m × Config m) :=
  pairLaw (cellMap n w L K t o) fun c =>
    labelCoupling (Measure.infinitePi fun _ : {e : Edge m // cellMap n w L K t o e = c} => M.F)
      (cellLabel n w L K t o lam c)

instance isProbabilityMeasure_labelPairLaw [IsProbabilityMeasure M.F] :
    IsProbabilityMeasure (labelPairLaw M n w L K t o lam) := by
  unfold labelPairLaw
  infer_instance

/-- The hypotheses on the labels `lam i (o i) g` of the blocks of the slabs `1 ≤ i ≤ K` with the
offsets `o` (the `dep`, `finite` and `measurableSet` fields of `IsBlockLabel`). -/
structure IsLabelFamily : Prop where
  /-- The label of a block is a function of the weights of the block. -/
  dep : ∀ i, 1 ≤ i → i ≤ K → ∀ (g : Fin m → ℤ) (ω ω' : Config m),
    (∀ e : Edge m, e.1 ∈ block n w L t i (o i) g → ω e = ω' e) →
      lam i (o i) g ω = lam i (o i) g ω'
  /-- The label of a block has finitely many values. -/
  finite : ∀ i, 1 ≤ i → i ≤ K → ∀ g : Fin m → ℤ, (range (lam i (o i) g)).Finite
  /-- The level sets of the label of a block are measurable. -/
  measurableSet : ∀ i, 1 ≤ i → i ≤ K → ∀ (g : Fin m → ℤ) (ω : Config m),
    MeasurableSet (lam i (o i) g ⁻¹' {lam i (o i) g ω})

end Defs

/-! ### Cells and labels -/

section Cells

variable {n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ}

/-- The cell of an edge is the block `(i, g)` exactly when the edge lies in the block `g` of slab
`i + 1`. -/
theorem cellMap_eq_some_iff (i : Fin K) (g : Fin m → ℤ) (e : Edge m) :
    cellMap n w L K t o e = some (i, g) ↔
      e.1 ∈ block n w L t ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g :=
  cellOf_eq_iff n w L K t o e (some (i, g))

/-- Two slabs with a common edge are the same slab. -/
theorem eq_of_mem_slabEdges {i j : ℕ} {e : Sym2 (Vertex m)}
    (hi : e ∈ slabEdges (((i : ℤ) - 1) * n) ((i : ℤ) * n))
    (hj : e ∈ slabEdges (((j : ℤ) - 1) * n) ((j : ℤ) * n)) : i = j := by
  by_contra hne
  have hd : Disjoint (slabEdges (m := m) (-(n : ℤ) + (i : ℤ) * n) (-(n : ℤ) + ((i : ℤ) + 1) * n))
      (slabEdges (-(n : ℤ) + (j : ℤ) * n) (-(n : ℤ) + ((j : ℤ) + 1) * n)) :=
    Responses.pairwise_disjoint_slabEdges (m := m) (-(n : ℤ)) n hne
  have e1 : ∀ k : ℕ, -(n : ℤ) + (k : ℤ) * n = ((k : ℤ) - 1) * n := fun k => by ring
  have e2 : ∀ k : ℕ, -(n : ℤ) + ((k : ℤ) + 1) * n = (k : ℤ) * n := fun k => by ring
  rw [e1, e2, e1, e2] at hd
  exact Set.disjoint_left.mp hd hi hj

/-- An edge of the cell `some c` lies in the block `G i g` only if `c` is `(i − 1, g)`. -/
theorem eq_of_cellMap_eq_some_of_mem_block {c : Fin K × (Fin m → ℤ)} {e : Edge m}
    (hc : cellMap n w L K t o e = some c) {i : ℕ} {g : Fin m → ℤ}
    (he : e.1 ∈ block n w L t i (o i) g) : (c.1 : ℕ) + 1 = i ∧ c.2 = g := by
  have hc' := (cellMap_eq_some_iff c.1 c.2 e).1 hc
  have hi : (c.1 : ℕ) + 1 = i := eq_of_mem_slabEdges hc'.1 he.1
  subst hi
  exact ⟨rfl, (eq_of_mem_block_of_mem_block hc' he).2⟩

/-- Every edge of slab `i + 1`, `i < K`, lies in a block cell of that slab, for `L ≥ 1`. -/
theorem exists_cellMap_eq_some (hL : 1 ≤ L) (i : Fin K) {e : Edge m}
    (he : e ∈ slabEdgeSet m n ((i : ℕ) + 1)) : ∃ g, cellMap n w L K t o e = some (i, g) := by
  obtain ⟨g, hg⟩ := exists_mem_block (w := w) (t := t) hL (o ((i : ℕ) + 1)) he
  exact ⟨g, (cellMap_eq_some_iff i g e).2 hg⟩

variable {β : Type*} {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β}

/-- The label of the block cell `some (i, g)`, read from the weights of the cell of `ω`, is the
label of `ω`. -/
theorem cellLabel_fiberEquiv (hlam : IsLabelFamily n w L K t o lam) (i : Fin K)
    (g : Fin m → ℤ) (ω : Config m) :
    cellLabel n w L K t o lam (some (i, g)) (fiberEquiv (cellMap n w L K t o) ω (some (i, g))) =
      some (lam ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g ω) := by
  refine congrArg some (hlam.dep _ (by omega) (by omega) g _ _ fun e he => ?_)
  exact fiberExtend_fiberEquiv _ ω ((cellMap_eq_some_iff i g e).2 he)

/-- The label of a block cell has finitely many values and measurable level sets. -/
theorem labelOK_cellLabel (hlam : IsLabelFamily n w L K t o lam) (i : Fin K) (g : Fin m → ℤ) :
    LabelOK (cellLabel n w L K t o lam (some (i, g))) := by
  have hi1 : 1 ≤ (i : ℕ) + 1 := by omega
  have hiK : (i : ℕ) + 1 ≤ K := by omega
  refine ⟨?_, fun y => ?_⟩
  · refine ((hlam.finite _ hi1 hiK g).image some).subset ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  · set ℓ := lam ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g
    have hset : cellLabel n w L K t o lam (some (i, g)) ⁻¹'
        {cellLabel n w L K t o lam (some (i, g)) y} =
        fiberExtend (cellMap n w L K t o) (some (i, g)) ⁻¹'
          (ℓ ⁻¹' {ℓ (fiberExtend (cellMap n w L K t o) (some (i, g)) y)}) := by
      ext y'
      simp [cellLabel, ℓ]
    rw [hset]
    exact measurable_fiberExtend _ _ (hlam.measurableSet _ hi1 hiK g _)

end Cells

/-! ### The replacement -/

section Replacement

variable {M : Model m} {n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ}
  {β : Type*} {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β}

/-- The new weights of a block are the old weights spliced with the new ones on the block. -/
theorem pairNew_eq_splice (i : ℕ) (g : Fin m → ℤ) :
    pairNew n w L t o i g = fun x : Config m × Config m =>
      splice {e : Edge m | e.1 ∈ block n w L t i (o i) g} x.1 x.2 :=
  funext fun x => resample_eq_splice _ x.1 x.2

theorem measurable_pairNew (i : ℕ) (g : Fin m → ℤ) : Measurable (pairNew n w L t o i g) := by
  rw [pairNew_eq_splice]
  exact measurable_splice _

/-- The fiber pair laws of `labelPairLaw` have the product law as first marginal. -/
theorem map_fst_cellPairLaw [IsProbabilityMeasure M.F] (c : Option (Fin K × (Fin m → ℤ))) :
    (labelCoupling (Measure.infinitePi fun _ : {e : Edge m // cellMap n w L K t o e = c} => M.F)
      (cellLabel n w L K t o lam c)).map Prod.fst =
      Measure.infinitePi fun _ : {e : Edge m // cellMap n w L K t o e = c} => M.F :=
  map_fst_labelCoupling _ _

/-- The old weights have the law `P`. -/
theorem map_fst_labelPairLaw (hM : M.Standing) :
    (labelPairLaw M n w L K t o lam).map Prod.fst = M.P := by
  have := hM.probF
  rw [Infra.FPP.IsIIDWeights.eq_infinitePi hM.iid]
  exact map_fst_pairLaw _ _ M.F fun c => map_fst_cellPairLaw c

/-- **Swapping the old and new weights on a block preserves `labelPairLaw`.** -/
theorem map_swapSplice_labelPairLaw [IsProbabilityMeasure M.F] (i : ℕ) (g : Fin m → ℤ) :
    (labelPairLaw M n w L K t o lam).map
      (swapSplice {e : Edge m | e.1 ∈ block n w L t i (o i) g}) =
      labelPairLaw M n w L K t o lam := by
  unfold labelPairLaw
  refine map_swapSplice_pairLaw _ _ _ fun c => ?_
  rcases c with _ | c
  · -- the rest of the edges: the independent pair
    rw [labelCoupling_of_const _ fun _ _ => rfl]
    set ν := Measure.infinitePi fun _ : {e : Edge m // cellMap n w L K t o e = none} => M.F
    have h := Infra.EfronStein.measurePreserving_swap_outside
      (fun _ : {e : Edge m // cellMap n w L K t o e = none} => M.F)
      {e : {e : Edge m // cellMap n w L K t o e = none} |
        e.1.1 ∈ block n w L t i (o i) g}ᶜ
    convert h.map_eq using 2
    funext p
    refine Prod.ext (funext fun e => ?_) (funext fun e => ?_) <;>
    · by_cases he : e.1.1 ∈ block n w L t i (o i) g
      · simp [swapSplice, splice_apply_of_mem (T := {e : {e : Edge m // cellMap n w L K t o e =
          none} | e.1.1 ∈ block n w L t i (o i) g}) he, Infra.EfronStein.resample, he]
      · simp [swapSplice, splice_apply_of_notMem (T := {e : {e : Edge m // cellMap n w L K t o e =
          none} | e.1.1 ∈ block n w L t i (o i) g}) he, Infra.EfronStein.resample, he]
  · -- a block cell: all of it or none of it lies in the block
    by_cases hc : (c.1 : ℕ) + 1 = i ∧ c.2 = g
    · have hT : {e : {e : Edge m // cellMap n w L K t o e = some c} |
          e.1 ∈ {e : Edge m | e.1 ∈ block n w L t i (o i) g}} = univ := by
        refine eq_univ_of_forall fun e => ?_
        obtain ⟨h1, h2⟩ := hc
        subst h1 h2
        exact (cellMap_eq_some_iff c.1 c.2 e.1).1 e.2
      rw [hT, swapSplice_univ, map_swap_labelCoupling]
    · have hT : {e : {e : Edge m // cellMap n w L K t o e = some c} |
          e.1 ∈ {e : Edge m | e.1 ∈ block n w L t i (o i) g}} = ∅ := by
        refine eq_empty_of_forall_notMem fun e he => hc ?_
        exact eq_of_cellMap_eq_some_of_mem_block e.2 he
      rw [hT, swapSplice_empty, Measure.map_id]

/-- **Exchangeability**: the pair (old weights, new weights of a block) is exchangeable under
`labelPairLaw`. -/
theorem map_pairNew_swap_labelPairLaw [IsProbabilityMeasure M.F] (i : ℕ) (g : Fin m → ℤ) :
    (labelPairLaw M n w L K t o lam).map (fun x => (x.1, pairNew n w L t o i g x)) =
      (labelPairLaw M n w L K t o lam).map (fun x => (pairNew n w L t o i g x, x.1)) := by
  rw [pairNew_eq_splice]
  exact map_splice_eq_of_map_swapSplice _ (map_swapSplice_labelPairLaw i g)

/-- **The pairs of weights of the slabs `1, …, K` are independent** under `labelPairLaw`, for
`L ≥ 1`. -/
theorem iIndepFun_slabPair_labelPairLaw (hM : M.Standing) (hL : 1 ≤ L) :
    iIndepFun (fun (i : Fin K) x => slabPair n ((i : ℕ) + 1) x)
      (labelPairLaw M n w L K t o lam) := by
  have := hM.probF
  have hS : ∀ (i : Fin K) (e : slabEdgeSet m n ((i : ℕ) + 1)),
      cellMap n w L K t o e.1 ∈ {c | ∃ g, c = some (i, g)} := fun i e => by
    obtain ⟨g, hg⟩ := exists_cellMap_eq_some (w := w) (t := t) (o := o) hL i e.2
    exact ⟨g, hg⟩
  unfold labelPairLaw
  refine iIndepFun_pairLaw _ _ (fun i : Fin K => {c | ∃ g, c = some (i, g)}) ?_
    (fun i => measurable_slabPair n _)
    (fun i s => (fun e => (s ⟨cellMap n w L K t o e.1, hS i e⟩).1 ⟨e.1, rfl⟩,
      fun e => (s ⟨cellMap n w L K t o e.1, hS i e⟩).2 ⟨e.1, rfl⟩)) (fun i => ?_)
    fun i r => rfl
  · intro i j hij
    refine Set.disjoint_left.2 fun c hi hj => hij ?_
    obtain ⟨g, rfl⟩ := hi
    obtain ⟨g', hg'⟩ := hj
    exact (Prod.mk.inj (Option.some.inj hg')).1
  · exact (measurable_pi_iff.2 fun e => (measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _))).prodMk
      (measurable_pi_iff.2 fun e => (measurable_pi_apply _).comp
        (measurable_snd.comp (measurable_pi_apply _)))

/-- **The joint label resampling is an exchangeable replacement of the blocks**
(`IsSlabReplacement`), with `old = Prod.fst` and `new = pairNew n w L t o`, for `L ≥ 1`. -/
theorem isSlabReplacement_labelPairLaw (hM : M.Standing) (hL : 1 ≤ L) :
    IsSlabReplacement M (labelPairLaw M n w L K t o lam) n K w L t o Prod.fst
      (pairNew n w L t o) := by
  have := hM.probF
  refine ⟨inferInstance, measurable_fst, map_fst_labelPairLaw hM, measurable_pairNew,
    fun i g x e he => ?_, map_pairNew_swap_labelPairLaw, ?_⟩
  · simp only [pairNew, resample, he, ite_false]
  · have hslab : ∀ (i : Fin K) (e : Edge m),
        e.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n) → e ∈ slabEdgeSet m n ((i : ℕ) + 1) :=
      fun i e he => by
        simpa only [slabEdgeSet, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_right] using he
    let φ : ∀ i : Fin K, (slabEdgeSet m n ((i : ℕ) + 1) → ℝ≥0) ×
        (slabEdgeSet m n ((i : ℕ) + 1) → ℝ≥0) →
        ({e : Edge m // e.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n)} → ℝ≥0) ×
          ((g : Fin m → ℤ) → {e : Edge m // e.1 ∈ block n w L t ((i : ℕ) + 1)
            (o ((i : ℕ) + 1)) g} → ℝ≥0) := fun i p =>
      (fun e => p.1 ⟨e.1, hslab i e.1 e.2⟩, fun g e => p.2 ⟨e.1, e.2.1⟩)
    have hφ : ∀ i, Measurable (φ i) := fun i =>
      (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_fst).prodMk
        (measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
          (measurable_pi_apply _).comp measurable_snd)
    have hind := (iIndepFun_slabPair_labelPairLaw (lam := lam) (o := o) (w := w) (t := t)
      hM hL).comp φ hφ
    convert hind using 1
    funext i x
    refine Prod.ext rfl (funext fun g => funext fun e => ?_)
    simp only [Function.comp_apply, φ, slabPair, pairNew, resample, e.2, ite_true]

/-- **Resampling a block given its label under `labelPairLaw`**: for `1 ≤ i ≤ K`, the pair
(old weights, new weights of the block `G i g`) has the law of `(ω, ω^{G,ω'})`, `ω` drawn from
`P` and `ω'` from `P` conditioned on `λ_{i,g}(ω') = λ_{i,g}(ω)`. -/
theorem lintegral_labelPairLaw_pairNew (hM : M.Standing) (hlam : IsLabelFamily n w L K t o lam)
    {i : ℕ} (hi : 1 ≤ i) (hiK : i ≤ K) (g : Fin m → ℤ) {h : Config m × Config m → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ x, h (x.1, pairNew n w L t o i g x) ∂labelPairLaw M n w L K t o lam =
      ∫⁻ ω, ∫⁻ ω', h (ω, resample (block n w L t i (o i) g) ω ω')
        ∂(M.P[|lam i (o i) g ⁻¹' {lam i (o i) g ω}]) ∂M.P := by
  have := hM.probF
  obtain ⟨i, rfl⟩ : ∃ i' : Fin K, (i' : ℕ) + 1 = i := ⟨⟨i - 1, by omega⟩, by simp; omega⟩
  have hT : {e : Edge m | e.1 ∈ block n w L t ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g} =
      {e | cellMap n w L K t o e = some (i, g)} := by
    ext e
    exact (cellMap_eq_some_iff i g e).symm
  have hres : ∀ ω ω' : Config m, resample (block n w L t ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g) ω ω' =
      splice {e | cellMap n w L K t o e = some (i, g)} ω ω' := fun ω ω' => by
    rw [resample_eq_splice, hT]
  simp_rw [pairNew, hres]
  rw [Infra.FPP.IsIIDWeights.eq_infinitePi hM.iid]
  unfold labelPairLaw
  rw [lintegral_pairLaw_splice_labelCoupling _ _ M.F (fun c => map_fst_cellPairLaw c) (some (i, g))
    (labelOK_cellLabel hlam i g) rfl hh]
  refine lintegral_congr fun ω => ?_
  have hset : (fun ω' => cellLabel n w L K t o lam (some (i, g))
      (fiberEquiv (cellMap n w L K t o) ω' (some (i, g)))) ⁻¹'
      {cellLabel n w L K t o lam (some (i, g)) (fiberEquiv (cellMap n w L K t o) ω (some (i, g)))} =
      lam ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g ⁻¹' {lam ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g ω} := by
    ext ω'
    simp only [mem_preimage, mem_singleton_iff, cellLabel_fiberEquiv hlam, Option.some.injEq]
  rw [hset]

/-- **The label of a resampled block is the old label**, almost surely under `labelPairLaw`. -/
theorem ae_lam_pairNew_eq (hM : M.Standing) (hlam : IsLabelFamily n w L K t o lam) {i : ℕ}
    (hi : 1 ≤ i) (hiK : i ≤ K) (g : Fin m → ℤ) :
    ∀ᵐ x ∂labelPairLaw M n w L K t o lam,
      lam i (o i) g (pairNew n w L t o i g x) = lam i (o i) g x.1 := by
  classical
  set ℓ := lam i (o i) g
  set D : Set (Config m × Config m) := {p | ¬ℓ p.2 = ℓ p.1} with hDdef
  have hD : MeasurableSet D := by
    have hD' : D = ⋃ v ∈ (hlam.finite i hi hiK g).toFinset, (ℓ ⁻¹' {v}) ×ˢ (ℓ ⁻¹' {v})ᶜ := by
      ext p
      simp only [hDdef, mem_ofPred_eq, mem_iUnion, mem_prod, mem_preimage, mem_singleton_iff,
        mem_compl_iff, Set.Finite.mem_toFinset, exists_prop]
      exact ⟨fun hp => ⟨ℓ p.1, ⟨p.1, rfl⟩, rfl, hp⟩, fun ⟨v, _, h1, h2⟩ => h1 ▸ h2⟩
    rw [hD']
    refine Finset.measurableSet_biUnion _ fun v hv => ?_
    obtain ⟨ω, rfl⟩ := (Set.Finite.mem_toFinset _).1 hv
    have hm := hlam.measurableSet i hi hiK g ω
    exact hm.prod hm.compl
  have hφ : Measurable fun x : Config m × Config m => (x.1, pairNew n w L t o i g x) :=
    measurable_fst.prodMk (measurable_pairNew i g)
  rw [ae_iff]
  change labelPairLaw M n w L K t o lam ((fun x => (x.1, pairNew n w L t o i g x)) ⁻¹' D) = 0
  rw [← lintegral_indicator_one (hφ hD)]
  change ∫⁻ x, D.indicator 1 (x.1, pairNew n w L t o i g x) ∂labelPairLaw M n w L K t o lam = 0
  rw [lintegral_labelPairLaw_pairNew hM hlam hi hiK g (measurable_one.indicator hD)]
  refine (lintegral_congr fun ω => ?_).trans lintegral_zero
  refine (lintegral_congr_ae ((ae_cond_mem (hlam.measurableSet i hi hiK g ω)).mono
    fun ω' hω' => ?_)).trans lintegral_zero
  have hagree : ℓ (resample (block n w L t i (o i) g) ω ω') = ℓ ω' :=
    hlam.dep i hi hiK g _ _ fun e he => by simp only [resample, he, ite_true]
  have hnot : (ω, resample (block n w L t i (o i) g) ω ω') ∉ D := fun hD' =>
    (show ¬ℓ (resample (block n w L t i (o i) g) ω ω') = ℓ ω from hD')
      (hagree.trans (show ℓ ω' = ℓ ω from hω'))
  exact indicator_of_notMem hnot _

/-- **The label Efron–Stein term under `labelPairLaw`**: for `1 ≤ i ≤ K` and measurable `X`,
`E(X − X^{G,λ_G})² = ∫ (X x.1 − X (new i g x))² d(labelPairLaw)`. -/
theorem labelES_eq_lintegral_labelPairLaw (hM : M.Standing)
    (hlam : IsLabelFamily n w L K t o lam) {i : ℕ} (hi : 1 ≤ i) (hiK : i ≤ K) (g : Fin m → ℤ)
    {X : Config m → ℝ} (hX : Measurable X) :
    labelES M.P X (block n w L t i (o i) g) (lam i (o i) g) =
      ∫⁻ x, ENNReal.ofReal ((X x.1 - X (pairNew n w L t o i g x)) ^ 2)
        ∂labelPairLaw M n w L K t o lam :=
  (lintegral_labelPairLaw_pairNew hM hlam hi hiK g (h := fun p =>
    ENNReal.ofReal ((X p.1 - X p.2) ^ 2))
    (((hX.comp measurable_fst).sub (hX.comp measurable_snd)).pow_const 2).ennreal_ofReal).symm

/-- **The law of the pair of weights of slab `i + 1` depends only on the offset of that slab**:
if `o (i + 1) = o' (i + 1)`, `i < K`, then `slabPair n (i + 1)` has the same law under
`labelPairLaw … o lam` and `labelPairLaw … o' lam`, for `L ≥ 1`. -/
theorem map_slabPair_labelPairLaw_congr (hM : M.Standing) (hL : 1 ≤ L) {o o' : ℕ → Fin m → ℤ}
    {i : ℕ} (hiK : i < K) (ho : o (i + 1) = o' (i + 1)) :
    (labelPairLaw M n w L K t o lam).map (slabPair n (i + 1)) =
      (labelPairLaw M n w L K t o' lam).map (slabPair n (i + 1)) := by
  have := hM.probF
  set i' : Fin K := ⟨i, hiK⟩
  have hS : ∀ c ∈ {c : Option (Fin K × (Fin m → ℤ)) | ∃ g, c = some (i', g)}, ∀ e : Edge m,
      cellMap n w L K t o e = c ↔ cellMap n w L K t o' e = c := by
    rintro _ ⟨g, rfl⟩ e
    rw [cellMap_eq_some_iff, cellMap_eq_some_iff]
    exact Iff.of_eq (by simp only [i', ho])
  have hA : ∀ e ∈ slabEdgeSet m n (i + 1),
      cellMap n w L K t o e ∈ {c : Option (Fin K × (Fin m → ℤ)) | ∃ g, c = some (i', g)} :=
    fun e he => exists_cellMap_eq_some (w := w) (t := t) (o := o) hL i' he
  unfold labelPairLaw
  refine map_restrict_pairLaw_congr hS hA fun c hc => ?_
  obtain ⟨g, rfl⟩ := hc
  rw [map_prodMap_labelCoupling, map_subtypeWeightsEquiv]
  congr 1
  funext y
  simp only [Function.comp_apply, cellLabel, Option.map_some, i']
  rw [← ho]
  congr 2
  funext e
  by_cases he : cellMap n w L K t o e = some (⟨i, hiK⟩, g)
  · have he' := (hS _ ⟨g, rfl⟩ e).1 he
    rw [fiberExtend_apply_of_eq _ _ he, fiberExtend_apply_of_eq _ _ he']
    rfl
  · have he' : ¬cellMap n w L K t o' e = some (⟨i, hiK⟩, g) := fun h => he ((hS _ ⟨g, rfl⟩ e).2 h)
    rw [fiberExtend_apply_of_ne _ _ he, fiberExtend_apply_of_ne _ _ he']

end Replacement

end CurvatureVariance.Paper.Gain.LabelResidual
