/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.LabelResidual.Blocks
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity
import CurvatureVariance.Infra.EfronStein.Coordinates
import Mathlib.Probability.Independence.InfinitePi

/-!
# Couplings given a label and products of pair laws

The resampling of Lemma `lem:residual` draws each block conditionally on its label (`X_G` in the
paper, `λ_G` here). This file builds the corresponding laws of pairs (old weights, new weights) by
two generic constructions:

* `labelCoupling ν ℓ`: the law of `(y, y')` with `y ∼ ν` and `y'` drawn from `ν` conditioned on
  `ℓ(y') = ℓ(y)`, for a label `ℓ` with finitely many values and measurable level sets
  (`LabelOK`); its density with respect to `ν ⊗ ν` is `1{ℓ y' = ℓ y}/ν(ℓ = ℓ y)`. It is a
  probability law with first marginal `ν` (`map_fst_labelCoupling`), it is exchangeable
  (`map_swap_labelCoupling`), its integrals are iterated conditional integrals
  (`lintegral_labelCoupling`). For a constant label it is the independent pair
  (`labelCoupling_of_const`), and a measurable equivalence carries it to the label coupling of
  the image (`map_prodMap_labelCoupling`).
* `pairLaw b Q`: the law of a pair of weight families on `E` assembled from independent pair laws
  `Q c` on the fibers of `b : E → ι` (`fiberEquiv`). If every `Q c` has first marginal `F^{⊗}`,
  so does `pairLaw b Q` (`map_fst_pairLaw`). Swapping the two members of the pair on a set `T`
  preserves `pairLaw b Q` when, in every fiber, it preserves `Q c` (`map_swapSplice_pairLaw`);
  then the pair (old, old spliced with new on `T`) is exchangeable
  (`map_splice_eq_of_map_swapSplice`). Resampling one fiber `b⁻¹{c₀}` under `pairLaw b Q` is
  resampling it under `Q c₀` on top of a sample of the product law (`lintegral_pairLaw_splice`,
  with `fiberUpdate`), and if `Q c₀` is a label coupling, it is resampling the fiber from the
  product law conditioned on the label (`lintegral_fiberUpdate_labelCoupling`,
  `lintegral_pairLaw_splice_labelCoupling`). Functions of the fiber pairs of disjoint sets of
  fibers are independent (`iIndepFun_pairLaw`), and the law of the pair on a set of edges depends
  only on the fiber pair laws of the fibers it meets (`map_restrict_pairLaw_congr`).

Throughout, `splice T x x'` takes the weights of `x'` on `T` and those of `x` elsewhere, and
`swapSplice T` exchanges the two members of a pair on `T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper.Gain

/-! ### Splicing -/

section Splice

variable {E : Type*}

open Classical in
/-- `splice T x x'`: the weights of `x'` on `T` and those of `x` elsewhere. -/
noncomputable def splice (T : Set E) (x x' : E → ℝ≥0) : E → ℝ≥0 :=
  fun e => if e ∈ T then x' e else x e

theorem splice_apply_of_mem {T : Set E} {x x' : E → ℝ≥0} {e : E} (he : e ∈ T) :
    splice T x x' e = x' e := by
  classical
  simp [splice, he]

theorem splice_apply_of_notMem {T : Set E} {x x' : E → ℝ≥0} {e : E} (he : e ∉ T) :
    splice T x x' e = x e := by
  classical
  simp [splice, he]

@[simp] theorem splice_univ (x x' : E → ℝ≥0) : splice univ x x' = x' := by
  funext e
  exact splice_apply_of_mem (mem_univ e)

/-- Splicing twice with the roles exchanged recovers the first configuration. -/
theorem splice_splice_swap (T : Set E) (x x' : E → ℝ≥0) :
    splice T (splice T x x') (splice T x' x) = x := by
  funext e
  by_cases he : e ∈ T
  · rw [splice_apply_of_mem he, splice_apply_of_mem he]
  · rw [splice_apply_of_notMem he, splice_apply_of_notMem he]

/-- Splicing is measurable in the pair. -/
theorem measurable_splice (T : Set E) :
    Measurable fun p : (E → ℝ≥0) × (E → ℝ≥0) => splice T p.1 p.2 := by
  refine measurable_pi_iff.mpr fun e => ?_
  by_cases he : e ∈ T
  · simp only [splice_apply_of_mem he]
    exact (measurable_pi_apply e).comp measurable_snd
  · simp only [splice_apply_of_notMem he]
    exact (measurable_pi_apply e).comp measurable_fst

@[simp] theorem splice_empty (x x' : E → ℝ≥0) : splice ∅ x x' = x := by
  funext e
  exact splice_apply_of_notMem (notMem_empty e)

/-- `swapSplice T p`: the exchange of the two members of the pair `p` on `T`. -/
noncomputable def swapSplice (T : Set E) (p : (E → ℝ≥0) × (E → ℝ≥0)) :
    (E → ℝ≥0) × (E → ℝ≥0) :=
  (splice T p.1 p.2, splice T p.2 p.1)

/-- The swap of a pair on `T` is measurable. -/
theorem measurable_swapSplice (T : Set E) : Measurable (swapSplice T) :=
  (measurable_splice T).prodMk ((measurable_splice T).comp measurable_swap)

@[simp] theorem swapSplice_univ : swapSplice (univ : Set E) = Prod.swap := by
  funext p
  simp only [swapSplice, splice_univ]
  rfl

@[simp] theorem swapSplice_empty : swapSplice (∅ : Set E) = id := by
  funext p
  simp [swapSplice]

/-- **Exchangeability from a swap**: if the law of a pair is invariant under the swap on `T`, the
pair (old, old with `T` taken from the new one) is exchangeable. -/
theorem map_splice_eq_of_map_swapSplice {μ : Measure ((E → ℝ≥0) × (E → ℝ≥0))} (T : Set E)
    (h : μ.map (swapSplice T) = μ) :
    μ.map (fun p => (p.1, splice T p.1 p.2)) = μ.map (fun p => (splice T p.1 p.2, p.1)) := by
  have hf : Measurable fun p : (E → ℝ≥0) × (E → ℝ≥0) => (p.1, splice T p.1 p.2) :=
    measurable_fst.prodMk (measurable_splice T)
  conv_lhs => rw [← h]
  rw [Measure.map_map hf (measurable_swapSplice T)]
  congr 1
  funext p
  simp [swapSplice, splice_splice_swap]

end Splice

/-- The resampling of a set of edges of a configuration is the splice of the edges in it. -/
theorem resample_eq_splice {m : ℕ} (G : Set (Sym2 (Vertex m))) (ω ω' : Config m) :
    resample G ω ω' = splice {e : Edge m | e.1 ∈ G} ω ω' := by
  funext e
  by_cases he : e.1 ∈ G
  · rw [splice_apply_of_mem (T := {e : Edge m | e.1 ∈ G}) he]
    simp [resample, he]
  · rw [splice_apply_of_notMem (T := {e : Edge m | e.1 ∈ G}) he]
    simp [resample, he]

/-! ### The coupling given a label -/

section Coupling

variable {Y B : Type*} [MeasurableSpace Y]

/-- A label with finitely many values and measurable level sets. -/
def LabelOK (ℓ : Y → B) : Prop :=
  (Set.range ℓ).Finite ∧ ∀ y, MeasurableSet (ℓ ⁻¹' {ℓ y})

/-- The density `1{ℓ y' = ℓ y}/ν(ℓ = ℓ y)` of the label coupling. -/
noncomputable def labelDensity (ν : Measure Y) (ℓ : Y → B) (z : Y × Y) : ℝ≥0∞ :=
  (ℓ ⁻¹' {ℓ z.1}).indicator (fun _ => (ν (ℓ ⁻¹' {ℓ z.1}))⁻¹) z.2

open Classical in
/-- **The coupling given a label**: the law of `(y, y')`, `y ∼ ν`, `y'` drawn from `ν` conditioned
on `ℓ(y') = ℓ(y)` (the resampling of Lemma `lem:residual`); the independent pair if `ℓ` is not
`LabelOK`. -/
noncomputable def labelCoupling (ν : Measure Y) (ℓ : Y → B) : Measure (Y × Y) :=
  if LabelOK ℓ then (ν.prod ν).withDensity (labelDensity ν ℓ) else ν.prod ν

theorem LabelOK.measurableSet_of_mem {ℓ : Y → B} (h : LabelOK ℓ) {b : B} (hb : b ∈ range ℓ) :
    MeasurableSet (ℓ ⁻¹' {b}) := by
  obtain ⟨y, rfl⟩ := hb
  exact h.2 y

/-- The density of the label coupling is measurable. -/
theorem measurable_labelDensity (ν : Measure Y) {ℓ : Y → B} (h : LabelOK ℓ) :
    Measurable (labelDensity ν ℓ) := by
  classical
  have heq : labelDensity ν ℓ = fun z => ∑ b ∈ h.1.toFinset,
      ((ℓ ⁻¹' {b}) ×ˢ (ℓ ⁻¹' {b})).indicator (fun _ => (ν (ℓ ⁻¹' {b}))⁻¹) z := by
    funext z
    rw [Finset.sum_eq_single (ℓ z.1)]
    · by_cases h2 : z.2 ∈ ℓ ⁻¹' {ℓ z.1}
      · rw [labelDensity, indicator_of_mem h2, indicator_of_mem (mk_mem_prod (by simp) h2)]
      · rw [labelDensity, indicator_of_notMem h2,
          indicator_of_notMem (fun h' => h2 (mem_prod.1 h').2)]
    · intro b _ hb
      exact indicator_of_notMem (fun h' => hb (mem_prod.1 h').1.symm) _
    · intro h'
      exact absurd ((Set.Finite.mem_toFinset h.1).2 ⟨z.1, rfl⟩) h'
  rw [heq]
  refine Finset.measurable_sum _ fun b hb => ?_
  have hm := h.measurableSet_of_mem ((Set.Finite.mem_toFinset h.1).1 hb)
  exact measurable_const.indicator (hm.prod hm)

/-- Almost every point lies in a level set of positive mass. -/
theorem ae_measure_labelSet_ne_zero (ν : Measure Y) {ℓ : Y → B} (h : LabelOK ℓ) :
    ∀ᵐ y ∂ν, ν (ℓ ⁻¹' {ℓ y}) ≠ 0 := by
  rw [ae_iff]
  have hsub : {y | ¬ν (ℓ ⁻¹' {ℓ y}) ≠ 0} ⊆
      ⋃ b ∈ {b | b ∈ range ℓ ∧ ν (ℓ ⁻¹' {b}) = 0}, ℓ ⁻¹' {b} := by
    intro y hy
    simp only [ne_eq, not_not, mem_ofPred_eq] at hy
    exact mem_biUnion ⟨⟨y, rfl⟩, hy⟩ (by simp)
  exact measure_mono_null hsub ((measure_biUnion_null_iff
    (h.1.subset fun b hb => hb.1).countable).2 fun b hb => hb.2)

/-- **Integrals against the label coupling** are iterated conditional integrals:
`∫ f d(labelCoupling ν ℓ) = ∫∫ f(y, y') dν[|ℓ = ℓ y](y') dν(y)`. -/
theorem lintegral_labelCoupling (ν : Measure Y) [SFinite ν] {ℓ : Y → B} (h : LabelOK ℓ)
    {f : Y × Y → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂labelCoupling ν ℓ = ∫⁻ y, ∫⁻ y', f (y, y') ∂(ν[|ℓ ⁻¹' {ℓ y}]) ∂ν := by
  rw [labelCoupling, ite_eq_left h, lintegral_withDensity_eq_lintegral_mul _
    (measurable_labelDensity ν h) hf, lintegral_prod _
    ((measurable_labelDensity ν h).mul hf).aemeasurable]
  refine lintegral_congr fun y => ?_
  have hA := h.2 y
  have hfy : Measurable fun y' => f (y, y') := hf.comp (measurable_const.prodMk measurable_id)
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, ← lintegral_indicator hA,
    ← lintegral_const_mul _ (hfy.indicator hA)]
  refine lintegral_congr fun y' => ?_
  simp only [Pi.mul_apply, labelDensity]
  by_cases hy' : y' ∈ ℓ ⁻¹' {ℓ y}
  · rw [indicator_of_mem hy', indicator_of_mem hy']
  · rw [indicator_of_notMem hy', indicator_of_notMem hy', zero_mul, mul_zero]

/-- The label coupling is a probability law. -/
instance isProbabilityMeasure_labelCoupling (ν : Measure Y) [IsProbabilityMeasure ν]
    (ℓ : Y → B) : IsProbabilityMeasure (labelCoupling ν ℓ) := by
  by_cases h : LabelOK ℓ
  · constructor
    have h1 := lintegral_labelCoupling ν h (f := fun _ => 1) measurable_const
    simp only [lintegral_one] at h1
    rw [h1]
    have hae : (fun y => (ν[|ℓ ⁻¹' {ℓ y}]) univ) =ᵐ[ν] fun _ => 1 := by
      filter_upwards [ae_measure_labelSet_ne_zero ν h] with y hy
      have := cond_isProbabilityMeasure (μ := ν) hy
      exact measure_univ
    rw [lintegral_congr_ae hae, lintegral_one, measure_univ]
  · rw [labelCoupling, ite_eq_right h]
    infer_instance

/-- The first marginal of the label coupling is `ν`. -/
theorem map_fst_labelCoupling (ν : Measure Y) [IsProbabilityMeasure ν] (ℓ : Y → B) :
    (labelCoupling ν ℓ).map Prod.fst = ν := by
  by_cases h : LabelOK ℓ
  · ext S hS
    rw [Measure.map_apply measurable_fst hS, ← lintegral_indicator_one (measurable_fst hS),
      lintegral_labelCoupling ν h (f := (Prod.fst ⁻¹' S).indicator 1)
        (measurable_one.indicator (measurable_fst hS))]
    have hae : (fun y => ∫⁻ y', (Prod.fst ⁻¹' S).indicator 1 (y, y') ∂(ν[|ℓ ⁻¹' {ℓ y}])) =ᵐ[ν]
        S.indicator 1 := by
      filter_upwards [ae_measure_labelSet_ne_zero ν h] with y hy
      have := cond_isProbabilityMeasure (μ := ν) hy
      by_cases hyS : y ∈ S
      · simp [hyS, indicator_of_mem]
      · simp [hyS, indicator_of_notMem]
    rw [lintegral_congr_ae hae, lintegral_indicator_one hS]
  · rw [labelCoupling, ite_eq_right h, Measure.map_fst_prod, measure_univ, one_smul]

/-- **The label coupling is exchangeable.** -/
theorem map_swap_labelCoupling (ν : Measure Y) [SFinite ν] (ℓ : Y → B) :
    (labelCoupling ν ℓ).map Prod.swap = labelCoupling ν ℓ := by
  by_cases h : LabelOK ℓ
  · have hsym : ∀ z : Y × Y, labelDensity ν ℓ z.swap = labelDensity ν ℓ z := by
      intro z
      simp only [labelDensity, Prod.fst_swap, Prod.snd_swap]
      by_cases hz : ℓ z.2 = ℓ z.1
      · rw [hz, indicator_of_mem (show z.1 ∈ ℓ ⁻¹' {ℓ z.1} from rfl),
          indicator_of_mem (show z.2 ∈ ℓ ⁻¹' {ℓ z.1} from hz)]
      · rw [indicator_of_notMem (show z.1 ∉ ℓ ⁻¹' {ℓ z.2} from fun h' => hz h'.symm),
          indicator_of_notMem (show z.2 ∉ ℓ ⁻¹' {ℓ z.1} from hz)]
    ext S hS
    rw [Measure.map_apply measurable_swap hS, labelCoupling, ite_eq_left h,
      withDensity_apply _ (measurable_swap hS), withDensity_apply _ hS]
    calc ∫⁻ z in Prod.swap ⁻¹' S, labelDensity ν ℓ z ∂ν.prod ν
        = ∫⁻ z in Prod.swap ⁻¹' S, labelDensity ν ℓ z.swap ∂ν.prod ν := by simp_rw [hsym]
      _ = ∫⁻ z in S, labelDensity ν ℓ z ∂ν.prod ν :=
          Measure.measurePreserving_swap.setLIntegral_comp_preimage hS
            (measurable_labelDensity ν h)
  · rw [labelCoupling, ite_eq_right h, Measure.prod_swap]

/-- For a constant label, the label coupling is the independent pair. -/
theorem labelCoupling_of_const (ν : Measure Y) [IsProbabilityMeasure ν] {ℓ : Y → B}
    (hℓ : ∀ y y', ℓ y = ℓ y') : labelCoupling ν ℓ = ν.prod ν := by
  unfold labelCoupling
  split_ifs with h
  · have h1 : labelDensity ν ℓ = 1 := by
      funext z
      have hs : ℓ ⁻¹' {ℓ z.1} = univ := eq_univ_of_forall fun y => hℓ y z.1
      simp only [labelDensity, hs, measure_univ, inv_one, indicator_univ, Pi.one_apply]
    rw [h1, withDensity_one]
  · rfl

/-- An integral against `ν` conditioned on the level set of `y` is an integral against `ν` with
the density `1{ℓ y' = ℓ y}/ν(ℓ = ℓ y)`. -/
theorem lintegral_cond_eq_lintegral_labelDensity (ν : Measure Y) {ℓ : Y → B} {y : Y}
    (hy : MeasurableSet (ℓ ⁻¹' {ℓ y})) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y', f y' ∂(ν[|ℓ ⁻¹' {ℓ y}]) = ∫⁻ y', labelDensity ν ℓ (y, y') * f y' ∂ν := by
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, ← lintegral_indicator hy,
    ← lintegral_const_mul _ (hf.indicator hy)]
  refine lintegral_congr fun y' => ?_
  simp only [labelDensity]
  by_cases hy' : y' ∈ ℓ ⁻¹' {ℓ y}
  · rw [indicator_of_mem hy', indicator_of_mem hy']
  · rw [indicator_of_notMem hy', indicator_of_notMem hy', zero_mul, mul_zero]

/-- Conditioning commutes with the image under a measurable map. -/
theorem cond_map {Y' : Type*} [MeasurableSpace Y'] (ν : Measure Y) {π : Y → Y'}
    (hπ : Measurable π) {S : Set Y'} (hS : MeasurableSet S) :
    (ν.map π)[|S] = (ν[|π ⁻¹' S]).map π := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul, Measure.map_apply hπ hS,
    Measure.restrict_map hπ hS]
  exact hπ.aemeasurable

/-- A measurable equivalence carries the label coupling to the label coupling of the image law
and the transported label. -/
theorem map_prodMap_labelCoupling {Y' : Type*} [MeasurableSpace Y'] (ν : Measure Y)
    [IsProbabilityMeasure ν] (τ : Y ≃ᵐ Y') (ℓ : Y → B) :
    (labelCoupling ν ℓ).map (Prod.map τ τ) = labelCoupling (ν.map τ) (ℓ ∘ τ.symm) := by
  have hτ : Measurable (Prod.map τ τ) := τ.measurable.prodMap τ.measurable
  have hiff : LabelOK (ℓ ∘ τ.symm) ↔ LabelOK ℓ := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rwa [τ.symm.surjective.range_comp] at h1, fun y => ?_⟩
      have hset : ℓ ⁻¹' {ℓ y} = τ ⁻¹' ((ℓ ∘ τ.symm) ⁻¹' {(ℓ ∘ τ.symm) (τ y)}) := by
        ext y'
        simp
      rw [hset]
      exact τ.measurable (h2 _)
    · rintro ⟨h1, h2⟩
      refine ⟨by rwa [τ.symm.surjective.range_comp], fun y' => ?_⟩
      exact τ.symm.measurable (h2 (τ.symm y'))
  by_cases h : LabelOK ℓ
  · have h' := hiff.2 h
    rw [labelCoupling, ite_eq_left h, labelCoupling, ite_eq_left h',
      Measure.map_prod_map ν ν τ.measurable τ.measurable]
    ext S hS
    rw [Measure.map_apply hτ hS, withDensity_apply _ (hτ hS), withDensity_apply _ hS,
      setLIntegral_map hS (measurable_labelDensity _ h') hτ]
    refine setLIntegral_congr_fun (hτ hS) fun z _ => ?_
    have hset : (ℓ ∘ τ.symm) ⁻¹' {(ℓ ∘ τ.symm) (τ z.1)} = τ.symm ⁻¹' (ℓ ⁻¹' {ℓ z.1}) := by
      ext y'
      simp
    simp only [labelDensity, Prod.map_fst, Prod.map_snd]
    have hpre : τ ⁻¹' (τ.symm ⁻¹' (ℓ ⁻¹' {ℓ z.1})) = ℓ ⁻¹' {ℓ z.1} := by
      ext y'
      simp
    rw [hset, MeasurableEquiv.map_apply, hpre]
    by_cases hz : z.2 ∈ ℓ ⁻¹' {ℓ z.1}
    · rw [indicator_of_mem hz, indicator_of_mem (show τ z.2 ∈ τ.symm ⁻¹' (ℓ ⁻¹' {ℓ z.1}) by
        simpa using hz)]
    · rw [indicator_of_notMem hz, indicator_of_notMem (show τ z.2 ∉ τ.symm ⁻¹' (ℓ ⁻¹' {ℓ z.1}) by
        simpa using hz)]
  · have h' : ¬LabelOK (ℓ ∘ τ.symm) := fun h' => h (hiff.1 h')
    rw [labelCoupling, ite_eq_right h, labelCoupling, ite_eq_right h',
      Measure.map_prod_map ν ν τ.measurable τ.measurable]

end Coupling

/-! ### Operations on the fibers of a map -/

section FiberOps

variable {E ι : Type*} (b : E → ι)

/-- The value of a weight family on the fibers at `e`, read in the fiber `c` of `e`. -/
theorem fiber_apply_eq' (x : ∀ c : ι, ({e : E // b e = c} → ℝ≥0)) (e : E) (c : ι)
    (h : b e = c) : x (b e) ⟨e, rfl⟩ = x c ⟨e, h⟩ := by
  subst h
  rfl

/-- A family indexed by the points of `S ⊆ ι` takes the same value at a point `e` of the fiber
of `c` and of the fiber of `c' = c`. -/
theorem fiber_apply_congr {S : Set ι} (s : ∀ c : S, ({e : E // b e = c.1} → ℝ≥0)) {c c' : S}
    (hc : c = c') (e : E) (h : b e = c.1) (h' : b e = c'.1) : s c ⟨e, h⟩ = s c' ⟨e, h'⟩ := by
  subst hc
  rfl

open Classical in
/-- `fiberExtend b c y`: the weights `y` of the fiber `b⁻¹{c}`, extended by `0` off the fiber. -/
noncomputable def fiberExtend (c : ι) (y : {e : E // b e = c} → ℝ≥0) : E → ℝ≥0 :=
  fun e => if h : b e = c then y ⟨e, h⟩ else 0

theorem fiberExtend_apply_of_eq {c : ι} (y : {e : E // b e = c} → ℝ≥0) {e : E} (h : b e = c) :
    fiberExtend b c y e = y ⟨e, h⟩ := by
  unfold fiberExtend
  exact dite_eq_left h

theorem fiberExtend_apply_of_ne {c : ι} (y : {e : E // b e = c} → ℝ≥0) {e : E} (h : ¬b e = c) :
    fiberExtend b c y e = 0 := by
  unfold fiberExtend
  exact dite_eq_right h

theorem measurable_fiberExtend (c : ι) : Measurable (fiberExtend b c) := by
  refine measurable_pi_iff.2 fun e => ?_
  by_cases h : b e = c
  · have heq : (fun y => fiberExtend b c y e) = fun y => y ⟨e, h⟩ :=
      funext fun y => fiberExtend_apply_of_eq b y h
    rw [heq]
    exact measurable_pi_apply _
  · have heq : (fun y => fiberExtend b c y e) = fun _ => 0 :=
      funext fun y => fiberExtend_apply_of_ne b y h
    rw [heq]
    exact measurable_const

/-- The extension of the weights of `ω` on a fiber agrees with `ω` on the fiber. -/
theorem fiberExtend_fiberEquiv {c : ι} (ω : E → ℝ≥0) {e : E} (h : b e = c) :
    fiberExtend b c (fiberEquiv b ω c) e = ω e := by
  rw [fiberExtend_apply_of_eq b _ h]
  rfl

/-- The law of the weights of one fiber. -/
theorem map_fiberEquiv_apply (F : Measure ℝ≥0) [IsProbabilityMeasure F] (c : ι) :
    (Measure.infinitePi fun _ : E => F).map (fun ω => fiberEquiv b ω c) =
      Measure.infinitePi fun _ : {e : E // b e = c} => F := by
  have h : (fun ω => fiberEquiv b ω c) = (fun y => y c) ∘ fiberEquiv b := rfl
  rw [h, ← Measure.map_map (measurable_pi_apply c) (fiberEquiv b).measurable, map_fiberEquiv,
    Measure.infinitePi_map_eval]

/-- Weights on `{e // p e}` read as weights on `{e // p' e}`, for equivalent predicates. -/
def subtypeWeightsEquiv {p p' : E → Prop} (h : ∀ e, p e ↔ p' e) :
    ({e : E // p e} → ℝ≥0) ≃ᵐ ({e : E // p' e} → ℝ≥0) where
  toFun y e := y ⟨e.1, (h e.1).2 e.2⟩
  invFun y e := y ⟨e.1, (h e.1).1 e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_pi_iff.2 fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- The product law is carried to the product law. -/
theorem map_subtypeWeightsEquiv (F : Measure ℝ≥0) [IsProbabilityMeasure F] {p p' : E → Prop}
    (h : ∀ e, p e ↔ p' e) :
    (Measure.infinitePi fun _ : {e : E // p e} => F).map (subtypeWeightsEquiv h) =
      Measure.infinitePi fun _ : {e : E // p' e} => F :=
  Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : {e : E // p e} => F)
    (f := fun e : {e : E // p' e} => (⟨e.1, (h e.1).2 e.2⟩ : {e : E // p e}))
    fun _ _ haa => Subtype.ext (congrArg Subtype.val haa :)

variable [DecidableEq ι]

/-- `fiberUpdate b c ω a`: the weights `a` on the fiber `b⁻¹{c}` and those of `ω` elsewhere. -/
noncomputable def fiberUpdate (c : ι) (ω : E → ℝ≥0) (a : {e : E // b e = c} → ℝ≥0) : E → ℝ≥0 :=
  (fiberEquiv b).symm (Function.update (fiberEquiv b ω) c a)

@[simp] theorem fiberEquiv_fiberUpdate (c : ι) (ω : E → ℝ≥0) (a : {e : E // b e = c} → ℝ≥0) :
    fiberEquiv b (fiberUpdate b c ω a) c = a := by
  simp [fiberUpdate]

@[simp] theorem fiberUpdate_fiberUpdate (c : ι) (ω : E → ℝ≥0) (a a' : {e : E // b e = c} → ℝ≥0) :
    fiberUpdate b c (fiberUpdate b c ω a) a' = fiberUpdate b c ω a' := by
  simp [fiberUpdate]

theorem measurable_fiberUpdate (c : ι) :
    Measurable fun q : (E → ℝ≥0) × ({e : E // b e = c} → ℝ≥0) => fiberUpdate b c q.1 q.2 :=
  (fiberEquiv b).symm.measurable.comp
    (measurable_update'.comp ((fiberEquiv b).measurable.prodMap measurable_id))

/-- Splicing in the fiber `b⁻¹{c}` replaces the fiber coordinate `c`. -/
theorem splice_fiberEquiv_symm (c : ι) (y y' : ∀ c : ι, ({e : E // b e = c} → ℝ≥0)) :
    splice {e | b e = c} ((fiberEquiv b).symm y) ((fiberEquiv b).symm y') =
      (fiberEquiv b).symm (Function.update y c (y' c)) := by
  funext e
  by_cases h : b e = c
  · rw [splice_apply_of_mem (show e ∈ {e | b e = c} from h), fiberEquiv_symm_apply,
      fiberEquiv_symm_apply, fiber_apply_eq' b y' e c h,
      fiber_apply_eq' b (Function.update y c (y' c)) e c h, Function.update_self]
  · rw [splice_apply_of_notMem (show e ∉ {e | b e = c} from h), fiberEquiv_symm_apply,
      fiberEquiv_symm_apply, Function.update_of_ne h]

/-- Splicing in a fiber is updating the fiber. -/
theorem splice_eq_fiberUpdate (c : ι) (ω ω' : E → ℝ≥0) :
    splice {e | b e = c} ω ω' = fiberUpdate b c ω (fiberEquiv b ω' c) := by
  have h := splice_fiberEquiv_symm b c (fiberEquiv b ω) (fiberEquiv b ω')
  rwa [MeasurableEquiv.symm_apply_apply, MeasurableEquiv.symm_apply_apply] at h

/-- **Resampling one fiber preserves the product law**: `(ω, a) ↦ ω` with the weights `a` on the
fiber `b⁻¹{c}` maps `F^{⊗E} ⊗ F^{⊗ b⁻¹{c}}` to `F^{⊗E}`. -/
theorem measurePreserving_fiberUpdate (F : Measure ℝ≥0) [IsProbabilityMeasure F] (c : ι) :
    MeasurePreserving (fun q : (E → ℝ≥0) × ({e : E // b e = c} → ℝ≥0) => fiberUpdate b c q.1 q.2)
      ((Measure.infinitePi fun _ : E => F).prod
        (Measure.infinitePi fun _ : {e : E // b e = c} => F))
      (Measure.infinitePi fun _ : E => F) := by
  have h1 : MeasurePreserving (fiberEquiv b) (Measure.infinitePi fun _ : E => F)
      (Measure.infinitePi fun c : ι => Measure.infinitePi fun _ : {e : E // b e = c} => F) :=
    ⟨(fiberEquiv b).measurable, map_fiberEquiv b F⟩
  have h2 := Infra.EfronStein.measurePreserving_update_infinitePi
    (fun c : ι => Measure.infinitePi fun _ : {e : E // b e = c} => F) c
  exact (h1.symm (fiberEquiv b)).comp (h2.comp (h1.prod (MeasurePreserving.id _)))

end FiberOps

/-! ### Products of pair laws over the fibers of a map -/

section PairLaw

variable {E ι : Type*} (b : E → ι)

/-- The two weight families of a family of pairs indexed by the fibers. -/
noncomputable def pairMap (r : ∀ c : ι, ({e : E // b e = c} → ℝ≥0) × ({e : E // b e = c} → ℝ≥0)) :
    (E → ℝ≥0) × (E → ℝ≥0) :=
  ((fiberEquiv b).symm fun c => (r c).1, (fiberEquiv b).symm fun c => (r c).2)

theorem measurable_pairMap : Measurable (pairMap b) :=
  ((MeasurableEquiv.measurable _).comp (measurable_pi_iff.2 fun c =>
      measurable_fst.comp (measurable_pi_apply c))).prodMk
    ((MeasurableEquiv.measurable _).comp (measurable_pi_iff.2 fun c =>
      measurable_snd.comp (measurable_pi_apply c)))

/-- The first members of the fiber pairs. -/
theorem measurable_fiberFst :
    Measurable fun (r : ∀ c : ι, ({e : E // b e = c} → ℝ≥0) × ({e : E // b e = c} → ℝ≥0))
      (c : ι) => (r c).1 :=
  measurable_pi_iff.2 fun c => measurable_fst.comp (measurable_pi_apply c)

variable (Q : ∀ c : ι, Measure (({e : E // b e = c} → ℝ≥0) × ({e : E // b e = c} → ℝ≥0)))

/-- **The pair law assembled from independent pair laws on the fibers.** -/
noncomputable def pairLaw : Measure ((E → ℝ≥0) × (E → ℝ≥0)) :=
  (Measure.infinitePi Q).map (pairMap b)

instance isProbabilityMeasure_pairLaw [∀ c, IsProbabilityMeasure (Q c)] :
    IsProbabilityMeasure (pairLaw b Q) := by
  unfold pairLaw
  infer_instance

/-- The first members of the fiber pairs have the product law if the first marginals of the
fiber pair laws do. -/
theorem map_fiberFst_infinitePi [∀ c, IsProbabilityMeasure (Q c)] (F : Measure ℝ≥0)
    [IsProbabilityMeasure F]
    (hfst : ∀ c, (Q c).map Prod.fst = Measure.infinitePi fun _ : {e : E // b e = c} => F) :
    (Measure.infinitePi Q).map (fun r c => (r c).1) =
      (Measure.infinitePi fun _ : E => F).map (fiberEquiv b) := by
  rw [Measure.infinitePi_map_pi _ (fun c => measurable_fst), map_fiberEquiv b F]
  congr 1
  funext c
  exact hfst c

/-- The first member of the pair has the product law if the first marginals of the fiber pair
laws do. -/
theorem map_fst_pairLaw [∀ c, IsProbabilityMeasure (Q c)] (F : Measure ℝ≥0)
    [IsProbabilityMeasure F]
    (hfst : ∀ c, (Q c).map Prod.fst = Measure.infinitePi fun _ : {e : E // b e = c} => F) :
    (pairLaw b Q).map Prod.fst = Measure.infinitePi fun _ : E => F := by
  have h1 : Prod.fst ∘ pairMap b = (fiberEquiv b).symm ∘ fun r c => (r c).1 := rfl
  rw [pairLaw, Measure.map_map measurable_fst (measurable_pairMap b), h1,
    ← Measure.map_map (fiberEquiv b).symm.measurable (measurable_fiberFst b),
    map_fiberFst_infinitePi b Q F hfst,
    Measure.map_map (fiberEquiv b).symm.measurable (fiberEquiv b).measurable]
  simp

/-- Exchanging the two members of the pair on `T` is exchanging them on `T` in every fiber. -/
theorem swapSplice_pairMap (T : Set E)
    (r : ∀ c : ι, ({e : E // b e = c} → ℝ≥0) × ({e : E // b e = c} → ℝ≥0)) :
    swapSplice T (pairMap b r) = pairMap b fun c => swapSplice {e | e.1 ∈ T} (r c) := by
  classical
  refine Prod.ext (funext fun e => ?_) (funext fun e => ?_) <;>
  · by_cases he : e ∈ T <;> simp [swapSplice, pairMap, splice, he]

/-- **Swapping on a set preserves the pair law** if, in every fiber, it preserves the fiber pair
law. -/
theorem map_swapSplice_pairLaw [∀ c, IsProbabilityMeasure (Q c)] (T : Set E)
    (hQ : ∀ c, (Q c).map (swapSplice {e | e.1 ∈ T}) = Q c) :
    (pairLaw b Q).map (swapSplice T) = pairLaw b Q := by
  have hm : Measurable fun (r : ∀ c : ι, ({e : E // b e = c} → ℝ≥0) × ({e : E // b e = c} → ℝ≥0))
      (c : ι) => swapSplice {e | e.1 ∈ T} (r c) :=
    measurable_pi_iff.2 fun c => (measurable_swapSplice _).comp (measurable_pi_apply c)
  have h1 : swapSplice T ∘ pairMap b = pairMap b ∘ fun r c => swapSplice {e | e.1 ∈ T} (r c) :=
    funext fun r => swapSplice_pairMap b T r
  rw [pairLaw, Measure.map_map (measurable_swapSplice T) (measurable_pairMap b), h1,
    ← Measure.map_map (measurable_pairMap b) hm,
    Measure.infinitePi_map_pi _ (fun c => measurable_swapSplice _)]
  congr 2
  funext c
  exact hQ c

/-- **Resampling one fiber under the pair law**: the pair (old weights, old weights with the
fiber `b⁻¹{c₀}` taken from the new ones) has the law of `(ω[c₀ ↦ z₁], ω[c₀ ↦ z₂])`, `ω` drawn from
the product law and `z` from `Q c₀`, independently. -/
theorem lintegral_pairLaw_splice [DecidableEq ι] [∀ c, IsProbabilityMeasure (Q c)]
    (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hfst : ∀ c, (Q c).map Prod.fst = Measure.infinitePi fun _ : {e : E // b e = c} => F)
    (c₀ : ι) {H : (E → ℝ≥0) × (E → ℝ≥0) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x, H (x.1, splice {e | b e = c₀} x.1 x.2) ∂pairLaw b Q =
      ∫⁻ ω, ∫⁻ z, H (fiberUpdate b c₀ ω z.1, fiberUpdate b c₀ ω z.2) ∂Q c₀
        ∂Measure.infinitePi fun _ : E => F := by
  set T : Set E := {e | b e = c₀}
  set V : (∀ c : ι, ({e : E // b e = c} → ℝ≥0)) →
      (({e : E // b e = c₀} → ℝ≥0) × ({e : E // b e = c₀} → ℝ≥0)) → ℝ≥0∞ :=
    fun y z => H ((fiberEquiv b).symm (Function.update y c₀ z.1),
      (fiberEquiv b).symm (Function.update y c₀ z.2)) with hV
  have hVm : Measurable fun q : (∀ c : ι, ({e : E // b e = c} → ℝ≥0)) ×
      (({e : E // b e = c₀} → ℝ≥0) × ({e : E // b e = c₀} → ℝ≥0)) => V q.1 q.2 := by
    refine hH.comp (Measurable.prodMk ?_ ?_)
    · exact (fiberEquiv b).symm.measurable.comp
        (measurable_update'.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    · exact (fiberEquiv b).symm.measurable.comp
        (measurable_update'.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hF : Measurable fun x : (E → ℝ≥0) × (E → ℝ≥0) => H (x.1, splice T x.1 x.2) :=
    hH.comp (measurable_fst.prodMk (measurable_splice T))
  have hkey : ∀ r z, (fun x : (E → ℝ≥0) × (E → ℝ≥0) => H (x.1, splice T x.1 x.2))
      (pairMap b (Function.update r c₀ z)) = V (fun c => (r c).1) z := by
    intro r z
    have h1 : (fun c => (Function.update r c₀ z c).1) = Function.update (fun c => (r c).1) c₀ z.1 :=
      funext fun c => Function.apply_update (fun _ p => p.1) r c₀ z c
    simp only [pairMap, hV]
    rw [splice_fiberEquiv_symm b c₀, h1, Function.update_idem, Function.update_self]
  have hg : Measurable fun y => ∫⁻ z, V y z ∂Q c₀ := hVm.lintegral_prod_right'
  calc ∫⁻ x, H (x.1, splice T x.1 x.2) ∂pairLaw b Q
      = ∫⁻ r, (fun x : (E → ℝ≥0) × (E → ℝ≥0) => H (x.1, splice T x.1 x.2)) (pairMap b r)
          ∂Measure.infinitePi Q := lintegral_map hF (measurable_pairMap b)
    _ = ∫⁻ q, (fun x : (E → ℝ≥0) × (E → ℝ≥0) => H (x.1, splice T x.1 x.2))
          (pairMap b (Function.update q.1 c₀ q.2)) ∂(Measure.infinitePi Q).prod (Q c₀) :=
        ((Infra.EfronStein.measurePreserving_update_infinitePi Q c₀).lintegral_comp
          (hF.comp (measurable_pairMap b))).symm
    _ = ∫⁻ q, V (fun c => (q.1 c).1) q.2 ∂(Measure.infinitePi Q).prod (Q c₀) :=
        lintegral_congr fun q => hkey q.1 q.2
    _ = ∫⁻ r, ∫⁻ z, V (fun c => (r c).1) z ∂Q c₀ ∂Measure.infinitePi Q :=
        lintegral_prod _ (hVm.comp ((measurable_fiberFst b).prodMap measurable_id)).aemeasurable
    _ = ∫⁻ y, ∫⁻ z, V y z ∂Q c₀ ∂(Measure.infinitePi Q).map (fun r c => (r c).1) :=
        (lintegral_map hg (measurable_fiberFst b)).symm
    _ = ∫⁻ y, ∫⁻ z, V y z ∂Q c₀ ∂(Measure.infinitePi fun _ : E => F).map (fiberEquiv b) := by
        rw [map_fiberFst_infinitePi b Q F hfst]
    _ = _ := lintegral_map hg (fiberEquiv b).measurable

/-- Independence passes to the image measure. -/
theorem iIndepFun_map_of_comp {Ω Ω' κ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {β : κ → Type*} [∀ k, MeasurableSpace (β k)] {μ : Measure Ω} {φ : Ω → Ω'}
    (hφ : Measurable φ) {f : ∀ k, Ω' → β k} (hf : ∀ k, Measurable (f k))
    (h : iIndepFun (fun k ω => f k (φ ω)) μ) : iIndepFun f (μ.map φ) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s sets hsets
  calc (μ.map φ) (⋂ k ∈ s, f k ⁻¹' sets k)
      = μ (⋂ k ∈ s, (fun ω => f k (φ ω)) ⁻¹' sets k) := by
        rw [Measure.map_apply hφ (Finset.measurableSet_biInter s fun k hk => hf k (hsets k hk))]
        congr 1
        ext ω
        simp
    _ = ∏ k ∈ s, μ ((fun ω => f k (φ ω)) ⁻¹' sets k) := h s hsets
    _ = ∏ k ∈ s, (μ.map φ) (f k ⁻¹' sets k) :=
        Finset.prod_congr rfl fun k hk => (Measure.map_apply hφ (hf k (hsets k hk))).symm

/-- **Independence under the pair law**: functions of the pair which read the fiber pairs of
pairwise disjoint sets of fibers are independent. -/
theorem iIndepFun_pairLaw [∀ c, IsProbabilityMeasure (Q c)] {κ : Type*} {β : κ → Type*}
    [∀ k, MeasurableSpace (β k)] (S : κ → Set ι) (hS : Pairwise fun k k' => Disjoint (S k) (S k'))
    {f : ∀ k, (E → ℝ≥0) × (E → ℝ≥0) → β k} (hf : ∀ k, Measurable (f k))
    (G : ∀ k, (∀ c : S k, ({e : E // b e = c.1} → ℝ≥0) × ({e : E // b e = c.1} → ℝ≥0)) → β k)
    (hG : ∀ k, Measurable (G k)) (hfG : ∀ k r, f k (pairMap b r) = G k fun c => r c) :
    iIndepFun f (pairLaw b Q) := by
  refine iIndepFun_map_of_comp (measurable_pairMap b) hf ?_
  have heq : (fun k r => f k (pairMap b r)) = fun k r => G k fun c : S k => r c := by
    funext k r
    exact hfG k r
  rw [heq]
  exact Infra.EfronStein.iIndepFun_comp_restrict_infinitePi Q S hS G hG

/-- **The law of the pair on a set of edges depends only on the fibers it meets**: if `b` and `b'`
have the same fibers over `S`, the edges of `A` lie in fibers over `S`, and the fiber pair laws over
`S` correspond, then the pair restricted to `A` has the same law under `pairLaw b Q` and
`pairLaw b' Q'`. -/
theorem map_restrict_pairLaw_congr {b b' : E → ι}
    {Q : ∀ c : ι, Measure (({e : E // b e = c} → ℝ≥0) × ({e : E // b e = c} → ℝ≥0))}
    {Q' : ∀ c : ι, Measure (({e : E // b' e = c} → ℝ≥0) × ({e : E // b' e = c} → ℝ≥0))}
    [∀ c, IsProbabilityMeasure (Q c)] [∀ c, IsProbabilityMeasure (Q' c)] {S : Set ι}
    (hS : ∀ c ∈ S, ∀ e, b e = c ↔ b' e = c) {A : Set E} (hA : ∀ e ∈ A, b e ∈ S)
    (hQ : ∀ c (hc : c ∈ S), (Q c).map (Prod.map (subtypeWeightsEquiv (hS c hc))
      (subtypeWeightsEquiv (hS c hc))) = Q' c) :
    (pairLaw b Q).map (fun x => ((fun e : A => x.1 e), fun e : A => x.2 e)) =
      (pairLaw b' Q').map (fun x => ((fun e : A => x.1 e), fun e : A => x.2 e)) := by
  have hbb : ∀ e ∈ A, b' e = b e := fun e he => (hS (b e) (hA e he) e).1 rfl
  have hA' : ∀ e ∈ A, b' e ∈ S := fun e he => (hbb e he).symm ▸ hA e he
  have hR : Measurable fun x : (E → ℝ≥0) × (E → ℝ≥0) =>
      ((fun e : A => x.1 e), fun e : A => x.2 e) :=
    (measurable_pi_iff.2 fun e => (measurable_pi_apply e.1).comp measurable_fst).prodMk
      (measurable_pi_iff.2 fun e => (measurable_pi_apply e.1).comp measurable_snd)
  let Ψ : (∀ c : S, ({e : E // b e = c.1} → ℝ≥0) × ({e : E // b e = c.1} → ℝ≥0)) →
      (A → ℝ≥0) × (A → ℝ≥0) := fun s =>
    (fun e => (s ⟨b e, hA e e.2⟩).1 ⟨e, rfl⟩, fun e => (s ⟨b e, hA e e.2⟩).2 ⟨e, rfl⟩)
  let Ψ' : (∀ c : S, ({e : E // b' e = c.1} → ℝ≥0) × ({e : E // b' e = c.1} → ℝ≥0)) →
      (A → ℝ≥0) × (A → ℝ≥0) := fun s =>
    (fun e => (s ⟨b' e, hA' e e.2⟩).1 ⟨e, rfl⟩, fun e => (s ⟨b' e, hA' e e.2⟩).2 ⟨e, rfl⟩)
  have hΨ : Measurable Ψ :=
    (measurable_pi_iff.2 fun e => (measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _))).prodMk
      (measurable_pi_iff.2 fun e => (measurable_pi_apply _).comp
        (measurable_snd.comp (measurable_pi_apply _)))
  have hΨ' : Measurable Ψ' :=
    (measurable_pi_iff.2 fun e => (measurable_pi_apply _).comp
      (measurable_fst.comp (measurable_pi_apply _))).prodMk
      (measurable_pi_iff.2 fun e => (measurable_pi_apply _).comp
        (measurable_snd.comp (measurable_pi_apply _)))
  let τ : ∀ c : S, (({e : E // b e = c.1} → ℝ≥0) × ({e : E // b e = c.1} → ℝ≥0)) →
      (({e : E // b' e = c.1} → ℝ≥0) × ({e : E // b' e = c.1} → ℝ≥0)) := fun c =>
    Prod.map (subtypeWeightsEquiv (hS c.1 c.2)) (subtypeWeightsEquiv (hS c.1 c.2))
  have hτ : ∀ c, Measurable (τ c) := fun c =>
    (subtypeWeightsEquiv (hS c.1 c.2)).measurable.prodMap
      (subtypeWeightsEquiv (hS c.1 c.2)).measurable
  have hτm : Measurable fun (s : ∀ c : S, ({e : E // b e = c.1} → ℝ≥0) ×
      ({e : E // b e = c.1} → ℝ≥0)) (c : S) => τ c (s c) :=
    measurable_pi_iff.2 fun c => (hτ c).comp (measurable_pi_apply c)
  have h1 : (fun x : (E → ℝ≥0) × (E → ℝ≥0) => ((fun e : A => x.1 e), fun e : A => x.2 e)) ∘
      pairMap b = Ψ ∘ S.domRestrict := rfl
  have h1' : (fun x : (E → ℝ≥0) × (E → ℝ≥0) => ((fun e : A => x.1 e), fun e : A => x.2 e)) ∘
      pairMap b' = Ψ' ∘ S.domRestrict := rfl
  have h2 : Ψ' ∘ (fun s c => τ c (s c)) = Ψ := by
    funext s
    refine Prod.ext (funext fun e => ?_) (funext fun e => ?_)
    · exact fiber_apply_congr b (fun c => (s c).1) (Subtype.ext (hbb e e.2)) e _ _
    · exact fiber_apply_congr b (fun c => (s c).2) (Subtype.ext (hbb e e.2)) e _ _
  have h3 : (Measure.infinitePi fun c : S => Q' c.1) =
      (Measure.infinitePi fun c : S => Q c.1).map fun s c => τ c (s c) := by
    rw [Measure.infinitePi_map_pi _ hτ]
    congr 1
    funext c
    exact (hQ c.1 c.2).symm
  rw [pairLaw, pairLaw, Measure.map_map hR (measurable_pairMap b),
    Measure.map_map hR (measurable_pairMap b'), h1, h1',
    ← Measure.map_map hΨ (Set.measurable_restrict S),
    ← Measure.map_map hΨ' (Set.measurable_restrict S),
    Measure.infinitePi_map_restrict', Measure.infinitePi_map_restrict', h3,
    Measure.map_map hΨ' hτm, h2]

end PairLaw

/-! ### Resampling a fiber given its label -/

section LabelFiber

variable {E ι B : Type*} (b : E → ι) [DecidableEq ι]

/-- **Resampling a fiber given its label**: if `ω` has the product law and `z` the label
coupling of the fiber `b⁻¹{c₀}` independently, then `(ω[c₀ ↦ z₁], ω[c₀ ↦ z₂])` has the law of
`(ω, ω^{c₀,ω'})`, `ω'` drawn from the product law conditioned on the label of the fiber being that
of `ω`. -/
theorem lintegral_fiberUpdate_labelCoupling (F : Measure ℝ≥0) [IsProbabilityMeasure F] (c₀ : ι)
    {ℓ : ({e : E // b e = c₀} → ℝ≥0) → B} (hℓ : LabelOK ℓ)
    {H : (E → ℝ≥0) × (E → ℝ≥0) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, ∫⁻ z, H (fiberUpdate b c₀ ω z.1, fiberUpdate b c₀ ω z.2)
        ∂labelCoupling (Measure.infinitePi fun _ : {e : E // b e = c₀} => F) ℓ
        ∂Measure.infinitePi (fun _ : E => F) =
      ∫⁻ ω, ∫⁻ ω', H (ω, splice {e | b e = c₀} ω ω')
        ∂((Measure.infinitePi fun _ : E => F)[|(fun ω => ℓ (fiberEquiv b ω c₀)) ⁻¹'
          {ℓ (fiberEquiv b ω c₀)}])
        ∂Measure.infinitePi fun _ : E => F := by
  set ν := Measure.infinitePi fun _ : E => F with hν
  set ν₀ := Measure.infinitePi fun _ : {e : E // b e = c₀} => F with hν₀
  have hπ : Measurable fun ω : E → ℝ≥0 => fiberEquiv b ω c₀ :=
    (measurable_pi_apply c₀).comp (fiberEquiv b).measurable
  have hU := measurable_fiberUpdate b c₀
  have hUω : ∀ ω, Measurable fun a : {e : E // b e = c₀} → ℝ≥0 => fiberUpdate b c₀ ω a :=
    fun ω => hU.comp (measurable_const.prodMk measurable_id)
  set G : (E → ℝ≥0) → ℝ≥0∞ := fun ω => ∫⁻ a', labelDensity ν₀ ℓ (fiberEquiv b ω c₀, a') *
    H (ω, fiberUpdate b c₀ ω a') ∂ν₀ with hGdef
  have hG : Measurable G := by
    refine Measurable.lintegral_prod_right' (f := fun q : (E → ℝ≥0) ×
      ({e : E // b e = c₀} → ℝ≥0) => labelDensity ν₀ ℓ (fiberEquiv b q.1 c₀, q.2) *
        H (q.1, fiberUpdate b c₀ q.1 q.2)) ?_
    exact ((measurable_labelDensity ν₀ hℓ).comp ((hπ.comp measurable_fst).prodMk
      measurable_snd)).mul (hH.comp (measurable_fst.prodMk hU))
  have hR : ∀ ω, ∫⁻ ω', H (ω, splice {e | b e = c₀} ω ω')
      ∂(ν[|(fun ω => ℓ (fiberEquiv b ω c₀)) ⁻¹' {ℓ (fiberEquiv b ω c₀)}]) = G ω := by
    intro ω
    have hS := hℓ.2 (fiberEquiv b ω c₀)
    have hHa : Measurable fun a' => H (ω, fiberUpdate b c₀ ω a') :=
      hH.comp (measurable_const.prodMk (hUω ω))
    have hset : (fun ω => ℓ (fiberEquiv b ω c₀)) ⁻¹' {ℓ (fiberEquiv b ω c₀)} =
        (fun ω => fiberEquiv b ω c₀) ⁻¹' (ℓ ⁻¹' {ℓ (fiberEquiv b ω c₀)}) := rfl
    simp_rw [splice_eq_fiberUpdate b c₀ ω]
    rw [hset]
    refine (lintegral_map hHa hπ).symm.trans ?_
    rw [← cond_map ν hπ hS, map_fiberEquiv_apply b F c₀,
      lintegral_cond_eq_lintegral_labelDensity ν₀ hS hHa]
  have hL : ∀ ω a, ∫⁻ a', H (fiberUpdate b c₀ ω a, fiberUpdate b c₀ ω a') ∂(ν₀[|ℓ ⁻¹' {ℓ a}]) =
      G (fiberUpdate b c₀ ω a) := by
    intro ω a
    rw [lintegral_cond_eq_lintegral_labelDensity ν₀ (hℓ.2 a)
      (f := fun a' => H (fiberUpdate b c₀ ω a, fiberUpdate b c₀ ω a'))
      (hH.comp (measurable_const.prodMk (hUω ω)))]
    simp only [hGdef, fiberEquiv_fiberUpdate, fiberUpdate_fiberUpdate]
  calc _ = ∫⁻ ω, ∫⁻ a, G (fiberUpdate b c₀ ω a) ∂ν₀ ∂ν := by
          refine lintegral_congr fun ω => ?_
          rw [lintegral_labelCoupling ν₀ hℓ
            (f := fun z => H (fiberUpdate b c₀ ω z.1, fiberUpdate b c₀ ω z.2))
            (hH.comp (((hUω ω).comp measurable_fst).prodMk
              ((hUω ω).comp measurable_snd)))]
          exact lintegral_congr fun a => hL ω a
    _ = ∫⁻ q, G (fiberUpdate b c₀ q.1 q.2) ∂ν.prod ν₀ :=
        (lintegral_prod _ (hG.comp hU).aemeasurable).symm
    _ = ∫⁻ ω, G ω ∂ν := (measurePreserving_fiberUpdate b F c₀).lintegral_comp hG
    _ = _ := lintegral_congr fun ω => (hR ω).symm

/-- **Resampling a fiber given its label under the pair law**: if the pair law of the fiber
`b⁻¹{c₀}` is the label coupling of `ℓ`, the pair (old weights, old weights with the fiber taken
from the new ones) has the law of `(ω, ω^{c₀,ω'})`, `ω'` drawn from the product law conditioned on
the label of the fiber being that of `ω`. -/
theorem lintegral_pairLaw_splice_labelCoupling
    (Q : ∀ c : ι, Measure (({e : E // b e = c} → ℝ≥0) × ({e : E // b e = c} → ℝ≥0)))
    [∀ c, IsProbabilityMeasure (Q c)] (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hfst : ∀ c, (Q c).map Prod.fst = Measure.infinitePi fun _ : {e : E // b e = c} => F)
    (c₀ : ι) {ℓ : ({e : E // b e = c₀} → ℝ≥0) → B} (hℓ : LabelOK ℓ)
    (hQ : Q c₀ = labelCoupling (Measure.infinitePi fun _ : {e : E // b e = c₀} => F) ℓ)
    {H : (E → ℝ≥0) × (E → ℝ≥0) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x, H (x.1, splice {e | b e = c₀} x.1 x.2) ∂pairLaw b Q =
      ∫⁻ ω, ∫⁻ ω', H (ω, splice {e | b e = c₀} ω ω')
        ∂((Measure.infinitePi fun _ : E => F)[|(fun ω => ℓ (fiberEquiv b ω c₀)) ⁻¹'
          {ℓ (fiberEquiv b ω c₀)}])
        ∂Measure.infinitePi fun _ : E => F := by
  rw [lintegral_pairLaw_splice b Q F hfst c₀ hH, hQ,
    lintegral_fiberUpdate_labelCoupling b F c₀ hℓ hH]

end LabelFiber

end CurvatureVariance.Paper.Gain.LabelResidual
