/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
Ported from Critical2DKPZ (https://github.com/scottnarmstrong/Critical2DKPZ) at f1c98da,
Critical2DKPZ/Gaussian/{ProductConditioning,ProductBlocks,CoordinateConditioning}.lean, and from
subdiffusive-process (https://github.com/nitromannitol/subdiffusive-process) at
4c6b8fa60357a07fd5713e5104a6cc70f8e432dc,
SubdiffusiveProcess/Probability/{ResamplingSum,ResampledLimit}.lean; modified.
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

/-!
# Coordinates of a product of probability spaces

For an arbitrary family of probability spaces `(X i, μ i)` and the product law
`Measure.infinitePi μ`:

* `coordinateSigma X S`: the σ-algebra of the coordinates in `S`; the restrictions to two
  disjoint blocks are independent (`indepFun_restrict_infinitePi`); an exhaustion generates the
  product σ-algebra (`iSup_coordinateSigma_eq_pi`);
* `resample T ω η`: the configuration reading `ω` on `T` and `η` off `T`. Splicing two
  independent samples gives a sample (`measurePreserving_resample`), the pair
  `(resample T ω η, resample T η ω)` is again a pair of independent samples
  (`measurePreserving_swap_outside`, exchangeability), and conditioning on the coordinates in `T`
  integrates out the others (`condExp_coordinateSigma_ae_eq`);
* one coordinate: replacing `xᵢ` by the `i`-th coordinate of an independent copy
  (`measurePreserving_update_pair`), or by an independent `y ∼ μ i`
  (`measurePreserving_update_infinitePi`), preserves the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace IsotropicVariance.Infra.EfronStein

/-- The square of an extended norm, as `ENNReal.ofReal` of the square. -/
theorem enorm_sq_eq_ofReal_sq (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg a), sq_abs]

/-! ### Conditional expectations under product decompositions -/

section ProductConditioning

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Conditioning on the first coordinate integrates out the second coordinate. -/
theorem condExp_prod_fst_integral {f : A × B → ℝ} (hf : Integrable f (μ.prod ν)) :
    (μ.prod ν)[f | (inferInstance : MeasurableSpace A).comap Prod.fst] =ᵐ[μ.prod ν]
      fun p => ∫ b, f (p.1, b) ∂ν := by
  have hm : (inferInstance : MeasurableSpace A).comap (Prod.fst : A × B → A) ≤
      (inferInstance : MeasurableSpace (A × B)) :=
    (measurable_fst : Measurable (Prod.fst : A × B → A)).comap_le
  let h : A → ℝ := fun a => ∫ b, f (a, b) ∂ν
  have hh : Integrable h μ := hf.integral_prod_left
  have hg : Integrable (fun p : A × B => h p.1) (μ.prod ν) := hh.comp_fst ν
  have hgm : AEStronglyMeasurable[(inferInstance : MeasurableSpace A).comap Prod.fst]
      (fun p : A × B => h p.1) (μ.prod ν) := by
    refine ⟨fun p => hh.aestronglyMeasurable.mk h p.1, ?_, ?_⟩
    · exact hh.aestronglyMeasurable.stronglyMeasurable_mk.comp_measurable
        (comap_measurable Prod.fst)
    · exact Measure.quasiMeasurePreserving_fst.ae_eq_comp hh.aestronglyMeasurable.ae_eq_mk
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
  · intro s hs hfin
    exact hg.integrableOn
  · intro s hs hfin
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hset : Prod.fst ⁻¹' t = t ×ˢ (Set.univ : Set B) := by ext p; simp
    rw [hset, setIntegral_prod _ hg.integrableOn, setIntegral_prod _ hf.integrableOn]
    simp [h]
  · exact hgm

/-- Conditional expectation is compatible with a measure-preserving relabeling. -/
theorem condExp_comp_measurableEquiv {X Y : Type*}
    {m : MeasurableSpace Y} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    {ξ : Measure X} {ζ : Measure Y} [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
    (e : X ≃ᵐ Y) (he : MeasurePreserving e ξ ζ)
    (hm : m ≤ mY)
    {f : Y → ℝ} (hf : Integrable f ζ) :
    ξ[f ∘ e | m.comap e] =ᵐ[ξ] (ζ[f | m]) ∘ e := by
  have hle : m.comap e ≤ mX := (MeasurableSpace.comap_mono hm).trans e.measurable.comap_le
  have hfc : Integrable (f ∘ e) ξ := he.integrable_comp_of_integrable hf
  have hgc : Integrable ((ζ[f | m]) ∘ e) ξ :=
    he.integrable_comp_of_integrable integrable_condExp
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle hfc
  · intro s hs hfin
    exact hgc.integrableOn
  · intro s hs hfin
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have het := he.restrict_preimage (hm t ht)
    change (∫ x in e ⁻¹' t, (ζ[f | m]) (e x) ∂ξ) =
      ∫ x in e ⁻¹' t, f (e x) ∂ξ
    rw [het.integral_comp' _, het.integral_comp' _]
    exact setIntegral_condExp hm hf ht
  · exact (stronglyMeasurable_condExp.comp_measurable
      (comap_measurable e)).aestronglyMeasurable

/-- Integrate the discarded coordinate after a measure-preserving product decomposition. -/
theorem condExp_equiv_fst_integral {X : Type*} [MeasurableSpace X]
    {ξ : Measure X} [IsProbabilityMeasure ξ]
    (e : X ≃ᵐ A × B) (he : MeasurePreserving e ξ (μ.prod ν))
    {f : X → ℝ} (hf : Integrable f ξ) :
    ξ[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)] =ᵐ[ξ]
      fun x => ∫ b, f (e.symm ((e x).1, b)) ∂ν := by
  have hfi : Integrable (f ∘ e.symm) (μ.prod ν) :=
    (he.symm e).integrable_comp_of_integrable hf
  have hce := condExp_comp_measurableEquiv e he
    (measurable_fst : Measurable (Prod.fst : A × B → A)).comap_le hfi
  have hav := he.quasiMeasurePreserving.ae_eq_comp (condExp_prod_fst_integral hfi)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e.symm_apply_apply] using
    hce.trans hav

/-- Exchanging the first components of two independent pairs preserves the law of the pairs. -/
theorem measurePreserving_swap_first
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (fun x : (A × B) × (A × B) => ((x.2.1, x.1.2), (x.1.1, x.2.2)))
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod ν).prod (μ.prod ν)) := by
  have f1 := measurePreserving_prodAssoc μ ν (μ.prod ν)
  have f2 : MeasurePreserving (Prod.map id Prod.swap)
      (μ.prod (ν.prod (μ.prod ν))) (μ.prod ((μ.prod ν).prod ν)) :=
    (MeasurePreserving.id μ).prod Measure.measurePreserving_swap
  have f3 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc)
      (μ.prod ((μ.prod ν).prod ν)) (μ.prod (μ.prod (ν.prod ν))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν)
  have f4 := (measurePreserving_prodAssoc μ μ (ν.prod ν)).symm
  have f5 : MeasurePreserving (Prod.map Prod.swap Prod.swap)
      ((μ.prod μ).prod (ν.prod ν)) ((μ.prod μ).prod (ν.prod ν)) :=
    Measure.measurePreserving_swap.prod Measure.measurePreserving_swap
  have g1 := measurePreserving_prodAssoc μ μ (ν.prod ν)
  have g2 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc.symm)
      (μ.prod (μ.prod (ν.prod ν))) (μ.prod ((μ.prod ν).prod ν)) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν).symm
  have g3 : MeasurePreserving (Prod.map id (Prod.map Prod.swap id))
      (μ.prod ((μ.prod ν).prod ν)) (μ.prod ((ν.prod μ).prod ν)) :=
    (MeasurePreserving.id μ).prod
      (Measure.measurePreserving_swap.prod (MeasurePreserving.id ν))
  have g4 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc)
      (μ.prod ((ν.prod μ).prod ν)) (μ.prod (ν.prod (μ.prod ν))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν μ ν)
  have g5 := (measurePreserving_prodAssoc μ ν (μ.prod ν)).symm
  have h := g5.comp (g4.comp (g3.comp (g2.comp (g1.comp
    (f5.comp (f4.comp (f3.comp (f2.comp f1))))))))
  convert h using 1
  funext x
  rfl

end ProductConditioning

/-! ### Blocks of coordinates -/

section Blocks

variable {I : Type*} {X : I → Type*} [mX : ∀ i, MeasurableSpace (X i)]
    (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- The σ-algebra of a restriction is generated by its coordinate evaluations. -/
theorem comap_restrict_eq_iSup (S : Set I) :
    (inferInstance : MeasurableSpace ((i : S) → X i)).comap S.domRestrict =
      ⨆ i ∈ S, (mX i).comap (fun x : (i : I) → X i => x i) := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, iSup_subtype]
  rfl

/-- Restrictions to disjoint sets of coordinates are independent. -/
theorem indepFun_restrict_infinitePi (S T : Set I) (hST : Disjoint S T) :
    IndepFun S.domRestrict T.domRestrict (Measure.infinitePi μ) := by
  rw [IndepFun_iff_Indep, comap_restrict_eq_iSup, comap_restrict_eq_iSup]
  have hi : iIndepFun (fun i (x : (i : I) → X i) => x i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  exact indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le)
    hi.iIndep hST

/-- Splitting the index set along a predicate and its complement preserves the product law. -/
theorem measurePreserving_infinitePi_split (p : I → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd X p) (Measure.infinitePi μ)
      ((Measure.infinitePi fun i : Subtype p => μ i).prod
        (Measure.infinitePi fun i : {i // ¬p i} => μ i)) := by
  refine ⟨(MeasurableEquiv.piEquivPiSubtypeProd X p).measurable, ?_⟩
  have hi := indepFun_restrict_infinitePi μ {i | p i} {i | ¬p i}
    (disjoint_compl_right)
  have hm := (indepFun_iff_map_prod_eq_prod_map_map
    (show AEMeasurable ({i | p i} : Set I).domRestrict (Measure.infinitePi μ) from
      (measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)).aemeasurable)
    (show AEMeasurable ({i | ¬p i} : Set I).domRestrict (Measure.infinitePi μ) from
      (measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)).aemeasurable)).mp hi
  simpa only [Set.domRestrict, Measure.infinitePi_map_restrict'] using! hm

end Blocks

/-! ### Coordinate σ-algebras -/

section Sigma

variable {I : Type*} (X : I → Type*) [∀ i, MeasurableSpace (X i)]

/-- The σ-algebra generated by the coordinates indexed by `S`. -/
@[instance_reducible]
def coordinateSigma (S : Set I) : MeasurableSpace ((i : I) → X i) :=
  MeasurableSpace.comap (fun (ω : (i : I) → X i) (j : S) => ω j) MeasurableSpace.pi

/-- The coordinate σ-algebra is contained in the product σ-algebra. -/
theorem coordinateSigma_le (S : Set I) : coordinateSigma X S ≤ MeasurableSpace.pi :=
  Measurable.comap_le (f := fun (ω : (i : I) → X i) (j : S) => ω j)
    (measurable_pi_iff.mpr fun j => measurable_pi_apply (j : I))

/-- The coordinate σ-algebra is the supremum of the σ-algebras of its coordinates. -/
theorem coordinateSigma_eq_iSup (S : Set I) :
    coordinateSigma X S = ⨆ i ∈ S, (inferInstance : MeasurableSpace (X i)).comap
      (fun x : (i : I) → X i => x i) :=
  comap_restrict_eq_iSup (X := X) S

/-- The coordinate σ-algebra is monotone in the index set. -/
theorem coordinateSigma_mono {S T : Set I} (h : S ⊆ T) :
    coordinateSigma X S ≤ coordinateSigma X T := by
  rw [coordinateSigma_eq_iSup, coordinateSigma_eq_iSup]
  exact iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ T) =>
    (inferInstance : MeasurableSpace (X i)).comap (fun x : (i : I) → X i => x i)) i (h hi)

/-- An exhausting sequence of coordinate sets generates the product σ-algebra. -/
theorem iSup_coordinateSigma_eq_pi (S : ℕ → Set I) (hS : ∀ i, ∃ n, i ∈ S n) :
    ⨆ n, coordinateSigma X (S n) = (MeasurableSpace.pi : MeasurableSpace ((i : I) → X i)) := by
  refine le_antisymm (iSup_le fun n => coordinateSigma_le X (S n)) ?_
  refine iSup_le fun i => ?_
  obtain ⟨n, hn⟩ := hS i
  refine le_trans ?_ (le_iSup (fun n => coordinateSigma X (S n)) n)
  rw [coordinateSigma_eq_iSup]
  exact le_iSup₂ (f := fun i (_ : i ∈ S n) =>
    (inferInstance : MeasurableSpace (X i)).comap (fun x : (i : I) → X i => x i)) i hn

/-- The filtration generated by an increasing sequence of coordinate sets. -/
def coordinateFiltration (S : ℕ → Set I) (hS : Monotone S) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace ((i : I) → X i)) where
  seq n := coordinateSigma X (S n)
  mono' _ _ hmn := coordinateSigma_mono X (hS hmn)
  le' n := coordinateSigma_le X (S n)

end Sigma

/-! ### Resampling a block of coordinates -/

section Resample

variable {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

omit [∀ i, MeasurableSpace (X i)] in
open Classical in
/-- Keep the coordinates in `T` from `ω` and take all other coordinates from `η`. -/
def resample (T : Set I) (ω η : (i : I) → X i) : (i : I) → X i :=
  fun i => if i ∈ T then ω i else η i

omit [∀ i, MeasurableSpace (X i)] in
theorem resample_apply_of_mem {T : Set I} {ω η : (i : I) → X i} {i : I} (hi : i ∈ T) :
    resample T ω η i = ω i := by
  classical
  simp [resample, hi]

omit [∀ i, MeasurableSpace (X i)] in
theorem resample_apply_of_notMem {T : Set I} {ω η : (i : I) → X i} {i : I} (hi : i ∉ T) :
    resample T ω η i = η i := by
  classical
  simp [resample, hi]

omit [∀ i, MeasurableSpace (X i)] in
/-- Resampling only reads `ω` on `T`. -/
theorem resample_congr_left {T : Set I} {ω ω' : (i : I) → X i} (h : ∀ i ∈ T, ω i = ω' i)
    (η : (i : I) → X i) : resample T ω η = resample T ω' η := by
  funext i
  by_cases hi : i ∈ T
  · rw [resample_apply_of_mem hi, resample_apply_of_mem hi, h i hi]
  · rw [resample_apply_of_notMem hi, resample_apply_of_notMem hi]

omit [∀ i, MeasurableSpace (X i)] in
/-- Replacing one coordinate is resampling outside the complement of that coordinate. -/
theorem update_eq_resample [DecidableEq I] (j : I) (ω η : (i : I) → X i) :
    Function.update ω j (η j) = resample {j}ᶜ ω η := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [resample_apply_of_notMem]
  · rw [Function.update_of_ne hij, resample_apply_of_mem (by simpa using hij)]

omit [∀ i, MeasurableSpace (X i)] in
/-- Resampling a coordinate of `T` commutes with splicing along `T`. -/
theorem resample_update_of_mem [DecidableEq I] {T : Set I} {j : I} (hj : j ∈ T)
    (ω η : (i : I) → X i) (y : X j) :
    resample T (Function.update ω j y) η = Function.update (resample T ω η) j y := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [resample_apply_of_mem hj]
  · by_cases hi : i ∈ T
    · rw [resample_apply_of_mem hi, Function.update_of_ne hij, Function.update_of_ne hij,
        resample_apply_of_mem hi]
    · rw [resample_apply_of_notMem hi, Function.update_of_ne hij, resample_apply_of_notMem hi]

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- The resampled configuration depends measurably on the pair of samples. -/
theorem measurable_resample (T : Set I) :
    Measurable (fun z : ((i : I) → X i) × ((i : I) → X i) => resample T z.1 z.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases hi : i ∈ T
  · simp only [resample_apply_of_mem hi]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [resample_apply_of_notMem hi]
    exact (measurable_pi_apply i).comp measurable_snd

/-- **Splicing preserves the law**: reading `T` from one sample and the rest from an independent
sample gives a sample. -/
theorem measurePreserving_resample (T : Set I) :
    MeasurePreserving (fun z : ((i : I) → X i) × ((i : I) → X i) => resample T z.1 z.2)
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) (Measure.infinitePi μ) := by
  classical
  refine ⟨measurable_resample T, ?_⟩
  refine Measure.eq_infinitePi μ fun s t ht => ?_
  have hpre : (fun z : ((i : I) → X i) × ((i : I) → X i) => resample T z.1 z.2) ⁻¹'
      Set.pi (↑s) t =
      (Set.pi (↑(s.filter (· ∈ T))) t) ×ˢ (Set.pi (↑(s.filter (fun i => i ∉ T))) t) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_filter,
      Set.mem_ofPred_eq, Finset.mem_coe]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have := h i hi.1
        rwa [resample_apply_of_mem hi.2] at this
      · have := h i hi.1
        rwa [resample_apply_of_notMem hi.2] at this
    · rintro ⟨h1, h2⟩ i hi
      by_cases hT : i ∈ T
      · rw [resample_apply_of_mem hT]; exact h1 i ⟨hi, hT⟩
      · rw [resample_apply_of_notMem hT]; exact h2 i ⟨hi, hT⟩
  rw [Measure.map_apply (measurable_resample T)
      (MeasurableSet.pi (Set.to_countable _) (fun i _ => ht i)), hpre,
    Measure.prod_prod, Measure.infinitePi_pi μ (fun i _ => ht i),
    Measure.infinitePi_pi μ (fun i _ => ht i),
    Finset.prod_filter_mul_prod_filter_not s (· ∈ T)]

/-- **Exchangeability of a block**: `(ω, η) ↦ (resample T ω η, resample T η ω)` preserves the law
of a pair of independent samples. -/
theorem measurePreserving_swap_outside (T : Set I) :
    MeasurePreserving (fun z : ((i : I) → X i) × ((i : I) → X i) =>
        (resample T z.1 z.2, resample T z.2 z.1))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd X (fun i => i ∈ T)
  let νS := Measure.infinitePi (fun i : T => μ i)
  let νC := Measure.infinitePi (fun i : {i // i ∉ T} => μ i)
  have hsplit : MeasurePreserving e (Measure.infinitePi μ) (νS.prod νC) :=
    measurePreserving_infinitePi_split μ (fun i => i ∈ T)
  have h := (Measure.measurePreserving_swap).comp
    (((MeasurePreserving.symm e hsplit).prod (MeasurePreserving.symm e hsplit)).comp
    ((measurePreserving_swap_first νS νC).comp (hsplit.prod hsplit)))
  convert h using 1
  funext z
  apply Prod.ext
  · funext i
    change (if i ∈ T then z.1 i else z.2 i) =
      (if _h : i ∈ T then z.1 i else z.2 i)
    split_ifs <;> rfl
  · funext i
    change (if i ∈ T then z.2 i else z.1 i) =
      (if _h : i ∈ T then z.2 i else z.1 i)
    split_ifs <;> rfl

/-- **Conditioning on the coordinates in `T` integrates out the others.** -/
theorem condExp_coordinateSigma_ae_eq (T : Set I) {F : ((i : I) → X i) → ℝ}
    (hFm : Measurable F) (hF : Integrable F (Measure.infinitePi μ)) :
    (Measure.infinitePi μ)[F | coordinateSigma X T] =ᵐ[Measure.infinitePi μ]
      fun ω => ∫ η, F (resample T ω η) ∂Measure.infinitePi μ := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd X (fun i => i ∈ T)
  have hsplit := measurePreserving_infinitePi_split μ (fun i => i ∈ T)
  have h1 := condExp_equiv_fst_integral e hsplit hF
  refine h1.trans (Filter.Eventually.of_forall fun ω => ?_)
  have h2 : MeasurePreserving (fun η => (e η).2) (Measure.infinitePi μ) _ :=
    measurePreserving_snd.comp hsplit
  have hm : Measurable (fun b => F (e.symm ((e ω).1, b))) :=
    hFm.comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
  dsimp only
  rw [← h2.map_eq, integral_map h2.measurable.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  rfl

end Resample

/-! ### Resampling one coordinate -/

section Update

variable {I : Type*} [DecidableEq I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Replacing one coordinate by that of an independent copy preserves the product law. -/
theorem measurePreserving_update_pair (j : I) :
    MeasurePreserving (fun q : ((i : I) → X i) × ((i : I) → X i) =>
        Function.update q.1 j (q.2 j))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) (Measure.infinitePi μ) := by
  have h := measurePreserving_resample μ ({j}ᶜ : Set I)
  convert h using 2 with q
  exact update_eq_resample j q.1 q.2

/-- **Resampling one coordinate preserves the law**: `(x, y) ↦ x[i ↦ y]` maps
`infinitePi μ ⊗ μ i` to `infinitePi μ`. -/
theorem measurePreserving_update_infinitePi (i : I) :
    MeasurePreserving (fun q : ((j : I) → X j) × X i => Function.update q.1 i q.2)
      ((Measure.infinitePi μ).prod (μ i)) (Measure.infinitePi μ) := by
  have hg : MeasurePreserving (fun p : ((j : I) → X j) × ((j : I) → X j) => (p.1, p.2 i))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      ((Measure.infinitePi μ).prod (μ i)) :=
    (MeasurePreserving.id _).prod (measurePreserving_eval_infinitePi μ i)
  refine ⟨measurable_update', ?_⟩
  rw [← hg.map_eq, Measure.map_map measurable_update' hg.measurable]
  exact (measurePreserving_update_pair μ i).map_eq

end Update

end IsotropicVariance.Infra.EfronStein
