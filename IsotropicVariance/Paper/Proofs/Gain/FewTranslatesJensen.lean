/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.FewTranslates
public import IsotropicVariance.Paper.Proofs.Gain.BridgeInfo
public import IsotropicVariance.Paper.Proofs.Resampling.Law
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Lemma `lem:fewtranslates`: `f − E_G[f]` as a conditional expectation of the change

The proof of Lemma `lem:fewtranslates` starts from the resampling `ω^G`
of `G` with `σ_G` constant, and the identity
`f − E_G[f] = ⌈K^{2/3}⌉⁻¹ Σ_m E[F_m − F_m^G | (X_H)_H]`, the conditional expectation being taken on
the joint law of the noise and of its resampling, given the labels of the old noise. The
expectation `E_G` is `X.P[· | Λ.otherSigma K o i z]`
(`Proofs.Gain.condExp_otherSigma_eq_sum_label`).

* `condExp_old_sub_new_ae_eq`: the identity for two random elements `old`, `new` of the law `P`, for
  σ-algebras `O`, `g`, independent, such that old and new agree on the events of `O`, and such that
  the events of `g` of `old` are independent of `new`. The conditional expectation of `Z(old)` is
  that of `Z` moved by `old`. For the term of `Z(new)`, the test sets `B ∩ C`, `B` in `O`, `C` in
  `g`, give both sides the value `P(C) ∫_B Z`, and they form a π-system (`setIntegral_sup_eq_zero`).
* `Setting.indep_new_old_bot`: with `σ_G = ⊥`, the old noise in `G` is independent of the new noise.
* `Setting.LabelFamily.otherSigma_le_aeClosure`: the labels of the other blocks are, up to null
  sets, information off `G`. Two blocks of adjacent slabs share a face, a null set.
* `condExp_sub_resampled_ae_eq`: **the first display of the proof of Lemma `lem:fewtranslates`**,
  for a function `Z` of the noise.
* `eLpNorm_sub_condExp_le`: Jensen's inequality for conditional expectation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper

namespace Proofs.Gain

/-! ### Conditional expectations of the old and the new variable -/

section Generic

variable {Ω Ω' : Type*} {m₁ m₂ A O g mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} {old new : Ω' → Ω}

/-- The integral of a function over a set of an independent σ-algebra. -/
theorem setIntegral_of_indep [IsProbabilityMeasure P] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    (hind : Indep m₁ m₂ P) {f : Ω → ℝ} (hf : StronglyMeasurable[m₁] f)
    (hfi : Integrable f P) {C : Set Ω} (hC : MeasurableSet[m₂] C) :
    ∫ ω in C, f ω ∂P = P.real C * ∫ ω, f ω ∂P := by
  have h := condExp_indep_eq h₁ h₂ hf hind
  rw [← setIntegral_condExp h₂ hfi hC, setIntegral_congr_ae (h₂ _ hC) (h.mono fun _ h _ => h),
    setIntegral_const, smul_eq_mul]

/-- A function with zero integral over the sets `B ∩ C` has zero integral over the sets of the
σ-algebra that they generate. -/
theorem setIntegral_sup_eq_zero [IsProbabilityMeasure P] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) {ψ : Ω → ℝ}
    (hψ : Integrable ψ P)
    (h : ∀ B C, MeasurableSet[m₁] B → MeasurableSet[m₂] C → ∫ ω in B ∩ C, ψ ω ∂P = 0) {S : Set Ω}
    (hS : MeasurableSet[m₁ ⊔ m₂] S) : ∫ ω in S, ψ ω ∂P = 0 := by
  let p : Set (Set Ω) := {s | ∃ u v, MeasurableSet[m₁] u ∧ MeasurableSet[m₂] v ∧ s = u ∩ v}
  have hp : IsPiSystem p := by
    rintro _ ⟨u, v, hu, hv, rfl⟩ _ ⟨u', v', hu', hv', rfl⟩ _
    refine ⟨u ∩ u', v ∩ v', hu.inter hu', hv.inter hv', ?_⟩
    ext x; simp only [mem_inter_iff]; tauto
  have hgen : m₁ ⊔ m₂ = MeasurableSpace.generateFrom p := by
    apply le_antisymm
    · refine sup_le (fun s hs => ?_) (fun s hs => ?_)
      · exact MeasurableSpace.measurableSet_generateFrom ⟨s, univ, hs, MeasurableSet.univ, by simp⟩
      · exact MeasurableSpace.measurableSet_generateFrom ⟨univ, s, MeasurableSet.univ, hs, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨u, v, hu, hv, rfl⟩
      exact (le_sup_left (a := m₁) (b := m₂) _ hu).inter (le_sup_right (a := m₁) (b := m₂) _ hv)
  have hle := sup_le h₁ h₂
  have huniv : ∫ ω, ψ ω ∂P = 0 := by
    simpa using h univ univ MeasurableSet.univ MeasurableSet.univ
  induction S, hS using MeasurableSpace.induction_on_inter hgen hp with
  | empty => simp
  | basic t ht =>
    obtain ⟨u, v, hu, hv, rfl⟩ := ht
    exact h u v hu hv
  | compl t htm ih => rw [setIntegral_compl (hle _ htm) hψ, ih, sub_zero, huniv]
  | iUnion f hd hfm ih =>
    rw [integral_iUnion (fun i => hle _ (hfm i)) hd hψ.integrableOn]
    simp [ih]

/-- The set integral of a function moved by a measure-preserving map. -/
theorem setIntegral_comp_measurePreserving (hold : MeasurePreserving old P' P) {S : Set Ω}
    (hS : MeasurableSet S) {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) :
    ∫ ω in old ⁻¹' S, Y (old ω) ∂P' = ∫ ω in S, Y ω ∂P := by
  have hY' : AEStronglyMeasurable Y (P'.map old) := by rwa [hold.map_eq]
  have h := setIntegral_map hS hY' hold.aemeasurable
  rw [hold.map_eq] at h
  exact h.symm

/-- The integral of a function moved by a measure-preserving map. -/
theorem integral_comp_measurePreserving (hold : MeasurePreserving old P' P) {Y : Ω → ℝ}
    (hY : AEStronglyMeasurable Y P) : ∫ ω, Y (old ω) ∂P' = ∫ ω, Y ω ∂P := by
  simpa using setIntegral_comp_measurePreserving hold MeasurableSet.univ hY

variable [IsProbabilityMeasure P] [IsProbabilityMeasure P']

omit [IsProbabilityMeasure P] in
/-- A conditional expectation given information moved by `old`, by test sets. -/
theorem condExp_comap_ae_eq_of_setIntegral (hold : MeasurePreserving old P' P) (hA : A ≤ mΩ)
    {D : Ω' → ℝ} (hD : Integrable D P') {Y : Ω → ℝ}
    (hY : StronglyMeasurable[A] Y) (hYi : Integrable Y P)
    (H : ∀ S, MeasurableSet[A] S → ∫ ω in old ⁻¹' S, D ω ∂P' = ∫ ω in S, Y ω ∂P) :
    P'[D | A.comap old] =ᵐ[P'] fun ω => Y (old ω) := by
  have hm : A.comap old ≤ mΩ' := (MeasurableSpace.comap_mono hA).trans hold.measurable.comap_le
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hD
    (fun _ _ _ => (hold.integrable_comp_of_integrable hYi).integrableOn) ?_ ?_).symm
  · rintro _ ⟨S, hS, rfl⟩ -
    change ∫ ω in old ⁻¹' S, Y (old ω) ∂P' = _
    rw [H S hS, setIntegral_comp_measurePreserving hold (hA _ hS) hYi.aestronglyMeasurable]
  · exact (hY.comp_measurable (comap_measurable old)).aestronglyMeasurable

/-- The conditional expectation of `Z(old)` given information about `old`. -/
theorem condExp_old_ae_eq (hold : MeasurePreserving old P' P) (hA : A ≤ mΩ) {Z : Ω → ℝ}
    (hZ : Integrable Z P) :
    P'[fun ω => Z (old ω) | A.comap old] =ᵐ[P'] fun ω => (P[Z | A]) (old ω) :=
  condExp_comap_ae_eq_of_setIntegral (D := fun ω => Z (old ω)) hold hA
    (hold.integrable_comp_of_integrable hZ) stronglyMeasurable_condExp integrable_condExp
    fun S hS => by
      rw [setIntegral_comp_measurePreserving hold (hA _ hS) hZ.aestronglyMeasurable,
        setIntegral_condExp hA hZ hS]

omit [IsProbabilityMeasure P] in
/-- The value `P(C) ∫_B Z` of the integral of `Z(new)` over `{old ∈ B ∩ C}`. -/
theorem setIntegral_new_inter (hold : MeasurePreserving old P' P)
    (hnew : MeasurePreserving new P' P) (hO : O ≤ mΩ) (hg : g ≤ mΩ)
    (hagree : ∀ B, MeasurableSet[O] B → ∀ᵐ ω ∂P', (old ω ∈ B ↔ new ω ∈ B))
    (hind : Indep (mΩ.comap new) (g.comap old) P') {Z : Ω → ℝ} (hZm : StronglyMeasurable Z)
    (hZ : Integrable Z P) {B C : Set Ω} (hB : MeasurableSet[O] B) (hC : MeasurableSet[g] C) :
    ∫ ω in old ⁻¹' B ∩ old ⁻¹' C, Z (new ω) ∂P' = P.real C * ∫ ω in B, Z ω ∂P := by
  have hB' := hO _ hB
  have hC' := hg _ hC
  have hset : (old ⁻¹' B ∩ old ⁻¹' C : Set Ω') =ᵐ[P'] old ⁻¹' C ∩ new ⁻¹' B := by
    filter_upwards [hagree B hB] with ω hω
    apply propext
    change (old ω ∈ B ∧ old ω ∈ C) ↔ (old ω ∈ C ∧ new ω ∈ B)
    rw [hω, and_comm]
  have hind' := setIntegral_of_indep (f := fun ω => B.indicator Z (new ω))
    ((MeasurableSpace.comap_mono le_rfl).trans hnew.measurable.comap_le)
    ((MeasurableSpace.comap_mono hg).trans hold.measurable.comap_le) hind
    ((hZm.indicator hB').comp_measurable (comap_measurable new))
    (hnew.integrable_comp_of_integrable (hZ.indicator hB')) (C := old ⁻¹' C) ⟨C, hC, rfl⟩
  have e : (fun ω => B.indicator Z (new ω)) = (new ⁻¹' B).indicator fun ω => Z (new ω) := by
    funext ω
    by_cases h : new ω ∈ B
    · rw [indicator_of_mem h, indicator_of_mem (show ω ∈ new ⁻¹' B from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show ω ∉ new ⁻¹' B from h)]
  rw [setIntegral_congr_set hset, ← setIntegral_indicator (hB'.preimage hnew.measurable), ← e,
    hind', integral_comp_measurePreserving hnew (hZ.indicator hB').aestronglyMeasurable,
    integral_indicator hB']
  congr 1
  rw [measureReal_def, measureReal_def, hold.measure_preimage hC'.nullMeasurableSet]

/-- The value `P(C) ∫_B Z` of the integral of `P[Z | O]` over `B ∩ C`. -/
theorem setIntegral_condExp_inter (hO : O ≤ mΩ) (hg : g ≤ mΩ) (hOg : Indep O g P) {Z : Ω → ℝ}
    (hZ : Integrable Z P) {B C : Set Ω} (hB : MeasurableSet[O] B) (hC : MeasurableSet[g] C) :
    ∫ ω in B ∩ C, (P[Z | O]) ω ∂P = P.real C * ∫ ω in B, Z ω ∂P := by
  have hB' := hO _ hB
  have hYm : StronglyMeasurable[O] (B.indicator (P[Z | O])) :=
    stronglyMeasurable_condExp.indicator hB
  have h := setIntegral_of_indep hO hg hOg hYm (integrable_condExp.indicator hB') hC
  rw [setIntegral_indicator hB', inter_comm] at h
  rw [h, integral_indicator hB', setIntegral_condExp hO hZ hB]

/-- The conditional expectation of `Z(new)`, for `Z` strongly measurable. -/
theorem condExp_new_ae_eq_of_stronglyMeasurable (hold : MeasurePreserving old P' P)
    (hnew : MeasurePreserving new P' P) (hO : O ≤ mΩ) (hg : g ≤ mΩ) (hOg : Indep O g P)
    (hagree : ∀ B, MeasurableSet[O] B → ∀ᵐ ω ∂P', (old ω ∈ B ↔ new ω ∈ B))
    (hind : Indep (mΩ.comap new) (g.comap old) P') {Z : Ω → ℝ} (hZm : StronglyMeasurable Z)
    (hZ : Integrable Z P) :
    P'[fun ω => Z (new ω) | (O ⊔ g).comap old] =ᵐ[P'] fun ω => (P[Z | O]) (old ω) := by
  have hYi : Integrable (P[Z | O]) P := integrable_condExp
  have hA := sup_le hO hg
  refine condExp_comap_ae_eq_of_setIntegral (D := fun ω => Z (new ω)) hold hA
    (hnew.integrable_comp_of_integrable hZ) (stronglyMeasurable_condExp.mono le_sup_left) hYi
    fun S hS => ?_
  have hZn : Integrable (fun ω => Z (new ω)) P' := hnew.integrable_comp_of_integrable hZ
  have hYo : Integrable (fun ω => (P[Z | O]) (old ω)) P' := hold.integrable_comp_of_integrable hYi
  have hψ : Integrable (fun ω => Z (new ω) - (P[Z | O]) (old ω)) P' := hZn.sub hYo
  have hS' : MeasurableSet[O.comap old ⊔ g.comap old] (old ⁻¹' S) := by
    rw [← MeasurableSpace.comap_sup]
    exact ⟨S, hS, rfl⟩
  have key := setIntegral_sup_eq_zero (P := P')
    ((MeasurableSpace.comap_mono hO).trans hold.measurable.comap_le)
    ((MeasurableSpace.comap_mono hg).trans hold.measurable.comap_le) hψ ?_ hS'
  · rw [integral_sub hZn.integrableOn hYo.integrableOn, sub_eq_zero,
      setIntegral_comp_measurePreserving hold (hA _ hS) hYi.aestronglyMeasurable] at key
    exact key
  · rintro _ _ ⟨B, hB, rfl⟩ ⟨C, hC, rfl⟩
    rw [integral_sub hZn.integrableOn hYo.integrableOn, sub_eq_zero,
      setIntegral_new_inter hold hnew hO hg hagree hind hZm hZ hB hC, ← preimage_inter,
      setIntegral_comp_measurePreserving hold ((hO _ hB).inter (hg _ hC)) hYi.aestronglyMeasurable,
      setIntegral_condExp_inter hO hg hOg hZ hB hC]

/-- The conditional expectation of `Z(new)`, given the information `O ⊔ g` of `old`, is
`P[Z | O]` at `old`. -/
theorem condExp_new_ae_eq (hold : MeasurePreserving old P' P) (hnew : MeasurePreserving new P' P)
    (hO : O ≤ mΩ) (hg : g ≤ mΩ) (hOg : Indep O g P)
    (hagree : ∀ B, MeasurableSet[O] B → ∀ᵐ ω ∂P', (old ω ∈ B ↔ new ω ∈ B))
    (hind : Indep (mΩ.comap new) (g.comap old) P') {Z : Ω → ℝ} (hZ : Integrable Z P) :
    P'[fun ω => Z (new ω) | (O ⊔ g).comap old] =ᵐ[P'] fun ω => (P[Z | O]) (old ω) := by
  have hZ' := hZ.1.ae_eq_mk
  have hZi : Integrable (hZ.1.mk Z) P := hZ.congr hZ'
  have h₁ : (fun ω => Z (new ω)) =ᵐ[P'] fun ω => hZ.1.mk Z (new ω) :=
    hnew.quasiMeasurePreserving.ae_eq_comp hZ'
  have h₂ : (fun ω => (P[Z | O]) (old ω)) =ᵐ[P'] fun ω => (P[hZ.1.mk Z | O]) (old ω) :=
    hold.quasiMeasurePreserving.ae_eq_comp (condExp_congr_ae hZ')
  exact (condExp_congr_ae h₁).trans ((condExp_new_ae_eq_of_stronglyMeasurable hold hnew hO hg hOg
    hagree hind hZ.1.stronglyMeasurable_mk hZi).trans h₂.symm)

/-- **The first display of the proof of Lemma `lem:fewtranslates`, generically**: the conditional
expectation of the change `Z(old) − Z(new)`, given the information `O ⊔ g` of `old`, is
`P[Z | O ⊔ g] − P[Z | O]` at `old`. -/
theorem condExp_old_sub_new_ae_eq (hold : MeasurePreserving old P' P)
    (hnew : MeasurePreserving new P' P) (hO : O ≤ mΩ) (hg : g ≤ mΩ) (hOg : Indep O g P)
    (hagree : ∀ B, MeasurableSet[O] B → ∀ᵐ ω ∂P', (old ω ∈ B ↔ new ω ∈ B))
    (hind : Indep (mΩ.comap new) (g.comap old) P') {Z : Ω → ℝ} (hZ : Integrable Z P) :
    P'[fun ω => Z (old ω) - Z (new ω) | (O ⊔ g).comap old] =ᵐ[P']
      fun ω => (P[Z | O ⊔ g] - P[Z | O]) (old ω) := by
  have hsub := condExp_sub (hold.integrable_comp_of_integrable hZ)
    (hnew.integrable_comp_of_integrable hZ) ((O ⊔ g).comap old)
  have h₁ := condExp_old_ae_eq hold (sup_le hO hg) hZ
  have h₂ := condExp_new_ae_eq hold hnew hO hg hOg hagree hind hZ
  filter_upwards [hsub, h₁, h₂] with ω e e₁ e₂
  have e' : (P'[(fun ω => Z (old ω)) - fun ω => Z (new ω) | (O ⊔ g).comap old]) ω =
      (P'[fun ω => Z (old ω) | (O ⊔ g).comap old]) ω -
        (P'[fun ω => Z (new ω) | (O ⊔ g).comap old]) ω := e
  change (P'[(fun ω => Z (old ω)) - fun ω => Z (new ω) | (O ⊔ g).comap old]) ω = _
  rw [e', e₁, e₂]
  rfl

end Generic

end Proofs.Gain

/-! ### The resampling with `σ_G` constant -/

namespace Setting

variable {m : ℕ} (X : Setting.{u} m)

/-- The choice `σ_G` constant of the proof of Lemma `lem:fewtranslates`. -/
def botInfo (n W : ℝ) (L : ℕ) : X.BlockInfo n W L :=
  ⟨fun _ => ⊥, fun _ => bot_le⟩

/-- The joint law of the noise and of its resamplings with `σ_G` constant. -/
noncomputable abbrev botResampling (n W : ℝ) (L : ℕ) :
    letI := X.measurableSpace; Measure (X.Ω × (BlockIdx m → X.Ω)) :=
  X.blockResampling n W L (X.botInfo n W L).1

open Proofs.Gain.Bridge Proofs.Resampling in
/-- With `σ_G` constant, the old noise in `G` is independent of the new noise of `G`: `ω^G|_G` is an
independent copy of `ω|_G`. -/
theorem indep_new_old_bot (n W : ℝ) (L : ℕ) (c : BlockIdx m) :
    Indep (X.measurableSpace.comap fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 c)
      ((X.info (block n W L c.1 c.2)).comap Prod.fst) (X.botResampling n W L) := by
  set G := block n W L c.1 c.2 with hGdef
  have hG : MeasurableSet G := measurableSet_block n W L _ _
  have hGfr : volume (frontier G) = 0 := volume_frontier_block n W L _ _
  have hle : X.info Gᶜ ⊔ ⊥ ≤ X.measurableSpace := sup_le (X.info_le _) bot_le
  have hindep : Indep (X.info G) (X.info Gᶜ ⊔ ⊥) X.P := by
    rw [sup_bot_eq]
    exact indep_info_compl _ hG hGfr
  have hold : MeasurePreserving Prod.fst (X.botResampling n W L) X.P :=
    X.measurePreserving_old _ _
  have hnew : MeasurePreserving (fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 c)
      (X.botResampling n W L) X.P :=
    X.measurePreserving_new (σ := (X.botInfo n W L).1) bot_le
  rw [Indep_iff]
  rintro _ _ ⟨D, hD, rfl⟩ ⟨C, hC, rfl⟩
  have hC' := X.info_le _ C hC
  have h₁ : X.botResampling n W L ((fun p => p.2 c) ⁻¹' D ∩ Prod.fst ⁻¹' C) =
      ∫⁻ ω in C, X.resampleKernel G ⊥ ω D ∂X.P := by
    have h := X.resamplingLaw_old_new_pi (fun p : BlockIdx m => block n W L p.1 p.2)
      (X.botInfo n W L).1 {c} hC' (A := fun _ => D) fun _ _ => hD
    simp only [Finset.mem_singleton, forall_eq, Finset.prod_singleton] at h
    refine (congrArg _ ?_).trans h
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    tauto
  have hκ : ∀ ω, X.resampleKernel G ⊥ ω = condExpKernel X.P (X.info Gᶜ ⊔ ⊥) ω :=
    X.resampleKernel_apply G bot_le
  have hκm : Measurable[X.info Gᶜ ⊔ ⊥] fun ω => X.resampleKernel G ⊥ ω D := by
    simp_rw [hκ]
    exact measurable_condExpKernel hD
  have h₂ := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (X.info_le G) hle hindep (f := C.indicator 1) (measurable_const.indicator hC) hκm
  have h₃ : ∫⁻ ω, X.resampleKernel G ⊥ ω D ∂X.P = X.P D := by
    have h := setLIntegral_kernel (P := X.P) hle hκ MeasurableSet.univ hD
    simpa using h
  have h₄ : ∫⁻ ω in C, X.resampleKernel G ⊥ ω D ∂X.P =
      ∫⁻ ω, C.indicator 1 ω * X.resampleKernel G ⊥ ω D ∂X.P := by
    rw [← lintegral_indicator hC']
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ C <;> simp [hω]
  rw [h₁, h₄, h₂, h₃, lintegral_indicator_one hC', hold.measure_preimage hC'.nullMeasurableSet,
    hnew.measure_preimage hD.nullMeasurableSet, mul_comm]

namespace LabelFamily

variable {X} {L K : ℕ} (Λ : X.LabelFamily)

open Proofs.Gain.Bridge in
/-- The labels of the other blocks are, up to null sets, information off the block: two blocks of
adjacent slabs share a face, which is a null set. -/
theorem otherSigma_le_aeClosure {n W : ℝ} (hn : 0 ≤ n) (hW : 0 < W) (hdet : Λ.IsDetermined n W L)
    (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ} (hz : IsBlockIndex L (o i) z) :
    Λ.otherSigma K o i z ≤ aeClosure (X.info (block n W L i z)ᶜ) X.P := by
  refine iSup₂_le fun i' z' => iSup_le fun hz' => iSup_le fun hne => ?_
  have hcc : (⟨i', z', hz'⟩ : Proofs.Gain.Bridge.BlockIdx L K o) ≠ ⟨i, z, hz⟩ := fun h => hne (by
    have h1 := congrArg Sigma.fst h
    subst h1
    have h2 := Subtype.ext_iff.1 (eq_of_heq (Sigma.mk.inj_iff.1 h).2)
    simp only [Prod.mk.injEq, true_and]
    exact h2)
  have hnull := volume_blockOf_inter hn hW hcc
  refine (Λ.sigma_le hdet i' z').trans ((info_le_aeClosure_diff X.toNoiseModel
    (measurableSet_block n W L _ _) (volume_frontier_block n W L _ _)
    (measurableSet_block n W L _ _) (volume_frontier_block n W L _ _) hnull).trans
    (aeClosure_mono (X.info_mono ?_)))
  exact fun x hx => hx.2

/-- The old noise and its resampling in the block `(i, z)` agree on the labels of the other
blocks. -/
theorem ae_mem_iff_new_of_otherSigma {n W : ℝ} (hn : 0 ≤ n) (hW : 0 < W)
    (hdet : Λ.IsDetermined n W L) (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ}
    (hz : IsBlockIndex L (o i) z) {B : Set X.Ω} (hB : MeasurableSet[Λ.otherSigma K o i z] B) :
    ∀ᵐ p ∂X.botResampling n W L, (p.1 ∈ B ↔ p.2 ((i : ℕ), z) ∈ B) := by
  obtain ⟨B', hB', hBB'⟩ := Λ.otherSigma_le_aeClosure hn hW hdet o hz B hB
  have h₁ := X.ae_mem_iff_new_of_compl (G := fun p : BlockIdx m => block n W L p.1 p.2)
    (σ := (X.botInfo n W L).1) (i := ((i : ℕ), z)) bot_le hB'
  have hold : MeasurePreserving Prod.fst (X.botResampling n W L) X.P :=
    X.measurePreserving_old _ _
  have hnew : MeasurePreserving (fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 ((i : ℕ), z))
      (X.botResampling n W L) X.P :=
    X.measurePreserving_new (σ := (X.botInfo n W L).1) bot_le
  have hae : ∀ᵐ ω ∂X.P, (ω ∈ B ↔ ω ∈ B') := eventuallyEqSet_iff.1 hBB'
  filter_upwards [h₁, hold.quasiMeasurePreserving.ae hae,
    hnew.quasiMeasurePreserving.ae hae] with p hp hp₁ hp₂
  rw [hp₁, hp, hp₂]

end LabelFamily

end Setting

namespace Proofs.Gain

variable {m L K : ℕ} {X : Setting.{u} m}

/-- **The first display of the proof of Lemma `lem:fewtranslates`**: for `Z` integrable,
`f = E[Z | (X_H)_H]` and `ω^G` the resampling of `G` with `σ_G` constant,
`f − E_G[f] = E[Z − Z^G | (X_H)_H]`, the conditional expectation on the joint law, given the labels
of the old noise. For `Z = F̄`, `Z − Z^G = ⌈K^{2/3}⌉⁻¹ Σ_m (F_m − F_m^G)`. -/
theorem condExp_sub_resampled_ae_eq (Λ : X.LabelFamily) {n W : ℝ} (hn : 0 < n) (hW : 0 < W)
    (hdet : Λ.IsDetermined n W L) (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ}
    (hz : IsBlockIndex L (o i) z) {Z : X.Ω → ℝ} (hZ : Integrable Z X.P) :
    (X.botResampling n W L)[fun p => Z p.1 - Z (p.2 ((i : ℕ), z)) |
        (Λ.allSigma K o).comap Prod.fst] =ᵐ[X.botResampling n W L]
      fun p => (X.P[Z | Λ.allSigma K o] -
        X.P[X.P[Z | Λ.allSigma K o] | Λ.otherSigma K o i z]) p.1 := by
  have hA : Λ.allSigma K o ≤ X.measurableSpace := Λ.allSigma_le hdet K o
  have hO : Λ.otherSigma K o i z ≤ X.measurableSpace := (Λ.otherSigma_le_allSigma K o i z).trans hA
  have hg : Λ.sigma i z ≤ X.measurableSpace := (Λ.sigma_le hdet i z).trans (X.info_le _)
  have hold : MeasurePreserving Prod.fst (X.botResampling n W L) X.P :=
    X.measurePreserving_old _ _
  have hnew : MeasurePreserving (fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 ((i : ℕ), z))
      (X.botResampling n W L) X.P :=
    X.measurePreserving_new (σ := (X.botInfo n W L).1) bot_le
  have hind : Indep (X.measurableSpace.comap fun p : X.Ω × (BlockIdx m → X.Ω) => p.2 ((i : ℕ), z))
      ((Λ.sigma i z).comap Prod.fst) (X.botResampling n W L) :=
    indep_of_indep_of_le_right (X.indep_new_old_bot n W L ((i : ℕ), z))
      (MeasurableSpace.comap_mono (Λ.sigma_le hdet i z))
  have key := condExp_old_sub_new_ae_eq hold hnew hO hg
    (Λ.indep_sigma_otherSigma hn hW hdet o hz).symm
    (fun B hB => Λ.ae_mem_iff_new_of_otherSigma hn.le hW hdet o hz hB) hind hZ
  rw [← Λ.allSigma_eq_otherSigma_sup o hz] at key
  refine key.trans ?_
  have htow : X.P[X.P[Z | Λ.allSigma K o] | Λ.otherSigma K o i z] =ᵐ[X.P]
      X.P[Z | Λ.otherSigma K o i z] :=
    condExp_condExp_of_le (Λ.otherSigma_le_allSigma K o i z) hA
  filter_upwards [hold.quasiMeasurePreserving.ae htow] with p hp
  simp only [Pi.sub_apply]
  rw [hp]

/-- **Jensen's inequality for conditional expectation** (proof of Lemma `lem:fewtranslates`): for
`p ≥ 1`, `‖f − E_G[f]‖_p ≤ ‖Z − Z^G‖_p`, with `f = E[Z | (X_H)_H]`. -/
theorem eLpNorm_sub_condExp_le (Λ : X.LabelFamily) {n W : ℝ} (hn : 0 < n) (hW : 0 < W)
    (hdet : Λ.IsDetermined n W L) (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ}
    (hz : IsBlockIndex L (o i) z) {Z : X.Ω → ℝ} (hZ : Integrable Z X.P) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (X.P[Z | Λ.allSigma K o] - X.P[X.P[Z | Λ.allSigma K o] | Λ.otherSigma K o i z]) p X.P ≤
      eLpNorm (fun q => Z q.1 - Z (q.2 ((i : ℕ), z))) p (X.botResampling n W L) := by
  have hold : MeasurePreserving Prod.fst (X.botResampling n W L) X.P :=
    X.measurePreserving_old _ _
  have hm : AEStronglyMeasurable (X.P[Z | Λ.allSigma K o] -
      X.P[X.P[Z | Λ.allSigma K o] | Λ.otherSigma K o i z]) X.P :=
    (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
  rw [← eLpNorm_comp_measurePreserving hm hold]
  refine le_of_eq_of_le (eLpNorm_congr_ae (condExp_sub_resampled_ae_eq Λ hn hW hdet o hz hZ).symm)
    (eLpNorm_condExp_le_eLpNorm _ hp)

end Proofs.Gain

end IsotropicVariance.Paper
