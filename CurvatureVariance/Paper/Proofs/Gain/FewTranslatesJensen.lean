/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.FewTranslates
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Lemma `lem:fewtranslates`: `f − E_G[f]` as a conditional expectation of the change

As `IsotropicVariance.Paper.Proofs.Gain.FewTranslatesJensen` in the continuum library, adapted. The
proof of Lemma `lem:fewtranslates` (the proof of [AB26, Lemma 6.4], with the changes of the paper)
starts from the resampling `ω^G` of `G` with `σ_G` constant, and the identity
`f − E_G[f] = ⌈K^{2/3}⌉⁻¹ Σ_m E[F_m − F_m^G | (X_H)_H]` (the first display of the proof of
[AB26, Lemma 6.4]), the conditional expectation being taken on the joint law of the weights and of
their resampling, given the labels of the old weights.

The first section is the same as in the continuum library. In the second, the joint law is `P ⊗ P`
with `old = Prod.fst` and `new = resample G`, which is simpler than the continuum's resampling
kernel: the facts on the labels are in `CurvatureVariance.Paper.Proofs.Gain.FewTranslates`.

* `condExp_old_sub_new_ae_eq`: the identity for two random elements `old`, `new` of the law `P`, for
  σ-algebras `O`, `g`, independent, such that old and new agree on the events of `O`, and such that
  the events of `g` of `old` are independent of `new`. The conditional expectation of `Z(old)` is
  that of `Z` moved by `old`. For the term of `Z(new)`, the test sets `B ∩ C`, `B` in `O`, `C` in
  `g`, give both sides the value `P(C) ∫_B Z`, and they form a π-system (`setIntegral_sup_eq_zero`).
* `condExp_sub_resampled_ae_eq`: **the identity of the first display of the proof of
  [AB26, Lemma 6.4]**, for a function `Z` of the weights.
* `eLpNorm_labelMean_sub_le`: Jensen's inequality for conditional expectation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace CurvatureVariance.Paper.Gain

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

/-- **The identity of the first display of the proof of [AB26, Lemma 6.4], generically**: the
conditional expectation of the change `Z(old) − Z(new)`, given the information `O ⊔ g` of `old`, is
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

/-! ### The resampling with `σ_G` constant -/

section Labels

variable {m : ℕ} {n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ} {β : Type*}
  {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β} {M : Model m}

/-- **The identity of the first display of the proof of [AB26, Lemma 6.4]**: for `Z` integrable,
`f = E[Z | (X_H)_H]` and `ω^G` the resampling of `G` with `σ_G` constant,
`f − E_G[f] = E[Z − Z^G | (X_H)_H]`, the conditional expectation on the joint law, given the labels
of the old weights. For `Z = F̄`, `Z − Z^G = ⌈K^{2/3}⌉⁻¹ Σ_m (F_m − F_m^G)`. -/
theorem IsOffsetLabels.condExp_sub_resampled_ae_eq (hM : M.Standing)
    (h : IsOffsetLabels n w L K t o lam) {i : ℕ} (hi : i < K) (g : Fin m → ℤ) {Z : Config m → ℝ}
    (hZ : Integrable Z M.P) :
    (M.P.prod M.P)[fun p => Z p.1 - Z (resample (block n w L t (i + 1) (o (i + 1)) g) p.1 p.2) |
        (blockLabelSigma K o lam Set.univ).comap Prod.fst] =ᵐ[M.P.prod M.P]
      fun p => (labelMean M.P Z K o lam -
        integrateLabel M.P (labelMean M.P Z K o lam) K o lam i g) p.1 := by
  have := hM.probP
  have hA : blockLabelSigma K o lam Set.univ ≤ (inferInstance : MeasurableSpace (Config m)) :=
    h.blockLabelSigma_le _
  have hO : blockLabelSigma K o lam {(i, g)}ᶜ ≤ (inferInstance : MeasurableSpace (Config m)) :=
    h.blockLabelSigma_le _
  have hg : MeasurableSpace.comap (lam (i + 1) (o (i + 1)) g) ⊤ ≤
      (inferInstance : MeasurableSpace (Config m)) := (h i hi g).comap_le
  have hold : MeasurePreserving (Prod.fst : Config m × Config m → Config m) (M.P.prod M.P) M.P :=
    measurePreserving_fst
  have hnew := measurePreserving_resample hM (block n w L t (i + 1) (o (i + 1)) g)
  have key := condExp_old_sub_new_ae_eq hold hnew hO hg (h.indep_label_otherLabels hM hi g).symm
    (fun B hB => Eventually.of_forall fun p => h.mem_iff_resample hB p.1 p.2)
    (h.indep_resample_label hM hi g) hZ
  rw [← blockLabelSigma_univ_eq hi g] at key
  refine key.trans ?_
  have hle : blockLabelSigma K o lam {(i, g)}ᶜ ≤ blockLabelSigma K o lam Set.univ := by
    rw [blockLabelSigma_univ_eq (o := o) (lam := lam) hi g]
    exact le_sup_left
  have htow : M.P[M.P[Z | blockLabelSigma K o lam Set.univ] | blockLabelSigma K o lam {(i, g)}ᶜ]
      =ᵐ[M.P] M.P[Z | blockLabelSigma K o lam {(i, g)}ᶜ] :=
    condExp_condExp_of_le hle hA
  filter_upwards [hold.quasiMeasurePreserving.ae htow] with p hp
  simp only [Pi.sub_apply, labelMean, integrateLabel]
  rw [hp]

/-- **Jensen's inequality for conditional expectation** (the second paragraph of the proof of
[AB26, Lemma 6.4]): for `p ≥ 1`, `‖f − E_G[f]‖_p ≤ ‖Z − Z^G‖_p`, with `f = E[Z | (X_H)_H]`. -/
theorem IsOffsetLabels.eLpNorm_labelMean_sub_le (hM : M.Standing)
    (h : IsOffsetLabels n w L K t o lam) {i : ℕ} (hi : i < K) (g : Fin m → ℤ) {Z : Config m → ℝ}
    (hZ : Integrable Z M.P) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (labelMean M.P Z K o lam -
        integrateLabel M.P (labelMean M.P Z K o lam) K o lam i g) p M.P ≤
      eLpNorm (fun q : Config m × Config m =>
        Z q.1 - Z (resample (block n w L t (i + 1) (o (i + 1)) g) q.1 q.2)) p
        (M.P.prod M.P) := by
  have := hM.probP
  have hold : MeasurePreserving (Prod.fst : Config m × Config m → Config m) (M.P.prod M.P) M.P :=
    measurePreserving_fst
  have hm : AEStronglyMeasurable (labelMean M.P Z K o lam -
      integrateLabel M.P (labelMean M.P Z K o lam) K o lam i g) M.P :=
    (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
  rw [← eLpNorm_comp_measurePreserving hm hold]
  refine le_of_eq_of_le (eLpNorm_congr_ae (h.condExp_sub_resampled_ae_eq hM hi g hZ).symm)
    (eLpNorm_condExp_le_eLpNorm _ hp)

end Labels

end CurvatureVariance.Paper.Gain
