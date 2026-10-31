/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.EfronStein.AllLabels
public import CurvatureVariance.Paper.Proofs.Gain.AVBridge
public import CurvatureVariance.Paper.Defs.Labels
import CurvatureVariance.Infra.FPP.Model

/-!
# Lemma `lem:residual`: the conditional Efron–Stein inequality on the configurations

The proof of Lemma `lem:residual` is the proof of [AB26, Lemma 6.3] with changes. Its second bound
(the third paragraph of that proof) applies [BLM03, Proposition 1], extended to countably many
independent variables, conditionally on `(X_G)_G`. Given the labels, the weights of the distinct
blocks are independent, and a block resampled given its label is a conditionally independent copy of
it.

`Infra.EfronStein.lintegral_sub_condExp_allLabelSigma_le` is that inequality on a product. It uses
`CurvatureVariance.blm_proposition1`. This file carries it to the configurations, with the block
coordinates `fiberEquiv` of `Gain.LabelResidual`, in which an i.i.d. law is the product of the laws
of the blocks and of the rest of the edges. The model is the continuum's
`IsotropicVariance.Paper.Proofs.Residual.lintegral_sub_condExp_allSigma_le`. The adaptation is the
one of the lattice's coordinates: the fibers of `cellOf` for the regions `regionMap` of the noise,
and `labelES` for `labelCouplingEnergy`.

* `condExp_comp_ae_eq`: conditional expectations pull back along a measure preserving map.
* `lintegral_sub_condExp_fibers_le`: the inequality on the configurations, for the labels of the
  fibers of a map `b : Edge m → ι`.
* `meanConditionalVariance_le`: for the labels of `Gain.IsLabelFamily` at offsets in range and a
  measurable `Z ∈ L²` of the weights of the blocks of the `K` slabs,
  `E[Var[Z | (X_G)_G]] ≤ ½ Σ_G E[(Z^G − Z)²]`. Of the family, only `isBlockLabel` is used, and of
  that only `dep`, `finite` and `measurableSet`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Residual

open CurvatureVariance CurvatureVariance.Paper CurvatureVariance.Paper.Gain
open LabelResidual (blockCell cellOf cellOf_eq_iff fiberEquiv fiberEquiv_symm_update map_fiberEquiv)
open Infra.EfronStein

/-- Conditional expectations pull back along a measure preserving map. As
`IsotropicVariance.Paper.Proofs.Residual.condExp_comp_ae_eq` in the continuum library. -/
theorem condExp_comp_ae_eq {Ω Ω' : Type*} {m : MeasurableSpace Ω'} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hm : m ≤ mΩ') {Φ : Ω → Ω'} (hΦ : MeasurePreserving Φ P Q)
    {f : Ω' → ℝ} (hf : Integrable f Q) : P[f ∘ Φ | m.comap Φ] =ᵐ[P] Q[f | m] ∘ Φ := by
  have hle : m.comap Φ ≤ mΩ := (MeasurableSpace.comap_mono hm).trans hΦ.measurable.comap_le
  have hfc : Integrable (f ∘ Φ) P := hΦ.integrable_comp_of_integrable hf
  have hgc : Integrable (Q[f | m] ∘ Φ) P := hΦ.integrable_comp_of_integrable integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hfc (fun s _ _ => hgc.integrableOn) ?_
    (stronglyMeasurable_condExp.comp_measurable (comap_measurable Φ)).aestronglyMeasurable).symm
  rintro _ ⟨t, ht, rfl⟩ _
  have key : ∀ g : Ω' → ℝ, AEStronglyMeasurable g Q →
      ∫ x in Φ ⁻¹' t, g (Φ x) ∂P = ∫ y in t, g y ∂Q := fun g hg => by
    rw [← setIntegral_map (hm t ht) (by rwa [hΦ.map_eq]) hΦ.aemeasurable, hΦ.map_eq]
  change ∫ x in Φ ⁻¹' t, Q[f | m] (Φ x) ∂P = ∫ x in Φ ⁻¹' t, f (Φ x) ∂P
  rw [key _ integrable_condExp.aestronglyMeasurable, key _ hf.aestronglyMeasurable,
    setIntegral_condExp hm hf ht]

/-- The `σ`-algebra `σ(f)` does not see an injective relabelling of the values. -/
theorem comap_comp_injective {α β γ : Type*} (f : α → β) {j : β → γ}
    (hj : Function.Injective j) :
    MeasurableSpace.comap (fun a => j (f a)) ⊤ = MeasurableSpace.comap f ⊤ := by
  refine MeasurableSpace.ext fun s => ?_
  simp only [MeasurableSpace.measurableSet_comap]
  constructor
  · rintro ⟨S, -, rfl⟩
    exact ⟨j ⁻¹' S, MeasurableSpace.measurableSet_top, rfl⟩
  · rintro ⟨T, -, rfl⟩
    refine ⟨j '' T, MeasurableSpace.measurableSet_top, ?_⟩
    ext a
    simp [hj.eq_iff]

variable {m : ℕ}

section Fibers

variable {ι : Type} [Countable ι] [DecidableEq ι] (b : Edge m → ι) (F : Measure ℝ≥0)
  [IsProbabilityMeasure F]

/-- The instance of `lintegral_sub_condExp_allLabelSigma_le` on the configurations. The hypotheses
on `lab` are the fields of `IsLabelOf`, and the factorization is that of the i.i.d. law over the
fibers of `b`. -/
theorem lintegral_sub_condExp_fibers_le (cell : ι → Set (Sym2 (Vertex m)))
    (hcell : ∀ (e : Edge m) (c : ι), e.1 ∈ cell c ↔ b e = c) {β : Type}
    (lab : ι → Config m → β)
    (hdep : ∀ c ω ω', (∀ e : Edge m, b e = c → ω e = ω' e) → lab c ω = lab c ω')
    (hfin : ∀ c, (Set.range (lab c)).Finite)
    (hmeas : ∀ c ω, MeasurableSet (lab c ⁻¹' {lab c ω}))
    {Z : Config m → ℝ} (hZm : Measurable Z)
    (hZ : MemLp Z 2 (Measure.infinitePi fun _ : Edge m => F)) :
    ∫⁻ ω, ENNReal.ofReal ((Z ω - (Measure.infinitePi fun _ : Edge m => F)[Z |
          ⨆ c, MeasurableSpace.comap (lab c) ⊤] ω) ^ 2) ∂(Measure.infinitePi fun _ : Edge m => F) ≤
      (∑' c, labelES (Measure.infinitePi fun _ : Edge m => F) Z (cell c) (lab c)) / 2 := by
  classical
  set P := Measure.infinitePi fun _ : Edge m => F with hPdef
  set e := fiberEquiv b with he
  let μ : ∀ c, Measure ({e : Edge m // b e = c} → ℝ≥0) := fiberLaw b F
  let Λ : ι → Type := fun c => ↥(Set.range (lab c))
  let _ : ∀ c, Fintype (Λ c) := fun c => (hfin c).fintype
  let _ : ∀ c, MeasurableSpace (Λ c) := fun _ => ⊤
  have _ : ∀ c, MeasurableSingletonClass (Λ c) :=
    fun _ => ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let ℓ : ∀ c, ({e : Edge m // b e = c} → ℝ≥0) → Λ c := fun c x =>
    ⟨lab c (e.symm (Function.update (e (fun _ => 0)) c x)), mem_range_self _⟩
  have hℓe : ∀ c ω, (ℓ c (e ω c) : β) = lab c ω := by
    intro c ω
    show lab c (e.symm (Function.update (e (fun _ => 0)) c (e ω c))) = lab c ω
    rw [he, fiberEquiv_symm_update b c _ ω fun e' => hcell e' c]
    refine hdep c _ _ fun e' he' => ?_
    simp [Paper.resample, (hcell e' c).2 he']
  have hℓlab : ∀ c ω ω', ℓ c (e ω' c) = ℓ c (e ω c) ↔ lab c ω' = lab c ω := by
    intro c ω ω'
    rw [Subtype.ext_iff, hℓe, hℓe]
  have hℓm : ∀ c, Measurable (ℓ c) := by
    intro c
    refine measurable_to_countable' fun a => ?_
    obtain ⟨v, ω₁, rfl⟩ := a
    have hpre : ℓ c ⁻¹' {⟨lab c ω₁, mem_range_self ω₁⟩} =
        (fun x => e.symm (Function.update (e (fun _ => 0)) c x)) ⁻¹' (lab c ⁻¹' {lab c ω₁}) := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, ℓ]
      exact Subtype.ext_iff
    rw [hpre]
    exact (e.symm.measurable.comp (measurable_update _)) (hmeas c ω₁)
  -- the function on the product of the fibers
  set Z' := Z ∘ e.symm with hZ'
  have hmap : P.map e = Measure.infinitePi μ := map_fiberEquiv b F
  have hMP : MeasurePreserving e P (Measure.infinitePi μ) := ⟨e.measurable, hmap⟩
  have hZ'm : Measurable Z' := hZm.comp e.symm.measurable
  have hZ'e : Z' ∘ e = Z := by
    funext ω
    simp [hZ']
  have hZ'2 : MemLp Z' 2 (Measure.infinitePi μ) := by
    rw [← hmap, e.measurableEmbedding.memLp_map_measure_iff, hZ'e]
    exact hZ
  have hsq : Measurable (Function.uncurry fun x x' : (∀ c, ({e : Edge m // b e = c} → ℝ≥0)) =>
      ENNReal.ofReal ((Z' x - Z' x') ^ 2)) :=
    (((hZ'm.comp measurable_fst).sub (hZ'm.comp measurable_snd)).pow_const 2).ennreal_ofReal
  have hER : ∀ c, ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((Z' x - Z' (Function.update x c y)) ^ 2)
      ∂(μ c)[|ℓ c ⁻¹' {ℓ c (x c)}] ∂Measure.infinitePi μ = labelES P Z (cell c) (lab c) := by
    intro c
    rw [lintegral_lintegral_update_fiber_cond F c (fun e' => hcell e' c) (lab c) (ℓ c) (hℓm c)
      (hℓlab c) hsq]
    simp only [← he, hZ', Function.comp_apply, MeasurableEquiv.symm_apply_apply, labelES, hPdef]
  -- the inequality, from `AllLabels`
  have hES := lintegral_sub_condExp_allLabelSigma_le μ hℓm hZ'm hZ'2
  -- the `σ`-algebras
  have hσ : (⨆ c, MeasurableSpace.comap (lab c) ⊤) =
      MeasurableSpace.comap e (allLabelSigma ℓ) := by
    rw [allLabelSigma, MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    refine iSup_congr fun c => ?_
    have hval : lab c = fun ω => ((ℓ c (e ω c) : Λ c) : β) := funext fun ω => (hℓe c ω).symm
    rw [hval, comap_comp_injective (fun ω => ℓ c (e ω c)) Subtype.val_injective]
    rfl
  set E := (Measure.infinitePi μ)[Z' | allLabelSigma ℓ] with hE
  have hcond : P[Z | ⨆ c, MeasurableSpace.comap (lab c) ⊤] =ᵐ[P] E ∘ e := by
    rw [hσ]
    have h := condExp_comp_ae_eq (allLabelSigma_le hℓm) hMP (hZ'2.integrable one_le_two)
    rwa [hZ'e] at h
  have hEm : Measurable E := (stronglyMeasurable_condExp.mono (allLabelSigma_le hℓm)).measurable
  have hg : Measurable fun x => ENNReal.ofReal ((Z' x - E x) ^ 2) :=
    ((hZ'm.sub hEm).pow_const 2).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal ((Z ω - P[Z | ⨆ c, MeasurableSpace.comap (lab c) ⊤] ω) ^ 2) ∂P
      = ∫⁻ ω, ENNReal.ofReal ((Z' (e ω) - E (e ω)) ^ 2) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hcond] with ω h
        rw [h]
        simp [hZ']
    _ = ∫⁻ x, ENNReal.ofReal ((Z' x - E x) ^ 2) ∂Measure.infinitePi μ := hMP.lintegral_comp hg
    _ ≤ _ := hES
    _ = _ := by rw [tsum_congr hER]

end Fibers

/-- **The check.** The labels of `IsLabelFamily`, at offsets in range, for an i.i.d. law and a
measurable `Z ∈ L²` of the weights of the blocks of the `K` slabs: the mean conditional variance
given all the labels is at most half the block energy, which are the two sides that the second bound
of `ResidualStatement` compares. Of the family, only `isBlockLabel` is used, and of that only `dep`,
`finite` and `measurableSet`. -/
theorem meanConditionalVariance_le {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {L n : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {Pv : Pt m} {α ε : ℝ}
    {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ}
    (hfam : IsLabelFamily M K A L n t Pv α ε lam) {o : ℕ → Fin m → ℤ}
    (ho : ∀ i k, 0 ≤ o i k ∧ o i k < L) {Z : Config m → ℝ} (hZm : Measurable Z)
    (hZ : MemLp Z 2 M.P)
    (hZdep : ∀ ω ω' : Config m, (∀ e : Edge m, (∃ i < K, ∃ g,
      e.1 ∈ block n (wInt M K A n) L t (i + 1) (o (i + 1)) g) → ω e = ω' e) → Z ω = Z ω') :
    meanConditionalVariance M.P Z K o lam ≤
      blockEnergy M.P Z n (wInt M K A n) L K t lam o / 2 := by
  classical
  have := hM.probF
  have hP : M.P = Measure.infinitePi fun _ : Edge m => M.F :=
    Infra.FPP.IsIIDWeights.eq_infinitePi hM.iid
  have hprob : IsProbabilityMeasure M.P := hM.probP
  set w := wInt M K A n with hw
  have hlabels : IsOffsetLabels n w L K t o lam := hfam.isOffsetLabels ho
  set b := cellOf (n := n) (w := w) (L := L) (K := K) (t := t) (o := o) with hb
  set cell := blockCell n w L K t o with hcelldef
  have hcell : ∀ (e : Edge m) c, e.1 ∈ cell c ↔ b e = c := fun e c =>
    (cellOf_eq_iff n w L K t o e c).symm
  let β := Vertex m → Vertex m → ℝ
  let lab : Option (Fin K × (Fin m → ℤ)) → Config m → Option β := fun c ω =>
    c.map fun c' => lam ((c'.1 : ℕ) + 1) (o ((c'.1 : ℕ) + 1)) c'.2 ω
  have hlabsome : ∀ (i : Fin K) g ω,
      lab (some (i, g)) ω = some (lam ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g ω) :=
    fun _ _ _ => rfl
  have hpre : ∀ (i : Fin K) g ω, lab (some (i, g)) ⁻¹' {lab (some (i, g)) ω} =
      lam ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g ⁻¹' {lam ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g ω} := by
    intro i g ω
    ext ω'
    simp [lab]
  have hprenone : ∀ ω, lab none ⁻¹' {lab none ω} = univ := fun ω => by ext; simp [lab]
  have hdep' : ∀ c ω ω', (∀ e : Edge m, b e = c → ω e = ω' e) → lab c ω = lab c ω' := by
    rintro (_ | ⟨i, g⟩) ω ω' h
    · rfl
    · rw [hlabsome, hlabsome, (hlabels i i.isLt g).dep ω ω' fun e he => h e ((hcell e _).1 he)]
  have hfin' : ∀ c, (Set.range (lab c)).Finite := by
    rintro (_ | ⟨i, g⟩)
    · exact (Set.finite_singleton none).subset (by rintro _ ⟨ω, rfl⟩; simp [lab])
    · refine ((hlabels i i.isLt g).finite.image some).subset ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨_, ⟨ω, rfl⟩, rfl⟩
  have hmeas' : ∀ c ω, MeasurableSet (lab c ⁻¹' {lab c ω}) := by
    rintro (_ | ⟨i, g⟩) ω
    · rw [hprenone]; exact MeasurableSet.univ
    · rw [hpre]; exact (hlabels i i.isLt g).measurableSet ω
  have hfix : ∀ ω ω', Z (resample (cell none) ω ω') = Z ω :=
    eq_of_resample_blockCell_none o hZdep
  have hlab0 : labelES M.P Z (cell none) (lab none) = 0 := by
    simp [labelES, hfix]
  have hsumR : ∑' c, labelES M.P Z (cell c) (lab c) = ∑ i ∈ Finset.range K,
      ∑' g : Fin m → ℤ, labelES M.P Z (block n w L t (i + 1) (o (i + 1)) g)
        (lam (i + 1) (o (i + 1)) g) := by
    rw [tsum_option_blocks hlab0]
    refine Finset.sum_congr rfl fun i hi => tsum_congr fun g => ?_
    simp only [Finset.mem_range.1 hi, ↓reduceDIte]
    refine labelES_congr_level _ _ _ fun ω ω' => ?_
    simp [lab]
  -- the `σ`-algebra of the paper is that of the cells
  have hσ : blockLabelSigma K o lam Set.univ = ⨆ c, MeasurableSpace.comap (lab c) ⊤ := by
    refine le_antisymm (iSup₂_le fun p hp => ?_) (iSup_le ?_)
    · refine le_iSup_of_le (some (⟨p.1, hp.1⟩, p.2)) ?_
      have h : lab (some (⟨p.1, hp.1⟩, p.2)) = fun ω => some (lam (p.1 + 1) (o (p.1 + 1)) p.2 ω) :=
        funext fun ω => hlabsome ⟨p.1, hp.1⟩ p.2 ω
      rw [h, comap_comp_injective _ (Option.some_injective _)]
    · rintro (_ | ⟨i, g⟩)
      · have h : lab none = fun _ => none := rfl
        rw [h, MeasurableSpace.comap_const]
        exact bot_le
      · have h : lab (some (i, g)) = fun ω => some (lam ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g ω) :=
          funext fun ω => hlabsome i g ω
        rw [h, comap_comp_injective _ (Option.some_injective _)]
        exact le_iSup₂_of_le ((i : ℕ), g) ⟨i.isLt, Set.mem_univ _⟩ le_rfl
  have h := lintegral_sub_condExp_fibers_le b M.F cell hcell lab hdep' hfin' hmeas' hZm (hP ▸ hZ)
  rw [← hP, hsumR, ← hσ] at h
  exact h

end CurvatureVariance.Paper.Proofs.Residual
