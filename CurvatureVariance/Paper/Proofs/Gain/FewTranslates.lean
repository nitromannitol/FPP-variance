/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Labels
public import CurvatureVariance.Paper.Proofs.Gain.InfluenceTranslate
public import CurvatureVariance.Paper.Proofs.LabelResidual.Blocks
public import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration

/-!
# Lemma `lem:fewtranslates`: the expectation `E_G` on the weights

As `IsotropicVariance.Paper.Proofs.Gain.FewTranslates` in the continuum library, adapted. The text
before [AB26, Lemma 6.3] defines `E_G` as the expectation over the variable `X_G` alone, the other
labels being fixed, and the text before Lemma `lem:residual` keeps it. The contract writes it as
`Gain.integrateLabel`, the conditional expectation given the labels of the other blocks. The labels
of distinct blocks are independent, so the two agree.

The continuum's independence comes from the independence of the noise in disjoint sets. Here the
labels are functions on `Config m`, and the one fact used is that resampling a block `G` changes no
label of another block, and makes the label of `G` that of the fresh weights.

* `IsOffsetLabels.apply_resample_of_ne`, `IsOffsetLabels.apply_resample_self`: this fact.
* `mem_iff_of_forall_label_eq`: the events of the labels of a set of blocks do not separate two
  configurations with the same labels.
* `indep_label_otherLabels`: the label of a block is independent of the others.
* `indep_resample_label`: the resampled weights of `G` are independent of the label of `G` of the
  old weights.
* `blockLabelSigma_univ_eq`: the information of all labels is that of the others and that of the
  block.
* `condExp_eq_sum_of_indep`: `E[φ(λ, rest) | rest] = Σ_v P(λ = v) φ(v, rest)` for `λ` finite-valued
  and independent of `rest`.
* `condExp_other_eq_sum_label`: **the identity.** If `f = φ ∘ (X_H)_H` almost surely, then almost
  surely `E[f | the other labels] = Σ_v P(X_G = v) φ((X_H)_H with X_G replaced by v)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace CurvatureVariance.Paper.Gain

/-! ### Integrating out an independent finite-valued variable -/

section Generic

variable {Ω V : Type*} {m₂ mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `E[φ(λ, rest) | rest] = Σ_v P(λ = v) φ(v, rest)` for `λ` finite-valued and independent of
`rest`, written with `h v = φ(v, rest)` measurable for the information `m₂` of `rest`, as in the
continuum library's module `IsotropicVariance.Paper.Proofs.Gain.FewTranslates`. -/
theorem condExp_eq_sum_of_indep [Fintype V] [IsProbabilityMeasure P] (hm₂ : m₂ ≤ mΩ) (ℓ : Ω → V)
    (hℓ : MeasurableSpace.comap ℓ ⊤ ≤ mΩ) (hind : Indep (MeasurableSpace.comap ℓ ⊤) m₂ P)
    (h : V → Ω → ℝ) (hm : ∀ v, StronglyMeasurable[m₂] (h v)) (hi : ∀ v, Integrable (h v) P) :
    P[fun ω => h (ℓ ω) ω | m₂] =ᵐ[P] fun ω => ∑ v, P.real (ℓ ⁻¹' {v}) * h v ω := by
  classical
  have hset : ∀ v, MeasurableSet[MeasurableSpace.comap ℓ ⊤] (ℓ ⁻¹' {v}) := fun v =>
    ⟨{v}, MeasurableSpace.measurableSet_top, rfl⟩
  let ind : V → Ω → ℝ := fun v => (ℓ ⁻¹' {v}).indicator 1
  have hindm : ∀ v, StronglyMeasurable[MeasurableSpace.comap ℓ ⊤] (ind v) := fun v =>
    stronglyMeasurable_const.indicator (hset v)
  have hindi : ∀ v, Integrable (ind v) P := fun v =>
    (integrable_const (1 : ℝ)).indicator (hℓ _ (hset v))
  have hsplit : (fun ω => h (ℓ ω) ω) = ∑ v, ind v * h v := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, ind]
    rw [Finset.sum_eq_single (ℓ ω)]
    · simp
    · intro v _ hv
      have : ω ∉ ℓ ⁻¹' {v} := fun hω => hv hω.symm
      simp [indicator_of_notMem this]
    · simp
  have hprod : ∀ v, Integrable (ind v * h v) P := fun v => by
    refine (hi v).bdd_mul (c := 1) (hindm v |>.mono hℓ).aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases hω : ω ∈ ℓ ⁻¹' {v} <;> simp [ind, hω]
  have hone : ∀ v, P[ind v * h v | m₂] =ᵐ[P] fun ω => P.real (ℓ ⁻¹' {v}) * h v ω := fun v => by
    have h1 := condExp_mul_of_stronglyMeasurable_right (hm v) (hprod v) (hindi v)
    have h2 := condExp_indep_eq hℓ hm₂ (hindm v) hind
    have h3 : ∫ ω, ind v ω ∂P = P.real (ℓ ⁻¹' {v}) := by
      rw [integral_indicator_one (hℓ _ (hset v))]
    filter_upwards [h1, h2] with ω h1 h2
    rw [h1, Pi.mul_apply, h2, h3]
  rw [hsplit]
  refine (condExp_finsetSum (fun v _ => hprod v) m₂).trans ?_
  have hall := ae_all_iff.2 hone
  filter_upwards [hall] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ => hω v

/-- A function of an independent pair: if `h v` is measurable for `m₂`, the integrability of
`h (ℓ ω) ω` gives that of `h v` at every value `v` of positive probability, as in the continuum
library's module `IsotropicVariance.Paper.Proofs.Gain.FewTranslates`. -/
theorem integrable_of_measure_ne_zero [IsProbabilityMeasure P] (hm₂ : m₂ ≤ mΩ) (ℓ : Ω → V)
    (hℓ : MeasurableSpace.comap ℓ ⊤ ≤ mΩ) (hind : Indep (MeasurableSpace.comap ℓ ⊤) m₂ P)
    (h : V → Ω → ℝ) (hm : ∀ v, StronglyMeasurable[m₂] (h v))
    (hi : Integrable (fun ω => h (ℓ ω) ω) P) {v : V} (hv : P (ℓ ⁻¹' {v}) ≠ 0) :
    Integrable (h v) P := by
  classical
  have hset : MeasurableSet[MeasurableSpace.comap ℓ ⊤] (ℓ ⁻¹' {v}) :=
    ⟨{v}, MeasurableSpace.measurableSet_top, rfl⟩
  have hsm : StronglyMeasurable (h v) := (hm v).mono hm₂
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace hℓ hm₂ hind
    (f := (ℓ ⁻¹' {v}).indicator 1) (g := fun ω => ‖h v ω‖ₑ)
    (measurable_const.indicator hset) (hm v).enorm
  have hle : ∫⁻ ω, (ℓ ⁻¹' {v}).indicator 1 ω * ‖h v ω‖ₑ ∂P ≤ ∫⁻ ω, ‖h (ℓ ω) ω‖ₑ ∂P := by
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ ℓ ⁻¹' {v}
    · have hω' : ℓ ω = v := hω
      simp [hω, hω']
    · simp [hω]
  rw [hprod, lintegral_indicator_one (hℓ _ hset)] at hle
  have hfin := hle.trans_lt hi.2
  exact lt_top_iff_ne_top.2 fun htop => by
    rw [htop, ENNReal.mul_top hv] at hfin
    exact lt_irrefl _ hfin

/-- **`E_G` is the expectation over `X_G` alone** (the text before [AB26, Lemma 6.3]), for variables
`lab c` with values in finite sets: if `O` is the information of the variables other than `c₀`,
`lab c₀` is independent of `O`, and `f = φ ∘ (lab c)_c` almost surely, with `φ` measurable, then
almost surely `E[f | O] = Σ_v P(lab c₀ = v) φ((lab c)_c with lab c₀ replaced by v)`.

As `condExp_otherSigma_eq_sum_label` of the continuum library's module
`IsotropicVariance.Paper.Proofs.Gain.FewTranslates`. The continuum's variables have one type of
values. Here each has its own, so the statement is for a family of finite types. Each
`φ((lab c)_c with lab c₀ replaced by v)` is integrable when `v` has positive probability
(`integrable_of_measure_ne_zero`). The terms of the other values vanish, so `φ` need not be bounded.
-/
theorem condExp_other_eq_sum_label {ι : Type*} [DecidableEq ι] {V : ι → Type*}
    [∀ c, MeasurableSpace (V c)] [∀ c, MeasurableSingletonClass (V c)] [∀ c, Fintype (V c)]
    [IsProbabilityMeasure P] (lab : ∀ c, Ω → V c) (c₀ : ι) (hO : m₂ ≤ mΩ)
    (hℓ : MeasurableSpace.comap (lab c₀) ⊤ ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap (lab c₀) ⊤) m₂ P)
    (hlab : ∀ c, c ≠ c₀ → MeasurableSpace.comap (lab c) ⊤ ≤ m₂)
    {φ : (∀ c, V c) → ℝ} (hφ : Measurable φ) {f : Ω → ℝ}
    (hf : f =ᵐ[P] fun ω => φ fun c => lab c ω) (hfi : Integrable f P) :
    P[f | m₂] =ᵐ[P] fun ω =>
      ∑ v : V c₀, P.real (lab c₀ ⁻¹' {v}) * φ (Function.update (fun c => lab c ω) c₀ v) := by
  classical
  set ℓ := lab c₀ with hℓ_def
  set h : V c₀ → Ω → ℝ := fun v ω => φ (Function.update (fun c => lab c ω) c₀ v) with hh
  have hupd : ∀ v, Measurable[m₂] fun ω => Function.update (fun c => lab c ω) c₀ v := fun v => by
    refine @Measurable.of_eval _ _ _ m₂ _ _ fun c => ?_
    by_cases hc : c = c₀
    · subst hc
      simp only [Function.update_self]
      exact @measurable_const _ _ _ m₂ _
    · simp only [Function.update_of_ne hc]
      refine Measurable.mono (ma := MeasurableSpace.comap (lab c) ⊤) ?_ (hlab c hc) le_rfl
      exact fun t _ => ⟨t, MeasurableSpace.measurableSet_top, rfl⟩
  have hm : ∀ v, StronglyMeasurable[m₂] (h v) := fun v =>
    (hφ.comp (hupd v)).stronglyMeasurable
  have hself : ∀ ω, h (ℓ ω) ω = φ fun c => lab c ω := fun ω => by
    simp only [hh]
    congr 1
    exact Function.update_eq_self c₀ (fun c => lab c ω)
  have hif : Integrable (fun ω => h (ℓ ω) ω) P :=
    hfi.congr (hf.mono fun ω hω => by rw [hω]; exact (hself ω).symm)
  set h' : V c₀ → Ω → ℝ := fun v => if P (ℓ ⁻¹' {v}) ≠ 0 then h v else 0 with hh'
  have hm' : ∀ v, StronglyMeasurable[m₂] (h' v) := fun v => by
    simp only [hh']
    split_ifs
    · exact hm v
    · exact stronglyMeasurable_zero
  have hi' : ∀ v, Integrable (h' v) P := fun v => by
    simp only [hh']
    split_ifs with hv
    · exact integrable_of_measure_ne_zero hO ℓ hℓ hind h hm hif hv
    · exact integrable_zero _ _ _
  have hae : f =ᵐ[P] fun ω => h' (ℓ ω) ω := by
    have hnull : ∀ᵐ ω ∂P, P (ℓ ⁻¹' {ℓ ω}) ≠ 0 := by
      have e : {ω | ¬ P (ℓ ⁻¹' {ℓ ω}) ≠ 0} =
          ⋃ v ∈ {v : V c₀ | P (ℓ ⁻¹' {v}) = 0}, ℓ ⁻¹' {v} := by
        ext ω
        simp
      rw [ae_iff, e]
      exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun v hv => hv
    filter_upwards [hf, hnull] with ω hω hne
    simp only [hh', ite_eq_left hne]
    rw [hω, hself]
  refine (condExp_congr_ae hae).trans ?_
  refine (condExp_eq_sum_of_indep hO ℓ hℓ hind h' hm' hi').trans ?_
  refine Eventually.of_forall fun ω => Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : P (ℓ ⁻¹' {v}) = 0
  · simp [measureReal_def, hv]
  · simp [hh', hv, hh]

end Generic

/-! ### Resampling a block and the labels -/

section Labels

variable {m : ℕ} {n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ} {β : Type*}
  {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β}

/-- **Resampling a block changes no label of another block.** -/
theorem IsOffsetLabels.apply_resample_of_ne (h : IsOffsetLabels n w L K t o lam) {i i' : ℕ}
    {g g' : Fin m → ℤ} (hi' : i' < K) (hne : (i', g') ≠ (i, g)) (ω ω' : Config m) :
    lam (i' + 1) (o (i' + 1)) g' (resample (block n w L t (i + 1) (o (i + 1)) g) ω ω') =
      lam (i' + 1) (o (i' + 1)) g' ω := by
  classical
  refine (h i' hi' g').dep _ _ fun e he => ?_
  have hnot : e.1 ∉ block n w L t (i + 1) (o (i + 1)) g := fun hG => by
    obtain ⟨h1, h2⟩ := LabelResidual.eq_of_mem_block_of_mem_block hG he
    exact hne (by rw [h1, h2])
  simp [resample, hnot]

/-- **Resampling a block makes its label that of the fresh weights.** -/
theorem IsOffsetLabels.apply_resample_self (h : IsOffsetLabels n w L K t o lam) {i : ℕ}
    (hi : i < K) (g : Fin m → ℤ) (ω ω' : Config m) :
    lam (i + 1) (o (i + 1)) g (resample (block n w L t (i + 1) (o (i + 1)) g) ω ω') =
      lam (i + 1) (o (i + 1)) g ω' := by
  classical
  refine (h i hi g).dep _ _ fun e he => ?_
  simp [resample, he]

omit t n w L in
/-- The events of the labels of a set of blocks do not separate two configurations with the same
labels on it. -/
theorem mem_iff_of_forall_label_eq {S : Set (ℕ × (Fin m → ℤ))} {B : Set (Config m)}
    (hB : MeasurableSet[blockLabelSigma K o lam S] B) {ω ω' : Config m}
    (h : ∀ p : ℕ × (Fin m → ℤ), p.1 < K → p ∈ S →
      lam (p.1 + 1) (o (p.1 + 1)) p.2 ω = lam (p.1 + 1) (o (p.1 + 1)) p.2 ω') :
    ω ∈ B ↔ ω' ∈ B := by
  let _ : MeasurableSpace β := ⊤
  let Φ : Config m → {p : ℕ × (Fin m → ℤ) // p.1 < K ∧ p ∈ S} → β :=
    fun ω p => lam (p.1.1 + 1) (o (p.1.1 + 1)) p.1.2 ω
  have hle : blockLabelSigma K o lam S ≤ MeasurableSpace.comap Φ MeasurableSpace.pi := by
    refine iSup₂_le fun p hp => ?_
    change MeasurableSpace.comap ((fun x => x (⟨p, hp⟩ :
      {p : ℕ × (Fin m → ℤ) // p.1 < K ∧ p ∈ S})) ∘ Φ) ⊤ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  obtain ⟨T, -, rfl⟩ := hle B hB
  have e : Φ ω = Φ ω' := funext fun p => h p.1 p.2.1 p.2.2
  simp only [mem_preimage, e]

/-- The old weights and their resampling of a block lie in the same events of the labels of the
other blocks. -/
theorem IsOffsetLabels.mem_iff_resample (h : IsOffsetLabels n w L K t o lam) {i : ℕ}
    {g : Fin m → ℤ} {B : Set (Config m)}
    (hB : MeasurableSet[blockLabelSigma K o lam {(i, g)}ᶜ] B) (ω ω' : Config m) :
    ω ∈ B ↔ resample (block n w L t (i + 1) (o (i + 1)) g) ω ω' ∈ B :=
  mem_iff_of_forall_label_eq hB fun _ hp hpS =>
    (h.apply_resample_of_ne (i := i) (g := g) hp hpS ω ω').symm

variable {M : Model m}

/-- **The label of a block is independent of the labels of the others.** Under `P ⊗ P`, the
resampling `ω^G` has the law `P`; it has the other labels of the old weights and the label of `G` of
the fresh weights. -/
theorem IsOffsetLabels.indep_label_otherLabels (hM : M.Standing)
    (h : IsOffsetLabels n w L K t o lam) {i : ℕ} (hi : i < K) (g : Fin m → ℤ) :
    Indep (MeasurableSpace.comap (lam (i + 1) (o (i + 1)) g) ⊤)
      (blockLabelSigma K o lam {(i, g)}ᶜ) M.P := by
  have := hM.probP
  set G := block n w L t (i + 1) (o (i + 1)) g with hG
  have hres := measurePreserving_resample hM G
  rw [Indep_iff]
  rintro _ B ⟨C, -, rfl⟩ hB
  have hC' : MeasurableSet (lam (i + 1) (o (i + 1)) g ⁻¹' C) :=
    (h i hi g).comap_le _ ⟨C, MeasurableSpace.measurableSet_top, rfl⟩
  have hB' : MeasurableSet B := h.blockLabelSigma_le _ B hB
  have hset : (fun p : Config m × Config m => resample G p.1 p.2) ⁻¹'
      (lam (i + 1) (o (i + 1)) g ⁻¹' C ∩ B) = B ×ˢ (lam (i + 1) (o (i + 1)) g ⁻¹' C) := by
    ext p
    simp only [mem_preimage, mem_inter_iff, mem_prod]
    rw [h.apply_resample_self hi g, ← h.mem_iff_resample hB, and_comm]
  rw [← hres.measure_preimage (hC'.inter hB').nullMeasurableSet, hset, Measure.prod_prod,
    mul_comm]

/-- **The resampling of a block is independent of the label of the block of the old weights**: the
exchange of the two samples in the block preserves `P ⊗ P`, maps the old weights to `ω^G`, and keeps
the label of `G` of the old weights in the second sample. -/
theorem IsOffsetLabels.indep_resample_label (hM : M.Standing)
    (h : IsOffsetLabels n w L K t o lam) {i : ℕ} (hi : i < K) (g : Fin m → ℤ) :
    Indep (MeasurableSpace.comap (fun p : Config m × Config m =>
        resample (block n w L t (i + 1) (o (i + 1)) g) p.1 p.2) inferInstance)
      ((MeasurableSpace.comap (lam (i + 1) (o (i + 1)) g) ⊤).comap Prod.fst) (M.P.prod M.P) := by
  have := hM.probP
  have := hM.probF
  set G := block n w L t (i + 1) (o (i + 1)) g with hG
  have hres := measurePreserving_resample hM G
  have hτ := Responses.measurePreserving_exchange hM.iid G
  have hfst : MeasurePreserving (Prod.fst : Config m × Config m → Config m) (M.P.prod M.P) M.P :=
    measurePreserving_fst
  rw [Indep_iff]
  rintro _ _ ⟨D, hD, rfl⟩ ⟨_, ⟨C, -, rfl⟩, rfl⟩
  have hC' : MeasurableSet (lam (i + 1) (o (i + 1)) g ⁻¹' C) :=
    (h i hi g).comap_le _ ⟨C, MeasurableSpace.measurableSet_top, rfl⟩
  have hset : (fun p : Config m × Config m => resample G p.1 p.2) ⁻¹' D ∩
      Prod.fst ⁻¹' (lam (i + 1) (o (i + 1)) g ⁻¹' C) =
      (fun p : Config m × Config m => (resample G p.1 p.2, resample G p.2 p.1)) ⁻¹'
        (D ×ˢ (lam (i + 1) (o (i + 1)) g ⁻¹' C)) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_prod]
    rw [h.apply_resample_self hi g]
  rw [hset, hτ.measure_preimage (hD.prod hC').nullMeasurableSet, Measure.prod_prod,
    hres.measure_preimage hD.nullMeasurableSet, hfst.measure_preimage hC'.nullMeasurableSet]

omit M in
/-- **The information of all labels is that of the others and that of the block.** -/
theorem blockLabelSigma_univ_eq {i : ℕ} (hi : i < K) (g : Fin m → ℤ) :
    blockLabelSigma K o lam Set.univ = blockLabelSigma K o lam {(i, g)}ᶜ ⊔
      MeasurableSpace.comap (lam (i + 1) (o (i + 1)) g) ⊤ := by
  refine le_antisymm (iSup₂_le fun p hp => ?_) (sup_le ?_ ?_)
  · by_cases hpe : p = (i, g)
    · subst hpe
      exact le_sup_right
    · have hle : MeasurableSpace.comap (lam (p.1 + 1) (o (p.1 + 1)) p.2) ⊤ ≤
          blockLabelSigma K o lam {(i, g)}ᶜ :=
        le_iSup₂_of_le p ⟨hp.1, hpe⟩ le_rfl
      exact hle.trans le_sup_left
  · exact iSup₂_le fun p hp => le_iSup₂_of_le p ⟨hp.1, Set.mem_univ _⟩ le_rfl
  · exact le_iSup₂_of_le (i, g) ⟨hi, Set.mem_univ _⟩ le_rfl

end Labels

end CurvatureVariance.Paper.Gain
