/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Resampling.CondKernel
public import Mathlib.Probability.ProductMeasure

/-!
# Independent draws given one outcome

Generic facts behind the characterization of the resampling of Section `sec:gain`, with no noise.
For Markov kernels `κ c` from `Ω` to itself and a kernel `K` drawing, given `ω`, independently from
all of them, consider the law `P ⊗ₘ K` of the old outcome `ω` and the new outcomes `(p.2 c)_c`.

* `compProd_prod_pi`: conditional independence, `P ⊗ K (C × Π_{c ∈ s} A c) = ∫_C ∏_c κ c (A c)`.
* `map_old_new`: the pair of the old outcome and the new outcome `c` has the law `P ⊗ₘ κ c`.
* `iIndep_groupSigma`: **independence of groups.** Let `a j` be independent σ-algebras and `I j`
  disjoint sets of indices. If, for `c` in `I j`, the probability `κ c (·, B)` of an event `B` of
  `a j` is almost surely measurable for `a j`, then the σ-algebras `groupSigma (a j) (I j)`
  (the information `a j` of the old outcome and of the new outcomes of `I j`) are independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Resampling

variable {Ω ι J : Type*} {a₀ : MeasurableSpace Ω} {a : J → MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- For independent σ-algebras `a j` and `h j` measurable for `a j`, the integral of a finite
product is the product of the integrals. -/
theorem lintegral_prod_of_iIndep (hind : iIndep a P) (ha : ∀ j, a j ≤ mΩ) (t : Finset J)
    {h : J → Ω → ℝ≥0∞} (hh : ∀ j ∈ t, Measurable[a j] (h j)) :
    ∫⁻ ω, ∏ j ∈ t, h j ω ∂P = ∏ j ∈ t, ∫⁻ ω, h j ω ∂P := by
  classical
  set h' : J → Ω → ℝ≥0∞ := fun j => if j ∈ t then h j else fun _ => 1 with hh'
  have hm : ∀ j, Measurable[a j] (h' j) := fun j => by
    by_cases hj : j ∈ t
    · simpa only [hh', hj, ite_true] using hh j hj
    · simp only [hh', hj, ite_false]
      exact measurable_const
  have hX : iIndepFun h' P := by
    rw [iIndepFun_iff_iIndep (fun _ => inferInstance)]
    exact iIndep_of_iIndep_of_le hind fun j => (hm j).comap_le
  have h₁ := lintegral_prod_eq_prod_lintegral_of_indepFun t h' hX
    fun j => (hm j).mono (ha j) le_rfl
  have hcongr : ∀ j ∈ t, h' j = h j := fun j hj => by simp only [hh', hj, ite_true]
  calc ∫⁻ ω, ∏ j ∈ t, h j ω ∂P = ∫⁻ ω, ∏ j ∈ t, h' j ω ∂P :=
        lintegral_congr fun ω => Finset.prod_congr rfl fun j hj => by rw [hcongr j hj]
    _ = ∏ j ∈ t, ∫⁻ ω, h' j ω ∂P := h₁
    _ = ∏ j ∈ t, ∫⁻ ω, h j ω ∂P := Finset.prod_congr rfl fun j hj => by rw [hcongr j hj]

/-! ### The law of the old and the new outcomes -/

variable {κ : ι → Kernel Ω Ω} [∀ c, IsMarkovKernel (κ c)] {K : Kernel Ω (ι → Ω)}
  [IsMarkovKernel K]

/-- **Conditional independence given the old outcome.** -/
theorem compProd_prod_pi (hK : ∀ ω, K ω = Measure.infinitePi fun c => κ c ω) {C : Set Ω}
    (hC : MeasurableSet C) (s : Finset ι) {A : ι → Set Ω} (hA : ∀ c ∈ s, MeasurableSet (A c)) :
    (P ⊗ₘ K) (C ×ˢ (s : Set ι).pi A) = ∫⁻ ω in C, ∏ c ∈ s, κ c ω (A c) ∂P := by
  rw [Measure.compProd_apply_prod hC (MeasurableSet.pi s.countable_toSet hA)]
  refine lintegral_congr fun ω => ?_
  rw [hK, Measure.infinitePi_pi _ hA]

/-- The same as an integral over the whole space. -/
theorem compProd_prod_pi_eq_lintegral (hK : ∀ ω, K ω = Measure.infinitePi fun c => κ c ω)
    {A : Set Ω} (hA : MeasurableSet A) (T : Finset ι) {B : ι → Set Ω}
    (hB : ∀ c, MeasurableSet (B c)) :
    (P ⊗ₘ K) (A ×ˢ (T : Set ι).pi B) =
      ∫⁻ ω, A.indicator 1 ω * ∏ c ∈ T, κ c ω (B c) ∂P := by
  rw [compProd_prod_pi hK hA T fun c _ => hB c, ← lintegral_indicator hA]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ A <;> simp [hω]

/-- The pair of the old outcome and the new outcome `c` has the law `P ⊗ₘ κ c`. -/
theorem map_old_new (hK : ∀ ω, K ω = Measure.infinitePi fun c => κ c ω) (c : ι) :
    (P ⊗ₘ K).map (fun p => (p.1, p.2 c)) = P ⊗ₘ κ c := by
  have hm : Measurable fun p : Ω × (ι → Ω) => (p.1, p.2 c) :=
    measurable_fst.prodMk ((measurable_pi_apply c).comp measurable_snd)
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.map_apply hm (hA.prod hB), Measure.compProd_apply_prod hA hB]
  have hset : (fun p : Ω × (ι → Ω) => (p.1, p.2 c)) ⁻¹' (A ×ˢ B) =
      A ×ˢ ((({c} : Finset ι) : Set ι).pi fun _ => B) := by
    ext p
    simp
  rw [hset, compProd_prod_pi hK hA _ fun _ _ => hB]
  simp

/-! ### The σ-algebra of a group of indices -/

/-- The information `a₀` of the old outcome and of the new outcomes of the indices `I`. -/
@[instance_reducible]
def groupSigma (a₀ : MeasurableSpace Ω) (I : Set ι) : MeasurableSpace (Ω × (ι → Ω)) :=
  a₀.comap Prod.fst ⊔ ⨆ c ∈ I, a₀.comap fun p => p.2 c

omit mΩ in
/-- The σ-algebra of one index. -/
theorem groupSigma_singleton (a₀ : MeasurableSpace Ω) (c : ι) :
    groupSigma a₀ {c} = a₀.comap Prod.fst ⊔ a₀.comap fun p : Ω × (ι → Ω) => p.2 c := by
  simp only [groupSigma, iSup_singleton]

omit mΩ in
/-- The σ-algebra of no index. -/
theorem groupSigma_empty (a₀ : MeasurableSpace Ω) :
    groupSigma a₀ (∅ : Set ι) = a₀.comap Prod.fst := by
  simp only [groupSigma, mem_empty_iff_false, iSup_false, iSup_bot, sup_bot_eq]

/-- The events `old ∈ A`, `new c ∈ B c` for `c` in a finite subset of `I`. -/
def groupEvents (a₀ : MeasurableSpace Ω) (I : Set ι) : Set (Set (Ω × (ι → Ω))) :=
  {E | ∃ (A : Set Ω) (T : Finset ι) (B : ι → Set Ω), MeasurableSet[a₀] A ∧ (∀ c ∈ T, c ∈ I) ∧
    (∀ c, MeasurableSet[a₀] (B c)) ∧ E = A ×ˢ (T : Set ι).pi B}

omit mΩ in
/-- The events of a group form a π-system. -/
theorem isPiSystem_groupEvents (I : Set ι) : IsPiSystem (groupEvents a₀ I) := by
  classical
  rintro _ ⟨A, T, B, hA, hT, hB, rfl⟩ _ ⟨A', T', B', hA', hT', hB', rfl⟩ -
  refine ⟨A ∩ A', T ∪ T',
    fun c => (if c ∈ T then B c else univ) ∩ (if c ∈ T' then B' c else univ),
    hA.inter hA', ?_, fun c => ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    exacts [hT c h, hT' c h]
  · refine @MeasurableSet.inter _ a₀ _ _ ?_ ?_ <;> split_ifs
    exacts [hB c, @MeasurableSet.univ _ a₀, hB' c, @MeasurableSet.univ _ a₀]
  · ext ⟨ω, x⟩
    simp only [mem_inter_iff, mem_prod, Set.mem_pi, Finset.mem_coe, Finset.mem_union]
    constructor
    · rintro ⟨⟨hωA, hx⟩, hωA', hx'⟩
      refine ⟨⟨hωA, hωA'⟩, fun c _ => ⟨?_, ?_⟩⟩
      · split_ifs with h
        exacts [hx c h, mem_univ _]
      · split_ifs with h
        exacts [hx' c h, mem_univ _]
    · rintro ⟨⟨hωA, hωA'⟩, hx⟩
      refine ⟨⟨hωA, fun c hc => ?_⟩, hωA', fun c hc => ?_⟩
      · have := (hx c (Or.inl hc)).1
        rwa [ite_eq_left hc] at this
      · have := (hx c (Or.inr hc)).2
        rwa [ite_eq_left hc] at this

omit mΩ in
/-- The events of a group generate its σ-algebra. -/
theorem groupSigma_eq_generateFrom (I : Set ι) :
    groupSigma a₀ I = generateFrom (groupEvents a₀ I) := by
  apply le_antisymm
  · refine sup_le ?_ (iSup₂_le fun c hc => ?_)
    · rintro _ ⟨A, hA, rfl⟩
      refine measurableSet_generateFrom ⟨A, ∅, fun _ => univ, hA, by simp, fun _ =>
        @MeasurableSet.univ _ a₀, ?_⟩
      ext p
      simp
    · rintro _ ⟨B, hB, rfl⟩
      refine measurableSet_generateFrom ⟨univ, {c}, fun _ => B, @MeasurableSet.univ _ a₀,
        by simpa using hc, fun _ => hB, ?_⟩
      ext p
      simp
  · refine generateFrom_le ?_
    rintro _ ⟨A, T, B, hA, hT, hB, rfl⟩
    have hset : A ×ˢ (T : Set ι).pi B =
        Prod.fst ⁻¹' A ∩ ⋂ c ∈ T, (fun p : Ω × (ι → Ω) => p.2 c) ⁻¹' B c := by
      ext p
      simp
    rw [hset]
    refine @MeasurableSet.inter _ (groupSigma a₀ I) _ _ (le_sup_left (a := a₀.comap Prod.fst) _
      ⟨A, hA, rfl⟩) (@Finset.measurableSet_biInter _ _ (groupSigma a₀ I) _ T fun c hc => ?_)
    exact (le_iSup₂_of_le (f := fun c (_ : c ∈ I) =>
      a₀.comap fun p : Ω × (ι → Ω) => p.2 c) c (hT c hc) le_rfl).trans le_sup_right _
      ⟨B c, hB c, rfl⟩

/-- The σ-algebra of a group is a part of the σ-algebra of the product. -/
theorem groupSigma_le (ha : a₀ ≤ mΩ) (I : Set ι) :
    groupSigma a₀ I ≤ (inferInstance : MeasurableSpace (Ω × (ι → Ω))) := by
  refine sup_le ((comap_mono ha).trans measurable_fst.comap_le) (iSup₂_le fun c _ => ?_)
  exact (comap_mono ha).trans ((measurable_pi_apply c).comp measurable_snd).comap_le

/-! ### Independence of groups -/

omit [IsProbabilityMeasure P] [∀ c, IsMarkovKernel (κ c)] in
/-- If the probabilities of the new outcomes of a group are almost surely measurable for `a₀`, so
is the probability given the old outcome of an event of the group. -/
theorem exists_measurable_ae_eq_prod {I : Set ι}
    (H : ∀ c ∈ I, ∀ B, MeasurableSet[a₀] B →
      ∃ g : Ω → ℝ≥0∞, Measurable[a₀] g ∧ ∀ᵐ ω ∂P, κ c ω B = g ω)
    {A : Set Ω} {T : Finset ι} {B : ι → Set Ω} (hA : MeasurableSet[a₀] A) (hT : ∀ c ∈ T, c ∈ I)
    (hB : ∀ c, MeasurableSet[a₀] (B c)) :
    ∃ h : Ω → ℝ≥0∞, Measurable[a₀] h ∧
      ∀ᵐ ω ∂P, A.indicator 1 ω * ∏ c ∈ T, κ c ω (B c) = h ω := by
  have hg : ∀ c ∈ T, ∃ g : Ω → ℝ≥0∞, Measurable[a₀] g ∧ ∀ᵐ ω ∂P, κ c ω (B c) = g ω :=
    fun c hc => H c (hT c hc) _ (hB c)
  choose! g hgm hgae using hg
  refine ⟨fun ω => A.indicator 1 ω * ∏ c ∈ T, g c ω, ?_, ?_⟩
  · exact (measurable_const.indicator hA).mul (Finset.measurable_prod T hgm)
  · filter_upwards [(eventually_all_finset T).2 hgae] with ω hω
    rw [Finset.prod_congr rfl hω]

omit mΩ in
/-- A finite intersection of rectangles is a rectangle. -/
theorem biInter_prod_pi (t : Finset J) (A : J → Set Ω) (T : J → Finset ι) (B : J → ι → Set Ω)
    [DecidableEq ι] :
    ⋂ j ∈ t, A j ×ˢ (T j : Set ι).pi (B j) =
      (⋂ j ∈ t, A j) ×ˢ ((t.biUnion T : Finset ι) : Set ι).pi
        fun c => ⋂ j ∈ t, ⋂ (_ : c ∈ T j), B j c := by
  ext p
  simp only [mem_iInter, mem_prod, Set.mem_pi, Finset.mem_coe, Finset.mem_biUnion]
  constructor
  · intro h
    exact ⟨fun j hj => (h j hj).1, fun c _ j hj hc => (h j hj).2 c hc⟩
  · rintro ⟨h₁, h₂⟩ j hj
    exact ⟨h₁ j hj, fun c hc => h₂ c ⟨j, hj, hc⟩ j hj hc⟩

omit mΩ in
/-- The indicator of a finite intersection is the product of the indicators. -/
theorem indicator_biInter_eq_prod (t : Finset J) (A : J → Set Ω) (ω : Ω) :
    (⋂ j ∈ t, A j).indicator (1 : Ω → ℝ≥0∞) ω = ∏ j ∈ t, (A j).indicator 1 ω := by
  by_cases hω : ω ∈ ⋂ j ∈ t, A j
  · rw [indicator_of_mem hω, Pi.one_apply]
    refine (Finset.prod_eq_one fun j hj => ?_).symm
    rw [indicator_of_mem (mem_iInter₂.1 hω j hj), Pi.one_apply]
  · rw [indicator_of_notMem hω]
    obtain ⟨j, hj, hωj⟩ : ∃ j ∈ t, ω ∉ A j := by
      simpa only [mem_iInter, not_forall, exists_prop] using hω
    exact (Finset.prod_eq_zero hj (indicator_of_notMem hωj _)).symm

/-- **Independence of groups.** Let `a j` be independent σ-algebras and `I j` pairwise disjoint sets
of indices. If, for `c` in `I j`, the probability `κ c (·, B)` of each event `B` of `a j` is almost
surely measurable for `a j`, then the information `a j` of the old outcome and of the new outcomes
of `I j` are independent, over `j`. -/
theorem iIndep_groupSigma (hK : ∀ ω, K ω = Measure.infinitePi fun c => κ c ω)
    (hind : iIndep a P) (ha : ∀ j, a j ≤ mΩ) {I : J → Set ι}
    (hI : Pairwise (Function.onFun Disjoint I))
    (H : ∀ j, ∀ c ∈ I j, ∀ B, MeasurableSet[a j] B →
      ∃ g : Ω → ℝ≥0∞, Measurable[a j] g ∧ ∀ᵐ ω ∂P, κ c ω B = g ω) :
    iIndep (fun j => groupSigma (a j) (I j)) (P ⊗ₘ K) := by
  classical
  refine iIndepSets.iIndep (fun j => groupSigma_le (ha j) (I j))
    (fun j => groupEvents (a j) (I j)) (fun j => isPiSystem_groupEvents (I j))
    (fun j => groupSigma_eq_generateFrom (I j)) ?_
  rw [iIndepSets_iff]
  intro t f hf
  choose! A T B hA hT hB hE using hf
  have hgrp : ∀ j ∈ t, ∃ h : Ω → ℝ≥0∞, Measurable[a j] h ∧
      ∀ᵐ ω ∂P, (A j).indicator 1 ω * ∏ c ∈ T j, κ c ω (B j c) = h ω :=
    fun j hj => exists_measurable_ae_eq_prod (H j) (hA j hj) (hT j hj) (hB j hj)
  choose! h hhm hhae using hgrp
  have hE' : ∀ j ∈ t, (P ⊗ₘ K) (f j) = ∫⁻ ω, h j ω ∂P := fun j hj => by
    rw [hE j hj, compProd_prod_pi_eq_lintegral hK (ha j _ (hA j hj)) (T j)
      fun c => ha j _ (hB j hj c)]
    exact lintegral_congr_ae (hhae j hj)
  rw [Finset.prod_congr rfl hE', ← lintegral_prod_of_iIndep hind ha t hhm]
  have hset : ⋂ j ∈ t, f j = ⋂ j ∈ t, A j ×ˢ (T j : Set ι).pi (B j) :=
    iInter₂_congr fun j hj => hE j hj
  -- the indices of different groups are different
  have hdisj : ∀ j ∈ t, ∀ j' ∈ t, ∀ c, c ∈ T j → c ∈ T j' → j = j' := by
    intro j hj j' hj' c hc hc'
    by_contra hjj
    exact disjoint_left.1 (hI hjj) (hT j hj c hc) (hT j' hj' c hc')
  have hB' : ∀ j ∈ t, ∀ c ∈ T j, (⋂ j' ∈ t, ⋂ (_ : c ∈ T j'), B j' c) = B j c := by
    intro j hj c hc
    ext y
    simp only [mem_iInter]
    refine ⟨fun hy => hy j hj hc, fun hy j' hj' hc' => ?_⟩
    rwa [← hdisj j hj j' hj' c hc hc']
  have hAm : MeasurableSet (⋂ j ∈ t, A j) :=
    Finset.measurableSet_biInter t fun j hj => ha j _ (hA j hj)
  have hBm : ∀ c, MeasurableSet (⋂ j ∈ t, ⋂ (_ : c ∈ T j), B j c) := fun c =>
    Finset.measurableSet_biInter t fun j hj => MeasurableSet.iInter fun _ => ha j _ (hB j hj c)
  have hpd : ((t : Set J)).PairwiseDisjoint T := fun j hj j' hj' hjj' =>
    Finset.disjoint_left.2 fun c hc hc' => hjj' (hdisj j hj j' hj' c hc hc')
  rw [hset, biInter_prod_pi, compProd_prod_pi_eq_lintegral hK hAm _ hBm]
  refine lintegral_congr_ae ?_
  filter_upwards [(eventually_all_finset t).2 hhae] with ω hω
  rw [← Finset.prod_congr rfl hω, Finset.prod_mul_distrib, indicator_biInter_eq_prod,
    Finset.prod_biUnion hpd]
  refine congrArg _ (Finset.prod_congr rfl fun j hj => Finset.prod_congr rfl fun c hc => ?_)
  rw [hB' j hj c hc]

end IsotropicVariance.Paper.Proofs.Resampling
