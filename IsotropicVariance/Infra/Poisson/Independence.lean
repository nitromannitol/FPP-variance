/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.BoundedLaw

/-!
# Independent restrictions of a Poisson random measure

Finite disjoint membership atoms give independent finite evaluation vectors. Directed generation
of the Giry sigma-algebra then gives independence of the restricted random measures themselves.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace IsotropicVariance.Infra.Poisson

/-- The two coordinate blocks of an independent family are independent vectors. -/
theorem indepFun_sum_blocks {Ω ι κ : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ι ⊕ κ → Ω → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hi : iIndepFun f P) :
    IndepFun (fun ω i => f (Sum.inl i) ω) (fun ω j => f (Sum.inr j) ω) P := by
  have hd : Disjoint (Set.range (Sum.inl : ι → ι ⊕ κ)) (Set.range (Sum.inr : κ → ι ⊕ κ)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    cases hj
  have hh := indep_iSup_of_disjoint (fun i => (hf i).comap_le) hi.iIndep hd
  rw [IndepFun_iff_Indep]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def]
  apply indep_of_indep_of_le hh
  · apply iSup_le
    intro i
    exact le_iSup_of_le (Sum.inl i) (le_iSup_of_le ⟨i, rfl⟩ le_rfl)
  · apply iSup_le
    intro j
    exact le_iSup_of_le (Sum.inr j) (le_iSup_of_le ⟨j, rfl⟩ le_rfl)

/-- Reassemble the region counts from their membership-atom counts. -/
noncomputable def reassembleCounts {ι : Type*} [Fintype ι]
    (v : (ι → Bool) → ℝ≥0∞) : ι → ℝ≥0∞ := by
  classical
  exact fun i => ∑ s : ι → Bool, if s i then v s else 0

/-- Reassembly is a measurable finite sum of coordinates. -/
theorem measurable_reassembleCounts {ι : Type*} [Fintype ι] :
    Measurable (reassembleCounts (ι := ι)) := by
  classical
  apply Measurable.of_eval
  intro i
  apply Finset.measurable_sum
  intro s _
  split_ifs
  · exact measurable_pi_apply s
  · exact measurable_const

/-- Two finite region-count vectors are independent when every cross pair of regions is disjoint. -/
theorem IsPoissonProcess.indepFun_count_vectors {d : ℕ} {Ω ι κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ] {lam : ℝ≥0}
    {η : Ω → Measure (E d)} {P : Measure Ω} (h : IsPoissonProcess lam η P)
    (B : ι → Set (E d)) (C : κ → Set (E d))
    (hB : ∀ i, MeasurableSet (B i)) (hC : ∀ j, MeasurableSet (C j))
    (hb : ∀ i, Bornology.IsBounded (B i)) (hc : ∀ j, Bornology.IsBounded (C j))
    (hcross : ∀ i j, Disjoint (B i) (C j)) :
    IndepFun (fun ω i => η ω (B i)) (fun ω j => η ω (C j)) P := by
  classical
  let A : (ι → Bool) ⊕ (κ → Bool) → Set (E d) :=
    Sum.elim (regionAtom B) (regionAtom C)
  have hcrossA (s : ι → Bool) (t : κ → Bool) : Disjoint (regionAtom B s) (regionAtom C t) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx.1
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy.1
    exact Set.disjoint_left.mp (hcross i j) hi hj
  have hmA (a) : MeasurableSet (A a) := by
    cases a with
    | inl s => exact measurableSet_regionAtom B hB s
    | inr t => exact measurableSet_regionAtom C hC t
  have hbA (a) : Bornology.IsBounded (A a) := by
    cases a with
    | inl s => exact isBounded_regionAtom B hb s
    | inr t => exact isBounded_regionAtom C hc t
  have hdA : Pairwise (fun s t => Disjoint (A s) (A t)) := by
    intro s t hst
    cases s with
    | inl s =>
      cases t with
      | inl t => exact pairwiseDisjoint_regionAtom B (fun hh => hst (congrArg Sum.inl hh))
      | inr t => exact hcrossA s t
    | inr s =>
      cases t with
      | inl t => exact (hcrossA t s).symm
      | inr t => exact pairwiseDisjoint_regionAtom C (fun hh => hst (congrArg Sum.inr hh))
  have hi := indepFun_sum_blocks (fun a => h.measurable_count (hmA a))
    (h.iIndepFun_counts A hmA hbA hdA)
  have hh := hi.comp measurable_reassembleCounts measurable_reassembleCounts
  have heqB : reassembleCounts ∘ (fun ω s => η ω (A (Sum.inl s))) =
      (fun ω i => η ω (B i)) := by
    funext ω i
    exact (count_eq_sum_atoms (η ω) B hB i).symm
  have heqC : reassembleCounts ∘ (fun ω s => η ω (A (Sum.inr s))) =
      (fun ω i => η ω (C i)) := by
    funext ω i
    exact (count_eq_sum_atoms (η ω) C hC i).symm
  rwa [heqB, heqC] at hh

/-- Independence of every pair of finite evaluation vectors implies independence of the
processes. -/
theorem indepFun_pi_of_finset {Ω T U : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : T → Ω → ℝ≥0∞) (Y : U → Ω → ℝ≥0∞)
    (hX : ∀ t, Measurable (X t)) (hY : ∀ u, Measurable (Y u))
    (hfin : ∀ (F : Finset T) (G : Finset U),
      IndepFun (fun ω (t : F) => X t ω) (fun ω (u : G) => Y u ω) P) :
    IndepFun (fun ω t => X t ω) (fun ω u => Y u ω) P := by
  classical
  let mX (t : T) := (inferInstance : MeasurableSpace ℝ≥0∞).comap (X t)
  let mY (u : U) := (inferInstance : MeasurableSpace ℝ≥0∞).comap (Y u)
  have hXm (F : Finset T) : (⨆ t ∈ F, mX t) ≤ ‹MeasurableSpace Ω› :=
    iSup₂_le fun t _ => (hX t).comap_le
  have hYm (G : Finset U) : (⨆ u ∈ G, mY u) ≤ ‹MeasurableSpace Ω› :=
    iSup₂_le fun u _ => (hY u).comap_le
  have hmonoX : Monotone (fun F : Finset T => ⨆ t ∈ F, mX t) := by
    intro F G hFG
    exact iSup₂_le fun t ht => le_iSup_of_le t (le_iSup_of_le (hFG ht) le_rfl)
  have hmonoY : Monotone (fun G : Finset U => ⨆ u ∈ G, mY u) := by
    intro F G hFG
    exact iSup₂_le fun u hu => le_iSup_of_le u (le_iSup_of_le (hFG hu) le_rfl)
  have hfin' (F : Finset T) (G : Finset U) :
      Indep (⨆ t ∈ F, mX t) (⨆ u ∈ G, mY u) P := by
    have hh := (IndepFun_iff_Indep _ _ _).mp (hfin F G)
    simpa only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def, iSup_subtype, mX, mY] using hh
  rw [IndepFun_iff_Indep]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def]
  change Indep (⨆ t, mX t) (⨆ u, mY u) P
  rw [iSup_eq_iSup_finset mX, iSup_eq_iSup_finset mY]
  apply indep_iSup_of_monotone _ hXm (iSup_le hYm) hmonoX
  intro F
  exact (indep_iSup_of_monotone (fun G => (hfin' F G).symm) hYm (hXm F) hmonoY).symm

/-- Restrictions of a Poisson process to disjoint Borel regions are independent random measures. -/
theorem IsPoissonProcess.indepFun_restrict {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (E d)} {P : Measure Ω} (h : IsPoissonProcess lam η P)
    {S T : Set (E d)} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : Disjoint S T) :
    IndepFun (fun ω => (η ω).restrict S) (fun ω => (η ω).restrict T) P := by
  have := h.isProbabilityMeasure
  let f := fun ω => (η ω).restrict S
  let g := fun ω => (η ω).restrict T
  have hfm : Measurable f := (measurable_restrict hS).comp h.measurable
  have hgm : Measurable g := (measurable_restrict hT).comp h.measurable
  have hpi : IndepFun (boundedEvaluations ∘ f) (boundedEvaluations ∘ g) P := by
    apply indepFun_pi_of_finset
      (fun B : BoundedBorelSets d => fun ω => f ω B.val)
      (fun B : BoundedBorelSets d => fun ω => g ω B.val)
      (fun B => (Measure.measurable_coe B.property.1).comp hfm)
      (fun B => (Measure.measurable_coe B.property.1).comp hgm)
    intro F G
    have hh := h.indepFun_count_vectors
      (fun B : F => B.val.val ∩ S) (fun B : G => B.val.val ∩ T)
      (fun B => B.val.property.1.inter hS) (fun B => B.val.property.1.inter hT)
      (fun B => B.val.property.2.subset inter_subset_left)
      (fun B => B.val.property.2.subset inter_subset_left)
      (fun _ _ => hST.mono inter_subset_right inter_subset_right)
    have hf : (fun ω (B : F) => f ω B.val.val) =
        (fun ω (B : F) => η ω (B.val.val ∩ S)) := by
      funext ω B
      exact Measure.restrict_apply B.val.property.1
    have hg : (fun ω (B : G) => g ω B.val.val) =
        (fun ω (B : G) => η ω (B.val.val ∩ T)) := by
      funext ω B
      exact Measure.restrict_apply B.val.property.1
    rw [hf, hg]
    exact hh

  rw [IndepFun_iff_Indep] at hpi ⊢
  change Indep ((inferInstance : MeasurableSpace (Measure (E d))).comap f)
    ((inferInstance : MeasurableSpace (Measure (E d))).comap g) P
  rw [giry_eq_comap_boundedEvaluations, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  exact hpi

/-- Restrictions to any pairwise disjoint Borel family are jointly independent. -/
theorem IsPoissonProcess.iIndepFun_restrict {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω]
    {lam : ℝ≥0} {η : Ω → Measure (E d)} {P : Measure Ω} (h : IsPoissonProcess lam η P)
    (S : ι → Set (E d)) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ProbabilityTheory.iIndepFun (fun i ω => (η ω).restrict (S i)) P := by
  classical
  have := h.isProbabilityMeasure
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro F
  induction F using Finset.induction_on with
  | empty => intro sets hs; simp
  | @insert i F hiF ih =>
    intro sets hs
    let T := ⋃ j ∈ F, S j
    have hT : MeasurableSet T := F.measurableSet_biUnion (fun j _ => hS j)
    have hsub (j : ι) (hj : j ∈ F) : S j ⊆ T := by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨j, hj, hx⟩
    have hdis : Disjoint (S i) T := by
      apply Set.disjoint_left.mpr
      intro x hxi hxt
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxt
      exact Set.disjoint_left.mp (hd (show i ≠ j from by intro hij; subst j; exact hiF hj)) hxi hxj
    let A : Set (Measure (E d)) :=
      ⋂ j ∈ F, (fun ν : Measure (E d) => ν.restrict (S j)) ⁻¹' sets j
    have hA : MeasurableSet A := F.measurableSet_biInter (fun j hj =>
      (measurable_restrict (hS j)) (hs j (Finset.mem_insert_of_mem hj)))
    have hpre : (fun ω => (η ω).restrict T) ⁻¹' A =
        ⋂ j ∈ F, (fun ω => (η ω).restrict (S j)) ⁻¹' sets j := by
      ext ω
      simp only [A, Set.mem_preimage, Set.mem_iInter]
      constructor <;> intro hh j hj
      · simpa only [Measure.restrict_restrict_of_subset (hsub j hj)] using hh j hj
      · simpa only [Measure.restrict_restrict_of_subset (hsub j hj)] using hh j hj
    have hfactor := (h.indepFun_restrict (hS i) hT hdis).measure_inter_preimage_eq_mul
      (sets i) A (hs i (Finset.mem_insert_self i F)) hA
    rw [hpre] at hfactor
    have hset : (⋂ j ∈ insert i F, (fun ω => (η ω).restrict (S j)) ⁻¹' sets j) =
        (fun ω => (η ω).restrict (S i)) ⁻¹' sets i ∩
          ⋂ j ∈ F, (fun ω => (η ω).restrict (S j)) ⁻¹' sets j := by
      ext ω
      simp
    rw [hset, Finset.prod_insert hiF, hfactor,
      ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))]

end IsotropicVariance.Infra.Poisson
