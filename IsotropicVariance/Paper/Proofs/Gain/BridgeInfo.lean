/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Model
public import Mathlib.Probability.Independence.Basic
import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Section `sec:gain`: information up to null sets

Tools on the noise interface `Paper.NoiseModel`.

* `aeClosure m₀ P`: the σ-algebra of the sets almost surely equal to a set of `m₀`.
* `indep_info_compl`: the information of a Borel set `G` with null frontier is
  independent of the information of `Gᶜ`.
* `measure_eq_zero_or_one_of_interior_eq_empty`: the information of a Borel set with
  null frontier and empty interior (a face shared by two blocks) is trivial, being independent of
  itself.
* `info_union_le_aeClosure`: the union law for two sets.
* `info_le_aeClosure_diff`: if `S ∩ G` is Lebesgue-null, every event of the noise in `S`
  is almost surely an event of the noise in `S \ G`.
* `exists_stronglyMeasurable_iSup_ae_eq`: a function determined by the noise in a
  set covered by a null-boundary partition is almost surely a function of the information of the
  pieces (the union law `union_ae` and conditional expectation).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set

namespace IsotropicVariance.Paper.Proofs.Gain.Bridge

open IsotropicVariance.Paper

/-! ### Sets almost surely equal to sets of a σ-algebra -/

section AeClosure

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The σ-algebra of the sets almost everywhere equal to a set of `m₀`. -/
@[instance_reducible]
def aeClosure (m₀ : MeasurableSpace Ω) (P : @Measure Ω mΩ) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, MeasurableSet[m₀] t ∧ s =ᵐ[P] t
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ m₀, EventuallyEq.rfl⟩
  measurableSet_compl _ := fun ⟨t, ht, h⟩ => ⟨tᶜ, ht.compl, h.compl⟩
  measurableSet_iUnion f hf := by
    choose t ht h using hf
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, EventuallyEqSet.countable_iUnion h⟩

variable {m₀ m₁ : MeasurableSpace Ω} {P : @Measure Ω mΩ}

/-- The sets of `aeClosure m₀ P`. -/
theorem measurableSet_aeClosure_iff {s : Set Ω} :
    MeasurableSet[aeClosure m₀ P] s ↔ ∃ t, MeasurableSet[m₀] t ∧ s =ᵐ[P] t :=
  Iff.rfl

/-- A σ-algebra lies in its closure. -/
theorem le_aeClosure : m₀ ≤ aeClosure m₀ P :=
  fun s hs => ⟨s, hs, EventuallyEq.rfl⟩

/-- The closure is monotone. -/
theorem aeClosure_mono (h : m₀ ≤ m₁) : aeClosure m₀ P ≤ aeClosure m₁ P :=
  fun _ ⟨t, ht, hst⟩ => ⟨t, h t ht, hst⟩

/-- The closure of a σ-algebra contained in the closure of `m₀` is contained in it. -/
theorem aeClosure_le_of_le (h : m₁ ≤ aeClosure m₀ P) : aeClosure m₁ P ≤ aeClosure m₀ P := by
  rintro s ⟨t, ht, hst⟩
  obtain ⟨t', ht', htt'⟩ := h t ht
  exact ⟨t', ht', hst.trans htt'⟩

/-- A σ-algebra whose sets have probability `0` or `1` lies in the closure of any σ-algebra. -/
theorem le_aeClosure_of_trivial [IsProbabilityMeasure P] (hle : m₁ ≤ mΩ)
    (h : ∀ s, MeasurableSet[m₁] s → P s = 0 ∨ P s = 1) : m₁ ≤ aeClosure m₀ P := by
  intro s hs
  rcases h s hs with h0 | h1
  · exact ⟨∅, @MeasurableSet.empty _ m₀, ae_eq_empty.2 h0⟩
  · refine ⟨univ, @MeasurableSet.univ _ m₀, ae_eq_univ.2 ?_⟩
    rwa [prob_compl_eq_zero_iff (hle s hs)]

end AeClosure

/-! ### Independence and triviality of information -/

section Info

variable {m : ℕ} (N : NoiseModel m)

/-- The information of a Borel set with null frontier is independent of the information of its
complement. -/
theorem indep_info_compl {G : Set (Pt m)} (hG : MeasurableSet G)
    (hGfr : volume (frontier G) = 0) : Indep (N.info G) (N.info Gᶜ) N.P := by
  have h := N.iIndep_info Bool (fun b => bif b then G else Gᶜ)
    (fun b => by cases b <;> simp [hG, hG.compl])
    (fun b => by cases b <;> simp [hGfr, frontier_compl])
    (by
      intro i j hij
      have hd : Disjoint (interior G) (interior Gᶜ) :=
        disjoint_compl_right.mono interior_subset interior_subset
      cases i <;> cases j
      · exact absurd rfl hij
      · exact hd.symm
      · exact hd
      · exact absurd rfl hij)
  exact h.indep (i := true) (j := false) (by decide)

/-- The information of a Borel set with null frontier and empty interior is trivial: it is
independent of itself. -/
theorem measure_eq_zero_or_one_of_interior_eq_empty {F : Set (Pt m)}
    (hF : MeasurableSet F) (hfr : volume (frontier F) = 0) (hint : interior F = ∅)
    {A : Set N.Ω} (hA : MeasurableSet[N.info F] A) : N.P A = 0 ∨ N.P A = 1 := by
  have h := N.iIndep_info Bool (fun _ => F) (fun _ => hF) (fun _ => hfr)
    (fun _ _ _ => by simp [Function.onFun, hint])
  exact measure_eq_zero_or_one_of_indep_self (h.indep (i := true) (j := false) (by decide)) hA

/-- **The union law for two sets.** Every event of the noise in the union of two disjoint Borel sets
with null frontiers is almost surely an event of the noise in the two sets. -/
theorem info_union_le_aeClosure {U V : Set (Pt m)} (hU : MeasurableSet U)
    (hUfr : volume (frontier U) = 0) (hV : MeasurableSet V) (hVfr : volume (frontier V) = 0)
    (hd : Disjoint U V) : N.info (U ∪ V) ≤ aeClosure (N.info U ⊔ N.info V) N.P := by
  intro A hA
  let T : ℕ → Set (Pt m) := fun k => if k = 0 then U else if k = 1 then V else ∅
  have hT : ∀ k, MeasurableSet (T k) := by
    intro k
    simp only [T]
    split_ifs
    exacts [hU, hV, MeasurableSet.empty]
  have hTfr : ∀ k, volume (frontier (T k)) = 0 := by
    intro k
    simp only [T]
    split_ifs
    exacts [hUfr, hVfr, by simp]
  have hTd : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
      simp only [Function.onFun, T, Nat.succ_ne_zero, ite_true, ite_false, ne_eq, Nat.zero_add,
        Nat.reduceEqDiff, not_true_eq_false] at hij ⊢ <;>
      first
      | exact hd
      | exact hd.symm
      | exact disjoint_empty _
      | exact empty_disjoint _
  have hTU : ⋃ k, T k = U ∪ V := by
    apply Subset.antisymm
    · refine iUnion_subset fun k => ?_
      simp only [T]
      split_ifs
      exacts [subset_union_left, subset_union_right, empty_subset _]
    · rintro x (hx | hx)
      · exact mem_iUnion.2 ⟨0, by simp [T, hx]⟩
      · exact mem_iUnion.2 ⟨1, by simp [T, hx]⟩
  obtain ⟨B, hB, hAB⟩ := N.union_ae T hT hTfr hTd A (by rw [hTU]; exact hA)
  have hle : (⨆ k, N.info (T k)) ≤ N.info U ⊔ N.info V := by
    refine iSup_le fun k => ?_
    simp only [T]
    split_ifs
    · exact le_sup_left
    · exact le_sup_right
    · exact (N.info_mono (empty_subset _)).trans le_sup_left
  exact ⟨B, hle B hB, measure_symmDiff_eq_zero_iff.1 hAB⟩

/-- If `S ∩ G` is Lebesgue-null, every event of the noise in `S` is almost surely an event of the
noise in `S \ G`: the noise in the null set `S ∩ G` carries no information. -/
theorem info_le_aeClosure_diff {S G : Set (Pt m)} (hS : MeasurableSet S)
    (hSfr : volume (frontier S) = 0) (hG : MeasurableSet G) (hGfr : volume (frontier G) = 0)
    (hnull : volume (S ∩ G) = 0) : N.info S ≤ aeClosure (N.info (S \ G)) N.P := by
  have h := info_union_le_aeClosure N (hS.diff hG) (null_frontier_diff hSfr hGfr) (hS.inter hG)
    (null_frontier_inter hSfr hGfr) (disjoint_sdiff_left.mono_right inter_subset_right)
  rw [sdiff_union_inter] at h
  refine h.trans (aeClosure_le_of_le (sup_le le_aeClosure ?_))
  exact le_aeClosure_of_trivial (N.info_le _) fun s hs =>
    measure_eq_zero_or_one_of_interior_eq_empty N (hS.inter hG) (null_frontier_inter hSfr hGfr)
      (Measure.interior_eq_empty_of_null hnull) hs

/-- **A version measurable for the pieces.** For a null-boundary partition `T` of a set
containing `U`, an integrable function determined by the noise in `U` is almost surely equal to a
function measurable for the information of the pieces: the union law `union_ae` puts every event
of `info (⋃ T k)` almost surely in `⨆ info (T k)`, and the conditional expectation given the
pieces is then a version. -/
theorem exists_stronglyMeasurable_iSup_ae_eq {T : ℕ → Set (Pt m)}
    (hT : ∀ k, MeasurableSet (T k)) (hTfr : ∀ k, volume (frontier (T k)) = 0)
    (hTd : Pairwise (Function.onFun Disjoint T)) {U : Set (Pt m)} (hU : U ⊆ ⋃ k, T k)
    {Z' : N.Ω → ℝ} (hZm : Measurable[N.info U] Z') (hZi : Integrable Z' N.P) :
    ∃ Z'' : N.Ω → ℝ, StronglyMeasurable[⨆ k, N.info (T k)] Z'' ∧ Z' =ᵐ[N.P] Z'' := by
  set M := ⨆ k, N.info (T k) with hM
  set M₁ := N.info (⋃ k, T k) with hM₁
  have hMM₁ : M ≤ M₁ := iSup_le fun k => N.info_mono (subset_iUnion T k)
  have hM₁le : M₁ ≤ N.measurableSpace := N.info_le _
  have hMle : M ≤ N.measurableSpace := hMM₁.trans hM₁le
  refine ⟨N.P[Z' | M], stronglyMeasurable_condExp, ?_⟩
  have hZM₁ : StronglyMeasurable[M₁] Z' :=
    (hZm.mono (N.info_mono hU) le_rfl).stronglyMeasurable
  have h := ae_eq_condExp_of_forall_setIntegral_eq (m := M₁) hM₁le hZi
    (fun s _ _ => integrable_condExp.integrableOn)
    (fun s hs _ => by
      obtain ⟨t, ht, hst⟩ := N.union_ae T hT hTfr hTd s hs
      have hst' : s =ᵐ[N.P] t := measure_symmDiff_eq_zero_iff.1 hst
      rw [setIntegral_congr_set hst', setIntegral_congr_set hst',
        setIntegral_condExp hMle hZi ht])
    (stronglyMeasurable_condExp.mono hMM₁).aestronglyMeasurable
  rw [condExp_of_stronglyMeasurable hM₁le hZM₁ hZi] at h
  exact h.symm

end Info

end IsotropicVariance.Paper.Proofs.Gain.Bridge
