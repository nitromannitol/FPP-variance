/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
public import CurvatureVariance.Paper.Proofs.Responses.Exchange
import CurvatureVariance.Paper.Proofs.Responses.SlabArrays
import CurvatureVariance.Infra.FPP.Model

/-!
# Independent resampling as an exchangeable slab replacement

Two independent copies of the weights are realized on one product indexed by `Bool × Edge`.
The original fields have joint law `P ⊗ P`; disjoint slabs read disjoint coordinates. Thus the
exchangeable-replacement contract can be specialized to the original-law Efron–Stein terms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- Two independent weight fields, with a single explicit coordinate carrier. -/
abbrev PairWeights (m : ℕ) := (Bool × Edge m) → ℝ≥0

/-- The old configuration in the paired weight space. -/
def pairOld (ω : PairWeights m) : Config m := fun e => ω (false, e)

/-- The independent fresh configuration in the paired weight space. -/
def pairFresh (ω : PairWeights m) : Config m := fun e => ω (true, e)

/-- The joint pair of configurations. -/
def pairFields (ω : PairWeights m) : Config m × Config m := (pairOld ω, pairFresh ω)

/-- The law of the paired coordinates. -/
noncomputable def pairLaw (F : Measure ℝ≥0) : Measure (PairWeights m) :=
  Measure.infinitePi fun _ : Bool × Edge m => F

/-- The two fields have the original product law. -/
theorem measurePreserving_pairFields {P : Measure (Config m)} {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] (hP : IsIIDWeights P F) :
    MeasurePreserving (pairFields (m := m)) (pairLaw F) (P.prod P) := by
  have hm : Measurable (pairFields (m := m)) :=
    (measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
  refine ⟨hm, ?_⟩
  let f : (Bool → Config m) → Config m × Config m := fun ω => (ω false, ω true)
  have hf : Measurable f := (measurable_pi_apply false).prodMk (measurable_pi_apply true)
  have heq : (pairLaw (m := m) F).map pairFields =
      ((pairLaw (m := m) F).map (MeasurableEquiv.curry Bool (Edge m) ℝ≥0)).map f := by
    rw [Measure.map_map hf (MeasurableEquiv.curry Bool (Edge m) ℝ≥0).measurable]
    rfl
  rw [heq, pairLaw, Measure.infinitePi_map_curry (fun (_ : Bool) (_ : Edge m) => F)]
  dsimp only [f]
  rw [Measure.infinitePi_map_eval_prod (P := fun _ : Bool => Measure.infinitePi (fun _ : Edge m => F))
      (by decide : false ≠ true), ← Infra.FPP.IsIIDWeights.eq_infinitePi hP]

/-- The distribution of `(X, X^G)` is unchanged when its components are exchanged. -/
theorem map_pair_resample_eq_swap {P : Measure (Config m)} {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] (hP : IsIIDWeights P F) (G : Set (Sym2 (Vertex m))) :
    (P.prod P).map (fun p : Config m × Config m => (p.1, resample G p.1 p.2)) =
      (P.prod P).map (fun p : Config m × Config m => (resample G p.1 p.2, p.1)) := by
  let τ : Config m × Config m → Config m × Config m := fun p =>
    (resample G p.1 p.2, resample G p.2 p.1)
  let f : Config m × Config m → Config m × Config m := fun p => (p.1, resample G p.1 p.2)
  have hτ := measurePreserving_exchange hP G
  have hf : Measurable f := measurable_fst.prodMk (measurable_resample G)
  have heq : f ∘ τ = fun p : Config m × Config m => (resample G p.1 p.2, p.1) := by
    funext p
    exact Prod.ext rfl (resample_resample G p.1 p.2)
  calc
    _ = (P.prod P).map (f ∘ τ) := by
      rw [← Measure.map_map hf hτ.measurable, hτ.map_eq]
    _ = _ := congrArg (fun g => (P.prod P).map g) heq

/-- Independent block replacement in the paired field space. -/
noncomputable def pairNew (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (o : ℕ → Fin m → ℤ) (i : ℕ) (g : Fin m → ℤ) (ω : PairWeights m) : Config m :=
  resample (block n w L t i (o i) g) (pairOld ω) (pairFresh ω)

/-- Independent resampling satisfies the complete exchangeable slab-replacement predicate. -/
theorem isSlabReplacement_pair {M : Model m} (hM : M.Standing) (n K w L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (o : ℕ → Fin m → ℤ) :
    IsSlabReplacement M (pairLaw M.F) n K w L t o pairOld (pairNew n w L t o) := by
  classical
  let : IsProbabilityMeasure M.F := hM.probF
  have hold : Measurable (pairOld (m := m)) := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  have hpair := measurePreserving_pairFields hM.iid
  refine ⟨by unfold pairLaw; infer_instance, hold, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairLaw]
    have hmap := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Bool × Edge m => M.F)
      (f := fun e : Edge m => (false, e)) (fun _ _ h => (Prod.mk.inj h).2)
    exact hmap.trans (Infra.FPP.IsIIDWeights.eq_infinitePi hM.iid).symm
  · intro i g
    exact (measurable_resample (block n w L t i (o i) g)).comp hpair.measurable
  · intro i g ω e he
    simp only [pairNew, resample, he, ite_false]
  · intro i g
    let G := block n w L t i (o i) g
    have h1 : (pairLaw (m := m) M.F).map (fun ω => (pairOld ω, pairNew n w L t o i g ω)) =
        (M.P.prod M.P).map (fun p : Config m × Config m => (p.1, resample G p.1 p.2)) := by
      rw [← hpair.map_eq, Measure.map_map
        (measurable_fst.prodMk (measurable_resample G)) hpair.measurable]
      rfl
    have h2 : (pairLaw (m := m) M.F).map (fun ω => (pairNew n w L t o i g ω, pairOld ω)) =
        (M.P.prod M.P).map (fun p : Config m × Config m => (resample G p.1 p.2, p.1)) := by
      rw [← hpair.map_eq, Measure.map_map
        ((measurable_resample G).prodMk measurable_fst) hpair.measurable]
      rfl
    rw [h1, h2]
    exact map_pair_resample_eq_swap hM.iid G
  · let E : Fin K → Set (Bool × Edge m) := fun i =>
      {be | be.2.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n)}
    have hblock : ∀ (i : Fin K) (g : Fin m → ℤ) (e : Edge m),
        e.1 ∈ block n w L t ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g →
          e.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n) := by
      intro i g e he
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using he.1
    let f : (i : Fin K) → (E i → ℝ≥0) →
        (({e : Edge m // e.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n)} → ℝ≥0) ×
          ((g : Fin m → ℤ) → {e : Edge m // e.1 ∈
            block n w L t ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g} → ℝ≥0)) :=
      fun i ξ => ((fun e => ξ ⟨(false, e.1), e.2⟩),
        fun g e => ξ ⟨(true, e.1), hblock i g e.1 e.2⟩)
    have hfm : ∀ i, Measurable (f i) := by
      intro i
      exact (measurable_pi_iff.mpr fun _ => measurable_pi_apply _).prodMk
        (measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
    have hE : Pairwise fun i j => Disjoint (E i) (E j) := by
      intro i j hij
      refine Set.disjoint_left.mpr fun be hi hj => ?_
      have hd := pairwise_disjoint_slabEdges (m := m) 0 n
        (show (i : ℕ) ≠ (j : ℕ) from fun h => hij (Fin.ext h))
      simp only [zero_add] at hd
      exact Set.disjoint_left.mp hd hi hj
    have hind := Infra.EfronStein.iIndepFun_comp_restrict_infinitePi
      (fun _ : Bool × Edge m => M.F) E hE f hfm
    unfold pairLaw
    convert hind using 1
    funext i ω
    apply Prod.ext
    · rfl
    · funext g e
      simp only [pairNew, resample, e.2, ite_true]
      rfl

end CurvatureVariance.Paper.Responses
