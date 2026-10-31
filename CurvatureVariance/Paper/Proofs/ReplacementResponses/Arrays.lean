/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.RRReplacement
import CurvatureVariance.Paper.Proofs.Responses.SlabArrays

/-!
# Independence of the replacement reward arrays

The reward of a slab is a measurable function of its old weights and the new weights inside
its blocks. Off a replaced block the new weights equal the old weights. Thus precisely the
independence assumption in `IsSlabReplacement.indep_slabs` gives independence of the arrays.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.ReplacementResponses

variable {m : ℕ}

open Classical in
/-- Zero extension of weights on a set of edges. -/
noncomputable def extendWeights (E : Set (Edge m)) (ξ : E → ℝ≥0) : Config m :=
  fun e => if h : e ∈ E then ξ ⟨e, h⟩ else 0

theorem measurable_extendWeights (E : Set (Edge m)) : Measurable (extendWeights E) := by
  classical
  refine measurable_pi_iff.mpr fun e => ?_
  by_cases he : e ∈ E
  · simpa only [extendWeights, he, dite_true] using measurable_pi_apply (⟨e, he⟩ : E)
  · simpa only [extendWeights, he, dite_false] using
      (measurable_const : Measurable (fun _ : E → ℝ≥0 => (0 : ℝ≥0)))

/-- Retaining pairs preserves measurability of the block sum. -/
theorem measurable_reward (M : Model m) (K : ℕ) (A : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (t : EuclideanSpace ℝ (Fin m)) {old : Ω → Config m}
    {new : ℕ → (Fin m → ℤ) → Ω → Config m} (hold : Measurable old)
    (hnew : ∀ i g, Measurable (new i g)) (i : ℕ) (j k : Fin m → ℤ) :
    Measurable (reward M K A n t old new i j k) := by
  classical
  change Measurable (fun ω => reward M K A n t old new i j k ω)
  by_cases h : IsRetainedPair M n (wInt M K A n) j k
  · simpa only [reward, h, ite_true] using Gain.measurable_rewardSum M K A n t hold hnew i j k
  · simpa only [reward, h, ite_false] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))

/-- Only the old and new weights within the indicated slab affect its reward. -/
theorem reward_congr (M : Model m) (K : ℕ) (A : ℝ) (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) {Ω Ω' : Type*} (old : Ω → Config m)
    (new : ℕ → (Fin m → ℤ) → Ω → Config m) (old' : Ω' → Config m)
    (new' : ℕ → (Fin m → ℤ) → Ω' → Config m) (i : ℕ) (j k : Fin m → ℤ)
    (ω : Ω) (ω' : Ω')
    (h0 : ∀ e : Edge m, e.1 ∈ slabEdges (((i : ℤ) - 1) * n) ((i : ℤ) * n) →
      old ω e = old' ω' e)
    (h1 : ∀ g (e : Edge m), e.1 ∈ slabEdges (((i : ℤ) - 1) * n) ((i : ℤ) * n) →
      new i g ω e = new' i g ω' e) :
    reward M K A n t old new i j k ω = reward M K A n t old' new' i j k ω' := by
  have h0' := fun u v => Responses.restrictedTime_congr _ u v h0
  have h1' := fun g u v => Responses.restrictedTime_congr _ u v (h1 g)
  simp only [reward, rewardSum, slabTimeReal, slabTime, h0', h1']

/-- The whole reward arrays of different slabs are independent under an arbitrary replacement. -/
theorem iIndepFun_rewardArrays {M : Model m} {Ω : Type*} [MeasurableSpace Ω]
    {Pr : Measure Ω} {n K L : ℕ} {A : ℝ} {t : EuclideanSpace ℝ (Fin m)}
    {o : ℕ → Fin m → ℤ} {old : Ω → Config m}
    {new : ℕ → (Fin m → ℤ) → Ω → Config m}
    (hR : IsSlabReplacement M Pr n K (wInt M K A n) L t o old new) :
    iIndepFun (fun (i : Fin K) ω => fun j k : Fin m → ℤ =>
      reward M K A n t old new ((i : ℕ) + 1) j k ω) Pr := by
  classical
  let E : Fin K → Set (Edge m) := fun i =>
    {e | e.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n)}
  let B : Fin K → (Fin m → ℤ) → Set (Edge m) := fun i g =>
    {e | e.1 ∈ block n (wInt M K A n) L t ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g}
  let V := fun i : Fin K => (E i → ℝ≥0) × ((g : Fin m → ℤ) → B i g → ℝ≥0)
  let c0 : (i : Fin K) → V i → Config m := fun i ξ => extendWeights (E i) ξ.1
  let cg : (i : Fin K) → (Fin m → ℤ) → V i → Config m := fun i g ξ e =>
    if h : e ∈ B i g then ξ.2 g ⟨e, h⟩ else c0 i ξ e
  have hc0 : ∀ i, Measurable (c0 i) := fun i =>
    (measurable_extendWeights (E i)).comp measurable_fst
  have hcg : ∀ i g, Measurable (cg i g) := by
    intro i g
    refine measurable_pi_iff.mpr fun e => ?_
    by_cases he : e ∈ B i g
    · simpa only [cg, he, dite_true, Function.comp_def] using
        (measurable_pi_apply (⟨e, he⟩ : B i g)).comp ((measurable_pi_apply g).comp measurable_snd)
    · simpa only [cg, he, dite_false, Function.comp_def] using (measurable_pi_apply e).comp (hc0 i)
  let Φ := fun (i : Fin K) (ξ : V i) => fun j k : Fin m → ℤ =>
    reward M K A n t (c0 i) (fun _ g => cg i g) ((i : ℕ) + 1) j k ξ
  have hΦ : ∀ i, Measurable (Φ i) := fun i => measurable_pi_iff.mpr fun j =>
    measurable_pi_iff.mpr fun k => measurable_reward M K A n t (hc0 i)
      (fun _ g => hcg i g) ((i : ℕ) + 1) j k
  have hind := hR.indep_slabs.comp Φ hΦ
  convert hind using 1
  funext i ω j k
  apply reward_congr
  · intro e he
    have he' : e ∈ E i := by
      simpa only [E, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using he
    change old ω e = extendWeights (E i) (fun e => old ω e.1) e
    simp only [extendWeights, he', dite_true]
  · intro g e he
    by_cases hb : e ∈ B i g
    · simp only [cg, hb, dite_true]
    · have he' : e ∈ E i := by
        simpa only [E, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using he
      change new ((i : ℕ) + 1) g ω e =
        (if h : e ∈ B i g then new ((i : ℕ) + 1) g ω e else
          extendWeights (E i) (fun e => old ω e.1) e)
      simp only [hb, dite_false, extendWeights, he', dite_true]
      exact hR.agree _ g ω e hb

end CurvatureVariance.Paper.ReplacementResponses
