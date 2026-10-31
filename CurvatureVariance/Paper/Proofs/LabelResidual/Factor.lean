/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.ReplacementResponses.Arrays

/-!
# The reward of a slab is a function of the slab's offset and weights

In the proof of Lemma `lem:residual`, for the replacement
`new i g x = resample (block n w L t i (o i) g) x.1 x.2` on pairs of configurations, the reward
array of slab `i` reads only the old and new weights of the edges of slab `i`
(`ReplacementResponses.reward_congr`) and the offset `o i` of that slab. Hence it is a function
`rewardFactor … i (o i)` of the offset and of the pair of weight families on the slab
(`slabPair n i x`), measurable jointly in a countable offset and the weights
(`measurable_rewardFactor`). This is the form in which the offset mixture makes the reward arrays
independent over the slabs.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.ReplacementResponses

variable {m : ℕ}

/-- The edges of slab `i`, the slab `[(i − 1)n, in]`. -/
def slabEdgeSet (m n i : ℕ) : Set (Edge m) :=
  {e | e.1 ∈ slabEdges (((i : ℤ) - 1) * n) ((i : ℤ) * n)}

/-- The old and new weights on the edges of slab `i`. -/
def slabPair (n i : ℕ) (x : Config m × Config m) :
    (slabEdgeSet m n i → ℝ≥0) × (slabEdgeSet m n i → ℝ≥0) :=
  (fun e => x.1 e.1, fun e => x.2 e.1)

theorem measurable_slabPair (n i : ℕ) : Measurable (slabPair (m := m) n i) :=
  (measurable_pi_iff.2 fun e => (measurable_pi_apply e.1).comp measurable_fst).prodMk
    (measurable_pi_iff.2 fun e => (measurable_pi_apply e.1).comp measurable_snd)

/-- The replacement of the blocks of the slabs with offsets `o` on pairs of configurations. -/
noncomputable def pairNew (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o : ℕ → Fin m → ℤ)
    (i : ℕ) (g : Fin m → ℤ) (x : Config m × Config m) : Config m :=
  resample (block n w L t i (o i) g) x.1 x.2

/-- The reward of slab `i` with the offset `s` of its blocks, as a function of the old and new
weights on the slab. -/
noncomputable def rewardFactor (M : Model m) (K : ℕ) (A : ℝ) (n L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (s : Fin m → ℤ)
    (p : (slabEdgeSet m n i → ℝ≥0) × (slabEdgeSet m n i → ℝ≥0)) (j k : Fin m → ℤ) : ℝ≥0∞ :=
  reward M K A n t (fun p => extendWeights (slabEdgeSet m n i) p.1)
    (fun _ g p => resample (block n (wInt M K A n) L t i s g)
      (extendWeights (slabEdgeSet m n i) p.1) (extendWeights (slabEdgeSet m n i) p.2)) i j k p

/-- **The reward of slab `i` reads only the slab's offset and weights.** -/
theorem reward_pairNew_eq (M : Model m) (K : ℕ) (A : ℝ) (n L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (o : ℕ → Fin m → ℤ) (i : ℕ) (j k : Fin m → ℤ)
    (x : Config m × Config m) :
    reward M K A n t Prod.fst (pairNew n (wInt M K A n) L t o) i j k x =
      rewardFactor M K A n L t i (o i) (slabPair n i x) j k := by
  classical
  unfold rewardFactor
  apply reward_congr
  · intro e he
    have he' : e ∈ slabEdgeSet m n i := he
    simp only [extendWeights, he', dite_true, slabPair]
  · intro g e he
    have he' : e ∈ slabEdgeSet m n i := he
    simp only [pairNew, resample, extendWeights, he', dite_true, slabPair]

/-- The reward of a slab is measurable jointly in a countable offset and the weights on the
slab. -/
theorem measurable_rewardFactor (M : Model m) (K : ℕ) (A : ℝ) (n L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (off : S → Fin m → ℤ) (j k : Fin m → ℤ) :
    Measurable fun q : S × ((slabEdgeSet m n i → ℝ≥0) × (slabEdgeSet m n i → ℝ≥0)) =>
      rewardFactor M K A n L t i (off q.1) q.2 j k := by
  refine measurable_from_prod_countable_right fun s => ?_
  have hold : Measurable fun p : (slabEdgeSet m n i → ℝ≥0) × (slabEdgeSet m n i → ℝ≥0) =>
      extendWeights (slabEdgeSet m n i) p.1 :=
    (measurable_extendWeights _).comp measurable_fst
  have hnew : ∀ (i' : ℕ) (g : Fin m → ℤ), Measurable fun p :
      (slabEdgeSet m n i → ℝ≥0) × (slabEdgeSet m n i → ℝ≥0) =>
      resample (block n (wInt M K A n) L t i (off s) g)
        (extendWeights (slabEdgeSet m n i) p.1) (extendWeights (slabEdgeSet m n i) p.2) := by
    intro i' g
    classical
    refine measurable_pi_iff.2 fun e => ?_
    by_cases he : e.1 ∈ block n (wInt M K A n) L t i (off s) g
    · simp only [resample, he, ite_true]
      exact (measurable_pi_apply e).comp ((measurable_extendWeights _).comp measurable_snd)
    · simp only [resample, he, ite_false]
      exact (measurable_pi_apply e).comp hold
  exact measurable_reward M K A n t hold hnew i j k

end CurvatureVariance.Paper.Gain.LabelResidual
