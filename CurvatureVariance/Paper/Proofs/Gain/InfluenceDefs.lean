/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.Gain.TubeGeodesics

/-!
# Tubes meeting a block

These are the objects of the proof of the `L¹` influence bound, the second bound of Lemma
`lem:fewtranslates`: as in the proof of [AB26, Lemma 6.4], with the cube indices of the minimizing
chains, resampling `G` changes `F_v` only if, for the old or the new weights, the cells within
distance `R_i(J_{i−1}, J_i)` of the segment `[J_{i−1}, J_i]` meet `G`.

* `Gain.TubeBound M Cd T`: the tube property of `Contracts.TubeStatement` for the model `M`,
  the constant `Cd` and slopes `|t| ≤ T` (stated before Lemma `lem:blocks`; the uses take
  `T = |t₀| + 1`).
* `Gain.TubeMeets`: for the weights `z`, the tube of slab `i + 1` of the tuple `Y` meets the
  index box `blockIndices L o g` of a block. The tube is the set of fine-cube indices within
  `slabRadius` of the segment `[J_i, J_{i+1}]`.
* `Gain.AllTubesMeet`: this holds for every minimizing tuple of `F` with the weights `z`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper

variable {m : ℕ}

/-- The tube property (`Contracts.TubeStatement`, stated before Lemma `lem:blocks`) for the model
`M`, the constant `Cd` and slopes `|t| ≤ T`. -/
def TubeBound (M : Model m) (Cd T : ℝ) : Prop :=
  ∀ (K : ℕ) (A : ℝ), 1 ≤ A → ∀ (ω : Config m) (n : ℕ), 1 ≤ n →
  ∀ (t : EuclideanSpace ℝ (Fin m)), ‖t‖ ≤ T → ∀ (i : ℕ), 1 ≤ i → ∀ j k : Fin m → ℤ,
  ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j, ∀ v ∈ rowCube n (wInt M K A n) t i k,
  ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
  ∀ e ∈ γ.edges, ∀ j' : Fin m → ℤ,
    ‖transversePoint (j' - fineIndex (wInt M K A n) t (edgeMid e))‖ ≤ 2 →
    j' ∈ tubeIndices j k (slabRadius M K A Cd ω n t i j k)

/-- `Contracts.TubeStatement` gives, for every slope bound `T ≥ 0`, a constant `Cd ≥ 0` with the
tube property for every model. -/
theorem exists_tubeBound (h : Contracts.TubeStatement m) {T : ℝ} (hT0 : 0 ≤ T) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ M : Model m, TubeBound M Cd T := by
  obtain ⟨Cd, hCd, hT⟩ := h T hT0
  exact ⟨Cd, hCd, fun M => hT M⟩

/-- For the weights `z`, the tube of slab `i + 1` of the tuple `Y` (the fine-cube indices within
`R_{i+1}(J_i, J_{i+1})` of the segment `[J_i, J_{i+1}]`, `J = tupleIndex`, `w = ⌈W_n⌉`,
`t = y/ℓ`) meets the index box `blockIndices L o g` of a block. -/
def TubeMeets (M : Model m) (K : ℕ) (A Cd : ℝ) (n ℓ : ℕ) (y : Fin m → ℤ) (L : ℕ) (i : Fin K)
    (o g : Fin m → ℤ) (z : Config m) (Y : Fin (K + 1) → Fin m → ℤ) : Prop :=
  ∃ j' ∈ Gain.blockIndices L o g,
    j' ∈ tubeIndices (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
      (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ)
      (slabRadius M K A Cd z n (targetSlope ℓ y) ((i : ℕ) + 1)
        (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
        (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ))

/-- For the weights `z`, the tube of slab `i + 1` of every minimizing tuple of `F` (from `0` to
`(ℓ, y)`) meets the index box `blockIndices L o g`. -/
def AllTubesMeet (M : Model m) (K : ℕ) (A Cd : ℝ) (n ℓ : ℕ) (y : Fin m → ℤ) (L : ℕ) (i : Fin K)
    (o g : Fin m → ℤ) (z : Config m) : Prop :=
  ∀ Y : Fin (K + 1) → Fin m → ℤ, IsMinTuple M z n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y →
    TubeMeets M K A Cd n ℓ y L i o g z Y

end CurvatureVariance.Paper.Gain
