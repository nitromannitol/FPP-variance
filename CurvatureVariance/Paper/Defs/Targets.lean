/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes

/-!
# The paper's internal objects: the targets and the minimum `F` of Section `sec:gain`

The beginning of Section `sec:gain`:

* `Paper.IsTarget`: a target `(ℓ, y)` with `y ∈ 𝒟(ℓ)` and `N/9 ≤ ℓ = Kn ≤ N`.
* `Paper.targetSlope`: `t = y/ℓ`.
* `Paper.targetMin`: the minimum `F` of equation `eq:F` over `K` slabs of width `n` from `0` to
  `(ℓ, y)` (`Paper.slabMin`), as a real number.
* `Paper.tupleIndex`: the cube indices `J_i` of the points of a chain, for the cubes `I_i(·)` of
  Section `sec:cubes` with `s = n` and `w = ⌈W_n⌉`.
* `Paper.indexJumpSq`: `|J_i − J_{i−1}|²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper

variable {m : ℕ}

/-- A target of Section `sec:gain`: `(ℓ, y)` with `y ∈ 𝒟(ℓ)` and `N/9 ≤ ℓ = Kn ≤ N`. -/
def IsTarget (M : Model m) (K N n ℓ : ℕ) (y : Fin m → ℤ) : Prop :=
  ℓ = K * n ∧ (N : ℝ) / 9 ≤ ℓ ∧ ℓ ≤ N ∧ y ∈ premiseDomain M ℓ

/-- The slope `t = y/ℓ` of a target (Section `sec:gain`). -/
noncomputable def targetSlope (ℓ : ℕ) (y : Fin m → ℤ) : EuclideanSpace ℝ (Fin m) :=
  (ℓ : ℝ)⁻¹ • transversePoint y

/-- The minimum `F` for the target `(ℓ, y)`, `ℓ = Kn`: the minimum of
equation `eq:F` over `K` slabs of width `n` from `0` to `(ℓ, y)` with slope `t = y/ℓ`, as a real
number. -/
noncomputable def targetMin (M : Model m) (ω : Config m) (n K ℓ : ℕ) (y : Fin m → ℤ) : ℝ :=
  (slabMin M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y)).toReal

/-- The cube index `J_i` of the `i`-th point of a chain, for the cubes `I_i(·)` of Section
`sec:cubes` with `s = n` and side `w` (Section `sec:gain`). -/
noncomputable def tupleIndex (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) {K : ℕ}
    (y : Fin (K + 1) → Fin m → ℤ) (i : Fin (K + 1)) : Fin m → ℤ :=
  rowIndex n w t i (y i)

/-- The squared index increment `|J_i − J_{i−1}|²` of a tuple across slab `i + 1`. -/
noncomputable def indexJumpSq (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) {K : ℕ}
    (y : Fin (K + 1) → Fin m → ℤ) (i : Fin K) : ℝ :=
  ‖transversePoint (tupleIndex n w t y i.succ - tupleIndex n w t y i.castSucc)‖ ^ 2

end CurvatureVariance.Paper
