/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Targets

/-!
# Contracts of the beginning of Section `sec:gain`: the comparison and the tubes

The statements of the beginning of Section `sec:gain` of the lattice paper.

* `FixedComparisonStatement` — equation `eq:fixedcomparison`: it uses Lemmas
  `lem:good` and `lem:slabs` and no induction hypothesis. The targets have `y ∈ 𝒟(ℓ)`, centred at
  `ℓ t₀`.
* `TubeStatement` — the containment of the cells near the slab geodesics in the tube of radius
  `R_i(j,k)` around the segment `[j, k]` (the text before Lemma `lem:blocks`), for slopes
  `|t| ≤ T`, with a constant that depends on `T`.

Every statement is uniform in the direction: its constants and thresholds come after a `Bounds`
record and before the models that fit it (`Model.Fits`), so they depend only on the law and the
bounds. `TubeStatement` is uniform already: its constant comes before the model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper

/-- **Equation `eq:fixedcomparison`**: for `ℓ = Kn ∈ [N/9, N]` with `n` an integer, `y ∈ 𝒟(ℓ)`,
`t = y/ℓ`, and `N` large depending on `K`, `E[(F − T(0,(ℓ,y)))²]^{1/2} ≤ C K log²N`, with `F` the
minimum of equation `eq:F` for `K` slabs of width `n` from `0` to `(ℓ, y)`.

Readings. `C` comes before `K`, as in the paper. Neither `F` nor `T` depends on `A`, so the bound
has no `A`. The proof uses Lemmas `lem:good` and `lem:slabs`, not the standing hypotheses
`eq:premise` and `eq:regime`, which is stronger. -/
def FixedComparisonStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
    eLpNorm (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P ≤
      ENNReal.ofReal (C * K * Real.log N ^ 2)

/-- **The tube property** (the text before Lemma `lem:blocks`: "We take `C` so large that every edge
of these geodesics lies in a cell with an index `z` such that `dist(z,[j,k]) ≤ R_i(j,k)`"): for
every bound `T ≥ 0` on the slopes there is a constant `C_d` (depending on `T` and `d`) such that,
with `R_i(j,k) = C_d(1 + R)` for the slab passage time `T^{(i)}` of slab `i` on
`I_{i−1}(j) × I_i(k)` (`s = n`, `w = ⌈(nQ_n)^{1/2}⌉`, slope `|t| ≤ T`), the cells within index
distance `R_i(j,k)` of the segment `[j, k]` contain those within `2` of every geodesic in slab `i`
from `I_{i−1}(j)` to `I_i(k)`.

This is stronger than the paper's statement, which has no margin `2`, and `C_d(1 + R)` is the
paper's `CR` up to a factor `2`, since `R ≥ 1`. The constant dominates the operator norm of the
shear `(q, h) ↦ h − tq` for `|t| ≤ T`, and the bounded midpoint and face errors; the uses take
`T = |t₀| + 1`, which contains the slopes of the targets for `N` large. A deterministic statement,
for every configuration. -/
def TubeStatement (m : ℕ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (M : Model m) (K : ℕ) (A : ℝ), 1 ≤ A →
  ∀ (ω : Config m) (n : ℕ), 1 ≤ n →
  ∀ (t : EuclideanSpace ℝ (Fin m)), ‖t‖ ≤ T → ∀ (i : ℕ), 1 ≤ i → ∀ j k : Fin m → ℤ,
  ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j, ∀ v ∈ rowCube n (wInt M K A n) t i k,
  ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
  ∀ e ∈ γ.edges, ∀ j' : Fin m → ℤ,
    ‖transversePoint (j' - fineIndex (wInt M K A n) t (edgeMid e))‖ ≤ 2 →
    j' ∈ tubeIndices j k (slabRadius M K A Cd ω n t i j k)

end CurvatureVariance.Paper.Contracts
