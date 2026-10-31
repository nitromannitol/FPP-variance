/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Targets

/-!
# The paper's internal objects: replacements, rewards and the averaged minimum of Section `sec:gain`

The objects that Section `sec:gain` takes from [AB26], with the weights in place of the noise:

* `Paper.IsSlabReplacement`: an exchangeable replacement of the blocks (the resampling of the text
  before Lemma `lem:blocks`). A probability space carries the old weights `old` (law `P`) and, for
  each block `(i, g)`, a configuration `new i g` that agrees with `old` off the block. The pair
  `(old, new i g)` is exchangeable, and the old weights of slab `i` together with the new weights of
  its blocks are independent over the slabs. Resampling from the original law and resampling
  conditionally on a function `σ_G` of the block's weights (the resampling of [AB26], defined before
  [AB26, Lemma 6.1]) are instances.
* `Paper.rewardSum`: the block sum `Q_n^{-2} ∑_G (sup_{I_{i−1}(j)×I_i(k)} (D_i^G − D_i)_+)²` (as in
  [AB26], before [AB26, Lemma 6.1]) for every pair, as a `[0, ∞]`-valued random variable;
  `Paper.reward`: the array `Y_i(j,k)`, the block sum on the retained pairs (`Paper.IsRetainedPair`)
  and `0` outside them (Section `sec:gain`).
* `Paper.transverseUnit`, `Paper.numTranslates`, `Paper.translatedMin`, `Paper.averagedMin`: the
  minima `F_v`, `0 ≤ v < ⌈K^{2/3}⌉`, with both endpoints (and all cubes) translated by `vLwe₂`, and
  their average `F̄` (as in [AB26], after [AB26, Lemma 6.2]; the text after Lemma `lem:labels`).
* `Paper.subcubeFace`: the points of the subcube of a block on a face of its slab (the set `Γ_G`
  of the text before Lemma `lem:labels`); `Paper.normSlabTime`: `(D_i(u,v) − P_t·(v−u))/Q_n`, the
  function `Φ` of the proof of Lemma `lem:labels`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper

variable {m : ℕ}

/-! ## Replacements and rewards (Section `sec:gain`) -/

/-- An exchangeable replacement of the blocks of the `K` slabs (the resampling of Section
`sec:gain`), for the blocks of slab `i` with offset `o i` (`Paper.block n w L t i (o i) g`). -/
structure IsSlabReplacement (M : Model m) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (n K w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o : ℕ → Fin m → ℤ) (old : Ω → Config m)
    (new : ℕ → (Fin m → ℤ) → Ω → Config m) : Prop where
  prob : IsProbabilityMeasure Pr
  measurable_old : Measurable old
  law_old : Pr.map old = M.P
  measurable_new : ∀ i g, Measurable (new i g)
  agree : ∀ i g ω (e : Edge m), e.1 ∉ block n w L t i (o i) g → new i g ω e = old ω e
  exchangeable : ∀ i g,
    Pr.map (fun ω => (old ω, new i g ω)) = Pr.map (fun ω => (new i g ω, old ω))
  indep_slabs : iIndepFun (fun (i : Fin K) (ω : Ω) =>
    ((fun e : {e : Edge m // e.1 ∈ slabEdges ((i : ℤ) * n) (((i : ℤ) + 1) * n)} => old ω e.1),
      fun (g : Fin m → ℤ)
          (e : {e : Edge m // e.1 ∈ block n w L t ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g}) =>
        new ((i : ℕ) + 1) g ω e.1)) Pr

/-- The block sum `Q_n^{-2} ∑_G (sup_{I_{i−1}(j)×I_i(k)} (D_i^G − D_i)_+)²` of a replacement (as in
[AB26], before [AB26, Lemma 6.1]), over the blocks `G = (i, g)` of slab `i`, the cubes those of
Section `sec:cubes` with `s = n` and `w = ⌈W_n⌉`, for every pair `(j, k)`; the reward array
`Paper.reward` is its restriction to the retained pairs. -/
noncomputable def rewardSum (M : Model m) (K : ℕ) (A : ℝ) {Ω : Type*} (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (old : Ω → Config m) (new : ℕ → (Fin m → ℤ) → Ω → Config m)
    (i : ℕ) (j k : Fin m → ℤ) (ω : Ω) : ℝ≥0∞ :=
  (ENNReal.ofReal (Q M K A n ^ 2))⁻¹ * ∑' g : Fin m → ℤ,
    (⨆ (u : Vertex m) (_ : u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j) (v : Vertex m)
        (_ : v ∈ rowCube n (wInt M K A n) t i k),
      ENNReal.ofReal (slabTimeReal (new i g ω) (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v -
        slabTimeReal (old ω) (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v)) ^ 2

open Classical in
/-- The reward array `Y_i(j,k)` (Section `sec:gain`): the block sum `rewardSum` on the retained
pairs `8w|k − j| ≤ n^{3/4+δ/100}` (`w = ⌈W_n⌉`), and `0` outside them, as in the paper; extended
nonnegative. -/
noncomputable def reward (M : Model m) (K : ℕ) (A : ℝ) {Ω : Type*} (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (old : Ω → Config m) (new : ℕ → (Fin m → ℤ) → Ω → Config m)
    (i : ℕ) (j k : Fin m → ℤ) (ω : Ω) : ℝ≥0∞ :=
  if IsRetainedPair M n (wInt M K A n) j k then rewardSum M K A n t old new i j k ω else 0

/-! ## The averaged minimum (the text after Lemma `lem:labels`) -/

/-- The first transverse unit vector `e₂ ∈ ℤ^{d-1}` (zero if `d = 1`). -/
def transverseUnit (m : ℕ) : Fin m → ℤ :=
  fun k => if (k : ℕ) = 0 then 1 else 0

/-- The number `⌈K^{2/3}⌉` of common translations (as in [AB26], after [AB26, Lemma 6.2]). -/
noncomputable def numTranslates (K : ℕ) : ℕ :=
  ⌈(K : ℝ) ^ ((2 : ℝ) / 3)⌉₊

/-- The minimum `F_τ` of equation `eq:F`, for `K` slabs of width `n` as in Section `sec:gain`, with
both endpoints translated by the transverse vector `τ`: from `(0, τ)` to `(ℓ, y + τ)`, slope
`t = y/ℓ`. -/
noncomputable def translatedMin (M : Model m) (ω : Config m) (n K ℓ : ℕ) (y τ : Fin m → ℤ) : ℝ :=
  (slabMin M ω n K (targetSlope ℓ y) (0, τ) ((ℓ : ℤ), y + τ)).toReal

/-- The average `F̄ = ⌈K^{2/3}⌉⁻¹ ∑_{0 ≤ v < ⌈K^{2/3}⌉} F_v` of the minima translated by `vLwe₂`,
`w = ⌈W_n⌉` (the text after Lemma `lem:labels`). -/
noncomputable def averagedMin (M : Model m) (K : ℕ) (A : ℝ) (L : ℕ) (ω : Config m) (n ℓ : ℕ)
    (y : Fin m → ℤ) : ℝ :=
  ((numTranslates K : ℕ) : ℝ)⁻¹ * ∑ v ∈ Finset.range (numTranslates K),
    translatedMin M ω n K ℓ y (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m)

/-! ## Subcubes of blocks (the set `Γ_G` of the text before Lemma `lem:labels`) -/

/-- The points `(x₁, z)` in the hyperplane `{x₁ = h}` of the subcube of the block `(i, g)` with
offset `o`: `z − x₁ t` lies in the cube of side `(L − 2⌈√L⌉) w` concentric with the block, i.e. in
`w (Lg + o + ⌈√L⌉ + [0, L − 2⌈√L⌉))` coordinatewise. -/
def subcubeFace (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ) (h : ℤ) :
    Set (Vertex m) :=
  {x | x.1 = h ∧ ∀ k,
    (w : ℝ) * ((L : ℝ) * g k + o k + ⌈Real.sqrt L⌉₊) ≤ (x.2 k : ℝ) - x.1 * t k ∧
      (x.2 k : ℝ) - x.1 * t k < (w : ℝ) * ((L : ℝ) * g k + o k + L - ⌈Real.sqrt L⌉₊)}

/-- The normalized slab passage time `(D_i(u,v) − P_t·(v − u))/Q_n` of slab `i` (the function `Φ`
of the proof of Lemma `lem:labels`). -/
noncomputable def normSlabTime (M : Model m) (K : ℕ) (A : ℝ) (ω : Config m) (n : ℕ) (P : Pt m)
    (i : ℕ) (u v : Vertex m) : ℝ :=
  (slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - inner ℝ P (point v - point u)) /
    Q M K A n

end CurvatureVariance.Paper
