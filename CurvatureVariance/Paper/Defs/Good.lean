/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs

/-!
# The three properties of Lemma `lem:good`, at one configuration

* `Paper.IsGood M C c N S ω`: the properties (1)–(3) of Lemma `lem:good` hold at the configuration
  `ω`, on the box `[−2N², 2N²]^d`.

The events `𝒢_N(S)` of the lemma are in `Contracts.GoodStatement`. Lemmas `lem:cone` and `lem:slabs`
are deterministic given `IsGood`, as the paper's proofs are: they use only (1)–(3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper

variable {m : ℕ}

/-- **The properties (1)–(3) of Lemma `lem:good`** at one configuration `ω`, at the scale `S`, with
the constants `C` and `c`: for all lattice points `x, y` of the box `[−2N², 2N²]^d`,

1. `|T(x,y) − μ(y−x)| ≤ C(S|y−x|^{1/2} + S²)`;
2. `T_P(x,y) ≤ C(|y−x| + S²)` for every slab `P = [p,q] × ℝ^{d−1}` with `x, y ∈ P`;
3. every self-avoiding path from `x` with `k ≥ CS²` edges has passage time at least `ck`.

Readings. A slab has `q − p ≥ 2` (the beginning of Section `sec:prelim`), and
`x, y ∈ [p,q] × ℝ^{d−1}` is `p ≤ x₁, y₁ ≤ q`. The passage time `T_P` is `slabTime`, with values in
`[0, ∞]`. The other endpoint of the path in (3) is any vertex, in the box or not, as in the paper.
-/
structure IsGood (M : Model m) (C c : ℝ) (N : ℕ) (S : ℝ) (ω : Config m) : Prop where
  /-- Lemma `lem:good` (1). -/
  passageTime_sub : ∀ x y : Vertex m, InBox (2 * (N : ℝ) ^ 2) x → InBox (2 * (N : ℝ) ^ 2) y →
    |passageTimeReal ω x y - M.μ.1 (point y - point x)| ≤
      C * (S * Real.sqrt ‖point y - point x‖ + S ^ 2)
  /-- Lemma `lem:good` (2). -/
  slabTime_le : ∀ x y : Vertex m, InBox (2 * (N : ℝ) ^ 2) x → InBox (2 * (N : ℝ) ^ 2) y →
    ∀ p q : ℤ, p + 2 ≤ q → p ≤ x.1 → x.1 ≤ q → p ≤ y.1 → y.1 ≤ q →
      slabTime ω p q x y ≤ ENNReal.ofReal (C * (‖point y - point x‖ + S ^ 2))
  /-- Lemma `lem:good` (3). -/
  le_walkCost : ∀ x : Vertex m, InBox (2 * (N : ℝ) ^ 2) x →
    ∀ (y : Vertex m) (γ : (latticeGraph m).Walk x y), γ.IsPath → C * S ^ 2 ≤ γ.length →
      c * γ.length ≤ (walkCost ω γ : ℝ)

end CurvatureVariance.Paper
