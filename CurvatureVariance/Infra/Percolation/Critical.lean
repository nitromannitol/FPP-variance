/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Balls
public import CurvatureVariance.Infra.Percolation.Exploration

/-!
# Critical probabilities of Bernoulli bond percolation

For a graph `G` with root `o`, on the carrier of the definitions `CurvatureVariance.percolationProb`
and `CurvatureVariance.bondCriticalProb` (Mathlib's `setBernoulli`, the law of the random set `S` of
open edges, and `openGraph G S`):

* `percolationProb G o p = θ(p)`: the probability that the open cluster of `o` is infinite;
* `criticalProb G o = p_c = sup {p : θ(p) = 0}`;
* `armProb G o p n = P_p(o ↔ distance n)`, the one-arm probability;
* `phiCriticalProb G o = p̃_c = sup {p : φ_p(S) < 1 for some finite S ∋ o}`, the critical
  parameter of Duminil-Copin and Tassion.

The bridges `percolationProb_eq` and `armProb_eq` rewrite them as probabilities under
`percolation G p` on `G.edgeSet → Bool`, where the proofs live. With
`G = latticeGraph m` and `o = 0`, `percolationProb` and `criticalProb` are
`CurvatureVariance.percolationProb m` and `CurvatureVariance.bondCriticalProb m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

/-! ### The set carrier -/

section Carrier

variable {ι : Type*}

open Classical in
/-- Configurations and sets of open coordinates correspond measurably. -/
noncomputable def openSetEquiv : (ι → Bool) ≃ᵐ Set ι where
  toFun := openSet
  invFun S i := decide (i ∈ S)
  left_inv ω := by funext i; cases hω : ω i <;> simp [openSet, hω]
  right_inv S := by ext i; simp [openSet]
  measurable_toFun := measurable_openSet
  measurable_invFun := by
    classical
    refine measurable_pi_iff.2 fun i => ?_
    exact (Measurable.of_discrete (f := fun P : Prop => decide P)).comp (measurable_set_mem i)

/-- Probabilities of arbitrary events under `setBer(univ, p)`. -/
theorem setBernoulli_univ_apply_eq (p : I) (E : Set (Set ι)) :
    setBer((Set.univ : Set ι), p) E = bernoulliProduct ι p (openSet ⁻¹' E) := by
  rw [setBernoulli_univ_eq_map]
  exact (openSetEquiv (ι := ι)).map_apply E

end Carrier

variable {V : Type*} (G : SimpleGraph V) (o : V)

/-! ### Definitions -/

/-- **The percolation probability** `θ(p)`: under Bernoulli(`p`) bond percolation on `G` (the
random set of open edges, Mathlib's `setBernoulli`), the probability that the open cluster of `o`
is infinite. -/
noncomputable def percolationProb (p : I) : ℝ≥0∞ :=
  setBer((Set.univ : Set G.edgeSet), p) {S | {x | (openGraph G S).Reachable o x}.Infinite}

/-- **The critical probability** `p_c = sup {p : θ(p) = 0}` (Kesten's `p_H`). -/
noncomputable def criticalProb : ℝ :=
  sSup (Subtype.val '' {p : I | percolationProb G o p = 0})

/-- **The one-arm probability** `P_p(o ↔ distance n)`: `o` is joined by an open path to a vertex
at graph distance at least `n`. -/
noncomputable def armProb (p : I) (n : ℕ) : ℝ≥0∞ :=
  setBer((Set.univ : Set G.edgeSet), p) {S | ∃ x, n ≤ G.dist o x ∧ (openGraph G S).Reachable o x}

/-- **The critical parameter of Duminil-Copin and Tassion**,
`p̃_c = sup {p : φ_p(S) < 1 for some finite S ∋ o}`. -/
noncomputable def phiCriticalProb [DecidableEq V] [G.LocallyFinite] : ℝ :=
  sSup (Subtype.val '' {p : I | ∃ S : Finset V, o ∈ S ∧ phi G p o S < 1})

/-! ### Bridges to `percolation G p` -/

variable {G o}

theorem percolationProb_eq (p : I) :
    percolationProb G o p =
      percolation G p {ω | {x | OpenConnected G ω Set.univ o x}.Infinite} := by
  rw [percolationProb, setBernoulli_univ_apply_eq]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, reachable_openGraph_openSet_iff]

theorem armProb_eq (p : I) (n : ℕ) : armProb G o p n = percolation G p (armEvent G o n) := by
  rw [armProb, setBernoulli_univ_apply_eq]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, reachable_openGraph_openSet_iff, armEvent]

/-! ### The critical probabilities lie in `[0, 1]` -/

theorem sSup_image_val_nonneg (s : Set I) : 0 ≤ sSup (Subtype.val '' s) :=
  Real.sSup_nonneg fun _ ⟨p, _, hp⟩ => hp ▸ p.2.1

theorem sSup_image_val_le_one (s : Set I) : sSup (Subtype.val '' s) ≤ 1 :=
  Real.sSup_le (fun _ ⟨p, _, hp⟩ => hp ▸ p.2.2) zero_le_one

theorem bddAbove_image_val (s : Set I) : BddAbove (Subtype.val '' s) :=
  ⟨1, fun _ ⟨p, _, hp⟩ => hp ▸ p.2.2⟩

theorem le_sSup_image_val {s : Set I} {p : I} (hp : p ∈ s) : (p : ℝ) ≤ sSup (Subtype.val '' s) :=
  le_csSup (bddAbove_image_val s) ⟨p, hp, rfl⟩

variable (G o)

theorem criticalProb_mem_Icc : criticalProb G o ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sSup_image_val_nonneg _, sSup_image_val_le_one _⟩

theorem phiCriticalProb_mem_Icc [DecidableEq V] [G.LocallyFinite] :
    phiCriticalProb G o ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sSup_image_val_nonneg _, sSup_image_val_le_one _⟩

end CurvatureVariance.Infra.Percolation
