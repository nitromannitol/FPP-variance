/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Choosing the two-parameter residual modulus

A uniform eventual estimate for every positive tolerance, together with a coarse bound for
all admissible parameters, gives a single `G(ε,L)` with exactly the quantifier order in
`Contracts.ResidualStatement`. This numerical lemma adds no probabilistic premise: its input
relation is the uniform bound already proved for each tolerance.
-/

@[expose] public section

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- Combine small estimates and a coarse bound into a single uniformly small majorant.
`H ε L c` may include all remaining slab and scale quantifiers of the energy estimate. -/
theorem exists_uniform_small_majorant (H : ℝ → ℕ → ℝ → Prop)
    (hmono : ∀ ε L a b, a ≤ b → H ε L a → H ε L b)
    (hcoarse : ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ L : ℕ, 16 ≤ L → H ε L C)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ L : ℕ, L₀ ≤ L → 16 ≤ L → H ε L η) :
    ∃ G : ℝ → ℕ → ℝ,
      (∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℕ,
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ L : ℕ, L₀ ≤ L → G ε L ≤ η) ∧
      ∀ ε : ℝ, 0 < ε → ∀ L : ℕ, 16 ≤ L → H ε L (G ε L) := by
  obtain ⟨C,hC,hcoarse⟩ := hcoarse
  let S : ℝ → ℕ → Set ℝ := fun ε L => {c | 0 ≤ c ∧ (0 < ε → 16 ≤ L → H ε L c)}
  have hne (ε : ℝ) (L : ℕ) : (S ε L).Nonempty := ⟨C,hC,fun hε hL => hcoarse ε hε L hL⟩
  have hbelow (ε : ℝ) (L : ℕ) : BddBelow (S ε L) := ⟨0, fun _ h => h.1⟩
  let G : ℝ → ℕ → ℝ := fun ε L => sInf (S ε L) + ε
  refine ⟨G, ?_, ?_⟩
  · intro η hη
    obtain ⟨ε₁,hε₁,L₁,h₁⟩ := hsmall (η/2) (by linarith)
    refine ⟨min ε₁ (η/2), lt_min hε₁ (by linarith), max L₁ 16, ?_⟩
    intro ε hε hε' L hL
    have hL₁ : L₁ ≤ L := (le_max_left _ _).trans hL
    have hL16 : 16 ≤ L := (le_max_right _ _).trans hL
    have hmem : η/2 ∈ S ε L :=
      ⟨by linarith, fun _ _ => h₁ ε hε (hε'.trans (min_le_left _ _)) L hL₁ hL16⟩
    have hi := csInf_le (hbelow ε L) hmem
    have he := hε'.trans (min_le_right _ _)
    dsimp [G]
    linarith
  · intro ε hε L hL
    obtain ⟨c,hc,hc'⟩ := exists_lt_of_csInf_lt (hne ε L)
      (show sInf (S ε L) < G ε L by dsimp [G]; linarith)
    exact hmono ε L c (G ε L) hc'.le (hc.2 hε hL)

end IsotropicVariance.Paper.Proofs.LabelResidual
