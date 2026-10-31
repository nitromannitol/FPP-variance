/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Selection.Lexicographic

/-! # Selection for costs defined only on the compact set -/

@[expose] public section
open Set MeasureTheory
namespace IsotropicVariance.Infra.Selection

/-- The subtype form requires the cost only on the compact constraint set. The last clause
is the first-differing-coordinate characterization of the lexicographically least tie. -/
theorem exists_measurable_lexMinimizer {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (K : Set (Fin k → ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (F : Ω → K → ℝ) (hc : ∀ ω, Continuous (F ω))
    (hm : ∀ x, Measurable (fun ω => F ω x)) :
    ∃ s : Ω → K, Measurable s ∧ ∀ ω,
      (∀ y : K, F ω (s ω) ≤ F ω y) ∧
      ∀ y : K, F ω y = F ω (s ω) → ∀ i : Fin k,
        (∀ j : Fin k, j < i → y.1 j = (s ω).1 j) → (s ω).1 i ≤ y.1 i := by
  classical
  let G : Ω → (Fin k → ℝ) → ℝ := fun ω x => if hx : x ∈ K then F ω ⟨x, hx⟩ else 0
  have hG (ω : Ω) (x : K) : G ω x = F ω x := by simp only [G, dite_eq_left x.2]
  have hcG (ω : Ω) : ContinuousOn (G ω) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa only [domRestrict_def, hG] using hc ω
  have hmG (x : Fin k → ℝ) (hx : x ∈ K) : Measurable (fun ω => G ω x) := by
    simpa only [G, dite_eq_left hx] using hm ⟨x, hx⟩
  let s : Ω → K := fun ω => ⟨lexMinimizer K hK hne G hcG ω,
    (isLexMinimizer_lexMinimizer K hK hne G hcG ω).1⟩
  refine ⟨s, (measurable_lexMinimizer K hK hne G hcG hmG).subtype_mk, ?_⟩
  intro ω
  have H := isLexMinimizer_lexMinimizer K hK hne G hcG ω
  have hs : (s ω).1 = lexMinimizer K hK hne G hcG ω := rfl
  have Hmin (y : K) : F ω (s ω) ≤ F ω y := by
    simpa only [← hs, hG] using H.2.1 y.1 y.2
  refine ⟨Hmin, ?_⟩
  intro y heq i hp
  apply H.2.2 y.1 y.2 _ i hp
  simpa only [← hs, hG] using heq

end IsotropicVariance.Infra.Selection
