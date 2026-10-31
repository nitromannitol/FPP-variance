/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.FiniteGridRepresentation

/-! # A finite coded passage time bounded even at off-support code values -/

@[expose] public section
open MeasureTheory Set Filter
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- Clipping the coded observable preserves its law and supplies deterministic
bounds at every code, while refresh differences remain an almost-sure claim. -/
theorem exists_bounded_grid_passTime_representation {m : ℕ} (X : Setting m)
    {a b : ℝ} (ha : 0 < a) (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    (u v : Pt m) :
    ∃ (n : ℕ) (_hn : 0 < n) (z : Fin n → Coord (Pt m) → ℤ), Function.Injective z ∧
      ∃ Φ : Fin n → X.Ω → ℕ → Bool,
        (∀ i, Measurable[X.info (gridCell (z i))] (Φ i)) ∧
        ∃ f : (Fin n → ℕ → Bool) → ℝ, Measurable f ∧
          (∀ x, 0 ≤ f x ∧ f x ≤ b * dist u v) ∧
          ((fun ω => f (fun i => Φ i ω)) =ᵐ[X.P] fun ω => X.passTime ω u v) ∧
          X.P.map (fun ω i => Φ i ω) = Measure.pi (fun i => X.P.map (Φ i)) := by
  obtain ⟨n, hn, z, hz, Φ, hΦ, f, hf, hRep, hLaw⟩ :=
    exists_finite_grid_passTime_representation X ha hBounds u v
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure X.P
  have hb : 0 ≤ b := ha.le.trans ((hBounds ω₀ u).1.trans (hBounds ω₀ u).2)
  have hL : 0 ≤ b * dist u v := mul_nonneg hb dist_nonneg
  let g := fun x => min (max (f x) 0) (b * dist u v)
  refine ⟨n, hn, z, hz, Φ, hΦ, g, (hf.max measurable_const).min measurable_const, ?_, ?_, hLaw⟩
  · intro x
    exact ⟨le_min (le_max_right _ _) hL, min_le_right _ _⟩
  · filter_upwards [hRep] with ω hω
    have hT0 : 0 ≤ X.passTime ω u v := ENNReal.toReal_nonneg
    have hT1 : X.passTime ω u v ≤ b * dist u v := (TimeConstant.passage_bounds ha.le (hBounds ω) u v).2
    simp only [g, hω, max_eq_left hT0, min_eq_left hT1]

end IsotropicVariance.Paper.Proofs.Classical
