/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.ReplacementBound
public import IsotropicVariance.Paper.Proofs.Classical.CurveVisits
public import IsotropicVariance.Paper.Proofs.Classical.SupportedSquares

/-! # Summed local replacement energy along one near-optimal curve

The same old curve is used for every replacement. Only the neighborhoods it
visits pay a fixed cost; the approximation error on the other coordinates
vanishes when the curve error tends to zero.
-/

@[expose] public section
open MeasureTheory Set
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical

/-- The deterministic summed positive-square estimate, with its explicit
near-optimality error, before letting that error tend to zero. -/
theorem sum_changes_sq_le_curve {m : ℕ} (X : Setting m) {a b D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    {ι : Type*} [DecidableEq ι] (J : Finset ι) (K : ι → Set (Pt m)) (M : ℕ)
    (hClosed : ∀ i ∈ J, IsClosed (K i))
    (hDiam : ∀ i ∈ J, ∀ x ∈ K i, ∀ y ∈ K i, dist x y ≤ D)
    (hOverlap : ∀ x : Pt m, (J.filter fun i => ∃ y ∈ K i, dist y x ≤ 1).card ≤ M)
    (ω : X.Ω) (ω' : ι → X.Ω)
    (hAgree : ∀ i ∈ J, ∀ x ∉ K i, X.ρ (ω' i) x = X.ρ ω x)
    (γ : RectifiableCurve (Pt m)) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hNear : (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤
      X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε) :
    let B := (b / a) * (b * D + 1)
    (∑ i ∈ J, max (X.passTime (ω' i) (γ.toFun 0) (γ.toFun 1) -
        X.passTime ω (γ.toFun 0) (γ.toFun 1)) 0 ^ 2) ≤
      2 * B ^ 2 * M * (γ.length.toReal + 1) + 2 * ε ^ 2 * J.card := by
  dsimp only
  let B := (b / a) * (b * D + 1)
  have hb : 0 ≤ b := ha.le.trans ((hBounds ω (γ.toFun 0)).1.trans (hBounds ω (γ.toFun 0)).2)
  have hBa : 0 ≤ b / a := div_nonneg hb ha.le
  have hB : 0 ≤ B := mul_nonneg hBa (by nlinarith only [mul_nonneg hb hD])
  let V := J.filter fun i => ∃ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ K i
  let d := fun i => X.passTime (ω' i) (γ.toFun 0) (γ.toFun 1) -
    X.passTime ω (γ.toFun 0) (γ.toFun 1)
  have hV : V ⊆ J := Finset.filter_subset _ _
  have hBound (i : ι) (hi : i ∈ J) : d i ≤ (if i ∈ V then B else 0) + ε := by
    by_cases hv : i ∈ V
    · have hVisit := (Finset.mem_filter.mp hv).2
      have hh := passage_change_le_of_visit X ha hBounds ω (ω' i) γ hNear
        (hClosed i hi) (hDiam i hi) (hAgree i hi) hVisit
      have hError := mul_le_mul_of_nonneg_left (add_le_add_right hε1 (b * D)) hBa
      rw [ite_eq_left hv]
      change d i ≤ B + ε
      change d i ≤ ε + (b / a) * (b * D + ε) at hh
      linarith only [hh, hError]
    · have hAvoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∉ K i := by
        intro t ht hKt
        exact hv (Finset.mem_filter.mpr ⟨hi, t, ht, hKt⟩)
      simpa only [ite_eq_right hv, zero_add] using
        passage_change_le_of_avoids X ω (ω' i) γ hNear (hAgree i hi) hAvoid
  have hEnergy := sum_positive_sq_le_card J V hV d hB hε hBound
  have hCount : (V.card : ℝ) ≤ (M : ℝ) * (γ.length.toReal + 1) := by
    apply card_visited_le γ V K M
    · intro x
      apply (Finset.card_le_card ?_).trans (hOverlap x)
      intro i hi
      exact Finset.mem_filter.mpr ⟨hV (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hScaled := mul_le_mul_of_nonneg_left hCount (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg B))
  change (∑ i ∈ J, max (d i) 0 ^ 2) ≤ _
  change (∑ i ∈ J, max (d i) 0 ^ 2) ≤ 2 * B ^ 2 * V.card + 2 * ε ^ 2 * J.card at hEnergy
  simpa only [mul_assoc] using hEnergy.trans (add_le_add_left hScaled (2 * ε ^ 2 * J.card))

end IsotropicVariance.Paper.Proofs.Classical
