/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.CostPerturbation

/-! # The bounded local replacement estimate

The first and last visits bound the cost paid in a changed neighborhood by a
constant depending only on its diameter and the ellipticity bounds.
-/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- Changing the density in a bounded closed neighborhood changes passage time
by at most a diameter-dependent constant, using one old near-optimal curve. -/
theorem passage_change_le_of_visit {m : ℕ} (X : Setting m) {a b : ℝ} (ha : 0 < a)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b) (ω ω' : X.Ω)
    (γ : RectifiableCurve (Pt m)) {ε D : ℝ}
    (hNear : (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤
      X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε)
    {K : Set (Pt m)} (hK : IsClosed K) (hDiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hAgree : ∀ x ∉ K, X.ρ ω' x = X.ρ ω x)
    (hVisit : ∃ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ K) :
    X.passTime ω' (γ.toFun 0) (γ.toFun 1) - X.passTime ω (γ.toFun 0) (γ.toFun 1) ≤
      ε + (b / a) * (b * D + ε) := by
  have hb : 0 ≤ b := ha.le.trans ((hBounds ω (γ.toFun 0)).1.trans (hBounds ω (γ.toFun 0)).2)
  obtain ⟨s, t, hs, hst, ht, hKs, hKt, hVisits⟩ := exists_first_last_visit γ hK hVisit
  let δ := γ.subcurve s t hs hst ht
  let ρ := fun x => ENNReal.ofReal (X.ρ ω x)
  let ρ' := fun x => ENNReal.ofReal (X.ρ ω' x)
  have hChange := cost_perturb_le_interval γ ρ ρ'
    (fun x => ENNReal.ofReal_le_ofReal (hBounds ω' x).2)
    (fun x hx => congrArg ENNReal.ofReal (hAgree x hx)) hVisits
  rw [← γ.length_subcurve hs hst ht] at hChange
  have hFinite : ENNReal.ofReal b * δ.length ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top δ.length_ne_top
  have hReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨setting_curve_cost_ne_top X ω γ, hFinite⟩) hChange
  rw [ENNReal.toReal_add (setting_curve_cost_ne_top X ω γ) hFinite,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hb] at hReal
  have hSub := nearoptimal_subarc X ω γ hNear hs hst ht
  have hLow := ENNReal.toReal_mono (setting_curve_cost_ne_top X ω δ)
    (δ.mul_length_le_cost (fun x => ENNReal.ofReal_le_ofReal (hBounds ω x).1))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le] at hLow
  have hUp : X.passTime ω (γ.toFun s) (γ.toFun t) ≤ b * D :=
    (TimeConstant.passage_bounds ha.le (hBounds ω) _ _).2.trans
      (mul_le_mul_of_nonneg_left (hDiam _ hKs _ hKt) hb)
  have hLength : a * δ.length.toReal ≤ b * D + ε := by linarith only [hLow, hSub, hUp]
  have hScaled := mul_le_mul_of_nonneg_left hLength (div_nonneg hb ha.le)
  have hId : (b / a) * (a * δ.length.toReal) = b * δ.length.toReal := by field_simp
  rw [hId] at hScaled
  have hNew := passTime_le_curve_cost X ω' γ
  change (γ.cost ρ').toReal ≤ (γ.cost ρ).toReal + b * δ.length.toReal at hReal
  change (γ.cost ρ).toReal ≤ X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε at hNear
  change X.passTime ω' (γ.toFun 0) (γ.toFun 1) ≤ (γ.cost ρ').toReal at hNew
  linarith only [hReal, hScaled, hNear, hNew]

/-- A near-optimal curve avoiding the changed region pays only its original
approximation error. -/
theorem passage_change_le_of_avoids {m : ℕ} (X : Setting m) (ω ω' : X.Ω)
    (γ : RectifiableCurve (Pt m)) {ε : ℝ}
    (hNear : (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤
      X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε)
    {K : Set (Pt m)} (hAgree : ∀ x ∉ K, X.ρ ω' x = X.ρ ω x)
    (hAvoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∉ K) :
    X.passTime ω' (γ.toFun 0) (γ.toFun 1) - X.passTime ω (γ.toFun 0) (γ.toFun 1) ≤ ε := by
  have hEq := cost_eq_of_avoids γ (fun x => ENNReal.ofReal (X.ρ ω x))
    (fun x => ENNReal.ofReal (X.ρ ω' x)) (fun x hx => congrArg ENNReal.ofReal (hAgree x hx)) hAvoid
  have hNew := passTime_le_curve_cost X ω' γ
  rw [hEq] at hNew
  linarith only [hNew, hNear]

end IsotropicVariance.Paper.Proofs.Classical
