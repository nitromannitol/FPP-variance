/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.ReplacementBound

/-! # Uniform bounded changes without a chosen minimizing curve -/

@[expose] public section
open Set Filter
open scoped Topology
namespace IsotropicVariance.Paper.Proofs.Classical

/-- Removing the approximation error gives a uniform one-sided change bound. -/
theorem passage_change_le {m : ℕ} (X : Setting m) {a b D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b) (ω ω' : X.Ω)
    {K : Set (Pt m)} (hK : IsClosed K) (hDiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hAgree : ∀ x ∉ K, X.ρ ω' x = X.ρ ω x) (u v : Pt m) :
    X.passTime ω' u v - X.passTime ω u v ≤ (b / a) * (b * D + 1) := by
  let B := (b / a) * (b * D + 1)
  have hb : 0 ≤ b := ha.le.trans ((hBounds ω u).1.trans (hBounds ω u).2)
  have hB : 0 ≤ B := mul_nonneg (div_nonneg hb ha.le) (by positivity)
  have hSmall (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      X.passTime ω' u v - X.passTime ω u v ≤ ε + B := by
    obtain ⟨γ, h0, h1, hNear⟩ := exists_nearoptimal_curve X ω u v hε
    have hNear' : (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤
        X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε := by simpa only [h0, h1] using hNear
    by_cases hv : ∃ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ K
    · have hh := passage_change_le_of_visit X ha hBounds ω ω' γ hNear' hK hDiam hAgree hv
      simp only [h0, h1] at hh
      have hmul := mul_le_mul_of_nonneg_left
        (add_le_add_right hε1 (b * D)) (div_nonneg hb ha.le)
      exact hh.trans (add_le_add_right hmul ε)
    · have hAvoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∉ K := by
        intro t ht hmem
        exact hv ⟨t, ht, hmem⟩
      have hh := passage_change_le_of_avoids X ω ω' γ hNear' hAgree hAvoid
      simp only [h0, h1] at hh
      exact hh.trans (le_add_of_nonneg_right hB)
  have hεLim : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply ge_of_tendsto (by simpa only [zero_add] using hεLim.add_const B)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
  exact hSmall (1 / n) (div_pos zero_lt_one hn0)
    ((div_le_iff₀ hn0).mpr (by simpa only [one_mul] using hnR))

/-- The same comparison in both directions gives an absolute bounded change. -/
theorem abs_passage_change_le {m : ℕ} (X : Setting m) {a b D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b) (ω ω' : X.Ω)
    {K : Set (Pt m)} (hK : IsClosed K) (hDiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hAgree : ∀ x ∉ K, X.ρ ω' x = X.ρ ω x) (u v : Pt m) :
    |X.passTime ω' u v - X.passTime ω u v| ≤ (b / a) * (b * D + 1) := by
  rw [abs_le]
  have h1 := passage_change_le X ha hD hBounds ω ω' hK hDiam hAgree u v
  have h2 := passage_change_le X ha hD hBounds ω' ω hK hDiam (fun x hx => (hAgree x hx).symm) u v
  constructor
  · linarith only [h2]
  · exact h1

end IsotropicVariance.Paper.Proofs.Classical
