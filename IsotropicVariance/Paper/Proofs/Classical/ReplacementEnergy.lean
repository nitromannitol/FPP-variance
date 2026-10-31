/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.CurveEnergy

/-! # The deterministic summed replacement-energy inequality

Let the old curve's near-optimality error tend to zero for a fixed finite
family. Its cardinality therefore disappears from the final bound. This is
the deterministic positive-square estimate used in the BLM application.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- Summed positive replacement squares are bounded linearly in endpoint
distance whenever changed neighborhoods have bounded diameter and overlap. -/
theorem sum_changes_sq_le {m : ℕ} (X : Setting m) {a b D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    {ι : Type*} [DecidableEq ι] (J : Finset ι) (K : ι → Set (Pt m)) (M : ℕ)
    (hClosed : ∀ i ∈ J, IsClosed (K i))
    (hDiam : ∀ i ∈ J, ∀ x ∈ K i, ∀ y ∈ K i, dist x y ≤ D)
    (hOverlap : ∀ x : Pt m, (J.filter fun i => ∃ y ∈ K i, dist y x ≤ 1).card ≤ M)
    (ω : X.Ω) (ω' : ι → X.Ω)
    (hAgree : ∀ i ∈ J, ∀ x ∉ K i, X.ρ (ω' i) x = X.ρ ω x) (u v : Pt m) :
    let B := (b / a) * (b * D + 1)
    (∑ i ∈ J, max (X.passTime (ω' i) u v - X.passTime ω u v) 0 ^ 2) ≤
      2 * B ^ 2 * M * (b * dist u v / a + 1) := by
  let B := (b / a) * (b * D + 1)
  let Q := 2 * B ^ 2 * M
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) (Nat.cast_nonneg M)
  let S := ∑ i ∈ J, max (X.passTime (ω' i) u v - X.passTime ω u v) 0 ^ 2
  have hSmall (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      S ≤ Q * ((b * dist u v + ε) / a + 1) + 2 * ε ^ 2 * J.card := by
    obtain ⟨γ, h0, h1, hNear⟩ := exists_nearoptimal_curve X ω u v hε
    have hNear' : (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤
        X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε := by simpa only [h0, h1] using hNear
    have hEnergy := sum_changes_sq_le_curve X ha hD hBounds J K M hClosed hDiam hOverlap
      ω ω' hAgree γ hε.le hε1 hNear'
    have hLow := ENNReal.toReal_mono (setting_curve_cost_ne_top X ω γ)
      (γ.mul_length_le_cost (fun x => ENNReal.ofReal_le_ofReal (hBounds ω x).1))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le] at hLow
    have hUp : X.passTime ω u v ≤ b * dist u v := (TimeConstant.passage_bounds ha.le (hBounds ω) u v).2
    have hLength : a * γ.length.toReal ≤ b * dist u v + ε := by linarith only [hLow, hNear, hUp]
    have hLength' : γ.length.toReal ≤ (b * dist u v + ε) / a :=
      (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hLength)
    have hScaled := mul_le_mul_of_nonneg_left (add_le_add_left hLength' 1) hQ
    simp only [h0, h1] at hEnergy
    change S ≤ Q * (γ.length.toReal + 1) + 2 * ε ^ 2 * J.card at hEnergy
    exact hEnergy.trans (add_le_add_left hScaled (2 * ε ^ 2 * J.card))
  have hεLim : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hLim : Tendsto (fun n : ℕ => Q * ((b * dist u v + 1 / n) / a + 1) + 2 * (1 / n) ^ 2 * J.card)
      atTop (𝓝 (Q * (b * dist u v / a + 1))) := by
    have hh := (((hεLim.const_add (b * dist u v)).div_const a).add_const 1).const_mul Q
    have hh' := hh.add ((hεLim.pow 2).const_mul (2 * (J.card : ℝ)))
    simp only [add_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hh'
    convert hh' using 1
    funext n
    ring
  apply ge_of_tendsto hLim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
  exact hSmall (1 / n) (div_pos zero_lt_one hn0)
    ((div_le_iff₀ hn0).mpr (by simpa only [one_mul] using hnR))

end IsotropicVariance.Paper.Proofs.Classical
