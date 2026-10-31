/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.FiniteInfluence

/-! # Passage time is unchanged by raising the density outside its influence ball -/

@[expose] public section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- A bounded upper extension of the density outside the deterministic
influence ball leaves the endpoint passage time unchanged. -/
theorem passage_eq_of_local_upper_extension {m : ℕ} (X : Setting m)
    {a b : ℝ} (ha : 0 < a) (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    (ω : X.Ω) (u v : Pt m) (σ : Pt m → ℝ)
    (hLower : ∀ x, X.ρ ω x ≤ σ x) (hUpper : ∀ x, σ x ≤ b)
    (hEq : ∀ x ∈ closedBall u ((b * dist u v + 1) / a), σ x = X.ρ ω x) :
    passageTime σ u v = X.passTime ω u v := by
  let ρ := fun x => ENNReal.ofReal (X.ρ ω x)
  let ρ' := fun x => ENNReal.ofReal (σ x)
  have hFinite : Measurability.passageTime ρ' u v ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top u v))
      (Measurability.passageTime_le_edist (fun x => ENNReal.ofReal_le_ofReal (hUpper x)) u v)
  have hMono : Measurability.passageTime ρ u v ≤ Measurability.passageTime ρ' u v := by
    apply iInf_mono
    intro γ
    apply iInf_mono
    intro _h0
    apply iInf_mono
    intro _h1
    exact γ.cost_mono fun x => ENNReal.ofReal_le_ofReal (hLower x)
  apply le_antisymm
  · have hSmall (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
        passageTime σ u v ≤ X.passTime ω u v + ε := by
      obtain ⟨γ, h0, h1, hNear⟩ := exists_nearoptimal_curve X ω u v hε
      have hNear' : (γ.cost ρ).toReal ≤
          X.passTime ω (γ.toFun 0) (γ.toFun 1) + ε := by
        simpa only [h0, h1] using hNear
      have hCost : γ.cost ρ' = γ.cost ρ := by
        apply lintegral_congr_ae
        filter_upwards [γ.ae_mem_Icc] with t ht
        apply congrArg ENNReal.ofReal
        apply hEq
        have hh := nearoptimal_mem_closedBall X ha hBounds ω γ hε1 hNear' ht
        simpa only [h0, h1] using hh
      have hPass := ENNReal.toReal_mono
        (hCost ▸ setting_curve_cost_ne_top X ω γ)
        (Measurability.passageTime_le_cost ρ' γ h0 h1)
      rw [hCost] at hPass
      exact hPass.trans hNear
    have hεLim : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply ge_of_tendsto (by simpa only [add_zero] using hεLim.const_add (X.passTime ω u v))
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
    exact hSmall (1 / n) (div_pos zero_lt_one hn0)
      ((div_le_iff₀ hn0).mpr (by simpa only [one_mul] using hnR))
  · exact ENNReal.toReal_mono hFinite hMono

end IsotropicVariance.Paper.Proofs.Classical
