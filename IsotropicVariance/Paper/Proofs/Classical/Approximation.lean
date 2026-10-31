/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.NearOptimal

/-! # Arbitrarily near-optimal curves for literal passage times

No minimizing curve or measurable selector is assumed. The defining infimum
supplies a curve within any positive deterministic error.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- The rectifiable infimum has arbitrarily accurate competitors. -/
theorem exists_nearoptimal_curve {m : ℕ} (X : Setting m) (ω : X.Ω) (u v : Pt m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : RectifiableCurve (Pt m), γ.toFun 0 = u ∧ γ.toFun 1 = v ∧
      (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤ X.passTime ω u v + ε := by
  obtain ⟨_a, b, _ha, hab⟩ := X.bounds
  let ρ := fun x => ENNReal.ofReal (X.ρ ω x)
  let T := Measurability.passageTime ρ u v
  have hT : T ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top u v))
    (Measurability.passageTime_le_edist (fun x => ENNReal.ofReal_le_ofReal (hab ω x).2) u v)
  have hGap : T < ENNReal.ofReal (T.toReal + ε) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le, ENNReal.ofReal_toReal hT]
    exact ENNReal.lt_add_right hT (ENNReal.ofReal_ne_zero_iff.mpr hε)
  change (⨅ γ : RectifiableCurve (Pt m), ⨅ (_ : γ.toFun 0 = u),
    ⨅ (_ : γ.toFun 1 = v), γ.cost ρ) < _ at hGap
  simp only [iInf_lt_iff] at hGap
  obtain ⟨γ, h0, h1, hCost⟩ := hGap
  refine ⟨γ, h0, h1, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCost.le
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ T.toReal + ε)] at hh
  exact hh

/-- The endpoints of the first and last visits to a compact parameter set lie
in that set, and every visit lies between them. -/
theorem exists_first_last_visit {E : Type*} [MetricSpace E] (γ : RectifiableCurve E)
    {K : Set E} (hK : IsClosed K)
    (hVisit : ∃ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ K) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ γ.toFun a ∈ K ∧ γ.toFun b ∈ K ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ K → a ≤ t ∧ t ≤ b := by
  let S := {t ∈ Icc (0 : ℝ) 1 | γ.toFun t ∈ K}
  have hEq : S = Icc (0 : ℝ) 1 ∩ γ.clamped ⁻¹' K := by
    ext t
    constructor
    · rintro ⟨ht, hKt⟩
      refine ⟨ht, ?_⟩
      change γ.clamped t ∈ K
      rw [γ.clamped_eq ht]
      exact hKt
    · rintro ⟨ht, hKt⟩
      refine ⟨ht, ?_⟩
      change γ.clamped t ∈ K at hKt
      rwa [γ.clamped_eq ht] at hKt
  have hS : IsCompact S := by
    rw [hEq]
    exact isCompact_Icc.inter_right (hK.preimage γ.continuous_clamped)
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, hKt⟩ := hVisit
    exact ⟨t, ht, hKt⟩
  obtain ⟨a, ha, hMin⟩ := hS.exists_isLeast hSne
  obtain ⟨b, hb, hMax⟩ := hS.exists_isGreatest hSne
  exact ⟨a, b, ha.1.1, hMin hb, hb.1.2, ha.2, hb.2,
    fun t ht hKt => ⟨hMin ⟨ht, hKt⟩, hMax ⟨ht, hKt⟩⟩⟩

end IsotropicVariance.Paper.Proofs.Classical
