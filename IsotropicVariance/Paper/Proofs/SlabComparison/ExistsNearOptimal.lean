/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.NearOptimal
public import IsotropicVariance.Paper.Proofs.Profiles.Basic
import IsotropicVariance.Paper.Proofs.Classical.NearOptimal

/-! # Existence of the near-optimal curves used in the slab proof -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {m : ℕ}

/-- The bounded setting admits a 1-optimal `RectifiableCurve` between any two endpoints. -/
theorem exists_oneOptimal (X : Setting m) (ω : X.Ω) (u v : Pt m) :
    ∃ γ : IsotropicVariance.RectifiableCurve (Pt m), IsOneOptimal (X.ρ ω) univ u v γ := by
  let ρ := fun x => ENNReal.ofReal (X.ρ ω x)
  let T := Infra.Measurability.passageTime ρ u v
  have hfin : T ≠ ⊤ := by
    obtain ⟨a, b, ha, hab⟩ := X.bounds
    have hb : 0 ≤ b := ha.le.trans ((hab ω u).1.trans (hab ω u).2)
    let B : NNReal := ⟨b, hb⟩
    exact Infra.Measurability.passageTime_ne_top
      (b := B) (fun x => by
        change ENNReal.ofReal (X.ρ ω x) ≤ (B : ENNReal)
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (hab ω x).2) u v
  have hlt : T < ENNReal.ofReal (T.toReal + 1) := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hfin]
    exact lt_add_one _
  change (⨅ (γ : IsotropicVariance.RectifiableCurve (Pt m)) (_ : γ.toFun 0 = u)
    (_ : γ.toFun 1 = v), γ.cost ρ) < ENNReal.ofReal (T.toReal + 1) at hlt
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
  obtain ⟨h0, hγ⟩ := iInf_lt_iff.mp hγ
  obtain ⟨h1, hγ⟩ := iInf_lt_iff.mp hγ
  refine ⟨γ, h0, h1, fun _ _ => mem_univ _, ?_⟩
  have heq : restrictedPassageTime (X.ρ ω) univ u v = T.toReal := by
    simp [restrictedPassageTime, T, Infra.Measurability.passageTime, ρ]
  rw [heq]
  exact hγ.le

/-- Borel densities give a Lipschitz 1-optimal curve; its reversal is 1-optimal too. This
allows the directional estimate to be applied from either endpoint without a second choice. -/
theorem exists_oneOptimal_lipschitz (X : Setting m) (ω : X.Ω) (u v : Pt m) :
    ∃ γ : Infra.Curves.LipCurve (Pt m) u v,
      IsOneOptimal (X.ρ ω) univ u v γ.toRectifiable ∧
      IsOneOptimal (X.ρ ω) univ v u γ.reverse.toRectifiable := by
  obtain ⟨δ, hδ⟩ := exists_oneOptimal X ω u v
  let ρ := fun x => ENNReal.ofReal (X.ρ ω x)
  have hm : Measurable ρ := (X.measurable_ρ.comp measurable_prodMk_left).ennreal_ofReal
  have hfin := Classical.setting_curve_cost_ne_top X ω δ
  have hlt : Infra.Measurability.passageTime ρ u v <
      ENNReal.ofReal (X.passTime ω u v + 1) := by
    have hT : Infra.Measurability.passageTime ρ u v ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (Infra.Measurability.passageTime_le_cost ρ δ hδ.1 hδ.2.1)
    rw [ENNReal.lt_ofReal_iff_toReal_lt hT]
    change X.passTime ω u v < X.passTime ω u v + 1
    linarith
  rw [Infra.Measurability.passageTime_eq_lipschitz hm] at hlt
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
  have heq (a b : Pt m) : restrictedPassageTime (X.ρ ω) univ a b = X.passTime ω a b := by
    simp [restrictedPassageTime, Setting.passTime, IsotropicVariance.passageTime]
  have hcost : γ.reverse.toRectifiable.cost ρ = γ.toRectifiable.cost ρ := by
    have hm' : Measurable fun x => Real.toNNReal (X.ρ ω x) :=
      measurable_real_toNNReal.comp (X.measurable_ρ.comp measurable_prodMk_left)
    change γ.reverse.toRectifiable.cost (fun x => (Real.toNNReal (X.ρ ω x) : ℝ≥0∞)) =
      γ.toRectifiable.cost (fun x => (Real.toNNReal (X.ρ ω x) : ℝ≥0∞))
    rw [γ.reverse.toRectifiable_cost hm', γ.toRectifiable_cost hm', γ.cost_reverse]
  refine ⟨γ, ⟨γ.map_zero, γ.map_one, fun _ _ => mem_univ _, ?_⟩,
    ⟨γ.reverse.map_zero, γ.reverse.map_one, fun _ _ => mem_univ _, ?_⟩⟩
  · rw [heq]
    exact hγ.le
  · rw [heq, Profiles.passTime_comm (X := X) ω v u]
    exact hcost.trans_le hγ.le

end IsotropicVariance.Paper.Proofs.SlabComparison
