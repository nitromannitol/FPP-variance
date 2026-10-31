/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Chain
import IsotropicVariance.Paper.Proofs.Classical.NearOptimal

/-! # Costs of ordered subarcs and near-optimality -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
open IsotropicVariance.Paper.Proofs.Classical (setting_curve_cost_ne_top)
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {m : ℕ} (X : Setting m) (ω : X.Ω)

/-- The real cost of a parameter subinterval of a literal rectifiable curve. -/
noncomputable def pieceCost (γ : IsotropicVariance.RectifiableCurve (Pt m)) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : ℝ :=
  ((γ.subcurve a b ha hab hb).cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal

lemma pieceCost_add (γ : IsotropicVariance.RectifiableCurve (Pt m)) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    pieceCost X ω γ a b ha hab (hbc.trans hc) +
      pieceCost X ω γ b c (ha.trans hab) hbc hc =
        pieceCost X ω γ a c ha (hab.trans hbc) hc := by
  have h := γ.cost_subcurve_add (ρ := fun x => ENNReal.ofReal (X.ρ ω x))
    ((X.measurable_ρ.comp measurable_prodMk_left).ennreal_ofReal) ha hab hbc hc
  have hh := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (setting_curve_cost_ne_top X ω _) (setting_curve_cost_ne_top X ω _)] at hh
  exact hh

lemma pieceCost_full (γ : IsotropicVariance.RectifiableCurve (Pt m)) :
    pieceCost X ω γ 0 1 le_rfl zero_le_one le_rfl =
      (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal := by
  unfold pieceCost
  have h := IsotropicVariance.RectifiableCurve.cost_congr_curve
    (γ := γ.subcurve 0 1 le_rfl zero_le_one le_rfl) (δ := γ)
    (fun t _ => by simp [IsotropicVariance.RectifiableCurve.subcurve, Infra.Curves.subParam])
    (fun x => ENNReal.ofReal (X.ρ ω x))
  exact congrArg ENNReal.toReal h

lemma passTime_le_pieceCost (γ : IsotropicVariance.RectifiableCurve (Pt m)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    X.passTime ω (γ.toFun a) (γ.toFun b) ≤ pieceCost X ω γ a b ha hab hb := by
  have h := Infra.Measurability.passageTime_le_cost
    (fun x => ENNReal.ofReal (X.ρ ω x)) (γ.subcurve a b ha hab hb)
    (γ.subcurve_start ha hab hb) (γ.subcurve_end ha hab hb)
  have hh := ENNReal.toReal_mono (setting_curve_cost_ne_top X ω _) h
  simpa only [Setting.passTime, ← Infra.TimeConstant.passage_eq_surface,
    Infra.TimeConstant.passage, pieceCost] using hh

/-- Every subarc of a 1-optimal curve is 1-optimal, in its real-cost form. -/
theorem pieceCost_le_passTime_add_one (γ : IsotropicVariance.RectifiableCurve (Pt m))
    {u v : Pt m} (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    pieceCost X ω γ a b ha hab hb ≤ X.passTime ω (γ.toFun a) (γ.toFun b) + 1 := by
  let δ := γ
  have hfull : (δ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤ X.passTime ω u v + 1 := by
    change (γ.cost (fun x => ENNReal.ofReal (X.ρ ω x))).toReal ≤ _
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hγ.2.2.2
    have heq : restrictedPassageTime (X.ρ ω) univ u v = X.passTime ω u v := by
      simp [restrictedPassageTime, Setting.passTime, IsotropicVariance.passageTime]
    rw [heq] at h
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ X.passTime ω u v + 1 from
      add_nonneg ENNReal.toReal_nonneg zero_le_one)] using h
  have hsplit1 := pieceCost_add X ω δ (a := 0) (b := a) (c := b) le_rfl ha hab hb
  have hsplit2 := pieceCost_add X ω δ (a := 0) (b := b) (c := 1) le_rfl (ha.trans hab) hb le_rfl
  rw [pieceCost_full] at hsplit2
  have htri1 := Infra.TimeConstant.setting_passTime_triangle X ω u (γ.toFun a) v
  have htri2 := Infra.TimeConstant.setting_passTime_triangle X ω (γ.toFun a) (γ.toFun b) v
  have hleft := passTime_le_pieceCost X ω δ le_rfl ha (hab.trans hb)
  have hright := passTime_le_pieceCost X ω δ (ha.trans hab) hb le_rfl
  change X.passTime ω (γ.toFun 0) (γ.toFun a) ≤ _ at hleft
  change X.passTime ω (γ.toFun b) (γ.toFun 1) ≤ _ at hright
  rw [hγ.1] at hleft
  rw [hγ.2.1] at hright
  linarith

/-- Ordered points of a 1-optimal curve have passage-time triangle defect at most one. -/
theorem ordered_passTime_defect (γ : IsotropicVariance.RectifiableCurve (Pt m))
    {u v : Pt m} (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) :
    X.passTime ω (γ.toFun a) (γ.toFun b) + X.passTime ω (γ.toFun b) (γ.toFun c) ≤
      X.passTime ω (γ.toFun a) (γ.toFun c) + 1 := by
  let δ := γ
  have h1 := passTime_le_pieceCost X ω δ ha hab (hbc.trans hc)
  have h2 := passTime_le_pieceCost X ω δ (ha.trans hab) hbc hc
  have h3 := pieceCost_add X ω δ ha hab hbc hc
  have h4 := pieceCost_le_passTime_add_one X ω γ hγ ha (hab.trans hbc) hc
  change X.passTime ω (γ.toFun a) (γ.toFun b) ≤ _ at h1
  change X.passTime ω (γ.toFun b) (γ.toFun c) ≤ _ at h2
  linarith

end IsotropicVariance.Paper.Proofs.SlabComparison
