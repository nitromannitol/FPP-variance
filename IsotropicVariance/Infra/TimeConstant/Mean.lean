/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.TimeConstant.SettingBounds
public import IsotropicVariance.Infra.TimeConstant.Fekete

/-! # Stationarity, subadditivity and the continuum time constant over `Setting`

Only the translation part of the measure-preserving proper-motion action is
used. No stationarity or comparison of passage times is assumed separately.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace IsotropicVariance.Infra.TimeConstant
open Paper

/-- Translations are proper rigid motions. -/
theorem isProperRigidMotion_translation {m : ℕ} (a : Pt m) :
    IsProperRigidMotion (AffineIsometryEquiv.constVAdd ℝ (Pt m) a) := by
  simp [IsProperRigidMotion, AffineIsometryEquiv.constVAdd, AffineEquiv.constVAdd]

/-- The passage triangle inequality for the literal real definition of the passage time. -/
theorem setting_passTime_triangle {m : ℕ} (X : Setting m) (ω : X.Ω) (u v w : Pt m) :
    X.passTime ω u w ≤ X.passTime ω u v + X.passTime ω v w := by
  obtain ⟨a, b, ha, hab⟩ := X.bounds
  have hb : 0 ≤ b := ha.le.trans ((hab ω u).1.trans (hab ω u).2)
  let B : ℝ≥0 := ⟨b, hb⟩
  have hBound : ∀ x, ENNReal.ofReal (X.ρ ω x) ≤ (B : ℝ≥0∞) := by
    intro x
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hab ω x).2
  have hFin (x y : Pt m) := Measurability.passageTime_ne_top hBound x y
  have hm : Measurable (fun x => ENNReal.ofReal (X.ρ ω x)) :=
    (X.measurable_ρ.comp measurable_prodMk_left).ennreal_ofReal
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hFin u v, hFin v w⟩)
    (Measurability.passageTime_triangle hm u v w)
  rw [ENNReal.toReal_add (hFin u v) (hFin v w)] at hh
  simpa only [Setting.passTime, ← passage_eq_surface, passage] using hh

/-- Pathwise covariance of the paper passage time. -/
theorem setting_passTime_covariant {m : ℕ} (X : Setting m)
    (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (hg : IsProperRigidMotion g) (ω : X.Ω) (u v : Pt m) :
    X.passTime (X.act g ω) (g u) (g v) = X.passTime ω u v := by
  simp only [Setting.passTime, ← passage_eq_surface]
  change passage (X.ρ (X.act g ω)) (g.toIsometryEquiv u) (g.toIsometryEquiv v) = _
  rw [passage_comp_isometry]
  congr 1
  funext x
  exact X.covariant g hg ω x

/-- Translating endpoints does not change the mean passage time. -/
theorem integral_passTime_translation {m : ℕ} (X : Setting m) (a u v : Pt m) :
    (∫ ω, X.passTime ω (a + u) (a + v) ∂X.P) = ∫ ω, X.passTime ω u v ∂X.P := by
  let g := AffineIsometryEquiv.constVAdd ℝ (Pt m) a
  have hg := isProperRigidMotion_translation a
  have hmp := X.measurePreserving_act g hg
  have hm : AEStronglyMeasurable (fun ω => X.passTime ω (a + u) (a + v))
      (Measure.map (X.act g) X.P) := by
    rw [hmp.map_eq]
    exact aestronglyMeasurable_passTime X (a + u) (a + v)
  have hh := integral_map hmp.aemeasurable hm
  rw [hmp.map_eq] at hh
  rw [hh]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => setting_passTime_covariant X g hg ω u v

/-- Every directional passage random variable is integrable. -/
theorem integrable_TRV {m : ℕ} (X : Setting m) (t : ℝ) : Integrable (X.TRV t) X.P :=
  integrable_passTime X 0 (t • e₁)

/-- The directional distance in the definition of the mean is the absolute
value of the parameter. -/
theorem dist_smul_e₁ {m : ℕ} (s t : ℝ) : dist (s • (e₁ : Pt m)) (t • e₁) = |s - t| := by
  rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, Paper.norm_e₁, mul_one]

/-- `T_s` is square integrable. -/
theorem memLp_TRV {m : ℕ} (X : Setting m) (s : ℝ) : MemLp (X.TRV s) 2 X.P := by
  obtain ⟨a, b, ha, hab⟩ := setting_passTime_bounds X
  have hd : dist (0 : Pt m) (s • e₁) = |s| := by
    simpa only [zero_smul, zero_sub, abs_neg] using dist_smul_e₁ (m := m) 0 s
  refine MemLp.of_bound (integrable_TRV X s).aestronglyMeasurable (|b| * |s|)
    (Eventually.of_forall fun ω => ?_)
  have h := hab ω 0 (s • e₁)
  rw [hd] at h
  have h0 : 0 ≤ X.TRV s ω := (mul_nonneg ha.le (abs_nonneg s)).trans h.1
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h.2.trans (mul_le_mul_of_nonneg_right (le_abs_self b) (abs_nonneg s))

/-- A mean passage time is subadditive on the real line, hence on `[0,∞)`. -/
theorem mean_subadditive {m : ℕ} (X : Setting m) (s t : ℝ) :
    X.mean (s + t) ≤ X.mean s + X.mean t := by
  have hh := integral_mono (integrable_TRV X (s + t))
    ((integrable_TRV X s).add (integrable_passTime X (s • e₁) ((s + t) • e₁)))
    (fun ω => setting_passTime_triangle X ω 0 (s • e₁) ((s + t) • e₁))
  dsimp only [Pi.add_apply] at hh
  rw [integral_add (integrable_TRV X s) (integrable_passTime X (s • e₁) ((s + t) • e₁))] at hh
  have heq : (∫ ω, X.passTime ω (s • e₁) ((s + t) • e₁) ∂X.P) = X.mean t := by
    have hs := integral_passTime_translation X (s • e₁) 0 (t • e₁)
    simpa only [add_zero, add_smul, Setting.mean, Setting.TRV] using hs
  rw [heq] at hh
  exact hh

/-- The mean has the same deterministic linear bounds as the density. -/
theorem mean_bounds {m : ℕ} (X : Setting m) :
    ∃ a b : ℝ, 0 < a ∧ ∀ t, 0 ≤ t → a * t ≤ X.mean t ∧ X.mean t ≤ b * t := by
  obtain ⟨a, b, ha, hab⟩ := setting_passTime_bounds X
  refine ⟨a, b, ha, fun t ht => ?_⟩
  have hd : dist (0 : Pt m) (t • e₁) = t := by
    simpa only [zero_smul, zero_sub, abs_neg, abs_of_nonneg ht] using dist_smul_e₁ (m := m) 0 t
  constructor
  · have hh := integral_mono (integrable_const (a * t)) (integrable_TRV X t)
      (fun ω => by simpa only [hd, Setting.TRV] using (hab ω 0 (t • e₁)).1)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, Setting.mean] using hh
  · have hh := integral_mono (integrable_TRV X t) (integrable_const (b * t))
      (fun ω => by simpa only [hd, Setting.TRV] using (hab ω 0 (t • e₁)).2)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, Setting.mean] using hh

/-- The directional mean is globally Lipschitz. -/
theorem mean_lipschitz {m : ℕ} (X : Setting m) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ s t : ℝ, |X.mean s - X.mean t| ≤ b * |s - t| := by
  obtain ⟨b, hb, hLip⟩ := setting_passTime_endpoint_bound X
  refine ⟨b, hb, fun s t => ?_⟩
  rw [Setting.mean, Setting.mean, ← integral_sub (integrable_TRV X s) (integrable_TRV X t)]
  calc
    _ ≤ ∫ ω, |X.TRV s ω - X.TRV t ω| ∂X.P := abs_integral_le_integral_abs
    _ ≤ ∫ _ω, b * |s - t| ∂X.P := integral_mono
      ((integrable_TRV X s).sub (integrable_TRV X t)).abs (integrable_const _) (fun ω => by
        simpa only [Setting.TRV, dist_self, zero_add, dist_smul_e₁] using
          hLip ω 0 (s • e₁) 0 (t • e₁))
    _ = _ := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

end IsotropicVariance.Infra.TimeConstant
