/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.TimeConstant.Limit

/-! # Normalization of the paper's setting by its time constant

Positive division preserves the density conditions in `Setting.withDensity`.
The normalized setting has limiting mean slope one and its variance is the
original variance divided by the square of the time constant.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
universe u
namespace IsotropicVariance.Infra.TimeConstant
open Paper

/-- Divide the density in a setting by a positive deterministic scalar. All
locality, measurability, bounds and covariance conditions are proved here. -/
noncomputable def rescale {m : ℕ} (X : Setting.{u} m) (k : ℝ) (hk : 0 < k) : Setting.{u} m :=
  X.withDensity (fun ω x => X.ρ ω x / k) (X.measurable_ρ.div_const k)
    (fun x => (X.determined x).div_const k)
    (fun U hU => (X.determined_joint U hU).div_const k)
    (by
      obtain ⟨a, b, ha, hab⟩ := X.bounds
      exact ⟨a / k, b / k, div_pos ha hk, fun ω x =>
        ⟨div_le_div_of_nonneg_right (hab ω x).1 hk.le,
          div_le_div_of_nonneg_right (hab ω x).2 hk.le⟩⟩)
    (by
      intro g hg ω x
      rw [X.covariant g hg ω x])

/-- The literal passage time scales with the density. -/
theorem rescale_passTime {m : ℕ} (X : Setting.{u} m) {k : ℝ} (hk : 0 < k)
    (ω : X.Ω) (u v : Pt m) :
    (rescale X k hk).passTime ω u v = X.passTime ω u v / k := by
  change IsotropicVariance.passageTime (fun x => X.ρ ω x / k) u v =
    IsotropicVariance.passageTime (X.ρ ω) u v / k
  simp only [← passage_eq_surface]
  exact passage_div _ hk u v

/-- The directional random passage time scales with the density. -/
theorem rescale_TRV {m : ℕ} (X : Setting.{u} m) {k : ℝ} (hk : 0 < k) (t : ℝ) (ω : X.Ω) :
    (rescale X k hk).TRV t ω = X.TRV t ω / k := rescale_passTime X hk ω 0 (t • e₁)

/-- Directional means scale with the density. -/
theorem rescale_mean {m : ℕ} (X : Setting.{u} m) {k : ℝ} (hk : 0 < k) (t : ℝ) :
    (rescale X k hk).mean t = X.mean t / k := by
  change (∫ ω, (rescale X k hk).TRV t ω ∂X.P) = X.mean t / k
  simp_rw [rescale_TRV]
  simp only [div_eq_mul_inv, integral_mul_const]
  rfl

/-- Dividing by a positive limiting slope makes the setting normalized. -/
theorem isNormalized_rescale {m : ℕ} (X : Setting.{u} m) {k : ℝ} (hk : 0 < k)
    (hLim : Tendsto (fun t : ℝ => X.mean t / t) atTop (𝓝 k)) :
    (rescale X k hk).IsNormalized := by
  have hh := hLim.div_const k
  rw [div_self hk.ne'] at hh
  change Tendsto (fun t : ℝ => (rescale X k hk).mean t / t) atTop (𝓝 1)
  convert hh using 1
  funext t
  rw [rescale_mean]
  ring

/-- Normalize the density by the positive continuum time constant. -/
noncomputable def normalized {m : ℕ} (X : Setting.{u} m) : Setting.{u} m :=
  rescale X (timeConstant X) (timeConstant_pos X)

/-- The normalized setting satisfies the paper's exact normalization predicate. -/
theorem normalized_isNormalized {m : ℕ} (X : Setting.{u} m) : (normalized X).IsNormalized :=
  isNormalized_rescale X (timeConstant_pos X) (tendsto_mean_div_timeConstant X)

end IsotropicVariance.Infra.TimeConstant
