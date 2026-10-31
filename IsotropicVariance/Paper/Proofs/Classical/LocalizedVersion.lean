/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.LocalExtension
public import IsotropicVariance.Infra.Measurability.SlabVersion

/-! # A passage-time version determined by a bounded noise region

Countable factorization and passage-time measurable versions are reused from
`IsotropicVariance.Infra.Measurability.SlabVersion`; localization uses a deterministic ball.
-/

@[expose] public section
open MeasureTheory Set Metric Filter
open scoped Classical ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.Slab

/-- Localizing the density to a ball gives joint measurability for the noise
in the ball enlarged by two. -/
theorem measurable_localizedDensity {m : ℕ} (X : Setting m) (u : Pt m) (R b : ℝ) :
    Measurable[(X.info (ball u (R + 2))).prod inferInstance]
      (fun p : X.Ω × Pt m => if p.2 ∈ closedBall u R then X.ρ p.1 p.2 else b) := by
  have hAP : ∀ x ∈ closedBall u R, closedBall x 1 ⊆ ball u (R + 2) := by
    intro x hx y hy
    have hd := dist_triangle y x u
    change dist x u ≤ R at hx
    change dist y x ≤ 1 at hy
    change dist y u < R + 2
    linarith only [hd, hx, hy]
  exact @measurable_dite_mem X.Ω (Pt m) _ (X.info (ball u (R + 2))) _
    (closedBall u R) _ measurableSet_closedBall hAP
    (fun p => X.ρ p.1 p.2) (X.determined_joint _ isOpen_ball) b

/-- The endpoint passage time has a version measurable for the information in
a deterministic bounded ball. No global information is included in the code. -/
theorem exists_localized_passTime_version {m : ℕ} (X : Setting m)
    {a b : ℝ} (ha : 0 < a) (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    (u v : Pt m) :
    let R := (b * dist u v + 1) / a
    ∃ V : X.Ω → ℝ, Measurable[X.info (ball u (R + 2))] V ∧
      V =ᵐ[X.P] fun ω => X.passTime ω u v := by
  let R := (b * dist u v + 1) / a
  let σ : X.Ω → Pt m → ℝ := fun ω x => if x ∈ closedBall u R then X.ρ ω x else b
  obtain ⟨Φ, hΦ, h, hh, hfh⟩ := exists_factor_of_measurable_prod
    (measurable_localizedDensity X u R b)
  have hΦm : Measurable Φ := hΦ.mono (X.info_le _) le_rfl
  let ρ' : (ℕ → Bool) × Pt m → ℝ≥0∞ := fun q => ENNReal.ofReal (min (h q) b)
  have hρ' : Measurable ρ' := (hh.min measurable_const).ennreal_ofReal
  have hbd : ∀ y x, ρ' (y, x) ≤ (b.toNNReal : ℝ≥0∞) :=
    fun _ _ => ENNReal.ofReal_le_ofReal (min_le_right _ _)
  obtain ⟨T, hTm, _hTc, hTae⟩ :=
    Measurability.exists_jointlyMeasurable_passageTime_version (X.P.map Φ) hρ' hbd
  refine ⟨fun ω => T (Φ ω) (u, v), ?_, ?_⟩
  · exact (hTm.comp (measurable_id.prodMk measurable_const)).comp hΦ
  · filter_upwards [ae_of_ae_map hΦm.aemeasurable hTae] with ω hω
    rw [hω (u, v)]
    have hσ : ∀ x, σ ω x ≤ b := by
      intro x
      dsimp only [σ]
      split_ifs
      · exact (hBounds ω x).2
      · exact le_rfl
    have hField : (fun x => ρ' (Φ ω, x)) = fun x => ENNReal.ofReal (σ ω x) := by
      funext x
      have hx := hfh ω x
      simp only at hx
      simp only [ρ', ← hx, min_eq_left (hσ x), σ]
    rw [hField]
    have hLower : ∀ x, X.ρ ω x ≤ σ ω x := by
      intro x
      dsimp only [σ]
      split_ifs
      · exact le_rfl
      · exact (hBounds ω x).2
    have hEq : ∀ x ∈ closedBall u R, σ ω x = X.ρ ω x := by
      intro x hx
      exact ite_eq_left hx
    exact passage_eq_of_local_upper_extension X ha hBounds ω u v (σ ω) hLower hσ hEq

end IsotropicVariance.Paper.Proofs.Classical
