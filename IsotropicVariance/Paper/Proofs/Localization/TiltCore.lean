/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.Tilt
public import IsotropicVariance.Paper.Proofs.Localization.LocalFinal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:localization` for one outcome, through the tilt bound

For a fixed outcome, in the frame `g` of a pair of cubes: given the upper bounds `Y₁`, `Y₂` for
`T(a, u)` and `T(v, b)`, the bound `Y₃` for the passage time in `S`, and the bound `G` of equation
`eq:boxpenalty`, every point `z = (t, w)` of every curve of `Π_{T_S}(u, v)` has `c'|w|²/n ≤ H`,
where `H = Y₁ + Y₂ + Y₃ + G + 1 + 4ε²/n` (`transverse_le_of_bounds`, the last paragraph of the
proof). The tilt bound at a slope `κ ≤ 1` then gives `dist(z, [u, v]) ≤ 2Y + ε` with
`Y = √(n H₊/c')` (`infDist_le_of_tilt`), and so `W⁻¹ sup dist(x, [u, v]) ≤ 2√m + 2√(H₊/(c'Q))`
when `ε = 2√m W` and `W² = nQ` (`deviation_le_of_tilt`).

The region of the Lean is `{|t| ≤ C₀n, |w| ≤ C₀n}`: it lies in the set `Λ` of the proof of the
lemma, and it contains the curves, because `C₀n` bounds their distance from the center of `I`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Localization

open Contracts Infra.Os

variable {m : ℕ}

/-- The endpoints are within `r + 2ε` of each other. -/
lemma dist_le_of_near (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {r ε : ℝ} (hr : 0 ≤ r) {u v : Pt m}
    (hu : dist u (g 0) ≤ ε) (hv : dist v (g (r • e₁)) ≤ ε) : dist u v ≤ r + 2 * ε := by
  have hcenters : dist (g 0) (g (r • e₁)) = r := by
    rw [dist_frame, zero_sub, norm_neg, norm_smul, norm_e₁, mul_one, Real.norm_of_nonneg hr]
  have := dist_triangle4 u (g 0) (g (r • e₁)) v
  rw [hcenters, dist_comm (g (r • e₁)) v] at this
  linarith only [this, hu, hv]

/-- The first paragraph of the proof of Lemma `lem:localization`: the curves
have length at most `C(|v − u| + 1)`, so they stay within `C₀n` of the center of `I`. -/
lemma norm_symm_curve_le {σ : Pt m → ℝ} {a₀ b : ℝ} (ha₀ : 0 < a₀) (haσ : ∀ x, a₀ ≤ σ x)
    (hσb : ∀ x, σ x ≤ b) {S : Set (Pt m)} (hS : Convex ℝ S) (g : Pt m ≃ᵃⁱ[ℝ] Pt m)
    {n r ε C₀ : ℝ} (hr : 0 ≤ r) (hC₀ : (b * (r + 2 * ε) + 1) / a₀ + ε ≤ C₀ * n) {u v : Pt m}
    (hu : dist u (g 0) ≤ ε) (hv : dist v (g (r • e₁)) ≤ ε) (huS : u ∈ S) (hvS : v ∈ S)
    {γ : RectifiableCurve (Pt m)} (hγ : IsOneOptimal σ S u v γ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ‖g.symm (γ.toFun s)‖ ≤ C₀ * n := by
  have hb0 : 0 ≤ b := (ha₀.le.trans (haσ 0)).trans (hσb 0)
  have huv := dist_le_of_near g hr hu hv
  have hD : restrictedPassageTime σ S u v ≤ b * (r + 2 * ε) := by
    rw [restrictedPassageTime_eq_toReal]
    have := restrictedInf_le hσb hS huS hvS
    rw [edist_dist, ← ENNReal.ofReal_mul hb0] at this
    have hε : 0 ≤ r + 2 * ε := dist_nonneg.trans huv
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) this).trans
      (mul_le_mul_of_nonneg_left huv hb0)
  have hzu : dist u (γ.toFun s) ≤ (restrictedPassageTime σ S u v + 1) / a₀ := by
    have := dist_start_le ha₀ haσ (by linarith only [restrictedPassageTime_nonneg σ S u v])
      hγ.2.2.2 hs
    rwa [hγ.1] at this
  have h0 : ‖g.symm (γ.toFun s)‖ = dist (γ.toFun s) (g 0) := by
    rw [← dist_zero_right]
    calc dist (g.symm (γ.toFun s)) 0 = dist (g.symm (γ.toFun s)) (g.symm (g 0)) := by simp
      _ = dist (γ.toFun s) (g 0) := g.symm.dist_map _ _
  rw [h0]
  have h1 := dist_triangle (γ.toFun s) u (g 0)
  rw [dist_comm] at hzu
  have hq : (restrictedPassageTime σ S u v + 1) / a₀ ≤ (b * (r + 2 * ε) + 1) / a₀ :=
    div_le_div_of_nonneg_right (by linarith only [hD]) ha₀.le
  linarith only [h1, hzu, hq, hC₀, hu]

/-- `|v − u| − e₁ · (v − u) ≤ 4ε²/n` for `u`, `v` within `ε` of the centers
(the upper bound in the proof of Lemma `lem:localization`). -/
lemma dist_sub_lon_le (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n r ε : ℝ} (hn : 0 < n) (hε : 0 ≤ ε)
    (hrε : n / 2 ≤ r - 2 * ε) {u v : Pt m} (hu : dist u (g 0) ≤ ε)
    (hv : dist v (g (r • e₁)) ≤ ε) :
    dist u v - (Pt.lon (g.symm v) - Pt.lon (g.symm u)) ≤ 4 * ε ^ 2 / n := by
  have hu' : dist (g.symm u) 0 ≤ ε := by
    rw [show (0 : Pt m) = g.symm (g 0) by simp, g.symm.dist_map]; exact hu
  have hv' : dist (g.symm v) (r • e₁) ≤ ε := by
    rw [show (r • e₁ : Pt m) = g.symm (g (r • e₁)) by simp, g.symm.dist_map]; exact hv
  have hlonu := Infra.Slab.abs_lon_sub_le (g.symm u) 0
  have htru := Pt.norm_tr_sub_le_dist (g.symm u) 0
  have hlonv := Infra.Slab.abs_lon_sub_le (g.symm v) (r • e₁)
  have htrv := Pt.norm_tr_sub_le_dist (g.symm v) (r • e₁)
  rw [Pt.lon_zero, sub_zero] at hlonu
  rw [Pt.tr_zero, sub_zero] at htru
  rw [Pt.lon_smul, Pt.lon_e₁, mul_one] at hlonv
  rw [Pt.tr_smul_e₁, sub_zero] at htrv
  have hw : n / 2 ≤ Pt.lon (g.symm v - g.symm u) := by
    rw [Pt.lon_sub]
    have := abs_le.1 (hlonu.trans hu')
    have := abs_le.1 (hlonv.trans hv')
    linarith
  have h := norm_sub_lon_le (v := g.symm v - g.symm u) (by linarith only [hw, hn])
  rw [← dist_eq_norm, g.symm.dist_map, dist_comm, Pt.lon_sub] at h
  have htr : ‖Pt.tr (g.symm v - g.symm u)‖ ≤ 2 * ε := by
    rw [Pt.tr_sub]
    linarith only [norm_sub_le (Pt.tr (g.symm v)) (Pt.tr (g.symm u)), htrv.trans hv',
      htru.trans hu']
  refine h.trans ?_
  rw [Pt.lon_sub] at hw
  rw [div_le_div_iff₀ (by linarith only [hw, hn]) hn]
  have h0 : 0 ≤ ‖Pt.tr (g.symm v - g.symm u)‖ := norm_nonneg _
  have h1 := mul_le_mul htr htr h0 (by linarith only [hε] : 0 ≤ 2 * ε)
  have h2 := mul_le_mul_of_nonneg_right h1 hn.le
  have h3 := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 8 * ε ^ 2)
  nlinarith only [h2, h3]

/-- **The bound on `|w|` for one outcome**: if `z = (t, w)` lies on
`π ∈ Π_{T_S}(u, v)`, then `T(a, z) + T(z, b) ≤ T(a, u) + T(π) + T(v, b)`, so the upper bound and
equation `eq:boxpenalty` give `c'|w|²/n ≤ H`. -/
theorem transverse_le_of_bounds (X : Setting m) {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (ω : X.Ω)
    {σ : Pt m → ℝ} {a₀ b : ℝ} (ha₀ : 0 < a₀) (haσ : ∀ x, a₀ ≤ σ x)
    (hσb : ∀ x, σ x ≤ b) (hρσ : ∀ x, X.ρ ω x ≤ σ x) {S : Set (Pt m)} (hS : Convex ℝ S)
    (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n r ε C₀ c' : ℝ} (hn : 0 < n) (hc' : 0 < c') (hε : 0 ≤ ε)
    (hrε : n / 2 ≤ r - 2 * ε) (hC₀ : (b * (r + 2 * ε) + 1) / a₀ + ε ≤ C₀ * n)
    {I I' : Set (Pt m)} (hI : ∀ u ∈ I, dist u (g 0) ≤ ε) (hI' : ∀ v ∈ I', dist v (g (r • e₁)) ≤ ε)
    (hIS : I ⊆ S) (hI'S : I' ⊆ S) {Y₁ Y₂ Y₃ G : ℝ}
    (h1 : ∀ u ∈ I, X.passTime ω (anchorA g n C₀) u ≤ Pt.lon (g.symm u) + 2 * C₀ * n + Y₁)
    (h2 : ∀ v ∈ I', X.passTime ω v (anchorB g n r C₀) ≤
      r + 2 * C₀ * n - Pt.lon (g.symm v) + Y₂)
    (h3 : ∀ u ∈ I, ∀ v ∈ I', restrictedPassageTime σ S u v ≤ dist u v + Y₃)
    (h4 : ∀ ζ : Pt m, |Pt.lon ζ| ≤ C₀ * n → ‖Pt.tr ζ‖ ≤ C₀ * n →
      c' * ‖Pt.tr ζ‖ ^ 2 / n ≤ X.passTime ω (anchorA g n C₀) (g ζ) +
        X.passTime ω (g ζ) (anchorB g n r C₀) - (r + 4 * C₀ * n) + G)
    {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I') {γ : RectifiableCurve (Pt m)}
    (hγ : IsOneOptimal σ S u v γ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖Pt.tr (g.symm (γ.toFun s))‖ ≤
      tubeRadius n c' (Y₁ + Y₂ + Y₃ + G + 1 + 4 * ε ^ 2 / n) := by
  have hr : 0 < r := by linarith only [hn, hrε, hε]
  set H := Y₁ + Y₂ + Y₃ + G + 1 + 4 * ε ^ 2 / n
  have hcurv := dist_sub_lon_le g hn hε hrε (hI u hu) (hI' v hv)
  set ζ := g.symm (γ.toFun s)
  have hζ : ‖ζ‖ ≤ C₀ * n :=
    norm_symm_curve_le ha₀ haσ hσb hS g hr.le hC₀ (hI u hu) (hI' v hv) (hIS hu) (hI'S hv) hγ hs
  have hlon : |Pt.lon ζ| ≤ C₀ * n := (Profiles.abs_lon_le_norm ζ).trans hζ
  have htr : ‖Pt.tr ζ‖ ≤ C₀ * n := (Profiles.norm_tr_le_norm ζ).trans hζ
  have hstep4 := h4 ζ hlon htr
  simp only [ζ, AffineIsometryEquiv.apply_symm_apply] at hstep4
  have hstep1 := step1_point X hB ω hρσ hγ hs (anchorA g n C₀) (anchorB g n r C₀)
  have hTu := h1 u hu
  have hTv := h2 v hv
  have hDuv := h3 u hu v hv
  have hsq : c' * ‖Pt.tr ζ‖ ^ 2 / n ≤ H := by
    simp only [H]
    linarith only [hstep4, hstep1, hTu, hTv, hDuv, hcurv]
  unfold tubeRadius
  rw [show ‖Pt.tr ζ‖ = Real.sqrt (‖Pt.tr ζ‖ ^ 2) by rw [Real.sqrt_sq (norm_nonneg _)]]
  refine Real.sqrt_le_sqrt ?_
  rw [le_div_iff₀ hc']
  rw [div_le_iff₀ hn] at hsq
  have e1 := mul_le_mul_of_nonneg_right (le_max_left H 0) hn.le
  linarith only [hsq, e1, mul_comm n (max H 0), mul_comm (‖Pt.tr ζ‖ ^ 2) c']

/-- **Equation `eq:localization` for one outcome, the last step**: the
curves lie in `S`, so the tilt bound at the slope `κ ≤ 1` applies at their points:
`dist(z, [u, v]) ≤ 2Y + ε`. -/
theorem infDist_le_of_tilt (X : Setting m) {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (ω : X.Ω)
    {σ : Pt m → ℝ} {a₀ b : ℝ} (ha₀ : 0 < a₀) (haσ : ∀ x, a₀ ≤ σ x)
    (hσb : ∀ x, σ x ≤ b) (hρσ : ∀ x, X.ρ ω x ≤ σ x) {S : Set (Pt m)} (hS : Convex ℝ S)
    (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n r ε C₀ c' κ : ℝ} (hn : 0 < n) (hc' : 0 < c') (hε : 0 ≤ ε)
    (hrε : n / 2 ≤ r - 2 * ε) (hC₀ : (b * (r + 2 * ε) + 1) / a₀ + ε ≤ C₀ * n) (hκ : κ ≤ 1)
    (htilt : ∀ z ∈ S, -(κ * ‖Pt.tr (g.symm z)‖) ≤ Pt.lon (g.symm z) ∧
      Pt.lon (g.symm z) ≤ r + κ * ‖Pt.tr (g.symm z)‖)
    {I I' : Set (Pt m)} (hI : ∀ u ∈ I, dist u (g 0) ≤ ε) (hI' : ∀ v ∈ I', dist v (g (r • e₁)) ≤ ε)
    (hIS : I ⊆ S) (hI'S : I' ⊆ S) {Y₁ Y₂ Y₃ G : ℝ}
    (h1 : ∀ u ∈ I, X.passTime ω (anchorA g n C₀) u ≤ Pt.lon (g.symm u) + 2 * C₀ * n + Y₁)
    (h2 : ∀ v ∈ I', X.passTime ω v (anchorB g n r C₀) ≤
      r + 2 * C₀ * n - Pt.lon (g.symm v) + Y₂)
    (h3 : ∀ u ∈ I, ∀ v ∈ I', restrictedPassageTime σ S u v ≤ dist u v + Y₃)
    (h4 : ∀ ζ : Pt m, |Pt.lon ζ| ≤ C₀ * n → ‖Pt.tr ζ‖ ≤ C₀ * n →
      c' * ‖Pt.tr ζ‖ ^ 2 / n ≤ X.passTime ω (anchorA g n C₀) (g ζ) +
        X.passTime ω (g ζ) (anchorB g n r C₀) - (r + 4 * C₀ * n) + G)
    {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I') {γ : RectifiableCurve (Pt m)}
    (hγ : IsOneOptimal σ S u v γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    infDist (γ.toFun t) (segment ℝ u v) ≤
      2 * tubeRadius n c' (Y₁ + Y₂ + Y₃ + G + 1 + 4 * ε ^ 2 / n) + ε := by
  have hr : 0 < r := by linarith only [hn, hrε, hε]
  have hY := transverse_le_of_bounds X hB ω ha₀ haσ hσb hρσ hS g hn hc' hε hrε hC₀ hI hI' hIS hI'S
    h1 h2 h3 h4 hu hv hγ ht
  obtain ⟨h0, h5⟩ := htilt _ (hγ.2.2.1 t ht)
  exact infDist_segment_le_of_tilt g hr hκ (hI u hu) (hI' v hv) hY h0 h5

/-- `W⁻¹(2Y + ε) = 2√m + 2√(H₊/(c'Q))` when `ε = 2√m W`, `W² = nQ` and `Y = √(n H₊/c')`. -/
lemma normalized_tilt_eq {n W Q c' H : ℝ} (hn : 0 < n) (hW : 0 < W) (hQ : 0 < Q)
    (hWQ : W ^ 2 = n * Q) (hc' : 0 < c') :
    W⁻¹ * (2 * tubeRadius n c' H + 2 * Real.sqrt m * W) =
      2 * Real.sqrt m + 2 * Real.sqrt (max H 0 / (c' * Q)) := by
  have htube : W⁻¹ * tubeRadius n c' H = Real.sqrt (max H 0 / (c' * Q)) := by
    unfold tubeRadius
    rw [show W⁻¹ = Real.sqrt (W⁻¹ ^ 2) by rw [Real.sqrt_sq (by positivity)],
      ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [inv_pow, hWQ]
    field_simp
  have e1 : W⁻¹ * W = 1 := inv_mul_cancel₀ hW.ne'
  calc W⁻¹ * (2 * tubeRadius n c' H + 2 * Real.sqrt m * W)
      = 2 * (W⁻¹ * tubeRadius n c' H) + 2 * Real.sqrt m * (W⁻¹ * W) := by ring
    _ = _ := by rw [htube, e1]; ring

/-- **The normalized deviation for one outcome**: `W⁻¹ sup dist(x, [u, v]) ≤ 2√m + 2√(H₊/(c'Q))`,
from the bounds `Y₁`, `Y₂`, `Y₃`, `G`. -/
theorem deviation_le_of_tilt (X : Setting m) {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (ω : X.Ω)
    {σ : Pt m → ℝ} {a₀ b : ℝ} (ha₀ : 0 < a₀) (haσ : ∀ x, a₀ ≤ σ x)
    (hσb : ∀ x, σ x ≤ b) (hρσ : ∀ x, X.ρ ω x ≤ σ x) {S : Set (Pt m)} (hS : Convex ℝ S)
    (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n r W Q C₀ c' κ : ℝ} (hn : 0 < n) (hW : 0 < W) (hQ : 0 < Q)
    (hWQ : W ^ 2 = n * Q) (hc' : 0 < c') (hrε : n / 2 ≤ r - 2 * (2 * Real.sqrt m * W))
    (hC₀ : (b * (r + 2 * (2 * Real.sqrt m * W)) + 1) / a₀ + 2 * Real.sqrt m * W ≤ C₀ * n)
    (hκ : κ ≤ 1) (htilt : ∀ z ∈ S, -(κ * ‖Pt.tr (g.symm z)‖) ≤ Pt.lon (g.symm z) ∧
      Pt.lon (g.symm z) ≤ r + κ * ‖Pt.tr (g.symm z)‖)
    {I I' : Set (Pt m)} (hI : ∀ u ∈ I, dist u (g 0) ≤ 2 * Real.sqrt m * W)
    (hI' : ∀ v ∈ I', dist v (g (r • e₁)) ≤ 2 * Real.sqrt m * W)
    (hIS : I ⊆ S) (hI'S : I' ⊆ S) {Y₁ Y₂ Y₃ G : ℝ}
    (h1 : ∀ u ∈ I, X.passTime ω (anchorA g n C₀) u ≤ Pt.lon (g.symm u) + 2 * C₀ * n + Y₁)
    (h2 : ∀ v ∈ I', X.passTime ω v (anchorB g n r C₀) ≤
      r + 2 * C₀ * n - Pt.lon (g.symm v) + Y₂)
    (h3 : ∀ u ∈ I, ∀ v ∈ I', restrictedPassageTime σ S u v ≤ dist u v + Y₃)
    (h4 : ∀ ζ : Pt m, |Pt.lon ζ| ≤ C₀ * n → ‖Pt.tr ζ‖ ≤ C₀ * n →
      c' * ‖Pt.tr ζ‖ ^ 2 / n ≤ X.passTime ω (anchorA g n C₀) (g ζ) +
        X.passTime ω (g ζ) (anchorB g n r C₀) - (r + 4 * C₀ * n) + G) :
    W⁻¹ * maxSegmentDeviation σ S I I' ≤ 2 * Real.sqrt m + 2 *
      Real.sqrt (max (Y₁ + Y₂ + Y₃ + G + 1 + 4 * (2 * Real.sqrt m * W) ^ 2 / n) 0 / (c' * Q)) := by
  set ε := 2 * Real.sqrt m * W
  have hε : 0 ≤ ε := by positivity
  set H := Y₁ + Y₂ + Y₃ + G + 1 + 4 * ε ^ 2 / n
  set R := 2 * tubeRadius n c' H + ε
  have hR0 : 0 ≤ R := by have := tubeRadius_nonneg n c' H; positivity
  have hdev : maxSegmentDeviation σ S I I' ≤ R := by
    unfold maxSegmentDeviation
    refine Real.iSup_le (fun u => Real.iSup_le (fun v => Real.iSup_le (fun γ => Real.iSup_le
      (fun t => ?_) hR0) hR0) hR0) hR0
    exact infDist_le_of_tilt X hB ω ha₀ haσ hσb hρσ hS g hn hc' hε hrε hC₀ hκ htilt hI hI' hIS
      hI'S h1 h2 h3 h4 u.2 v.2 γ.2 t.2
  have hW0 : 0 ≤ W⁻¹ := by positivity
  calc W⁻¹ * maxSegmentDeviation σ S I I' ≤ W⁻¹ * R := mul_le_mul_of_nonneg_left hdev hW0
    _ = _ := normalized_tilt_eq hn hW hQ hWQ hc'

end IsotropicVariance.Paper.Proofs.Localization
