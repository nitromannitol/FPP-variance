/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
public import CurvatureVariance.Paper.Proofs.Geometry.TurningArith
public import CurvatureVariance.Paper.Proofs.Geometry.TurningExcess
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# One angular increment

The second step of the proof of Lemma `lem:cone`: if `y = f i` precedes `y' = f j` on an excess
path ending at `x' = f n`, both at distance comparable to `R` from `x'`, and `x' − y` is a positive
multiple of `(1, τ)`, the subgradient `P_τ` turns the triangle excess of `y, y', x'` into
`μ(x' − y') − P_τ · (x' − y')`, and the angular bound, equation `eq:angular`, bounds the angle
between `x' − y'` and `(1, τ)` by `C (S^{1/2} R^{−1/4} + ρ^{1+δ/2})`, where `ρ = |τ − t₀|` is the
reference term of `eq:angular` (`angle_step_le`).

`angle_link_le` is one link of the dyadic chain: from a point at angle at most `β` from `(1, t)`,
`‖t‖ ≤ T`, the slope `τ` of the chord is within `κ β` of `t`, `κ = slopeFactor T`
(`fst_pos_and_norm_slope_sub_le`), so `|τ − t₀| ≤ |t − t₀| + κ β`, and the angle of a later point
exceeds `β` by at most one increment. The subgradient is taken from `AngularSupport`.
-/

@[expose] public section

open InnerProductGeometry

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper

variable {m : ℕ}

/-- The constant of one angular increment, for the comparability constant `K`, the excess constant
`b` and the constant `c` of equation `eq:angular`: `(K b (2K)^{1/2} / c)^{1/2}`. -/
noncomputable def stepConst (K b c : ℝ) : ℝ :=
  Real.sqrt (K * b * Real.sqrt (2 * K) / c)

theorem stepConst_nonneg (K b c : ℝ) : 0 ≤ stepConst K b c :=
  Real.sqrt_nonneg _

variable {μ : Seminorm ℝ (Pt m)} {b S : ℝ} {f : ℕ → Pt m}

/-- **The angular increment, squared.** Let `p` be a subgradient of `μ` at `(1, τ)` with the angular
bound, equation `eq:angular`, with reference term `ρ`. If `f i` precedes `f j` (`j ≤ n`),
`f n − f i = s (1, τ)` with `s > 0`, `‖f n − f i‖, ‖f n − f j‖ ≤ K R` and `R ≤ K ‖f n − f j‖`,
then the squared angle between `f n − f j` and `(1, τ)` is at most
`K b (2K)^{1/2} / c · S / R^{1/2} + (C / c) ρ^{2+δ}`. -/
theorem sq_angle_step_le (hf : IsExcessPath μ b S f) (hb : 0 ≤ b) (hS : 0 ≤ S) {p : Pt m}
    {τ : EuclideanSpace ℝ (Fin m)} {ρ δ c C : ℝ} (hpc : inner ℝ p (slopeVec τ) = μ (slopeVec τ))
    (hp1 : ∀ z, inner ℝ p z ≤ μ z)
    (hp4 : ∀ z : Pt m, z ≠ 0 →
      c * ‖z‖ * angle z (slopeVec τ) ^ 2 - C * ‖z‖ * ρ ^ (2 + δ) ≤ μ z - inner ℝ p z)
    (hc : 0 < c) {K R s : ℝ} (hK : 0 < K) (hR : 0 < R) (hSR : S ^ 2 ≤ 2 * K * R) (hs : 0 < s)
    {i j n : ℕ} (hij : i ≤ j) (hjn : j ≤ n) (hw : f n - f i = s • slopeVec τ)
    (h₁ : ‖f n - f i‖ ≤ K * R) (h₂ : ‖f n - f j‖ ≤ K * R) (h₃ : R ≤ K * ‖f n - f j‖) :
    angle (f n - f j) (slopeVec τ) ^ 2 ≤
      K * b * Real.sqrt (2 * K) / c * (S / Real.sqrt R) + C / c * ρ ^ (2 + δ) := by
  set w := f n - f i with hwdef
  set w' := f n - f j with hw'def
  have hKR0 : 0 ≤ K * R := by positivity
  -- the triangle excess for `f i, f j, f n`
  have hsplit : f j - f i = w - w' := by rw [hwdef, hw'def]; abel
  have d12 : ‖f j - f i‖ ≤ 2 * K * R := by
    rw [hsplit]
    calc ‖w - w'‖ ≤ ‖w‖ + ‖w'‖ := norm_sub_le _ _
      _ ≤ K * R + K * R := add_le_add h₁ h₂
      _ = 2 * K * R := by ring
  have hex := hf.excess_le i j n hij hjn (2 * K * R) hSR d12 (by linarith) (by linarith)
  rw [hsplit] at hex
  set E := b * S * Real.sqrt (2 * K * R) with hEdef
  -- the contact at `f n − f i`
  have hμw : μ w = inner ℝ p w := by
    rw [hw, map_smul_eq_mul, inner_smul_right, hpc, Real.norm_eq_abs, abs_of_pos hs]
  have hdef : μ w' - inner ℝ p w' ≤ E := by
    have h1 := hp1 (w - w')
    have h2 : inner ℝ p w = inner ℝ p (w - w') + inner ℝ p w' := by
      rw [← inner_add_right, sub_add_cancel]
    linarith
  -- equation `eq:angular` at `f n − f j`
  have hw'pos : 0 < ‖w'‖ := by
    have : 0 < K * ‖w'‖ := hR.trans_le h₃
    exact pos_of_mul_pos_right this hK.le
  have h4 := hp4 w' (norm_pos_iff.1 hw'pos)
  set θ := angle w' (slopeVec τ)
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hE : E ≤ K * b * Real.sqrt (2 * K) * S * ‖w'‖ / Real.sqrt R := by
    rw [hEdef, Real.sqrt_mul (by positivity), le_div_iff₀ hsR]
    have hRR : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR.le
    have hX : 0 ≤ b * S * Real.sqrt (2 * K) := by positivity
    have := mul_le_mul_of_nonneg_left h₃ hX
    calc b * S * (Real.sqrt (2 * K) * Real.sqrt R) * Real.sqrt R
        = b * S * Real.sqrt (2 * K) * (Real.sqrt R * Real.sqrt R) := by ring
      _ = b * S * Real.sqrt (2 * K) * R := by rw [hRR]
      _ ≤ b * S * Real.sqrt (2 * K) * (K * ‖w'‖) := this
      _ = K * b * Real.sqrt (2 * K) * S * ‖w'‖ := by ring
  have hpos : 0 < c * ‖w'‖ := mul_pos hc hw'pos
  refine le_of_mul_le_mul_right ?_ hpos
  have key : (K * b * Real.sqrt (2 * K) / c * (S / Real.sqrt R) + C / c * ρ ^ (2 + δ)) *
      (c * ‖w'‖) = K * b * Real.sqrt (2 * K) * S * ‖w'‖ / Real.sqrt R +
        C * ‖w'‖ * ρ ^ (2 + δ) := by
    field_simp
  rw [key]
  nlinarith

/-- **The angular increment** (the proof of Lemma `lem:cone`): under the hypotheses of
`sq_angle_step_le`, the angle between `f n − f j` and `(1, τ)` is at most
`stepConst K b c · turnErr S R + (C / c)^{1/2} ρ^{1+δ/2}`. -/
theorem angle_step_le (hf : IsExcessPath μ b S f) (hb : 0 ≤ b) (hS : 0 ≤ S) {p : Pt m}
    {τ : EuclideanSpace ℝ (Fin m)} {ρ δ c C : ℝ} (hρ : 0 ≤ ρ)
    (hpc : inner ℝ p (slopeVec τ) = μ (slopeVec τ))
    (hp1 : ∀ z, inner ℝ p z ≤ μ z)
    (hp4 : ∀ z : Pt m, z ≠ 0 →
      c * ‖z‖ * angle z (slopeVec τ) ^ 2 - C * ‖z‖ * ρ ^ (2 + δ) ≤ μ z - inner ℝ p z)
    (hc : 0 < c) (hC : 0 ≤ C) {K R s : ℝ} (hK : 0 < K) (hR : 0 < R) (hSR : S ^ 2 ≤ 2 * K * R)
    (hs : 0 < s) {i j n : ℕ} (hij : i ≤ j) (hjn : j ≤ n) (hw : f n - f i = s • slopeVec τ)
    (h₁ : ‖f n - f i‖ ≤ K * R) (h₂ : ‖f n - f j‖ ≤ K * R) (h₃ : R ≤ K * ‖f n - f j‖) :
    angle (f n - f j) (slopeVec τ) ≤
      stepConst K b c * turnErr S R + Real.sqrt (C / c) * ρ ^ (1 + δ / 2) := by
  have hsq := sq_angle_step_le hf hb hS hpc hp1 hp4 hc hK hR hSR hs hij hjn hw h₁ h₂ h₃
  have ha : 0 ≤ K * b * Real.sqrt (2 * K) / c * (S / Real.sqrt R) := by positivity
  have hτ : 0 ≤ C / c * ρ ^ (2 + δ) := by positivity
  refine (Real.le_sqrt_of_sq_le hsq).trans ((sqrt_add_le_add_sqrt ha hτ).trans ?_)
  rw [Real.sqrt_mul (show 0 ≤ K * b * Real.sqrt (2 * K) / c by positivity) (S / Real.sqrt R),
    Real.sqrt_mul (show 0 ≤ C / c by positivity) (ρ ^ (2 + δ)),
    Real.sqrt_eq_rpow (ρ ^ (2 + δ)), ← Real.rpow_mul hρ,
    show (2 + δ) * (1 / 2) = 1 + δ / 2 by ring]
  rfl

/-- **One link of the chain.** If `f n − f i` is at angle at most `β ≤ aperture T` from `(1, t)`,
with `‖t‖ ≤ T` and `‖t − t₀‖ + κ β ≤ r₁`, `κ = slopeFactor T`, and a later point `f j` is at
distance comparable to `R` from `f n`, then the angle of `f n − f j` from `(1, t)` exceeds `β` by at
most one angular increment, with reference term `(‖t − t₀‖ + κ β)^{1+δ/2}`. -/
theorem angle_link_le {t₀ : EuclideanSpace ℝ (Fin m)} {δ c C r₁ T : ℝ}
    (hsupp : AngularSupport μ t₀ δ c C r₁) (hc : 0 < c)
    (hC : 0 ≤ C) (hf : IsExcessPath μ b S f) (hb : 0 ≤ b) (hS : 0 ≤ S)
    {t : EuclideanSpace ℝ (Fin m)} (ht : ‖t‖ ≤ T) {i j n : ℕ} (hij : i ≤ j) (hjn : j ≤ n)
    {β : ℝ} (hβ : angle (f n - f i) (slopeVec t) ≤ β) (hβ4 : β ≤ aperture T)
    (hβr : ‖t - t₀‖ + slopeFactor T * β ≤ r₁) {K R : ℝ} (hK : 0 < K) (hR : 0 < R)
    (hSR : S ^ 2 ≤ 2 * K * R)
    (h₁ : ‖f n - f i‖ ≤ K * R) (h₂ : ‖f n - f j‖ ≤ K * R) (h₃ : R ≤ K * ‖f n - f j‖)
    (hδ : 0 ≤ δ) :
    angle (f n - f j) (slopeVec t) ≤
      β + stepConst K b c * turnErr S R +
        Real.sqrt (C / c) * (‖t - t₀‖ + slopeFactor T * β) ^ (1 + δ / 2) := by
  set w := f n - f i with hwdef
  obtain ⟨hpos, hslope⟩ := fst_pos_and_norm_slope_sub_le ht hβ4 hβ
  set τ := w.fst⁻¹ • w.snd with hτdef
  have hτ : ‖τ - t₀‖ ≤ ‖t - t₀‖ + slopeFactor T * β := by
    have h' : ‖τ - t₀‖ ≤ ‖τ - t‖ + ‖t - t₀‖ := by
      calc ‖τ - t₀‖ = ‖(τ - t) + (t - t₀)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖τ - t‖ + ‖t - t₀‖ := norm_add_le _ _
    linarith
  obtain ⟨p, hpc, hp1, hp4⟩ := hsupp τ (hτ.trans hβr)
  have hw : w = w.fst • slopeVec τ := eq_smul_slopeVec w hpos.ne'
  have hstep := angle_step_le hf hb hS (norm_nonneg _) hpc hp1 hp4 hc hC hK hR hSR hpos hij hjn
    hw h₁ h₂ h₃
  have htri := angle_le_angle_add_angle (f n - f j) (slopeVec τ) (slopeVec t)
  have hang : angle (slopeVec τ) (slopeVec t) ≤ β := by
    rw [← angle_smul_left_of_pos (slopeVec τ) (slopeVec t) hpos, ← hw]
    exact hβ
  have hpow : ‖τ - t₀‖ ^ (1 + δ / 2) ≤ (‖t - t₀‖ + slopeFactor T * β) ^ (1 + δ / 2) :=
    Real.rpow_le_rpow (norm_nonneg _) hτ (by positivity)
  have := mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg (C / c))
  linarith

end CurvatureVariance.Paper.Proofs.Geometry
