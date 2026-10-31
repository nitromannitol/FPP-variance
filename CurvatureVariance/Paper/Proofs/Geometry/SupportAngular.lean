/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SupportQuadratic
public import CurvatureVariance.Paper.Proofs.Geometry.SupportSubgradient
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
public import CurvatureVariance.Infra.FPP.TimeConstantNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Module

/-!
# The supporting hyperplanes: the angular bound `eq:angular`

Equation `eq:angular` (Lemma `lem:support`):
`μ(z) − P_t·z ≥ c|z| ∠(z,(1,t))² − C|z||t − t₀|^{2+δ}` for `z ≠ 0` and `|t − t₀| ≤ r₁`. The defect
`D = μ − P_t` is nonnegative, subadditive, positively homogeneous and zero at `(1,t)`. A short step
`l x` from `(1,t)` in the direction of a unit vector `x` ends on the ray of `(1, t + h)` with
`h = (l/s)(x₂ − x₁ t)`, `s = 1 + l x₁`, and `|h| ≤ 2l(1 + |t|) ≤ r₁` for a step `l` depending on
a bound `T ≥ |t₀|`. Equation `eq:support` at that slope and subadditivity bound the transverse
residual `|x₂ − x₁ t|`, which controls the sine of the angle away from the ray opposite to `(1,t)`
(`sq_angle_mul_sq_le_sq_residual`); near that ray `D` is close to `D(−e) = 2μ(e)`, by the
symmetry of the norm and its equivalence with the Euclidean norm.

This is the argument of the proof of Lemma `lem:support`. It uses only
`eq:support` near `t₀`, the subadditivity and symmetry of the norm, and `|p| ≤ sup_{|z|=1} μ(z)`
(the paper's `μ^*`) for a subgradient `p`. Every constant depends on the direction
only through a bound `T ≥ |t₀|` (`bd.T`), by way of the step `l`.

`exists_support_bounds` proves the two equations at a `Bounds` record.
Supporting covectors exist by `exists_isSubgradient` (`Proofs.Geometry.SupportSubgradient`, imported
here).
-/

@[expose] public section

open InnerProductGeometry
open scoped InnerProductSpace

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Angular geometry -/

/-- Away from the opposite direction, every residual to a line controls the angle. -/
theorem sq_angle_mul_sq_le_sq_residual {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x e : V} (hx : ‖x‖ = 1) (he : ‖e‖ = 1) {r : ℝ} (hr : 0 ≤ r) (hsep : r ≤ ‖x + e‖) (b : ℝ) :
    r ^ 2 * (angle x e) ^ 2 ≤ Real.pi ^ 2 * ‖x - b • e‖ ^ 2 := by
  let z : ℝ := ⟪x, e⟫_ℝ
  have hz : z = Real.cos (angle x e) := inner_eq_cos_angle_of_norm_eq_one hx he
  have hz0 : -1 ≤ z := hz ▸ Real.neg_one_le_cos _
  have hsum : ‖x + e‖ ^ 2 = 2 + 2 * z := by
    rw [norm_add_pow_two_real, hx, he]
    dsimp only [z]
    ring
  have hres : ‖x - b • e‖ ^ 2 = 1 - 2 * b * z + b ^ 2 := by
    rw [norm_sub_pow_two_real, hx, norm_smul, Real.norm_eq_abs, he, mul_one,
      inner_smul_right, sq_abs]
    dsimp only [z]
    ring
  have hsq := (sq_le_sq₀ hr (norm_nonneg _)).mpr hsep
  rw [hsum] at hsq
  have hcos := Real.cos_le_one_sub_mul_cos_sq
    (show |angle x e| ≤ Real.pi by rw [abs_of_nonneg (angle_nonneg _ _)]; exact angle_le_pi _ _)
  rw [← hz] at hcos
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hθ : 2 * (angle x e) ^ 2 ≤ Real.pi ^ 2 * (1 - z) := by
    have h := (mul_le_mul_iff_right₀ hp).mpr hcos
    have hid : Real.pi ^ 2 * (1 - 2 / Real.pi ^ 2 * (angle x e) ^ 2) =
        Real.pi ^ 2 - 2 * (angle x e) ^ 2 := by field_simp
    rw [hid] at h
    linarith only [h]
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (angle x e))
  have hθmul := mul_le_mul_of_nonneg_right hθ (by linarith only [hz0] : 0 ≤ 1 + z)
  have hres' : 1 - z ^ 2 ≤ ‖x - b • e‖ ^ 2 := by
    rw [hres]
    nlinarith only [sq_nonneg (b - z)]
  have hresmul := mul_le_mul_of_nonneg_left hres' hp.le
  nlinarith only [hmul, hθmul, hresmul]

/-- The residual of `x` to the line through `(1, t)`, at the parameter `x₁`. -/
theorem norm_sub_fst_smul_slopeVec (t : EuclideanSpace ℝ (Fin m)) (x : Pt m) :
    ‖x - x.fst • slopeVec t‖ = ‖x.snd - x.fst • t‖ := by
  have h : x - x.fst • slopeVec t = WithLp.toLp 2 ((0 : ℝ), x.snd - x.fst • t) := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · change x.fst - x.fst * 1 = 0
      ring
    · rfl
  rw [h]
  exact WithLp.norm_toLp_snd _ _ _ _

/-! ### The angular bound -/

section Angular

variable {μ : PtNorm m} {δ : ℝ}

/-- **The transverse residual is controlled by the defect**: from the lower bound of equation
`eq:support` with constant `c₀` on `|t − t₀|, |h| ≤ r₁`, for a slope `|t − t₀| ≤ r₁`, a
subgradient `p` at `(1, t)`, a unit vector `x` and a step `l ≤ 1/2` with `2l(1 + |t|) ≤ r₁`,
`(c₀ l/2) |x₂ − x₁ t|² − (2C/l) |t − t₀|^{2+δ} ≤ μ(x) − p·x`. -/
theorem transverse_defect_lower {t₀ : EuclideanSpace ℝ (Fin m)} {c₀ r₁ C : ℝ} (hc₀ : 0 < c₀)
    (hC : 0 < C)
    (hq : ∀ t h : EuclideanSpace ℝ (Fin m), ‖t - t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient μ (slopeVec t) p →
        c₀ * ‖h‖ ^ 2 - C * ‖t - t₀‖ ^ (2 + δ) ≤
          μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)))
    {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1 / 2) {t : EuclideanSpace ℝ (Fin m)} (ht : ‖t - t₀‖ ≤ r₁)
    (hlr : 2 * l * (1 + ‖t‖) ≤ r₁) {p : Pt m}
    (hp : IsSubgradient μ (slopeVec t) p) {x : Pt m} (hx : ‖x‖ = 1) :
    c₀ * l / 2 * ‖x.snd - x.fst • t‖ ^ 2 - 2 * C / l * ‖t - t₀‖ ^ (2 + δ) ≤
      μ.1 x - ⟪p, x⟫_ℝ := by
  have hfst : |x.fst| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hx] using WithLp.norm_fst_le ℝ x
  have hsnd : ‖x.snd‖ ≤ 1 := (WithLp.norm_snd_le ℝ x).trans_eq hx
  set s := 1 + l * x.fst with hsdef
  have hs1 : 1 / 2 ≤ s := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs x.fst |>.trans hfst) hl.le
    nlinarith
  have hs2 : s ≤ 2 := by
    have := mul_le_mul_of_nonneg_left (le_abs_self x.fst |>.trans hfst) hl.le
    nlinarith
  have hs0 : 0 < s := by linarith
  set τ := s⁻¹ • (t + l • x.snd) with hτdef
  have hshift : slopeVec t + l • x = s • slopeVec τ := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · change 1 + l * x.fst = s * 1
      rw [mul_one]
    · change t + l • x.snd = s • (s⁻¹ • (t + l • x.snd))
      rw [smul_inv_smul₀ hs0.ne']
  set h := τ - t with hhdef
  have hh : h = (l / s) • (x.snd - x.fst • t) := by
    apply smul_right_injective _ hs0.ne'
    change s • (τ - t) = s • ((l / s) • (x.snd - x.fst • t))
    rw [smul_sub, hτdef, smul_inv_smul₀ hs0.ne', smul_smul, mul_div_cancel₀ _ hs0.ne', hsdef]
    module
  have hhn : ‖h‖ ≤ r₁ := by
    have hres : ‖x.snd - x.fst • t‖ ≤ 1 + ‖t‖ := by
      calc ‖x.snd - x.fst • t‖ ≤ ‖x.snd‖ + ‖x.fst • t‖ := norm_sub_le _ _
        _ = ‖x.snd‖ + |x.fst| * ‖t‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 + 1 * ‖t‖ := add_le_add hsnd
            (mul_le_mul_of_nonneg_right hfst (norm_nonneg _))
        _ = 1 + ‖t‖ := by ring
    have hls : l / s ≤ 2 * l := by
      rw [div_le_iff₀ hs0]
      nlinarith
    rw [hh, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hl hs0)]
    calc l / s * ‖x.snd - x.fst • t‖ ≤ 2 * l * (1 + ‖t‖) :=
          mul_le_mul hls hres (norm_nonneg _) (by positivity)
      _ ≤ r₁ := hlr
  have htτ : t + h = τ := by rw [hhdef]; abel
  have hlow := hq t h ht hhn p hp
  rw [htτ] at hlow
  -- the defect is homogeneous, subadditive and zero at `(1, t)`
  have hhom : μ.1 (s • slopeVec τ) - ⟪p, s • slopeVec τ⟫_ℝ =
      s * (μ.1 (slopeVec τ) - ⟪p, slopeVec τ⟫_ℝ) := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hs0, inner_smul_right]
    ring
  have hsub : μ.1 (slopeVec t + l • x) - ⟪p, slopeVec t + l • x⟫_ℝ ≤
      l * (μ.1 x - ⟪p, x⟫_ℝ) := by
    have h1 := map_add_le_add μ.1 (slopeVec t) (l • x)
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hl] at h1
    rw [inner_add_right, inner_smul_right, hp.1]
    linarith
  rw [hshift, hhom] at hsub
  set R := ‖x.snd - x.fst • t‖ ^ 2 with hR
  set T := ‖t - t₀‖ ^ (2 + δ) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg (norm_nonneg _) _
  have hR0 : 0 ≤ R := sq_nonneg _
  have e1 : s * (c₀ * ‖h‖ ^ 2) = c₀ * l ^ 2 / s * R := by
    rw [hh, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hR]
    field_simp
  have e2 : c₀ * l ^ 2 / 2 * R ≤ c₀ * l ^ 2 / s * R :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) (by positivity)
      hs2) hR0
  have e3 : s * (C * T) ≤ 2 * (C * T) := mul_le_mul_of_nonneg_right hs2 (by positivity)
  have e4 := mul_le_mul_of_nonneg_left hlow hs0.le
  have key : c₀ * l ^ 2 / 2 * R - 2 * C * T ≤ l * (μ.1 x - ⟪p, x⟫_ℝ) := by
    have : s * (c₀ * ‖h‖ ^ 2 - C * T) = s * (c₀ * ‖h‖ ^ 2) - s * (C * T) := by ring
    linarith
  have hdiv : c₀ * l / 2 * R - 2 * C / l * T = (c₀ * l ^ 2 / 2 * R - 2 * C * T) / l := by
    field_simp
  rw [hdiv, div_le_iff₀ hl]
  linarith

/-- **Equation `eq:angular`**: for `T ≥ 0` and constants `c₀, r₁, C > 0` there are `c, C' > 0`
such that, for every `t₀` with `|t₀| ≤ T` at which the lower bound of equation `eq:support` holds
with constant `c₀` on `|t − t₀|, |h| ≤ r₁`,
`c|z|∠(z,(1,t))² − C'|z||t − t₀|^{2+δ} ≤ μ(z) − p·z` for `|t − t₀| ≤ r₁`, every subgradient `p`
at `(1, t)` and `z ≠ 0`. The constants depend on `t₀` only through the bound `T`, by way of the step
`l = min(1/2, r₁/(2(1 + T + r₁)))`. -/
theorem angular_support {T c₀ r₁ C : ℝ} (hT : 0 ≤ T) (hc₀ : 0 < c₀) (hr₁ : 0 < r₁)
    (hC : 0 < C) :
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∀ t₀ : EuclideanSpace ℝ (Fin m), ‖t₀‖ ≤ T →
      (∀ t h : EuclideanSpace ℝ (Fin m), ‖t - t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
        ∀ p : Pt m, IsSubgradient μ (slopeVec t) p →
          c₀ * ‖h‖ ^ 2 - C * ‖t - t₀‖ ^ (2 + δ) ≤
            μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h))) →
      ∀ t : EuclideanSpace ℝ (Fin m), ‖t - t₀‖ ≤ r₁ →
        ∀ p : Pt m, IsSubgradient μ (slopeVec t) p → ∀ z : Pt m, z ≠ 0 →
          c * ‖z‖ * angle z (slopeVec t) ^ 2 - C' * ‖z‖ * ‖t - t₀‖ ^ (2 + δ) ≤
            μ.1 z - inner ℝ p z := by
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := PtNorm.exists_bounds μ
  set l := min (1 / 2) (r₁ / (2 * (1 + T + r₁))) with hldef
  have hden : 0 < 2 * (1 + T + r₁) := by positivity
  have hl : 0 < l := lt_min (by norm_num) (div_pos hr₁ hden)
  have hl1 : l ≤ 1 / 2 := min_le_left _ _
  have hlr0 : l * (2 * (1 + T + r₁)) ≤ r₁ := by
    have := min_le_right (1 / 2 : ℝ) (r₁ / (2 * (1 + T + r₁)))
    rwa [← hldef, le_div_iff₀ hden] at this
  set R := min 1 (lo / (2 * hi)) with hRdef
  have hR : 0 < R := lt_min one_pos (by positivity)
  have hRhi : 2 * hi * R ≤ lo := by
    have := min_le_right (1 : ℝ) (lo / (2 * hi))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  set c := min lo (c₀ * l / 2 * R ^ 2) / Real.pi ^ 2 with hcdef
  have hc : 0 < c := div_pos (lt_min hlo (by positivity)) hp2
  have hclo : c * Real.pi ^ 2 ≤ lo := by
    rw [hcdef, div_mul_cancel₀ _ hp2.ne']; exact min_le_left _ _
  have hcl : c * Real.pi ^ 2 ≤ c₀ * l / 2 * R ^ 2 := by
    rw [hcdef, div_mul_cancel₀ _ hp2.ne']; exact min_le_right _ _
  set C' := 2 * C / l + 1 with hC'def
  have hC' : 0 < C' := by positivity
  refine ⟨c, C', hc, hC', fun t₀ ht₀ hq t ht p hp => ?_⟩
  have hT0 : 0 ≤ ‖t - t₀‖ ^ (2 + δ) := Real.rpow_nonneg (norm_nonneg _) _
  have hlr : 2 * l * (1 + ‖t‖) ≤ r₁ := by
    have htn : ‖t‖ ≤ T + r₁ := by
      calc ‖t‖ = ‖(t - t₀) + t₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖t - t₀‖ + ‖t₀‖ := norm_add_le _ _
        _ ≤ T + r₁ := by linarith
    have := mul_le_mul_of_nonneg_left htn hl.le
    linarith
  -- the subgradient has norm at most `hi`
  have hpnorm : ‖p‖ ≤ hi := by
    have h1 : ‖p‖ ^ 2 ≤ hi * ‖p‖ := by
      rw [← real_inner_self_eq_norm_sq]
      exact (hp.2 p).trans (hb p).2
    by_contra hcon
    push Not at hcon
    have : hi * ‖p‖ < ‖p‖ * ‖p‖ := mul_lt_mul_of_pos_right hcon (by linarith)
    rw [sq] at h1
    linarith
  have hunit : ∀ x : Pt m, ‖x‖ = 1 →
      c * angle x (slopeVec t) ^ 2 - C' * ‖t - t₀‖ ^ (2 + δ) ≤ μ.1 x - ⟪p, x⟫_ℝ := by
    intro x hx
    set q := slopeVec t with hqdef
    have hq1 : 1 ≤ ‖q‖ := one_le_norm_slopeVec t
    have hq0 : 0 < ‖q‖ := by linarith
    set e : Pt m := ‖q‖⁻¹ • q with hedef
    have he : ‖e‖ = 1 := by
      rw [hedef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq0), inv_mul_cancel₀ hq0.ne']
    have hangle : angle x e = angle x q := angle_smul_right_of_pos x q (inv_pos.2 hq0)
    have hθπ : angle x q ^ 2 ≤ Real.pi ^ 2 :=
      (sq_le_sq₀ (angle_nonneg _ _) Real.pi_pos.le).2 (angle_le_pi _ _)
    by_cases hnear : ‖x + e‖ ≤ R
    · -- near the opposite ray: `D(x) ≥ D(−e) − 2 hi |x + e| = 2 μ(e) − 2 hi |x + e|`
      have hpe : ⟪p, e⟫_ℝ = μ.1 e := by
        rw [hedef, inner_smul_right, map_smul_eq_mul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hq0), hqdef, hp.1]
      have hmue : lo ≤ μ.1 e := by have := (hb e).1; rwa [he, mul_one] at this
      have hlip : μ.1 (-e) - ⟪p, -e⟫_ℝ ≤ μ.1 x - ⟪p, x⟫_ℝ + 2 * hi * ‖x + e‖ := by
        have h1 : μ.1 (-e) ≤ μ.1 x + μ.1 (-e - x) := by
          have := map_add_le_add μ.1 x (-e - x)
          rwa [add_sub_cancel] at this
        have h2 : μ.1 (-e - x) ≤ hi * ‖x + e‖ := by
          have := (hb (-e - x)).2
          rwa [show ‖-e - x‖ = ‖x + e‖ by rw [show -e - x = -(x + e) by abel, norm_neg]] at this
        have h3 : -⟪p, -e - x⟫_ℝ ≤ hi * ‖x + e‖ := by
          have := real_inner_le_norm p (-(-e - x))
          rw [inner_neg_right, show -(-e - x) = x + e by abel] at this
          have := mul_le_mul_of_nonneg_right hpnorm (norm_nonneg (x + e))
          linarith
        have h4 : ⟪p, -e⟫_ℝ = ⟪p, x⟫_ℝ + ⟪p, -e - x⟫_ℝ := by
          rw [← inner_add_right, add_sub_cancel]
        linarith
      rw [map_neg_eq_map, inner_neg_right, hpe] at hlip
      have hcθ := (mul_le_mul_of_nonneg_left hθπ hc.le).trans hclo
      have hRx := mul_le_mul_of_nonneg_left hnear (by positivity : (0 : ℝ) ≤ 2 * hi)
      have hCT := mul_nonneg hC'.le hT0
      linarith
    · have hgeom := sq_angle_mul_sq_le_sq_residual hx he hR.le (le_of_not_ge hnear)
        (x.fst * ‖q‖)
      have hres : x - (x.fst * ‖q‖) • e = x - x.fst • q := by
        rw [hedef, smul_smul, mul_assoc, mul_inv_cancel₀ hq0.ne', mul_one]
      rw [hangle, hres, hqdef, norm_sub_fst_smul_slopeVec] at hgeom
      have hlocal := transverse_defect_lower hc₀ hC hq hl hl1 ht hlr hp hx
      have hcθ : c * angle x (slopeVec t) ^ 2 ≤ c₀ * l / 2 * ‖x.snd - x.fst • t‖ ^ 2 := by
        have h1 : c * Real.pi ^ 2 * angle x (slopeVec t) ^ 2 ≤
            c₀ * l / 2 * R ^ 2 * angle x (slopeVec t) ^ 2 :=
          mul_le_mul_of_nonneg_right hcl (sq_nonneg _)
        have h2 : c₀ * l / 2 * (R ^ 2 * angle x (slopeVec t) ^ 2) ≤
            c₀ * l / 2 * (Real.pi ^ 2 * ‖x.snd - x.fst • t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
        have h3 : c * angle x (slopeVec t) ^ 2 * Real.pi ^ 2 ≤
            c₀ * l / 2 * ‖x.snd - x.fst • t‖ ^ 2 * Real.pi ^ 2 := by linarith
        exact le_of_mul_le_mul_right h3 hp2
      have hCl : 2 * C / l * ‖t - t₀‖ ^ (2 + δ) ≤ C' * ‖t - t₀‖ ^ (2 + δ) :=
        mul_le_mul_of_nonneg_right (by linarith) hT0
      linarith
  intro z hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  set y : Pt m := ‖z‖⁻¹ • z with hydef
  have hy : ‖y‖ = 1 := by
    rw [hydef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hz0), inv_mul_cancel₀ hz0.ne']
  have hhom : ‖z‖ * (μ.1 y - ⟪p, y⟫_ℝ) = μ.1 z - ⟪p, z⟫_ℝ := by
    rw [hydef, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hz0), inner_smul_right]
    field_simp
  have hang : angle y (slopeVec t) = angle z (slopeVec t) :=
    angle_smul_left_of_pos _ _ (inv_pos.2 hz0)
  have := mul_le_mul_of_nonneg_left (hunit y hy) hz0.le
  rw [hhom, hang] at this
  calc c * ‖z‖ * angle z (slopeVec t) ^ 2 - C' * ‖z‖ * ‖t - t₀‖ ^ (2 + δ)
      = ‖z‖ * (c * angle z (slopeVec t) ^ 2 - C' * ‖t - t₀‖ ^ (2 + δ)) := by ring
    _ ≤ _ := this

end Angular

/-! ### The contract -/

/-- **Lemma `lem:support`**: equations `eq:support` and `eq:angular`, with the constants of
`support_quadratic` at `bd` and those of `angular_support` at the norm of `bd.law` and
`T = bd.T`. -/
theorem exists_support_bounds (m : ℕ) (bd : Bounds m) (hbd : bd.Valid) :
    ∃ c C r₁ : ℝ, 0 < c ∧ 0 < C ∧ 0 < r₁ ∧
    ∀ M : Model m, M.Standing → M.Fits bd →
      (∀ t h : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
        ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
          c * ‖h‖ ^ 2 - C * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
              M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
              C * ‖h‖ ^ 2 + C * ‖t - M.t₀‖ ^ (2 + M.δ)) ∧
      (∀ t : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ →
        ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p → ∀ z : Pt m, z ≠ 0 →
          c * ‖z‖ * angle z (slopeVec t) ^ 2 - C * ‖z‖ * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 z - inner ℝ p z) := by
  obtain ⟨c₀, r₁, C, hc₀, hr₁, hC, hq⟩ := support_quadratic hbd
  obtain ⟨c₅, C₅, hc₅, hC₅, hang⟩ :=
    angular_support (μ := bd.law.μ) (δ := bd.law.δ) hbd.T_nonneg hc₀ hr₁ hC
  refine ⟨min c₀ c₅, max C C₅, r₁, lt_min hc₀ hc₅, lt_max_of_lt_left hC, hr₁,
    fun M hM hfit => ⟨fun t h ht hh p hp => ?_, fun t ht p hp z hz => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := hq M hM hfit t h ht hh p hp
    have hT := Real.rpow_nonneg (norm_nonneg (t - M.t₀)) (2 + M.δ)
    have hhs := sq_nonneg ‖h‖
    have hc : min c₀ c₅ ≤ c₀ := min_le_left _ _
    have hC' : C ≤ max C C₅ := le_max_left _ _
    constructor
    · have := mul_le_mul_of_nonneg_right hc hhs
      have := mul_le_mul_of_nonneg_right hC' hT
      linarith
    · have := mul_le_mul_of_nonneg_right hC' hhs
      have := mul_le_mul_of_nonneg_right hC' hT
      linarith
  · rw [← hfit.μ_eq, ← hfit.δ_eq] at hang
    have h := hang M.t₀ hfit.t₀_le (fun t h ht hh p hp => (hq M hM hfit t h ht hh p hp).1)
      t ht p hp z hz
    have hz0 := norm_nonneg z
    have hA := sq_nonneg (angle z (slopeVec t))
    have hT := Real.rpow_nonneg (norm_nonneg (t - M.t₀)) (2 + M.δ)
    have h1 : min c₀ c₅ * ‖z‖ * angle z (slopeVec t) ^ 2 ≤
        c₅ * ‖z‖ * angle z (slopeVec t) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hz0) hA
    have h2 : C₅ * ‖z‖ * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ max C C₅ * ‖z‖ * ‖t - M.t₀‖ ^ (2 + M.δ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hz0) hT
    linarith

end CurvatureVariance.Paper.Proofs.Geometry
