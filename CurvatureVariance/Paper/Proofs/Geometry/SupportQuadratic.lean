/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
public import CurvatureVariance.Paper.Proofs.Geometry.PosDef

/-!
# The supporting hyperplanes: the quadratic bound `eq:support`

Equation `eq:support` (Lemma `lem:support`): for `|t − t₀|, |h|` small and a subgradient `P_t` of
`μ` at `(1, t)`,
`c|h|² − C|t − t₀|^{2+δ} ≤ μ(1,t+h) − P_t·(1,t+h) ≤ C|h|² + C|t − t₀|^{2+δ}`. As in the proof of
Lemma `lem:support`: by the subgradient inequality at `t + h/2` and at `t − h`, the middle term lies
between the second differences `μ(1,t+h) − 2μ(1,t+h/2) + μ(1,t)` and
`μ(1,t+h) + μ(1,t−h) − 2μ(1,t)`. Written with the expansion of equation `eq:curvature` at `(1, t₀)`,
their affine parts `p₀·(·)` cancel, their quadratic parts are `q₀(h)/2` and `2 q₀(h)` (the polar
identities of a quadratic form), and their remainders are `O(|h|^{2+δ} + |t − t₀|^{2+δ})`. The
bounds `λ|h|² ≤ q₀(h) ≤ Λ|h|²` (`Proofs.Geometry.PosDef`) and `|h|^{2+δ} ≤ |h|² r₁^δ` for a small
radius `r₁` absorb the first remainder (`support_quadratic`, with `c = λ/4`).
-/

@[expose] public section

open InnerProductGeometry

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper

variable {m : ℕ}

theorem slopeVec_add_add_slopeVec_sub (t h : EuclideanSpace ℝ (Fin m)) :
    slopeVec (t + h) + slopeVec (t - h) = (2 : ℝ) • slopeVec t := by
  apply WithLp.ofLp_injective
  simp only [slopeVec, WithLp.ofLp_add, WithLp.ofLp_smul, Prod.mk_add_mk,
    Prod.smul_mk, smul_eq_mul]
  refine Prod.ext (by norm_num) ?_
  simp only
  rw [two_smul]
  abel

theorem slopeVec_add_eq (t h : EuclideanSpace ℝ (Fin m)) :
    slopeVec (t + h) = (2 : ℝ) • slopeVec (t + (1 / 2 : ℝ) • h) - slopeVec t := by
  apply WithLp.ofLp_injective
  simp only [slopeVec, WithLp.ofLp_sub, WithLp.ofLp_smul, WithLp.ofLp_toLp, Prod.mk_sub_mk,
    Prod.smul_mk, smul_eq_mul]
  refine Prod.ext (by norm_num) ?_
  simp only
  module

/-- `x^q ≤ 8 (a^q + b^q)` for `0 ≤ x ≤ a + b` and `0 ≤ q ≤ 3`. -/
theorem rpow_le_eight_mul_add {a b x q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx0 : 0 ≤ x)
    (hx : x ≤ a + b) (hq0 : 0 ≤ q) (hq : q ≤ 3) :
    x ^ q ≤ 8 * (a ^ q + b ^ q) := by
  have hmax : x ≤ 2 * max a b := by
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have hm0 : 0 ≤ max a b := le_max_of_le_left ha
  calc x ^ q ≤ (2 * max a b) ^ q := Real.rpow_le_rpow hx0 hmax hq0
    _ = 2 ^ q * max a b ^ q := Real.mul_rpow (by norm_num) hm0
    _ ≤ 8 * (a ^ q + b ^ q) := by
        have h2 : (2 : ℝ) ^ q ≤ 8 := by
          calc (2 : ℝ) ^ q ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
            _ = 8 := by norm_num
        have hmq : max a b ^ q ≤ a ^ q + b ^ q := by
          rcases le_total a b with h | h
          · rw [max_eq_right h]
            linarith [Real.rpow_nonneg ha q]
          · rw [max_eq_left h]
            linarith [Real.rpow_nonneg hb q]
        have := Real.rpow_nonneg hm0 q
        calc 2 ^ q * max a b ^ q ≤ 8 * max a b ^ q := mul_le_mul_of_nonneg_right h2 this
          _ ≤ 8 * (a ^ q + b ^ q) := mul_le_mul_of_nonneg_left hmq (by norm_num)

/-- **Equation `eq:support`** (Lemma `lem:support`, and its proof): for valid
bounds `bd` there are `c, r₁, C > 0` such that for every model fitting `bd`, `|t − t₀| ≤ r₁`,
`|h| ≤ r₁` and every subgradient `p` of `μ` at `(1, t)`,
`c|h|² − C|t − t₀|^{2+δ} ≤ μ(1,t+h) − p·(1,t+h) ≤ C|h|² + C|t − t₀|^{2+δ}`. Here `c = λ/4` with
`λ = bd.lam`, the lower bound of `q₀` on the unit sphere, and `Λ = bd.Lam`, `bd.Crem`, `bd.rrem`
give the other constants. -/
theorem support_quadratic {bd : Bounds m} (hbd : bd.Valid) :
    ∃ c r₁ C : ℝ, 0 < c ∧ 0 < r₁ ∧ 0 < C ∧ ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ t h : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
        ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
          c * ‖h‖ ^ 2 - C * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
              M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
              C * ‖h‖ ^ 2 + C * ‖t - M.t₀‖ ^ (2 + M.δ) := by
  have hδ := hbd.law.delta_pos
  set lam := bd.lam with hlamdef
  set Lam := bd.Lam with hLamdef
  have hlam : 0 < lam := hbd.lam_pos
  have hLam : 0 ≤ Lam := hbd.Lam_nonneg
  set K := bd.Crem with hKdef
  have hK : 0 ≤ K := hbd.Crem_nonneg
  -- the radius
  set ρ := (lam / (128 * K + 1)) ^ (1 / bd.law.δ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  set r₁ := min (bd.rrem / 2) ρ with hr₁
  have hr₁0 : 0 < r₁ := lt_min (by linarith [hbd.rrem_pos]) hρ0
  have hr₁a : r₁ ≤ bd.rrem / 2 := min_le_left _ _
  have hr₁c : r₁ ≤ ρ := min_le_right _ _
  have hsmall' : r₁ ^ bd.law.δ ≤ lam / (128 * K + 1) := by
    calc r₁ ^ bd.law.δ ≤ ρ ^ bd.law.δ := Real.rpow_le_rpow hr₁0.le hr₁c hδ.le
      _ = lam / (128 * K + 1) := by
          rw [hρ, ← Real.rpow_mul (by positivity), one_div_mul_cancel hδ.ne', Real.rpow_one]
  refine ⟨lam / 4, r₁, 2 * Lam + lam + 32 * K + 1, by positivity, hr₁0, by positivity,
    fun M hM hfit t h ht hh p hp => ?_⟩
  have hδM : M.δ = bd.law.δ := hfit.δ_eq
  have hδ : 0 < M.δ := hM.delta_pos
  have hδ1 : M.δ ≤ 1 := hM.delta_le_one
  have hsmall : r₁ ^ M.δ ≤ lam / (128 * K + 1) := hδM ▸ hsmall'
  have hlow : ∀ h, lam * ‖h‖ ^ 2 ≤ M.q₀ h := hfit.q₀_lower
  set q := 2 + M.δ with hq
  set f : EuclideanSpace ℝ (Fin m) → ℝ := fun s => M.μ.1 (slopeVec s) with hf
  -- the remainder of equation `eq:curvature`, at the offset `s` from `t₀`
  have hrem : ∀ s : EuclideanSpace ℝ (Fin m), ‖s‖ ≤ bd.rrem →
      |f (M.t₀ + s) - f M.t₀ - inner ℝ M.p₀ s - M.q₀ s| ≤ K * ‖s‖ ^ q := fun s hs =>
    (hM.curvature s (hs.trans hfit.rrem_le)).trans
      (mul_le_mul_of_nonneg_right hfit.Crem_le (Real.rpow_nonneg (norm_nonneg _) _))
  set τ := t - M.t₀ with hτdef
  have hq0 : 0 ≤ q := by linarith
  have hq3 : q ≤ 3 := by linarith
  -- the powers of the offsets used
  have hpow : ∀ s : EuclideanSpace ℝ (Fin m), ‖s‖ ≤ ‖τ‖ + ‖h‖ →
      ‖s‖ ^ q ≤ 8 * (‖τ‖ ^ q + ‖h‖ ^ q) := fun s hs =>
    rpow_le_eight_mul_add (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hs hq0 hq3
  have hhq : ‖h‖ ^ q ≤ r₁ ^ M.δ * ‖h‖ ^ 2 := by
    rw [hq, Real.rpow_add' (norm_nonneg _) (by linarith), Real.rpow_two, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) hh hδ.le) (sq_nonneg _)
  have htq : 0 ≤ ‖τ‖ ^ q := Real.rpow_nonneg (norm_nonneg _) _
  have hhq0 : 0 ≤ ‖h‖ ^ q := Real.rpow_nonneg (norm_nonneg _) _
  -- remainders at the offsets `τ + h`, `τ − h`, `τ + h/2`, `τ`
  have hn1 : ‖τ + h‖ ≤ ‖τ‖ + ‖h‖ := norm_add_le _ _
  have hn2 : ‖τ - h‖ ≤ ‖τ‖ + ‖h‖ := norm_sub_le _ _
  have hn3 : ‖τ + (1 / 2 : ℝ) • h‖ ≤ ‖τ‖ + ‖h‖ := by
    have := norm_add_le τ ((1 / 2 : ℝ) • h)
    rw [norm_smul] at this
    have : ‖(1 / 2 : ℝ)‖ * ‖h‖ ≤ ‖h‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
      linarith [norm_nonneg h]
    linarith
  have hn0 : ‖τ‖ ≤ ‖τ‖ + ‖h‖ := by linarith [norm_nonneg h]
  have hR1 := hrem (τ + h) (by linarith)
  have hR2 := hrem (τ - h) (by linarith)
  have hR3 := hrem (τ + (1 / 2 : ℝ) • h) (by linarith)
  have hR0 := hrem τ (by linarith)
  have e1 : M.t₀ + (τ + h) = t + h := by rw [hτdef]; abel
  have e2 : M.t₀ + (τ - h) = t - h := by rw [hτdef]; abel
  have e3 : M.t₀ + (τ + (1 / 2 : ℝ) • h) = t + (1 / 2 : ℝ) • h := by rw [hτdef]; abel
  have e0 : M.t₀ + τ = t := by rw [hτdef]; abel
  clear_value τ
  rw [e1] at hR1
  rw [e2] at hR2
  rw [e3] at hR3
  rw [e0] at hR0
  have hp1 := hpow _ hn1
  have hp2 := hpow _ hn2
  have hp3 := hpow _ hn3
  have hp0 := hpow _ hn0
  rw [abs_le] at hR1 hR2 hR3 hR0
  -- the affine part cancels in both second differences
  have hlpar : inner ℝ M.p₀ (τ + h) + inner ℝ M.p₀ (τ - h) = 2 * inner ℝ M.p₀ τ := by
    rw [inner_add_right, inner_sub_right]
    ring
  have hlmid : inner ℝ M.p₀ (τ + h) - 2 * inner ℝ M.p₀ (τ + (1 / 2 : ℝ) • h) +
      inner ℝ M.p₀ τ = 0 := by
    rw [inner_add_right, inner_add_right, inner_smul_right]
    ring
  -- the quadratic parts are `2 q₀(h)` and `q₀(h)/2`
  have hqpar : M.q₀ (τ + h) + M.q₀ (τ - h) = 2 * M.q₀ τ + 2 * M.q₀ h := by
    rw [QuadraticMap.map_add M.q₀ τ h, sub_eq_add_neg, QuadraticMap.map_add M.q₀ τ (-h),
      QuadraticMap.map_neg, QuadraticMap.polar_neg_right]
    ring
  have hqmid : M.q₀ (τ + h) - 2 * M.q₀ (τ + (1 / 2 : ℝ) • h) + M.q₀ τ = M.q₀ h / 2 := by
    rw [QuadraticMap.map_add M.q₀ τ h, QuadraticMap.map_add M.q₀ τ ((1 / 2 : ℝ) • h),
      QuadraticMap.map_smul, QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul]
    ring
  have hqlow := hlow h
  have hqup : M.q₀ h ≤ Lam * ‖h‖ ^ 2 := hfit.q₀_upper h
  -- the subgradient inequalities
  have hsub1 : 2 * f t - f (t - h) ≤ inner ℝ p (slopeVec (t + h)) := by
    have h1 := hp.2 (slopeVec (t - h))
    have h2 : inner ℝ p (slopeVec (t + h)) + inner ℝ p (slopeVec (t - h)) = 2 * f t := by
      rw [← inner_add_right, slopeVec_add_add_slopeVec_sub, inner_smul_right, hp.1]
    simp only [hf]
    linarith
  have hsub2 : inner ℝ p (slopeVec (t + h)) ≤ 2 * f (t + (1 / 2 : ℝ) • h) - f t := by
    have h1 := hp.2 (slopeVec (t + (1 / 2 : ℝ) • h))
    rw [slopeVec_add_eq t h, inner_sub_right, inner_smul_right, hp.1]
    simp only [hf]
    linarith
  -- the absorption of `‖h‖^{2+δ}`
  have hKs : 32 * K * ‖h‖ ^ q ≤ lam / 4 * ‖h‖ ^ 2 := by
    have h1 : 32 * K * r₁ ^ M.δ ≤ lam / 4 := by
      calc 32 * K * r₁ ^ M.δ ≤ 32 * K * (lam / (128 * K + 1)) :=
            mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ ≤ lam / 4 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith only [hlam]
    calc 32 * K * ‖h‖ ^ q ≤ 32 * K * (r₁ ^ M.δ * ‖h‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hhq (by positivity)
      _ = (32 * K * r₁ ^ M.δ) * ‖h‖ ^ 2 := by ring
      _ ≤ lam / 4 * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hKt := mul_le_mul_of_nonneg_left hp0 hK
  have hK1 := mul_le_mul_of_nonneg_left hp1 hK
  have hK2 := mul_le_mul_of_nonneg_left hp2 hK
  have hK3 := mul_le_mul_of_nonneg_left hp3 hK
  have hCT : 32 * K * ‖τ‖ ^ q ≤ (2 * Lam + lam + 32 * K + 1) * ‖τ‖ ^ q :=
    mul_le_mul_of_nonneg_right (by linarith) htq
  have hCh : (2 * Lam + lam / 4) * ‖h‖ ^ 2 ≤ (2 * Lam + lam + 32 * K + 1) * ‖h‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  constructor
  · simp only [hf] at hR1 hR3 hR0 hsub2 ⊢
    linarith
  · simp only [hf] at hR1 hR2 hR0 hsub1 ⊢
    linarith

end CurvatureVariance.Paper.Proofs.Geometry
