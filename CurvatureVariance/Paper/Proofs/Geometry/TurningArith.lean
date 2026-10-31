/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Arithmetic of the dyadic chain

Real inequalities used by the induction over dyadic radii in the proof of the cone bounds,
equation `eq:cone` (the proof of Lemma `lem:cone`):

* `turnErr S R = (S / R^{1/2})^{1/2} = S^{1/2} R^{−1/4}`, the fluctuation part of one angular
  increment at radius `R`, with its scaling (`turnErr_two_mul_le`, `turnErr_mul_le_inv`) and its
  smallness above a radius `M S²` (`turnErr_le_of_sq_le`);
* `potential_step`: one step of the potential `P turnErr S R_j + Q j |t − t₀|^{1+δ/2}` that
  dominates the angle at the `j`-th chain point (the induction in the proof of Lemma `lem:cone`),
  for a slope factor `κ` (`slopeFactor T` in use);
* `nat_le_two_mul_of_two_pow_le_exp`: at most `2 L` dyadic radii fit between `S²` and `S² e^L`.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Proofs.Geometry

/-- The fluctuation part of one angular increment at radius `R`: `(S / R^{1/2})^{1/2}`. -/
noncomputable def turnErr (S R : ℝ) : ℝ :=
  Real.sqrt (S / Real.sqrt R)

theorem turnErr_nonneg (S R : ℝ) : 0 ≤ turnErr S R :=
  Real.sqrt_nonneg _

/-- Exact scaling of `turnErr`. -/
theorem turnErr_mul (S : ℝ) {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    turnErr S (c * R) = (Real.sqrt (Real.sqrt c))⁻¹ * turnErr S R := by
  unfold turnErr
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have e1 : S / Real.sqrt (c * R) = (Real.sqrt c)⁻¹ * (S / Real.sqrt R) := by
    rw [Real.sqrt_mul hc.le]; field_simp
  rw [e1, Real.sqrt_mul (inv_nonneg.2 hs.le), Real.sqrt_inv]

/-- Doubling the radius gains a factor `6 / 7`. -/
theorem turnErr_two_mul_le (S : ℝ) {R : ℝ} (hR : 0 < R) :
    turnErr S (2 * R) ≤ 6 / 7 * turnErr S R := by
  rw [turnErr_mul S hR zero_lt_two]
  have h2 : (49 / 36 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have h3 : (7 / 6 : ℝ) ≤ Real.sqrt (Real.sqrt 2) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have h4 : (Real.sqrt (Real.sqrt 2))⁻¹ ≤ 6 / 7 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  exact mul_le_mul_of_nonneg_right h4 (turnErr_nonneg S R)

/-- `turnErr` is antitone in the radius. -/
theorem turnErr_anti {S R R' : ℝ} (hS : 0 ≤ S) (hR : 0 < R) (hRR' : R ≤ R') :
    turnErr S R' ≤ turnErr S R := by
  unfold turnErr
  have h1 : Real.sqrt R ≤ Real.sqrt R' := Real.sqrt_le_sqrt hRR'
  have h0 : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  gcongr

/-- Shrinking the radius by a factor `c ≤ 1` costs at most `c⁻¹`. -/
theorem turnErr_mul_le_inv (S : ℝ) {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (hc1 : c ≤ 1) :
    turnErr S (c * R) ≤ c⁻¹ * turnErr S R := by
  rw [turnErr_mul S hR hc]
  have h1 : c ≤ Real.sqrt c := Real.le_sqrt_of_sq_le (by nlinarith)
  have h2 : Real.sqrt c ≤ Real.sqrt (Real.sqrt c) := Real.le_sqrt_of_sq_le (by
    have := Real.sqrt_le_one.2 hc1
    have := Real.sqrt_nonneg c
    nlinarith)
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hc (h1.trans h2)) (turnErr_nonneg S R)

/-- Above the radius `x⁻⁴ S²`, `turnErr S R ≤ x`. -/
theorem turnErr_le_of_sq_le {S R x : ℝ} (hS : 0 ≤ S) (hR : 0 < R) (hx : 0 ≤ x)
    (h : S ^ 2 ≤ x ^ 4 * R) : turnErr S R ≤ x := by
  unfold turnErr
  rw [Real.sqrt_le_left hx, div_le_iff₀ (Real.sqrt_pos.2 hR)]
  have e : Real.sqrt (x ^ 4 * R) = x ^ 2 * Real.sqrt R := by
    rw [Real.sqrt_mul (by positivity), show x ^ 4 = (x ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg x)]
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hS, e] at this

/-- `turnErr S R = S^{1/2} R^{−1/4}`. -/
theorem turnErr_eq_rpow {S R : ℝ} (hS : 0 ≤ S) (hR : 0 < R) :
    turnErr S R = S ^ ((1 : ℝ) / 2) * R ^ (-(1 : ℝ) / 4) := by
  unfold turnErr
  rw [Real.sqrt_div hS, Real.sqrt_eq_rpow S, Real.sqrt_eq_rpow R,
    Real.sqrt_eq_rpow (R ^ (1 / (2 : ℝ))), ← Real.rpow_mul hR.le, div_eq_mul_inv,
    ← Real.rpow_neg hR.le]
  norm_num

/-- `√(a + b) ≤ √a + √b` for nonnegative `a, b`. -/
theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- `(a + b)^p ≤ 4 (a^p + b^p)` for `a, b ≥ 0` and `0 ≤ p ≤ 2`. -/
theorem add_rpow_le_four {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) (hp2 : p ≤ 2) :
    (a + b) ^ p ≤ 4 * (a ^ p + b ^ p) := by
  have hmax : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  have hM : 0 ≤ max a b := le_max_of_le_left ha
  have h1 : (a + b) ^ p ≤ (2 * max a b) ^ p := Real.rpow_le_rpow (by positivity) hmax hp
  rw [Real.mul_rpow zero_le_two hM] at h1
  have h2 : (2 : ℝ) ^ p ≤ 4 := by
    calc (2 : ℝ) ^ p ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hp2
      _ = 4 := by norm_num
  have h3 : max a b ^ p ≤ a ^ p + b ^ p := by
    rcases max_choice a b with h | h <;> rw [h]
    · linarith [Real.rpow_nonneg hb p]
    · linarith [Real.rpow_nonneg ha p]
  have h4 : 0 ≤ max a b ^ p := Real.rpow_nonneg hM p
  nlinarith

/-- **One step of the potential.** With `X = P turnErr S (2R)` and `Y = Q j τ₀`,
`τ₀ = tn^{1+δ/2}`, and a slope factor `κ > 0`: if `κ X` is below `ε₁` with `ε₁^{δ/2} ≤ η`,
`κ Y ≤ tn`, `4 κ A₂ η ≤ 1/12`, and the new angle `θ` exceeds `X + Y` by at most one angular
increment `A₁ turnErr S R + A₂ (tn + κ (X + Y))^{1+δ/2}`, then
`θ ≤ P turnErr S R + Q (j + 1) τ₀`. -/
theorem potential_step {S R P Q A₁ A₂ η ε₁ δ tn θ j κ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hκ : 0 < κ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hP : 14 * A₁ ≤ P)
    (hQ : 16 * A₂ ≤ Q) (hη : 4 * κ * A₂ * η ≤ 1 / 12) (hε₁ : ε₁ ^ (δ / 2) ≤ η) (htn : 0 ≤ tn)
    (hj : 0 ≤ j) (hX : κ * (P * turnErr S (2 * R)) ≤ ε₁)
    (hY : κ * (Q * j * tn ^ (1 + δ / 2)) ≤ tn)
    (hθ : θ ≤ (P * turnErr S (2 * R) + Q * j * tn ^ (1 + δ / 2)) + A₁ * turnErr S R +
      A₂ * (tn + κ * (P * turnErr S (2 * R) + Q * j * tn ^ (1 + δ / 2))) ^ (1 + δ / 2)) :
    θ ≤ P * turnErr S R + Q * (j + 1) * tn ^ (1 + δ / 2) := by
  set p := 1 + δ / 2 with hp
  set e := turnErr S R with he
  set X := P * turnErr S (2 * R) with hXdef
  set τ₀ := tn ^ p with hτ₀
  set Y := Q * j * τ₀ with hYdef
  have hP0 : 0 ≤ P := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have he0 : 0 ≤ e := turnErr_nonneg S R
  have hX0 : 0 ≤ X := mul_nonneg hP0 (turnErr_nonneg S _)
  have hτ0 : 0 ≤ τ₀ := Real.rpow_nonneg htn p
  have hY0 : 0 ≤ Y := by positivity
  have hp0 : 0 ≤ p := by positivity
  have hp2 : p ≤ 2 := by linarith
  have hκX : 0 ≤ κ * X := mul_nonneg hκ.le hX0
  -- the slope argument of the superlinear term
  have h1 : (tn + κ * (X + Y)) ^ p ≤ (2 * tn + κ * X) ^ p :=
    Real.rpow_le_rpow (by positivity) (by linarith) hp0
  have h2 := add_rpow_le_four (by positivity : 0 ≤ 2 * tn) hκX hp0 hp2
  have h3 : (2 * tn) ^ p ≤ 4 * τ₀ := by
    rw [Real.mul_rpow zero_le_two htn]
    have : (2 : ℝ) ^ p ≤ 4 := by
      calc (2 : ℝ) ^ p ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hp2
        _ = 4 := by norm_num
    exact mul_le_mul_of_nonneg_right this hτ0
  have h4 : (κ * X) ^ p ≤ κ * X * η := by
    rw [hp, Real.rpow_add' hκX (by positivity), Real.rpow_one]
    have : (κ * X) ^ (δ / 2) ≤ η :=
      (Real.rpow_le_rpow hκX hX (by positivity)).trans hε₁
    exact mul_le_mul_of_nonneg_left this hκX
  have hsup' : (tn + κ * (X + Y)) ^ p ≤ 16 * τ₀ + 4 * (κ * X * η) := by
    have := h1.trans h2
    linarith
  have hsup : A₂ * (tn + κ * (X + Y)) ^ p ≤ 16 * A₂ * τ₀ + 4 * κ * A₂ * η * X := by
    have := mul_le_mul_of_nonneg_left hsup' hA₂
    linarith [show A₂ * (16 * τ₀ + 4 * (κ * X * η)) = 16 * A₂ * τ₀ + 4 * κ * A₂ * η * X by ring]
  -- the gain of the doubled radius
  have h6 : X ≤ 6 / 7 * (P * e) := by
    have := mul_le_mul_of_nonneg_left (turnErr_two_mul_le S hR) hP0
    rw [hXdef]; linarith
  have h7 : 4 * κ * A₂ * η * X ≤ X / 12 := by
    have := mul_le_mul_of_nonneg_right hη hX0
    linarith
  have h8 : A₁ * e ≤ P * e / 14 := by
    have := mul_le_mul_of_nonneg_right hP he0
    linarith
  have h9 : 16 * A₂ * τ₀ ≤ Q * τ₀ := mul_le_mul_of_nonneg_right hQ hτ0
  have hY' : Q * (j + 1) * τ₀ = Y + Q * τ₀ := by rw [hYdef]; ring
  rw [hY']
  linarith

/-- At most `2 L` dyadic factors fit below `e^L`. -/
theorem nat_le_two_mul_of_two_pow_le_exp {j : ℕ} {L : ℝ} (h : (2 : ℝ) ^ j ≤ Real.exp L) :
    (j : ℝ) ≤ 2 * L := by
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_pow] at hlog
  have h2 : 1 - (2 : ℝ)⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos two_pos
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

/-- The accumulated slope term of `j ≤ 2 L` steps stays below `tn / κ` when
`tn^{δ/2} L ≤ ε₀` and `2 κ Q ε₀ ≤ 1`: `κ Q j tn^{1+δ/2} ≤ tn`. -/
theorem slope_term_le {Q L ε₀ δ tn j κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hQ : 0 ≤ Q)
    (htn : 0 ≤ tn) (hj : j ≤ 2 * L) (htL : tn ^ (δ / 2) * L ≤ ε₀)
    (hε₀ : 2 * κ * Q * ε₀ ≤ 1) :
    κ * (Q * j * tn ^ (1 + δ / 2)) ≤ tn := by
  have hpow : tn ^ (1 + δ / 2) = tn * tn ^ (δ / 2) := by
    rw [Real.rpow_add' htn (by positivity), Real.rpow_one]
  rw [hpow]
  have ht0 : 0 ≤ tn ^ (δ / 2) := Real.rpow_nonneg htn _
  have e1 : κ * (Q * j * (tn * tn ^ (δ / 2))) ≤ κ * (Q * (2 * L) * (tn * tn ^ (δ / 2))) := by
    gcongr
  have e2 : κ * (Q * (2 * L) * (tn * tn ^ (δ / 2))) = 2 * κ * Q * tn * (tn ^ (δ / 2) * L) := by
    ring
  have e3 : 2 * κ * Q * tn * (tn ^ (δ / 2) * L) ≤ 2 * κ * Q * tn * ε₀ :=
    mul_le_mul_of_nonneg_left htL (by positivity)
  have e4 : 2 * κ * Q * tn * ε₀ ≤ tn := by
    have := mul_le_mul_of_nonneg_right hε₀ htn
    linarith [show 2 * κ * Q * tn * ε₀ = 2 * κ * Q * ε₀ * tn by ring]
  linarith

end CurvatureVariance.Paper.Proofs.Geometry
