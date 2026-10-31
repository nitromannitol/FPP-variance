/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.Geometry.SlabPaths

/-!
# Proposition `prop:profiles`: the connectors, the links and `eq:profiledifference`

* `abs_passageTime_sub_le`: for the connector endpoints `a, z` of `I` and `z', a'` of `I'`, the
  upper bound `T(u, v) ≤ T(u, z) + T(z, z') + T(z', v)` and the lower bound
  `T(a, a') ≤ T(a, u) + T(u, v) + T(v, a')`; the linear terms `P_t · ( )` telescope, and
  `P_t·(v − u) ≤ μ(v − u)`, `P_t·(a' − a) ≤ μ(a' − a)`.
* `abs_slabTimeReal_sub_le`: `|D − μ| ≤ |T − μ| + (D − T)` when `T ≤ D < ∞`.
* The numerical conditions of the links (`link_slope_le`, `link_margin_le`) and the threshold
  for `s` (`exists_large_scale`).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ### At a fixed outcome -/

/-- **The two-sided bound at a fixed outcome**, from the connectors and the two links. -/
theorem abs_passageTime_sub_le {M : Model m} {P : Pt m} (hsub : ∀ x, inner ℝ P x ≤ M.μ.1 x)
    (ω : Config m) {a z z' a' u v : Vertex m} {xI xI' l₁ l₂ κ : ℝ}
    (h1 : passageTimeReal ω a u - inner ℝ P (point u - point a) ≤ xI)
    (h2 : passageTimeReal ω u z - inner ℝ P (point z - point u) ≤ xI)
    (h3 : passageTimeReal ω z' v - inner ℝ P (point v - point z') ≤ xI')
    (h4 : passageTimeReal ω v a' - inner ℝ P (point a' - point v) ≤ xI')
    (hl₁ : |passageTimeReal ω z z' - M.μ.1 (point z' - point z)| ≤ l₁)
    (hl₂ : |passageTimeReal ω a a' - M.μ.1 (point a' - point a)| ≤ l₂)
    (hκ₁ : M.μ.1 (point z' - point z) - inner ℝ P (point z' - point z) ≤ κ)
    (hκ₂ : M.μ.1 (point v - point u) - inner ℝ P (point v - point u) ≤ κ) :
    |passageTimeReal ω u v - M.μ.1 (point v - point u)| ≤ xI + xI' + l₁ + l₂ + κ := by
  have t1 := Moments.passageTimeReal_triangle ω u z v
  have t2 := Moments.passageTimeReal_triangle ω z z' v
  have t3 := Moments.passageTimeReal_triangle ω a u a'
  have t4 := Moments.passageTimeReal_triangle ω u v a'
  have s1 := hsub (point v - point u)
  have s2 := hsub (point a' - point a)
  have hl₁' := abs_le.mp hl₁
  have hl₂' := abs_le.mp hl₂
  have hl₁0 := (abs_nonneg _).trans hl₁
  have hl₂0 := (abs_nonneg _).trans hl₂
  simp only [inner_sub_right] at h1 h2 h3 h4 s1 s2 hκ₁ hκ₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `|D − μ| ≤ |T − μ| + (D − T)` when `T ≤ D < ∞`. -/
theorem abs_slabTimeReal_sub_le {ω : Config m} {u v : Vertex m} {x y c : ℝ}
    (hT : (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v)
    (hD : slabTime ω u.1 v.1 u v ≠ ⊤)
    (hpd : slabTimeReal ω u.1 v.1 u v - passageTimeReal ω u v ≤ y)
    (hx : |passageTimeReal ω u v - c| ≤ x) : |slabTimeReal ω u.1 v.1 u v - c| ≤ x + y := by
  have h1 : passageTimeReal ω u v ≤ slabTimeReal ω u.1 v.1 u v := by
    have h := ENNReal.toReal_mono hD hT
    rw [ENNReal.coe_toReal] at h
    exact h
  have hx' := abs_le.mp hx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The slab passage time across a slab of width at least two is finite: the coordinate path
through the level `u₁ + 1` stays in the slab. -/
theorem slabTime_ne_top (ω : Config m) {u v : Vertex m} (h : u.1 + 2 ≤ v.1) :
    slabTime ω u.1 v.1 u v ≠ ⊤ := by
  have hedges := Geometry.slabPath_edges_mem (p := u.1) (q := v.1) (c := u.1 + 1) le_rfl (by omega)
    (by omega) le_rfl (by omega) (by omega)
  have hD : slabTime ω u.1 v.1 u v ≤ (walkCost ω (Geometry.slabPath u v (u.1 + 1)) : ℝ≥0∞) :=
    iInf₂_le _ hedges
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hD

/-! ### Numerical conditions -/

/-- The slope condition of a link of length `λ ≤ 2s`: `λ τ ≤ (24/25) λ^{3/4+δ/100}` for
`τ ≤ (4/5) s^{δ/100−1/4}` (used with `τ = |t − t₀|`). -/
theorem link_slope_le {δ s lam τ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hls : lam ≤ 2 * s) (ht : τ ≤ 4 / 5 * s ^ (δ / 100 - 1 / 4)) :
    lam * τ ≤ 24 / 25 * lam ^ ((3 : ℝ) / 4 + δ / 100) := by
  have h := ht.trans (slope_le_of_le_two_mul hδ hδ1 hlam hls)
  rw [show (3 : ℝ) / 4 + δ / 100 = (δ / 100 - 1 / 4) + 1 by ring, Real.rpow_add hlam,
    Real.rpow_one]
  calc lam * τ ≤ lam * (24 / 25 * lam ^ (δ / 100 - 1 / 4)) :=
        mul_le_mul_of_nonneg_left h hlam.le
    _ = 24 / 25 * (lam ^ (δ / 100 - 1 / 4) * lam) := by ring

/-- The margin condition of a link of length `λ ≥ 10⁴ (1 + T)² d`, `T ≥ 0`:
`(4 + T)√d ≤ (1/25) λ^{3/4+δ/100}` (used with `T = |t₀|`). -/
theorem link_margin_le {δ lam x T : ℝ} (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hlam : 10 ^ 4 * ((1 + T) ^ 2 * ((m : ℝ) + 1)) ≤ lam)
    (hx : x ≤ (4 + T) * Real.sqrt ((m : ℝ) + 1)) :
    x ≤ (1 - 24 / 25) * lam ^ ((3 : ℝ) / 4 + δ / 100) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlam1 : 1 ≤ lam := by nlinarith only [hlam, hm0, hT]
  have h1 : Real.sqrt lam ≤ lam ^ ((3 : ℝ) / 4 + δ / 100) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlam1 (by linarith)
  have h2 : 100 * (1 + T) * Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt lam := by
    calc 100 * (1 + T) * Real.sqrt ((m : ℝ) + 1) =
          Real.sqrt (10 ^ 4 * ((1 + T) ^ 2 * ((m : ℝ) + 1))) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by positivity),
            show (10 : ℝ) ^ 4 = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
            Real.sqrt_sq (by linarith)]
          ring
      _ ≤ Real.sqrt lam := Real.sqrt_le_sqrt hlam
  have h3 : (4 + T) * Real.sqrt ((m : ℝ) + 1) ≤
      1 / 25 * (100 * (1 + T) * Real.sqrt ((m : ℝ) + 1)) := by
    have := Real.sqrt_nonneg ((m : ℝ) + 1)
    nlinarith only [this, hT]
  linarith

/-- The threshold for `s`: `s ≥ 32`, `s ≥ 2·10⁴ (1 + T)² d`, and `s^{-1/5} ≤ ρ/2`. -/
theorem exists_large_scale {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) (T : ℝ) :
    ∃ S₀ : ℝ, 32 ≤ S₀ ∧ 2 * 10 ^ 4 * ((1 + T) ^ 2 * ((m : ℝ) + 1)) ≤ S₀ ∧
      ∀ x : ℝ, S₀ ≤ x → x ^ (-(1 / 5 : ℝ)) ≤ ρ / 2 := by
  obtain ⟨S, hS⟩ := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)).eventually
    (ge_mem_nhds (by linarith : (0 : ℝ) < ρ / 2))).exists_forall_of_atTop
  refine ⟨max (max 32 (2 * 10 ^ 4 * ((1 + T) ^ 2 * ((m : ℝ) + 1)))) S,
    (le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
    fun x hx => hS x ((le_max_right _ _).trans hx)⟩

end CurvatureVariance.Paper.Proofs.ShortLengths
