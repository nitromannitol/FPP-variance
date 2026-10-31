/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusEvents
public import CurvatureVariance.Paper.Proofs.Localization.ModulusCover
public import CurvatureVariance.Paper.Proofs.Localization.ModulusNumbers
public import CurvatureVariance.Paper.Proofs.Localization.ModulusExcess
import CurvatureVariance.Paper.Proofs.Localization.Common
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry
import Mathlib.Tactic.Linarith

/-!
# Lemma `lem:modulus` at fixed parameters

The proof of Lemma `lem:modulus` for one admissible configuration of parameters. With `s = ⌈gℓ⌉`:
Proposition `prop:profiles` in its first case on the pairs of cubes of side `(gℓQ_{gℓ})^{1/2}` at
length `s`, with `b = 1`, and in its second case on `I × I'`, equations `eq:support` and
`eq:scales`, equation `eq:union` and the moment of order `16d` of Lemma `lem:localization` give
`‖Z‖_{8d} ≤ C(b)(g + g^{1/3} log(2/g)) Q_ℓ`, for endpoints moved by at most `h W_ℓ`, `h = g⁴`.

* `offset_le`, `box_facts`, `box_index_le`: the boxes that hold the first and the last vertex;
* `abs_supportExcess_endpoints_le`: the change of `φ` at the two points;
* `supportExcess_le_on_pair`: the bound of `φ` on `I × I'`;
* `modulus_fixed`: the assembly.

The steps on the boxes and on `φ` are at the length `s = ⌈gℓ⌉` and on the balls of radius
`g⁻¹ W_ℓ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-! ## The constants -/

/-- The constant of the transverse offset: `σ + (1 + T) g⁻¹ W ≤ C₂ g⁻¹ W`. -/
noncomputable def offsetConst (m : ℕ) (T b : ℝ) : ℝ := T * (2 * m * (b + 3) + 2)

/-- The constant `C(b)` of the change of `φ`. -/
noncomputable def moveConst (m : ℕ) (T b Cs : ℝ) : ℝ := 2 * Cs * offsetConst m T b ^ 2 + 3 * Cs

/-- The constant `C(b)` of the bound of `φ` on `I × I'`. -/
noncomputable def pairConst (m : ℕ) (b Cs : ℝ) : ℝ := 2 * Cs * m ^ 2 * (b + 1) ^ 2 + 3 * Cs

/-- The constant `C(b)` of the total bound `C(b)(g + g^{1/3} log(2/g)) Q_ℓ`. It does not depend on
`g`. -/
noncomputable def rateConst (m : ℕ) (T b C₁ Cb Cs Cr CU : ℝ) : ℝ :=
  momentConst (8 * (m + 1)) * 4 * CU * C₁ * logConst m T b + 2 * moveConst m T b Cs +
    (momentConst (2 * (8 * (m + 1))) * 2 * Cb + pairConst m b Cs) * Cr

theorem moveConst_pos (m : ℕ) (T b : ℝ) {Cs : ℝ} (hCs : 0 < Cs) : 0 < moveConst m T b Cs := by
  unfold moveConst
  have : 0 ≤ 2 * Cs * offsetConst m T b ^ 2 := by positivity
  linarith only [this, hCs]

theorem pairConst_pos (m : ℕ) (b : ℝ) {Cs : ℝ} (hCs : 0 < Cs) : 0 < pairConst m b Cs := by
  unfold pairConst
  have : 0 ≤ 2 * Cs * m ^ 2 * (b + 1) ^ 2 := by positivity
  linarith only [this, hCs]

theorem rateConst_pos (m : ℕ) {T b C₁ Cb Cs Cr CU : ℝ} (hT : 1 ≤ T) (hb : 1 ≤ b) (hC₁ : 0 < C₁)
    (hCb : 0 < Cb) (hCs : 0 < Cs) (hCr : 0 ≤ Cr) (hCU : 0 < CU) :
    0 < rateConst m T b C₁ Cb Cs Cr CU := by
  unfold rateConst
  have h1 := momentConst_pos (8 * (m + 1))
  have h2 := momentConst_pos (2 * (8 * (m + 1)))
  have h3 := moveConst_pos m T b hCs
  have h4 := pairConst_pos m b hCs
  have h5 := logConst_nonneg m hT hb
  have hA : 0 ≤ momentConst (8 * (m + 1)) * 4 * CU * C₁ * logConst m T b :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1.le (by norm_num)) hCU.le) hC₁.le) h5
  have hC : 0 ≤ (momentConst (2 * (8 * (m + 1))) * 2 * Cb + pairConst m b Cs) * Cr :=
    mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg h2.le (by norm_num)) hCb.le) h4.le) hCr
  linarith only [hA, hC, h3]

/-! ## The boxes -/

/-- The transverse offset of the two points, with `σ = 2 m ρ` and `ρ = T(2/g + b + 1) W`. -/
theorem offset_le {mr T b g Wl : ℝ} (hm : 0 ≤ mr) (hT : 1 ≤ T) (hb : 1 ≤ b) (hg : 0 < g)
    (hg1 : g ≤ 1) (hWl : 0 ≤ Wl) :
    2 * mr * (T * (2 / g + b + 1) * Wl) + (1 + T) * (g⁻¹ * Wl) ≤
      T * (2 * mr * (b + 3) + 2) * (g⁻¹ * Wl) := by
  have hginv1 : 1 ≤ g⁻¹ := one_le_inv_iff₀.mpr ⟨hg, hg1⟩
  have hT0 : 0 ≤ T := by linarith only [hT]
  have h1 : 2 / g + b + 1 ≤ (b + 3) * g⁻¹ := by
    rw [div_eq_mul_inv]; nlinarith only [hginv1, hb]
  have hW0 : 0 ≤ g⁻¹ * Wl := mul_nonneg (by linarith only [hginv1]) hWl
  have k1 : 2 * mr * (T * (2 / g + b + 1) * Wl) ≤ 2 * mr * (T * ((b + 3) * g⁻¹) * Wl) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hT0) hWl)
      (mul_nonneg zero_le_two hm)
  have k2 : (1 + T) * (g⁻¹ * Wl) ≤ 2 * T * (g⁻¹ * Wl) :=
    mul_le_mul_of_nonneg_right (by linarith only [hT]) hW0
  have e : T * (2 * mr * (b + 3) + 2) * (g⁻¹ * Wl) =
      2 * mr * (T * ((b + 3) * g⁻¹) * Wl) + 2 * T * (g⁻¹ * Wl) := by ring
  rw [e]
  linarith only [k1, k2]

/-- The boxes of half-side `ρ = T(2/g + b + 1) W` hold the first and the last vertex. -/
theorem box_facts {T b g Wl a a' e : ℝ} (hT : 1 ≤ T) (hb : 1 ≤ b) (hg : 0 < g) (hWl0 : 0 < Wl)
    (ha : a ≤ b * Wl) (ha' : a' ≤ b * Wl) (he : 4 * e ≤ Wl) :
    (1 + T) * (g⁻¹ * Wl) + max a a' / 2 + 4 * e ≤ T * (2 / g + b + 1) * Wl ∧
      a ≤ 2 * (T * (2 / g + b + 1) * Wl) ∧ a' ≤ 2 * (T * (2 / g + b + 1) * Wl) := by
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hT1 := sub_nonneg.2 hT
  have hgi : 0 ≤ g⁻¹ * Wl := by positivity
  have hmax : max a a' ≤ b * Wl := max_le ha ha'
  have h1 : (1 + T) * (g⁻¹ * Wl) ≤ T * (2 / g) * Wl := by
    rw [div_eq_mul_inv]
    linarith only [mul_nonneg hT1 hgi]
  have hbW : 0 ≤ b * Wl := mul_nonneg hb0 hWl0.le
  have k2 : b * Wl ≤ T * b * Wl := by linarith only [mul_nonneg hT1 hbW]
  have k3 : Wl ≤ T * Wl := by linarith only [mul_nonneg hT1 hWl0.le]
  have e1 : T * (2 / g + b + 1) * Wl = T * (2 / g) * Wl + T * b * Wl + T * Wl := by ring
  have hg2 : 0 ≤ T * (2 / g) * Wl := by
    have : 0 ≤ T := by linarith only [hT]
    positivity
  rw [e1]
  refine ⟨by linarith only [h1, hmax, k2, k3, he, hbW], ?_, ?_⟩ <;>
    linarith only [ha, ha', k2, k3, hg2, hbW, hWl0]

/-- The grid of cubes of side `s₀ ≥ g W` covers the boxes. -/
theorem box_index_le {T b g Wl s₀ : ℝ} (hT : 1 ≤ T) (hb : 1 ≤ b) (hg : 0 < g) (hs₀ : 0 < s₀)
    (hWratio : Wl ≤ g⁻¹ * s₀) :
    T * (2 / g + b + 1) * Wl / s₀ + 1 / 2 ≤ gridSize T b g := by
  refine le_trans ?_ (le_gridSize T b g)
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hg2 : 0 ≤ 2 / g := by positivity
  have hgb : 0 ≤ T * (2 / g + b + 1) :=
    mul_nonneg hT0 (by linarith only [hg2, hb])
  have h : Wl ≤ 2 / g * s₀ := by
    have hgi : 0 ≤ g⁻¹ * s₀ := by positivity
    rw [div_eq_mul_inv]
    linarith only [hWratio, hgi]
  have : T * (2 / g + b + 1) * Wl / s₀ ≤ T * (2 / g + b + 1) * (2 / g) := by
    rw [div_le_iff₀ hs₀, mul_assoc (T * (2 / g + b + 1))]
    exact mul_le_mul_of_nonneg_left h hgb
  linarith only [this]

/-- The offset from the line of slope `t` of two vertices near a line, at transverse distance `ρ`
in each coordinate. -/
theorem norm_offset_le {x u : Vertex m} {z t : EuclideanSpace ℝ (Fin m)} {L ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hx : ∀ j, |(x.2 j : ℝ) - z j| ≤ ρ) (hu : ∀ j, |(u.2 j : ℝ) - (z j - L * t j)| ≤ ρ) :
    ‖(point x - point u).snd - L • t‖ ≤ 2 * m * ρ := by
  have e1 : 2 * (m : ℝ) * ρ = m * (2 * ρ) := by ring
  rw [e1]
  refine norm_le_of_forall_abs_le (mul_nonneg zero_le_two hρ0) fun j => ?_
  simp only [WithLp.sub_snd, Infra.FPP.point_snd, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    Infra.FPP.transversePoint_apply]
  have e2 : (x.2 j : ℝ) - u.2 j - L * t j =
      ((x.2 j : ℝ) - z j) - ((u.2 j : ℝ) - (z j - L * t j)) := by ring
  rw [e2]
  have := abs_sub ((x.2 j : ℝ) - z j) ((u.2 j : ℝ) - (z j - L * t j))
  linarith only [this, hx j, hu j]

/-- **The change of `φ` at the two points**: with `σ = 2 m ρ`, a bound `hmove` for a move at
transverse offset `σ` gives the bound at `x − u` for `x` in the box at `s` from `I`, and at
`v − x'` for `x'` in the box at `s` from `I'`. -/
theorem abs_supportExcess_endpoints_le {μ : PtNorm m} {P₀ : Pt m} {p : ℤ} {ℓ s : ℕ}
    {c c' t : EuclideanSpace ℝ (Fin m)} {a a' ρ σ w₀ D : ℝ} (hρ0 : 0 ≤ ρ) (ha : a ≤ 2 * ρ)
    (ha' : a' ≤ 2 * ρ) (hσ : σ = 2 * m * ρ)
    (hmove : ∀ y w : Pt m, y.fst = s → ‖y.snd - (s : ℝ) • t‖ ≤ σ → ‖w‖ ≤ w₀ →
      |supportExcess μ P₀ (y + w) - supportExcess μ P₀ y| ≤ D) :
    (∀ u ∈ transverseCube p c a, ∀ u₂ ∈ transverseCube p c a, ‖point u - point u₂‖ ≤ w₀ →
      ∀ x ∈ transverseCube (p + s) (c + (s : ℝ) • t) (2 * ρ),
        |supportExcess μ P₀ (point x - point u₂) - supportExcess μ P₀ (point x - point u)| ≤ D) ∧
    (∀ v ∈ transverseCube (p + ℓ) c' a', ∀ v₂ ∈ transverseCube (p + ℓ) c' a',
      ‖point v - point v₂‖ ≤ w₀ →
      ∀ x ∈ transverseCube (p + ((ℓ : ℤ) - s)) (c' - (s : ℝ) • t) (2 * ρ),
        |supportExcess μ P₀ (point v₂ - point x) - supportExcess μ P₀ (point v - point x)| ≤
          D) := by
  constructor
  · intro u hu u₂ _ huu x hx
    have hyL : (point x - point u).fst = s := by
      simp only [WithLp.sub_fst, Infra.FPP.point_fst, hx.1, hu.1]; push_cast; ring
    have hx' : ∀ j, |(x.2 j : ℝ) - (c + (s : ℝ) • t) j| ≤ ρ := by
      intro j
      have := hx.2 j; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this ⊢
      linarith only [this]
    have hu' : ∀ j, |(u.2 j : ℝ) - ((c + (s : ℝ) • t) j - s * t j)| ≤ ρ := by
      intro j
      have := hu.2 j
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [add_sub_cancel_right]
      linarith only [this, ha]
    have hσy := norm_offset_le hρ0 hx' hu'
    rw [← hσ] at hσy
    have := hmove (point x - point u) (point u - point u₂) hyL hσy huu
    have e : point x - point u + (point u - point u₂) = point x - point u₂ := by abel
    rwa [e] at this
  · intro v hv v₂ _ hvv x hx
    have hyL : (point v - point x).fst = s := by
      simp only [WithLp.sub_fst, Infra.FPP.point_fst, hx.1, hv.1]; push_cast; ring
    have hv' : ∀ j, |(v.2 j : ℝ) - c' j| ≤ ρ := by
      intro j; have := hv.2 j; linarith only [this, ha']
    have hx' : ∀ j, |(x.2 j : ℝ) - (c' j - s * t j)| ≤ ρ := by
      intro j
      have := hx.2 j; simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
      linarith only [this]
    have hσy := norm_offset_le hρ0 hv' hx'
    rw [← hσ] at hσy
    have hw : ‖point v₂ - point v‖ ≤ w₀ := by rwa [norm_sub_rev]
    have := hmove (point v - point x) (point v₂ - point v) hyL hσy hw
    have e : point v - point x + (point v₂ - point v) = point v₂ - point x := by abel
    rwa [e] at this

/-- **The bound of `φ` on `I × I'`**: by equations `eq:support` and `eq:scales`,
`φ(v − u) ≤ C(b) Q_ℓ`. -/
theorem supportExcess_le_on_pair {μ : PtNorm m} {P₀ : Pt m} {p : ℤ} {ℓ : ℕ}
    {c c' t t₀ : EuclideanSpace ℝ (Fin m)} {a a' b Cs r₁ δ T Wl Ql ηw : ℝ} (hb : 1 ≤ b)
    (hCs : 0 < Cs) (hℓ0 : (0 : ℝ) < ℓ) (hWl0 : 0 < Wl) (hT : ‖t‖ ≤ T)
    (hup : ∀ h' : EuclideanSpace ℝ (Fin m), ‖h'‖ ≤ r₁ →
      supportExcess μ P₀ (slopeVec (t + h')) ≤ Cs * ‖h'‖ ^ 2 + Cs * ‖t - t₀‖ ^ (2 + δ))
    (ha : a ≤ b * Wl) (ha' : a' ≤ b * Wl)
    (hcc : ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1))
    (hW4 : 4 * Real.sqrt ((m : ℝ) + 1) ≤ Wl) (hWsq : Wl ^ 2 = ℓ * Ql) (hWℓ : Wl ≤ ηw * ℓ)
    (hηw4 : 2 * m * (b + 1) * ηw ≤ r₁) (hcost : (ℓ : ℝ) * ‖t - t₀‖ ^ (2 + δ) ≤ Ql) :
    ∀ u ∈ transverseCube p c a, ∀ v ∈ transverseCube (p + ℓ) c' a',
      supportExcess μ P₀ (point v - point u) ≤ pairConst m b Cs * Ql := by
  intro u hu v hv
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hb1 : 0 ≤ b + 1 := by linarith only [hb]
  have hsq : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
  have hCs2 : 0 ≤ 2 * Cs := by linarith only [hCs]
  have hCs3 : 0 ≤ 3 * Cs := by linarith only [hCs]
  set σI := m * (b * Wl + 2 * Real.sqrt ((m : ℝ) + 1)) with hσIdef
  have hσI0 : 0 ≤ σI := mul_nonneg hm0
    (add_nonneg (mul_nonneg hb0 hWl0.le) (mul_nonneg zero_le_two hsq))
  have hσI : σI ≤ m * (b + 1) * Wl := by
    rw [hσIdef]
    have h2s : 2 * Real.sqrt ((m : ℝ) + 1) ≤ Wl := by linarith only [hW4, hsq]
    linarith only [mul_le_mul_of_nonneg_left h2s hm0]
  have hyL : (point v - point u).fst = ℓ := by
    simp only [WithLp.sub_fst, Infra.FPP.point_fst, hv.1, hu.1]; push_cast; ring
  have hσy : ‖(point v - point u).snd - (ℓ : ℝ) • t‖ ≤ σI := by
    refine norm_le_of_forall_abs_le
      (add_nonneg (mul_nonneg hb0 hWl0.le) (mul_nonneg zero_le_two hsq)) fun j => ?_
    simp only [WithLp.sub_snd, Infra.FPP.point_snd, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, Infra.FPP.transversePoint_apply]
    have hcj := (Moments.ExpArray.abs_apply_le_norm (c' - c - (ℓ : ℝ) • t) j).trans hcc
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hcj
    have e : (v.2 j : ℝ) - u.2 j - ℓ * t j =
        ((v.2 j : ℝ) - c' j) - ((u.2 j : ℝ) - c j) + (c' j - c j - ℓ * t j) := by ring
    rw [e]
    have k1 := abs_add_le (((v.2 j : ℝ) - c' j) - ((u.2 j : ℝ) - c j)) (c' j - c j - ℓ * t j)
    have k2 := abs_sub ((v.2 j : ℝ) - c' j) ((u.2 j : ℝ) - c j)
    linarith only [k1, k2, hv.2 j, hu.2 j, hcj, ha, ha']
  have hsmall : 2 * (σI + (1 + T) * 0) / ℓ ≤ r₁ := by
    have : 2 * (σI + (1 + T) * 0) / ℓ ≤ 2 * m * (b + 1) * ηw := by
      rw [div_le_iff₀ hℓ0]
      have := mul_le_mul_of_nonneg_left hWℓ (mul_nonneg hm0 hb1)
      linarith only [this, hσI]
    linarith only [this, hηw4]
  have hle := supportExcess_le_of_mem_ball hCs.le hup hℓ0 hyL hσy le_rfl
    (div_nonneg hℓ0.le zero_le_two) hT hsmall (z := point v - point u)
    (by rw [sub_self, norm_zero])
  refine hle.trans ?_
  have h1 : 2 * Cs * (σI + (1 + T) * 0) ^ 2 / ℓ ≤ 2 * Cs * m ^ 2 * (b + 1) ^ 2 * Ql := by
    rw [div_le_iff₀ hℓ0, mul_zero, add_zero]
    have : σI ^ 2 ≤ (m * (b + 1) * Wl) ^ 2 := pow_le_pow_left₀ hσI0 hσI 2
    rw [mul_pow, mul_pow, hWsq] at this
    have := mul_le_mul_of_nonneg_left this hCs2
    linarith only [this]
  have h2 : 3 * Cs * ℓ * ‖t - t₀‖ ^ (2 + δ) ≤ 3 * Cs * Ql := by
    have := mul_le_mul_of_nonneg_left hcost hCs3
    linarith only [this]
  unfold pairConst
  linarith only [h1, h2]

/-! ## The assembly -/

/-- `2 S / s ≤ r₁`: the slopes stay within `r₁` of `t`, from `W_ℓ ≤ η ℓ`. -/
theorem small_slope_le {C₂ g s ℓ Wl ηw S r₁ : ℝ} (hC₂ : 0 ≤ C₂) (hg : 0 < g) (hs : 0 < s)
    (hℓ : 0 < ℓ) (hr₁ : 0 ≤ r₁) (hS : S ≤ C₂ * (g⁻¹ * Wl)) (hWl : Wl ≤ ηw * ℓ) (hgs : g * ℓ ≤ s)
    (hηw : 2 * C₂ * ηw ≤ r₁ * g ^ 2) : 2 * S / s ≤ r₁ := by
  rw [div_le_iff₀ hs]
  have hgi : 0 ≤ g⁻¹ := by positivity
  have h1 : C₂ * (g⁻¹ * Wl) ≤ C₂ * (g⁻¹ * (ηw * ℓ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWl hgi) hC₂
  have h2 : 2 * C₂ * ηw * (g⁻¹ * ℓ) ≤ r₁ * g ^ 2 * (g⁻¹ * ℓ) :=
    mul_le_mul_of_nonneg_right hηw (by positivity)
  have e : r₁ * g ^ 2 * (g⁻¹ * ℓ) = r₁ * (g * ℓ) := by field_simp
  have h3 := mul_le_mul_of_nonneg_left hgs hr₁
  have e2 : 2 * C₂ * ηw * (g⁻¹ * ℓ) = 2 * (C₂ * (g⁻¹ * (ηw * ℓ))) := by ring
  linarith only [hS, h1, h2, e, h3, e2]

/-- `g⁻¹ W ≤ s/2`, from `W_ℓ ≤ η ℓ`. -/
theorem radius_le_half {g s ℓ Wl ηw : ℝ} (hg : 0 < g) (hℓ : 0 < ℓ) (hWl : Wl ≤ ηw * ℓ)
    (hgs : g * ℓ ≤ s) (hηw : ηw ≤ g ^ 2 / 2) : g⁻¹ * Wl ≤ s / 2 := by
  have hgi : 0 ≤ g⁻¹ := by positivity
  have h1 : g⁻¹ * Wl ≤ g⁻¹ * (ηw * ℓ) := mul_le_mul_of_nonneg_left hWl hgi
  have h2 : g⁻¹ * (ηw * ℓ) ≤ g⁻¹ * (g ^ 2 / 2 * ℓ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hηw hℓ.le) hgi
  have e : g⁻¹ * (g ^ 2 / 2 * ℓ) = g * ℓ / 2 := by field_simp
  linarith only [h1, h2, e, hgs]

/-- **Lemma `lem:modulus` at fixed parameters** (the proof of Lemma `lem:modulus`). The hypothesis
`hS1` is Proposition `prop:profiles` in its first case at the length `s = ⌈gℓ⌉`, for `gℓ ≤ s ≤ 2gℓ`
and `b = 1`, `hXi` is the same proposition on `I × I'`, `hR` is Lemma `lem:localization` at
`p = 16d`, and `hU` is equation `eq:union`. -/
theorem modulus_fixed (M : Model m) (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {b g Cb C₁ Cr Cs CU r₁ ηw T : ℝ} (hb : 1 ≤ b) (hT : 1 ≤ T) (hg : 0 < g)
    (hg128 : g ≤ 1 / 128) (hCb : 0 < Cb) (hC₁ : 0 < C₁) (hCr : 0 ≤ Cr) (hCs : 0 < Cs)
    (hCU : 0 < CU) (hr₁ : 0 ≤ r₁) (hU : UnionOne CU) {ℓ s : ℕ} (hs0 : 0 < s)
    (hsg : g * ℓ ≤ s) (hs2g : (s : ℝ) ≤ 2 * g * ℓ) (hℓm : 16 * ((m : ℝ) + 1) ≤ ℓ)
    {t : EuclideanSpace ℝ (Fin m)} (ht : ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4))
    (htT : ‖t‖ ≤ T) (hcost : (ℓ : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Q M K A ℓ)
    (hηw1 : ηw * (2 * m * gridSize T b g) ≤ 1 / 4) (hηw2 : ηw ≤ g ^ 2 / 2)
    (hηw3 : 2 * offsetConst m T b * ηw ≤ r₁ * g ^ 2) (hηw4 : 2 * m * (b + 1) * ηw ≤ r₁)
    (hWℓ : W M K A ℓ ≤ ηw * ℓ)
    (hWs : W M K A s ≤ ηw * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100))
    {I I' : Set (Vertex m)} (hII : IsCubePair M K A ℓ b t I I') {P₀ : Pt m}
    (hP₀ : IsSubgradient M.μ (slopeVec t) P₀)
    (hsup : ∀ h' : EuclideanSpace ℝ (Fin m), ‖h'‖ ≤ r₁ →
      supportExcess M.μ P₀ (slopeVec (t + h')) ≤ Cs * ‖h'‖ ^ 2 + Cs * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hgeo : ∀ᵐ ω ∂M.P, ∀ u v : Vertex m, ∃ γ : (latticeGraph m).Walk u v,
      γ.IsPath ∧ walkCost ω γ = passageTime ω u v)
    (hXi : Contracts.ShortConclusion M K A ℓ Cb t I I')
    (hS1 : ∀ (τ : EuclideanSpace ℝ (Fin m)) (J J' : Set (Vertex m)),
      IsCubePair M K A s 1 τ J J' → ‖τ - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
      Contracts.ShortConclusion M K A s C₁ τ J J')
    (hR : ∫⁻ ω, locRadius ω I I' (W M K A ℓ) ^ (2 * (8 * (m + 1))) ∂M.P ≤
      ENNReal.ofReal (Cr ^ (2 * (8 * (m + 1))))) :
    ∃ X : Config m → ℝ, eLpNorm X (8 * (m + 1) : ℕ) M.P ≤
        ENNReal.ofReal (rateConst m T b C₁ Cb Cs Cr CU *
          (g + g ^ ((1 : ℝ) / 3) * Real.log (2 / g)) * Q M K A ℓ) ∧
      ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ u₂ ∈ I, ∀ v ∈ I', ∀ v₂ ∈ I',
        ‖point u - point u₂‖ ≤ g ^ 4 * W M K A ℓ → ‖point v - point v₂‖ ≤ g ^ 4 * W M K A ℓ →
        |passageTimeReal ω u v - passageTimeReal ω u₂ v₂ -
          inner ℝ P₀ (point v - point u - point v₂ + point u₂)| ≤ X ω := by
  obtain ⟨p, c, c', a, a', rfl, rfl, ha0, ha, ha0', ha', hcc⟩ := hII
  have : IsProbabilityMeasure M.P := hM.probP
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  set Wl := W M K A ℓ with hWldef
  set Ql := Q M K A ℓ with hQldef
  set n := gridSize T b g with hndef
  set s₀ := W M K A (g * ℓ) with hs₀def
  -- scales
  have hg2 : g ≤ 1 / 2 := by linarith only [hg128]
  have hg1 : g ≤ 1 := by linarith only [hg128]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith only [hm0]
  have hℓ1 : (1 : ℝ) ≤ ℓ := by linarith only [hℓm, hm1]
  have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hℓ1]
  have hgℓ0 : 0 < g * ℓ := mul_pos hg hℓ0
  have hs0r : (0 : ℝ) < s := by exact_mod_cast hs0
  have hgℓle : 2 * g * ℓ ≤ ℓ / 64 := by
    have := mul_le_mul_of_nonneg_right hg128 hℓ0.le
    linarith only [this]
  have hs16 : 16 * (s : ℝ) ≤ ℓ := by linarith only [hs2g, hgℓle, hℓ0]
  have hsℓ : (s : ℝ) ≤ ℓ := by linarith only [hs16, hs0r]
  have hs2ℓ : 2 * s ≤ ℓ := by
    have : ((2 * s : ℕ) : ℝ) ≤ ℓ := by push_cast; linarith only [hs16, hs0r]
    exact_mod_cast this
  have hWl0 : 0 < Wl := W_pos M hA0 hℓ0
  have hs₀0 : 0 < s₀ := W_pos M hA0 hgℓ0
  have hQl0 : 0 < Ql := Q_pos hA0 hℓ0
  have hWsq : Wl ^ 2 = ℓ * Ql := W_sq M hℓ0.le hA0.le
  have hs₀W : s₀ ≤ W M K A s := Real.sqrt_le_sqrt
    (mul_le_mul hsg (Q_le_Q hM hK hA0.le hgℓ0.le hsg) (Q_nonneg hA0.le hgℓ0.le) hs0r.le)
  have hsq : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
  have hW4 : 4 * Real.sqrt ((m : ℝ) + 1) ≤ Wl := by
    have h1 : Real.sqrt (16 * ((m : ℝ) + 1)) = 4 * Real.sqrt ((m : ℝ) + 1) := by
      rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h1]
    exact (Real.sqrt_le_sqrt hℓm).trans (sqrt_le_W M hM hK hA hℓ1)
  have hWratio : Wl ≤ g⁻¹ * s₀ := by
    have h1 := W_le_div_mul M hM hK hA0 hgℓ0 (mul_le_of_le_one_left hℓ0.le hg1)
    have e : (ℓ : ℝ) / (g * ℓ) = g⁻¹ := by field_simp
    rwa [e] at h1
  have hQs : Q M K A s ≤ g ^ ((1 : ℝ) / 3) * Ql :=
    Q_le_rpow_third M hM hK hA0.le hs0r hg hℓ0 hg128 hs2g
  have hpow0 : 0 ≤ ‖t - M.t₀‖ ^ (2 + M.δ) := Real.rpow_nonneg (norm_nonneg _) _
  have hscost : (s : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Ql :=
    (mul_le_mul_of_nonneg_right hsℓ hpow0).trans hcost
  -- the boxes
  set ρ := T * (2 / g + b + 1) * Wl with hρdef
  obtain ⟨hρ, ha2, ha2'⟩ := box_facts hT hb hg hWl0 ha ha' hW4
  have hρ0 : 0 ≤ ρ := by
    have hT0 : 0 ≤ T := by linarith only [hT]
    have hgi : 0 ≤ 2 / g := by positivity
    exact mul_nonneg (mul_nonneg hT0 (by linarith only [hgi, hb])) hWl0.le
  have hn : ρ / s₀ + 1 / 2 ≤ n := box_index_le hT hb hg hs₀0 hWratio
  -- the variable `D`
  have hθ₁ : 0 < C₁ * Q M K A s := mul_pos hC₁ (Q_pos hA0 hs0r)
  have hY := exists_box_bound M (p := p) (ℓ := ℓ) (c := c) (c' := c') hU hs0 hs₀0 hs₀W hn hθ₁
    (fun k hk k' hk' => grid_slope_le hM.delta_le_one hs0 hs16 ht hs₀0.le (hs₀W.trans hWs) hηw1
      hk hk') hS1
  -- Proposition `prop:profiles` on `I × I'`
  have hℓ1024 : (0 : ℝ) ≤ (ℓ : ℝ) / 1024 := by positivity
  have hXi' : ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (Cb * Ql) X ∧ ∀ᵐ ω ∂M.P,
      ∀ u ∈ transverseCube p c a, ∀ v ∈ transverseCube (p + ℓ) c' a',
        |passageTimeReal ω u v - M.μ.1 (point v - point u)| ≤ X ω := by
    obtain ⟨X, hXO, hXb⟩ := hXi
    exact ⟨X, hXO, hXb.mono fun ω hω u hu v hv => hω.1 u (subset_thicken _ _ hℓ1024 hu)
      v (subset_thicken _ _ hℓ1024 hv)⟩
  -- the move of `φ`
  set σ := 2 * m * ρ with hσdef
  have hSo : σ + (1 + T) * (g⁻¹ * Wl) ≤ offsetConst m T b * (g⁻¹ * Wl) := offset_le hm0 hT hb hg hg1
    hWl0.le
  have hC₂ : 0 ≤ offsetConst m T b := by
    unfold offsetConst
    have hT0 : 0 ≤ T := by linarith only [hT]
    have hb3 : 0 ≤ b + 3 := by linarith only [hb]
    positivity
  have hρL := radius_le_half hg hℓ0 hWℓ hsg hηw2
  have hsmall := small_slope_le hC₂ hg hs0r hℓ0 hr₁ hSo hWℓ hsg hηw3
  obtain ⟨hD₁, hD₂⟩ := abs_supportExcess_endpoints_le (μ := M.μ) (P₀ := P₀) (p := p) (ℓ := ℓ)
    (s := s) (c := c) (c' := c') (t := t) (w₀ := g ^ 4 * Wl)
    (D := moveConst m T b Cs * g * Ql) hρ0 ha2 ha2' hσdef
    (fun y w hy hσy hw => abs_supportExcess_move_le hP₀ hCs hsup hg hg2 hs0r hWl0 hQl0.le htT hρL
      hsmall hSo hWsq hsg hscost hy hσy hw)
  -- `φ` on `I × I'`
  have hFb := supportExcess_le_on_pair (μ := M.μ) (P₀ := P₀) (p := p) (c := c) (c' := c') hb hCs
    hℓ0 hWl0 htT hsup ha ha' hcc hW4 hWsq hWℓ hηw4 hcost
  have hF0 : 0 ≤ pairConst m b Cs * Ql := mul_nonneg (pairConst_pos m b hCs).le hQl0.le
  have hmv := moveConst_pos m T b hCs
  have hD0 : 0 ≤ moveConst m T b Cs * g * Ql := mul_nonneg (mul_nonneg hmv.le hg.le) hQl0.le
  have hl0 : 0 < 2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ) := by positivity
  have hlog0 : 0 < Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ)) := by
    refine Real.log_pos ?_
    have := Nat.cast_nonneg (α := ℝ) (2 * ((2 * n + 1) ^ m) ^ 2)
    linarith only [this]
  have hθ : 0 < CU * (C₁ * Q M K A s) * Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ)) :=
    mul_pos (mul_pos hCU hθ₁) hlog0
  -- the two events
  obtain ⟨X, hXb, hXd⟩ := exists_modulus_bound M hM hs2ℓ hP₀ hWl0 hg hθ
    (mul_pos hCb hQl0) hD0 hF0 hCr hcc htT ha2 ha2' hρ hgeo hY hXi' hD₁ hD₂ hFb hR
  refine ⟨X, hXb.trans (ENNReal.ofReal_le_ofReal ?_), hXd⟩
  -- the numbers
  have hc1 := momentConst_pos (8 * (m + 1))
  have hc2 := momentConst_pos (2 * (8 * (m + 1)))
  have hlc := logConst_nonneg m hT hb
  have hlog := log_pairs_le m hT hb hg hg1
  have hgc : 0 ≤ g ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hg.le _
  have hg2l : 0 ≤ Real.log (2 / g) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hg]; linarith only [hg1]
  have hx : momentConst (8 * (m + 1)) * (4 * (CU * (C₁ * Q M K A s) *
      Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ)))) ≤
      (momentConst (8 * (m + 1)) * 4 * CU * C₁ * logConst m T b) *
        (g ^ ((1 : ℝ) / 3) * Real.log (2 / g)) * Ql := by
    have hk : 0 ≤ momentConst (8 * (m + 1)) * 4 * CU * C₁ :=
      mul_nonneg (mul_nonneg (mul_nonneg hc1.le (by norm_num)) hCU.le) hC₁.le
    have hprod : Q M K A s * Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ)) ≤
        g ^ ((1 : ℝ) / 3) * Ql * (logConst m T b * Real.log (2 / g)) :=
      mul_le_mul hQs hlog hlog0.le (mul_nonneg hgc hQl0.le)
    have := mul_le_mul_of_nonneg_left hprod hk
    calc _ = momentConst (8 * (m + 1)) * 4 * CU * C₁ *
          (Q M K A s * Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ))) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hy : 2 * (moveConst m T b Cs * g * Ql) ≤ (2 * moveConst m T b Cs) * g * Ql := by
    apply le_of_eq; ring
  have hz : (momentConst (2 * (8 * (m + 1))) * (2 * (Cb * Ql)) + pairConst m b Cs * Ql) * (g * Cr) ≤
      ((momentConst (2 * (8 * (m + 1))) * 2 * Cb + pairConst m b Cs) * Cr) * g * Ql := by
    apply le_of_eq; ring
  have htot := sum_le_rate hg.le (mul_nonneg hgc hg2l) hQl0.le
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc1.le (by norm_num)) hCU.le) hC₁.le) hlc)
    (by linarith only [hmv] : 0 ≤ 2 * moveConst m T b Cs)
    (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg hc2.le (by norm_num)) hCb.le)
      (pairConst_pos m b hCs).le) hCr) hx hy hz
  simpa only [momentConst, rateConst] using htot

end CurvatureVariance.Paper.Localization.Modulus
