/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Chart.Transversal
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.PosDef

/-!
# Lemma `lem:chart`: the transverse expansion

**Lemma `lem:chart`**: under the expansion `AssumptionCAt` at `(ξ, H)` with `a = ξ₁ > 0` and
`t₀ = a⁻¹ ξ'`, there are `r₀ > 0`, `C`, `p₀` and a positive definite `q₀` with
`|μ(1, t₀ + h) − μ(1, t₀) − p₀·h − q₀(h)| ≤ C|h|^{2+δ}` for `|h| ≤ r₀`, where `δ` is the exponent
of the expansion.

The proof is that of Lemma `lem:chart` in the paper, for a hyperplane `H` transverse to `ξ` and with
constants that are not explicit; the paper takes `H = ξ^⊥` and makes the constants explicit
(`Chart.chartUniformStatement_holds`). This form serves the theorem at one direction. With `ℓ` the
transversal functional
(`ℓ(ξ) = 1`, `ker ℓ = H`), `r_h = a⁻¹ + ℓ(0, h)` and `v_h = π_H(0, h) ∈ H`,
`(1, t₀ + h) = a⁻¹ξ + (0, h) = r_h (ξ + v_h / r_h)`. Homogeneity and the expansion at
`v_h / r_h` give `μ(1, t₀ + h) − μ(1, t₀) = ℓ(0, h) μ(ξ) + ℓ_H(v_h) + r_h⁻¹ q_H(v_h) + r_h E` with
`|E| ≤ M |v_h / r_h|^{2+δ}` (`expansion_identity`). The linear term is `p₀·h`, and
`q₀(h) = a q_H(v_h)` is positive definite since `h ↦ v_h` is injective. Replacing `r_h⁻¹` by `a`
costs `O(|h|³) ≤ O(|h|^{2+δ})` because `|h| ≤ 1` and `δ ≤ 1` (`chart_error_le`). The radius
`r₀ ≤ 1` gives the three smallness conditions: `|h| ≤ 1`, `|ℓ(0, h)| ≤ 1/(2a)`, so that
`r_h ∈ [1/(2a), 3/(2a)]`, and `|v_h / r_h|` at most the radius of the expansion (`radius_facts`).
-/

@[expose] public section

namespace CurvatureVariance.Paper.Chart

open CurvatureVariance.Paper

variable {m : ℕ}

/-- The algebraic identity of the proof: with `r = a⁻¹ + λ`,
`r μ(ξ + h') − a⁻¹ μ(ξ) − (μ(ξ) λ + ℓ_H(v)) − a q_H(v) = r E + (r⁻¹ − a) q_H(v)`, where
`E = μ(ξ + h') − μ(ξ) − r⁻¹ ℓ_H(v) − r⁻² q_H(v)` is the error of the expansion at `h' = v / r`. -/
theorem expansion_identity {a lam r μξ μξh ℓv qv : ℝ} (hr : 0 < r) (hrdef : r = a⁻¹ + lam) :
    r * μξh - a⁻¹ * μξ - (μξ * lam + ℓv) - a * qv =
      r * (μξh - μξ - r⁻¹ * ℓv - r⁻¹ * r⁻¹ * qv) + (r⁻¹ - a) * qv := by
  have h1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  linear_combination μξ * hrdef + (ℓv + r⁻¹ * qv) * h1

/-- If `|λ| ≤ C_λ x ≤ 1/(2a)`, then `r = a⁻¹ + λ ∈ [1/(2a), 3/(2a)]`. -/
theorem r_bounds {a lam Cl x : ℝ} (ha : 0 < a) (hlam : |lam| ≤ Cl * x)
    (hlx : 2 * a * Cl * x ≤ 1) : 1 / (2 * a) ≤ a⁻¹ + lam ∧ a⁻¹ + lam ≤ 3 / (2 * a) := by
  have hClx : Cl * x ≤ 1 / (2 * a) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hainv : a⁻¹ = 2 * (1 / (2 * a)) := by field_simp
  have h3 : 3 / (2 * a) = 3 * (1 / (2 * a)) := by ring
  obtain ⟨hl1, hl2⟩ := abs_le.mp hlam
  rw [hainv, h3]
  constructor <;> linarith

/-- The facts given by `|h| ≤ r₀`, with `r₀ = min(1, 1/(2a(C_λ+1)), r/(2a(C_v+1)))`. -/
theorem radius_facts {a Cl Cv rC x : ℝ} (ha : 0 < a) (hCl : 0 ≤ Cl) (hCv : 0 ≤ Cv)
    (hx0 : 0 ≤ x)
    (hx : x ≤ min 1 (min (1 / (2 * a * (Cl + 1))) (rC / (2 * a * (Cv + 1))))) :
    x ≤ 1 ∧ 2 * a * Cl * x ≤ 1 ∧ 2 * a * Cv * x ≤ rC := by
  have h1 := hx.trans (min_le_left _ _)
  have h2 := (hx.trans (min_le_right _ _)).trans (min_le_left _ _)
  have h3 := (hx.trans (min_le_right _ _)).trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h2 h3
  have hax := mul_nonneg ha.le hx0
  exact ⟨h1, by linarith, by linarith⟩

/-- The error bound: `|r E + (r⁻¹ − a) q_H(v)| ≤ C x^{2+δ}`, from `|E| ≤ M s^{2+δ}` with
`s ≤ 2a C_v x` and `|q_H(v)| ≤ C_q (C_v x)²`, for `x ≤ 1` and `δ ≤ 1`. -/
theorem chart_error_le {a lam r x s E qv Cl Cv Cq M δ : ℝ} (ha : 0 < a) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hCl : 0 ≤ Cl) (hCv : 0 ≤ Cv) (hCq : 0 ≤ Cq)
    (hM : 0 ≤ M) (hlam : |lam| ≤ Cl * x) (hlx : 2 * a * Cl * x ≤ 1) (hrdef : r = a⁻¹ + lam)
    (hs0 : 0 ≤ s) (hs : s ≤ 2 * a * Cv * x) (hE : |E| ≤ M * s ^ (2 + δ))
    (hqv : |qv| ≤ Cq * (Cv * x) ^ 2) :
    |r * E + (r⁻¹ - a) * qv| ≤
      (3 / (2 * a) * M * (2 * a * Cv) ^ (2 + δ) + 2 * a ^ 2 * Cl * Cq * Cv ^ 2) *
        x ^ (2 + δ) := by
  obtain ⟨hr1, hr2⟩ := r_bounds ha hlam hlx
  rw [← hrdef] at hr1 hr2
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hrinv : r⁻¹ ≤ 2 * a := by
    rw [inv_le_comm₀ hr0 (by positivity), ← one_div]; exact hr1
  have hT1 : |r * E| ≤ 3 / (2 * a) * M * (2 * a * Cv) ^ (2 + δ) * x ^ (2 + δ) := by
    rw [abs_mul, abs_of_pos hr0]
    have hsx : s ^ (2 + δ) ≤ (2 * a * Cv) ^ (2 + δ) * x ^ (2 + δ) := by
      rw [← Real.mul_rpow (by positivity) hx0]
      exact Real.rpow_le_rpow hs0 hs (by linarith)
    calc r * |E| ≤ 3 / (2 * a) * (M * s ^ (2 + δ)) :=
          mul_le_mul hr2 hE (abs_nonneg _) (by positivity)
      _ ≤ 3 / (2 * a) * (M * ((2 * a * Cv) ^ (2 + δ) * x ^ (2 + δ))) := by gcongr
      _ = _ := by ring
  have hinv : |r⁻¹ - a| ≤ 2 * a ^ 2 * Cl * x := by
    have h1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
    have h2 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
    have heq : r⁻¹ - a = -(a * lam) * r⁻¹ := by
      linear_combination (-a * r⁻¹) * hrdef - r⁻¹ * h2 + a * h1
    rw [heq, abs_mul, abs_neg, abs_mul, abs_of_pos ha, abs_of_pos (inv_pos.mpr hr0)]
    calc a * |lam| * r⁻¹ ≤ a * (Cl * x) * (2 * a) := by gcongr
      _ = 2 * a ^ 2 * Cl * x := by ring
  have hx3 : x ^ 3 ≤ x ^ (2 + δ) := by
    rw [show x ^ 3 = x ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast x 3).symm]
    exact Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 (by linarith) (by push_cast; linarith)
  have hT2 : |(r⁻¹ - a) * qv| ≤ 2 * a ^ 2 * Cl * Cq * Cv ^ 2 * x ^ (2 + δ) := by
    rw [abs_mul]
    calc |r⁻¹ - a| * |qv| ≤ (2 * a ^ 2 * Cl * x) * (Cq * (Cv * x) ^ 2) :=
          mul_le_mul hinv hqv (abs_nonneg _) (by positivity)
      _ = 2 * a ^ 2 * Cl * Cq * Cv ^ 2 * x ^ 3 := by ring
      _ ≤ 2 * a ^ 2 * Cl * Cq * Cv ^ 2 * x ^ (2 + δ) := by gcongr
  calc |r * E + (r⁻¹ - a) * qv| ≤ |r * E| + |(r⁻¹ - a) * qv| := abs_add_le _ _
    _ ≤ _ := add_le_add hT1 hT2
    _ = _ := by ring

/-- `(1, t₀ + h) = a⁻¹ ξ + (0, h)` with `a = ξ₁` and `t₀ = a⁻¹ ξ'`. -/
theorem slopeVec_smul_inv_add {ξ : Pt m} (ha : ξ.ofLp.1 ≠ 0) (h : EuclideanSpace ℝ (Fin m)) :
    slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2 + h) = (ξ.ofLp.1)⁻¹ • ξ + inr h := by
  apply WithLp.ofLp_injective
  ext
  · simp [slopeVec, inr_apply]; exact (inv_mul_cancel₀ ha).symm
  · simp [slopeVec, inr_apply]

/-- `(1, t₀) = a⁻¹ ξ`. -/
theorem slopeVec_smul_inv {ξ : Pt m} (ha : ξ.ofLp.1 ≠ 0) :
    slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2) = (ξ.ofLp.1)⁻¹ • ξ := by
  simpa using slopeVec_smul_inv_add ha 0

/-- The pointwise expansion: under `AssumptionCAt` at `(ξ, H)`, for `|h|` small (in the sense of
`radius_facts`), `μ(1, t₀ + h) − μ(1, t₀) − (μ(ξ) ℓ(0, h) + ℓ_H(v_h)) − a q_H(v_h)` is at most
`C|h|^{2+δ}`. -/
theorem chart_pointwise (μ : PtNorm m) (ξ : Pt m) (H : Submodule ℝ (Pt m))
    (hc : IsCompl (Submodule.span ℝ {ξ}) H) (hξ : ξ ≠ 0) (ha : 0 < ξ.ofLp.1)
    {δ rC M Cl Cv Cq : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hCl : 0 ≤ Cl) (hCv : 0 ≤ Cv)
    (hCq : 0 ≤ Cq) (ℓ : Module.Dual ℝ H) (q : QuadraticForm ℝ H)
    (hCb : ∀ h : H, ‖h‖ ≤ rC → |μ.1 (ξ + h) - μ.1 ξ - ℓ h - q h| ≤ M * ‖h‖ ^ (2 + δ))
    (hlam : ∀ h, |transversal ξ H hc hξ (inr h)| ≤ Cl * ‖h‖)
    (hV : ∀ h, ‖Submodule.projectionOnto H _ hc.symm (inr h)‖ ≤ Cv * ‖h‖)
    (hqb : ∀ v : H, |q v| ≤ Cq * ‖v‖ ^ 2) (h : EuclideanSpace ℝ (Fin m)) (hx1 : ‖h‖ ≤ 1)
    (hlx : 2 * ξ.ofLp.1 * Cl * ‖h‖ ≤ 1) (hvx : 2 * ξ.ofLp.1 * Cv * ‖h‖ ≤ rC) :
    |μ.1 (slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2 + h)) - μ.1 (slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2)) -
        (μ.1 ξ * transversal ξ H hc hξ (inr h) +
          ℓ (Submodule.projectionOnto H _ hc.symm (inr h))) -
        ξ.ofLp.1 * q (Submodule.projectionOnto H _ hc.symm (inr h))| ≤
      (3 / (2 * ξ.ofLp.1) * M * (2 * ξ.ofLp.1 * Cv) ^ (2 + δ) +
        2 * ξ.ofLp.1 ^ 2 * Cl * Cq * Cv ^ 2) * ‖h‖ ^ (2 + δ) := by
  obtain ⟨r, hr⟩ : ∃ r, r = (ξ.ofLp.1)⁻¹ + transversal ξ H hc hξ (inr h) := ⟨_, rfl⟩
  have hr1 := (r_bounds ha (hlam h) hlx).1
  rw [← hr] at hr1
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr1
  have hrinv : r⁻¹ ≤ 2 * ξ.ofLp.1 := by
    rw [inv_le_comm₀ hr0 (by positivity), ← one_div]; exact hr1
  set v := Submodule.projectionOnto H _ hc.symm (inr h) with hv
  -- the point `(1, t₀ + h) = r (ξ + v / r)`
  have hpt : slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2 + h) = r • (ξ + ((r⁻¹ • v : H) : Pt m)) := by
    rw [slopeVec_smul_inv_add ha.ne' h, Submodule.coe_smul, smul_add, smul_smul,
      mul_inv_cancel₀ hr0.ne', one_smul, hr, add_smul, add_assoc]
    congr 1
    exact (transversal_smul_add ξ H hc hξ (inr h)).symm
  have hμx : μ.1 (slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2 + h)) =
      r * μ.1 (ξ + ((r⁻¹ • v : H) : Pt m)) := by
    rw [hpt, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr0]
  have hμ0 : μ.1 (slopeVec ((ξ.ofLp.1)⁻¹ • ξ.ofLp.2)) = (ξ.ofLp.1)⁻¹ * μ.1 ξ := by
    rw [slopeVec_smul_inv ha.ne', map_smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
  -- the expansion at `h' = v / r`
  have hs : ‖r⁻¹ • v‖ ≤ 2 * ξ.ofLp.1 * Cv * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
    calc r⁻¹ * ‖v‖ ≤ (2 * ξ.ofLp.1) * (Cv * ‖h‖) :=
          mul_le_mul hrinv (hV h) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hE := hCb (r⁻¹ • v) (hs.trans hvx)
  rw [map_smul, smul_eq_mul, QuadraticMap.map_smul, smul_eq_mul] at hE
  have hqv : |q v| ≤ Cq * (Cv * ‖h‖) ^ 2 :=
    (hqb v).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hV h) 2) hCq)
  rw [hμx, hμ0, expansion_identity hr0 hr]
  exact chart_error_le ha (norm_nonneg h) hx1 hδ hδ1 hCl hCv hCq hM (hlam h) hlx hr
    (norm_nonneg _) hs hE hqv

/-- **Lemma `lem:chart`** (Transverse expansion). -/
theorem chartStatement_holds : Contracts.ChartStatement m := by
  intro μ ξ H ha hc hC
  obtain ⟨δ, hδ, hδ1, rC, hrC, M, hM, ℓ, q, hq, hCb⟩ := hC
  have hξ : ξ ≠ 0 := by rintro rfl; simp at ha
  obtain ⟨Cl, hCl, hlam⟩ := exists_norm_le_mul_norm (transversal ξ H hc hξ ∘ₗ inr)
  obtain ⟨Cv, hCv, hV⟩ :=
    exists_norm_le_mul_norm (Submodule.projectionOnto H _ hc.symm ∘ₗ inr (m := m))
  obtain ⟨Cq, hCq, hqb⟩ := Proofs.Geometry.exists_abs_le_mul_norm_sq_of_quadraticForm q
  let f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ :=
    μ.1 ξ • (transversal ξ H hc hξ ∘ₗ inr) + ℓ ∘ₗ (Submodule.projectionOnto H _ hc.symm ∘ₗ inr)
  refine ⟨δ, hδ, hδ1, min 1 (min (1 / (2 * ξ.ofLp.1 * (Cl + 1))) (rC / (2 * ξ.ofLp.1 * (Cv + 1)))),
    by positivity,
    3 / (2 * ξ.ofLp.1) * M * (2 * ξ.ofLp.1 * Cv) ^ (2 + δ) +
      2 * ξ.ofLp.1 ^ 2 * Cl * Cq * Cv ^ 2, by positivity,
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm
      (LinearMap.toContinuousLinearMap f),
    ξ.ofLp.1 • q.comp (Submodule.projectionOnto H _ hc.symm ∘ₗ inr), ?_, fun h hh => ?_⟩
  · intro h hh0
    rw [_root_.smul_apply, QuadraticMap.comp_apply, smul_eq_mul]
    exact mul_pos ha (hq _ (projectionOnto_inr_ne_zero ξ H hc ha.ne' hh0))
  · obtain ⟨hx1, hlx, hvx⟩ := radius_facts ha hCl hCv (norm_nonneg h) hh
    rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap',
      _root_.smul_apply, QuadraticMap.comp_apply, smul_eq_mul]
    exact chart_pointwise μ ξ H hc hξ ha hδ hδ1 hM hCl hCv hCq ℓ q hCb
      (fun h => by simpa using hlam h) (fun h => by simpa using hV h) hqb h hx1 hlx hvx

end CurvatureVariance.Paper.Chart
