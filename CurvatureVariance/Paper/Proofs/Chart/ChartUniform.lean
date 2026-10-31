/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Chart.Chart
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:chart` with explicit constants

**Lemma `lem:chart` at a unit direction** (`ChartUniformStatement`): for a norm with
`μ ≤ hi |·|` and (Curv) at a unit `ζ = (a, ζ')`, `a > 0`, on `H = ζ^⊥` with the constants
`δ, r, M, c`, the expansion at `t₀ = a⁻¹ ζ'` holds with `c a³ |h|² ≤ q₀(h) ≤ Λ |h|²`, remainder
`(12M + 2Λ) |h|^{2+δ}` and radius `min(1, r)/4`, where `Λ = hi/r + M r^δ` (`chartLam`).

The proof is that of `chartStatement_holds` (`chart_pointwise`) with its three constants made
explicit, as in the proof of Lemma `lem:chart` in the paper, which writes `μ^*` for `hi` and `λ` for
`c`:
* on `ζ^⊥` the transversal functional is `x ↦ ⟨x, ζ⟩` and the projection along `ζ` is orthogonal
  (`transversal_eq_inner`, `transversal_sq_add_norm_sq`), so `C_ℓ = C_v = 1` and
  `a |h| ≤ |v_h|` (`inr_bounds`);
* (Curv) at `h` and `−h` with `μ(ζ ± h) ≤ μ(ζ) + hi |h|` bounds `q` by `hi |h| + M |h|^{2+δ}` on
  the ball of radius `r`, and homogeneity gives `q(v) ≤ Λ |v|²` (`quadratic_le_chartLam`);
* the remainder constant `(3/(2a)) M (2a)^{2+δ} + 2a²Λ` is at most `12M + 2Λ` since `a ≤ 1`
  (`chart_const_le`), and `min(1, r)/4` meets the three smallness conditions of `radius_facts`.

The hypothesis that `a` is a largest coordinate is not used here; it gives `a ≥ d^{−1/2}`
downstream.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Chart

open CurvatureVariance.Paper

variable {m : ℕ}

/-- `⟨a ζ + y, ζ⟩ = a` for a unit `ζ` and `y ⊥ ζ`, in a real inner product space. -/
private theorem inner_smul_add_unit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ζ y : E} (hζ : ‖ζ‖ = 1) (hy : inner ℝ y ζ = 0) (a : ℝ) : inner ℝ (a • ζ + y) ζ = a := by
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hζ, hy]; ring

/-- Pythagoras, `‖a ζ + y‖² = a² + ‖y‖²` for a unit `ζ` and `y ⊥ ζ`, in a real inner product
space. -/
private theorem norm_smul_add_sq_unit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ζ y : E} (hζ : ‖ζ‖ = 1) (hy : inner ℝ ζ y = 0) (a : ℝ) :
    ‖a • ζ + y‖ ^ 2 = a ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, hy, norm_smul, hζ, mul_one, Real.norm_eq_abs,
    sq_abs]
  ring

section Orthogonal

variable {ζ : Pt m} (hζ : ‖ζ‖ = 1)
  (hc : IsCompl (Submodule.span ℝ {ζ}) (Submodule.span ℝ {ζ})ᗮ) (hξ : ζ ≠ 0)

include hζ in
/-- On `ζ^⊥`, for a unit `ζ`, the transversal functional is `x ↦ ⟨x, ζ⟩`. -/
theorem transversal_eq_inner (x : Pt m) : transversal ζ _ hc hξ x = inner ℝ x ζ := by
  have hπ : inner ℝ (Submodule.projectionOnto _ _ hc.symm x : Pt m) ζ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (Submodule.projectionOnto _ _ hc.symm x).2
  exact (inner_smul_add_unit hζ hπ _).symm.trans
    (congrArg (fun z => inner ℝ z ζ) (transversal_smul_add ζ _ hc hξ x))

include hζ in
/-- Pythagoras for the decomposition `x = ℓ(x) ζ + π_H(x)` along a unit `ζ`. -/
theorem transversal_sq_add_norm_sq (x : Pt m) :
    transversal ζ _ hc hξ x ^ 2 + ‖(Submodule.projectionOnto _ _ hc.symm x : Pt m)‖ ^ 2 =
      ‖x‖ ^ 2 := by
  have hπ : inner ℝ ζ (Submodule.projectionOnto _ _ hc.symm x : Pt m) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (Submodule.projectionOnto _ _ hc.symm x).2
  exact (norm_smul_add_sq_unit hζ hπ _).symm.trans
    (congrArg (fun z => ‖z‖ ^ 2) (transversal_smul_add ζ _ hc hξ x))

include hζ in
/-- The constants of the chart at a unit `ζ = (a, ζ')`: `|ℓ(0, h)| ≤ |h|`, `|v_h| ≤ |h|` and
`a² |h|² ≤ |v_h|²`, with `v_h = π_H(0, h)`. -/
theorem inr_bounds (h : EuclideanSpace ℝ (Fin m)) :
    |transversal ζ _ hc hξ (inr h)| ≤ ‖h‖ ∧
      ‖(Submodule.projectionOnto _ _ hc.symm (inr h) : Pt m)‖ ≤ ‖h‖ ∧
      ζ.ofLp.1 ^ 2 * ‖h‖ ^ 2 ≤ ‖(Submodule.projectionOnto _ _ hc.symm (inr h) : Pt m)‖ ^ 2 := by
  have hpy := transversal_sq_add_norm_sq hζ hc hξ (inr h)
  have hinr : ‖inr h‖ ^ 2 = ‖h‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]; simp [inr_apply]
  have hζ2 : ζ.ofLp.1 ^ 2 + ‖ζ.ofLp.2‖ ^ 2 = 1 := by
    have := WithLp.prod_norm_sq_eq_of_L2 ζ
    rw [hζ, one_pow, Real.norm_eq_abs, sq_abs] at this
    exact this.symm
  have hL : |transversal ζ _ hc hξ (inr h)| ≤ ‖h‖ * ‖ζ.ofLp.2‖ := by
    rw [transversal_eq_inner hζ hc hξ, WithLp.prod_inner_apply]
    simpa [inr_apply] using abs_real_inner_le_norm h ζ.ofLp.2
  have hζ' : ‖ζ.ofLp.2‖ ≤ 1 := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero, one_pow]
    linarith only [hζ2, sq_nonneg ζ.ofLp.1]
  have hL2 : transversal ζ _ hc hξ (inr h) ^ 2 ≤ ‖h‖ ^ 2 * ‖ζ.ofLp.2‖ ^ 2 := by
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hL 2
  rw [hinr] at hpy
  refine ⟨hL.trans (mul_le_of_le_one_right (norm_nonneg _) hζ'), ?_, ?_⟩
  · rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero]
    linarith only [hpy, sq_nonneg (transversal ζ _ hc hξ (inr h))]
  · have : ‖h‖ ^ 2 * ‖ζ.ofLp.2‖ ^ 2 = ‖h‖ ^ 2 - ζ.ofLp.1 ^ 2 * ‖h‖ ^ 2 := by
      rw [show ‖ζ.ofLp.2‖ ^ 2 = 1 - ζ.ofLp.1 ^ 2 by linarith only [hζ2]]; ring
    linarith only [hpy, hL2, this]

end Orthogonal

/-- The bound `q(v) ≤ Λ |v|²`, `Λ = hi/r + M r^δ`, of the quadratic part of (Curv) on a subspace
`H`, for a norm with `μ ≤ hi |·|`: (Curv) at `w` and `−w` with `μ(ζ ± w) ≤ μ(ζ) + hi |w|` gives
`q(w) ≤ hi |w| + M |w|^{2+δ}` for `|w| ≤ r`, and homogeneity carries this from `|w| = r` to every
`v`. -/
theorem quadratic_le_chartLam (μ : PtNorm m) {hi : ℝ} (hμ : ∀ x : Pt m, μ.1 x ≤ hi * ‖x‖)
    {ζ : Pt m} {H : Submodule ℝ (Pt m)} {δ r M : ℝ} (hr : 0 < r) (ℓ : Module.Dual ℝ H)
    (q : QuadraticForm ℝ H)
    (hC : ∀ h : H, ‖h‖ ≤ r → |μ.1 (ζ + h) - μ.1 ζ - ℓ h - q h| ≤ M * ‖h‖ ^ (2 + δ))
    (v : H) : q v ≤ chartLam hi r M δ * ‖v‖ ^ 2 := by
  have hb : ∀ u : H, μ.1 (ζ + u) ≤ μ.1 ζ + hi * ‖u‖ := fun u =>
    (map_add_le_add μ.1 ζ u).trans (add_le_add_right (hμ u) _)
  have hball : ∀ w : H, ‖w‖ = r → q w ≤ hi * r + M * r ^ (2 + δ) := by
    intro w hw
    have hw' : ‖-w‖ = r := by rw [norm_neg, hw]
    have h1 := (abs_le.mp (hC w hw.le)).1
    have h2 := (abs_le.mp (hC (-w) hw'.le)).1
    have hb1 := hb w
    have hb2 := hb (-w)
    rw [hw] at h1 hb1
    rw [hw'] at h2 hb2
    linarith only [h1, h2, hb1, hb2, map_neg ℓ w, QuadraticMap.map_neg q w]
  by_cases hv : v = 0
  · subst hv; simp
  have ht : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw := hball ((r / ‖v‖) • v) (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr ht), div_mul_cancel₀ _ ht.ne'])
  rw [QuadraticMap.map_smul, smul_eq_mul, Real.rpow_add hr, Real.rpow_two] at hw
  have hs : 0 < r / ‖v‖ * (r / ‖v‖) := mul_pos (div_pos hr ht) (div_pos hr ht)
  calc q v ≤ (hi * r + M * (r ^ 2 * r ^ δ)) / (r / ‖v‖ * (r / ‖v‖)) := by
        rw [le_div_iff₀ hs]; exact (mul_comm _ _).trans_le hw
    _ = chartLam hi r M δ * ‖v‖ ^ 2 := by
        unfold chartLam; field_simp

/-- The remainder constant of `chart_pointwise` with `C_ℓ = C_v = 1` and `C_q = Λ` is at most
`12M + 2Λ` when `a ≤ 1`: `(3/(2a)) (2a)^{2+δ} = 3 (2a)^{1+δ} ≤ 12`. -/
theorem chart_const_le {a M δ Λ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hΛ : 0 ≤ Λ) :
    3 / (2 * a) * M * (2 * a * 1) ^ (2 + δ) + 2 * a ^ 2 * 1 * Λ * 1 ^ 2 ≤ 12 * M + 2 * Λ := by
  have h2a : 0 < 2 * a := by positivity
  have hsplit : (2 * a * 1) ^ (2 + δ) = 2 * a * (2 * a) ^ (1 + δ) := by
    rw [mul_one, show (2 : ℝ) + δ = 1 + (1 + δ) by ring, Real.rpow_add h2a, Real.rpow_one]
  have hpow : (2 * a) ^ (1 + δ) ≤ 4 := by
    calc (2 * a) ^ (1 + δ) ≤ 2 ^ (1 + δ) :=
          Real.rpow_le_rpow h2a.le (by linarith only [ha1]) (by linarith only [hδ])
      _ ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hδ1])
      _ = 4 := by norm_num
  have h1 : 3 / (2 * a) * M * (2 * a * 1) ^ (2 + δ) = 3 * M * (2 * a) ^ (1 + δ) := by
    rw [hsplit]; field_simp
  have ha2 : a ^ 2 ≤ 1 := pow_le_one₀ ha.le ha1
  rw [h1]
  have hMp : 3 * M * (2 * a) ^ (1 + δ) ≤ 3 * M * 4 :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hM)
  linarith only [hMp, mul_le_mul_of_nonneg_right ha2 hΛ]

/-- **Lemma `lem:chart` with explicit constants** (`ChartUniformStatement`). -/
theorem chartUniformStatement_holds : Contracts.ChartUniformStatement m := by
  intro μ hi hhi hμ ζ hζ ha _ δ r M c hδ hδ1 hr hM hc hC
  obtain ⟨ℓ, q, hq, hCb⟩ := hC
  have hcH : IsCompl (Submodule.span ℝ {ζ}) (Submodule.span ℝ {ζ})ᗮ :=
    Submodule.isCompl_orthogonal _
  have hξ : ζ ≠ 0 := by rintro rfl; simp at ha
  have ha1 : ζ.ofLp.1 ≤ 1 := by
    have h1 : ‖ζ‖ ^ 2 = ζ.ofLp.1 ^ 2 + ‖ζ.ofLp.2‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]; rfl
    rw [hζ, one_pow] at h1
    rw [← pow_le_pow_iff_left₀ ha.le zero_le_one two_ne_zero, one_pow]
    linarith only [h1, sq_nonneg ‖ζ.ofLp.2‖]
  have hΛ : 0 ≤ chartLam hi r M δ :=
    add_nonneg (div_nonneg hhi.le hr.le) (mul_nonneg hM (Real.rpow_nonneg hr.le _))
  have hqΛ := quadratic_le_chartLam μ hμ hr ℓ q hCb
  have hqb : ∀ v, |q v| ≤ chartLam hi r M δ * ‖v‖ ^ 2 := fun v => by
    rw [abs_of_nonneg ((mul_nonneg hc.le (sq_nonneg _)).trans (hq v))]; exact hqΛ v
  have hinr := inr_bounds hζ hcH hξ
  let π := Submodule.projectionOnto _ _ hcH.symm
  let f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ℝ :=
    μ.1 ζ • (transversal ζ _ hcH hξ ∘ₗ inr) + ℓ ∘ₗ (π ∘ₗ inr)
  refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm
      (LinearMap.toContinuousLinearMap f), ζ.ofLp.1 • q.comp (π ∘ₗ inr), fun h => ?_,
    fun h => ?_, fun h hh => ?_⟩
  · rw [_root_.smul_apply, QuadraticMap.comp_apply, smul_eq_mul]
    calc c * ζ.ofLp.1 ^ 3 * ‖h‖ ^ 2 = ζ.ofLp.1 * (c * (ζ.ofLp.1 ^ 2 * ‖h‖ ^ 2)) := by ring
      _ ≤ ζ.ofLp.1 * (c * ‖π (inr h)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinr h).2.2 hc.le) ha.le
      _ ≤ ζ.ofLp.1 * q (π (inr h)) := mul_le_mul_of_nonneg_left (hq _) ha.le
  · rw [_root_.smul_apply, QuadraticMap.comp_apply, smul_eq_mul]
    calc ζ.ofLp.1 * q (π (inr h)) ≤ ζ.ofLp.1 * (chartLam hi r M δ * ‖π (inr h)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hqΛ _) ha.le
      _ ≤ 1 * (chartLam hi r M δ * ‖h‖ ^ 2) :=
          mul_le_mul ha1 (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hinr h).2.1 2) hΛ)
            (mul_nonneg hΛ (sq_nonneg _)) zero_le_one
      _ = chartLam hi r M δ * ‖h‖ ^ 2 := one_mul _
  · have h4 : min 1 r / 4 ≤ 1 / 4 ∧ min 1 r / 4 ≤ r / 4 :=
      ⟨div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num),
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)⟩
    have hah : ζ.ofLp.1 * ‖h‖ ≤ ‖h‖ := mul_le_of_le_one_left (norm_nonneg _) ha1
    have hx1 : ‖h‖ ≤ 1 := by linarith only [hh, h4.1]
    have hlx : 2 * ζ.ofLp.1 * 1 * ‖h‖ ≤ 1 := by linarith only [hah, hh, h4.1]
    have hvx : 2 * ζ.ofLp.1 * 1 * ‖h‖ ≤ r := by linarith only [hah, hh, h4.2, hr]
    rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap',
      _root_.smul_apply, QuadraticMap.comp_apply, smul_eq_mul]
    refine (chart_pointwise μ ζ _ hcH hξ ha hδ hδ1 hM zero_le_one zero_le_one hΛ ℓ q hCb
      (fun h => (one_mul ‖h‖).symm ▸ (hinr h).1) (fun h => (one_mul ‖h‖).symm ▸ (hinr h).2.1) hqb
      h hx1 hlx hvx).trans ?_
    exact mul_le_mul_of_nonneg_right (chart_const_le ha ha1 hδ hδ1 hM hΛ)
      (Real.rpow_nonneg (norm_nonneg h) _)

end CurvatureVariance.Paper.Chart
