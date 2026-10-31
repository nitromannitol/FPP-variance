/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Infra.Os.Power
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bounded paths in `O₁` (Section `sec:prelim`, the classical bounds)

By Assumption (W) and equation `eq:sum`, the passage time along a path with `m` edges is at most
`O₁(Cm)`:

* `exists_lintegral_exp_le_two`: under (W) there is `β > 0` with `E e^{β τ} ≤ 2` (concave-power
  Jensen from the exponential moment of (W)).
* `exists_isOs_weight`: a single weight is `O₁(θ₀)`, `θ₀ = 1/β`.
* `isOs_walkCost`: the cost of a walk of length `k` is `O₁(θ₀ (k + 1))` ([AKM, Lemma A.4], no
  independence needed).
* `isOs_passageTimeReal_l1Dist`: `T(u, v) ≤ O₁(θ₀ (|u − v|₁ + 1))`, along a coordinate path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

/-- Under (W) a weight has an exponential moment at most two: `∫ e^{β x} dF ≤ 2` for some
`β > 0`. -/
theorem exists_lintegral_exp_le_two {M : Law m} (hM : M.Valid) :
    ∃ β : ℝ, 0 < β ∧ ∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂M.F ≤ 2 := by
  have := hM.probF
  obtain ⟨α, hα, hint⟩ := hM.assumptionW.1
  set Z := ∫⁻ x, ENNReal.ofReal (Real.exp (α * x)) ∂M.F with hZ
  have hZfin : Z ≠ ⊤ := by
    rw [hZ, ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_ne_top
  set L := max (Real.log Z.toReal) 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  set a := min 1 (Real.log 2 / (L + 1)) with ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hapos : 0 < a := lt_min one_pos (div_pos hlog2 (by linarith only [hL0]))
  have ha1 : a ≤ 1 := min_le_left _ _
  refine ⟨a * α, mul_pos hapos hα, ?_⟩
  have hpow : ∀ x : ℝ≥0, ENNReal.ofReal (Real.exp (a * α * x)) =
      ENNReal.ofReal (Real.exp (α * x)) ^ a := by
    intro x
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2; ring
  simp_rw [hpow]
  have hmeas : AEMeasurable (fun x : ℝ≥0 => ENNReal.ofReal (Real.exp (α * x))) M.F :=
    ((measurable_const.mul measurable_coe_nnreal_real).exp.ennreal_ofReal).aemeasurable
  refine (lintegral_rpow_le hmeas hapos ha1).trans ?_
  rw [← hZ, ← ENNReal.ofReal_toReal hZfin, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
    hapos.le, ← ENNReal.ofReal_ofNat 2]
  apply ENNReal.ofReal_le_ofReal
  rcases (ENNReal.toReal_nonneg (a := Z)).eq_or_lt with hz | hz
  · rw [← hz, Real.zero_rpow hapos.ne']; norm_num
  · rw [Real.rpow_def_of_pos hz]
    calc Real.exp (Real.log Z.toReal * a) ≤ Real.exp (L * (Real.log 2 / (L + 1))) := by
          apply Real.exp_le_exp.mpr
          calc Real.log Z.toReal * a ≤ L * a :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hapos.le
            _ ≤ L * (Real.log 2 / (L + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hL0
      _ ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          rw [mul_div_assoc', div_le_iff₀ (by linarith only [hL0])]
          nlinarith only [hlog2, hL0]
      _ = 2 := Real.exp_log (by norm_num)

/-- Under (W) a single weight is `O₁(θ₀)` for a constant `θ₀` depending only on the law. -/
theorem exists_isOs_weight {M : Law m} (hM : M.Valid) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ e : Edge m, CurvatureVariance.IsOs M.P 1 θ₀ (fun ω => (ω e : ℝ)) := by
  obtain ⟨β, hβ, hint⟩ := exists_lintegral_exp_le_two hM
  refine ⟨1 / β, by positivity, fun e => ⟨(measurable_pi_apply e).coe_nnreal_real.aemeasurable,
    ?_⟩⟩
  have hfun : (fun ω : Config m =>
      ENNReal.ofReal (Real.exp ((max (ω e : ℝ) 0 / (1 / β)) ^ (1 : ℝ))))
      = (fun x : ℝ≥0 => ENNReal.ofReal (Real.exp (β * x))) ∘ (fun ω : Config m => ω e) := by
    funext ω
    simp only [Function.comp_apply, Real.rpow_one, max_eq_left (NNReal.coe_nonneg _)]
    congr 2
    field_simp
  have hmap := lintegral_map (μ := M.P)
    (f := fun x : ℝ≥0 => ENNReal.ofReal (Real.exp (β * x)))
    ((measurable_const.mul measurable_coe_nnreal_real).exp.ennreal_ofReal)
    (measurable_pi_apply (X := fun _ : Edge m => ℝ≥0) e)
  rw [(hM.iid.2 e).map_eq] at hmap
  rw [hfun]
  exact hmap.symm.le.trans hint

/-- **Bounded paths**: the cost of a walk of length `k` is `O₁(θ₀ (k + 1))` when every
weight is `O₁(θ₀)`. -/
theorem isOs_walkCost {M : Model m} (hM : M.Standing) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hw : ∀ e : Edge m, CurvatureVariance.IsOs M.P 1 θ₀ (fun ω => (ω e : ℝ))) {u v : Vertex m}
    (p : (latticeGraph m).Walk u v) :
    CurvatureVariance.IsOs M.P 1 (θ₀ * (p.length + 1)) (fun ω => (walkCost ω p : ℝ)) := by
  have := hM.probP
  have hfun : (fun ω : Config m => (walkCost ω p : ℝ)) =
      fun ω => ∑ i : Fin p.darts.length, (ω (Infra.FPP.dartEdge p i) : ℝ) := by
    funext ω; exact Infra.FPP.coe_walkCost_eq_sum p ω
  rw [hfun]
  rcases (Finset.univ : Finset (Fin p.darts.length)).eq_empty_or_nonempty with hT | hT
  · simp only [hT, Finset.sum_empty]
    exact isOs_zero one_pos _
  · have h := isOs_one_finset_sum (P := M.P) Finset.univ hT (fun _ => θ₀) (fun _ _ => hθ₀) _
      (fun i _ => hw (Infra.FPP.dartEdge p i))
    refine h.mono_scale zero_le_one (Finset.sum_pos (fun _ _ => hθ₀) hT) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      SimpleGraph.Walk.length_darts]
    nlinarith only [hθ₀]

/-- `T(u, v) ≤ O₁(θ₀ (|u − v|₁ + 1))`, along a coordinate path. -/
theorem isOs_passageTimeReal_l1Dist {M : Model m} (hM : M.Standing) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hw : ∀ e : Edge m, CurvatureVariance.IsOs M.P 1 θ₀ (fun ω => (ω e : ℝ))) (u v : Vertex m) :
    CurvatureVariance.IsOs M.P 1 (θ₀ * (Infra.FPP.l1Dist u v + 1)) (fun ω => passageTimeReal ω u v) := by
  obtain ⟨p, -, hp⟩ := Infra.FPP.exists_isPath_length_eq_l1Dist u v
  have h := isOs_walkCost hM hθ₀ hw p
  rw [hp] at h
  refine h.mono zero_le_one (by positivity) (measurable_passageTimeReal u v).aemeasurable
    (Eventually.of_forall fun ω => ?_)
  exact NNReal.coe_le_coe.mpr (Infra.FPP.passageTime_le_walkCost ω p)

end CurvatureVariance.Paper.Moments
