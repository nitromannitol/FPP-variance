/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Reduction.Coordinates

/-!
# The choice of coordinates, at every point

The beginning of Section `sec:prelim`: "Since permutations and sign changes of the coordinates
preserve the law of the weights, `μ` and (Curv), we order and orient the coordinates so that the
first component `ξ₁` of `ξ` is positive and has the largest absolute value." The transport of
`Proofs.Reduction.Coordinates` for the law of `T(0, x)` at every vertex `x`, not only at `⌊nξ⌋`:

* `map_passageTime_apply`: `T(0, x)` and `T(0, Φ x)` have the same law;
* `norm_choice_sub_smul`: with `A_j ξ = a (1, t₀)`, the distance from `x` to `βξ` is the distance
  from `Φ_j x` to `βa (1, t₀)`;
* `reductionUniformStatement`: the contract `Contracts.ReductionUniformStatement`, from
  Lemma `lem:chart` with explicit constants. The model has the law `choiceLaw` of the signed
  permutation `choiceIsometry` to a largest coordinate of `ξ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Reduction

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- **The law in the new coordinates**: `T(0, x)` and `T(0, Φ x)` have the same law, since
transporting the weights along `Φ⁻¹` preserves their law and
`T_{transport Φ⁻¹ ω}(0, Φ x) = T_ω(0, x)`. The proof is that of `evariance_passageTime_apply`. -/
theorem map_passageTime_apply {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} (hP : IsIIDWeights P F) (Φ : latticeGraph m ≃g latticeGraph m)
    (hΦ0 : Φ 0 = 0) (x : Vertex m) :
    Measure.map (fun ω => passageTimeReal ω 0 x) P =
      Measure.map (fun ω => passageTimeReal ω 0 (Φ x)) P := by
  have hΦ0' : Φ.symm 0 = 0 := by rw [RelIso.symm_apply_eq, hΦ0]
  have hg := IsIIDWeights.measurePreserving_transport hP Φ.symm
  have hX : Measurable fun ω => passageTimeReal ω 0 (Φ x) :=
    measurable_passageTime_real (0 : Vertex m) (Φ x)
  have e : (fun ω => passageTimeReal ω 0 x) =
      (fun ω => passageTimeReal ω 0 (Φ x)) ∘ transport Φ.symm := by
    funext ω
    simp only [passageTimeReal, Function.comp_apply, passageTime_transport, hΦ0',
      RelIso.symm_apply_apply]
  rw [e, ← Measure.map_map hX hg.measurable, hg.map_eq]

/-- **The distance in the new coordinates**, at every vertex: with `A_j ξ = a (1, t₀)`,
`|Φ_j x − βa (1, t₀)| = |x − βξ|`. -/
theorem norm_choice_sub_smul (j : Option (Fin m) × Bool) {ξ : Pt m}
    (hξ : (choiceIsometry j ξ).ofLp.1 ≠ 0) (x : Vertex m) (β : ℝ) :
    ‖point (choiceIso j x) -
        (β * (choiceIsometry j ξ).ofLp.1) •
          slopeVec (((choiceIsometry j ξ).ofLp.1)⁻¹ • (choiceIsometry j ξ).ofLp.2)‖ =
      ‖point x - β • ξ‖ := by
  rw [point_choiceIso, mul_smul, smul_slopeVec_inv hξ, ← map_smul, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- **The choice of coordinates, at every point** (the beginning of Section `sec:prelim`, and the
last sentences of the proof of Theorem `thm:main`), from Lemma `lem:chart` with explicit constants:
`hi` is a Lipschitz bound of `μ` (`PtNorm.exists_bounds`), the laws are `choiceLaw j`, and for a
unit direction the choice is a largest coordinate `k₀` with the sign of `ξ_{k₀}`. -/
theorem reductionUniformStatement {m : ℕ} (hchart : ChartUniformStatement m) :
    ReductionUniformStatement m := by
  intro hm F _ hW P _ hP μ hμ
  obtain ⟨lo, hi, -, hhi, hb⟩ := PtNorm.exists_bounds μ
  refine ⟨hi, hhi, fun x => (hb x).2, fun δ r M c hδ hδ₁ hr hM hc => ?_⟩
  refine ⟨choiceLaw F P μ δ, fun j => ⟨⟨hm, inferInstanceAs (IsProbabilityMeasure F), hW,
    inferInstanceAs (IsProbabilityMeasure P), hP,
    isTimeConstant_transportNorm hP hμ (choiceIso j) (choiceIso_zero j) (choiceIso_add j) _
      (point_choiceIso j), hδ, hδ₁⟩, rfl⟩, fun ξ hξ hCξ => ?_⟩
  -- a largest coordinate `k₀`, with the sign of `ξ_{k₀}`
  obtain ⟨k₀, -, hk₀⟩ :=
    Finset.exists_max_image Finset.univ (fun k => |ptCoord ξ k|) Finset.univ_nonempty
  have hk₀' : ∀ k, |ptCoord ξ k| ≤ |ptCoord ξ k₀| := fun k => hk₀ k (Finset.mem_univ k)
  set j : Option (Fin m) × Bool := (k₀, decide (0 < ptCoord ξ k₀)) with hj
  set A := choiceIsometry j with hA
  set ζ := A ξ with hζdef
  set a := ζ.ofLp.1 with ha_def
  have haeq : a = |ptCoord ξ k₀| := choiceIsometry_fst ξ k₀
  -- `a ∈ [d^{−1/2}, 1]`
  obtain ⟨hlo, hup⟩ := sq_bounds_of_largest hξ hk₀'
  rw [← haeq] at hlo hup
  set S := Real.sqrt ((m : ℝ) + 1) with hSdef
  have hS : 0 < S := Real.sqrt_pos.2 (Nat.cast_add_one_pos m)
  have hS2 : S ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (Nat.cast_add_one_pos m).le
  have ha0 : 0 ≤ a := haeq ▸ abs_nonneg _
  have haS : 1 ≤ a * S := by
    have e : (a * S) ^ 2 = ((m : ℝ) + 1) * a ^ 2 := by rw [mul_pow, hS2]; ring
    rw [← pow_le_pow_iff_left₀ zero_le_one (mul_nonneg ha0 hS.le) two_ne_zero, one_pow, e]
    exact hlo
  have ha : 0 < a := lt_of_le_of_ne ha0 fun h => by
    rw [← h, zero_mul] at haS; exact absurd haS (by norm_num)
  have ha1 : a ≤ 1 := by
    rw [← pow_le_pow_iff_left₀ ha0 zero_le_one two_ne_zero, one_pow]; exact hup
  have halo : 1 / S ≤ a := by rw [div_le_iff₀ hS]; linarith only [haS]
  -- the hypotheses of Lemma `lem:chart` in the new coordinates
  have hζ : ‖ζ‖ = 1 := by rw [hζdef, LinearIsometryEquiv.norm_map, hξ]
  have hζj : ∀ i : Fin m, |ζ.ofLp.2 i| ≤ ζ.ofLp.1 := fun i => by
    rw [hζdef, hA, choiceIsometry_snd, ← ha_def, haeq]
    exact hk₀' _
  have hhi' : ∀ x : Pt m, (transportNorm μ A).1 x ≤ hi * ‖x‖ := fun x => by
    rw [transportNorm_apply]
    exact ((hb _).2).trans_eq (by rw [LinearIsometryEquiv.norm_map])
  obtain ⟨p₀, q₀, hqlo, hqhi, hcurv⟩ := hchart (transportNorm μ A) hi hhi hhi' ζ hζ ha hζj
    δ r M c hδ hδ₁ hr hM hc (assumptionCWith_transportNorm hCξ A)
  -- the model, in the bounds of Lemma `lem:chart`
  set Md : Model m := ⟨choiceLaw F P μ δ j, 12 * M + 2 * chartLam hi r M δ, min 1 r / 4,
    a⁻¹ • ζ.ofLp.2, p₀, q₀⟩ with hMd
  have hca : 0 < c * a ^ 3 := mul_pos hc (pow_pos ha 3)
  have hMs : Md.Standing :=
    { one_le_m := hm, probF := inferInstanceAs (IsProbabilityMeasure F), assumptionW := hW,
      probP := inferInstanceAs (IsProbabilityMeasure P), iid := hP,
      timeConstant := isTimeConstant_transportNorm hP hμ (choiceIso j) (choiceIso_zero j)
        (choiceIso_add j) _ (point_choiceIso j),
      delta_pos := hδ, delta_le_one := hδ₁,
      rrem_pos := div_pos (lt_min one_pos hr) (by norm_num),
      q₀_posDef := fun h hh => lt_of_lt_of_le (mul_pos hca (pow_pos (norm_pos_iff.2 hh) 2))
        (hqlo h),
      curvature := hcurv }
  have hfit : Md.Fits (chartBounds (choiceLaw F P μ δ j) hi r M c) :=
    { law_eq := rfl, rrem_le := le_rfl, Crem_le := le_rfl,
      q₀_lower := fun h => le_trans
        (mul_le_mul_of_nonneg_right (div_le_mul_pow_three hc haS) (sq_nonneg _)) (hqlo h),
      q₀_upper := hqhi,
      t₀_le := norm_inv_smul_snd_le hζ ha hlo }
  refine ⟨j, Md, choiceIso j, a, hMs, hfit, halo, ha1, fun x => ?_, fun x => ?_, fun x β => ?_⟩
  · exact map_passageTime_apply hP _ (choiceIso_zero j) x
  · show (transportNorm μ A).1 (point (choiceIso j x)) = μ.1 (point x)
    rw [transportNorm_apply, point_choiceIso, A.symm_apply_apply]
  · exact norm_choice_sub_smul j ha.ne' x β

end CurvatureVariance.Paper.Proofs.Reduction
