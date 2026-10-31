/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Reduction.Transport
public import CurvatureVariance.Paper.Proofs.Chart.Chart
public import CurvatureVariance.Paper.Proofs.Chart.ChartUniform
public import CurvatureVariance.Infra.FPP.TimeConstantNorm

/-!
# The choice of coordinates

The beginning of Section `sec:prelim`: "Since permutations and sign changes of the coordinates
preserve the law of the weights, `μ` and (Curv), we order and orient the coordinates so that the
first component `ξ₁` of `ξ` is positive and has the largest absolute value." Here no invariance of
`μ` is assumed: the transported norm is shown to be a time constant of the same law. A choice
`j = (k₀, b)` is a coordinate `k₀` and a sign `b`; `Φ_j` (`choiceIso`) is the signed permutation of
`ℤ^d` that puts the coordinate `k₀` first, with the sign `b`, and `A_j` (`choiceIsometry`) its
linear isometry of `ℝ^d`. For `b` the sign of `ξ_{k₀}`, `A_j ξ = a(1, t₀)` with `a = |ξ_{k₀}|`
(`choiceIsometry_fst`), and:

* `μ ∘ A_j⁻¹` is a time constant of the same law (`isTimeConstant_transportNorm`);
* `AssumptionCAt`, (Curv) and transversality hold at `A_j ξ` (`assumptionCAt_transportNorm`,
  `isCompl_map`, `assumptionCWith_transportNorm`), so Lemma `lem:chart` gives the expansion at `t₀`,
  hence a model with the standing hypotheses;
* `Var T(0, ⌊nξ⌋) = Var T(0, Φ_j⌊nξ⌋)` (`evariance_passageTime_apply`);
* `|point (Φ_j⌊nξ⌋) − n a (1, t₀)| = |⌊nξ⌋ − nξ| ≤ √d` (`norm_choice_floorVertex_sub_le`). The
  floor is taken in the original coordinates and never pushed through `Φ_j`.

At one direction any coordinate with `ξ_{k₀} ≠ 0` will do: `reductionStatement_of_chart` proves
`Contracts.ReductionStatement` from `Contracts.ChartStatement`, and `reductionStatement_holds`
closes it with `Chart.chartStatement_holds`.

For the uniform theorem `k₀` is a largest coordinate of the unit direction `ξ`. Then
`a ∈ [d^{−1/2}, 1]` and `|t₀| ≤ √(d−1)`, and Lemma `lem:chart` with explicit constants
(`Contracts.ChartUniformStatement`) puts the model in the bounds `chartBounds` of the law
`choiceLaw j`, one of `2d`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Reduction

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- A nonzero point has a nonzero coordinate. -/
theorem exists_ptCoord_ne_zero {ξ : Pt m} (hξ : ξ ≠ 0) : ∃ k, ptCoord ξ k ≠ 0 := by
  by_contra h
  push Not at h
  exact hξ (ptCoord_injective (funext fun k => by simpa using h k))

/-! ## The choices of coordinates -/

/-- The signs of the choice of coordinates with sign `b`: `−1` on the first coordinate when `b` is
false, and `1` elsewhere. -/
def choiceSign (b : Bool) : Option (Fin m) → ℤ :=
  fun k => if k = none then (if b then 1 else -1) else 1

theorem choiceSign_eq (b : Bool) (k : Option (Fin m)) :
    choiceSign b k = 1 ∨ choiceSign b k = -1 := by
  unfold choiceSign
  split_ifs <;> simp

theorem choiceSign_mul_self (b : Bool) (k : Option (Fin m)) :
    (choiceSign b k : ℝ) * choiceSign b k = 1 := by
  rcases choiceSign_eq b k with h | h <;> rw [h] <;> norm_num

/-- The lattice automorphism `Φ_j` of the choice `j = (k₀, b)`: the signed permutation that
exchanges the first coordinate with `k₀` and gives it the sign `b`. -/
def choiceIso (j : Option (Fin m) × Bool) : latticeGraph m ≃g latticeGraph m :=
  signedPermIso (σ := Equiv.swap none j.1) (choiceSign_eq j.2)

/-- The linear isometry `A_j` of `ℝ^d` of the choice `j`. -/
noncomputable def choiceIsometry (j : Option (Fin m) × Bool) : Pt m ≃ₗᵢ[ℝ] Pt m :=
  signedPermIsometry (Equiv.swap none j.1) (fun k => (choiceSign j.2 k : ℝ))
    (choiceSign_mul_self j.2)

/-- The law of the model of the choice `j`: the same weights, and the time constant `μ ∘ A_j⁻¹`. -/
noncomputable def choiceLaw (F : Measure ℝ≥0) (P : Measure (Config m)) (μ : PtNorm m) (δ : ℝ)
    (j : Option (Fin m) × Bool) : Law m :=
  ⟨F, P, transportNorm μ (choiceIsometry j), δ⟩

theorem point_choiceIso (j : Option (Fin m) × Bool) (z : Vertex m) :
    point (choiceIso j z) = choiceIsometry j (point z) :=
  point_signedPermIso (choiceSign_eq j.2) z

theorem choiceIso_zero (j : Option (Fin m) × Bool) : choiceIso j 0 = 0 :=
  signedPermIso_zero (choiceSign_eq j.2)

theorem choiceIso_add (j : Option (Fin m) × Bool) (z w : Vertex m) :
    choiceIso j (z + w) = choiceIso j z + choiceIso j w :=
  signedPermIso_add (choiceSign_eq j.2) z w

theorem ptCoord_choiceIsometry (j : Option (Fin m) × Bool) (x : Pt m) (k : Option (Fin m)) :
    ptCoord (choiceIsometry j x) k = choiceSign j.2 k * ptCoord x (Equiv.swap none j.1 k) :=
  congrFun (ptCoord_signedPermPt _ _ x) k

/-- With the sign of `ξ_{k₀}`, the first coordinate of `A_j ξ` is `|ξ_{k₀}|`. -/
theorem choiceIsometry_fst (ξ : Pt m) (k₀ : Option (Fin m)) :
    (choiceIsometry (k₀, decide (0 < ptCoord ξ k₀)) ξ).ofLp.1 = |ptCoord ξ k₀| := by
  have h := ptCoord_choiceIsometry (k₀, decide (0 < ptCoord ξ k₀)) ξ none
  rw [Equiv.swap_apply_left] at h
  rw [show (choiceIsometry (k₀, decide (0 < ptCoord ξ k₀)) ξ).ofLp.1 =
    ptCoord (choiceIsometry (k₀, decide (0 < ptCoord ξ k₀)) ξ) none from rfl, h]
  by_cases hc : 0 < ptCoord ξ k₀
  · simp [choiceSign, hc, abs_of_pos hc]
  · simp [choiceSign, hc, abs_of_nonpos (not_lt.1 hc)]

/-- The transverse coordinates of `A_j ξ` are coordinates of `ξ`. -/
theorem choiceIsometry_snd (j : Option (Fin m) × Bool) (ξ : Pt m) (i : Fin m) :
    (choiceIsometry j ξ).ofLp.2 i = ptCoord ξ (Equiv.swap none j.1 (some i)) := by
  show ptCoord (choiceIsometry j ξ) (some i) = _
  rw [ptCoord_choiceIsometry]
  simp [choiceSign]

/-- A point with nonzero first coordinate `a` is `a (1, a⁻¹ x')`. -/
theorem smul_slopeVec_inv {x : Pt m} (hx : x.ofLp.1 ≠ 0) :
    x.ofLp.1 • slopeVec ((x.ofLp.1)⁻¹ • x.ofLp.2) = x := by
  apply ptCoord_injective
  funext k
  cases k with
  | none => simp [ptCoord, slopeVec]
  | some j =>
    simp only [ptCoord, slopeVec, Option.elim]
    exact mul_inv_cancel_left₀ hx _

/-- **The distance in the new coordinates**: with `A_j ξ = a(1, t₀)`,
`|Φ_j⌊nξ⌋ − n a (1, t₀)| = |⌊nξ⌋ − nξ| ≤ √d`. -/
theorem norm_choice_floorVertex_sub_le (j : Option (Fin m) × Bool) {ξ : Pt m}
    (hξ : (choiceIsometry j ξ).ofLp.1 ≠ 0) (n : ℕ) :
    ‖point (choiceIso j (floorVertex ((n : ℝ) • ξ))) -
        ((n : ℝ) * (choiceIsometry j ξ).ofLp.1) •
          slopeVec (((choiceIsometry j ξ).ofLp.1)⁻¹ • (choiceIsometry j ξ).ofLp.2)‖ ≤
      Real.sqrt ((m : ℝ) + 1) := by
  rw [point_choiceIso, mul_smul, smul_slopeVec_inv hξ, ← map_smul, ← map_sub,
    LinearIsometryEquiv.norm_map]
  exact norm_point_floorVertex_sub_le _

/-! ## The choice of coordinates at one direction -/

/-- **The choice of coordinates at one direction** (as at the beginning of Section `sec:prelim`,
for the theorem at one direction, which is not in the paper) from Lemma `lem:chart`. -/
theorem reductionStatement_of_chart (m : ℕ) (hchart : ChartStatement m) :
    ReductionStatement m := by
  intro hm F _ hW P _ hP μ hμ ξ hξ H hH hC
  obtain ⟨k₀, hk₀⟩ := exists_ptCoord_ne_zero hξ
  -- the signed permutation: the coordinate `k₀` first, with the sign of `ξ_{k₀}`
  set j : Option (Fin m) × Bool := (k₀, decide (0 < ptCoord ξ k₀)) with hj
  set A := choiceIsometry j with hA
  -- the direction in the new coordinates: `A ξ = a (1, t₀)` with `a = |ξ_{k₀}| > 0`
  set ξ' := A ξ with hξ'
  set a := ξ'.ofLp.1 with ha_def
  have ha : 0 < a := by
    rw [ha_def, hξ', hA, hj, choiceIsometry_fst]
    exact abs_pos.2 hk₀
  -- the time constant, the curvature hypothesis and the chart in the new coordinates
  set μ' := transportNorm μ A
  have hμ' : IsTimeConstant P μ' := isTimeConstant_transportNorm hP hμ (choiceIso j)
    (choiceIso_zero j) (choiceIso_add j) A (point_choiceIso j)
  obtain ⟨δ, hδ0, hδ1, r₀, hr₀, C, -, p₀, q₀, hq₀, hcurv⟩ :=
    hchart μ' ξ' _ ha (isCompl_map hH A) (assumptionCAt_transportNorm hC A)
  have hM : (⟨⟨F, P, μ', δ⟩, C, r₀, a⁻¹ • ξ'.ofLp.2, p₀, q₀⟩ : Model m).Standing :=
    { one_le_m := hm, probF := inferInstance, assumptionW := hW, probP := inferInstance,
      iid := hP, timeConstant := hμ', delta_pos := hδ0, delta_le_one := hδ1,
      rrem_pos := hr₀, q₀_posDef := hq₀, curvature := hcurv }
  refine ⟨⟨⟨F, P, μ', δ⟩, C, r₀, a⁻¹ • ξ'.ofLp.2, p₀, q₀⟩, choiceIso j, a,
    Real.sqrt ((m : ℝ) + 1), hM, ha, fun n => ?_, fun n => ?_⟩
  · exact evariance_passageTime_apply hP _ (choiceIso_zero j) _
  · exact norm_choice_floorVertex_sub_le j ha.ne' n

/-- **The choice of coordinates at one direction** (as at the beginning of Section `sec:prelim`,
for the theorem at one direction, which is not in the paper): the contract
`Contracts.ReductionStatement`. -/
theorem reductionStatement_holds (m : ℕ) : ReductionStatement m :=
  reductionStatement_of_chart m Chart.chartStatement_holds

/-! ## The choice of coordinates for the uniform theorem -/

/-- A largest coordinate `a` of a unit direction satisfies `1 ≤ d a²` and `a² ≤ 1`. -/
theorem sq_bounds_of_largest {ξ : Pt m} (hξ : ‖ξ‖ = 1) {k₀ : Option (Fin m)}
    (hk₀ : ∀ k, |ptCoord ξ k| ≤ |ptCoord ξ k₀|) :
    1 ≤ ((m : ℝ) + 1) * |ptCoord ξ k₀| ^ 2 ∧ |ptCoord ξ k₀| ^ 2 ≤ 1 := by
  have hsum : (1 : ℝ) = ∑ k, ptCoord ξ k ^ 2 := by
    rw [← norm_sq_eq_sum_ptCoord, hξ, one_pow]
  refine ⟨?_, ?_⟩
  · calc (1 : ℝ) = ∑ k, ptCoord ξ k ^ 2 := hsum
      _ ≤ ∑ _k : Option (Fin m), |ptCoord ξ k₀| ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs (ptCoord ξ k)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hk₀ k) 2
      _ = ((m : ℝ) + 1) * |ptCoord ξ k₀| ^ 2 := by simp
  · rw [sq_abs, hsum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (ptCoord ξ k)) (Finset.mem_univ k₀)

/-- The slope of a unit vector `ζ = (a, ζ')` with `1 ≤ d a²` and `a > 0`: `|a⁻¹ ζ'| ≤ √(d−1)`. -/
theorem norm_inv_smul_snd_le {ζ : Pt m} (hζ : ‖ζ‖ = 1) (ha : 0 < ζ.ofLp.1)
    (hlo : 1 ≤ ((m : ℝ) + 1) * ζ.ofLp.1 ^ 2) :
    ‖(ζ.ofLp.1)⁻¹ • ζ.ofLp.2‖ ≤ Real.sqrt m := by
  set a := ζ.ofLp.1 with ha_def
  have hn : ‖ζ‖ ^ 2 = ‖a‖ ^ 2 + ‖ζ.ofLp.2‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 ζ
  rw [hζ, Real.norm_eq_abs, sq_abs] at hn
  have ht : a * ‖a⁻¹ • ζ.ofLp.2‖ = ‖ζ.ofLp.2‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.le), ← mul_assoc, mul_inv_cancel₀ ha.ne',
      one_mul]
  have h2 : a ^ 2 * ‖a⁻¹ • ζ.ofLp.2‖ ^ 2 ≤ a ^ 2 * m := by
    have e : a ^ 2 * ‖a⁻¹ • ζ.ofLp.2‖ ^ 2 = ‖ζ.ofLp.2‖ ^ 2 := by rw [← ht]; ring
    rw [e]
    linarith only [hn, hlo]
  have h3 : ‖a⁻¹ • ζ.ofLp.2‖ ^ 2 ≤ m := le_of_mul_le_mul_left h2 (pow_pos ha 2)
  simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h3

/-- `c d^{−3/2} ≤ c a³` for `a ≥ d^{−1/2}`, in the form `1 ≤ a √d`. -/
theorem div_le_mul_pow_three {a c : ℝ} (hc : 0 < c) (has : 1 ≤ a * Real.sqrt ((m : ℝ) + 1)) :
    c / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) ≤ c * a ^ 3 := by
  set S := Real.sqrt ((m : ℝ) + 1) with hSdef
  have hS : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hS2 : S ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have h3 : 1 ≤ (a * S) ^ 3 := one_le_pow₀ has
  rw [div_le_iff₀ (by positivity)]
  calc c = c * 1 := (mul_one c).symm
    _ ≤ c * (a * S) ^ 3 := mul_le_mul_of_nonneg_left h3 hc.le
    _ = c * a ^ 3 * (((m : ℝ) + 1) * S) := by rw [← hS2]; ring

end CurvatureVariance.Paper.Proofs.Reduction
