/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.OsTail
public import CurvatureVariance.Paper.Defs.Basic
public import CurvatureVariance.Infra.FPP.Statements
import CurvatureVariance.Statements.Inputs.MeasureAbsPassageTimeSubIntegralLe

/-!
# The tails of `T − E T`, from [ADH, Theorem 3.13] and the Chernoff bound

The first bound of equation `eq:classical` follows (the text after it) from [ADH, Theorem 3.13],
"which gives Gaussian tails for the lower deviations at all scales and for the upper deviations up
to a fixed multiple of `|x|₁`", and "the Chernoff bound for the weights along a path of `|x|₁`
edges", which "gives the larger upper deviations". Bound (1) of Lemma `lem:good` uses the same
inputs (the proof of Lemma `lem:good`). This file composes them, for `r = |x|₁ ≥ 1`, in one form,
`P(±(T − E T) ≥ z) ≤ e^{−ρ min(z²/r, z)}` for all `z ≥ 0`:

* `measure_le_passageTimeReal_le`: the Chernoff bound for a coordinate path;
* `measure_le_of_gauss_of_chernoff`, `measure_le_neg_of_gauss`: the arithmetic of the composition.
  For the upper deviations there are three ranges: `z ≤ C₂ r`, [ADH, Theorem 3.13];
  `C₂ r ≤ z ≤ A r`, where `A` is large enough for Chernoff, [ADH, Theorem 3.13] at the level
  `C₂ r`, by monotonicity; `z ≥ A r`,
  the Chernoff bound, since `T − E T ≥ z` gives `T ≥ z` as `E T ≥ 0`;
* `exists_tails_zero_of_law`: the two tails from `0` to `x`, from the cited
  `CurvatureVariance.measure_abs_passageTime_sub_integral_le`;
* `exists_tails_of_law`: the same from `u` to `v`, by translation invariance;
* `isAbsOs_of_tails`: `|X| ≤ O₁(C √r)` from such tails, through
  `isOs_one_of_measure_ge_le_mul_exp`, which uses the cited
  `CurvatureVariance.isOs_of_measure_ge_le`.

Reading. The Chernoff bound is the paper's input after equation `eq:classical` and in the proof of
Lemma `lem:good`, and it is used in the form `P(cost ≥ z) ≤ e^{−αz} M^r`, not through the bound
`O₁(Cm)` of the text before equation `eq:classical`. That bound has a tail at the scale `r`, and at
the level `z ≈ r` the tail of `eq:classical` is at the scale `r^{1/2}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

theorem oneNorm_eq_l1Dist (x : Vertex m) : oneNorm x = (l1Dist 0 x : ℝ) := by
  rw [oneNorm, l1Dist_zero_eq]

theorem one_le_oneNorm {x : Vertex m} (hx : x ≠ 0) : 1 ≤ oneNorm x := by
  rw [oneNorm_eq_l1Dist]
  exact_mod_cast one_le_l1Dist_zero hx

/-! ## The composition -/

/-- The rate `ρ = min(C₁, C₁ C₂² / A, α/2)` of the tails, `A = C₂ + 2κ/α`. -/
noncomputable def classicalRate (C₁ C₂ α κ : ℝ) : ℝ :=
  min (min C₁ (C₁ * C₂ ^ 2 / (C₂ + 2 * κ / α))) (α / 2)

theorem classicalRate_pos {C₁ C₂ α κ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hα : 0 < α)
    (hκ : 0 ≤ κ) : 0 < classicalRate C₁ C₂ α κ :=
  lt_min (lt_min hC₁ (by positivity)) (by positivity)

section Composition

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The lower deviations**: a Gaussian tail at all scales gives the tail of the common form. -/
theorem measure_le_neg_of_gauss {D : Ω → ℝ} {C₁ ρ r z : ℝ} (hC₁ : 0 < C₁) (hρ : ρ ≤ C₁)
    (hr : 1 ≤ r) (hz : 0 ≤ z)
    (hgauss : ∀ t : ℝ, 0 ≤ t → P {ω | D ω ≤ -(t * √r)} ≤
      ENNReal.ofReal (Real.exp (-(C₁ * t ^ 2)))) :
    P {ω | D ω ≤ -z} ≤ ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / r) z))) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hs : 0 < √r := Real.sqrt_pos.2 hr0
  have hts : z / √r * √r = z := div_mul_cancel₀ _ hs.ne'
  have ht2 : (z / √r) ^ 2 = z ^ 2 / r := by rw [div_pow, Real.sq_sqrt hr0.le]
  have h := hgauss (z / √r) (by positivity)
  rw [hts, ht2] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_)))
  exact mul_le_mul hρ (min_le_left _ _) (le_min (by positivity) hz) hC₁.le

/-- **The upper deviations**: a Gaussian tail up to `C₂ r` and the Chernoff bound give the tail of
the common form, at the rate `classicalRate`. -/
theorem measure_le_of_gauss_of_chernoff {D : Ω → ℝ} {C₁ C₂ α κ r z : ℝ} (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hα : 0 < α) (hκ : 0 ≤ κ) (hr : 1 ≤ r) (hz : 0 ≤ z)
    (hgauss : ∀ t : ℝ, 0 ≤ t → t ≤ C₂ * √r → P {ω | t * √r ≤ D ω} ≤
      ENNReal.ofReal (Real.exp (-(C₁ * t ^ 2))))
    (hchernoff : P {ω | z ≤ D ω} ≤ ENNReal.ofReal (Real.exp (-(α * z) + κ * r))) :
    P {ω | z ≤ D ω} ≤
      ENNReal.ofReal (Real.exp (-(classicalRate C₁ C₂ α κ * min (z ^ 2 / r) z))) := by
  set ρ := classicalRate C₁ C₂ α κ with hρdef
  set A := C₂ + 2 * κ / α with hA
  have hρ1 : ρ ≤ C₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ C₁ * C₂ ^ 2 / A := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ρ ≤ α / 2 := min_le_right _ _
  have hr0 : 0 < r := by linarith only [hr]
  have hs : 0 < √r := Real.sqrt_pos.2 hr0
  have hA0 : 0 < A := by positivity
  have hmin0 : 0 ≤ min (z ^ 2 / r) z := le_min (by positivity) hz
  rcases le_or_gt z (C₂ * r) with h1 | h1
  · -- the Gaussian range of [ADH, Theorem 3.13]
    have hts : z / √r * √r = z := div_mul_cancel₀ _ hs.ne'
    have ht2 : (z / √r) ^ 2 = z ^ 2 / r := by rw [div_pow, Real.sq_sqrt hr0.le]
    have htC : z / √r ≤ C₂ * √r := by
      rw [div_le_iff₀ hs, mul_assoc, Real.mul_self_sqrt hr0.le]
      exact h1
    have h := hgauss (z / √r) (by positivity) htC
    rw [hts, ht2] at h
    refine h.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_)))
    exact mul_le_mul hρ1 (min_le_left _ _) hmin0 hC₁.le
  rcases le_or_gt z (A * r) with h2 | h2
  · -- [ADH, Theorem 3.13] at the level `C₂ r`, by monotonicity
    have hlevel : C₂ * √r * √r = C₂ * r := by rw [mul_assoc, Real.mul_self_sqrt hr0.le]
    have hsub : {ω | z ≤ D ω} ⊆ {ω | C₂ * √r * √r ≤ D ω} := fun ω hω => by
      simp only [Set.mem_ofPred_eq, hlevel] at hω ⊢
      exact h1.le.trans hω
    refine (measure_mono hsub).trans ((hgauss (C₂ * √r) (by positivity) le_rfl).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))))
    rw [mul_pow, Real.sq_sqrt hr0.le]
    calc ρ * min (z ^ 2 / r) z
        ≤ C₁ * C₂ ^ 2 / A * (A * r) :=
          mul_le_mul hρ2 ((min_le_right _ _).trans h2) hmin0 (by positivity)
      _ = C₁ * (C₂ ^ 2 * r) := by field_simp
  · -- the Chernoff bound
    refine hchernoff.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have h3 : 2 * κ / α * r ≤ A * r :=
      mul_le_mul_of_nonneg_right (by rw [hA]; linarith only [hC₂]) hr0.le
    have h4 : 2 * κ * r ≤ z * α := by
      have h5 : 2 * κ / α * r ≤ z := by linarith only [h3, h2]
      rwa [div_mul_eq_mul_div, div_le_iff₀ hα] at h5
    have h6 : ρ * min (z ^ 2 / r) z ≤ α / 2 * z :=
      mul_le_mul hρ3 (min_le_right _ _) hmin0 (by positivity)
    linarith only [h4, h6]

/-- The constant of the `O₁` bound of `isAbsOs_of_tails`. -/
noncomputable def tailOsConst (ρ : ℝ) : ℝ :=
  (1 + Real.log (2 * Real.exp ρ) / (2 * Real.log 2)) * (2 * (1 / ρ))

theorem tailOsConst_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < tailOsConst ρ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK : 0 ≤ Real.log (2 * Real.exp ρ) := by
    refine Real.log_nonneg ?_
    linarith only [Real.one_le_exp hρ.le]
  unfold tailOsConst
  positivity

/-- **`|X| ≤ O₁(C √r)` from the tails**: if `P(X ≤ −z)` and `P(X ≥ z)` are at most
`e^{−ρ min(z²/r, z)}` for `z ≥ 0`, with `r ≥ 1`, then `|X| ≤ O₁(C √r)`, with `C` depending on `ρ`
only. At the level `z = (y/ρ) √r` the exponent is at least `y − ρ`, which is the prefactor. -/
theorem isAbsOs_of_tails [IsProbabilityMeasure P] {X : Ω → ℝ} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 1 ≤ r)
    (hX : AEMeasurable X P)
    (hlow : ∀ z : ℝ, 0 ≤ z → P {ω | X ω ≤ -z} ≤
      ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / r) z))))
    (hup : ∀ z : ℝ, 0 ≤ z → P {ω | z ≤ X ω} ≤
      ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / r) z)))) :
    IsAbsOs P 1 (tailOsConst ρ * √r) X := by
  have hr0 : 0 < r := by linarith only [hr]
  have hs1 : 1 ≤ √r := by rwa [Real.one_le_sqrt]
  have hs : 0 < √r := by linarith only [hs1]
  set K := 2 * Real.exp ρ with hK
  have hK1 : 1 ≤ K := by linarith only [Real.one_le_exp hρ.le, hK]
  set θ := 1 / ρ * √r with hθ
  have hθ0 : 0 < θ := by positivity
  have hW : AEMeasurable (fun ω => |X ω|) P := continuous_abs.measurable.comp_aemeasurable hX
  have hexp : ∀ y : ℝ, 0 ≤ y → y - ρ ≤ ρ * min ((θ * y) ^ 2 / r) (θ * y) := by
    intro y hy
    have h1 : (θ * y) ^ 2 / r = (y / ρ) ^ 2 := by
      rw [hθ]
      field_simp
      rw [Real.sq_sqrt hr0.le]
      field_simp
    have h2 : y / ρ ≤ θ * y := by
      rw [hθ, show y / ρ = 1 / ρ * 1 * y by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 (by positivity)) hy
    rw [h1]
    have hmul : ρ * (y / ρ) = y := mul_div_cancel₀ _ hρ.ne'
    have h3 : y - ρ ≤ ρ * (y / ρ) ^ 2 := by
      have : ρ * (y / ρ) ^ 2 * ρ = y ^ 2 := by field_simp
      have h4 : (y - ρ) * ρ ≤ ρ * (y / ρ) ^ 2 * ρ := by
        rw [this]
        nlinarith only [sq_nonneg (y - ρ), sq_nonneg y, sq_nonneg ρ]
      exact le_of_mul_le_mul_right h4 hρ
    have h5 : y - ρ ≤ ρ * (θ * y) := by
      have := mul_le_mul_of_nonneg_left h2 hρ.le
      linarith only [this, hmul, hρ]
    rcases min_cases ((y / ρ) ^ 2) (θ * y) with ⟨h6, -⟩ | ⟨h6, -⟩ <;> rw [h6] <;> assumption
  have htail : ∀ y : ℝ, 0 ≤ y → P {ω | θ * y ≤ |X ω|} ≤
      ENNReal.ofReal (K * Real.exp (-y)) := by
    intro y hy
    have hz : 0 ≤ θ * y := by positivity
    have hsub : {ω | θ * y ≤ |X ω|} ⊆ {ω | X ω ≤ -(θ * y)} ∪ {ω | θ * y ≤ X ω} := fun ω hω =>
      (le_abs.1 hω).symm.imp (fun h => by simpa only [Set.mem_ofPred_eq] using
        (le_neg.1 h : X ω ≤ -(θ * y))) id
    have hbound : Real.exp (-(ρ * min ((θ * y) ^ 2 / r) (θ * y))) ≤
        Real.exp ρ * Real.exp (-y) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith only [hexp y hy])
    calc P {ω | θ * y ≤ |X ω|}
        ≤ P {ω | X ω ≤ -(θ * y)} + P {ω | θ * y ≤ X ω} :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (Real.exp ρ * Real.exp (-y)) +
            ENNReal.ofReal (Real.exp ρ * Real.exp (-y)) :=
          add_le_add ((hlow _ hz).trans (ENNReal.ofReal_le_ofReal hbound))
            ((hup _ hz).trans (ENNReal.ofReal_le_ofReal hbound))
      _ = ENNReal.ofReal (K * Real.exp (-y)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), hK]
          congr 1
          ring
  have h := isOs_one_of_measure_ge_le_mul_exp hθ0 hK1 hW htail
  refine ⟨hX, ?_⟩
  convert h using 1
  rw [tailOsConst, hθ]
  ring

end Composition

/-! ## The tails of the passage time -/

/-- **The Chernoff bound for the weights along a path of `|x|₁` edges** (the text after equation
`eq:classical`): `P(T(0, x) ≥ z) ≤ e^{−αz} M^{|x|₁}`, `M = E e^{ατ}`. -/
theorem measure_le_passageTimeReal_le {P : Measure (Config m)} {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] (hP : IsIIDWeights P F) {α : ℝ} (hα : 0 ≤ α)
    (hexp : Integrable (fun x : ℝ≥0 => Real.exp (α * x)) F) (x : Vertex m) (z : ℝ) :
    P {ω | z ≤ passageTimeReal ω 0 x} ≤
      ENNReal.ofReal (Real.exp (-(α * z) + Real.log (expMom F α) * oneNorm x)) := by
  obtain ⟨p, hp, hl⟩ := exists_isPath_length_eq_l1Dist 0 x
  have hM : 0 < expMom F α := by linarith only [one_le_expMom hα hexp]
  have hsub : {ω | z ≤ passageTimeReal ω 0 x} ⊆ {ω | z ≤ (walkCost ω p : ℝ)} := fun ω hω =>
    le_trans hω (NNReal.coe_le_coe.2 (passageTime_le_walkCost ω p))
  refine (measure_mono hsub).trans ((IsIIDWeights.measure_le_walkCost_le hP p
    hp.isTrail.edges_nodup hα hexp z).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  have hMn : (∫ x : ℝ≥0, Real.exp (α * x) ∂F) ^ l1Dist 0 x =
      Real.exp ((l1Dist 0 x : ℝ) * Real.log (expMom F α)) := by
    rw [Real.exp_nat_mul, Real.exp_log hM]
    rfl
  rw [hl, hMn, ← Real.exp_add, oneNorm_eq_l1Dist]
  congr 1
  ring

/-- **The two tails from `0` to `x`** (the text after equation `eq:classical`): from the cited
[ADH, Theorem 3.13] and the Chernoff bound, `P(±(T(0,x) − E T(0,x)) ≥ z) ≤ e^{−ρ min(z²/r, z)}`,
`r = |x|₁`. The rate depends on the law only. -/
theorem exists_tails_zero_of_law {L : Law m} (hL : L.Valid) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : Vertex m, x ≠ 0 →
      Integrable (fun ω => passageTimeReal ω 0 x) L.P ∧ ∀ z : ℝ, 0 ≤ z →
        L.P {ω | passageTimeReal ω 0 x - ∫ ω', passageTimeReal ω' 0 x ∂L.P ≤ -z} ≤
            ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / oneNorm x) z))) ∧
        L.P {ω | z ≤ passageTimeReal ω 0 x - ∫ ω', passageTimeReal ω' 0 x ∂L.P} ≤
            ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / oneNorm x) z))) := by
  have := hL.probF
  have := hL.probP
  obtain ⟨C₁, C₂, hC₁, hC₂, hadh⟩ :=
    CurvatureVariance.measure_abs_passageTime_sub_integral_le hL.one_le_m L.F hL.assumptionW
  obtain ⟨⟨α, hα, hexp⟩, -⟩ := hL.assumptionW
  have hκ : 0 ≤ Real.log (expMom L.F α) := Real.log_nonneg (one_le_expMom hα.le hexp)
  have hρ := classicalRate_pos hC₁ hC₂ hα hκ
  refine ⟨_, hρ, fun x hx => ?_⟩
  obtain ⟨hint, hup, hlow⟩ := hadh L.P hL.iid x hx
  have hr : 1 ≤ oneNorm x := one_le_oneNorm hx
  have hET : 0 ≤ ∫ ω, passageTimeReal ω 0 x ∂L.P :=
    integral_nonneg fun ω => NNReal.coe_nonneg _
  refine ⟨hint, fun z hz => ⟨?_, ?_⟩⟩
  · exact measure_le_neg_of_gauss hC₁ ((min_le_left _ _).trans (min_le_left _ _)) hr hz hlow
  · refine measure_le_of_gauss_of_chernoff hC₁ hC₂ hα hκ hr hz hup
      ((measure_mono fun ω hω => ?_).trans (measure_le_passageTimeReal_le hL.iid hα.le hexp x z))
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith only [hω, hET]

/-- A law of `T(u, v) − E T(u, v)` equals that of `T(0, v − u) − E T(0, v − u)`, by translation
invariance. -/
theorem measure_passageTimeReal_sub_mem_eq {P : Measure (Config m)}
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P) (u v : Vertex m) {B : Set ℝ}
    (hB : MeasurableSet B) :
    P {ω | passageTimeReal ω u v - ∫ ω', passageTimeReal ω' u v ∂P ∈ B} =
      P {ω | passageTimeReal ω 0 (v - u) - ∫ ω', passageTimeReal ω' 0 (v - u) ∂P ∈ B} := by
  have h := identDistrib_passageTime_add (hT u) 0 (v - u)
  have e := integral_passageTime_add (hT u) 0 (v - u)
  simp only [zero_add, sub_add_cancel] at h e
  have e' : ∫ ω', passageTimeReal ω' u v ∂P = ∫ ω', passageTimeReal ω' 0 (v - u) ∂P := e
  rw [e']
  set c := ∫ ω', passageTimeReal ω' 0 (v - u) ∂P
  have hB' : MeasurableSet ((fun t : ℝ≥0 => (t : ℝ) - c) ⁻¹' B) :=
    (measurable_coe_nnreal_real.sub_const c) hB
  exact h.measure_mem_eq hB'

/-- **The two tails from `u` to `v`** (the pairs of bound (1) of Lemma `lem:good`): the tails of
`exists_tails_zero_of_law`, by translation invariance. -/
theorem exists_tails_of_law {L : Law m} (hL : L.Valid) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u v : Vertex m, u ≠ v → ∀ z : ℝ, 0 ≤ z →
      L.P {ω | passageTimeReal ω u v - ∫ ω', passageTimeReal ω' u v ∂L.P ≤ -z} ≤
          ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / oneNorm (v - u)) z))) ∧
      L.P {ω | z ≤ passageTimeReal ω u v - ∫ ω', passageTimeReal ω' u v ∂L.P} ≤
          ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / oneNorm (v - u)) z))) := by
  have := hL.probF
  have := hL.probP
  obtain ⟨ρ, hρ, h⟩ := exists_tails_zero_of_law hL
  refine ⟨ρ, hρ, fun u v huv z hz => ?_⟩
  have hT : ∀ a : Vertex m, MeasurePreserving (translate a) L.P L.P :=
    fun a => IsIIDWeights.measurePreserving_translate hL.iid a
  obtain ⟨hlow, hup⟩ := (h (v - u) (sub_ne_zero.2 huv.symm)).2 z hz
  have e1 := measure_passageTimeReal_sub_mem_eq hT u v (measurableSet_Iic (a := -z))
  have e2 := measure_passageTimeReal_sub_mem_eq hT u v (measurableSet_Ici (a := z))
  simp only [Set.mem_Iic, Set.mem_Ici] at e1 e2
  rw [e1, e2]
  exact ⟨hlow, hup⟩

end CurvatureVariance.Paper.Proofs.Geometry
