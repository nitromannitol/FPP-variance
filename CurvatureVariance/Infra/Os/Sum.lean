/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Os.Power
public import CurvatureVariance.Infra.Os.Convex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Finite sums without independence

AKM Lemma A.4, p. 457. The convex shift gives a constant depending only
on the exponent; convexity without a shift gives constant one for `s ≥ 1`.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace CurvatureVariance.Infra.Os

/-- A finite-sum Jensen step for any convex majorant of the exponential power. -/
theorem isOs_sum_of_convex {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s B r : ℝ} (hs : 0 < s) (hB : 0 ≤ B) (hr : 1 ≤ r)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ (Ici 0) g)
    (hLower : ∀ x : ℝ, 0 ≤ x → Real.exp (x ^ s) ≤ g x)
    (hUpper : ∀ x : ℝ, 0 ≤ x → g x ≤ B * Real.exp (x ^ s))
    (hBr : ENNReal.ofReal B * 2 ≤ (2 : ℝ≥0∞) ^ r)
    (T : Finset ι) (θ : ι → ℝ) (hθ : ∀ i ∈ T, 0 < θ i)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ T, IsOs P s (θ i) (X i))
    (hX0 : ∀ i ∈ T, 0 ≤ᵐ[P] X i) (hT : T.Nonempty) :
    IsOs P s (r ^ (1 / s) * ∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω) := by
  classical
  let A := ∑ i ∈ T, θ i
  have hA : 0 < A := Finset.sum_pos (fun i hi => hθ i hi) hT
  let w := fun i => θ i / A
  have hw (i) (hi : i ∈ T) : 0 ≤ w i := div_nonneg (hθ i hi).le hA.le
  have hws : ∑ i ∈ T, w i = 1 := by dsimp only [w]; rw [← Finset.sum_div, div_self hA.ne']
  have hMeas : AEMeasurable (fun ω => ∑ i ∈ T, X i ω) P :=
    T.aemeasurable_fun_sum fun i hi => (hX i hi).1
  apply isOs_of_exp_moment_le hs hA hr hMeas
  apply le_trans _ hBr
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal B * ∑ i ∈ T,
        ENNReal.ofReal (w i) * ENNReal.ofReal (Real.exp ((max (X i ω) 0 / θ i) ^ s)) ∂P := by
      apply lintegral_mono_ae
      have hAll : ∀ᵐ ω ∂P, ∀ i ∈ T, 0 ≤ X i ω := by
        refine (Filter.eventually_all_finset T).mpr (fun i hi => ?_)
        exact (hX0 i hi).mono fun ω h => by change (0 : ℝ) ≤ X i ω at h; exact h
      filter_upwards [hAll] with ω hω
      have hSum0 : 0 ≤ ∑ i ∈ T, X i ω := Finset.sum_nonneg fun i hi => hω i hi
      have hEq : ∑ i ∈ T, w i * (X i ω / θ i) = (∑ i ∈ T, X i ω) / A := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [w]
        field_simp [(hθ i hi).ne']
      rw [max_eq_left hSum0]
      have hENN : (∑ i ∈ T, ENNReal.ofReal (w i) * ENNReal.ofReal (Real.exp ((max (X i ω) 0 / θ i) ^ s))) =
          ENNReal.ofReal (∑ i ∈ T, w i * Real.exp ((max (X i ω) 0 / θ i) ^ s)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (hw i hi) (Real.exp_pos _).le)]
        apply Finset.sum_congr rfl
        intro i hi
        exact (ENNReal.ofReal_mul (hw i hi)).symm
      rw [hENN, ← ENNReal.ofReal_mul hB]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ g ((∑ i ∈ T, X i ω) / A) := hLower _ (div_nonneg hSum0 hA.le)
        _ ≤ ∑ i ∈ T, w i * g (X i ω / θ i) := by
          rw [← hEq]
          exact hg.map_sum_le hw hws (fun i hi => div_nonneg (hω i hi) (hθ i hi).le)
        _ ≤ B * ∑ i ∈ T, w i * Real.exp ((max (X i ω) 0 / θ i) ^ s) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          rw [max_eq_left (hω i hi)]
          simpa only [mul_assoc, mul_left_comm B] using
            mul_le_mul_of_nonneg_left (hUpper _ (div_nonneg (hω i hi) (hθ i hi).le)) (hw i hi)
    _ = ENNReal.ofReal B * ∑ i ∈ T, ENNReal.ofReal (w i) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X i ω) 0 / θ i) ^ s)) ∂P) := by
      rw [lintegral_const_mul'' _ (T.aemeasurable_fun_sum fun i hi =>
        (aemeasurable_exp_pos_rpow (hX i hi).1 s (θ i)).const_mul _),
        lintegral_finsetSum' T (fun i hi => (aemeasurable_exp_pos_rpow (hX i hi).1 s (θ i)).const_mul _)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_const_mul'' _ (aemeasurable_exp_pos_rpow (hX i hi).1 s (θ i))
    _ ≤ ENNReal.ofReal B * ∑ i ∈ T, ENNReal.ofReal (w i) * 2 := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      exact Finset.sum_le_sum fun i hi => mul_le_mul le_rfl (hX i hi).2 zero_le zero_le
    _ = ENNReal.ofReal B * 2 := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg hw, hws, ENNReal.ofReal_one, one_mul]

/-- The constant in AKM A.4. For `s < 1`, this is the explicit choice
`σ^(-1/s)` with `σ = log 2 / (log 2 + (1-s)/s)` in its proof. -/
noncomputable def sumConstant (s : ℝ) : ℝ :=
  if 1 ≤ s then 1 else (1 + ((1 - s) / s) / Real.log 2) ^ (1 / s)

/-- The sum constant is positive for every positive exponent. -/
theorem sumConstant_pos {s : ℝ} (hs : 0 < s) : 0 < sumConstant s := by
  unfold sumConstant
  split_ifs with h
  · exact zero_lt_one
  · exact Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (div_nonneg (sub_nonneg.mpr (le_of_not_ge h)) hs.le) (Real.log_pos (by norm_num)).le)) _

/-- For `s ≥ 1`, AKM A.4 has exactly constant one. -/
theorem isOs_sum_ge_one {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : ℝ} (hs : 1 ≤ s)
    (T : Finset ι) (θ : ι → ℝ) (hθ : ∀ i ∈ T, 0 < θ i)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ T, IsOs P s (θ i) (X i))
    (hX0 : ∀ i ∈ T, 0 ≤ᵐ[P] X i) (hT : T.Nonempty) :
    IsOs P s (∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω) := by
  have hConv : ConvexOn ℝ (Ici 0) (fun x : ℝ => Real.exp (x ^ s)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (Real.exp_le_exp.mpr ((convexOn_rpow hs).2 hx hy ha hb hab)).trans
      (convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hab)
  have hh := isOs_sum_of_convex (zero_lt_one.trans_le hs) (show (0 : ℝ) ≤ 1 by norm_num)
    (r := 1) le_rfl _ hConv (fun _ _ => le_rfl) (fun x _ => by rw [one_mul])
    (by norm_num) T θ hθ X hX hX0 hT
  simpa only [Real.one_rpow, one_mul] using hh

/-- AKM A.4 for finite nonnegative families, with no independence. -/
theorem isOs_sum {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : ℝ} (hs : 0 < s)
    (T : Finset ι) (θ : ι → ℝ) (hθ : ∀ i ∈ T, 0 < θ i)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ T, IsOs P s (θ i) (X i))
    (hX0 : ∀ i ∈ T, 0 ≤ᵐ[P] X i) (hT : T.Nonempty) :
    IsOs P s (sumConstant s * ∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω) := by
  classical
  by_cases hs1 : 1 ≤ s
  · simpa only [sumConstant, ite_eq_left hs1, one_mul] using isOs_sum_ge_one hs1 T θ hθ X hX hX0 hT
  have hslt : s < 1 := lt_of_not_ge hs1
  let a := ((1 - s) / s) ^ (1 / s)
  have hapos : 0 < a := Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hslt) hs) _
  have ha : a ^ s = (1 - s) / s := by
    dsimp only [a]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
  let r := 1 + a ^ s / Real.log 2
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hr : 1 ≤ r := le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg hapos.le _) hlog.le)
  have hConv := convexOn_exp_rpow_shift hs hapos (by rw [ha, mul_div_cancel₀ _ hs.ne'])
  have hLower (x : ℝ) (hx : 0 ≤ x) : Real.exp (x ^ s) ≤ Real.exp ((x + a) ^ s) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow hx (le_add_of_nonneg_right hapos.le) hs.le)
  have hUpper (x : ℝ) (hx : 0 ≤ x) : Real.exp ((x + a) ^ s) ≤ Real.exp (a ^ s) * Real.exp (x ^ s) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr ((Real.rpow_add_le_add_rpow hx hapos.le hs.le hslt.le).trans_eq (add_comm _ _))
  have hBr : ENNReal.ofReal (Real.exp (a ^ s)) * 2 ≤ (2 : ℝ≥0∞) ^ r := by
    apply le_of_eq
    rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show Real.log 2 * r = a ^ s + Real.log 2 by dsimp only [r]; field_simp; ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hh := isOs_sum_of_convex hs (Real.exp_pos _).le hr _ hConv hLower hUpper hBr T θ hθ X hX hX0 hT
  simpa only [sumConstant, ite_eq_right hs1, r, ha] using hh

/-- Finite sums of arbitrary real variables obey the same bound: replacing each
summand by its positive part reduces this to AKM A.4. This is the form used in
the lattice paper's notation paragraph. -/
theorem isOs_sum_le {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : ℝ} (hs : 0 < s)
    (T : Finset ι) (θ : ι → ℝ) (hθ : ∀ i ∈ T, 0 < θ i)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ T, IsOs P s (θ i) (X i)) (hT : T.Nonempty) :
    IsOs P s (sumConstant s * ∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω) := by
  let Y := fun i ω => max (X i ω) 0
  have hY (i) (hi : i ∈ T) : IsOs P s (θ i) (Y i) := by
    refine ⟨(hX i hi).1.max aemeasurable_const, ?_⟩
    simpa only [Y, max_assoc, max_self] using (hX i hi).2
  have hh := isOs_sum hs T θ hθ Y hY
    (fun i _ => Filter.Eventually.of_forall fun ω => le_max_right (X i ω) 0) hT
  exact hh.mono hs.le (mul_pos (sumConstant_pos hs) (Finset.sum_pos hθ hT))
    (T.aemeasurable_fun_sum fun i hi => (hX i hi).1)
    (Filter.Eventually.of_forall fun ω => Finset.sum_le_sum fun i _ => le_max_left (X i ω) 0)

end CurvatureVariance.Infra.Os
