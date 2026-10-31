/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanDefs
public import CurvatureVariance.Statements.TimeConstant.IsTimeConstant
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The mean passage time

Basic properties of `h(x) = E T(0, x)` (`meanTime`) under a translation-invariant law:
- `E T(u, v) = h(v - u)`;
- `h(0) = 0` and `h ≥ 0`;
- subadditivity, `h(-x) = h(x)` and `h(n x) ≤ n h(x)`.

Two consequences of the time-constant property `T(0, n x)/n → μ(x)` almost surely
(`IsTimeConstant`):
- **`E T ≥ μ`** (the left inequality of [ADH, Thm 3.33]), by Fatou's lemma and
  `h(n x) ≤ n h(x)` (`le_meanTime`);
- the convergence in probability used in Alexander's argument (`tendsto_measure_lt_passageTime`).

The translation invariance of the law of independent weights is
`IsIIDWeights.measurePreserving_translate` (`CurvatureVariance.Infra.FPP.Model`), and
`passageTime_self` is in `CurvatureVariance.Infra.FPP.Walks`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ} {P : Measure (Config m)}

@[simp] theorem meanTime_zero : meanTime P 0 = 0 := by
  simp [meanTime]

theorem meanTime_nonneg (x : Vertex m) : 0 ≤ meanTime P x :=
  integral_nonneg fun _ => NNReal.coe_nonneg _

section Invariant

variable (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
include hT

/-- `E T(u, v) = h(v - u)` under a translation-invariant law. -/
theorem integral_passageTime_eq_meanTime (u v : Vertex m) :
    ∫ ω, (passageTime ω u v : ℝ) ∂P = meanTime P (v - u) := by
  have := integral_passageTime_add (hT u) 0 (v - u)
  simp only [zero_add, sub_add_cancel] at this
  exact this

/-- `h(-x) = h(x)`. -/
theorem meanTime_neg (x : Vertex m) : meanTime P (-x) = meanTime P x := by
  have h1 : meanTime P (-x) = ∫ ω, (passageTime ω (-x) 0 : ℝ) ∂P := by
    unfold meanTime
    congr 1
    funext ω
    rw [passageTime_symm]
  rw [h1, integral_passageTime_eq_meanTime hT, zero_sub, neg_neg]

variable (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
include hI

/-- **Subadditivity** of the mean passage time. -/
theorem meanTime_add_le (x y : Vertex m) : meanTime P (x + y) ≤ meanTime P x + meanTime P y := by
  have hpt : ∀ ω : Config m, (passageTime ω 0 (x + y) : ℝ) ≤
      passageTime ω 0 x + passageTime ω x (x + y) := fun ω => by
    exact_mod_cast passageTime_triangle ω 0 x (x + y)
  calc meanTime P (x + y) ≤ ∫ ω, ((passageTime ω 0 x : ℝ) + passageTime ω x (x + y)) ∂P :=
        integral_mono (hI 0 (x + y)) ((hI 0 x).add (hI x (x + y))) hpt
    _ = meanTime P x + meanTime P y := by
        rw [integral_add (hI 0 x) (hI x (x + y)), integral_passageTime_eq_meanTime hT x (x + y),
          add_sub_cancel_left]
        rfl

/-- `h(n x) ≤ n h(x)`. -/
theorem meanTime_nsmul_le (n : ℕ) (x : Vertex m) : meanTime P (n • x) ≤ n * meanTime P x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    calc meanTime P (n • x + x) ≤ meanTime P (n • x) + meanTime P x := meanTime_add_le hT hI _ _
      _ ≤ n * meanTime P x + meanTime P x := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) * meanTime P x := by push_cast; ring

/-- **`E T ≥ μ`**: under the time-constant property, `μ(x) ≤ E T(0, x)` at every lattice
point, by Fatou's lemma along `T(0, n x)/n → μ(x)` and `E T(0, n x) ≤ n E T(0, x)`. -/
theorem le_meanTime [IsProbabilityMeasure P] {μ : PtNorm m} (hμ : IsTimeConstant P μ)
    (x : Vertex m) : μ.1 (point x) ≤ meanTime P x := by
  set f : ℕ → Config m → ℝ := fun n ω => (passageTime ω 0 (n • x) : ℝ) / n with hf
  have hf0 : ∀ n ω, 0 ≤ f n ω := fun n ω => div_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg n)
  have hfm : ∀ n, Measurable (f n) := fun n => (measurable_passageTime_real 0 (n • x)).div_const _
  have hfi : ∀ n, Integrable (f n) P := fun n => (hI 0 (n • x)).div_const _
  have key : ENNReal.ofReal (μ.1 (point x)) ≤ ENNReal.ofReal (meanTime P x) := by
    calc ENNReal.ofReal (μ.1 (point x)) = ∫⁻ _, ENNReal.ofReal (μ.1 (point x)) ∂P := by
          rw [lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hμ x] with ω hω
          exact (((ENNReal.continuous_ofReal.tendsto _).comp hω).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop :=
          lintegral_liminf_le fun n => (hfm n).ennreal_ofReal
      _ ≤ ENNReal.ofReal (meanTime P x) := by
          refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
          filter_upwards [eventually_ge_atTop 1] with n hn
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hf0 n))]
          refine ENNReal.ofReal_le_ofReal ?_
          have hn' : (0 : ℝ) < n := by exact_mod_cast hn
          rw [hf, integral_div, div_le_iff₀ hn', mul_comm]
          exact meanTime_nsmul_le hT hI n x
  exact (ENNReal.ofReal_le_ofReal_iff (meanTime_nonneg x)).1 key

end Invariant

/-- **Convergence in probability** under the time-constant property at `x`: for `δ > 0`,
`P(T(0, N x) > N (μ(x) + δ)) → 0`. -/
theorem tendsto_measure_lt_passageTime [IsFiniteMeasure P] {μ : PtNorm m} {x : Vertex m}
    (hμx : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (passageTime ω 0 (n • x) : ℝ) / n) atTop (𝓝 (μ.1 (point x))))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => P {ω | (N : ℝ) * (μ.1 (point x) + δ) < passageTime ω 0 (N • x)})
      atTop (𝓝 0) := by
  have hTIM := tendstoInMeasure_of_tendsto_ae
    (f := fun (n : ℕ) (ω : Config m) => (passageTime ω 0 (n • x) : ℝ) / n)
    (g := fun _ => μ.1 (point x))
    (fun n => ((measurable_passageTime_real 0 (n • x)).div_const _).aestronglyMeasurable) hμx
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hTIM (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)) (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [edist_dist, Real.dist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have : μ.1 (point x) + δ < (passageTime ω 0 (N • x) : ℝ) / N := by
    rw [lt_div_iff₀ hN', mul_comm]; exact hω
  rw [abs_of_pos (by linarith)]
  linarith

end CurvatureVariance.Infra.FPP
