/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.TimeConstantLimit
public import CurvatureVariance.Infra.FPP.TimeConstantNorm
public import CurvatureVariance.Infra.FPP.ConcentrationScale
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The time constant of first-passage percolation

For the law `P` of independent weights with an integrable law `F`, the cheap-path estimate
`CheapPaths P a c` and the concentration `PassageTimeConcentration P C₀ c₀`:

* **existence** (`exists_isTimeConstant_of_cheapPaths`, [ADH, Theorems 2.1 and 2.5]):
  1. Fekete's lemma gives `g(z) = lim E T(0, n z)/n` on `ℤ^d` (`latticeTimeConstant`);
  2. the concentration and Borel–Cantelli give `T(0, n z)/n → g(z)` almost surely;
  3. `g` is homogeneous, subadditive and symmetric, with `a |z| ≤ g(z) ≤ d E τ |z|` (the cheap-path
     estimate for the lower bound);
  4. so `g` is the restriction of a norm (`exists_ptNorm_extend`);
  5. the convergence holds in `L¹` too: `T(0, n z)/n ≥ 0`, its mean converges to the almost-sure
     limit, and dominated convergence controls the negative part of `T(0, n z)/n - g(z)`;
* **uniqueness** (`isTimeConstant_unique`), for every law: almost-sure limits are unique, and two
  norms that agree at the lattice points agree everywhere (`ptNorm_ext_of_point`);
* the direction `e₁` (`exists_tendsto_passageTime_div_of_cheapPaths`) and the positivity of the
  time constant there from the cheap-path estimate alone (`timeConstant_pos_of_cheapPaths`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Uniqueness -/

/-- **The time constant is unique**: two norms with the time-constant property for the same law
are equal. -/
theorem isTimeConstant_unique {P : Measure (Config m)} [IsProbabilityMeasure P] {μ μ' : PtNorm m}
    (hμ : IsTimeConstant P μ) (hμ' : IsTimeConstant P μ') : μ = μ' :=
  ptNorm_ext_of_point fun z => by
    obtain ⟨ω, h₁, h₂⟩ := ((hμ z).and (hμ' z)).exists
    exact tendsto_nhds_unique h₁ h₂

/-! ### Linear growth of the mean -/

/-- With an integrable weight, `E T(0, x) ≤ d E τ |x|`. -/
theorem IsIIDWeights.meanTime_le {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} (hP : IsIIDWeights P F) (hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) F)
    (x : Vertex m) :
    meanTime P x ≤ ((m + 1) * ∫ t, (t : ℝ) ∂F) * ‖point x‖ := by
  have hτ : 0 ≤ ∫ t, (t : ℝ) ∂F := integral_nonneg fun t => NNReal.coe_nonneg t
  have h1 := IsIIDWeights.integral_passageTime_le hP hF 0 x
  have h2 := mul_le_mul_of_nonneg_right (l1Dist_zero_le_norm_point x) hτ
  calc meanTime P x ≤ l1Dist 0 x * ∫ t, (t : ℝ) ∂F := h1
    _ ≤ (m + 1) * ‖point x‖ * ∫ t, (t : ℝ) ∂F := h2
    _ = ((m + 1) * ∫ t, (t : ℝ) ∂F) * ‖point x‖ := by ring

/-! ### Convergence in `L¹` -/

/-- **`L¹` convergence from almost-sure convergence and convergence of the means**, for
nonnegative functions with a constant limit: `|f - g| = (f - g) + 2 (g - f)⁺`, and `(g - f)⁺` is
dominated by `g⁺`. -/
theorem tendsto_integral_abs_sub_of_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : ℕ → Ω → ℝ} {g : ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfi : ∀ n, Integrable (f n) P) (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 g))
    (hmean : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 g)) :
    Tendsto (fun n => ∫ ω, |f n ω - g| ∂P) atTop (𝓝 0) := by
  have hpos : ∀ n, Integrable (fun ω => max (g - f n ω) 0) P := fun n =>
    ((integrable_const g).sub (hfi n)).pos_part
  have hid : ∀ n, ∫ ω, |f n ω - g| ∂P =
      (∫ ω, f n ω ∂P - g) + 2 * ∫ ω, max (g - f n ω) 0 ∂P := by
    intro n
    have h1 : Integrable (fun ω => f n ω - g) P := (hfi n).sub (integrable_const g)
    have e : (fun ω => |f n ω - g|) = fun ω => (f n ω - g) + 2 * max (g - f n ω) 0 := by
      funext ω
      rcases le_total (f n ω) g with h | h
      · rw [abs_of_nonpos (by linarith only [h]), max_eq_left (by linarith only [h])]; ring
      · rw [abs_of_nonneg (by linarith only [h]), max_eq_right (by linarith only [h])]; ring
    rw [e, integral_add h1 ((hpos n).const_mul 2),
      integral_sub (hfi n) (integrable_const g), integral_const_mul]
    simp
  have hdom : Tendsto (fun n => ∫ ω, max (g - f n ω) 0 ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun n ω => max (g - f n ω) 0) (f := fun _ => (0 : ℝ)) (fun _ => max g 0)
      (fun n => (hpos n).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (le_max_right _ _)]
        exact max_le_max (by linarith only [hf0 n ω]) le_rfl)
      (by
        filter_upwards [hae] with ω hω
        have := (tendsto_const_nhds (x := g)).sub hω |>.max (tendsto_const_nhds (x := (0 : ℝ)))
        simpa using this)
    simpa using h
  have hsum := (hmean.sub_const g).add (hdom.const_mul 2)
  simp only [sub_self, mul_zero, add_zero] at hsum
  exact hsum.congr fun n => (hid n).symm

/-! ### Existence -/

/-- The lattice point `(n, 0)` is `n` times the first unit vector. -/
theorem nsmul_longitudinal (n : ℕ) : n • ((1, 0) : Vertex m) = ((n : ℤ), 0) :=
  Prod.ext (by simp) (by simp)

/-- The lattice time constant is the restriction of a norm. -/
theorem exists_ptNorm_eq_latticeTimeConstant {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) F) {P : Measure (Config m)}
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hcheap : CheapPaths P a c) :
    ∃ μ : PtNorm m, ∀ z : Vertex m, μ.1 (point z) = latticeTimeConstant P z := by
  have hT := IsIIDWeights.measurePreserving_translate hP
  have hI := IsIIDWeights.integrable_passageTime hP hF
  exact exists_ptNorm_extend ha (latticeTimeConstant_nsmul hT hI) (latticeTimeConstant_add_le hT hI)
    (latticeTimeConstant_neg hT hI) (le_latticeTimeConstant hT hI ha hc hcheap)
    (latticeTimeConstant_le hT hI (IsIIDWeights.meanTime_le hP hF))

/-- **The time constant exists** ([ADH, Theorems 2.1 and 2.5]), from the cheap-path estimate and
the concentration of the passage time: there is a norm `μ` on `ℝ^d` with `T(0, n x)/n → μ(x)`
almost surely and in `L¹` at every lattice point `x`. -/
theorem exists_isTimeConstant_of_cheapPaths {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) F) {P : Measure (Config m)}
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hcheap : CheapPaths P a c) {C₀ c₀ : ℝ} (hc₀ : 0 < c₀)
    (hconc : PassageTimeConcentration P C₀ c₀) :
    ∃ μ : PtNorm m, IsTimeConstant P μ ∧ ∀ x : Vertex m,
      Tendsto (fun n : ℕ => ∫ ω, |(passageTime ω 0 (n • x) : ℝ) / n - μ.1 (point x)| ∂P) atTop
        (𝓝 0) := by
  have hT := IsIIDWeights.measurePreserving_translate hP
  have hI := IsIIDWeights.integrable_passageTime hP hF
  obtain ⟨μ, hμ⟩ := exists_ptNorm_eq_latticeTimeConstant hF hP ha hc hcheap
  have hae : IsTimeConstant P μ := fun x => by
    rw [hμ x]; exact ae_tendsto_passageTime_div hT hI hc₀ hconc x
  refine ⟨μ, hae, fun x => ?_⟩
  refine tendsto_integral_abs_sub_of_tendsto
    (fun n ω => div_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg n))
    (fun n => (hI 0 (n • x)).div_const _) (hae x) ?_
  have h := tendsto_meanTime_div_latticeTimeConstant hT hI x
  rw [← hμ x] at h
  refine h.congr fun n => ?_
  rw [integral_div]
  rfl

/-- **The time constant in the direction `e₁`**: `T(0, n e₁)/n → μ₁ ≥ 0` almost surely and in
`L¹` ([ADH, Theorem 2.1]). -/
theorem exists_tendsto_passageTime_div_of_cheapPaths {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) F) {P : Measure (Config m)}
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hcheap : CheapPaths P a c) {C₀ c₀ : ℝ} (hc₀ : 0 < c₀)
    (hconc : PassageTimeConcentration P C₀ c₀) :
    ∃ μ₁ : ℝ, 0 ≤ μ₁ ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 ((n : ℤ), 0) : ℝ) / n) atTop (𝓝 μ₁)) ∧
      Tendsto (fun n : ℕ => ∫ ω, |(passageTime ω 0 ((n : ℤ), 0) : ℝ) / n - μ₁| ∂P) atTop
        (𝓝 0) := by
  obtain ⟨μ, hμ, hL1⟩ := exists_isTimeConstant_of_cheapPaths hF hP ha hc hcheap hc₀ hconc
  refine ⟨μ.1 (point ((1, 0) : Vertex m)), apply_nonneg _ _, ?_, ?_⟩
  · filter_upwards [hμ ((1, 0) : Vertex m)] with ω hω
    exact hω.congr fun n => by rw [nsmul_longitudinal]
  · exact (hL1 ((1, 0) : Vertex m)).congr fun n => by rw [nsmul_longitudinal]

/-! ### Positivity -/

/-- **The time constant is positive** in the direction `e₁` ([ADH, Theorem 2.5]), from the
cheap-path estimate: `P(T(0, n e₁) < a n) ≤ e^{-cn}` is summable, so by Borel–Cantelli almost
surely `T(0, n e₁) ≥ a n` eventually, and the limit is at least `a`. -/
theorem timeConstant_pos_of_cheapPaths {P : Measure (Config m)} [IsProbabilityMeasure P]
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hcheap : CheapPaths P a c) (μ₁ : ℝ)
    (hμ₁ : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 ((n : ℤ), 0) : ℝ) / n) atTop
      (𝓝 μ₁)) :
    0 < μ₁ := by
  have hfloor : ∀ n : ℕ, ⌊‖point (((n : ℤ), 0) : Vertex m)‖⌋₊ = n := fun n => by
    rw [← nsmul_longitudinal, point_nsmul, norm_smul, norm_point_longitudinal, mul_one,
      Real.norm_natCast, Nat.floor_natCast]
  have hbad : ∀ n : ℕ, P {ω | (passageTime ω 0 (((n : ℤ), 0) : Vertex m) : ℝ) < a * n} ≤
      ENNReal.ofReal (Real.exp (-(c * n))) := fun n => by
    have h := measure_passageTime_lt_le hcheap (((n : ℤ), 0) : Vertex m)
    rwa [hfloor n] at h
  have hsum : Summable fun n : ℕ => Real.exp (-(c * n)) := by
    have := Real.summable_exp_nat_mul_iff.2 (neg_lt_zero.2 hc)
    refine this.congr fun n => ?_
    ring_nf
  have hfin : (∑' n : ℕ, P {ω | (passageTime ω 0 (((n : ℤ), 0) : Vertex m) : ℝ) < a * n}) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbad)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hsum]
    exact ENNReal.ofReal_ne_top
  obtain ⟨ω, hω₁, hω₂⟩ := ((ae_eventually_notMem hfin).and hμ₁).exists
  have hge : ∀ᶠ n : ℕ in atTop,
      a ≤ (passageTime ω 0 (((n : ℤ), 0) : Vertex m) : ℝ) / n := by
    filter_upwards [hω₁, eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    simp only [not_lt] at hn
    rw [le_div_iff₀ hn']
    exact hn
  exact ha.trans_le (ge_of_tendsto hω₂ hge)

end CurvatureVariance.Infra.FPP
