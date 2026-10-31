/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Audit.LatticeVariance.SolutionDefs
public import CurvatureVariance.Statements.Main.LintegralExpPassageTimeLe
public import CurvatureVariance.Statements.Main.EvariancePassageTimeFloorVertexLeUniform
public import CurvatureVariance.Statements.Companions.ExistsIsTimeConstant
public import CurvatureVariance.Statements.Companions.IsIIDWeightsUnique
public import CurvatureVariance.Statements.Inputs.IntegralPassageTimeLeTimeConstantAdd
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Probability.Independence.InfinitePi

/-!
# Solution: an exponential-moment bound for lattice first-passage percolation

The theorems of the lattice challenge, proved from the library. The definitions are a verbatim
copy of the challenge's, in the module `SolutionDefs`. They coincide by definition with the
library's (`CurvatureVariance.passageTime`, `CurvatureVariance.AssumptionW`, ...), so the library's
theorems apply to them directly.

The product law `weightLaw m F` has independent weights with law `F` (Mathlib's `infinitePi`). The
library's time constant is a norm `μ` with `T(0, n x) / n → μ(x)` almost surely
(`CurvatureVariance.exists_isTimeConstant`). Alexander's bound [ADH, Theorem 3.33]
`μ(x) ≤ E T(0, x) ≤ μ(x) + C (|x| log |x|)^{1/2}`
(`CurvatureVariance.integral_passageTime_le_timeConstant_add`) and the comparison of `μ` with the
Euclidean norm give `E T(0, ⌊n x⌋) / n → μ(x)`, so `timeConstant m F = μ`. With this, the
exponential-moment bound and the variance bound are the library's theorems
`CurvatureVariance.lintegral_exp_passageTime_le` and
`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`, for the law `weightLaw m F` and
the norm `μ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace LatticeVariance

namespace Bridge

/-- A seminorm on `ℝ^d` is bounded by a multiple of the Euclidean norm. -/
theorem exists_seminorm_le {m : ℕ} (μ : Seminorm ℝ (Pt m)) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Pt m, μ x ≤ K * ‖x‖ := by
  let b := Module.finBasis ℝ (Pt m)
  let C : Fin (Module.finrank ℝ (Pt m)) → ℝ := fun i =>
    ‖LinearMap.toContinuousLinearMap (b.coord i)‖
  refine ⟨∑ i, C i * μ (b i) + 1, ?_, fun x => ?_⟩
  · have : 0 ≤ ∑ i, C i * μ (b i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg μ _)
    linarith only [this]
  · have hx : μ x ≤ ∑ i, |b.repr x i| * μ (b i) := by
      conv_lhs => rw [← b.sum_repr x]
      refine (Finset.le_sum_of_subadditive μ (map_zero μ).le (map_add_le_add μ) _ _).trans
        (Finset.sum_le_sum fun i _ => ?_)
      rw [map_smul_eq_mul, Real.norm_eq_abs]
    have hc : ∀ i, |b.repr x i| ≤ C i * ‖x‖ := fun i => by
      have := (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm x
      simpa [C] using this
    calc μ x ≤ ∑ i, |b.repr x i| * μ (b i) := hx
      _ ≤ ∑ i, (C i * ‖x‖) * μ (b i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (apply_nonneg μ _)
      _ = (∑ i, C i * μ (b i)) * ‖x‖ := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (∑ i, C i * μ (b i) + 1) * ‖x‖ := by
          nlinarith only [norm_nonneg x]

/-- The vertex `⌊y⌋` is within `m + 1` of `y`. -/
theorem norm_point_floorVertex_sub_le {m : ℕ} (y : Pt m) :
    ‖point (floorVertex y) - y‖ ≤ (m : ℝ) + 1 := by
  set w : Pt m := point (floorVertex y) - y with hw
  have h1 : |w.fst| ≤ 1 := by
    have : w.fst = (⌊y.fst⌋ : ℝ) - y.fst := by simp [hw, point, floorVertex]
    rw [this, abs_le]
    constructor <;> linarith only [Int.floor_le y.fst, Int.lt_floor_add_one y.fst]
  have h2 : ‖w.snd‖ ^ 2 ≤ m := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ j, ‖w.snd j‖ ^ 2 ≤ ∑ _j : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have : w.snd j = (⌊y.snd j⌋ : ℝ) - y.snd j := by simp [hw, point, floorVertex]
          rw [this, Real.norm_eq_abs, sq_abs, sq_le_one_iff_abs_le_one, abs_le]
          constructor <;> linarith only [Int.floor_le (y.snd j), Int.lt_floor_add_one (y.snd j)]
      _ = m := by simp
  have h3 : ‖w‖ ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    have : w.fst ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith only [this, h2, hm]
  exact le_of_sq_le_sq h3 (by positivity)

/-- `T(u, u) = 0`: the empty walk costs nothing. -/
theorem passageTime_self {m : ℕ} (ω : Config m) (u : Vertex m) : passageTime ω u u = 0 :=
  nonpos_iff_eq_zero.mp (ciInf_le (OrderBot.bddBelow _) SimpleGraph.Walk.nil)

/-- `√(r log r) / n → 0` when `1 ≤ r_n ≤ A n`. -/
theorem tendsto_sqrt_mul_log_div {A : ℝ} (hA : 0 < A) {r : ℕ → ℝ}
    (hr : ∀ᶠ n in atTop, 1 ≤ r n ∧ r n ≤ n * A) :
    Tendsto (fun n : ℕ => √(r n * Real.log (r n)) / n) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => √(2 * A * √A) / √(√(n : ℝ))) atTop (𝓝 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    exact Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hg
  filter_upwards [hr, eventually_ge_atTop 1] with n ⟨hr1, hrA⟩ hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn']
  -- `log r ≤ 2 √r`
  have hlog : Real.log (r n) ≤ 2 * √(r n) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith only [hr1] : 0 < r n))
    rw [Real.log_sqrt (by linarith only [hr1])] at h
    linarith only [h]
  have hlog0 : 0 ≤ Real.log (r n) := Real.log_nonneg hr1
  have hsr : √(r n) ≤ √(n * A) := Real.sqrt_le_sqrt hrA
  have hsn : √((n : ℝ) * A) = √(n : ℝ) * √A := Real.sqrt_mul hn0.le A
  have hsn0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsnn : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hssn : 0 < √(√(n : ℝ)) := Real.sqrt_pos.mpr hsn0
  -- `r log r ≤ 2 A √A n √n`
  have hprod : r n * Real.log (r n) ≤ 2 * A * √A * (n * √(n : ℝ)) := by
    have h1 : r n * Real.log (r n) ≤ r n * (2 * √(r n)) :=
      mul_le_mul_of_nonneg_left hlog (by linarith only [hr1])
    have h2 : r n * (2 * √(r n)) ≤ (n * A) * (2 * (√(n : ℝ) * √A)) := by
      rw [← hsn]
      exact mul_le_mul hrA (by linarith only [hsr]) (by positivity) (by positivity)
    linarith only [h1, h2]
  rw [div_le_div_iff₀ hn0 hssn]
  -- compare squares
  have hlhs : 0 ≤ √(r n * Real.log (r n)) * √(√(n : ℝ)) := by positivity
  have hrhs : 0 ≤ √(2 * A * √A) * n := by positivity
  refine (pow_le_pow_iff_left₀ hlhs hrhs two_ne_zero).mp ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  calc r n * Real.log (r n) * √(n : ℝ) ≤ 2 * A * √A * (n * √(n : ℝ)) * √(n : ℝ) :=
        mul_le_mul_of_nonneg_right hprod hsn0.le
    _ = 2 * A * √A * (n : ℝ) ^ 2 := by
        rw [mul_assoc (2 * A * √A), mul_assoc (n : ℝ), hsnn]; ring

/-- The product law of the weights is a probability measure. -/
theorem isProbabilityMeasure_weightLaw (m : ℕ) (F : Measure ℝ≥0) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (weightLaw m F) := by
  unfold weightLaw; infer_instance

end Bridge

/-- Under `weightLaw m F` the weights are independent, each with law `F`. -/
theorem weightLaw_iid (m : ℕ) (F : Measure ℝ≥0) [IsProbabilityMeasure F] :
    iIndepFun (fun (e : Edge m) (ω : Config m) => ω e) (weightLaw m F) ∧
      ∀ e : Edge m, HasLaw (fun ω : Config m => ω e) F (weightLaw m F) := by
  refine ⟨?_, fun e => ?_⟩
  · exact iIndepFun_infinitePi (P := fun _ : Edge m => F) (X := fun _ => id)
      (fun _ => measurable_id)
  · exact (measurePreserving_eval_infinitePi (fun _ : Edge m => F) e).hasLaw

namespace Bridge

/-- The product law satisfies the library's `IsIIDWeights`. -/
theorem isIIDWeights (m : ℕ) (F : Measure ℝ≥0) [IsProbabilityMeasure F] :
    CurvatureVariance.IsIIDWeights (m := m) (weightLaw m F) F :=
  weightLaw_iid m F

/-- Under (W), the time constant of the library is the limit of `E T(0, ⌊n x⌋) / n`. -/
theorem tendsto_of_isTimeConstant {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) (μ : CurvatureVariance.PtNorm m)
    (hμ : CurvatureVariance.IsTimeConstant (m := m) (weightLaw m F) μ) (x : Pt m) :
    Tendsto (fun n : ℕ =>
        (∫ ω, (passageTime ω 0 (floorVertex ((n : ℝ) • x)) : ℝ) ∂weightLaw m F) / n)
      atTop (𝓝 (μ.1 x)) := by
  obtain ⟨C, hC, hAlex⟩ := CurvatureVariance.integral_passageTime_le_timeConstant_add hm F hW
  have hA := @hAlex (weightLaw m F) (isProbabilityMeasure_weightLaw m F) (isIIDWeights m F) μ hμ
  obtain ⟨K, hK, hle⟩ := exists_seminorm_le μ.1
  by_cases hx : x = 0
  · subst hx
    have h0 : ∀ n : ℕ, floorVertex ((n : ℝ) • (0 : Pt m)) = 0 := fun n => by
      simp [floorVertex]; rfl
    simp only [h0, passageTime_self, NNReal.coe_zero, integral_zero, zero_div, map_zero]
    exact tendsto_const_nhds
  set D : ℝ := (m : ℝ) + 1 with hD
  have hD0 : 0 < D := by positivity
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set p : ℕ → Pt m := fun n => point (floorVertex ((n : ℝ) • x)) with hp
  have hpn : ∀ n : ℕ, ‖p n - (n : ℝ) • x‖ ≤ D := fun n => norm_point_floorVertex_sub_le _
  have hnorm : ∀ n : ℕ, ‖(n : ℝ) • x‖ = n * ‖x‖ := fun n => by
    rw [norm_smul, Real.norm_natCast]
  -- `|μ(p n) - n μ(x)| ≤ K D`
  have hμp : ∀ n : ℕ, |μ.1 (p n) - n * μ.1 x| ≤ K * D := fun n => by
    have h := abs_sub_map_le_sub μ.1 (p n) ((n : ℝ) • x)
    rw [map_smul_eq_mul, Real.norm_natCast] at h
    exact h.trans ((hle _).trans (mul_le_mul_of_nonneg_left (hpn n) hK.le))
  -- `r n = ‖p n‖` grows linearly
  have hr_le : ∀ n : ℕ, 1 ≤ n → ‖p n‖ ≤ n * (‖x‖ + D) := fun n hn => by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := norm_le_norm_add_norm_sub' (p n) ((n : ℝ) • x)
    rw [hnorm] at this
    nlinarith only [this, hpn n, hn', hD0]
  have hr_ge : ∀ n : ℕ, n * ‖x‖ - D ≤ ‖p n‖ := fun n => by
    have := norm_sub_norm_le ((n : ℝ) • x) (p n)
    rw [hnorm, norm_sub_rev] at this
    linarith only [this, hpn n]
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 1 < ‖p n‖ := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 + D) / ‖x‖)
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    refine ⟨le_of_max_le_right hn, ?_⟩
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
    have : 1 + D < n * ‖x‖ := by
      rw [div_lt_iff₀ hx0] at hN; nlinarith only [hN, hNn, hx0]
    linarith only [this, hr_ge n]
  -- the error term
  have herr : Tendsto (fun n : ℕ => (K * D + C * √(‖p n‖ * Real.log ‖p n‖)) / n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => K * D / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 := (tendsto_sqrt_mul_log_div (A := ‖x‖ + D) (by positivity) (r := fun n => ‖p n‖)
      (hev.mono fun n hn => ⟨hn.2.le, hr_le n hn.1⟩)).const_mul C
    rw [mul_zero] at h2
    have := h1.add h2
    rw [add_zero] at this
    exact this.congr fun n => by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ herr
  filter_upwards [hev] with n ⟨hn1, hpn1⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨hlo, hhi⟩ := hA (floorVertex ((n : ℝ) • x)) hpn1
  have habs := abs_le.mp (hμp n)
  set a : ℝ := ∫ ω, (passageTime ω 0 (floorVertex ((n : ℝ) • x)) : ℝ) ∂weightLaw m F with ha
  have hlo' : μ.1 (p n) ≤ a := hlo
  have hhi' : a ≤ μ.1 (p n) + C * √(‖p n‖ * Real.log ‖p n‖) := hhi
  have hs : 0 ≤ C * √(‖p n‖ * Real.log ‖p n‖) := by positivity
  have heq : a / n - μ.1 x = (a - n * μ.1 x) / n := by field_simp
  rw [heq, Real.norm_eq_abs, abs_div, abs_of_pos hn0]
  refine div_le_div_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) hn0.le
  · linarith only [hlo', habs.1, hs]
  · linarith only [hhi', habs.2]

/-- Under (W), `timeConstant m F` is the library's time constant. -/
theorem exists_ptNorm {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) :
    ∃ μ : CurvatureVariance.PtNorm m,
      CurvatureVariance.IsTimeConstant (m := m) (weightLaw m F) μ ∧ timeConstant m F = ⇑μ.1 := by
  obtain ⟨μ, hμ⟩ := @CurvatureVariance.exists_isTimeConstant m hm F _ hW (weightLaw m F)
    (isProbabilityMeasure_weightLaw m F) (isIIDWeights m F)
  exact ⟨μ, hμ, funext fun x => (tendsto_of_isTimeConstant hm F hW μ hμ x).limUnder_eq⟩

end Bridge

/-- The exponential-moment bound (Theorem `thm:main`), from the library. -/
theorem lintegral_exp_passageTime_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 →
      AssumptionCWith (timeConstant m F) ξ δ r M c → ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) (weightLaw m F) ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - timeConstant m F (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂weightLaw m F ≤ 2 := by
  obtain ⟨μ, hμ, heq⟩ := Bridge.exists_ptNorm hm F hW
  rw [heq]
  exact @CurvatureVariance.lintegral_exp_passageTime_le m hm F _ hW
    (weightLaw m F) (Bridge.isProbabilityMeasure_weightLaw m F) (Bridge.isIIDWeights m F) μ hμ
    δ r M c hδ hδ₁ hr hM hc

/-- The variance bound along the ray, a consequence of Theorem `thm:main`, from the library. -/
theorem variance_passageTime_floorVertex_le_uniform {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ ξ : Pt m, ‖ξ‖ = 1 →
      AssumptionCWith (timeConstant m F) ξ δ r M c → ∀ n : ℕ, n₀ ≤ n →
        evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) (weightLaw m F) ≤
          ENNReal.ofReal ((n : ℝ) ^ (1 - ε)) := by
  obtain ⟨μ, hμ, heq⟩ := Bridge.exists_ptNorm hm F hW
  rw [heq]
  exact @CurvatureVariance.evariance_passageTime_floorVertex_le_uniform m hm F _ hW
    (weightLaw m F) (Bridge.isProbabilityMeasure_weightLaw m F) (Bridge.isIIDWeights m F) μ hμ
    δ r M c hδ hδ₁ hr hM hc

/-- `weightLaw m F` is the only law of the configuration under which the weights are independent,
each with law `F`. -/
theorem eq_weightLaw {m : ℕ} {F : Measure ℝ≥0} {P : Measure (Config m)}
    (hind : iIndepFun (fun (e : Edge m) (ω : Config m) => ω e) P)
    (hlaw : ∀ e : Edge m, HasLaw (fun ω : Config m => ω e) F P) :
    P = weightLaw m F := by
  have := hind.isProbabilityMeasure
  have hadj : (latticeGraph m).Adj 0 (1, 0) := by
    rw [latticeGraph, SimpleGraph.fromRel_adj]
    refine ⟨fun h => ?_, Or.inl (Or.inl (by simp))⟩
    have := congrArg Prod.fst h
    simp at this
  have hF : IsProbabilityMeasure F := by
    rw [← (hlaw ⟨_, (latticeGraph m).mem_edgeSet.mpr hadj⟩).map_eq]
    exact (Measure.isProbabilityMeasure_map_iff (hlaw _).aemeasurable).mpr inferInstance
  exact CurvatureVariance.IsIIDWeights.unique (m := m) ⟨hind, hlaw⟩ (Bridge.isIIDWeights m F)

/-- Under (W), the limit defining `timeConstant m F x` exists. -/
theorem tendsto_integral_passageTime_div {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (x : Pt m) :
    Tendsto (fun n : ℕ =>
        (∫ ω, (passageTime ω 0 (floorVertex ((n : ℝ) • x)) : ℝ) ∂weightLaw m F) / n)
      atTop (𝓝 (timeConstant m F x)) := by
  obtain ⟨μ, hμ, heq⟩ := Bridge.exists_ptNorm hm F hW
  rw [heq]
  exact Bridge.tendsto_of_isTimeConstant hm F hW μ hμ x

/-- Under (W), the time constant is a norm on `ℝ^d`: a seminorm that vanishes only at `0`. -/
theorem timeConstant_isNorm {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (hW : AssumptionW m F) :
    ∃ μ : Seminorm ℝ (Pt m), ⇑μ = timeConstant m F ∧ ∀ x, μ x = 0 → x = 0 := by
  obtain ⟨μ, -, heq⟩ := Bridge.exists_ptNorm hm F hW
  exact ⟨μ.1, heq.symm, μ.2⟩

/-- Under (W), the time constant is the paper's: for every `x ∈ ℤ^d`, almost surely
`T(0, n x) / n → μ(x)` as `n → ∞`. -/
theorem ae_tendsto_passageTime_div {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (x : Vertex m) :
    ∀ᵐ ω ∂weightLaw m F,
      Tendsto (fun n : ℕ => (passageTime ω 0 (n • x) : ℝ) / n) atTop
        (𝓝 (timeConstant m F (point x))) := by
  obtain ⟨μ, hμ, heq⟩ := Bridge.exists_ptNorm hm F hW
  rw [heq]
  exact hμ x

end LatticeVariance
