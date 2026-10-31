/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanBasic
public import Mathlib.Analysis.Subadditive
import CurvatureVariance.Infra.FPP.MeanSkeleton
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith

/-!
# The lattice time constant

For a translation-invariant law with integrable passage times, `n ↦ E T(0, n z)` is subadditive,
so by Fekete's lemma `g(z) = lim_n E T(0, n z)/n = inf_{n ≥ 1} E T(0, n z)/n` exists
(`latticeTimeConstant`). We prove:
- `g(n z) = n g(z)`, `g(z + w) ≤ g(z) + g(w)`, `g(-z) = g(z)` and `g(z) ≤ E T(0, z)`;
- the upper bound `g(z) ≤ A |z|` from a linear bound on the mean, and the lower bound
  `g(z) ≥ a |z|` from the cheap-path estimate `CheapPaths P a c`;
- almost sure convergence `T(0, n z)/n → g(z)` from the concentration hypothesis
  `PassageTimeConcentration P C c` (at `u = n^{1/4}` its bound is stretched-exponential in `n`),
  by Borel–Cantelli.

The concentration hypothesis is the predicate `PassageTimeConcentration` of
`CurvatureVariance.Infra.FPP.Hypotheses`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Infra.FPP


variable {m : ℕ} {P : Measure (Config m)}

/-- The lattice time constant `g(z) = lim_n E T(0, n z)/n = inf_{n ≥ 1} E T(0, n z)/n` (Fekete). -/
noncomputable def latticeTimeConstant (P : Measure (Config m)) (z : Vertex m) : ℝ :=
  sInf ((fun n : ℕ => meanTime P (n • z) / n) '' Set.Ici 1)

section Invariant

variable (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
  (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)

include hT hI

theorem subadditive_meanTime (z : Vertex m) : Subadditive fun n : ℕ => meanTime P (n • z) :=
  fun a b => by simpa only [add_nsmul] using meanTime_add_le hT hI (a • z) (b • z)

omit hT hI in
theorem bddBelow_meanTime_div (z : Vertex m) :
    BddBelow (Set.range fun n : ℕ => meanTime P (n • z) / n) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (meanTime_nonneg _) n.cast_nonneg⟩

/-- **Fekete**: `E T(0, n z)/n → g(z)`. -/
theorem tendsto_meanTime_div_latticeTimeConstant (z : Vertex m) :
    Tendsto (fun n : ℕ => meanTime P (n • z) / n) atTop (𝓝 (latticeTimeConstant P z)) := by
  have h := (subadditive_meanTime hT hI z).tendsto_lim (bddBelow_meanTime_div z)
  have e : (subadditive_meanTime hT hI z).lim = latticeTimeConstant P z := by
    unfold Subadditive.lim latticeTimeConstant; rfl
  rwa [e] at h

theorem latticeTimeConstant_nsmul (n : ℕ) (z : Vertex m) :
    latticeTimeConstant P (n • z) = n * latticeTimeConstant P z := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := tendsto_meanTime_div_latticeTimeConstant hT hI (0 • z : Vertex m)
    have h0 : (fun k : ℕ => meanTime P (k • (0 • z : Vertex m)) / k) = fun _ => 0 := by
      funext k; simp
    rw [h0] at h
    simpa using (tendsto_nhds_unique h tendsto_const_nhds)
  · have h1 := tendsto_meanTime_div_latticeTimeConstant hT hI (n • z)
    have h2 := ((tendsto_meanTime_div_latticeTimeConstant hT hI z).const_mul (n : ℝ)).comp
      (tendsto_atTop_mono (fun j : ℕ => Nat.le_mul_of_pos_right j hn) tendsto_id :
        Tendsto (fun j : ℕ => j * n) atTop atTop)
    refine tendsto_nhds_unique h1 (h2.congr fun j => ?_)
    simp only [Function.comp, ← mul_nsmul']
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
      push_cast
      field_simp

theorem latticeTimeConstant_add_le (z w : Vertex m) :
    latticeTimeConstant P (z + w) ≤ latticeTimeConstant P z + latticeTimeConstant P w := by
  refine le_of_tendsto_of_tendsto' (tendsto_meanTime_div_latticeTimeConstant hT hI (z + w))
    ((tendsto_meanTime_div_latticeTimeConstant hT hI z).add
      (tendsto_meanTime_div_latticeTimeConstant hT hI w)) fun n => ?_
  rw [← add_div, smul_add]
  gcongr
  exact meanTime_add_le hT hI _ _

theorem latticeTimeConstant_neg (z : Vertex m) :
    latticeTimeConstant P (-z) = latticeTimeConstant P z := by
  refine tendsto_nhds_unique (tendsto_meanTime_div_latticeTimeConstant hT hI (-z)) ?_
  have := tendsto_meanTime_div_latticeTimeConstant hT hI z
  refine this.congr fun n => ?_
  simp [meanTime_neg hT]

theorem latticeTimeConstant_le {A : ℝ} (hlin : ∀ x, meanTime P x ≤ A * ‖point x‖) (z : Vertex m) :
    latticeTimeConstant P z ≤ A * ‖point z‖ := by
  refine le_of_tendsto (tendsto_meanTime_div_latticeTimeConstant hT hI z)
    (Eventually.of_forall fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using (meanTime_nonneg z).trans (hlin z)
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    refine (hlin _).trans (le_of_eq ?_)
    rw [point_nsmul, norm_smul, Real.norm_natCast]; ring

end Invariant

/-! ### The lower bound from the cheap-path estimate -/

/-- If `T(0, x) < a k` with `k = ⌊|x|⌋`, then some self-avoiding path of length `k` from `0`
costs at most `a k`, so the event has probability at most `e^{-ck}`. -/
theorem measure_passageTime_lt_le {a c : ℝ} (hcheap : CheapPaths P a c) (x : Vertex m) :
    P {ω | (passageTime ω 0 x : ℝ) < a * ⌊‖point x‖⌋₊} ≤
      ENNReal.ofReal (Real.exp (-(c * ⌊‖point x‖⌋₊))) := by
  refine le_trans (measure_mono ?_) (hcheap 0 ⌊‖point x‖⌋₊)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  set k := ⌊‖point x‖⌋₊ with hk
  set ε : ℝ≥0 := Real.toNNReal ((a * k - passageTime ω 0 x) / 2) with hε
  have hεpos : 0 < ε := Real.toNNReal_pos.2 (by linarith only [hω])
  have hεc : (ε : ℝ) = (a * k - passageTime ω 0 x) / 2 :=
    Real.coe_toNNReal _ (by linarith only [hω])
  obtain ⟨p, hp⟩ := exists_walkCost_lt ω 0 x hεpos
  have hp' : (walkCost ω p : ℝ) < a * k := by
    have : (walkCost ω p : ℝ) < (passageTime ω 0 x : ℝ) + ε := by exact_mod_cast hp
    linarith only [this, hεc, hω]
  set q : (latticeGraph m).Walk 0 x := (p.toPath : (latticeGraph m).Walk 0 x) with hq
  have hqp : q.IsPath := p.toPath.2
  have hqc : walkCost ω q ≤ walkCost ω p := walkCost_toPath_le ω p
  have hlen : k ≤ q.length := by
    have h1 := norm_point_sub_le_length q
    rw [point_zero, zero_sub, norm_neg] at h1
    have h2 : (k : ℝ) ≤ ‖point x‖ := Nat.floor_le (norm_nonneg _)
    exact_mod_cast h2.trans h1
  refine ⟨_, q.take k, hqp.take k, by rw [SimpleGraph.Walk.take_length]; omega, ?_⟩
  have hc : walkCost ω (q.take k) ≤ walkCost ω q := by
    have := walkCost_take_add_drop ω q k
    rw [← this]; exact le_self_add
  have : (walkCost ω (q.take k) : ℝ) ≤ walkCost ω p := by exact_mod_cast hc.trans hqc
  linarith only [this, hp']

/-- A single point: `E T(0, x) ≥ a ⌊|x|⌋ (1 - e^{-c⌊|x|⌋})`. -/
theorem le_meanTime_of_cheapPaths [IsProbabilityMeasure P]
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    {a c : ℝ} (ha : 0 ≤ a) (hcheap : CheapPaths P a c) (x : Vertex m) :
    a * ⌊‖point x‖⌋₊ * (1 - Real.exp (-(c * ⌊‖point x‖⌋₊))) ≤ meanTime P x := by
  set k := ⌊‖point x‖⌋₊ with hk
  have hmk : MeasurableSet {ω : Config m | (passageTime ω 0 x : ℝ) < a * k} :=
    measurableSet_lt (measurable_passageTime_real 0 x) measurable_const
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => (passageTime ω 0 x : ℝ))
    (Eventually.of_forall fun ω => NNReal.coe_nonneg _) (hI 0 x) (a * k)
  have h2 : P.real {ω | a * k ≤ (passageTime ω 0 x : ℝ)} ≥ 1 - Real.exp (-(c * k)) := by
    have hc : {ω | a * k ≤ (passageTime ω 0 x : ℝ)} =
        {ω : Config m | (passageTime ω 0 x : ℝ) < a * k}ᶜ := by
      ext ω; simp
    rw [hc, probReal_compl_eq_one_sub hmk]
    have : P.real {ω : Config m | (passageTime ω 0 x : ℝ) < a * k} ≤ Real.exp (-(c * k)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) (measure_passageTime_lt_le hcheap x)
    linarith only [this]
  have hak : 0 ≤ a * k := mul_nonneg ha k.cast_nonneg
  calc a * k * (1 - Real.exp (-(c * k))) ≤ a * k * P.real {ω | a * k ≤ (passageTime ω 0 x : ℝ)} :=
        mul_le_mul_of_nonneg_left h2 hak
    _ ≤ meanTime P x := h1

section Invariant

variable (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
  (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)

include hT hI

theorem le_latticeTimeConstant [IsProbabilityMeasure P] {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hcheap : CheapPaths P a c) (z : Vertex m) :
    a * ‖point z‖ ≤ latticeTimeConstant P z := by
  have hlim := tendsto_meanTime_div_latticeTimeConstant hT hI z
  obtain ⟨s, hs_def⟩ : ∃ s, s = ‖point z‖ := ⟨_, rfl⟩
  rw [← hs_def]
  rcases (hs_def ▸ norm_nonneg (point z) : 0 ≤ s).eq_or_lt with hs | hs
  · rw [← hs, mul_zero]
    exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
      div_nonneg (meanTime_nonneg _) n.cast_nonneg)
  · have hfl : Tendsto (fun n : ℕ => ⌊(n : ℝ) * s⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hs)
    have hk : Tendsto (fun n : ℕ => (⌊(n : ℝ) * s⌋₊ : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hfl
    have hratio : Tendsto (fun n : ℕ => (⌊(n : ℝ) * s⌋₊ : ℝ) / n) atTop (𝓝 s) := by
      have h1 := ((tendsto_nat_floor_div_atTop (R := ℝ)).comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hs)).mul_const s
      rw [one_mul] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [Function.comp]
      field_simp
    have hq : Tendsto (fun n : ℕ => Real.exp (-(c * ⌊(n : ℝ) * s⌋₊))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hk.const_mul_atTop hc)
    have hb : Tendsto (fun n : ℕ => a * ((⌊(n : ℝ) * s⌋₊ : ℝ) / n) *
        (1 - Real.exp (-(c * ⌊(n : ℝ) * s⌋₊)))) atTop (𝓝 (a * s * (1 - 0))) :=
      (hratio.const_mul a).mul (tendsto_const_nhds.sub hq)
    rw [sub_zero, mul_one] at hb
    refine le_of_tendsto_of_tendsto' hb hlim fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h := le_meanTime_of_cheapPaths hI ha.le hcheap (n • z)
      rw [point_nsmul, norm_smul, Real.norm_natCast, ← hs_def] at h
      calc a * ((⌊(n : ℝ) * s⌋₊ : ℝ) / n) * (1 - Real.exp (-(c * ⌊(n : ℝ) * s⌋₊)))
          = a * ⌊(n : ℝ) * s⌋₊ * (1 - Real.exp (-(c * ⌊(n : ℝ) * s⌋₊))) / n := by ring
        _ ≤ meanTime P (n • z) / n := by gcongr

end Invariant

/-! ### Almost sure convergence -/

/-- A nonzero lattice point has positive norm. -/
theorem norm_point_pos {z : Vertex m} (hz : z ≠ 0) : 0 < ‖point z‖ := by
  refine (norm_nonneg _).lt_of_ne fun h => hz ?_
  have h2 := norm_point_sq z
  rw [← h] at h2
  have h1 : (z.1 : ℝ) ^ 2 = 0 := by
    nlinarith only [h2, sq_nonneg (z.1 : ℝ), sq_nonneg ‖transversePoint z.2‖]
  have h3 : ‖transversePoint z.2‖ ^ 2 = 0 := by
    nlinarith only [h2, sq_nonneg (z.1 : ℝ), sq_nonneg ‖transversePoint z.2‖]
  have h4 : transversePoint z.2 = 0 := norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 h3)
  refine Prod.ext ?_ ?_
  · exact_mod_cast pow_eq_zero_iff (two_ne_zero) |>.1 h1
  · funext j
    have := congrFun (congrArg (fun v : EuclideanSpace ℝ (Fin m) => (v : Fin m → ℝ)) h4) j
    simpa using this

/-- Stretched-exponential decay: `exp(-c r^{1/4}) ≤ 8! / (c^8 r^2)`. -/
theorem exp_neg_mul_rpow_le {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    Real.exp (-(c * r ^ (1 / 4 : ℝ))) ≤ (Nat.factorial 8 : ℝ) / (c ^ 8 * r ^ 2) := by
  have hy : 0 ≤ c * r ^ (1 / 4 : ℝ) := by positivity
  have h8 : (c * r ^ (1 / 4 : ℝ)) ^ 8 = c ^ 8 * r ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (r ^ (1 / 4 : ℝ)), ← Real.rpow_mul hr.le]
    norm_num
  have h := Real.pow_div_factorial_le_exp _ hy 8
  rw [h8] at h
  have hpos : 0 < c ^ 8 * r ^ 2 / (Nat.factorial 8 : ℝ) := by positivity
  calc Real.exp (-(c * r ^ (1 / 4 : ℝ))) = (Real.exp (c * r ^ (1 / 4 : ℝ)))⁻¹ := Real.exp_neg _
    _ ≤ (c ^ 8 * r ^ 2 / (Nat.factorial 8 : ℝ))⁻¹ := inv_anti₀ hpos h
    _ = _ := inv_div _ _

/-- The normalised fluctuation bound tends to zero. -/
theorem tendsto_rpow_fluct (s : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt s * (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
  have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop).const_mul (Real.sqrt s)
  rwa [mul_zero] at this

theorem fluct_eq {n s : ℝ} (hn : 0 < n) :
    n ^ (1 / 4 : ℝ) * Real.sqrt (n * s) / n = Real.sqrt s * n ^ (-(1 / 4 : ℝ)) := by
  have e : n ^ (1 / 4 : ℝ) * n ^ (1 / 2 : ℝ) = n ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hn]; norm_num
  have e2 : n ^ (-(1 / 4 : ℝ)) = n ^ (3 / 4 : ℝ) / n := by
    rw [← Real.rpow_sub_one hn.ne']; norm_num
  rw [Real.sqrt_mul hn.le, Real.sqrt_eq_rpow n, e2, ← e]
  field_simp

/-- Borel–Cantelli input: the probability of a large deviation at scale `n` is at most
`K / n^2`. -/
theorem measure_deviation_le [IsProbabilityMeasure P] {C c : ℝ} (hc : 0 < c)
    (hconc : PassageTimeConcentration P C c)
    (z : Vertex m) {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ (n : ℝ) * ‖point z‖) :
    P {ω | (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt ‖point (n • z)‖ <
        |(passageTime ω 0 (n • z) : ℝ) - ∫ ω', (passageTime ω' 0 (n • z) : ℝ) ∂P|} ≤
      ENNReal.ofReal (|C| * (Nat.factorial 8 : ℝ) / c ^ 8 * (1 / (n : ℝ) ^ 2)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : ‖point (n • z)‖ = (n : ℝ) * ‖point z‖ := by
    rw [point_nsmul, norm_smul, Real.norm_natCast]
  refine (hconc (n • z) (by rw [hnorm]; exact h2) _ (by positivity)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  calc C * Real.exp (-(c * (n : ℝ) ^ (1 / 4 : ℝ)))
      ≤ |C| * Real.exp (-(c * (n : ℝ) ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * ((Nat.factorial 8 : ℝ) / (c ^ 8 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (exp_neg_mul_rpow_le hc hnpos) (abs_nonneg C)
    _ = _ := by field_simp

/-- Almost surely, eventually `|T(0, n z) - E T(0, n z)| ≤ n^{1/4} √(n |z|)`. -/
theorem ae_eventually_deviation_le [IsProbabilityMeasure P] {C c : ℝ} (hc : 0 < c)
    (hconc : PassageTimeConcentration P C c)
    {z : Vertex m} (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      |(passageTime ω 0 (n • z) : ℝ) - meanTime P (n • z)| ≤
        (n : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt ((n : ℝ) * ‖point z‖) := by
  have hs : 0 < ‖point z‖ := norm_point_pos hz
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n → 2 ≤ (n : ℝ) * ‖point z‖ := by
    refine ⟨⌈2 / ‖point z‖⌉₊ + 1, by omega, fun n hn => ?_⟩
    have h1 : 2 / ‖point z‖ ≤ (n : ℝ) := by
      have : (⌈2 / ‖point z‖⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈2 / ‖point z‖⌉₊ ≤ n)
      exact (Nat.le_ceil _).trans this
    rwa [div_le_iff₀ hs] at h1
  have hgs : Summable fun k : ℕ =>
      |C| * (Nat.factorial 8 : ℝ) / c ^ 8 * (1 / ((k + N0 : ℕ) : ℝ) ^ 2) :=
    (((summable_nat_add_iff N0).2 (Real.summable_one_div_nat_pow.2 one_lt_two))).mul_left _
  have hg0 : ∀ k : ℕ, 0 ≤ |C| * (Nat.factorial 8 : ℝ) / c ^ 8 * (1 / ((k + N0 : ℕ) : ℝ) ^ 2) :=
    fun k => by positivity
  have hsum : ∑' k : ℕ, P {ω | ((k + N0 : ℕ) : ℝ) ^ (1 / 4 : ℝ) *
      Real.sqrt ‖point ((k + N0 : ℕ) • z)‖ <
        |(passageTime ω 0 ((k + N0 : ℕ) • z) : ℝ) -
          ∫ ω', (passageTime ω' 0 ((k + N0 : ℕ) • z) : ℝ) ∂P|} ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k =>
      measure_deviation_le hc hconc z (n := k + N0) (by omega) (hN0.2 _ (by omega)))
    rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hgs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨K0, hK⟩ := eventually_atTop.1 hω
  filter_upwards [eventually_ge_atTop (K0 + N0)] with n hn
  have := hK (n - N0) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at this
  simp only [not_lt, point_nsmul, norm_smul, Real.norm_natCast] at this
  exact this

section Invariant

variable (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
  (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)

include hT hI

/-- **Almost sure convergence** of `T(0, n z)/n` to the lattice time constant, from the
concentration hypothesis `PassageTimeConcentration P C c`, by Borel–Cantelli. -/
theorem ae_tendsto_passageTime_div [IsProbabilityMeasure P] {C c : ℝ} (hc : 0 < c)
    (hconc : PassageTimeConcentration P C c)
    (z : Vertex m) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (passageTime ω 0 (n • z) : ℝ) / n) atTop
      (𝓝 (latticeTimeConstant P z)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : latticeTimeConstant P (0 : Vertex m) = 0 := by
      simpa using latticeTimeConstant_nsmul hT hI 0 (0 : Vertex m)
    refine Eventually.of_forall fun ω => ?_
    rw [h0]
    simp
  have hmean := tendsto_meanTime_div_latticeTimeConstant hT hI z
  filter_upwards [ae_eventually_deviation_le hc hconc hz] with ω hω
  have hev : ∀ᶠ n : ℕ in atTop,
      dist ((passageTime ω 0 (n • z) : ℝ) / n) (latticeTimeConstant P z) ≤
      Real.sqrt ‖point z‖ * (n : ℝ) ^ (-(1 / 4 : ℝ)) +
        dist (meanTime P (n • z) / n) (latticeTimeConstant P z) := by
    filter_upwards [hω, eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 : dist ((passageTime ω 0 (n • z) : ℝ) / n) (meanTime P (n • z) / n) ≤
        Real.sqrt ‖point z‖ * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hnpos, ← fluct_eq hnpos]
      exact div_le_div_of_nonneg_right hn hnpos.le
    exact (dist_triangle _ (meanTime P (n • z) / n) _).trans (by linarith only [h1])
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun n => dist_nonneg)
    hev ?_)
  have := (tendsto_rpow_fluct ‖point z‖).add (tendsto_iff_dist_tendsto_zero.1 hmean)
  rwa [add_zero] at this

end Invariant

end CurvatureVariance.Infra.FPP
