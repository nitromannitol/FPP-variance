/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Arrays.SquareCount
public import CurvatureVariance.Infra.Arrays.SquareOrder
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import CurvatureVariance.Infra.Arrays.Estimates
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# [AB26, Lemma 2.4] by the `L²` counting of its proof

The proof of [AB26, Lemma 2.4], step by step, for `d = m + 1`. All suprema are taken in
`ℝ≥0∞`, so the maxima `V_r` and `Y_a` of that proof need no a priori finiteness.

* `maxSum Z r`: `V_r`, the maximum of `∑_i Z_i(k_{i-1}, k_i)` over the sequences with
  `∑_i |k_i - k_{i-1}|² ≤ 2^r M`.
* `maxLargest Z r a`: `Y_a`, the maximum over these sequences of the `a`-th largest of the entries,
  and `maxSum_le_sum_maxLargest`: `V_r ≤ ∑_a Y_a`.
* `measure_lt_maxLargest_le`: the union bound over the sets of triples, from independence of the
  arrays and Markov's inequality for the `4d`-th moments (`measure_iInter_lt_le`).
* `lintegral_maxLargest_sq_le`: `E[Y_a²]^{1/2} ≤ C 2^{r/4} (M/a)^{1/2}`.
* `lintegral_maxSum_sq_le`: `E[V_r²]^{1/2} ≤ C M 2^{r/4}`.
* `ofReal_sub_le_maxSum`: the supremum is at most `V_0 + ∑_{r ≥ 1} (V_r - 2^{r-1} M)₊`.
* `lintegral_iSup_penalizedSum_le_of_square`: the lemma.

The count of the sets of triples is `choose_mul_pairCount_le`, in
`CurvatureVariance.Infra.Arrays.SquareCount`.

The same proof as `IsotropicVariance.Infra.Arrays.Square` in the continuum library. It lives
beside the tail route of `MomentBound`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CurvatureVariance.Infra.Arrays

variable {Ω : Type*} {m M : ℕ}

/-- Markov's inequality for a moment at most one. -/
theorem measure_gt_le_inv_pow [MeasurableSpace Ω] (P : Measure Ω) {Y : Ω → ℝ} (hY : Measurable Y)
    (hpos : ∀ ω, 0 ≤ Y ω) (p : ℕ) (hint : Integrable (fun ω => Y ω ^ p) P)
    (hmom : ∫ ω, Y ω ^ p ∂P ≤ 1) {x : ℝ} (hx : 0 < x) :
    P {ω | x < Y ω} ≤ ENNReal.ofReal ((x ^ p)⁻¹) := by
  have hpow : 0 < x ^ p := by positivity
  have hmark := meas_ge_le_lintegral_div (μ := P)
    ((ENNReal.measurable_ofReal.comp (hY.pow_const p)).aemeasurable)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hpow)) ENNReal.ofReal_ne_top
  have hinc : {ω | x < Y ω} ⊆ {ω | ENNReal.ofReal (x ^ p) ≤ ENNReal.ofReal (Y ω ^ p)} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hx.le (le_of_lt hω) p)
  have hi : (∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂P) ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
      (fun ω => pow_nonneg (hpos ω) p))]
    exact (ENNReal.ofReal_le_ofReal hmom).trans_eq ENNReal.ofReal_one
  calc P {ω | x < Y ω} ≤ _ := measure_mono hinc
    _ ≤ 1 / ENNReal.ofReal (x ^ p) := hmark.trans (ENNReal.div_le_div_right hi _)
    _ = ENNReal.ofReal ((x ^ p)⁻¹) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos hpow]

/-- The entry `Z_i(k_{i-1}, k_i)` of the sequence `k`, in `ℝ≥0∞`. -/
noncomputable def seqEntry (Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ)
    (k : Fin M → Fin m → ℤ) (ω : Ω) (i : Fin M) : ℝ≥0∞ :=
  ENNReal.ofReal (Z i ω (pathPt 0 k i) (k i))

/-- `V_r` of [AB26, Lemma 2.4]: the supremum of `∑_i Z_i(k_{i-1}, k_i)` over the sequences with
`∑_i |k_i - k_{i-1}|² ≤ 2^r M`. -/
noncomputable def maxSum (Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ) (r : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (k : Fin M → Fin m → ℤ) (_ : energy 0 k ≤ 2 ^ r * M), ∑ i, seqEntry Z k ω i

/-- `Y_a` of [AB26, Lemma 2.4]: the supremum over the same sequences of the `a`-th largest of
the entries `Z_i(k_{i-1}, k_i)`. -/
noncomputable def maxLargest (Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ) (r a : ℕ) (ω : Ω) :
    ℝ≥0∞ :=
  ⨆ (k : Fin M → Fin m → ℤ) (_ : energy 0 k ≤ 2 ^ r * M), aLargest (seqEntry Z k ω) a

/-- The energy of the sequence through `0` and `k`, written as in the statement of the lemma. -/
lemma energy_eq_sum_sq (k : Fin M → Fin m → ℤ) :
    energy 0 k = ∑ i : Fin M, ∑ j : Fin m, ((k i j : ℝ) - (pathPt 0 k i j : ℝ)) ^ 2 := by
  simp [energy, sqNorm, Int.cast_sum, Int.cast_pow, Int.cast_sub, pathPt_succ]

/-- `V_r ≤ ∑_a Y_a` ([AB26, Lemma 2.4]). -/
theorem maxSum_le_sum_maxLargest (Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ) (r : ℕ) (ω : Ω) :
    maxSum Z r ω ≤ ∑ a ∈ Finset.Icc 1 M, maxLargest Z r a ω := by
  refine iSup₂_le fun k hk => ?_
  have h := sum_le_sum_aLargest (seqEntry Z k ω) (Finset.univ : Finset (Fin M))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (Finset.sum_le_sum fun a _ => le_iSup₂_of_le k hk le_rfl)

/-- The total length of the pairs of a sequence with `∑_i |k_i - k_{i-1}|² ≤ 2^r M` is at most
`m^{1/2} 2^{r/2} M` ([AB26, Lemma 2.4]). -/
theorem pairLength_le_of_energy_le (k : Fin M → Fin m → ℤ) {r : ℕ} (hk : energy 0 k ≤ 2 ^ r * M)
    {a : ℕ} {e : Fin a → Fin M} (he : StrictMono e) :
    pairLength a 0 (pairList (pathPt 0 k) e) ≤ Real.sqrt m * 2 ^ ((r : ℝ) / 2) * M := by
  have h1 := pairLength_pairList_le (pathPt 0 k) a 0 e he fun _ => Nat.zero_le _
  rw [pathPt_zero] at h1
  have h2 := sq_sum_l1Length_le (pathPt 0 k) M
  rw [← Finset.range_eq_Ico, ← energy_eq_sum_range] at h2
  set w : ℝ := (2 : ℝ) ^ ((r : ℝ) / 2) with hw
  have hw0 : 0 < w := by positivity
  have hw2 : w ^ 2 = 2 ^ r := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (r : ℝ) / 2 * ((2 : ℕ) : ℝ) = r := by push_cast; ring
    rw [this, Real.rpow_natCast]
  have hS0 : 0 ≤ ∑ j ∈ Finset.Ico 0 M, l1Length (pathPt 0 k (j + 1) - pathPt 0 k j) :=
    Finset.sum_nonneg fun _ _ => l1Length_nonneg _
  have h3 : (∑ j ∈ Finset.Ico 0 M, l1Length (pathPt 0 k (j + 1) - pathPt 0 k j)) ^ 2 ≤
      (Real.sqrt m * w * M) ^ 2 := by
    rw [← Finset.range_eq_Ico]
    rw [← Finset.range_eq_Ico] at hS0
    calc _ ≤ (m : ℝ) * M * energy 0 k := h2
      _ ≤ (m : ℝ) * M * (2 ^ r * M) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = (Real.sqrt m * w * M) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), hw2]
          ring
  exact h1.trans ((pow_le_pow_iff_left₀ hS0 (by positivity) two_ne_zero).1 h3)

section Measurable

variable [MeasurableSpace Ω] {Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ}

lemma measurable_seqEntry (hmeas : ∀ i j k, Measurable (fun ω => Z i ω j k))
    (k : Fin M → Fin m → ℤ) (i : Fin M) : Measurable fun ω => seqEntry Z k ω i :=
  (hmeas i _ _).ennreal_ofReal

lemma measurable_maxSum (hmeas : ∀ i j k, Measurable (fun ω => Z i ω j k)) (r : ℕ) :
    Measurable (maxSum Z r) :=
  Measurable.iSup fun k => Measurable.iSup fun _ =>
    Finset.measurable_fun_sum _ fun i _ => measurable_seqEntry hmeas k i

lemma measurable_maxLargest (hmeas : ∀ i j k, Measurable (fun ω => Z i ω j k)) (r a : ℕ) :
    Measurable (maxLargest Z r a) :=
  Measurable.iSup fun k => Measurable.iSup fun _ => Measurable.iSup fun _ =>
    Measurable.iSup fun _ => Measurable.iInf fun i => Measurable.iInf fun _ =>
      measurable_seqEntry hmeas k i

end Measurable

section Union

variable [MeasurableSpace Ω] {P : Measure Ω} {Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ}
  (hmeas : ∀ i j k, Measurable (fun ω => Z i ω j k))
  (hnonneg : ∀ i ω j k, 0 ≤ Z i ω j k)
  (hind : iIndepFun Z P)
  (hint : ∀ i j k, Integrable (fun ω => Z i ω j k ^ (4 * (m + 1))) P)
  (hmom : ∀ i j k, ∫ ω, Z i ω j k ^ (4 * (m + 1)) ∂P ≤ 1)

include hmeas hnonneg hind hint hmom

/-- [AB26, Lemma 2.4]: the `a` entries of a set of triples lie in independent arrays, so, by
Markov's inequality for their `4d`-th moments, they all exceed `x` with probability at most
`x^{-4da}`. -/
theorem measure_iInter_lt_le {a : ℕ} {e : Fin a → Fin M} (he : Function.Injective e)
    (L : Fin a → IdxPair m) {x : ℝ} (hx : 0 < x) :
    P (⋂ h : Fin a, {ω | x < Z (e h) ω (L h).1 (L h).2}) ≤
      ENNReal.ofReal ((x ^ (4 * (m + 1)))⁻¹) ^ a := by
  have hm : ∀ h, MeasurableSet {f : (Fin m → ℤ) → (Fin m → ℤ) → ℝ | x < f (L h).1 (L h).2} :=
    fun h => measurableSet_lt measurable_const
      ((measurable_pi_apply _).comp (measurable_pi_apply _))
  have hprod := (hind.precomp he).meas_iInter (μ := P)
    (s := fun h => {ω | x < Z (e h) ω (L h).1 (L h).2}) fun h => ⟨_, hm h, rfl⟩
  rw [hprod]
  calc ∏ h : Fin a, P {ω | x < Z (e h) ω (L h).1 (L h).2}
      ≤ ∏ _h : Fin a, ENNReal.ofReal ((x ^ (4 * (m + 1)))⁻¹) :=
        Finset.prod_le_prod fun h _ => measure_gt_le_inv_pow P (hmeas _ _ _)
          (fun ω => hnonneg _ ω _ _) _ (hint _ _ _) (hmom _ _ _) hx
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The union bound over the sets of triples ([AB26, Lemma 2.4]). A set of `a` triples of a
sequence with `∑_i |k_i - k_{i-1}|² ≤ 2^r M` is given by a set of `a` indices and a list of pairs
of total length at most `m^{1/2} 2^{r/2} M`. -/
theorem measure_lt_maxLargest_le {a : ℕ} (r : ℕ) {x : ℝ} (hx : 0 < x) :
    P {ω | ENNReal.ofReal x < maxLargest Z r a ω} ≤
      (M.choose a : ℝ≥0∞) * pairCount m a (Real.sqrt m * 2 ^ ((r : ℝ) / 2) * M) *
        ENNReal.ofReal ((x ^ (4 * (m + 1)))⁻¹) ^ a := by
  classical
  set R : ℝ := Real.sqrt m * 2 ^ ((r : ℝ) / 2) * M with hR
  set q : ℝ≥0∞ := ENNReal.ofReal ((x ^ (4 * (m + 1)))⁻¹) ^ a with hq
  let e : {S : Finset (Fin M) // S.card = a} → Fin a → Fin M := fun S => S.1.orderEmbOfFin S.2
  let A : {S : Finset (Fin M) // S.card = a} → (Fin a → IdxPair m) → Set Ω :=
    fun S L => ⋂ h : Fin a, {ω | x < Z (e S h) ω (L h).1 (L h).2}
  have hsub : {ω | ENNReal.ofReal x < maxLargest Z r a ω} ⊆
      ⋃ (S) (L) (_ : pairLength a 0 L ≤ R), A S L := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, maxLargest, lt_iSup_iff, aLargest] at hω
    obtain ⟨k, hk, S, hS, hlt⟩ := hω
    have hmono : StrictMono (e ⟨S, hS⟩) := (S.orderEmbOfFin hS).strictMono
    refine Set.mem_iUnion.2 ⟨⟨S, hS⟩, Set.mem_iUnion.2 ⟨pairList (pathPt 0 k) (e ⟨S, hS⟩),
      Set.mem_iUnion.2 ⟨pairLength_le_of_energy_le k hk hmono, Set.mem_iInter.2 fun h => ?_⟩⟩⟩
    have hmem : e ⟨S, hS⟩ h ∈ S := S.orderEmbOfFin_mem hS h
    have hentry : ENNReal.ofReal x < seqEntry Z k ω (e ⟨S, hS⟩ h) :=
      lt_of_lt_of_le hlt (biInf_le _ hmem)
    have hlt' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx.le).1 hentry
    change x < Z (e ⟨S, hS⟩ h) ω (pathPt 0 k (e ⟨S, hS⟩ h))
      (pathPt 0 k ((e ⟨S, hS⟩ h : ℕ) + 1))
    rwa [pathPt_succ]
  have hA : ∀ S L, P (A S L) ≤ q := fun S L =>
    measure_iInter_lt_le hmeas hnonneg hind hint hmom (S.1.orderEmbOfFin S.2).injective L hx
  have hL : ∀ S, P (⋃ (L) (_ : pairLength a 0 L ≤ R), A S L) ≤ pairCount m a R * q := by
    intro S
    calc P (⋃ (L) (_ : pairLength a 0 L ≤ R), A S L)
        ≤ ∑' L, P (⋃ _ : pairLength a 0 L ≤ R, A S L) := measure_iUnion_le _
      _ ≤ ∑' L, (if pairLength a 0 L ≤ R then 1 else 0) * q :=
          ENNReal.tsum_le_tsum fun L => by
            by_cases h : pairLength a 0 L ≤ R
            · simpa only [h, Set.iUnion_true, ↓reduceIte, one_mul] using hA S L
            · simp [h]
      _ = pairCount m a R * q := ENNReal.tsum_mul_right
  calc P {ω | ENNReal.ofReal x < maxLargest Z r a ω}
      ≤ P (⋃ (S) (L) (_ : pairLength a 0 L ≤ R), A S L) := measure_mono hsub
    _ ≤ ∑' S, P (⋃ (L) (_ : pairLength a 0 L ≤ R), A S L) := measure_iUnion_le _
    _ ≤ ∑' _S : {S : Finset (Fin M) // S.card = a}, pairCount m a R * q :=
        ENNReal.tsum_le_tsum hL
    _ = (M.choose a : ℝ≥0∞) * pairCount m a R * q := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
          Fintype.card_fin, nsmul_eq_mul, mul_assoc]

end Union

/-- The constant of the levels of `Y_a`. -/
noncomputable def levelConst (m : ℕ) : ℝ := 1 + tripleCountConst m

lemma one_le_levelConst (m : ℕ) : 1 ≤ levelConst m := by
  have := tripleCountConst_pos m
  unfold levelConst
  linarith only [this]

/-- With `b = B 2^{r/4} q^{1/2}`, where `q = M/a`, the count `c = [C 2^{rd} q^{2d}]^a` of the sets
of triples and the level `2^j b` satisfy `c (2^j b)^{-4da} ≤ 16^{-j}`. -/
lemma level_real_le {a r : ℕ} (j : ℕ) (ha : 1 ≤ a) {q : ℝ} (hq : 1 ≤ q) :
    (tripleCountConst m * 2 ^ (r * (m + 1)) * q ^ (2 * (m + 1))) ^ a *
      (((2 ^ j * (levelConst m * 2 ^ ((r : ℝ) / 4) * q ^ ((1 : ℝ) / 2))) ^ (4 * (m + 1)))⁻¹) ^ a ≤
      (1 / 16) ^ j := by
  have hq0 : 0 < q := by linarith only [hq]
  have hB1 := one_le_levelConst m
  have hB0 : 0 < levelConst m := by linarith only [hB1]
  set τ : ℝ := (2 : ℝ) ^ ((r : ℝ) / 4) with hτ
  set s : ℝ := q ^ ((1 : ℝ) / 2) with hs
  have hτ0 : 0 < τ := by positivity
  have hs0 : 0 < s := by positivity
  have hτ4 : τ ^ 4 = 2 ^ r := by
    rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (r : ℝ) / 4 * ((4 : ℕ) : ℝ) = r := by push_cast; ring
    rw [this, Real.rpow_natCast]
  have hs2 : s ^ 2 = q := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    norm_num
  set b : ℝ := levelConst m * τ * s with hb
  have hb0 : 0 < b := by positivity
  set p : ℕ := 4 * (m + 1) with hp
  set c : ℝ := tripleCountConst m * 2 ^ (r * (m + 1)) * q ^ (2 * (m + 1)) with hc
  have hc0 : 0 < c := by
    have := tripleCountConst_pos m
    positivity
  have hcb : c ≤ b ^ p := by
    have h1 : b ^ p = levelConst m ^ p * (τ ^ 4) ^ (m + 1) * (s ^ 2) ^ (2 * (m + 1)) := by
      rw [hb, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      congr 2
      rw [hp]
      ring
    have h2 : tripleCountConst m ≤ levelConst m ^ p := by
      have h3 : levelConst m ≤ levelConst m ^ p := le_self_pow₀ hB1 (by omega)
      have h4 : tripleCountConst m ≤ levelConst m := by
        unfold levelConst
        linarith only
      exact h4.trans h3
    rw [h1, hτ4, hs2, ← pow_mul, hc]
    gcongr
  have h16 : (16 : ℝ) ^ j ≤ ((2 : ℝ) ^ j) ^ p := by
    have h1 : ((2 : ℝ) ^ j) ^ p = ((16 : ℝ) ^ j) ^ (m + 1) := by
      rw [← pow_mul, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, hp]
      congr 1
      ring
    rw [h1]
    exact le_self_pow₀ (one_le_pow₀ (by norm_num)) (by omega)
  set t : ℝ := c * ((2 ^ j * b) ^ p)⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ (1 / 16) ^ j := by
    have hb' : 0 < b ^ p := by positivity
    have h2 : 0 < (2 : ℝ) ^ j := by positivity
    rw [ht, mul_pow, mul_inv, one_div, inv_pow]
    calc c * ((((2 : ℝ) ^ j) ^ p)⁻¹ * (b ^ p)⁻¹)
        = c * (b ^ p)⁻¹ * (((2 : ℝ) ^ j) ^ p)⁻¹ := by ring
      _ ≤ 1 * ((16 : ℝ) ^ j)⁻¹ := by
          gcongr
          exact mul_inv_le_one_of_le₀ hcb hb'.le
      _ = ((16 : ℝ) ^ j)⁻¹ := one_mul _
  have ht2 : t ≤ 1 := ht1.trans (pow_le_one₀ (by norm_num) (by norm_num))
  rw [← mul_pow]
  exact (pow_le_of_le_one ht0 ht2 (by omega)).trans ht1

/-- `∑_{a ≤ M} (M/a)^{1/2} ≤ 2 M`, the sum over `a` in [AB26, Lemma 2.4]. -/
lemma sum_rpow_half_le (M : ℕ) :
    ∑ a ∈ Finset.Icc 1 M, ((M : ℝ) / a) ^ ((1 : ℝ) / 2) ≤ 2 * M := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h := sum_Icc_rpow_neg_le (θ := 1 / 2) (by norm_num) (by norm_num) M
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [e] at h
  calc ∑ a ∈ Finset.Icc 1 M, ((M : ℝ) / a) ^ ((1 : ℝ) / 2)
      = (M : ℝ) ^ ((1 : ℝ) / 2) * ∑ a ∈ Finset.Icc 1 M, (a : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Real.div_rpow hM (Nat.cast_nonneg a), Real.rpow_neg (Nat.cast_nonneg a), div_eq_mul_inv]
    _ ≤ (M : ℝ) ^ ((1 : ℝ) / 2) * ((M : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * ((M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((1 : ℝ) / 2)) := by ring
    _ = 2 * M := by
        rw [← Real.rpow_add_of_nonneg hM (by norm_num) (by norm_num)]
        norm_num

section Square

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ}
  (hmeas : ∀ i j k, Measurable (fun ω => Z i ω j k))
  (hnonneg : ∀ i ω j k, 0 ≤ Z i ω j k)
  (hind : iIndepFun Z P)
  (hint : ∀ i j k, Integrable (fun ω => Z i ω j k ^ (4 * (m + 1))) P)
  (hmom : ∀ i j k, ∫ ω, Z i ω j k ^ (4 * (m + 1)) ∂P ≤ 1)

include hmeas hnonneg hind hint hmom

/-- `E[Y_a²]^{1/2} ≤ C 2^{r/4} (M/a)^{1/2}` ([AB26, Lemma 2.4]), for `1 ≤ a ≤ M`. -/
theorem lintegral_maxLargest_sq_le {a : ℕ} (r : ℕ) (ha : 1 ≤ a) (haM : a ≤ M) :
    ∫⁻ ω, maxLargest Z r a ω ^ 2 ∂P ≤
      ENNReal.ofReal
        (3 * (levelConst m * 2 ^ ((r : ℝ) / 4) * ((M : ℝ) / a) ^ ((1 : ℝ) / 2))) ^ 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hq1 : 1 ≤ (M : ℝ) / a := (one_le_div ha0).2 (by exact_mod_cast haM)
  have hq0 : 0 < (M : ℝ) / a := by linarith only [hq1]
  have hB0 : 0 < levelConst m := by linarith only [one_le_levelConst m]
  set b : ℝ := levelConst m * 2 ^ ((r : ℝ) / 4) * ((M : ℝ) / a) ^ ((1 : ℝ) / 2) with hb
  have hb0 : 0 < b := by positivity
  refine lintegral_sq_le_of_dyadic_tail (measurable_maxLargest hmeas r a) hb0 fun j => ?_
  have hx : 0 < 2 ^ j * b := by positivity
  have hu : 0 ≤ ((2 ^ j * b) ^ (4 * (m + 1)))⁻¹ := by positivity
  calc P {ω | ENNReal.ofReal (2 ^ j * b) < maxLargest Z r a ω}
      ≤ (M.choose a : ℝ≥0∞) * pairCount m a (Real.sqrt m * 2 ^ ((r : ℝ) / 2) * M) *
          ENNReal.ofReal (((2 ^ j * b) ^ (4 * (m + 1)))⁻¹) ^ a :=
        measure_lt_maxLargest_le hmeas hnonneg hind hint hmom r hx
    _ ≤ ENNReal.ofReal ((tripleCountConst m * 2 ^ (r * (m + 1)) *
            ((M : ℝ) / a) ^ (2 * (m + 1))) ^ a) *
          ENNReal.ofReal (((2 ^ j * b) ^ (4 * (m + 1)))⁻¹) ^ a :=
        mul_le_mul' (choose_mul_pairCount_le ha haM r) le_rfl
    _ = ENNReal.ofReal
          ((tripleCountConst m * 2 ^ (r * (m + 1)) * ((M : ℝ) / a) ^ (2 * (m + 1))) ^ a *
            (((2 ^ j * b) ^ (4 * (m + 1)))⁻¹) ^ a) := by
        rw [ENNReal.ofReal_mul (by have := tripleCountConst_pos m; positivity),
          ENNReal.ofReal_pow hu]
    _ ≤ ENNReal.ofReal ((1 / 16) ^ j) := ENNReal.ofReal_le_ofReal (level_real_le j ha hq1)

/-- `E[V_r²]^{1/2} ≤ C M 2^{r/4}` ([AB26, Lemma 2.4]). -/
theorem lintegral_maxSum_sq_le (r : ℕ) :
    ∫⁻ ω, maxSum Z r ω ^ 2 ∂P ≤ ENNReal.ofReal (6 * levelConst m * 2 ^ ((r : ℝ) / 4) * M) ^ 2 := by
  have hB0 : 0 < levelConst m := by linarith only [one_le_levelConst m]
  set B : ℝ := levelConst m with hB
  set τ : ℝ := (2 : ℝ) ^ ((r : ℝ) / 4) with hτ
  have hτ0 : 0 < τ := by positivity
  set f : ℕ → ℝ := fun a => 3 * (B * τ * ((M : ℝ) / a) ^ ((1 : ℝ) / 2)) with hf
  have hf0 : ∀ a, 0 ≤ f a := fun a => by
    simp only [hf]
    positivity
  have hsum := lintegral_sum_sq_le (P := P) (Finset.Icc 1 M) (Y := fun a => maxLargest Z r a)
    (measurable_maxLargest hmeas r) (c := fun a => ENNReal.ofReal (f a)) fun a ha => by
      rw [Finset.mem_Icc] at ha
      exact lintegral_maxLargest_sq_le hmeas hnonneg hind hint hmom r ha.1 ha.2
  have hle : ∑ a ∈ Finset.Icc 1 M, ENNReal.ofReal (f a) ≤ ENNReal.ofReal (6 * B * τ * M) := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => hf0 a]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∑ a ∈ Finset.Icc 1 M, f a
        = 3 * B * τ * ∑ a ∈ Finset.Icc 1 M, ((M : ℝ) / a) ^ ((1 : ℝ) / 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by simp only [hf]; ring
      _ ≤ 3 * B * τ * (2 * M) := mul_le_mul_of_nonneg_left (sum_rpow_half_le M) (by positivity)
      _ = 6 * B * τ * M := by ring
  calc ∫⁻ ω, maxSum Z r ω ^ 2 ∂P
      ≤ ∫⁻ ω, (∑ a ∈ Finset.Icc 1 M, maxLargest Z r a ω) ^ 2 ∂P :=
        lintegral_mono fun ω => pow_le_pow_left₀ zero_le (maxSum_le_sum_maxLargest Z r ω) 2
    _ ≤ (∑ a ∈ Finset.Icc 1 M, ENNReal.ofReal (f a)) ^ 2 := hsum
    _ ≤ _ := pow_le_pow_left₀ zero_le hle 2

end Square

/-- The first display of [AB26, Lemma 2.4]: the penalized sum of any sequence is at most
`V_0 + ∑_{r ≥ 1} (V_r - 2^{r-1} M)₊`. -/
theorem ofReal_sub_le_maxSum {Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ}
    (hnonneg : ∀ i ω j k, 0 ≤ Z i ω j k) (hM : 1 ≤ M) (k : Fin M → Fin m → ℤ) (ω : Ω) :
    ENNReal.ofReal ((∑ i : Fin M, Z i ω (pathPt 0 k i) (k i)) - energy 0 k) ≤
      maxSum Z 0 ω + ∑' r : ℕ, (maxSum Z (r + 1) ω - ENNReal.ofReal (2 ^ r * M)) := by
  classical
  set x : ℝ := ∑ i : Fin M, Z i ω (pathPt 0 k i) (k i) with hx
  have hx0 : 0 ≤ x := Finset.sum_nonneg fun i _ => hnonneg _ _ _ _
  have hE0 := energy_nonneg (0 : Fin m → ℤ) k
  have hV : ∀ r : ℕ, energy 0 k ≤ 2 ^ r * M → ENNReal.ofReal x ≤ maxSum Z r ω := fun r hr => by
    rw [hx, ENNReal.ofReal_sum_of_nonneg fun i _ => hnonneg _ _ _ _]
    exact le_iSup₂_of_le k hr le_rfl
  have hex : ∃ r : ℕ, energy 0 k ≤ 2 ^ r * M := by
    obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt (energy (0 : Fin m → ℤ) k) (by norm_num : (1 : ℝ) < 2)
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    exact ⟨r, hr.le.trans (le_mul_of_one_le_right (by positivity) hM')⟩
  obtain h0 | ⟨r, hr⟩ : Nat.find hex = 0 ∨ ∃ r, Nat.find hex = r + 1 := by
    cases Nat.find hex with
    | zero => exact Or.inl rfl
    | succ r => exact Or.inr ⟨r, rfl⟩
  · have hspec := Nat.find_spec hex
    rw [h0] at hspec
    calc ENNReal.ofReal (x - energy 0 k) ≤ ENNReal.ofReal x :=
          ENNReal.ofReal_le_ofReal (by linarith only [hE0])
      _ ≤ maxSum Z 0 ω := hV 0 hspec
      _ ≤ _ := le_self_add
  · have hspec := Nat.find_spec hex
    rw [hr] at hspec
    have hnot : ¬ energy 0 k ≤ 2 ^ r * M := Nat.find_min hex (by omega)
    have hlt : (2 : ℝ) ^ r * M < energy 0 k := not_le.mp hnot
    calc ENNReal.ofReal (x - energy 0 k) ≤ ENNReal.ofReal (x - 2 ^ r * M) :=
          ENNReal.ofReal_le_ofReal (by linarith only [hlt])
      _ = ENNReal.ofReal x - ENNReal.ofReal (2 ^ r * M) := ENNReal.ofReal_sub _ (by positivity)
      _ ≤ maxSum Z (r + 1) ω - ENNReal.ofReal (2 ^ r * M) := tsub_le_tsub_right (hV _ hspec) _
      _ ≤ ∑' r : ℕ, (maxSum Z (r + 1) ω - ENNReal.ofReal (2 ^ r * M)) :=
          ENNReal.le_tsum (f := fun r : ℕ => maxSum Z (r + 1) ω - ENNReal.ofReal (2 ^ r * M)) r
      _ ≤ _ := le_add_self

/-- `(2^{(r+1)/4})² ≤ 2 (3/2)^r`. -/
lemma rpow_quarter_sq_le (r : ℕ) :
    ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 4)) ^ 2 ≤ 2 * (3 / 2) ^ r := by
  set w : ℝ := Real.sqrt 2 with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg 2
  have hw2 : w ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hw32 : w ≤ 3 / 2 := by nlinarith only [hw0, hw2]
  have e : ((2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 4)) ^ 2 = w ^ (r + 1) := by
    rw [hw, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  rw [e, pow_succ, mul_comm]
  have h1 : w ^ r ≤ (3 / 2) ^ r := pow_le_pow_left₀ hw0 hw32 r
  have h2 : w ≤ 2 := by linarith only [hw32]
  exact mul_le_mul h2 h1 (by positivity) (by norm_num)

/-- **[AB26, Lemma 2.4]**, by the `L²` counting of its proof:
independent arrays of nonnegative random variables with unit `4d`-th moments, `d = m + 1`, have an
expected penalized supremum at most `C M`. The sequence consists of its `M` free indices, with
`pathPt 0 k 0 = 0` its initial point. -/
theorem lintegral_iSup_penalizedSum_le_of_square (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (Ω : Type*) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ),
      (∀ i j k, Measurable (fun ω => Z i ω j k)) →
      (∀ i ω j k, 0 ≤ Z i ω j k) →
      iIndepFun Z P →
      (∀ i j k, Integrable (fun ω => Z i ω j k ^ (4 * (m + 1))) P) →
      (∀ i j k, ∫ ω, Z i ω j k ^ (4 * (m + 1)) ∂P ≤ 1) →
      (∫⁻ ω, ⨆ k : Fin M → Fin m → ℤ,
        ENNReal.ofReal ((∑ i : Fin M, Z i ω (pathPt 0 k i) (k i)) -
          ∑ i : Fin M, ∑ j : Fin m,
            ((k i j : ℝ) - (pathPt 0 k i j : ℝ)) ^ 2) ∂P) ≤
        ENNReal.ofReal (C * M) := by
  have hB0 : 0 < levelConst m := by linarith only [one_le_levelConst m]
  set K : ℝ := 6 * levelConst m with hK
  have hK0 : 0 < K := by positivity
  refine ⟨1 + 9 * K ^ 2, by positivity, fun M Ω _ P _ Z hmeas hnonneg hind hint hmom => ?_⟩
  by_cases hM : 1 ≤ M
  · have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hV2 := lintegral_maxSum_sq_le hmeas hnonneg hind hint hmom
    have hmV := measurable_maxSum hmeas
    have hzero : ∫⁻ ω, maxSum Z 0 ω ∂P ≤ ENNReal.ofReal ((1 + K ^ 2) * M) := by
      set c : ℝ≥0∞ := ENNReal.ofReal M with hc
      have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hM0).ne'
      have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
      have hpt : ∀ ω, maxSum Z 0 ω ≤ c + maxSum Z 0 ω ^ 2 * c⁻¹ := fun ω =>
        le_tsub_add.trans (by rw [add_comm]; exact add_le_add le_rfl (tsub_le_sq_mul_inv hc0 hct))
      have hV0 := hV2 0
      rw [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one] at hV0
      calc ∫⁻ ω, maxSum Z 0 ω ∂P
          ≤ ∫⁻ ω, c + maxSum Z 0 ω ^ 2 * c⁻¹ ∂P := lintegral_mono hpt
        _ = c + (∫⁻ ω, maxSum Z 0 ω ^ 2 ∂P) * c⁻¹ := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
              lintegral_mul_const _ ((hmV 0).pow_const 2)]
        _ ≤ c + ENNReal.ofReal (K * M) ^ 2 * c⁻¹ :=
            add_le_add le_rfl (mul_le_mul' hV0 le_rfl)
        _ = ENNReal.ofReal (M + (K * M) ^ 2 * (M : ℝ)⁻¹) := by
            have hinv : c⁻¹ = ENNReal.ofReal ((M : ℝ)⁻¹) := (ENNReal.ofReal_inv_of_pos hM0).symm
            rw [hinv, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add hM0.le (by positivity)]
        _ = ENNReal.ofReal ((1 + K ^ 2) * M) := by
            congr 1
            field_simp
    have hterm : ∀ r : ℕ, ∫⁻ ω, (maxSum Z (r + 1) ω - ENNReal.ofReal (2 ^ r * M)) ∂P ≤
        ENNReal.ofReal (2 * K ^ 2 * M * (3 / 4) ^ r) := by
      intro r
      have hc1 : (0 : ℝ) < 2 ^ r * M := by positivity
      set c : ℝ≥0∞ := ENNReal.ofReal (2 ^ r * M) with hc
      have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hc1).ne'
      have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
      set τ : ℝ := (2 : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 4) with hτ
      have hτ0 : 0 < τ := by positivity
      have hτ2 : τ ^ 2 ≤ 2 * (3 / 2) ^ r := rpow_quarter_sq_le r
      calc ∫⁻ ω, (maxSum Z (r + 1) ω - c) ∂P
          ≤ ∫⁻ ω, maxSum Z (r + 1) ω ^ 2 * c⁻¹ ∂P :=
            lintegral_mono fun ω => tsub_le_sq_mul_inv hc0 hct
        _ = (∫⁻ ω, maxSum Z (r + 1) ω ^ 2 ∂P) * c⁻¹ :=
            lintegral_mul_const _ ((hmV (r + 1)).pow_const 2)
        _ ≤ ENNReal.ofReal (K * τ * M) ^ 2 * c⁻¹ := mul_le_mul' (hV2 (r + 1)) le_rfl
        _ = ENNReal.ofReal ((K * τ * M) ^ 2 * ((2 : ℝ) ^ r * M)⁻¹) := by
            have hinv : c⁻¹ = ENNReal.ofReal (((2 : ℝ) ^ r * M)⁻¹) :=
              (ENNReal.ofReal_inv_of_pos hc1).symm
            rw [hinv, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (2 * K ^ 2 * M * (3 / 4) ^ r) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h34 : ((3 : ℝ) / 2) ^ r = 2 ^ r * (3 / 4) ^ r := by
              rw [← mul_pow]
              norm_num
            have h2 : (0 : ℝ) < 2 ^ r := by positivity
            calc (K * τ * M) ^ 2 * ((2 : ℝ) ^ r * M)⁻¹
                = K ^ 2 * M * (τ ^ 2 * ((2 : ℝ) ^ r)⁻¹) := by
                  field_simp
              _ ≤ K ^ 2 * M * (2 * (3 / 2) ^ r * ((2 : ℝ) ^ r)⁻¹) := by gcongr
              _ = 2 * K ^ 2 * M * (3 / 4) ^ r := by
                  rw [h34]
                  field_simp
    have hsum : ∑' r : ℕ, ENNReal.ofReal (2 * K ^ 2 * M * (3 / 4) ^ r) =
        ENNReal.ofReal (8 * K ^ 2 * M) := by
      have hs : Summable fun r : ℕ => 2 * K ^ 2 * M * ((3 : ℝ) / 4) ^ r :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => by positivity) hs, tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      congr 1
      norm_num
      ring
    calc ∫⁻ ω, ⨆ k : Fin M → Fin m → ℤ,
          ENNReal.ofReal ((∑ i : Fin M, Z i ω (pathPt 0 k i) (k i)) -
            ∑ i : Fin M, ∑ j : Fin m, ((k i j : ℝ) - (pathPt 0 k i j : ℝ)) ^ 2) ∂P
        ≤ ∫⁻ ω, maxSum Z 0 ω +
            ∑' r : ℕ, (maxSum Z (r + 1) ω - ENNReal.ofReal (2 ^ r * M)) ∂P :=
          lintegral_mono fun ω => iSup_le fun k => by
            rw [← energy_eq_sum_sq]
            exact ofReal_sub_le_maxSum hnonneg hM k ω
      _ = ∫⁻ ω, maxSum Z 0 ω ∂P +
            ∑' r : ℕ, ∫⁻ ω, (maxSum Z (r + 1) ω - ENNReal.ofReal (2 ^ r * M)) ∂P := by
          rw [lintegral_add_left (hmV 0),
            lintegral_tsum fun r => ((hmV (r + 1)).sub_const _).aemeasurable]
      _ ≤ ENNReal.ofReal ((1 + K ^ 2) * M) + ENNReal.ofReal (8 * K ^ 2 * M) :=
          add_le_add hzero ((ENNReal.tsum_le_tsum hterm).trans_eq hsum)
      _ = ENNReal.ofReal ((1 + 9 * K ^ 2) * M) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  · have : M = 0 := by omega
    subst M
    simp

end CurvatureVariance.Infra.Arrays
