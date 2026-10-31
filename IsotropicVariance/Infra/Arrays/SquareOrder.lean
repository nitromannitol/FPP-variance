/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Order statistics and square integrals for Lemma `lem:polynomialarray`

The steps of the paper's proof that do not involve the arrays.

* `aLargest x a`: the `a`-th largest of the numbers `x i`, and `sum_le_sum_aLargest`, a sum is at
  most the sum of its `a`-th largest terms.
* `lintegral_sq_le_of_dyadic_tail`: from the tail bound of a union bound to `E[Y²]`. The paper
  leaves this integration implicit; the dyadic levels below stay in `ℝ≥0∞`, so no a priori
  finiteness of the supremum is needed.
* `lintegral_sum_sq_le`: Minkowski's inequality in `L²` over a finite sum, used for "summing over
  `a`".
* `tsub_le_sq_mul_inv`: `(x - c)₊ ≤ x²/c`, which gives
  `E[(V_r - 2^{r-1} M)₊] ≤ E[V_r²]/(2^{r-1} M)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Infra.Arrays

/-- The `a`-th largest of the numbers `x i`, counted with multiplicity: the maximum, over the sets
of `a` indices, of the minimum over the set. -/
noncomputable def aLargest {ι : Type*} (x : ι → ℝ≥0∞) (a : ℕ) : ℝ≥0∞ :=
  ⨆ (S : Finset ι) (_ : S.card = a), ⨅ i ∈ S, x i

/-- A finite sum is at most the sum of its `a`-th largest terms (the bound `V_r ≤ ∑_a Y_a` in the
proof of Lemma `lem:polynomialarray`). -/
theorem sum_le_sum_aLargest {ι : Type*} (x : ι → ℝ≥0∞) (s : Finset ι) :
    ∑ i ∈ s, x i ≤ ∑ a ∈ Finset.Icc 1 s.card, aLargest x a := by
  classical
  induction h : s.card generalizing s with
  | zero => simp [Finset.card_eq_zero.mp h]
  | succ n ih =>
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image s x hne
    have hcard : (s.erase i₀).card = n := by rw [Finset.card_erase_of_mem hi₀, h]; rfl
    have htop : x i₀ ≤ aLargest x (n + 1) :=
      le_iSup₂_of_le s h (le_iInf₂ fun i hi => hmin i hi)
    rw [← Finset.add_sum_erase s x hi₀, Finset.sum_Icc_succ_top (by omega), add_comm]
    exact add_le_add (ih _ hcard) htop

/-- `(x - c)₊ ≤ x²/c` for `0 < c < ∞`. -/
lemma tsub_le_sq_mul_inv {x c : ℝ≥0∞} (h0 : c ≠ 0) (ht : c ≠ ⊤) : x - c ≤ x ^ 2 * c⁻¹ := by
  by_cases hx : x ≤ c
  · rw [tsub_eq_zero_of_le hx]
    exact zero_le
  · have hc : c ≤ x := (not_le.mp hx).le
    calc x - c ≤ x := tsub_le_self
      _ = x * (c * c⁻¹) := by rw [ENNReal.mul_inv_cancel h0 ht, mul_one]
      _ ≤ x * (x * c⁻¹) := by gcongr
      _ = x ^ 2 * c⁻¹ := by ring

/-- The dyadic layer-cake bound at one point: `y² ≤ b² + ∑_j (2^{j+1} b)² 1_{y > 2^j b}`. -/
lemma sq_le_add_tsum_dyadic {b : ℝ} (hb : 0 < b) (y : ℝ≥0∞) :
    y ^ 2 ≤ ENNReal.ofReal (b ^ 2) + ∑' j : ℕ,
      if ENNReal.ofReal (2 ^ j * b) < y then ENNReal.ofReal ((2 ^ (j + 1) * b) ^ 2) else 0 := by
  classical
  by_cases hfin : ∃ j : ℕ, y ≤ ENNReal.ofReal (2 ^ j * b)
  · have hsq : ∀ j : ℕ, y ≤ ENNReal.ofReal (2 ^ j * b) →
        y ^ 2 ≤ ENNReal.ofReal ((2 ^ j * b) ^ 2) := fun j h => by
      rw [ENNReal.ofReal_pow (by positivity)]
      exact pow_le_pow_left₀ zero_le h 2
    obtain h0 | ⟨j, hj⟩ : Nat.find hfin = 0 ∨ ∃ j, Nat.find hfin = j + 1 := by
      cases Nat.find hfin with
      | zero => exact Or.inl rfl
      | succ j => exact Or.inr ⟨j, rfl⟩
    · have hspec := Nat.find_spec hfin
      rw [h0] at hspec
      have h := hsq 0 hspec
      rw [pow_zero, one_mul] at h
      exact h.trans le_self_add
    · have hspec := Nat.find_spec hfin
      rw [hj] at hspec
      have hle := hsq (j + 1) hspec
      have hnot : ENNReal.ofReal (2 ^ j * b) < y := not_le.mp (Nat.find_min hfin (by omega))
      refine hle.trans (le_trans ?_ le_add_self)
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum j)
      simp only [hnot, ↓reduceIte]
  · push Not at hfin
    have hbig : ∀ j : ℕ, ENNReal.ofReal (b ^ 2) ≤
        if ENNReal.ofReal (2 ^ j * b) < y then ENNReal.ofReal ((2 ^ (j + 1) * b) ^ 2) else 0 := by
      intro j
      simp only [hfin j, ↓reduceIte]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
      have h3 : b ≤ 2 ^ (j + 1) * b := le_mul_of_one_le_left hb.le h2
      exact pow_le_pow_left₀ hb.le h3 2
    have htop : ∑' j : ℕ,
        (if ENNReal.ofReal (2 ^ j * b) < y then ENNReal.ofReal ((2 ^ (j + 1) * b) ^ 2) else 0) =
          ⊤ := by
      refine top_le_iff.mp (le_trans (le_of_eq ?_) (ENNReal.tsum_le_tsum hbig))
      exact (ENNReal.tsum_const_eq_top_of_ne_zero
        (ENNReal.ofReal_pos.mpr (by positivity)).ne').symm
    rw [htop, add_top]
    exact le_top

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- From a tail bound at the dyadic levels `2^j b` to the square integral: the step from the union
bound to `E[Y_a²]^{1/2}` in the proof of Lemma `lem:polynomialarray`. -/
theorem lintegral_sq_le_of_dyadic_tail [IsProbabilityMeasure P] {Y : Ω → ℝ≥0∞} (hY : Measurable Y)
    {b : ℝ} (hb : 0 < b)
    (htail : ∀ j : ℕ, P {ω | ENNReal.ofReal (2 ^ j * b) < Y ω} ≤ ENNReal.ofReal ((1 / 16) ^ j)) :
    ∫⁻ ω, Y ω ^ 2 ∂P ≤ ENNReal.ofReal (3 * b) ^ 2 := by
  classical
  set A : ℕ → Set Ω := fun j => {ω | ENNReal.ofReal (2 ^ j * b) < Y ω} with hA
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((2 ^ (j + 1) * b) ^ 2) with hc
  have hmeas : ∀ j, MeasurableSet (A j) := fun j => measurableSet_lt measurable_const hY
  have hpoint : ∀ ω, Y ω ^ 2 ≤
      ENNReal.ofReal (b ^ 2) + ∑' j : ℕ, (A j).indicator (fun _ => c j) ω := fun ω =>
    (sq_le_add_tsum_dyadic hb (Y ω)).trans_eq (by
      simp only [hA, hc, Set.indicator_apply, Set.mem_ofPred_eq])
  have hterm : ∀ j : ℕ, c j * P (A j) ≤ ENNReal.ofReal (4 * b ^ 2 * (1 / 4) ^ j) := by
    intro j
    calc c j * P (A j) ≤ c j * ENNReal.ofReal ((1 / 16) ^ j) := mul_le_mul' le_rfl (htail j)
      _ = ENNReal.ofReal ((2 ^ (j + 1) * b) ^ 2 * (1 / 16) ^ j) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (4 * b ^ 2 * (1 / 4) ^ j) := by
          congr 1
          have h16 : ((1 : ℝ) / 16) ^ j = (1 / 4) ^ j * (1 / 4) ^ j := by
            rw [← mul_pow]; norm_num
          have h44 : ((2 : ℝ) ^ j) ^ 2 * (1 / 4) ^ j = 1 := by
            rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]; norm_num
          rw [h16, pow_succ' 2 j]
          linear_combination (4 * b ^ 2 * (1 / 4) ^ j) * h44
  have hsum : ∑' j : ℕ, ENNReal.ofReal (4 * b ^ 2 * (1 / 4) ^ j) =
      ENNReal.ofReal (4 * b ^ 2 * (4 / 3)) := by
    have hs : Summable fun j : ℕ => 4 * b ^ 2 * ((1 : ℝ) / 4) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc ∫⁻ ω, Y ω ^ 2 ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (b ^ 2) + ∑' j : ℕ, (A j).indicator (fun _ => c j) ω ∂P :=
        lintegral_mono hpoint
    _ = ENNReal.ofReal (b ^ 2) + ∑' j : ℕ, c j * P (A j) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun j => (measurable_const.indicator (hmeas j)).aemeasurable]
        simp only [lintegral_indicator_const (hmeas _)]
    _ ≤ ENNReal.ofReal (b ^ 2) + ENNReal.ofReal (4 * b ^ 2 * (4 / 3)) :=
        add_le_add le_rfl ((ENNReal.tsum_le_tsum hterm).trans_eq hsum)
    _ = ENNReal.ofReal (b ^ 2 + 4 * b ^ 2 * (4 / 3)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((3 * b) ^ 2) :=
        ENNReal.ofReal_le_ofReal (by nlinarith only [sq_nonneg b])
    _ = ENNReal.ofReal (3 * b) ^ 2 := ENNReal.ofReal_pow (by positivity) 2

/-- Minkowski's inequality in `L²` for a finite sum, in the form used for `V_r ≤ ∑_a Y_a` in the
proof of Lemma `lem:polynomialarray`. -/
theorem lintegral_sum_sq_le {ι : Type*} (s : Finset ι) {Y : ι → Ω → ℝ≥0∞}
    (hY : ∀ i, Measurable (Y i)) {c : ι → ℝ≥0∞} (h : ∀ i ∈ s, ∫⁻ ω, Y i ω ^ 2 ∂P ≤ c i ^ 2) :
    ∫⁻ ω, (∑ i ∈ s, Y i ω) ^ 2 ∂P ≤ (∑ i ∈ s, c i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hp : (0 : ℝ) < 2 := by norm_num
    have hS : Measurable fun ω => ∑ j ∈ s, Y j ω := Finset.measurable_fun_sum s fun j _ => hY j
    have key := ENNReal.lintegral_Lp_add_le (μ := P) (hY i).aemeasurable hS.aemeasurable
      (p := 2) (by norm_num)
    simp only [Pi.add_apply, ENNReal.rpow_two, one_div] at key
    have h1 : (∫⁻ ω, Y i ω ^ 2 ∂P) ^ (2 : ℝ)⁻¹ ≤ c i :=
      (ENNReal.rpow_inv_le_iff hp).2 (by
        rw [ENNReal.rpow_two]
        exact h i (Finset.mem_insert_self i s))
    have h2 : (∫⁻ ω, (∑ j ∈ s, Y j ω) ^ 2 ∂P) ^ (2 : ℝ)⁻¹ ≤ ∑ j ∈ s, c j :=
      (ENNReal.rpow_inv_le_iff hp).2 (by
        rw [ENNReal.rpow_two]
        exact ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    have h3 := (ENNReal.rpow_inv_le_iff hp).1 (key.trans (add_le_add h1 h2))
    rw [ENNReal.rpow_two] at h3
    simpa only [Finset.sum_insert hi] using h3

end Tail

end IsotropicVariance.Infra.Arrays
