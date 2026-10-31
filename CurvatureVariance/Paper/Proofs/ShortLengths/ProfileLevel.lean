/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.OsTail

/-!
# The least good level of an increasing family of events

The proof of Proposition `prop:profiles` for `s ≤ N/2`: "Let `S ≥ log N` be the least integer such
that `𝒢_N(S)` occurs, so that `S ≤ log N + 1 + O₂(C)`". For an increasing family `G j`
of measurable events (`j` counts the integers above `⌈log N⌉`), the number of failed levels
`failCount G ω = ∑ⱼ 1_{G jᶜ}(ω)` is measurable, almost surely finite when `P(G jᶜ) → 0`, and `ω`
lies in `G ⌈failCount G ω⌉` (`mem_of_failCount_ne_top`). If `P(G jᶜ) ≤ e^{-c j²/2}`, then
`B · failCount² ≤ O₁(C)` with `C` depending only on `B` and `c` (`isOs_failCount_sq`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Infra.Os CurvatureVariance.Paper.Proofs.Geometry

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The number of failed levels. -/
noncomputable def failCount (G : ℕ → Set Ω) (ω : Ω) : ℝ≥0∞ :=
  ∑' j, (G j)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω

theorem measurable_failCount {G : ℕ → Set Ω} (hG : ∀ j, MeasurableSet (G j)) :
    Measurable (failCount G) := by
  unfold failCount
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s => s.measurable_fun_sum fun j _ =>
    measurable_const.indicator (hG j).compl

omit [MeasurableSpace Ω] in
/-- In `G j`, at most `j` levels fail. -/
theorem failCount_le_of_mem {G : ℕ → Set Ω} (hmono : Monotone G) {ω : Ω} {j : ℕ}
    (h : ω ∈ G j) : failCount G ω ≤ j := by
  unfold failCount
  rw [tsum_eq_sum (s := Finset.range j) fun i hi => by
    have hij : j ≤ i := by simpa using hi
    rw [Set.indicator_of_notMem (show ω ∉ (G i)ᶜ from fun hc => hc (hmono hij h))]]
  calc ∑ i ∈ Finset.range j, (G i)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ω
      ≤ ∑ _i ∈ Finset.range j, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun i _ => Set.indicator_le_self _ (fun _ => (1 : ℝ≥0∞)) ω
    _ = j := by simp

omit [MeasurableSpace Ω] in
/-- If the count is finite, `ω` lies in the event at the level `⌈count⌉`. -/
theorem mem_of_failCount_ne_top {G : ℕ → Set Ω} (hmono : Monotone G) {ω : Ω}
    (hfin : failCount G ω ≠ ⊤) : ω ∈ G ⌈(failCount G ω).toReal⌉₊ := by
  by_contra hcon
  set J := ⌈(failCount G ω).toReal⌉₊ with hJ
  have hall : ∀ i ∈ Finset.range (J + 1), ω ∉ G i := fun i hi h =>
    hcon (hmono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) h)
  have hsum : ((J + 1 : ℕ) : ℝ≥0∞) ≤ failCount G ω := by
    calc ((J + 1 : ℕ) : ℝ≥0∞) = ∑ i ∈ Finset.range (J + 1), (G i)ᶜ.indicator
          (fun _ => (1 : ℝ≥0∞)) ω := by
          rw [Finset.sum_congr rfl fun i hi => Set.indicator_of_mem (hall i hi) _]
          simp
      _ ≤ failCount G ω := ENNReal.sum_le_tsum _
  have h1 := ENNReal.toReal_mono hfin hsum
  rw [ENNReal.toReal_natCast] at h1
  push_cast at h1
  have h2 := Nat.le_ceil (failCount G ω).toReal
  rw [← hJ] at h2
  linarith

omit [MeasurableSpace Ω] in
/-- The count exceeds `y > 0` only off the event at the level `⌈y⌉ − 1`. -/
theorem le_failCount_subset {G : ℕ → Set Ω} (hmono : Monotone G) {y : ℝ} (hy : 0 < y) :
    {ω | y ≤ (failCount G ω).toReal} ⊆ (G (⌈y⌉₊ - 1))ᶜ := by
  intro ω hω hmem
  have h1 := failCount_le_of_mem hmono hmem
  have hfin : failCount G ω ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) h1
  have h2 := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h1
  rw [ENNReal.toReal_natCast] at h2
  have h3 : ((⌈y⌉₊ - 1 : ℕ) : ℝ) < y := by
    have hc : 1 ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hy).ne'
    rw [Nat.cast_sub hc]
    have := Nat.ceil_lt_add_one hy.le
    push_cast
    linarith
  simp only [Set.mem_ofPred_eq] at hω
  linarith

/-- The count is almost surely finite when the failure probabilities tend to zero. -/
theorem ae_failCount_ne_top {P : Measure Ω} {G : ℕ → Set Ω} (hmono : Monotone G)
    (hlim : Tendsto (fun j => P (G j)ᶜ) atTop (𝓝 0)) : ∀ᵐ ω ∂P, failCount G ω ≠ ⊤ := by
  have hsub : ∀ j, {ω | failCount G ω = ⊤} ⊆ (G j)ᶜ := fun j ω hω hmem => by
    have := failCount_le_of_mem hmono hmem
    simp only [Set.mem_ofPred_eq] at hω
    rw [hω] at this
    exact ENNReal.natCast_ne_top j (top_le_iff.1 this)
  have h0 : P {ω | failCount G ω = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto' hlim fun j => measure_mono (hsub j)) bot_le
  rw [ae_iff]
  simpa using h0

/-- **The square of the count is `O₁`**: if `P(G jᶜ) ≤ e^{-c j²/2}` for every `j`, then
`B · count² ≤ O₁(C)` with `C` depending only on `B > 0` and `c > 0`. -/
theorem isOs_failCount_sq {P : Measure Ω} [IsProbabilityMeasure P] {G : ℕ → Set Ω}
    (hmono : Monotone G) (hG : ∀ j, MeasurableSet (G j)) {c B : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hfail : ∀ j : ℕ, P (G j)ᶜ ≤ ENNReal.ofReal (Real.exp (-(c / 2 * (j : ℝ) ^ 2)))) :
    IsOs P 1 ((1 + Real.log (Real.exp (c / 2)) / (2 * Real.log 2)) * (2 * (4 * B / c)))
      (fun ω => B * (failCount G ω).toReal ^ 2) := by
  have hK : 1 ≤ Real.exp (c / 2) := Real.one_le_exp (by linarith)
  refine isOs_one_of_measure_ge_le_mul_exp (by positivity) hK
    (((ENNReal.measurable_toReal.comp (measurable_failCount hG)).pow_const 2).const_mul
      B).aemeasurable fun x hx => ?_
  rcases hx.eq_or_lt with rfl | hx0
  · refine prob_le_one.trans ?_
    rw [neg_zero, Real.exp_zero, mul_one, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hK
  set y := Real.sqrt (4 * x / c) with hy
  have hy0 : 0 < y := Real.sqrt_pos.2 (by positivity)
  have hsub : {ω | 4 * B / c * x ≤ B * (failCount G ω).toReal ^ 2} ⊆
      {ω | y ≤ (failCount G ω).toReal} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have h1 : 4 * x / c ≤ (failCount G ω).toReal ^ 2 := by
      have : 4 * B / c * x = B * (4 * x / c) := by ring
      rw [this] at hω
      exact le_of_mul_le_mul_left hω hB
    calc y ≤ Real.sqrt ((failCount G ω).toReal ^ 2) := Real.sqrt_le_sqrt h1
      _ = (failCount G ω).toReal := Real.sqrt_sq ENNReal.toReal_nonneg
  refine (measure_mono (hsub.trans (le_failCount_subset hmono hy0))).trans
    ((hfail _).trans (ENNReal.ofReal_le_ofReal ?_))
  -- `e^{-(c/2) z²} ≤ e^{c/2} e^{-x}` for `z = ⌈y⌉ − 1 ≥ max(y − 1, 0)`, `y² = 4x/c`
  set z : ℝ := ((⌈y⌉₊ - 1 : ℕ) : ℝ) with hz
  have hz0 : 0 ≤ z := Nat.cast_nonneg _
  have hzy : y - 1 ≤ z := by
    have hc1 : 1 ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hy0).ne'
    rw [hz, Nat.cast_sub hc1]
    have := Nat.le_ceil y
    push_cast
    linarith
  have hy2 : y ^ 2 = 4 * x / c := Real.sq_sqrt (by positivity)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have key : c / 4 * y ^ 2 - c / 2 ≤ c / 2 * z ^ 2 := by
    rcases le_or_gt y 1 with h | h
    · have : c / 4 * y ^ 2 ≤ c / 4 := by
        have : y ^ 2 ≤ 1 := by nlinarith only [h, hy0]
        nlinarith only [this, hc]
      nlinarith only [this, hc, sq_nonneg z]
    · have h1 : (y - 1) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (by linarith) hzy 2
      have h2 : y ^ 2 / 2 - 1 ≤ (y - 1) ^ 2 := by nlinarith only [sq_nonneg (y - 2)]
      nlinarith only [h1, h2, hc]
  have : c / 4 * y ^ 2 = x := by rw [hy2]; field_simp
  linarith

end CurvatureVariance.Paper.Proofs.ShortLengths
