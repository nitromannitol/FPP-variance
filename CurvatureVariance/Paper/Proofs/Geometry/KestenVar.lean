/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.OsTail
public import CurvatureVariance.Infra.FPP.CheapPaths
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Kesten's estimate as a random variable

Kesten's estimate, as used in Section `sec:prelim`: the largest number of edges of a simple path
from `u` with passage time at most `a` times its number of edges is at most `O₁(C)`. Here
(`cheapLength a u`, valued in `ℝ≥0∞`):

* `le_cheapLength`: a simple path from `u` with `k` edges and cost at most `a k` has `k` at most
  the variable;
* `measure_ofReal_lt_cheapLength_le`: under `CheapPaths P a c`,
  `P(cheapLength > y) ≤ e^{-cy/2}/(1 − e^{-c/2})`, by a union bound over the lengths;
* `ae_cheapLength_lt_top`, `isOs_toReal_cheapLength`: it is almost surely finite and `O₁(C)`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Infra.FPP CurvatureVariance.Infra.Os

variable {m : ℕ}

/-- The event that some simple path from `u` with `k` edges costs at most `a k`. -/
def cheapEvent (a : ℝ) (u : Vertex m) (k : ℕ) : Set (Config m) :=
  {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk u v), γ.IsPath ∧ γ.length = k ∧
    (walkCost ω γ : ℝ) ≤ a * k}

theorem measurableSet_cheapEvent (a : ℝ) (u : Vertex m) (k : ℕ) :
    MeasurableSet (cheapEvent a u k) := by
  have : cheapEvent a u k = pathEvent u (fun l x => l = k ∧ x ≤ a * k) := by
    ext ω
    simp [cheapEvent, pathEvent]
  rw [this]
  refine measurableSet_pathEvent u fun l => ?_
  by_cases hl : l = k
  · have : {x : ℝ | l = k ∧ x ≤ a * k} = Set.Iic (a * k) := by
      ext x
      simp [hl]
    rw [this]
    exact measurableSet_Iic
  · simp [hl]

/-- The largest number of edges of a simple path from `u` costing at most `a` per edge. -/
noncomputable def cheapLength (a : ℝ) (u : Vertex m) (ω : Config m) : ℝ≥0∞ :=
  ⨆ k : ℕ, (cheapEvent a u k).indicator (fun _ => (k : ℝ≥0∞)) ω

theorem measurable_cheapLength (a : ℝ) (u : Vertex m) : Measurable (cheapLength a u) :=
  Measurable.iSup fun k => measurable_const.indicator (measurableSet_cheapEvent a u k)

theorem le_cheapLength {a : ℝ} {u v : Vertex m} {ω : Config m}
    (γ : (latticeGraph m).Walk u v) (hγ : γ.IsPath) (hcost : (walkCost ω γ : ℝ) ≤ a * γ.length) :
    (γ.length : ℝ≥0∞) ≤ cheapLength a u ω := by
  refine le_trans (le_of_eq ?_) (le_iSup _ γ.length)
  rw [Set.indicator_of_mem (show ω ∈ cheapEvent a u γ.length from ⟨v, γ, hγ, rfl, hcost⟩)]

/-- **The tail of the Kesten variable**: `P(cheapLength > y) ≤ e^{-cy/2} / (1 − e^{-c/2})`. -/
theorem measure_ofReal_lt_cheapLength_le {P : Measure (Config m)} {a c : ℝ} (hc : 0 < c)
    (hcheap : CheapPaths P a c) (u : Vertex m) (y : ℝ) :
    P {ω | ENNReal.ofReal y < cheapLength a u ω} ≤
      ENNReal.ofReal (Real.exp (-(c / 2 * y)) / (1 - Real.exp (-(c / 2)))) := by
  set F : ℕ → Set (Config m) := fun k => if y < k then cheapEvent a u k else ∅ with hF
  have hsub : {ω | ENNReal.ofReal y < cheapLength a u ω} ⊆ ⋃ k, F k := by
    intro ω hω
    obtain ⟨k, hk⟩ := lt_iSup_iff.1 (show ENNReal.ofReal y < cheapLength a u ω from hω)
    by_cases hmem : ω ∈ cheapEvent a u k
    · rw [Set.indicator_of_mem hmem] at hk
      have hyk : y < k := by
        rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff'] at hk
        exact hk.1
      exact Set.mem_iUnion.2 ⟨k, by simp only [hF, hyk, ↓reduceIte]; exact hmem⟩
    · rw [Set.indicator_of_notMem hmem] at hk
      exact absurd hk (not_lt_of_ge bot_le)
  have hr : Real.exp (-(c / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hr0 : 0 ≤ Real.exp (-(c / 2)) := (Real.exp_pos _).le
  have hterm : ∀ k : ℕ, P (F k) ≤
      ENNReal.ofReal (Real.exp (-(c / 2 * y))) * ENNReal.ofReal (Real.exp (-(c / 2))) ^ k := by
    intro k
    rw [← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_nat_mul,
      ← Real.exp_add]
    by_cases hyk : y < k
    · simp only [hF, hyk, ↓reduceIte]
      refine (hcheap u k).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      nlinarith
    · simp only [hF, hyk, ↓reduceIte, measure_empty, zero_le]
  calc P {ω | ENNReal.ofReal y < cheapLength a u ω} ≤ P (⋃ k, F k) := measure_mono hsub
    _ ≤ ∑' k, P (F k) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(c / 2 * y))) *
          ENNReal.ofReal (Real.exp (-(c / 2))) ^ k := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (Real.exp (-(c / 2 * y))) *
          (1 - ENNReal.ofReal (Real.exp (-(c / 2))))⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (Real.exp (-(c / 2 * y)) / (1 - Real.exp (-(c / 2)))) := by
        rw [div_eq_mul_inv (Real.exp _), ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_sub _ hr0, ENNReal.ofReal_one]

/-- The Kesten variable is almost surely finite. -/
theorem ae_cheapLength_lt_top {P : Measure (Config m)} {a c : ℝ} (hc : 0 < c)
    (hcheap : CheapPaths P a c) (u : Vertex m) : ∀ᵐ ω ∂P, cheapLength a u ω < ⊤ := by
  have hr : Real.exp (-(c / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set K := (1 - Real.exp (-(c / 2)))⁻¹ with hK
  have hbound : ∀ n : ℕ, P {ω | cheapLength a u ω = ⊤} ≤
      ENNReal.ofReal (K * Real.exp (-(c / 2 * n))) := by
    intro n
    refine (measure_mono fun ω hω => ?_).trans
      ((measure_ofReal_lt_cheapLength_le hc hcheap u n).trans (le_of_eq ?_))
    · simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hω]
      exact ENNReal.ofReal_lt_top
    · rw [hK, div_eq_mul_inv, mul_comm]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (K * Real.exp (-(c / 2 * n)))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.exp (-(c / 2 * n))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hc))
    have h2 := ENNReal.tendsto_ofReal (h1.const_mul K)
    rwa [mul_zero, ENNReal.ofReal_zero] at h2
  have h0 : P {ω | cheapLength a u ω = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) bot_le
  rw [ae_iff]
  simpa [lt_top_iff_ne_top] using h0

/-- **Kesten's estimate as an `O₁` variable**: the Kesten variable, as a real number, is `O₁(C)`
with `C` depending only on `c`. -/
theorem isOs_toReal_cheapLength {P : Measure (Config m)} [IsProbabilityMeasure P] {a c : ℝ}
    (hc : 0 < c) (hcheap : CheapPaths P a c) (u : Vertex m) :
    IsOs P 1 ((1 + Real.log (Real.exp (c / 2) / (1 - Real.exp (-(c / 2)))) / (2 * Real.log 2)) *
      (2 * (2 / c))) (fun ω => (cheapLength a u ω).toReal) := by
  have hr : Real.exp (-(c / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hK : 1 ≤ Real.exp (c / 2) / (1 - Real.exp (-(c / 2))) := by
    rw [le_div_iff₀ (by linarith)]
    have : 1 ≤ Real.exp (c / 2) := Real.one_le_exp (by linarith)
    linarith [(Real.exp_pos (-(c / 2))).le]
  refine isOs_one_of_measure_ge_le_mul_exp (by positivity) hK
    (ENNReal.measurable_toReal.comp (measurable_cheapLength a u)).aemeasurable fun x hx => ?_
  rcases hx.eq_or_lt with rfl | hx0
  · refine prob_le_one.trans ?_
    rw [neg_zero, Real.exp_zero, mul_one, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hK
  refine (measure_mono fun ω hω => ?_).trans
    ((measure_ofReal_lt_cheapLength_le hc hcheap u (2 / c * x - 1)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  · simp only [Set.mem_ofPred_eq] at hω ⊢
    have hpos : 0 < (cheapLength a u ω).toReal := lt_of_lt_of_le (by positivity) hω
    have hne : cheapLength a u ω ≠ ⊤ := fun h => by simp [h] at hpos
    rw [← ENNReal.ofReal_toReal hne]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by linarith)
  · have hc' := hc.ne'
    rw [div_mul_eq_mul_div (Real.exp (c / 2)), ← Real.exp_add]
    congr 2
    field_simp
    ring

end CurvatureVariance.Paper.Proofs.Geometry
