/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.Step2Offsets
public import CurvatureVariance.Paper.Proofs.Gain.AVLabels
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Real
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds

/-!
# The offsets for which a tube is not in the subcube of one block

The bound on the event `E` of the proof of Lemma `lem:residual`: for uniform offsets, the
probability that the fine cubes within distance `R_i(j,k)` of the segment from `j` to `k` are not in
the subcube of one block is at most `C(1 + |j − k| + √L)/L`.

* `tubeIndices_mem_box`: the fine cubes within distance `r₀ ≥ 0` of the segment `[j, k]` lie in
  the box `∏_c [min(j_c, k_c) − ⌊r₀⌋, max(j_c, k_c) + ⌊r₀⌋]`.
* `card_offsets_not_subset_tube_le` (**counting bad offsets**): if `|j − k| + 2r₀ ≤ s`, the tube
  `tubeIndices j k r₀` fails to lie in the subcube index set of every block for at most
  `m (s + 2⌈√L⌉) L^{m−1}` of the `L^m` offsets `σ ∈ {0, …, L − 1}^m`
  (from `card_offsets_bad_le`); `card_offsets_not_subset_tube_div_le`: as a fraction,
  `m (s + 2⌈√L⌉)/L`.
* `avg_offsets_not_subset_tube_le`: the average over the `L^m` offsets of one slab of the indicator
  that the tube is not in the subcube of one block is at most `m (s + 2⌈√L⌉)/L`.
-/

@[expose] public section

open Set Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- A coordinate of a point of the segment `[j, k] ⊂ ℝ^{d−1}` lies between those of `j` and `k`. -/
theorem apply_mem_of_mem_segment {j k : Fin m → ℤ} {y : EuclideanSpace ℝ (Fin m)}
    (hy : y ∈ segment ℝ (transversePoint j) (transversePoint k)) (c : Fin m) :
    min ((j c : ℤ) : ℝ) (k c) ≤ y c ∧ y c ≤ max ((j c : ℤ) : ℝ) (k c) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have hy : (a • transversePoint j + b • transversePoint k) c = a * j c + b * k c := by
    simp [transversePoint]
  rw [hy]
  have h1 := min_le_left ((j c : ℤ) : ℝ) (k c)
  have h2 := min_le_right ((j c : ℤ) : ℝ) (k c)
  have h3 := le_max_left ((j c : ℤ) : ℝ) (k c)
  have h4 := le_max_right ((j c : ℤ) : ℝ) (k c)
  have hb' : b = 1 - a := by linarith
  subst hb'
  constructor <;> nlinarith

/-- **The tube lies in a box**: the fine cubes within distance `r₀ ≥ 0` of the segment `[j, k]`
have their `c`-th coordinate in `[min(j_c, k_c) − ⌊r₀⌋, max(j_c, k_c) + ⌊r₀⌋]`. -/
theorem tubeIndices_mem_box {j k : Fin m → ℤ} {r₀ : ℝ} (hr₀ : 0 ≤ r₀) {j' : Fin m → ℤ}
    (hj' : j' ∈ tubeIndices j k (ENNReal.ofReal r₀)) (c : Fin m) :
    min (j c) (k c) - ⌊r₀⌋ ≤ j' c ∧ j' c ≤ max (j c) (k c) + ⌊r₀⌋ := by
  have hd : Metric.infDist (transversePoint j')
      (segment ℝ (transversePoint j) (transversePoint k)) ≤ r₀ :=
    (ENNReal.ofReal_le_ofReal_iff hr₀).1 hj'
  have hne : (segment ℝ (transversePoint j) (transversePoint k)).Nonempty :=
    ⟨_, left_mem_segment ℝ _ _⟩
  -- every point of the segment is within `dist` of `j'` in the coordinate `c`
  have hcoord : ∀ y ∈ segment ℝ (transversePoint j) (transversePoint k),
      |((j' c : ℤ) : ℝ) - y c| ≤ dist (transversePoint j') y := by
    intro y _
    rw [dist_eq_norm]
    have h := PiLp.norm_apply_le (transversePoint j' - y) c
    simpa [transversePoint, Real.norm_eq_abs] using h
  have hlo : min ((j c : ℤ) : ℝ) (k c) - j' c ≤ Metric.infDist (transversePoint j')
      (segment ℝ (transversePoint j) (transversePoint k)) := by
    refine (Metric.le_infDist hne).2 fun y hy => ?_
    have h1 := (apply_mem_of_mem_segment hy c).1
    have h2 := hcoord y hy
    have h3 := neg_abs_le (((j' c : ℤ) : ℝ) - y c)
    linarith
  have hhi : ((j' c : ℤ) : ℝ) - max ((j c : ℤ) : ℝ) (k c) ≤ Metric.infDist (transversePoint j')
      (segment ℝ (transversePoint j) (transversePoint k)) := by
    refine (Metric.le_infDist hne).2 fun y hy => ?_
    have h1 := (apply_mem_of_mem_segment hy c).2
    have h2 := hcoord y hy
    have h3 := le_abs_self (((j' c : ℤ) : ℝ) - y c)
    linarith
  have e1 : (min (j c) (k c) - j' c : ℤ) ≤ ⌊r₀⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  have e2 : (j' c - max (j c) (k c) : ℤ) ≤ ⌊r₀⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  constructor <;> linarith

open Classical in
/-- **Counting bad offsets for a tube** (in the proof of Lemma `lem:residual`): if
`|j − k| + 2r₀ ≤ s`, `r₀ ≥ 0`, the fine cubes within distance `r₀` of the segment `[j, k]` fail to
lie in the subcube index set of every block for at most `m (s + 2⌈√L⌉) L^{m−1}` offsets
`σ ∈ {0, …, L − 1}^m`. -/
theorem card_offsets_not_subset_tube_le {L : ℕ} (hL : 1 ≤ L) (j k : Fin m → ℤ) {r₀ : ℝ}
    (hr₀ : 0 ≤ r₀) {s : ℤ} (hs : ‖transversePoint (j - k)‖ + 2 * r₀ ≤ s) :
    ((({σ : Fin m → Fin L | ¬ ∃ g, tubeIndices j k (ENNReal.ofReal r₀) ⊆
        subIndices L (fun c => ((σ c : ℕ) : ℤ)) g} : Finset (Fin m → Fin L)).card : ℕ) : ℤ) ≤
      m * (s + 2 * ⌈Real.sqrt L⌉₊) * L ^ (m - 1) := by
  have hfl : (⌊r₀⌋ : ℝ) ≤ r₀ := Int.floor_le r₀
  have hfl0 : 0 ≤ ⌊r₀⌋ := Int.floor_nonneg.2 hr₀
  refine card_offsets_bad_le hL (lo := fun c => min (j c) (k c) - ⌊r₀⌋)
    (hi := fun c => max (j c) (k c) + ⌊r₀⌋) (fun j' hj' c => tubeIndices_mem_box hr₀ hj' c)
    (fun c => ?_) (fun c => ?_)
  · have := min_le_max (a := j c) (b := k c)
    linarith
  · have habs : max (j c) (k c) - min (j c) (k c) = |j c - k c| := by
      rw [max_sub_min_eq_abs, abs_sub_comm]
    have hc := Responses.abs_coord_le_norm_transversePoint (j - k) c
    have hreal : ((|j c - k c| + 2 * ⌊r₀⌋ : ℤ) : ℝ) ≤ s := by
      push_cast
      simp only [Pi.sub_apply, Int.cast_sub] at hc
      linarith
    have hint : |j c - k c| + 2 * ⌊r₀⌋ ≤ s := by exact_mod_cast hreal
    linarith

open Classical in
/-- **Counting bad offsets for a tube, as a fraction**: at most `m (s + 2⌈√L⌉)/L` of the `L^m`
offsets are bad. -/
theorem card_offsets_not_subset_tube_div_le {L : ℕ} (hL : 1 ≤ L) (j k : Fin m → ℤ) {r₀ : ℝ}
    (hr₀ : 0 ≤ r₀) {s : ℤ} (hs : ‖transversePoint (j - k)‖ + 2 * r₀ ≤ s) :
    (({σ : Fin m → Fin L | ¬ ∃ g, tubeIndices j k (ENNReal.ofReal r₀) ⊆
        subIndices L (fun c => ((σ c : ℕ) : ℤ)) g} : Finset (Fin m → Fin L)).card : ℝ) /
        (L : ℝ) ^ m ≤
      m * (s + 2 * ⌈Real.sqrt L⌉₊) / L := by
  have h := card_offsets_not_subset_tube_le hL j k hr₀ hs
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hR : (({σ : Fin m → Fin L | ¬ ∃ g, tubeIndices j k (ENNReal.ofReal r₀) ⊆
        subIndices L (fun c => ((σ c : ℕ) : ℤ)) g} : Finset (Fin m → Fin L)).card : ℝ) ≤
      m * (s + 2 * ⌈Real.sqrt L⌉₊) * (L : ℝ) ^ (m - 1) := by
    exact_mod_cast h
  rw [div_le_div_iff₀ (pow_pos hL0 m) hL0]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one] at hR ⊢
    nlinarith [hR, hL0]
  · have hpow : (L : ℝ) ^ m = (L : ℝ) ^ (m - 1) * L := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [hpow]
    calc _ ≤ (m * (s + 2 * ⌈Real.sqrt L⌉₊) * (L : ℝ) ^ (m - 1)) * L :=
          mul_le_mul_of_nonneg_right hR hL0.le
      _ = _ := by ring

open Classical in
/-- The average over the offsets `σ ∈ {0, …, L−1}^m` of one slab of the indicator that the tube
is not in the subcube of one block is at most `m (s + 2⌈√L⌉)/L`. -/
theorem avg_offsets_not_subset_tube_le {L : ℕ} (hL : 1 ≤ L) (j k : Fin m → ℤ) {r₀ : ℝ}
    (hr₀ : 0 ≤ r₀) {s : ℤ} (hs : ‖transversePoint (j - k)‖ + 2 * r₀ ≤ s) :
    ((L : ℝ≥0∞) ^ m)⁻¹ * ∑ σ : Fin m → Fin L,
        (if ∃ g, tubeIndices j k (ENNReal.ofReal r₀) ⊆ subIndices L (fun c => ((σ c : ℕ) : ℤ)) g
          then 0 else 1) ≤
      ENNReal.ofReal (m * (s + 2 * ⌈Real.sqrt L⌉₊) / L) := by
  set bad : Finset (Fin m → Fin L) := {σ : Fin m → Fin L | ¬ ∃ g, tubeIndices j k
    (ENNReal.ofReal r₀) ⊆ subIndices L (fun c => ((σ c : ℕ) : ℤ)) g} with hbad
  have hsum : (∑ σ : Fin m → Fin L,
      (if ∃ g, tubeIndices j k (ENNReal.ofReal r₀) ⊆ subIndices L (fun c => ((σ c : ℕ) : ℤ)) g
        then (0 : ℝ≥0∞) else 1)) = (bad.card : ℝ≥0∞) := by
    rw [hbad, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs <;> simp
  rw [hsum]
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpow : ((L : ℝ≥0∞) ^ m) = ENNReal.ofReal ((L : ℝ) ^ m) := by
    rw [ENNReal.ofReal_pow hL0.le, ENNReal.ofReal_natCast]
  rw [hpow, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (pow_pos hL0 m),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div]
  exact card_offsets_not_subset_tube_div_le hL j k hr₀ hs

end CurvatureVariance.Paper.Gain.LabelResidual
