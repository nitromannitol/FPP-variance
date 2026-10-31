/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.Positivity

/-!
# The counting of translates

An elementary piece of the proof of Lemma `lem:fewtranslates`, **counting translates met by a
tube**: the projection onto the `e₂` axis of the fine cubes within index distance `r` of the
segment `[j, k]` meets at most `2 + (|j − k| + 2r)/L ≤ 3 + |k − j| + 2r` of the translates of a
block by multiples of `L w e₂` (`card_translates_meet_tube_le`).
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Counting the translates of a block met by a tube -/

/-- A point of the segment `[x, y]` of `ℝ^{d−1}` has its coordinates between those of `x` and
`y`. -/
theorem coord_mem_uIcc_of_mem_segment {x y p : EuclideanSpace ℝ (Fin m)}
    (hp : p ∈ segment ℝ x y) (c : Fin m) : p c ∈ uIcc (x c) (y c) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  have h : (a • x + b • y) c = a * x c + b * y c := by simp
  rw [h, mem_uIcc]
  have hb' : a = 1 - b := by linarith
  subst hb'
  rcases le_total (x c) (y c) with hxy | hxy
  · left
    constructor <;> nlinarith [mul_nonneg hb (sub_nonneg.2 hxy), mul_nonneg ha (sub_nonneg.2 hxy)]
  · right
    constructor <;> nlinarith [mul_nonneg hb (sub_nonneg.2 hxy), mul_nonneg ha (sub_nonneg.2 hxy)]

/-- **The projection of a tube**: an index within distance `r` of the segment `[j, k]` has its
coordinate `c` within `r` of the interval between `j c` and `k c`. -/
theorem coord_bounds_of_mem_tubeIndices {j k j' : Fin m → ℤ} {r : ℝ} (hr : 0 ≤ r)
    (hj' : j' ∈ tubeIndices j k (ENNReal.ofReal r)) (c : Fin m) :
    min (j c : ℝ) (k c) - r ≤ j' c ∧ (j' c : ℝ) ≤ max (j c : ℝ) (k c) + r := by
  have hd : Metric.infDist (transversePoint j')
      (segment ℝ (transversePoint j) (transversePoint k)) ≤ r :=
    (ENNReal.ofReal_le_ofReal_iff hr).1 hj'
  have hne : (segment ℝ (transversePoint j) (transversePoint k)).Nonempty :=
    ⟨_, left_mem_segment ℝ _ _⟩
  have key : ∀ ε > 0, min (j c : ℝ) (k c) - r - ε < j' c ∧
      (j' c : ℝ) < max (j c : ℝ) (k c) + r + ε := by
    intro ε hε
    obtain ⟨p, hp, hdp⟩ := (Metric.infDist_lt_iff hne).1 (show _ < r + ε by linarith)
    have hpc := coord_mem_uIcc_of_mem_segment hp c
    have hcoord : |(transversePoint j' c) - p c| ≤ dist (transversePoint j') p := by
      rw [EuclideanSpace.dist_eq]
      have h1 : |(transversePoint j' c) - p c| = Real.sqrt (((transversePoint j' c) - p c) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      rw [h1]
      refine Real.sqrt_le_sqrt ?_
      have h2 : ((transversePoint j' c) - p c) ^ 2 = dist (transversePoint j' c) (p c) ^ 2 := by
        rw [Real.dist_eq, sq_abs]
      rw [h2]
      exact Finset.single_le_sum (f := fun i => dist (transversePoint j' i) (p i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ c)
    have hj'c : transversePoint j' c = (j' c : ℝ) := rfl
    have hjc : transversePoint j c = (j c : ℝ) := rfl
    have hkc : transversePoint k c = (k c : ℝ) := rfl
    rw [hj'c] at hcoord
    rw [mem_uIcc, hjc, hkc] at hpc
    have habs := abs_lt.1 (hcoord.trans_lt hdp)
    rcases hpc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor
      · linarith [min_le_left (j c : ℝ) (k c)]
      · linarith [le_max_right (j c : ℝ) (k c)]
    · constructor
      · linarith [min_le_right (j c : ℝ) (k c)]
      · linarith [le_max_left (j c : ℝ) (k c)]
  constructor
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    linarith [(key ε hε).1]
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    linarith [(key ε hε).2]

/-- The integers `s` with `α < L s ≤ β` number at most `(β − α)/L + 1`. -/
theorem card_filter_mul_mem_Ioc_le {L : ℕ} (hL : 1 ≤ L) {α β : ℝ} (hαβ : α ≤ β) (S : Finset ℤ)
    (hS : ∀ s ∈ S, α < (L : ℝ) * s ∧ (L : ℝ) * s ≤ β) :
    (S.card : ℝ) ≤ (β - α) / L + 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hsub : S ⊆ Finset.Ioc ⌊α / L⌋ ⌊β / L⌋ := by
    intro s hs
    obtain ⟨h1, h2⟩ := hS s hs
    rw [Finset.mem_Ioc]
    constructor
    · rw [Int.floor_lt, div_lt_iff₀ hL0]
      linarith
    · rw [Int.le_floor, le_div_iff₀ hL0]
      linarith
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Ioc] at hcard
  have h1 : ((S.card : ℕ) : ℝ) ≤ ((⌊β / L⌋ - ⌊α / L⌋).toNat : ℝ) := by exact_mod_cast hcard
  have h2 : ((⌊β / L⌋ - ⌊α / L⌋).toNat : ℝ) ≤ max ((⌊β / L⌋ : ℝ) - ⌊α / L⌋) 0 := by
    rcases le_total 0 (⌊β / L⌋ - ⌊α / L⌋) with h | h
    · have e : (((⌊β / L⌋ - ⌊α / L⌋).toNat : ℕ) : ℝ) = ((⌊β / L⌋ - ⌊α / L⌋ : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
      rw [e]
      push_cast
      exact le_max_left _ _
    · rw [Int.toNat_eq_zero.2 h]
      simp
  have h3 : (⌊β / L⌋ : ℝ) ≤ β / L := Int.floor_le _
  have h4 : α / L - 1 < (⌊α / L⌋ : ℝ) := Int.sub_one_lt_floor _
  have h5 : (β - α) / L = β / L - α / L := sub_div _ _ _
  refine h1.trans (h2.trans (max_le ?_ ?_))
  · linarith
  · have : 0 ≤ (β - α) / L := div_nonneg (by linarith) hL0.le
    linarith

open Classical in
/-- **Counting translates** (the proof of Lemma `lem:fewtranslates`): the tube
`tubeIndices j k r` meets at most `3 + |k − j| + 2r` of the index boxes
`L (g − v e₂) + o + {0, …, L−1}^{d−1}`, `0 ≤ v < V`, of the translates of a block by multiples of
`L w e₂` (sharper: `2 + (|k − j| + 2r)/L`). -/
theorem card_translates_meet_tube_le (hm : 1 ≤ m) {L : ℕ} (hL : 1 ≤ L) (o g j k : Fin m → ℤ)
    (r : ℝ≥0∞) (V : ℕ) :
    (({v ∈ Finset.range V | ∃ j' ∈ tubeIndices j k r, ∀ c : Fin m,
        (L : ℤ) * (g - ((v : ℕ) : ℤ) • transverseUnit m) c + o c ≤ j' c ∧
          j' c < (L : ℤ) * (g - ((v : ℕ) : ℤ) • transverseUnit m) c + o c + L}).card : ℝ≥0∞) ≤
      3 + ENNReal.ofReal ‖transversePoint (k - j)‖ + 2 * r := by
  rcases eq_or_ne r ⊤ with hr | hr
  · simp [hr]
  set r₀ := r.toReal with hr₀
  have hr0 : 0 ≤ r₀ := ENNReal.toReal_nonneg
  have hrr : r = ENNReal.ofReal r₀ := (ENNReal.ofReal_toReal hr).symm
  set c₀ : Fin m := ⟨0, hm⟩
  set lo : ℝ := min (j c₀ : ℝ) (k c₀)
  set hi : ℝ := max (j c₀ : ℝ) (k c₀)
  set Sv := {v ∈ Finset.range V | ∃ j' ∈ tubeIndices j k r, ∀ c : Fin m,
        (L : ℤ) * (g - ((v : ℕ) : ℤ) • transverseUnit m) c + o c ≤ j' c ∧
          j' c < (L : ℤ) * (g - ((v : ℕ) : ℤ) • transverseUnit m) c + o c + L}
  -- the integers `s = g c₀ − v`
  have hinj : Set.InjOn (fun v : ℕ => g c₀ - (v : ℤ)) (Sv : Set ℕ) := by
    intro v _ v' _ h
    simp only [sub_right_inj, Nat.cast_inj] at h
    exact h
  have hcardS : (Sv.image fun v : ℕ => g c₀ - (v : ℤ)).card = Sv.card :=
    Finset.card_image_of_injOn hinj
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlohi : lo ≤ hi := min_le_max
  have hbound := card_filter_mul_mem_Ioc_le hL (α := lo - r₀ - o c₀ - L) (β := hi + r₀ - o c₀)
    (by linarith)
    (Sv.image fun v : ℕ => g c₀ - (v : ℤ)) (by
      intro s hs
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨-, j', hj', hbox⟩ := Finset.mem_filter.1 hv
      have hproj := coord_bounds_of_mem_tubeIndices hr0 (hrr ▸ hj') c₀
      obtain ⟨h1, h2⟩ := hbox c₀
      have hunit : ((v : ℤ) • transverseUnit m) c₀ = v := by
        simp [transverseUnit, c₀]
      simp only [Pi.sub_apply, hunit] at h1 h2
      have h1' : (L : ℝ) * ((g c₀ : ℝ) - v) + o c₀ ≤ j' c₀ := by exact_mod_cast h1
      have h2' : (j' c₀ : ℝ) < (L : ℝ) * ((g c₀ : ℝ) - v) + o c₀ + L := by exact_mod_cast h2
      push_cast
      constructor <;> linarith [hproj.1, hproj.2])
  rw [hcardS] at hbound
  have hkj : |((k c₀ : ℝ) - j c₀)| ≤ ‖transversePoint (k - j)‖ := by
    have hc : transversePoint (k - j) c₀ = (k c₀ : ℝ) - j c₀ := by
      simp [transversePoint]
    rw [← hc, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le _ _
  have hhilo : hi - lo ≤ ‖transversePoint (k - j)‖ := by
    have h := abs_le.1 hkj
    simp only [hi, lo]
    rcases le_total (j c₀ : ℝ) (k c₀) with h' | h'
    · rw [max_eq_right h', min_eq_left h']
      linarith [h.2]
    · rw [max_eq_left h', min_eq_right h']
      linarith [h.1]
  have hnum : 0 ≤ hi - lo + 2 * r₀ := by
    have : lo ≤ hi := min_le_max
    linarith
  have hfrac : ((hi + r₀ - o c₀) - (lo - r₀ - o c₀ - L)) / L ≤ hi - lo + 2 * r₀ + 1 := by
    rw [div_le_iff₀ hL0]
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  have hreal : (Sv.card : ℝ) ≤ 3 + ‖transversePoint (k - j)‖ + 2 * r₀ := by linarith
  calc ((Sv.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal (Sv.card : ℝ) := by simp
    _ ≤ ENNReal.ofReal (3 + ‖transversePoint (k - j)‖ + 2 * r₀) := ENNReal.ofReal_le_ofReal hreal
    _ = 3 + ENNReal.ofReal ‖transversePoint (k - j)‖ + 2 * r := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by norm_num) (norm_nonneg _), hrr, ENNReal.ofReal_mul (by norm_num)]
      norm_num

end CurvatureVariance.Paper.Gain
