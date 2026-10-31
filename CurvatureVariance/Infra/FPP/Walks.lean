/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.Lattice
public import CurvatureVariance.Statements.Lattice.Config
public import CurvatureVariance.Statements.Lattice.WalkCost
public import CurvatureVariance.Statements.Lattice.PassageTime
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic.Linarith
import CurvatureVariance.Infra.Kesten.Deterministic

/-!
# Walks, costs and passage times on `ℤ^d`

For `walkCost` and `passageTime` on the lattice graph:

* walk costs: concatenation, reversal, loop deletion (with zero weights allowed), locality;
* the passage time: the bound by every walk cost, symmetry, the triangle inequality, approximation
  by walk costs;
* measurability in the configuration (walks between two vertices form a countable type);
* the displacement bound `‖point u - point v‖ ≤ length`;
* the `ℓ¹` distance `l1Dist`: every walk is at least that long, and a coordinate path realizes it;
* at most `(2d)^k` walks of length `k` from a vertex.

Weights may vanish, so a geodesic need not be a path; loop deletion (`walkCost_toPath_le`) turns
a walk into a path of no larger cost.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ} (ω : Config m) {u v w : Vertex m}

/-! ### Costs -/

@[simp] theorem walkCost_cons (h : (latticeGraph m).Adj u v) (p : (latticeGraph m).Walk v w) :
    walkCost ω (p.cons h) = ω ⟨s(u, v), h⟩ + walkCost ω p := rfl

/-- Concatenation adds costs. -/
@[simp] theorem walkCost_append (p : (latticeGraph m).Walk u v) (q : (latticeGraph m).Walk v w) :
    walkCost ω (p.append q) = walkCost ω p + walkCost ω q := by
  simp only [walkCost, SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]

/-- Reversal preserves cost because edge weights are unoriented. -/
@[simp] theorem walkCost_reverse (p : (latticeGraph m).Walk u v) :
    walkCost ω p.reverse = walkCost ω p := by
  simp [walkCost, SimpleGraph.Walk.darts_reverse, List.map_map, Function.comp_def]

/-- Bypassing repeated vertices cannot increase cost. -/
theorem walkCost_bypass_le (p : (latticeGraph m).Walk u v) : walkCost ω p.bypass ≤ walkCost ω p :=
  Kesten.walkCost_le_of_darts_sublist ω _ _ p.darts_bypass_sublist_darts

/-- Deleting loops cannot increase a cost (zero weights allowed). -/
theorem walkCost_toPath_le (p : (latticeGraph m).Walk u v) :
    walkCost ω (p.toPath : (latticeGraph m).Walk u v) ≤ walkCost ω p :=
  walkCost_bypass_le ω p

/-- A cost depends only on the weights of the traversed edges. -/
theorem walkCost_congr (p : (latticeGraph m).Walk u v) {ω' : Config m}
    (h : ∀ e : Edge m, e.1 ∈ p.edges → ω e = ω' e) : walkCost ω p = walkCost ω' p := by
  unfold walkCost
  congr 1
  refine List.map_congr_left fun t ht => h _ ?_
  exact List.mem_map_of_mem ht

/-! ### The passage time -/

/-- The passage time is at most the cost of every walk. -/
theorem passageTime_le_walkCost (p : (latticeGraph m).Walk u v) :
    passageTime ω u v ≤ walkCost ω p :=
  ciInf_le (OrderBot.bddBelow _) p

/-- `T(u, u) = 0`. -/
@[simp] theorem passageTime_self (u : Vertex m) : passageTime ω u u = 0 :=
  le_antisymm (passageTime_le_walkCost ω (.nil : (latticeGraph m).Walk u u)) bot_le

/-- The passage time is approached by walk costs. -/
theorem exists_walkCost_lt (u v : Vertex m) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ p : (latticeGraph m).Walk u v, walkCost ω p < passageTime ω u v + ε := by
  have : Nonempty ((latticeGraph m).Walk u v) := nonempty_walk u v
  exact exists_lt_of_ciInf_lt (lt_add_of_pos_right _ hε)

/-- The passage time is symmetric. -/
theorem passageTime_symm (u v : Vertex m) : passageTime ω u v = passageTime ω v u := by
  have : Nonempty ((latticeGraph m).Walk u v) := nonempty_walk u v
  have : Nonempty ((latticeGraph m).Walk v u) := nonempty_walk v u
  apply le_antisymm
  · exact le_ciInf fun p => by simpa using passageTime_le_walkCost ω p.reverse
  · exact le_ciInf fun p => by simpa using passageTime_le_walkCost ω p.reverse

/-- The triangle inequality for the passage time. -/
theorem passageTime_triangle (u v w : Vertex m) :
    passageTime ω u w ≤ passageTime ω u v + passageTime ω v w := by
  have : Nonempty ((latticeGraph m).Walk u v) := nonempty_walk u v
  have : Nonempty ((latticeGraph m).Walk v w) := nonempty_walk v w
  unfold passageTime
  refine NNReal.le_iInf_add_iInf fun p q => ?_
  rw [← walkCost_append]
  exact ciInf_le (OrderBot.bddBelow _) _

/-- Moving the endpoints changes the passage time by at most the connecting passage times. -/
theorem abs_passageTime_sub_le (u v u' v' : Vertex m) :
    |(passageTime ω u v : ℝ) - passageTime ω u' v'| ≤
      passageTime ω u u' + passageTime ω v v' := by
  have h₁ := passageTime_triangle ω u u' v
  have h₂ := passageTime_triangle ω u' v' v
  have h₃ := passageTime_triangle ω u' u v'
  have h₄ := passageTime_triangle ω u v v'
  rw [passageTime_symm ω v' v] at h₂
  rw [passageTime_symm ω u' u] at h₃
  have k₁ := NNReal.coe_le_coe.mpr h₁
  have k₂ := NNReal.coe_le_coe.mpr h₂
  have k₃ := NNReal.coe_le_coe.mpr h₃
  have k₄ := NNReal.coe_le_coe.mpr h₄
  simp only [NNReal.coe_add] at k₁ k₂ k₃ k₄
  exact abs_le.mpr ⟨by linarith only [k₃, k₄], by linarith only [k₁, k₂]⟩

/-! ### Measurability -/

/-- The cost of a fixed walk is measurable in the configuration. -/
theorem measurable_walkCost (p : (latticeGraph m).Walk u v) :
    Measurable fun ω : Config m => walkCost ω p := by
  induction p with
  | nil => exact measurable_const
  | cons h p ih =>
    simp only [walkCost_cons]
    exact (measurable_pi_apply _).add ih

/-- The passage time between two fixed vertices is measurable (a countable infimum). -/
theorem measurable_passageTime (u v : Vertex m) :
    Measurable fun ω : Config m => passageTime ω u v :=
  Measurable.iInf fun p => measurable_walkCost p

/-- The passage time between two fixed vertices is measurable, as a real number. -/
theorem measurable_passageTime_real (u v : Vertex m) :
    Measurable fun ω : Config m => (passageTime ω u v : ℝ) :=
  (measurable_passageTime u v).coe_nnreal_real

/-! ### Displacement -/

/-- A walk is at least as long as the Euclidean distance between its endpoints. -/
theorem norm_point_sub_le_length (p : (latticeGraph m).Walk u v) :
    ‖point u - point v‖ ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have htri := norm_sub_le_norm_sub_add_norm_sub (point a) (point b) (point c)
    have hedge := (norm_point_sub_point_of_adj h).le
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    linarith only [htri, hedge, ih]

/-- A vertex of a walk is within its number of edges of the start. -/
theorem norm_point_sub_le_length_of_mem (p : (latticeGraph m).Walk u v)
    {z : Vertex m} (hz : z ∈ p.support) : ‖point z - point u‖ ≤ p.length := by
  classical
  have h1 := norm_point_sub_le_length (p.takeUntil z hz)
  have h2 := SimpleGraph.Walk.length_takeUntil_le_length p hz
  rw [norm_sub_rev] at h1
  exact h1.trans (by exact_mod_cast h2)

/-! ### The `ℓ¹` distance -/

/-- The `ℓ¹` distance `|u - v|₁` of two vertices. -/
def l1Dist {m : ℕ} (u v : Vertex m) : ℕ := (u.1 - v.1).natAbs + ∑ j, (u.2 j - v.2 j).natAbs

/-- The `ℓ¹` distance, as an integer. -/
theorem l1Dist_eq {m : ℕ} (u v : Vertex m) :
    (l1Dist u v : ℤ) = |u.1 - v.1| + ∑ j, |u.2 j - v.2 j| := by
  simp [l1Dist]

theorem l1Dist_comm {m : ℕ} (u v : Vertex m) : l1Dist u v = l1Dist v u := by
  simp only [l1Dist, ← Int.natAbs_neg (u.1 - v.1), neg_sub]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [← Int.natAbs_neg, neg_sub]

/-! ### Coordinate walks -/

/-- A longitudinal walk from `x` to `x + (n, 0)` of length `n`. -/
theorem exists_longitudinal_walk_nat (x : Vertex m) (n : ℕ) :
    ∃ p : (latticeGraph m).Walk x (x + ((n : ℤ), 0)), p.length = n ∧
      ∀ y ∈ p.support, y.2 = x.2 ∧ x.1 ≤ y.1 ∧ y.1 ≤ x.1 + n := by
  induction n with
  | zero => exact ⟨(SimpleGraph.Walk.nil).copy rfl (by simp), by simp, by simp⟩
  | succ n ih =>
    obtain ⟨p, hl, hs⟩ := ih
    have hadj := latticeGraph_adj_add_longitudinal (x + ((n : ℤ), 0))
    have heq : x + ((n : ℤ), 0) + (1, 0) = x + (((n + 1 : ℕ) : ℤ), 0) := by
      ext <;> simp [add_assoc]
    refine ⟨(p.concat hadj).copy rfl heq, by simp [hl], fun y hy => ?_⟩
    simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat,
      List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · have := hs y hy
      exact ⟨this.1, this.2.1, by push_cast; linarith [this.2.2]⟩
    · simp only [Prod.fst_add, Prod.snd_add, add_zero]
      refine ⟨trivial, by omega, by push_cast; linarith⟩

/-- A longitudinal walk from `x` to `(a, x.2)`. -/
theorem exists_longitudinal_walk (x : Vertex m) (a : ℤ) :
    ∃ p : (latticeGraph m).Walk x (a, x.2), (p.length : ℤ) = |x.1 - a| ∧
      ∀ y ∈ p.support, y.2 = x.2 ∧ min x.1 a ≤ y.1 ∧ y.1 ≤ max x.1 a := by
  rcases le_or_gt x.1 a with h | h
  · obtain ⟨p, hl, hs⟩ := exists_longitudinal_walk_nat x (a - x.1).toNat
    have heq : x + ((((a - x.1).toNat : ℕ) : ℤ), 0) = (a, x.2) := by
      ext <;> simp [Int.toNat_of_nonneg (sub_nonneg.2 h)]
    refine ⟨p.copy rfl heq, ?_, fun y hy => ?_⟩
    · rw [SimpleGraph.Walk.length_copy, hl, abs_of_nonpos (by omega)]; omega
    · rw [SimpleGraph.Walk.support_copy] at hy
      have := hs y hy
      refine ⟨this.1, by omega, by omega⟩
  · obtain ⟨p, hl, hs⟩ := exists_longitudinal_walk_nat ((a, x.2) : Vertex m) (x.1 - a).toNat
    have heq : ((a, x.2) : Vertex m) + ((((x.1 - a).toNat : ℕ) : ℤ), 0) = x := by
      ext <;> simp [Int.toNat_of_nonneg (sub_nonneg.2 h.le)]
    refine ⟨(p.copy rfl heq).reverse, ?_, fun y hy => ?_⟩
    · rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_copy, hl, abs_of_pos (by omega)]
      omega
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_copy] at hy
      have := hs y hy
      refine ⟨this.1, by simp only at this; omega, by simp only at this; omega⟩

private theorem sum_abs_step {b u w : Fin m → ℤ} {j : Fin m} (hj : |w j - b j| + 1 = |u j - b j|)
    (hw : ∀ i, i ≠ j → w i = u i) :
    ∑ i, |w i - b i| + 1 = ∑ i, |u i - b i| := by
  have h : ∑ i, (|u i - b i| - |w i - b i|) = 1 := by
    rw [Finset.sum_eq_single j]
    · linarith
    · intro i _ hi; rw [hw i hi]; ring
    · simp
  rw [Finset.sum_sub_distrib] at h
  linarith

/-- A transverse walk from `x` to `(x.1, b)`, at constant longitudinal level. -/
theorem exists_transverse_walk (b : Fin m → ℤ) :
    ∀ (N : ℕ) (x : Vertex m), ∑ j, |x.2 j - b j| = (N : ℤ) →
    ∃ p : (latticeGraph m).Walk x (x.1, b), (p.length : ℤ) = N ∧ ∀ y ∈ p.support, y.1 = x.1 := by
  intro N
  induction N with
  | zero =>
    intro x hx
    have hxb : x.2 = b := by
      funext j
      have h0 : ∀ i ∈ Finset.univ, |x.2 i - b i| = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)).1 (by simpa using hx)
      have := h0 j (Finset.mem_univ j)
      rw [abs_eq_zero] at this; omega
    have heq : x = (x.1, b) := Prod.ext rfl hxb
    exact ⟨(SimpleGraph.Walk.nil).copy rfl heq, by simp, by simp⟩
  | succ N ih =>
    intro x hx
    have hne : ∃ j, x.2 j ≠ b j := by
      by_contra hcon
      push Not at hcon
      simp [hcon] at hx
      omega
    obtain ⟨j, hj⟩ := hne
    have key : ∀ x' : Vertex m, (latticeGraph m).Adj x x' → x'.1 = x.1 →
        ∑ i, |x'.2 i - b i| = (N : ℤ) →
        ∃ p : (latticeGraph m).Walk x (x.1, b), (p.length : ℤ) = ((N + 1 : ℕ) : ℤ) ∧
          ∀ y ∈ p.support, y.1 = x.1 := by
      intro x' hadj h1 hs
      obtain ⟨p, hl, hsup⟩ := ih x' hs
      have heq : (x'.1, b) = (x.1, b) := by rw [h1]
      refine ⟨(SimpleGraph.Walk.cons hadj p).copy rfl heq, by simp [hl], fun y hy => ?_⟩
      rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · rfl
      · rw [hsup y hy, h1]
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · refine key (x + (0, Pi.single j 1)) (latticeGraph_adj_add_transverse x j) (by simp) ?_
      have := sum_abs_step (b := b) (u := x.2) (w := (x + (0, Pi.single j 1)).2) (j := j)
        (by simp only [Prod.snd_add, Pi.add_apply, Pi.single_eq_same]
            rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]; ring)
        (fun i hi => by simp [hi])
      omega
    · refine key (x - (0, Pi.single j 1)) (latticeGraph_adj_sub_transverse x j) (by simp) ?_
      have := sum_abs_step (b := b) (u := x.2) (w := (x - (0, Pi.single j 1)).2) (j := j)
        (by simp only [Prod.snd_sub, Pi.sub_apply, Pi.single_eq_same]
            rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]; ring)
        (fun i hi => by simp [hi])
      omega

/-- The coordinate route from `u` to `v`: longitudinal first, then transverse. -/
theorem exists_coordinate_walk (u v : Vertex m) :
    ∃ p : (latticeGraph m).Walk u v,
      (p.length : ℤ) = |u.1 - v.1| + ∑ j, |u.2 j - v.2 j| ∧
      ∀ y ∈ p.support, min u.1 v.1 ≤ y.1 ∧ y.1 ≤ max u.1 v.1 := by
  obtain ⟨p, hl, hs⟩ := exists_longitudinal_walk u v.1
  have hnn : 0 ≤ ∑ j, |u.2 j - v.2 j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨q, hl2, hs2⟩ :=
    exists_transverse_walk v.2 (∑ j, |u.2 j - v.2 j|).toNat ((v.1, u.2) : Vertex m)
    (by simpa using (Int.toNat_of_nonneg hnn).symm)
  refine ⟨p.append q, ?_, fun y hy => ?_⟩
  · rw [SimpleGraph.Walk.length_append]; push_cast
    rw [hl, hl2, Int.toNat_of_nonneg hnn]
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hy
    rcases hy with hy | hy
    · exact (hs y hy).2
    · rw [hs2 y hy]
      exact ⟨by simp, by simp⟩

/-! ### Walks and the `ℓ¹` distance -/


/-- The triangle inequality for the `ℓ¹` distance. -/
theorem l1Dist_triangle (u v w : Vertex m) : l1Dist u w ≤ l1Dist u v + l1Dist v w := by
  have h1 : (u.1 - w.1).natAbs ≤ (u.1 - v.1).natAbs + (v.1 - w.1).natAbs := by
    have := Int.natAbs_add_le (u.1 - v.1) (v.1 - w.1)
    rwa [sub_add_sub_cancel] at this
  have h2 : ∑ j, (u.2 j - w.2 j).natAbs ≤
      ∑ j, (u.2 j - v.2 j).natAbs + ∑ j, (v.2 j - w.2 j).natAbs := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := Int.natAbs_add_le (u.2 j - v.2 j) (v.2 j - w.2 j)
    rwa [sub_add_sub_cancel] at this
  unfold l1Dist
  omega

/-- A vertex is at `ℓ¹` distance zero from itself. -/
@[simp] theorem l1Dist_self (u : Vertex m) : l1Dist u u = 0 := by simp [l1Dist]

/-- Adjacent vertices are at `ℓ¹` distance one. -/
theorem l1Dist_of_adj {x y : Vertex m} (h : (latticeGraph m).Adj x y) : l1Dist x y = 1 := by
  rw [l1Dist_comm]
  have hd : l1Dist y x = (y - x).1.natAbs + ∑ j, ((y - x).2 j).natAbs := by simp [l1Dist]
  rw [hd]
  rcases latticeGraph_adj_iff_sub.1 h with h | h | ⟨j, h | h⟩ <;> rw [h]
  · simp
  · simp
  · simp [Pi.single_apply, apply_ite Int.natAbs]
  · simp [Pi.single_apply, apply_ite Int.natAbs]

/-- Every walk is at least as long as the `ℓ¹` distance of its endpoints. -/
theorem l1Dist_le_length {m : ℕ} {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    l1Dist u v ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    rename_i a b c
    have h1 := l1Dist_triangle a b c
    rw [l1Dist_of_adj h] at h1
    omega

/-- A coordinate path realizes the `ℓ¹` distance. -/
theorem exists_isPath_length_eq_l1Dist {m : ℕ} (u v : Vertex m) :
    ∃ p : (latticeGraph m).Walk u v, p.IsPath ∧ p.length = l1Dist u v := by
  classical
  obtain ⟨p, hl, -⟩ := exists_coordinate_walk u v
  have hl' : p.length = l1Dist u v := by
    have := l1Dist_eq u v
    omega
  refine ⟨p.bypass, p.bypass_isPath, le_antisymm ?_ (l1Dist_le_length _)⟩
  exact hl' ▸ p.length_bypass_le_length

end CurvatureVariance.Infra.FPP
