/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanDefs
import Mathlib.Tactic.Linarith

/-!
# Skeletons of lattice walks

Deterministic combinatorics of lattice walks used in the mean bound:

* `exists_skeleton`: a walk at scale `R` is cut at the successive first exits from balls of
  radius `R`, giving at most `max p.length 1` skeleton steps of length in `[R, R + 1]` (except the
  last), whose passage times sum to at most the cost of the walk;
* `sum_walkEdges`, `card_walkEdges_le`, `walkEdges_subset_edgesNear`: the edge set
  of a walk;
* `card_latticeBall_le`: `#(lattice ball of radius R) ≤ (2R + 1)^(m+1)`.
-/

@[expose] public section

open scoped NNReal

namespace CurvatureVariance.Infra.FPP

open SimpleGraph

variable {m : ℕ}

/-- Cost splits along `take`/`drop`. -/
theorem walkCost_take_add_drop (ω : Config m) {u v : Vertex m} (p : (latticeGraph m).Walk u v)
    (n : ℕ) : walkCost ω (p.take n) + walkCost ω (p.drop n) = walkCost ω p := by
  unfold walkCost
  rw [Walk.darts_take, Walk.darts_drop, ← List.sum_append, ← List.map_append,
    List.take_append_drop]

private theorem skeleton_aux (R : ℝ) (hR : 0 ≤ R) : ∀ (N : ℕ) {u w : Vertex m}
    (p : (latticeGraph m).Walk u w), p.length = N →
    ∃ (q : ℕ) (v : ℕ → Vertex m), 0 < q ∧ q ≤ max p.length 1 ∧ v 0 = u ∧ v q = w ∧
      (∀ i < q, ‖point (v (i + 1)) - point (v i)‖ ≤ R + 1) ∧
      (∀ i, i + 1 < q → R ≤ ‖point (v (i + 1)) - point (v i)‖) ∧
      ∀ ω : Config m, ∑ i ∈ Finset.range q, (passageTime ω (v i) (v (i + 1)) : ℝ) ≤
        walkCost ω p := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro u w p hN
  by_cases hex : ∃ n, 0 < n ∧ n ≤ p.length ∧ R ≤ ‖point (p.getVert n) - point u‖
  · set n₀ := Nat.find hex with hn₀
    obtain ⟨h0, hle, hR0⟩ := Nat.find_spec hex
    have hdist : ‖point (p.getVert n₀) - point u‖ ≤ R + 1 := by
      obtain ⟨y, hy, hyd⟩ : ∃ y, (latticeGraph m).Adj y (p.getVert n₀) ∧
          ‖point y - point u‖ ≤ R := by
        refine ⟨p.getVert (n₀ - 1), ?_, ?_⟩
        · have := p.adj_getVert_succ (i := n₀ - 1) (by omega)
          rwa [Nat.sub_add_cancel h0] at this
        · by_cases h1 : n₀ - 1 = 0
          · rw [h1, Walk.getVert_zero]; simpa using hR
          · have := Nat.find_min hex (m := n₀ - 1) (by omega)
            by_contra hc
            exact this ⟨by omega, by omega, (not_le.1 hc).le⟩
      calc ‖point (p.getVert n₀) - point u‖
          = ‖(point (p.getVert n₀) - point y) + (point y - point u)‖ := by congr 1; abel
        _ ≤ ‖point (p.getVert n₀) - point y‖ + ‖point y - point u‖ := norm_add_le _ _
        _ ≤ 1 + R := add_le_add (by
            rw [norm_sub_rev]; exact (norm_point_sub_point_of_adj hy).le) hyd
        _ = R + 1 := add_comm _ _
    have hcost := fun ω : Config m => walkCost_take_add_drop ω p n₀
    have hT : ∀ ω : Config m, (passageTime ω u (p.getVert n₀) : ℝ) +
        walkCost ω (p.drop n₀) ≤ walkCost ω p := fun ω => by
      have h1 := passageTime_le_walkCost ω (p.take n₀)
      have h2 := hcost ω
      have : (passageTime ω u (p.getVert n₀) : ℝ) ≤ walkCost ω (p.take n₀) := by exact_mod_cast h1
      have h3 : ((walkCost ω (p.take n₀) + walkCost ω (p.drop n₀) : ℝ≥0) : ℝ) =
        walkCost ω p := by exact_mod_cast h2
      push_cast at h3
      linarith only [this, h3]
    have hw : n₀ = p.length → p.getVert n₀ = w := fun h => by rw [h]; exact p.getVert_length
    by_cases hend : n₀ = p.length
    · refine ⟨1, fun i => if i = 0 then u else w, one_pos, le_max_right _ _, by simp, by simp,
        ?_, fun i hi => by omega, ?_⟩
      · intro i hi
        obtain rfl : i = 0 := by omega
        simpa [hw hend] using hdist
      · intro ω
        rw [Finset.sum_range_one]
        show ((passageTime ω u w : ℝ≥0) : ℝ) ≤ _
        have h1 : (passageTime ω u (p.getVert n₀) : ℝ) + walkCost ω (p.drop n₀) ≤
            walkCost ω p := hT ω
        have e : passageTime ω u (p.getVert n₀) = passageTime ω u w := by rw [hw hend]
        rw [e] at h1
        have := (walkCost ω (p.drop n₀)).coe_nonneg
        linarith only [h1, this]
    · have hlt : (p.drop n₀).length < N := by
        rw [Walk.drop_length]; omega
      obtain ⟨q, v, hq, hqle, hv0, hvq, hstep, hmid, hsum⟩ := ih _ hlt (p.drop n₀) rfl
      have hdl : (p.drop n₀).length = p.length - n₀ := Walk.drop_length _ _
      refine ⟨q + 1, fun i => if i = 0 then u else v (i - 1), by omega, ?_, by simp, ?_, ?_, ?_, ?_⟩
      · rw [hdl] at hqle; omega
      · simpa using hvq
      · intro i hi
        rcases i with _ | i
        · simpa [hv0] using hdist
        · simpa using hstep i (by omega)
      · intro i hi
        rcases i with _ | i
        · simpa [hv0] using hR0
        · simpa using hmid i (by omega)
      · intro ω
        rw [Finset.sum_range_succ']
        have h1 := hsum ω
        have h2 := hT ω
        simp only [Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false, ite_false, ite_true,
          hv0]
        linarith only [h1, h2]
  · refine ⟨1, fun i => if i = 0 then u else w, one_pos, le_max_right _ _, by simp, by simp,
      ?_, fun i hi => by omega, ?_⟩
    · intro i hi
      obtain rfl : i = 0 := by omega
      push Not at hex
      by_cases hl : p.length = 0
      · obtain rfl := Walk.eq_of_length_eq_zero hl
        simpa using hR.trans (by linarith only [hR])
      · have := hex p.length (by omega) le_rfl
        rw [p.getVert_length] at this
        simpa using (this.le.trans (by linarith only : R ≤ R + 1))
    · intro ω
      simpa using passageTime_le_walkCost ω p

/-- **Skeleton of a walk at scale `R`**: the walk is cut at successive first exits from balls of
radius `R`; the skeleton has at most `max p.length 1` steps, each of length at most `R + 1`, all but
the last of length at least `R`, and the passage times along it sum to at most the cost of `p`. -/
theorem exists_skeleton {u w : Vertex m} (p : (latticeGraph m).Walk u w) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (q : ℕ) (v : ℕ → Vertex m), 0 < q ∧ q ≤ max p.length 1 ∧ v 0 = u ∧ v q = w ∧
      (∀ i < q, ‖point (v (i + 1)) - point (v i)‖ ≤ R + 1) ∧
      (∀ i, i + 1 < q → R ≤ ‖point (v (i + 1)) - point (v i)‖) ∧
      ∀ ω : Config m, ∑ i ∈ Finset.range q, (passageTime ω (v i) (v (i + 1)) : ℝ) ≤
        walkCost ω p :=
  skeleton_aux R hR _ p rfl

/-- The edges of a walk, with weights, as a list of lattice edges. -/
private theorem walkEdges_eq {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    walkEdges p =
      (p.darts.map fun t => (⟨t.edge, t.edge_mem⟩ : Edge m)).toFinset := by
  ext e
  rw [mem_walkEdges, List.mem_toFinset, List.mem_map, Walk.edges, List.mem_map]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, Subtype.ext h⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-- For a walk without repeated edges the cost is the sum of the weights over its edge set. -/
theorem sum_walkEdges {u v : Vertex m} {p : (latticeGraph m).Walk u v} (hp : p.edges.Nodup)
    (ω : Config m) : ∑ e ∈ walkEdges p, (ω e : ℝ) = walkCost ω p := by
  have hnd : (p.darts.map fun t => (⟨t.edge, t.edge_mem⟩ : Edge m)).Nodup := by
    refine List.Nodup.of_map Subtype.val ?_
    simpa [List.map_map, Function.comp_def, Walk.edges] using hp
  rw [walkEdges_eq, List.sum_toFinset _ hnd, List.map_map]
  unfold walkCost
  push_cast [NNReal.coe_list_sum, List.map_map]
  rfl

/-- A walk has at most `p.length` distinct edges. -/
theorem card_walkEdges_le {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    (walkEdges p).card ≤ p.length := by
  classical
  unfold walkEdges
  calc _ ≤ p.edges.toFinset.card := by rw [Finset.card_subtype]; exact Finset.card_filter_le _ _
    _ ≤ p.edges.length := List.toFinset_card_le _
    _ = p.length := p.length_edges

/-- The edges of a walk from `u` of length `n` lie within distance `‖u‖ + n` of the origin. -/
theorem walkEdges_subset_edgesNear {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    walkEdges p ⊆ edgesNear m (‖point u‖ + p.length) := by
  intro e he
  rw [mem_edgesNear]
  rw [mem_walkEdges] at he
  intro x hx
  have hxs : x ∈ p.support := p.mem_support_of_mem_edges he hx
  have h1 := norm_point_sub_le_length (p.takeUntil x hxs)
  have h2 : ((p.takeUntil x hxs).length : ℝ) ≤ p.length := by
    exact_mod_cast p.length_takeUntil_le_length hxs
  have h3 : ‖point x‖ ≤ ‖point u‖ + ‖point u - point x‖ := by
    calc ‖point x‖ = ‖point u - (point u - point x)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith only [h1, h2, h3]

/-- The number of lattice points in the ball of radius `R` is at most `(2R + 1)^(m+1)`. -/
theorem card_latticeBall_le {R : ℝ} (hR : 0 ≤ R) :
    ((latticeBall m R).card : ℝ) ≤ (2 * R + 1) ^ (m + 1) := by
  classical
  unfold latticeBall
  set k := ⌊R⌋₊
  have h1 : (((Finset.Icc (-(k : ℤ)) k ×ˢ
      Fintype.piFinset fun _ : Fin m => Finset.Icc (-(k : ℤ)) k).filter
        fun y : Vertex m => ‖point y‖ ≤ R).card) ≤ (2 * k + 1) ^ (m + 1) := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_succ']
    have : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
    rw [this]
  have h2 : ((k : ℝ)) ≤ R := Nat.floor_le hR
  calc _ ≤ (((2 * k + 1 : ℕ) ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ _ := by
      push_cast
      gcongr

end CurvatureVariance.Infra.FPP
