/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Walks, coarse images of walks, and separated subfamilies

Four graph-theoretic facts used in the block renormalization proof of Kesten's estimate. Nothing
here involves the lattice or probability.

* `exists_prefix_exit`: a walk that starts outside a set `far` and visits it has an initial
  segment that stays outside `far` until its last vertex, which lies in `far` and is adjacent to a
  vertex outside `far`.
* `exists_walk_support_eq_image`: if `f : V → W` sends every edge of `G` to a vertex or an edge of
  `H`, then for every walk `γ` of `G` there is a walk of `H` from `f u` whose vertex set is
  `f '' γ.support` and whose length is at most `2 (#(f '' γ.support) - 1)` (a depth-first traversal
  of a spanning tree of the image).
* `sum_card_finsetWalkLength_le`: in a graph of maximal degree at most `D` there are at most `D^k`
  walks of length `k` from a given vertex.
* `exists_subset_pairwise_not_card_le`: if every element of a finite set `A` is related to at most
  `K` elements of `A` by a reflexive symmetric relation `close`, then `A` contains a subfamily `B`
  of pairwise non-related elements with `#A ≤ K #B` (greedy selection).
-/

@[expose] public section

namespace CurvatureVariance.Infra.Kesten

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-! ### First exit along a walk -/

/-- A walk starting outside `far` and visiting `far` has an initial segment ending at its first
vertex in `far`: every dart of the segment starts outside `far`, and the endpoint is adjacent to a
vertex outside `far`. -/
theorem exists_prefix_exit {far : V → Prop} {s v : V} (q : G.Walk s v) (hs : ¬ far s)
    (hw : ∃ w ∈ q.support, far w) :
    ∃ (y : V) (r : G.Walk s y), far y ∧ r.darts <+: q.darts ∧ (∀ d ∈ r.darts, ¬ far d.fst) ∧
      ∃ y', ¬ far y' ∧ G.Adj y' y := by
  induction q with
  | nil =>
    obtain ⟨w, hw, hfar⟩ := hw
    rw [Walk.support_nil, List.mem_singleton] at hw
    exact absurd (hw ▸ hfar) hs
  | @cons a b c h q ih =>
    by_cases hb : far b
    · refine ⟨b, Walk.cons h Walk.nil, hb, ?_, ?_, a, hs, h⟩
      · simp [Walk.darts_cons]
      · intro d hd
        rw [Walk.darts_cons, Walk.darts_nil, List.mem_singleton] at hd
        subst hd
        exact hs
    · obtain ⟨w, hw, hfar⟩ := hw
      have hw' : ∃ w ∈ q.support, far w := by
        rw [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact absurd hfar hs
        · exact ⟨w, hw, hfar⟩
      obtain ⟨y, r, hy, hpre, hr, y', hy', hadj⟩ := ih hb hw'
      refine ⟨y, Walk.cons h r, hy, ?_, ?_, y', hy', hadj⟩
      · simpa [Walk.darts_cons] using hpre
      · intro d hd
        rw [Walk.darts_cons, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hs
        · exact hr d hd

/-! ### A walk through the image of a walk -/

/-- Inserting a detour `y → z → y` at a vertex `y` of a walk adds `z` to its vertex set and two to
its length. -/
theorem exists_walk_support_insert [DecidableEq W] {s e y z : W} (Γ : H.Walk s e)
    (hy : y ∈ Γ.support) (hyz : H.Adj y z) :
    ∃ Γ' : H.Walk s e, Γ'.support.toFinset = insert z Γ.support.toFinset ∧
      Γ'.length = Γ.length + 2 := by
  obtain ⟨p, q, rfl⟩ := Walk.mem_support_iff_exists_append.mp hy
  refine ⟨p.append (Walk.cons hyz (Walk.cons hyz.symm q)), ?_, ?_⟩
  · have hp : y ∈ p.support := p.end_mem_support
    rw [Walk.support_append, Walk.support_append, Walk.support_cons, Walk.support_cons,
      List.tail_cons, ← q.cons_tail_support]
    ext x
    by_cases hx : x = y
    · subst hx
      simp [hp]
    · simp only [List.toFinset_append, List.toFinset_cons, List.tail_cons, Finset.mem_union,
        Finset.mem_insert, List.mem_toFinset, hx, false_or]
      tauto
  · simp only [Walk.length_append, Walk.length_cons]
    omega

/-- Visiting the successive entries of a list, each equal or adjacent to the previous one (the
first being adjacent or equal to a vertex `c` of `Γ₀`), by inserting a detour at each new entry. -/
theorem exists_walk_support_union [DecidableEq W] {s e : W} (l : List W) (Γ₀ : H.Walk s e)
    {c : W} (hc : c ∈ Γ₀.support) (hl : List.IsChain (fun a b => a = b ∨ H.Adj a b) (c :: l)) :
    ∃ Γ : H.Walk s e, Γ.support.toFinset = Γ₀.support.toFinset ∪ l.toFinset ∧
      Γ.length + 2 * Γ₀.support.toFinset.card ≤
        Γ₀.length + 2 * (Γ₀.support.toFinset ∪ l.toFinset).card := by
  induction l generalizing Γ₀ c with
  | nil => exact ⟨Γ₀, by simp, by simp⟩
  | cons b l ih =>
    rw [List.isChain_cons_cons] at hl
    by_cases hb : b ∈ Γ₀.support
    · obtain ⟨Γ, h1, h2⟩ := ih Γ₀ hb hl.2
      have hU : Γ₀.support.toFinset ∪ (b :: l).toFinset = Γ₀.support.toFinset ∪ l.toFinset := by
        rw [List.toFinset_cons, Finset.union_insert,
          Finset.insert_eq_of_mem (Finset.mem_union_left _ (List.mem_toFinset.2 hb))]
      rw [hU]
      exact ⟨Γ, h1, h2⟩
    · have hadj : H.Adj c b := hl.1.resolve_left fun h => hb (h ▸ hc)
      obtain ⟨Γ₁, h1s, h1l⟩ := exists_walk_support_insert Γ₀ hc hadj
      have hb1 : b ∈ Γ₁.support := by
        rw [← List.mem_toFinset, h1s]
        exact Finset.mem_insert_self _ _
      obtain ⟨Γ, h2s, h2l⟩ := ih Γ₁ hb1 hl.2
      have hU : Γ₁.support.toFinset ∪ l.toFinset = Γ₀.support.toFinset ∪ (b :: l).toFinset := by
        rw [h1s, List.toFinset_cons, Finset.union_insert, Finset.insert_union]
      have hcard : Γ₁.support.toFinset.card = Γ₀.support.toFinset.card + 1 := by
        rw [h1s, Finset.card_insert_of_notMem (by simpa using hb)]
      refine ⟨Γ, h2s.trans hU, ?_⟩
      rw [← hU]
      rw [hcard, h1l] at h2l
      omega

/-- If `f` sends every edge of `G` to a vertex or an edge of `H`, the image of a walk `γ` of `G`
is the vertex set of a walk of `H` from `f u` of length at most `2 (#(f '' γ.support) - 1)`. -/
theorem exists_walk_support_eq_image [DecidableEq V] [DecidableEq W] (f : V → W)
    (hf : ∀ x y, G.Adj x y → f x = f y ∨ H.Adj (f x) (f y)) {u v : V} (γ : G.Walk u v) :
    ∃ (w : W) (Γ : H.Walk (f u) w), Γ.support.toFinset = γ.support.toFinset.image f ∧
      Γ.length + 2 ≤ 2 * (γ.support.toFinset.image f).card := by
  have hchain : List.IsChain (fun a b => a = b ∨ H.Adj a b) (γ.support.map f) :=
    List.isChain_map_of_isChain f hf γ.isChain_adj_support
  rw [← γ.cons_tail_support, List.map_cons] at hchain
  obtain ⟨Γ, hsupp, hlen⟩ := exists_walk_support_union _ (Walk.nil : H.Walk (f u) (f u))
    (Walk.start_mem_support _) hchain
  have himage : γ.support.toFinset.image f =
      (Walk.nil : H.Walk (f u) (f u)).support.toFinset ∪ (γ.support.tail.map f).toFinset := by
    ext x
    simp only [Finset.mem_image, List.mem_toFinset, Finset.mem_union, Walk.support_nil,
      List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false,
      List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [← γ.cons_tail_support, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inl rfl
      · exact Or.inr ⟨a, ha, rfl⟩
    · rintro (rfl | ⟨a, ha, rfl⟩)
      · exact ⟨u, γ.start_mem_support, rfl⟩
      · exact ⟨a, List.mem_of_mem_tail ha, rfl⟩
  refine ⟨f u, Γ, hsupp.trans himage.symm, ?_⟩
  rw [himage]
  simpa using hlen

/-! ### Counting walks -/

/-- In a graph of maximal degree at most `D`, there are at most `D ^ k` walks of length `k` from a
vertex `u` (summed over any finite set of endpoints). -/
theorem sum_card_finsetWalkLength_le [DecidableEq V] [G.LocallyFinite] {D : ℕ}
    (hD : ∀ v, G.degree v ≤ D) (k : ℕ) (u : V) (S : Finset V) :
    ∑ v ∈ S, (G.finsetWalkLength k u v).card ≤ D ^ k := by
  induction k generalizing u with
  | zero =>
    have h : ∀ v, (G.finsetWalkLength 0 u v).card ≤ if u = v then 1 else 0 := by
      intro v
      by_cases huv : u = v
      · subst huv
        simp [SimpleGraph.finsetWalkLength]
      · simp [SimpleGraph.finsetWalkLength, huv]
    refine (Finset.sum_le_sum fun v _ => h v).trans ?_
    rw [Finset.sum_ite_eq, pow_zero]
    split_ifs <;> simp
  | succ k ih =>
    have h : ∀ v, (G.finsetWalkLength (k + 1) u v).card ≤
        ∑ w : G.neighborSet u, (G.finsetWalkLength k w v).card := by
      intro v
      change (Finset.univ.biUnion fun (w : G.neighborSet u) =>
        (G.finsetWalkLength k w v).map
          ⟨fun p => SimpleGraph.Walk.cons w.property p, fun _ _ h => by injection h⟩).card ≤ _
      refine Finset.card_biUnion_le.trans ?_
      exact Finset.sum_le_sum fun w _ => by simp
    refine (Finset.sum_le_sum fun v _ => h v).trans ?_
    rw [Finset.sum_comm]
    refine le_trans (Finset.sum_le_sum fun (w : G.neighborSet u) _ => ih (w : V)) ?_
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, pow_succ, mul_comm]
    refine Nat.mul_le_mul_left _ ?_
    rw [SimpleGraph.card_neighborSet_eq_degree]
    exact hD u

/-! ### A separated subfamily -/

/-- Greedy selection: if every element of `A` is `close` to at most `K` elements of `A`, for a
reflexive symmetric relation `close`, then `A` contains a subfamily `B` of pairwise non-`close`
elements with `#A ≤ K * #B`. -/
theorem exists_subset_pairwise_not_card_le {α : Type*} [DecidableEq α] (close : α → α → Prop)
    [DecidableRel close] (hrefl : ∀ a, close a a) (hsymm : ∀ a b, close a b → close b a)
    (A : Finset α) (K : ℕ) (hK : ∀ a ∈ A, (A.filter (close a)).card ≤ K) :
    ∃ B ⊆ A, (∀ a ∈ B, ∀ b ∈ B, a ≠ b → ¬ close a b) ∧ A.card ≤ K * B.card := by
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    set A' := A.filter fun b => ¬ close z b with hA'
    have hzA' : z ∉ A' := by simp [hA', hrefl z]
    have hsub : A' ⊆ A := Finset.filter_subset _ _
    have hss : A' ⊂ A := Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => hzA' (h ▸ hz)⟩
    have hK' : ∀ a ∈ A', (A'.filter (close a)).card ≤ K := fun a ha =>
      (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans (hK a (hsub ha))
    obtain ⟨B', hB'A', hsep, hcard⟩ := ih A' hss hK'
    have hzB' : z ∉ B' := fun h => hzA' (hB'A' h)
    refine ⟨insert z B', Finset.insert_subset hz (hB'A'.trans hsub), ?_, ?_⟩
    · have hfar : ∀ b ∈ B', ¬ close z b := fun b hb => (Finset.mem_filter.1 (hB'A' hb)).2
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha' <;> rcases hb with rfl | hb'
      · exact absurd rfl hab
      · exact hfar b hb'
      · exact fun h => hfar a ha' (hsymm _ _ h)
      · exact hsep a ha' b hb' hab
    · have hsplit : (A.filter (close z)).card + A'.card = A.card :=
        Finset.card_filter_add_card_filter_not _
      rw [Finset.card_insert_of_notMem hzB', mul_add, mul_one]
      have := hK z hz
      omega

end CurvatureVariance.Infra.Kesten
