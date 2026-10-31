/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Product
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Open walks and connections in bond percolation

Bond percolation on a graph `G` lives on the configurations `ω : G.edgeSet → Bool`, an edge `e`
being open when `ω e = true`, under `percolation G p = bernoulliProduct G.edgeSet p`.

* `IsOpenIn ω A p`: every edge crossed by the walk `p` lies in the edge set `A` and is open.
* `OpenConnected G ω A u v`: some walk from `u` to `v` is open in `A`; with `A = univ` this is
  `u ↔ v`, with `A` the edges inside a vertex set `S` it is the connection `u ↔ v` in `S` of
  Duminil-Copin and Tassion.
* Locality (`dependsOn_openConnected`): the connection depends only on the edges of `A`.
* Measurability on a countable vertex set (`measurableSet_openConnected`) and monotonicity in the
  configuration (`isUpperSet_openConnected`).
* `openGraph`, the graph of open edges of a set `S` of edges (the carrier of Mathlib's
  `setBernoulli`, as in the definition `CurvatureVariance.openGraph`), and
  `reachable_openGraph_openSet_iff`: reachability in the open graph of `openSet ω` is
  `OpenConnected G ω univ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} (G : SimpleGraph V)

/-- **Bernoulli bond percolation** on `G` with parameter `p`: the edges are open independently,
each with probability `p`. -/
noncomputable abbrev percolation (p : I) : Measure (G.edgeSet → Bool) :=
  bernoulliProduct G.edgeSet p

variable {G}

/-- The walk `p` is **open inside** the edge set `A` in the configuration `ω`: every edge it
crosses lies in `A` and is open. -/
def IsOpenIn (ω : G.edgeSet → Bool) (A : Set (Sym2 V)) {u v : V} (p : G.Walk u v) : Prop :=
  ∀ d ∈ p.darts, d.edge ∈ A ∧ ω ⟨d.edge, d.edge_mem⟩ = true

variable (G) in
/-- `u` and `v` are **connected by an open walk inside** the edge set `A` in `ω`. -/
def OpenConnected (ω : G.edgeSet → Bool) (A : Set (Sym2 V)) (u v : V) : Prop :=
  ∃ p : G.Walk u v, IsOpenIn ω A p

section Walks

variable {ω ω' : G.edgeSet → Bool} {A B : Set (Sym2 V)} {u v w : V}

@[simp] theorem isOpenIn_nil : IsOpenIn ω A (SimpleGraph.Walk.nil : G.Walk u u) := by
  simp [IsOpenIn]

theorem isOpenIn_cons {h : G.Adj u v} {p : G.Walk v w} :
    IsOpenIn ω A (SimpleGraph.Walk.cons h p) ↔
      (s(u, v) ∈ A ∧ ω ⟨s(u, v), h⟩ = true) ∧ IsOpenIn ω A p := by
  simp [IsOpenIn]

theorem isOpenIn_append {p : G.Walk u v} {q : G.Walk v w} :
    IsOpenIn ω A (p.append q) ↔ IsOpenIn ω A p ∧ IsOpenIn ω A q := by
  simp only [IsOpenIn, SimpleGraph.Walk.darts_append, List.mem_append]
  exact ⟨fun h => ⟨fun d hd => h d (.inl hd), fun d hd => h d (.inr hd)⟩,
    fun h d hd => hd.elim (h.1 d) (h.2 d)⟩

theorem IsOpenIn.mono_edges {p : G.Walk u v} (hp : IsOpenIn ω A p) (hAB : A ⊆ B) :
    IsOpenIn ω B p := fun d hd => ⟨hAB (hp d hd).1, (hp d hd).2⟩

theorem IsOpenIn.mono_config {p : G.Walk u v} (hp : IsOpenIn ω A p) (hω : ω ≤ ω') :
    IsOpenIn ω' A p := fun d hd =>
  ⟨(hp d hd).1, by
    have h₁ := hω ⟨d.edge, d.edge_mem⟩
    have h₂ := (hp d hd).2
    revert h₁ h₂
    cases ω ⟨d.edge, d.edge_mem⟩ <;> cases ω' ⟨d.edge, d.edge_mem⟩ <;> simp⟩

/-- Openness of a walk depends only on the configuration on the edges it crosses inside `A`. -/
theorem IsOpenIn.congr {p : G.Walk u v} (hp : IsOpenIn ω A p)
    (h : ∀ e : G.edgeSet, e.1 ∈ A → ω e = ω' e) : IsOpenIn ω' A p := fun d hd =>
  ⟨(hp d hd).1, (h ⟨d.edge, d.edge_mem⟩ (hp d hd).1).symm.trans (hp d hd).2⟩

end Walks

section Connections

variable {ω ω' : G.edgeSet → Bool} {A B : Set (Sym2 V)} {u v w : V}

theorem OpenConnected.refl (ω : G.edgeSet → Bool) (A : Set (Sym2 V)) (u : V) :
    OpenConnected G ω A u u :=
  ⟨.nil, isOpenIn_nil⟩

theorem OpenConnected.trans (h₁ : OpenConnected G ω A u v) (h₂ : OpenConnected G ω A v w) :
    OpenConnected G ω A u w :=
  let ⟨p, hp⟩ := h₁; let ⟨q, hq⟩ := h₂; ⟨p.append q, isOpenIn_append.2 ⟨hp, hq⟩⟩

/-- An open edge of `A` connects its endpoints. -/
theorem OpenConnected.of_adj (h : G.Adj u v) (hA : s(u, v) ∈ A) (hω : ω ⟨s(u, v), h⟩ = true) :
    OpenConnected G ω A u v :=
  ⟨.cons h .nil, isOpenIn_cons.2 ⟨⟨hA, hω⟩, isOpenIn_nil⟩⟩

theorem OpenConnected.mono_edges (h : OpenConnected G ω A u v) (hAB : A ⊆ B) :
    OpenConnected G ω B u v :=
  let ⟨p, hp⟩ := h; ⟨p, hp.mono_edges hAB⟩

theorem OpenConnected.mono_config (h : OpenConnected G ω A u v) (hω : ω ≤ ω') :
    OpenConnected G ω' A u v :=
  let ⟨p, hp⟩ := h; ⟨p, hp.mono_config hω⟩

theorem OpenConnected.congr (h : OpenConnected G ω A u v)
    (hω : ∀ e : G.edgeSet, e.1 ∈ A → ω e = ω' e) : OpenConnected G ω' A u v :=
  let ⟨p, hp⟩ := h; ⟨p, hp.congr hω⟩

/-- **Locality**: a connection inside `A` depends only on the edges of `A`. -/
theorem dependsOn_openConnected (A : Set (Sym2 V)) (u v : V) :
    DependsOn (fun ω : G.edgeSet → Bool => OpenConnected G ω A u v) {e | e.1 ∈ A} := by
  intro ω ω' h
  exact propext ⟨fun hc => hc.congr fun e he => h e he, fun hc => hc.congr fun e he => (h e he).symm⟩

/-- Locality for the event that `u` is connected inside `A` to some vertex of `W`. -/
theorem dependsOn_exists_openConnected (A : Set (Sym2 V)) (u : V) (W : Set V) :
    DependsOn (fun ω : G.edgeSet → Bool => ∃ w ∈ W, OpenConnected G ω A u w) {e | e.1 ∈ A} := by
  intro ω ω' h
  refine propext ⟨fun ⟨w, hw, hc⟩ => ⟨w, hw, hc.congr fun e he => h e he⟩,
    fun ⟨w, hw, hc⟩ => ⟨w, hw, hc.congr fun e he => (h e he).symm⟩⟩

/-- Connections are increasing events. -/
theorem isUpperSet_openConnected (A : Set (Sym2 V)) (u v : V) :
    IsUpperSet {ω : G.edgeSet → Bool | OpenConnected G ω A u v} :=
  fun _ _ hω h => OpenConnected.mono_config h hω

theorem isUpperSet_exists_openConnected (A : Set (Sym2 V)) (u : V) (W : Set V) :
    IsUpperSet {ω : G.edgeSet → Bool | ∃ w ∈ W, OpenConnected G ω A u w} :=
  fun _ _ hω ⟨w, hw, h⟩ => ⟨w, hw, h.mono_config hω⟩

end Connections

section Measurability

/-- Walks on a countable vertex set are countable, by their vertex lists. -/
instance countable_walk [Countable V] {u v : V} : Countable (G.Walk u v) :=
  SimpleGraph.Walk.support_injective.countable

theorem measurableSet_isOpenIn (A : Set (Sym2 V)) {u v : V} (p : G.Walk u v) :
    MeasurableSet {ω : G.edgeSet → Bool | IsOpenIn ω A p} := by
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
    have : {ω : G.edgeSet → Bool | IsOpenIn ω A (SimpleGraph.Walk.cons h q)} =
        {ω | s(a, b) ∈ A ∧ ω ⟨s(a, b), h⟩ = true} ∩ {ω | IsOpenIn ω A q} := by
      ext ω; simp [isOpenIn_cons]
    rw [this]
    refine MeasurableSet.inter ?_ ih
    by_cases hA : s(a, b) ∈ A
    · have hm : MeasurableSet {ω : G.edgeSet → Bool | ω ⟨s(a, b), h⟩ = true} :=
        (measurable_pi_apply (X := fun _ : G.edgeSet => Bool) ⟨s(a, b), h⟩)
          (measurableSet_singleton true)
      simpa [hA] using hm
    · simp [hA]

theorem measurableSet_openConnected [Countable V] (A : Set (Sym2 V)) (u v : V) :
    MeasurableSet {ω : G.edgeSet → Bool | OpenConnected G ω A u v} := by
  have : {ω : G.edgeSet → Bool | OpenConnected G ω A u v} =
      ⋃ p : G.Walk u v, {ω | IsOpenIn ω A p} := by
    ext ω; simp [OpenConnected]
  rw [this]
  exact MeasurableSet.iUnion fun p => measurableSet_isOpenIn A p

theorem measurableSet_exists_openConnected [Countable V] (A : Set (Sym2 V)) (u : V)
    (W : Set V) :
    MeasurableSet {ω : G.edgeSet → Bool | ∃ w ∈ W, OpenConnected G ω A u w} := by
  have : {ω : G.edgeSet → Bool | ∃ w ∈ W, OpenConnected G ω A u w} =
      ⋃ w ∈ W, {ω | OpenConnected G ω A u w} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable W) fun w _ => measurableSet_openConnected A u w

end Measurability

section OpenGraph

variable (G) in
/-- The **open graph** of a set `S` of edges: the graph whose edges are those of `S` (the
carrier of Mathlib's `setBernoulli`, as in the definition `CurvatureVariance.openGraph`). -/
def openGraph (S : Set G.edgeSet) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ((↑) '' S)

/-- **Reachability in the open graph** of the open edges of `ω` is connection by an open walk. -/
theorem reachable_openGraph_openSet_iff (ω : G.edgeSet → Bool) (u v : V) :
    (openGraph G (openSet ω)).Reachable u v ↔ OpenConnected G ω Set.univ u v := by
  constructor
  · rintro ⟨q⟩
    induction q with
    | nil => exact OpenConnected.refl ω _ _
    | @cons a b c h q ih =>
      rw [openGraph, SimpleGraph.fromEdgeSet_adj] at h
      obtain ⟨⟨e, he, hee⟩, -⟩ := h
      have hG : G.Adj a b := by
        have := e.2; rw [hee] at this; exact this
      have hω : ω ⟨s(a, b), hG⟩ = true := by
        have : e = ⟨s(a, b), hG⟩ := Subtype.ext hee
        subst this; exact he
      exact (OpenConnected.of_adj hG (Set.mem_univ _) hω).trans ih
  · rintro ⟨p, hp⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c h q ih =>
      rw [isOpenIn_cons] at hp
      have hadj : (openGraph G (openSet ω)).Adj a b := by
        rw [openGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨⟨s(a, b), h⟩, hp.1.2, rfl⟩, G.ne_of_adj h⟩
      exact hadj.reachable.trans (ih hp.2)

end OpenGraph

end CurvatureVariance.Infra.Percolation
