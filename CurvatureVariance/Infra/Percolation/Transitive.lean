/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Exploration
public import CurvatureVariance.Infra.Percolation.Balls
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Graph automorphisms and Bernoulli percolation

An automorphism `g : G ≃g G` acts on configurations by `mapConfig g`, the edge `g e` having the
state of `e`. It preserves Bernoulli percolation (`measurePreserving_mapConfig`), transports open
connections (`openConnected_mapConfig_iff`), distances (`dist_map`), edges inside a set
(`image_edgesWithin`), hence the probabilities of connections and of the one-arm event
(`percolation_openConnected_map`, `percolation_armEvent_map`) and the quantity `φ_p`
(`phi_map`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V}

/-- The configuration transported by the automorphism `g`: the edge `g e` has the state of `e`. -/
def mapConfig (g : G ≃g G) (ω : G.edgeSet → Bool) : G.edgeSet → Bool :=
  fun e => ω (g.symm.mapEdgeSet e)

theorem mapConfig_eq_piCongrLeft (g : G ≃g G) :
    (mapConfig g : (G.edgeSet → Bool) → G.edgeSet → Bool) =
      MeasurableEquiv.piCongrLeft (fun _ : G.edgeSet => Bool) g.mapEdgeSet := by
  funext ω e
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp only [mapConfig, cast_eq]
  rfl

/-- **Automorphisms preserve Bernoulli percolation.** -/
theorem measurePreserving_mapConfig (g : G ≃g G) (p : unitInterval) :
    MeasurePreserving (mapConfig g) (percolation G p) (percolation G p) := by
  rw [mapConfig_eq_piCongrLeft]
  refine ⟨MeasurableEquiv.measurable _, ?_⟩
  exact Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : G.edgeSet => bernoulliMeasure true false p) g.mapEdgeSet

theorem symm_mapEdgeSet_map (g : G ≃g G) (e : G.edgeSet) :
    g.symm.mapEdgeSet (g.mapEdgeSet e) = e :=
  Subtype.ext (by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ x y => simp [SimpleGraph.Hom.mapEdgeSet])

theorem mapConfig_apply_map (g : G ≃g G) (ω : G.edgeSet → Bool) (e : G.edgeSet) :
    mapConfig g ω (g.mapEdgeSet e) = ω e := by
  show ω (g.symm.mapEdgeSet (g.mapEdgeSet e)) = ω e
  rw [symm_mapEdgeSet_map]

theorem openConnected_map_of (g : G ≃g G) {ω : G.edgeSet → Bool} {A : Set (Sym2 V)} {u v : V}
    (h : OpenConnected G ω A u v) :
    OpenConnected G (mapConfig g ω) (Sym2.map g '' A) (g u) (g v) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.map g.toHom, fun d hd => ?_⟩
  rw [SimpleGraph.Walk.darts_map, List.mem_map] at hd
  obtain ⟨d', hd', rfl⟩ := hd
  obtain ⟨h1, h2⟩ := hp d' hd'
  refine ⟨⟨d'.edge, h1, ?_⟩, ?_⟩
  · simp [SimpleGraph.Dart.edge]
  · have := mapConfig_apply_map g ω ⟨d'.edge, d'.edge_mem⟩
    rw [← h2, ← this]
    rfl

theorem openConnected_mapConfig_iff (g : G ≃g G) (ω : G.edgeSet → Bool) (A : Set (Sym2 V))
    (u v : V) :
    OpenConnected G (mapConfig g ω) (Sym2.map g '' A) (g u) (g v) ↔ OpenConnected G ω A u v := by
  refine ⟨fun h => ?_, openConnected_map_of g⟩
  have h' := openConnected_map_of g.symm h
  have hA : Sym2.map g.symm '' (Sym2.map g '' A) = A := by
    rw [Set.image_image]
    simp [Sym2.map_map]
  have hω : mapConfig g.symm (mapConfig g ω) = ω := by
    funext e; exact congrArg ω (symm_mapEdgeSet_map g e)
  rw [hA, hω] at h'
  simpa using h'

theorem image_edgesWithin (g : G ≃g G) (S : Set V) :
    Sym2.map g '' edgesWithin S = edgesWithin (g '' S) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_edgesWithin]
    constructor
    · rintro ⟨e, he, hab⟩
      induction e using Sym2.ind with
      | _ x y =>
        rw [mk_mem_edgesWithin] at he
        simp only [Sym2.map_mk, Sym2.eq_iff] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨⟨x, he.1, rfl⟩, ⟨y, he.2, rfl⟩⟩
        · exact ⟨⟨y, he.2, rfl⟩, ⟨x, he.1, rfl⟩⟩
    · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
      exact ⟨s(x, y), mk_mem_edgesWithin.2 ⟨hx, hy⟩, rfl⟩

theorem dist_map_le (g : G ≃g G) (u v : V) : G.dist (g u) (g v) ≤ G.dist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
    simpa [hp] using SimpleGraph.dist_le (p.map g.toHom)
  · have h' : ¬ G.Reachable (g u) (g v) := fun h' => h (by
      obtain ⟨q⟩ := h'
      exact ⟨by simpa using q.map g.symm.toHom⟩)
    rw [SimpleGraph.dist_eq_zero_of_not_reachable h, SimpleGraph.dist_eq_zero_of_not_reachable h']

theorem dist_map (g : G ≃g G) (u v : V) : G.dist (g u) (g v) = G.dist u v := by
  refine le_antisymm (dist_map_le g u v) ?_
  simpa using dist_map_le g.symm (g u) (g v)

theorem percolation_openConnected_map [Countable V] (g : G ≃g G) (p : unitInterval)
    (A : Set (Sym2 V)) (u v : V) :
    percolation G p {ω | OpenConnected G ω (Sym2.map g '' A) (g u) (g v)} =
      percolation G p {ω | OpenConnected G ω A u v} := by
  have : {ω | OpenConnected G ω A u v} =
      mapConfig g ⁻¹' {ω | OpenConnected G ω (Sym2.map g '' A) (g u) (g v)} := by
    ext ω; simp [openConnected_mapConfig_iff]
  rw [this]
  exact ((measurePreserving_mapConfig g p).measure_preimage
    (measurableSet_openConnected _ _ _).nullMeasurableSet).symm

theorem image_univ_map (g : G ≃g G) : Sym2.map g '' (Set.univ : Set (Sym2 V)) = Set.univ :=
  Set.eq_univ_of_forall fun e => ⟨Sym2.map g.symm e, trivial, by simp [Sym2.map_map]⟩

/-- Arm probabilities are invariant under automorphisms. -/
theorem percolation_armEvent_map [Countable V] (g : G ≃g G) (p : unitInterval) (v : V) (n : ℕ) :
    percolation G p (armEvent G (g v) n) = percolation G p (armEvent G v n) := by
  have : armEvent G v n = mapConfig g ⁻¹' armEvent G (g v) n := by
    ext ω
    simp only [armEvent, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, hw, hc⟩
      refine ⟨g w, by rwa [dist_map], ?_⟩
      have := (openConnected_mapConfig_iff g ω Set.univ v w).2 hc
      rwa [image_univ_map] at this
    · rintro ⟨w, hw, hc⟩
      obtain ⟨w', rfl⟩ := g.surjective w
      refine ⟨w', by rwa [dist_map] at hw, ?_⟩
      rw [← image_univ_map g] at hc
      exact (openConnected_mapConfig_iff g ω Set.univ v w').1 hc
  rw [this]
  exact ((measurePreserving_mapConfig g p).measure_preimage
    (measurableSet_armEvent _ _).nullMeasurableSet).symm

/-- `φ_p` is invariant under automorphisms. -/
theorem phi_map [Countable V] [DecidableEq V] [G.LocallyFinite] (g : G ≃g G) (p : unitInterval)
    (v : V) (S : Finset V) :
    phi G p (g v) (S.map g.toEquiv.toEmbedding) = phi G p v S := by
  have hcard : ∀ x : V, ((G.neighborFinset (g x)).filter
      (· ∉ S.map g.toEquiv.toEmbedding)).card = ((G.neighborFinset x).filter (· ∉ S)).card := by
    intro x
    refine Finset.card_bij (fun y _ => g.symm y) ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_map_equiv] at hy ⊢
      refine ⟨?_, hy.2⟩
      have := g.symm.map_adj_iff.2 hy.1
      simpa using this
    · intro a _ b _ h; exact g.symm.injective h
    · intro y hy
      refine ⟨g y, ?_, by simp⟩
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, Finset.mem_map_equiv] at hy ⊢
      exact ⟨g.map_adj_iff.2 hy.1, (g.toEquiv.symm_apply_apply y).symm ▸ hy.2⟩
  unfold phi
  congr 1
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  refine congrArg₂ (· • ·) (hcard x) ?_
  have h := percolation_openConnected_map g p (edgesWithin (S : Set V)) v x
  rw [image_edgesWithin] at h
  simp only [Finset.coe_map] at *
  exact congrArg ENNReal.toReal h

end CurvatureVariance.Infra.Percolation
