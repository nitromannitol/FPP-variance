/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Connections
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The exploration bound of Duminil-Copin and Tassion

For a finite set `S` of vertices containing `v`, the random set `𝒞 = clusterIn G ω S v` is the
set of vertices of `S` joined to `v` by an open path inside `S`. Duminil-Copin and Tassion
(*A new proof of the sharpness of the phase transition for Bernoulli percolation on `ℤ^d`*,
arXiv:1502.03051, §2.1) bound the probability that `v` is joined to a vertex outside `𝒞`: some
edge `{x, y}` of the edge boundary `ΔS` (`x ∈ S`, `y ∉ S`) is open with `x ∈ 𝒞`, and `y` is joined
to the target off `𝒞`. The three events depend on disjoint sets of edges. Summing over the values
of `𝒞` gives (`measure_exit_le`)

`P_p(v ↔ w for some w ∈ W, w ∉ 𝒞) ≤ ∑_{{x,y} ∈ ΔS} p P_p(v ↔^S x) P_p(y ↔ W)`.

`phi G p v S = p ∑_{{x,y} ∈ ΔS} P_p(v ↔^S x)` is their quantity `φ_p(S)` (rooted at `v`), and
`measure_exists_openConnected_le_phi` is the form used for exponential decay.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V}

/-! ### Edge sets and the cluster inside a finite set -/

/-- The edges with both endpoints in `S`. -/
def edgesWithin (S : Set V) : Set (Sym2 V) := {e | ∀ x ∈ e, x ∈ S}

theorem mk_mem_edgesWithin {S : Set V} {x y : V} : s(x, y) ∈ edgesWithin S ↔ x ∈ S ∧ y ∈ S := by
  simp [edgesWithin]

variable (G) in
/-- The edge `e` is an open edge of `G` in `ω`. -/
def IsOpenEdge (ω : G.edgeSet → Bool) (e : Sym2 V) : Prop :=
  ∃ h : e ∈ G.edgeSet, ω ⟨e, h⟩ = true

theorem measurableSet_isOpenEdge (e : Sym2 V) :
    MeasurableSet {ω : G.edgeSet → Bool | IsOpenEdge G ω e} := by
  by_cases h : e ∈ G.edgeSet
  · have : {ω : G.edgeSet → Bool | IsOpenEdge G ω e} = {ω | ω ⟨e, h⟩ = true} := by
      ext ω; simp [IsOpenEdge, h]
    rw [this]
    exact (measurable_pi_apply (X := fun _ : G.edgeSet => Bool) ⟨e, h⟩)
      (measurableSet_singleton true)
  · have : {ω : G.edgeSet → Bool | IsOpenEdge G ω e} = ∅ := by
      ext ω; simp [IsOpenEdge, h]
    rw [this]; exact MeasurableSet.empty

theorem dependsOn_isOpenEdge (e : Sym2 V) :
    DependsOn (· ∈ {ω : G.edgeSet → Bool | IsOpenEdge G ω e}) {f : G.edgeSet | f.1 = e} := by
  intro ω ω' h
  simp only [Set.mem_ofPred_eq, IsOpenEdge]
  exact propext ⟨fun ⟨he, hω⟩ => ⟨he, (h ⟨e, he⟩ rfl).symm.trans hω⟩,
    fun ⟨he, hω⟩ => ⟨he, (h ⟨e, he⟩ rfl).trans hω⟩⟩

theorem percolation_isOpenEdge (p : I) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    percolation G p {ω | IsOpenEdge G ω e} = ENNReal.ofReal p := by
  have : {ω : G.edgeSet → Bool | IsOpenEdge G ω e} = {ω | ω ⟨e, he⟩ = true} := by
    ext ω; simp [IsOpenEdge, he]
  rw [this, percolation, bernoulliProduct_coord_true]

/-- The intersection of events depending on `D₁` and `D₂` depends on `D₁ ∪ D₂`. -/
theorem dependsOn_inter {ι : Type*} {A B : Set (ι → Bool)} {D₁ D₂ : Set ι}
    (hA : DependsOn (· ∈ A) D₁) (hB : DependsOn (· ∈ B) D₂) :
    DependsOn (· ∈ A ∩ B) (D₁ ∪ D₂) := by
  intro ω ω' h
  have h₁ := hA fun i hi => h i (.inl hi)
  have h₂ := hB fun i hi => h i (.inr hi)
  simp only [Set.mem_inter_iff] at h₁ h₂ ⊢
  rw [h₁, h₂]

variable (G) in
open Classical in
/-- **The open cluster of `v` inside the finite set `S`**: the vertices of `S` joined to `v` by an
open path all of whose vertices lie in `S` (`𝒞` of Duminil-Copin and Tassion). -/
noncomputable def clusterIn (ω : G.edgeSet → Bool) (S : Finset V) (v : V) : Finset V :=
  S.filter fun z => OpenConnected G ω (edgesWithin (S : Set V)) v z

theorem mem_clusterIn {ω : G.edgeSet → Bool} {S : Finset V} {v z : V} :
    z ∈ clusterIn G ω S v ↔ z ∈ S ∧ OpenConnected G ω (edgesWithin (S : Set V)) v z := by
  classical
  simp [clusterIn]

theorem clusterIn_subset (ω : G.edgeSet → Bool) (S : Finset V) (v : V) :
    clusterIn G ω S v ⊆ S :=
  fun _ hz => (mem_clusterIn.1 hz).1

/-- The cluster inside `S` is closed under open edges inside `S`. -/
theorem mem_clusterIn_of_adj {ω : G.edgeSet → Bool} {S : Finset V} {v a b : V}
    (ha : a ∈ clusterIn G ω S v) (h : G.Adj a b) (hb : b ∈ S) (hω : ω ⟨s(a, b), h⟩ = true) :
    b ∈ clusterIn G ω S v := by
  rw [mem_clusterIn] at ha ⊢
  exact ⟨hb, ha.2.trans (OpenConnected.of_adj h (mk_mem_edgesWithin.2 ⟨ha.1, hb⟩) hω)⟩

/-! ### The walk decomposition -/

/-- A walk whose vertices all lie in `T` uses only edges with both endpoints in `T`. -/
theorem IsOpenIn.inter_edgesWithin {ω : G.edgeSet → Bool} {A : Set (Sym2 V)} {T : Set V}
    {a b : V} {p : G.Walk a b} (hp : IsOpenIn ω A p) (hT : ∀ z ∈ p.support, z ∈ T) :
    IsOpenIn ω (edgesWithin T) p := by
  intro d hd
  refine ⟨?_, (hp d hd).2⟩
  rw [SimpleGraph.Dart.edge, mk_mem_edgesWithin]
  exact ⟨hT _ (p.dart_fst_mem_support_of_mem_darts hd),
    hT _ (p.dart_snd_mem_support_of_mem_darts hd)⟩

/-- **The last exit from the cluster.** An open walk ending outside `𝒞` either avoids `𝒞` or
leaves it through an open edge `{x, y}` with `x ∈ 𝒞`, `y ∉ S`, after which it avoids `𝒞`. -/
theorem avoids_or_exits {ω : G.edgeSet → Bool} {S : Finset V} {v : V} :
    ∀ {a w : V} (p : G.Walk a w), IsOpenIn ω Set.univ p → w ∉ clusterIn G ω S v →
      (∀ z ∈ p.support, z ∉ clusterIn G ω S v) ∨
      ∃ x y, x ∈ clusterIn G ω S v ∧ y ∉ S ∧ IsOpenEdge G ω s(x, y) ∧
        OpenConnected G ω (edgesWithin (↑(clusterIn G ω S v) : Set V)ᶜ) y w
  | _, _, .nil, _, hw => .inl fun z hz => by
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ hw
  | a, w, .cons (v := b) h q, hp, hw => by
      rw [isOpenIn_cons] at hp
      rcases avoids_or_exits q hp.2 hw with hq | hq
      · by_cases ha : a ∈ clusterIn G ω S v
        · right
          have hb : b ∉ clusterIn G ω S v := hq b q.start_mem_support
          have hbS : b ∉ S := fun hbS => hb (mem_clusterIn_of_adj ha h hbS hp.1.2)
          exact ⟨a, b, ha, hbS, ⟨h, hp.1.2⟩, q, (hp.2.inter_edgesWithin hq)⟩
        · left
          intro z hz
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact ha
          · exact hq z hz
      · exact .inr hq

/-! ### Locality of the cluster event -/

/-- Along an open walk inside `S` starting in a set `T ⊆ S` closed under the open edges of `ω`
inside `S`, the walk stays in `T`, and is open in every `ω'` that agrees with `ω` on the edges
inside `S` touching `T`. -/
theorem walk_stays {ω ω' : G.edgeSet → Bool} {S : Finset V} {T : Set V}
    (hT : ∀ a b (h : G.Adj a b), a ∈ T → b ∈ S → ω ⟨s(a, b), h⟩ = true → b ∈ T)
    (hagree : ∀ e : G.edgeSet, e.1 ∈ edgesWithin (S : Set V) → (∃ z ∈ e.1, z ∈ T) → ω e = ω' e) :
    ∀ {a b : V} (p : G.Walk a b), IsOpenIn ω (edgesWithin (S : Set V)) p → a ∈ T →
      b ∈ T ∧ IsOpenIn ω' (edgesWithin (S : Set V)) p
  | _, _, .nil, _, ha => ⟨ha, isOpenIn_nil⟩
  | a, _, .cons (v := c) h q, hp, ha => by
      rw [isOpenIn_cons] at hp
      have hcS : c ∈ S := (mk_mem_edgesWithin.1 hp.1.1).2
      have hc : c ∈ T := hT a c h ha hcS hp.1.2
      obtain ⟨hb, hq⟩ := walk_stays hT hagree q hp.2 hc
      refine ⟨hb, isOpenIn_cons.2 ⟨⟨hp.1.1, ?_⟩, hq⟩⟩
      rw [← hagree ⟨s(a, c), h⟩ hp.1.1 ⟨a, Sym2.mem_mk_left a c, ha⟩]
      exact hp.1.2

/-- The cluster inside `S` is determined by the edges inside `S` that touch it. -/
theorem clusterIn_eq_of_agree {ω ω' : G.edgeSet → Bool} {S : Finset V} {v : V} (hv : v ∈ S)
    {A : Finset V} (hA : clusterIn G ω S v = A)
    (hagree : ∀ e : G.edgeSet, e.1 ∈ edgesWithin (S : Set V) → (∃ z ∈ e.1, z ∈ A) →
      ω e = ω' e) :
    clusterIn G ω' S v = A := by
  have hclosed : ∀ a b (h : G.Adj a b), a ∈ (A : Set V) → b ∈ S → ω ⟨s(a, b), h⟩ = true →
      b ∈ (A : Set V) := by
    intro a b h ha hb hω
    rw [Finset.mem_coe, ← hA] at ha ⊢
    exact mem_clusterIn_of_adj ha h hb hω
  have hvA : v ∈ A := hA ▸ mem_clusterIn.2 ⟨hv, OpenConnected.refl _ _ _⟩
  ext z
  constructor
  · intro hz
    obtain ⟨-, q, hq⟩ := mem_clusterIn.1 hz
    -- walk in `ω'` from `v ∈ A`; `A` is closed for `ω'` on the agreeing edges
    have hclosed' : ∀ a b (h : G.Adj a b), a ∈ (A : Set V) → b ∈ S →
        ω' ⟨s(a, b), h⟩ = true → b ∈ (A : Set V) := by
      intro a b h ha hb hω
      refine hclosed a b h ha hb ?_
      rw [hagree ⟨s(a, b), h⟩ (mk_mem_edgesWithin.2 ⟨?_, hb⟩) ⟨a, Sym2.mem_mk_left a b, ha⟩]
      · exact hω
      · rw [Finset.mem_coe, ← hA] at ha; exact (mem_clusterIn.1 ha).1
    exact (walk_stays (ω := ω') (ω' := ω) hclosed'
      (fun e he hz => (hagree e he hz).symm) q hq hvA).1
  · intro hz
    have hz' := hz
    rw [← hA, mem_clusterIn] at hz'
    obtain ⟨hzS, q, hq⟩ := hz'
    exact mem_clusterIn.2 ⟨hzS, q, (walk_stays hclosed hagree q hq hvA).2⟩

/-- The edges determining the event `{𝒞 = A}`: the edges inside `S` touching `A`. -/
def clusterEdges (S A : Finset V) : Set (Sym2 V) :=
  {e | e ∈ edgesWithin (S : Set V) ∧ ∃ z ∈ e, z ∈ A}

theorem dependsOn_clusterIn_eq {S : Finset V} {v : V} (hv : v ∈ S) (A : Finset V) :
    DependsOn (· ∈ {ω : G.edgeSet → Bool | clusterIn G ω S v = A})
      {e : G.edgeSet | e.1 ∈ clusterEdges S A} := by
  intro ω ω' h
  simp only [Set.mem_ofPred_eq]
  exact propext ⟨fun hA => clusterIn_eq_of_agree hv hA fun e he hz => h e ⟨he, hz⟩,
    fun hA => clusterIn_eq_of_agree hv hA fun e he hz => (h e ⟨he, hz⟩).symm⟩

variable [Countable V]

theorem measurableSet_clusterIn_eq (S : Finset V) (v : V) (A : Finset V) :
    MeasurableSet {ω : G.edgeSet → Bool | clusterIn G ω S v = A} := by
  have : {ω : G.edgeSet → Bool | clusterIn G ω S v = A} =
      {_ω | A ⊆ S} ∩ ⋂ z ∈ (S : Set V),
        {ω | OpenConnected G ω (edgesWithin (S : Set V)) v z ↔ z ∈ A} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_coe]
    constructor
    · rintro rfl
      exact ⟨fun z hz => (mem_clusterIn.1 hz).1,
        fun z hz => ⟨fun h => mem_clusterIn.2 ⟨hz, h⟩, fun h => (mem_clusterIn.1 h).2⟩⟩
    · rintro ⟨hAS, h⟩
      ext z
      rw [mem_clusterIn]
      exact ⟨fun hz => (h z hz.1).1 hz.2, fun hz => ⟨hAS hz, (h z (hAS hz)).2 hz⟩⟩
  rw [this]
  refine MeasurableSet.inter ?_ (MeasurableSet.biInter (Set.to_countable _) fun z _ => ?_)
  · by_cases hAS : A ⊆ S <;> simp [hAS]
  · by_cases hz : z ∈ A
    · have : {ω : G.edgeSet → Bool | OpenConnected G ω (edgesWithin (S : Set V)) v z ↔ z ∈ A} =
          {ω | OpenConnected G ω (edgesWithin (S : Set V)) v z} := by
        ext ω; simp [hz]
      rw [this]; exact measurableSet_openConnected _ v z
    · have : {ω : G.edgeSet → Bool | OpenConnected G ω (edgesWithin (S : Set V)) v z ↔ z ∈ A} =
          {ω | OpenConnected G ω (edgesWithin (S : Set V)) v z}ᶜ := by
        ext ω; simp [hz]
      rw [this]; exact (measurableSet_openConnected _ v z).compl

/-! ### The exploration bound -/

section Bound

variable [DecidableEq V] [G.LocallyFinite]

omit [Countable V] in
/-- The ordered edge boundary of `S`: pairs `(x, y)` with `x ∈ S`, `y ∉ S` adjacent. -/
theorem mem_boundary {S : Finset V} {x y : V} :
    y ∈ (G.neighborFinset x).filter (· ∉ S) ↔ G.Adj x y ∧ y ∉ S := by
  simp

omit [Countable V] in
/-- The decomposition of the exit event along the values of `𝒞` and the exit edge. -/
theorem exit_subset {S : Finset V} {v : V} (hv : v ∈ S) (W : Set V) :
    {ω : G.edgeSet → Bool | ∃ w ∈ W, w ∉ clusterIn G ω S v ∧ OpenConnected G ω Set.univ v w} ⊆
      ⋃ A ∈ S.powerset, ⋃ x ∈ A, ⋃ y ∈ (G.neighborFinset x).filter (· ∉ S),
        {ω | clusterIn G ω S v = A} ∩ {ω | IsOpenEdge G ω s(x, y)} ∩
          {ω | ∃ w ∈ W, OpenConnected G ω (edgesWithin (A : Set V)ᶜ) y w} := by
  rintro ω ⟨w, hw, hwC, q, hq⟩
  rcases avoids_or_exits q hq hwC with hav | ⟨x, y, hx, hy, hxy, hyw⟩
  · exact absurd (mem_clusterIn.2 ⟨hv, OpenConnected.refl _ _ _⟩) (hav v q.start_mem_support)
  · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_powerset,
      exists_prop]
    refine ⟨clusterIn G ω S v, clusterIn_subset ω S v, x, hx, y, ?_, ⟨rfl, hxy⟩, w, hw, hyw⟩
    exact mem_boundary.2 ⟨hxy.1, hy⟩

omit [DecidableEq V] [G.LocallyFinite] in
/-- One term of the exploration bound: the three events depend on disjoint sets of edges. -/
theorem measure_exit_term_le {S A : Finset V} {v x y : V} (hv : v ∈ S) (hx : x ∈ A)
    (hxy : G.Adj x y) (hy : y ∉ S) (W : Set V) (p : I) :
    percolation G p ({ω | clusterIn G ω S v = A} ∩ {ω | IsOpenEdge G ω s(x, y)} ∩
        {ω | ∃ w ∈ W, OpenConnected G ω (edgesWithin (A : Set V)ᶜ) y w}) ≤
      percolation G p {ω | clusterIn G ω S v = A} * ENNReal.ofReal p *
        percolation G p {ω | ∃ w ∈ W, OpenConnected G ω Set.univ y w} := by
  have h1 := dependsOn_clusterIn_eq (G := G) hv A
  have h2 := dependsOn_isOpenEdge (G := G) s(x, y)
  have h3 := dependsOn_exists_openConnected (G := G) (edgesWithin (A : Set V)ᶜ) y W
  have hd12 : Disjoint {e : G.edgeSet | e.1 ∈ clusterEdges S A} {f : G.edgeSet | f.1 = s(x, y)} := by
    rw [Set.disjoint_left]
    intro e he he'
    have he1 : e.1 ∈ edgesWithin (S : Set V) := he.1
    have he2 : e.1 = s(x, y) := he'
    rw [he2] at he1
    exact hy (mk_mem_edgesWithin.1 he1).2
  have hd3 : Disjoint ({e : G.edgeSet | e.1 ∈ clusterEdges S A} ∪ {f : G.edgeSet | f.1 = s(x, y)})
      {e : G.edgeSet | e.1 ∈ edgesWithin (A : Set V)ᶜ} := by
    rw [Set.disjoint_left]
    intro e he he3
    have he3' : ∀ z ∈ e.1, z ∉ (A : Set V) := he3
    rcases he with ⟨-, z, hz, hzA⟩ | he
    · exact he3' z hz hzA
    · have he2 : e.1 = s(x, y) := he
      exact he3' x (he2 ▸ Sym2.mem_mk_left x y) hx
  rw [measure_inter_eq_mul_of_dependsOn
      ((measurableSet_clusterIn_eq S v A).inter (measurableSet_isOpenEdge _))
      (measurableSet_exists_openConnected _ y W) (dependsOn_inter h1 h2) h3 hd3 p,
    measure_inter_eq_mul_of_dependsOn (measurableSet_clusterIn_eq S v A)
      (measurableSet_isOpenEdge _) h1 h2 hd12 p,
    percolation_isOpenEdge p hxy]
  exact mul_le_mul' le_rfl (measure_mono fun ω ⟨w, hw, h⟩ =>
    ⟨w, hw, h.mono_edges (Set.subset_univ _)⟩)

omit [G.LocallyFinite] in
/-- Summing `{𝒞 = A}` over the values `A ∋ x` gives `P_p(v ↔ x in S)`. -/
theorem sum_measure_clusterIn_eq {S : Finset V} {v x : V} (hx : x ∈ S) (p : I) :
    ∑ A ∈ S.powerset.filter (x ∈ ·), percolation G p {ω | clusterIn G ω S v = A} =
      percolation G p {ω | OpenConnected G ω (edgesWithin (S : Set V)) v x} := by
  rw [← measure_biUnion_finset]
  · congr 1
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · rintro ⟨A, ⟨-, hxA⟩, rfl⟩
      exact (mem_clusterIn.1 hxA).2
    · intro h
      exact ⟨clusterIn G ω S v, ⟨clusterIn_subset ω S v, mem_clusterIn.2 ⟨hx, h⟩⟩, rfl⟩
  · intro A _ B _ hAB
    exact Set.disjoint_left.2 fun ω hA hB => hAB (hA.symm.trans hB)
  · exact fun A _ => measurableSet_clusterIn_eq S v A

/-- **The exploration bound** ([Duminil-Copin and Tassion, §2.1]): the probability that `v` is
joined to some `w ∈ W` outside the cluster `𝒞` of `v` in `S` is at most
`∑_{{x,y} ∈ ΔS} p P_p(v ↔ x in S) P_p(y ↔ W)`. -/
theorem measure_exit_le {S : Finset V} {v : V} (hv : v ∈ S) (W : Set V) (p : I) :
    percolation G p
        {ω | ∃ w ∈ W, w ∉ clusterIn G ω S v ∧ OpenConnected G ω Set.univ v w} ≤
      ∑ x ∈ S, ∑ y ∈ (G.neighborFinset x).filter (· ∉ S),
        ENNReal.ofReal p * percolation G p {ω | OpenConnected G ω (edgesWithin (S : Set V)) v x} *
          percolation G p {ω | ∃ w ∈ W, OpenConnected G ω Set.univ y w} := by
  set P := percolation G p
  calc P {ω | ∃ w ∈ W, w ∉ clusterIn G ω S v ∧ OpenConnected G ω Set.univ v w}
      ≤ ∑ A ∈ S.powerset, ∑ x ∈ A, ∑ y ∈ (G.neighborFinset x).filter (· ∉ S),
          P ({ω | clusterIn G ω S v = A} ∩ {ω | IsOpenEdge G ω s(x, y)} ∩
            {ω | ∃ w ∈ W, OpenConnected G ω (edgesWithin (A : Set V)ᶜ) y w}) := by
        refine (measure_mono (exit_subset hv W)).trans ?_
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun A _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ A ∈ S.powerset, ∑ x ∈ A, ∑ y ∈ (G.neighborFinset x).filter (· ∉ S),
          P {ω | clusterIn G ω S v = A} * ENNReal.ofReal p *
            P {ω | ∃ w ∈ W, OpenConnected G ω Set.univ y w} := by
        refine Finset.sum_le_sum fun A _ => Finset.sum_le_sum fun x hx =>
          Finset.sum_le_sum fun y hy => ?_
        obtain ⟨hxy, hyS⟩ := mem_boundary.1 hy
        exact measure_exit_term_le hv hx hxy hyS W p
    _ = ∑ x ∈ S, ∑ A ∈ S.powerset.filter (x ∈ ·), ∑ y ∈ (G.neighborFinset x).filter (· ∉ S),
          P {ω | clusterIn G ω S v = A} * ENNReal.ofReal p *
            P {ω | ∃ w ∈ W, OpenConnected G ω Set.univ y w} := by
        refine Finset.sum_comm' fun A x => ?_
        simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨fun ⟨hA, hx⟩ => ⟨⟨hA, hx⟩, hA hx⟩, fun ⟨⟨hA, hx⟩, _⟩ => ⟨hA, hx⟩⟩
    _ = ∑ x ∈ S, ∑ y ∈ (G.neighborFinset x).filter (· ∉ S),
          ENNReal.ofReal p * P {ω | OpenConnected G ω (edgesWithin (S : Set V)) v x} *
            P {ω | ∃ w ∈ W, OpenConnected G ω Set.univ y w} := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.sum_comm, ← sum_measure_clusterIn_eq hx p]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun A _ => ?_
        ring

variable (G) in
/-- **The quantity `φ_p(S)` of Duminil-Copin and Tassion**, rooted at `v`: `p` times the sum over
the edges `{x, y}` of the edge boundary of `S` (`x ∈ S`, `y ∉ S`) of `P_p(v ↔ x in S)`. -/
noncomputable def phi (p : I) (v : V) (S : Finset V) : ℝ :=
  p * ∑ x ∈ S, ∑ _y ∈ (G.neighborFinset x).filter (· ∉ S),
    (percolation G p {ω | OpenConnected G ω (edgesWithin (S : Set V)) v x}).toReal

omit [Countable V] in
theorem ofReal_phi (p : I) (v : V) (S : Finset V) :
    ENNReal.ofReal (phi G p v S) = ∑ x ∈ S, ∑ _y ∈ (G.neighborFinset x).filter (· ∉ S),
      ENNReal.ofReal p * percolation G p {ω | OpenConnected G ω (edgesWithin (S : Set V)) v x} := by
  rw [phi, ENNReal.ofReal_mul p.2.1,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => ENNReal.toReal_nonneg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **The exploration bound in terms of `φ_p(S)`**: if every target `w ∈ W` lies outside `S` and
every vertex `y` just outside `S` reaches `W` with probability at most `a`, then `v` reaches `W`
with probability at most `φ_p(S) a`. -/
theorem measure_exists_openConnected_le_phi {S : Finset V} {v : V} (hv : v ∈ S) {W : Set V}
    (hW : ∀ w ∈ W, w ∉ S) (p : I) {a : ℝ≥0∞}
    (ha : ∀ x ∈ S, ∀ y, G.Adj x y → y ∉ S →
      percolation G p {ω | ∃ w ∈ W, OpenConnected G ω Set.univ y w} ≤ a) :
    percolation G p {ω | ∃ w ∈ W, OpenConnected G ω Set.univ v w} ≤
      ENNReal.ofReal (phi G p v S) * a := by
  have hsub : {ω : G.edgeSet → Bool | ∃ w ∈ W, OpenConnected G ω Set.univ v w} ⊆
      {ω | ∃ w ∈ W, w ∉ clusterIn G ω S v ∧ OpenConnected G ω Set.univ v w} :=
    fun ω ⟨w, hw, h⟩ => ⟨w, hw, fun hwC => hW w hw (mem_clusterIn.1 hwC).1, h⟩
  refine (measure_mono hsub).trans ((measure_exit_le hv W p).trans ?_)
  rw [ofReal_phi, Finset.sum_mul]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨hxy, hyS⟩ := mem_boundary.1 hy
  exact mul_le_mul' le_rfl (ha x hx y hxy hyS)

end Bound

end CurvatureVariance.Infra.Percolation
