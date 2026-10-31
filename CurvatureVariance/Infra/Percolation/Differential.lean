/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Russo
public import CurvatureVariance.Infra.Percolation.Balls
public import CurvatureVariance.Infra.Percolation.Exploration
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# The differential inequality of Duminil-Copin and Tassion

For the one-arm event `A = armEvent G o n` (`o` joined to distance `n`), which depends on the
finitely many edges with an endpoint at distance `< n`, Russo's formula gives
`d/dp P_p(A) = ∑_e P_p(e pivotal)`. Duminil-Copin and Tassion (arXiv:1502.03051, Lemma 2.1) bound
this from below through the random set `𝒮` of vertices at distance `< n` that are not joined to
the sphere of radius `n` (`blockedSet`): on `{𝒮 = S}` with `o ∈ S`, every edge `{x, y}` of the edge
boundary of `S` with `o ↔ x` in `S` is pivotal, `{𝒮 = S}` depends only on the edges not inside
`S`, and `o ↔ x` in `S` only on the edges inside `S`. Hence (`le_mul_sum_pivotal`)

`c (1 - P_p(A)) ≤ p (1 - p) ∑_e P_p(e pivotal)` whenever `φ_p(S) ≥ c` for all `S ∋ o` at distance
`< n`.

Integrating with `c = 1` above `q` (`le_toReal_percolation_armEvent`) gives the mean-field lower
bound `P_p(A) ≥ (p - q)/(p(1 - q))` uniformly in `n`, hence for the infinite cluster
(`le_percolation_infinite`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval Filter
open scoped ENNReal Topology

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V}

/-! ### Reaching the sphere -/

variable (G) in
/-- `z` reaches the sphere of radius `n` about `o` through edges with an endpoint at distance
`< n`. -/
def ReachesSphere (ω : G.edgeSet → Bool) (o : V) (n : ℕ) (z : V) : Prop :=
  ∃ w, G.dist o w = n ∧ OpenConnected G ω (innerEdges G o n) z w

theorem armEvent_eq_reachesSphere (hG : G.Connected) (o : V) (n : ℕ) :
    armEvent G o n = {ω | ReachesSphere G ω o n o} := by
  rw [armEvent_eq hG]; rfl

theorem reachesSphere_of_dist_eq {ω : G.edgeSet → Bool} {o w : V} {n : ℕ} (hw : G.dist o w = n) :
    ReachesSphere G ω o n w :=
  ⟨w, hw, OpenConnected.refl _ _ _⟩

/-- An open edge from a vertex at distance `< n` to a vertex reaching the sphere. -/
theorem reachesSphere_of_adj {ω : G.edgeSet → Bool} {o x y : V} {n : ℕ} (hx : G.dist o x < n)
    (h : G.Adj x y) (hω : ω ⟨s(x, y), h⟩ = true) (hy : ReachesSphere G ω o n y) :
    ReachesSphere G ω o n x :=
  let ⟨w, hw, hyw⟩ := hy
  ⟨w, hw, (OpenConnected.of_adj (A := innerEdges G o n) h ⟨x, Sym2.mem_mk_left x y, hx⟩
    hω).trans hyw⟩

theorem ReachesSphere.mono_config {ω ω' : G.edgeSet → Bool} {o z : V} {n : ℕ}
    (h : ReachesSphere G ω o n z) (hω : ω ≤ ω') : ReachesSphere G ω' o n z :=
  let ⟨w, hw, hzw⟩ := h; ⟨w, hw, hzw.mono_config hω⟩

theorem measurableSet_reachesSphere [Countable V] (o : V) (n : ℕ) (z : V) :
    MeasurableSet {ω : G.edgeSet → Bool | ReachesSphere G ω o n z} := by
  have : {ω : G.edgeSet → Bool | ReachesSphere G ω o n z} =
      {ω | ∃ w ∈ {w | G.dist o w = n}, OpenConnected G ω (innerEdges G o n) z w} := by
    ext ω; simp [ReachesSphere]
  rw [this]
  exact measurableSet_exists_openConnected _ z _

/-! ### The blocked set `𝒮` -/

section Blocked

variable [G.LocallyFinite] (hG : G.Connected)

open Classical in
/-- **The set `𝒮` of Duminil-Copin and Tassion**: the vertices at distance `< n` from `o` that are
not joined to the sphere of radius `n`. -/
noncomputable def blockedSet (ω : G.edgeSet → Bool) (o : V) (n : ℕ) : Finset V :=
  (innerBall hG o n).filter fun z => ¬ReachesSphere G ω o n z

variable {hG}

theorem mem_blockedSet {ω : G.edgeSet → Bool} {o z : V} {n : ℕ} :
    z ∈ blockedSet hG ω o n ↔ G.dist o z < n ∧ ¬ReachesSphere G ω o n z := by
  classical
  simp [blockedSet, mem_innerBall]

/-- If `o ∈ 𝒮`, the arm event fails. -/
theorem notMem_armEvent_of_mem_blockedSet {ω : G.edgeSet → Bool} {o : V} {n : ℕ}
    (h : o ∈ blockedSet hG ω o n) : ω ∉ armEvent G o n := by
  rw [armEvent_eq_reachesSphere hG]
  exact (mem_blockedSet.1 h).2

/-- An open walk inside the inner edges ending on the sphere stays off `𝒮`, and is open in every
configuration agreeing with `ω` on the inner edges not inside `S = 𝒮`. -/
theorem walk_to_sphere_open {ω ω' : G.edgeSet → Bool} {o : V} {n : ℕ} {S : Finset V}
    (hS : blockedSet hG ω o n = S)
    (hagree : ∀ e : G.edgeSet, e.1 ∈ innerEdges G o n → e.1 ∉ edgesWithin (S : Set V) →
      ω e = ω' e) {w : V} (hw : G.dist o w = n) :
    ∀ {z : V} (q : G.Walk z w), IsOpenIn ω (innerEdges G o n) q →
      ReachesSphere G ω o n z ∧ IsOpenIn ω' (innerEdges G o n) q
  | _, .nil, _ => ⟨reachesSphere_of_dist_eq hw, isOpenIn_nil⟩
  | z, .cons (v := c) h q, hq => by
      rw [isOpenIn_cons] at hq
      obtain ⟨hc, hq'⟩ := walk_to_sphere_open hS hagree hw q hq.2
      have hcS : c ∉ S := fun hcS => by
        rw [← hS] at hcS; exact (mem_blockedSet.1 hcS).2 hc
      refine ⟨⟨w, hw, (OpenConnected.of_adj h hq.1.1 hq.1.2).trans ⟨q, hq.2⟩⟩,
        isOpenIn_cons.2 ⟨⟨hq.1.1, ?_⟩, hq'⟩⟩
      rw [← hagree ⟨s(z, c), h⟩ hq.1.1 fun hin => hcS (hin c (Sym2.mem_mk_right z c))]
      exact hq.1.2

/-- **`𝒮` is determined by the edges not inside it** (among those with an endpoint at distance
`< n`). -/
theorem blockedSet_eq_of_agree {ω ω' : G.edgeSet → Bool} {o : V} {n : ℕ} {S : Finset V}
    (hS : blockedSet hG ω o n = S)
    (hagree : ∀ e : G.edgeSet, e.1 ∈ innerEdges G o n → e.1 ∉ edgesWithin (S : Set V) →
      ω e = ω' e) :
    blockedSet hG ω' o n = S := by
  have hSB : ∀ z ∈ S, G.dist o z < n := fun z hz => by
    rw [← hS] at hz; exact (mem_blockedSet.1 hz).1
  -- reaching the sphere in `ω` implies reaching it in `ω'`
  have h₁ : ∀ z, ReachesSphere G ω o n z → ReachesSphere G ω' o n z := by
    rintro z ⟨w, hw, q, hq⟩
    exact ⟨w, hw, q, (walk_to_sphere_open hS hagree hw q hq).2⟩
  -- a vertex of `S` does not reach the sphere in `ω'`
  have h₂ : ∀ z ∈ S, ¬ReachesSphere G ω' o n z := by
    rintro z hz ⟨w, hw, q, hq⟩
    have hwS : w ∉ S := fun hwS => by have := hSB w hwS; omega
    obtain ⟨d, hd, hdS, hdS'⟩ := q.exists_boundary_dart (S : Set V) hz hwS
    have hdin := (hq d hd).1
    have hfst : G.dist o d.fst < n := hSB _ hdS
    have hω : ω ⟨d.edge, d.edge_mem⟩ = true := by
      have hmem : d.snd ∈ d.edge := by
        rw [SimpleGraph.Dart.edge]; exact Sym2.mem_mk_right _ _
      rw [hagree ⟨d.edge, d.edge_mem⟩ hdin fun hin => hdS' (hin d.snd hmem)]
      exact (hq d hd).2
    have hsnd : ReachesSphere G ω o n d.snd := by
      by_cases hsB : G.dist o d.snd < n
      · by_contra hns
        have : d.snd ∈ blockedSet hG ω o n := mem_blockedSet.2 ⟨hsB, hns⟩
        rw [hS] at this; exact hdS' this
      · exact reachesSphere_of_dist_eq (le_antisymm
          (dist_le_of_adj_of_dist_lt hG d.adj hfst) (not_lt.1 hsB))
    have hfst' : ReachesSphere G ω o n d.fst := reachesSphere_of_adj hfst d.adj hω hsnd
    have : d.fst ∈ blockedSet hG ω o n := by rw [hS]; exact hdS
    exact (mem_blockedSet.1 this).2 hfst'
  ext z
  rw [mem_blockedSet]
  constructor
  · rintro ⟨hzn, hz⟩
    by_contra hzS
    have : z ∉ blockedSet hG ω o n := by rw [hS]; exact hzS
    rw [mem_blockedSet, not_and, not_not] at this
    exact hz (h₁ z (this hzn))
  · intro hz
    exact ⟨hSB z hz, h₂ z hz⟩

/-- The edges determining `{𝒮 = S}`: inner edges not inside `S`. -/
def blockedEdges (o : V) (n : ℕ) (S : Finset V) : Set (Sym2 V) :=
  {e | e ∈ innerEdges G o n ∧ e ∉ edgesWithin (S : Set V)}

theorem dependsOn_blockedSet_eq (o : V) (n : ℕ) (S : Finset V) :
    DependsOn (· ∈ {ω : G.edgeSet → Bool | blockedSet hG ω o n = S})
      {e : G.edgeSet | e.1 ∈ blockedEdges (G := G) o n S} := by
  intro ω ω' h
  simp only [Set.mem_ofPred_eq]
  exact propext ⟨fun hS => blockedSet_eq_of_agree hS fun e he he' => h e ⟨he, he'⟩,
    fun hS => blockedSet_eq_of_agree hS fun e he he' => (h e ⟨he, he'⟩).symm⟩

theorem measurableSet_blockedSet_eq [Countable V] (o : V) (n : ℕ) (S : Finset V) :
    MeasurableSet {ω : G.edgeSet → Bool | blockedSet hG ω o n = S} := by
  have : {ω : G.edgeSet → Bool | blockedSet hG ω o n = S} =
      {_ω | S ⊆ innerBall hG o n} ∩ ⋂ z ∈ (innerBall hG o n : Set V),
        {ω | ¬ReachesSphere G ω o n z ↔ z ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_coe]
    constructor
    · rintro rfl
      refine ⟨fun z hz => mem_innerBall hG |>.2 (mem_blockedSet.1 hz).1, fun z hz => ?_⟩
      rw [mem_blockedSet]
      exact ⟨fun h => ⟨(mem_innerBall hG).1 hz, h⟩, fun h => h.2⟩
    · rintro ⟨hSB, h⟩
      ext z
      rw [mem_blockedSet]
      constructor
      · rintro ⟨hz, hzr⟩
        exact (h z ((mem_innerBall hG).2 hz)).1 hzr
      · intro hz
        exact ⟨(mem_innerBall hG).1 (hSB hz), (h z (hSB hz)).2 hz⟩
  rw [this]
  refine MeasurableSet.inter ?_ (MeasurableSet.biInter (Set.to_countable _) fun z _ => ?_)
  · by_cases hSB : S ⊆ innerBall hG o n <;> simp [hSB]
  · by_cases hz : z ∈ S
    · have : {ω : G.edgeSet → Bool | ¬ReachesSphere G ω o n z ↔ z ∈ S} =
          {ω | ReachesSphere G ω o n z}ᶜ := by
        ext ω; simp [hz]
      rw [this]; exact (measurableSet_reachesSphere o n z).compl
    · have : {ω : G.edgeSet → Bool | ¬ReachesSphere G ω o n z ↔ z ∈ S} =
          {ω | ReachesSphere G ω o n z} := by
        ext ω; simp [hz]
      rw [this]; exact measurableSet_reachesSphere o n z

end Blocked

/-! ### Pivotal edges -/

section Pivotal

variable [G.LocallyFinite] {hG : G.Connected}

variable (hG) in
/-- The edges with an endpoint at distance `< n`, as a finset: the arm event depends only on
them. -/
noncomputable def innerEdgeFinset (o : V) (n : ℕ) : Finset G.edgeSet :=
  (finite_innerEdges hG o n).toFinset

theorem coe_innerEdgeFinset (o : V) (n : ℕ) :
    ((innerEdgeFinset hG o n : Finset G.edgeSet) : Set G.edgeSet) =
      {e : G.edgeSet | e.1 ∈ innerEdges G o n} :=
  Set.Finite.coe_toFinset _

theorem dependsOn_armEvent_innerEdgeFinset (o : V) (n : ℕ) :
    DependsOn (· ∈ armEvent G o n) ((innerEdgeFinset hG o n : Finset G.edgeSet) : Set G.edgeSet) := by
  rw [coe_innerEdgeFinset]; exact dependsOn_armEvent hG o n

variable [DecidableEq V]

omit [G.LocallyFinite] in
theorem le_update_true (ω : G.edgeSet → Bool) (e : G.edgeSet) : ω ≤ Function.update ω e true := by
  intro f
  by_cases hf : f = e
  · subst hf; simp
  · simp [Function.update_of_ne hf]

omit [G.LocallyFinite] in
theorem update_false_le (ω : G.edgeSet → Bool) (e : G.edgeSet) : Function.update ω e false ≤ ω := by
  intro f
  by_cases hf : f = e
  · subst hf; simp
  · simp [Function.update_of_ne hf]

/-- **On `{𝒮 = S}`, the boundary edges `{x, y}` with `o ↔ x` in `S` are pivotal**, and the arm
event fails. -/
theorem mem_pivotalEvent_of_blockedSet {ω : G.edgeSet → Bool} {o : V} {n : ℕ} {S : Finset V}
    (hoS : o ∈ S) (hS : blockedSet hG ω o n = S) {x y : V} (hx : x ∈ S) (h : G.Adj x y)
    (hy : y ∉ S) (hox : OpenConnected G ω (edgesWithin (S : Set V)) o x) :
    ω ∈ pivotalEvent (armEvent G o n) ⟨s(x, y), h⟩ ∧ ω ∉ armEvent G o n := by
  have hSB : ∀ z ∈ S, G.dist o z < n := fun z hz => by
    rw [← hS] at hz; exact (mem_blockedSet.1 hz).1
  have hA : ω ∉ armEvent G o n := notMem_armEvent_of_mem_blockedSet (hS ▸ hoS)
  refine ⟨⟨?_, fun h' => hA (isUpperSet_armEvent o n (update_false_le ω _) h')⟩, hA⟩
  set ω₁ := Function.update ω ⟨s(x, y), h⟩ true
  have hle := le_update_true ω ⟨s(x, y), h⟩
  have hox₁ : OpenConnected G ω₁ (innerEdges G o n) o x :=
    (hox.mono_edges fun e he =>
      Sym2.ind (f := fun e => e ∈ edgesWithin (S : Set V) → e ∈ innerEdges G o n)
        (fun a b hab => ⟨a, Sym2.mem_mk_left a b, hSB a (hab a (Sym2.mem_mk_left a b))⟩)
        e he).mono_config hle
  have hy₁ : ReachesSphere G ω₁ o n y := by
    refine ReachesSphere.mono_config ?_ hle
    by_cases hyn : G.dist o y < n
    · by_contra hns
      have : y ∈ blockedSet hG ω o n := mem_blockedSet.2 ⟨hyn, hns⟩
      rw [hS] at this; exact hy this
    · exact reachesSphere_of_dist_eq (le_antisymm (dist_le_of_adj_of_dist_lt hG h (hSB x hx))
        (not_lt.1 hyn))
  have hxy₁ : ReachesSphere G ω₁ o n x :=
    reachesSphere_of_adj (hSB x hx) h (by simp [ω₁]) hy₁
  show ω₁ ∈ armEvent G o n
  rw [armEvent_eq_reachesSphere hG]
  obtain ⟨w, hw, hxw⟩ := hxy₁
  exact ⟨w, hw, hox₁.trans hxw⟩

/-- Off the arm event, `𝒮` is a set containing `o`: the events `{𝒮 = S}`, `o ∈ S`, partition
the complement of the arm event. -/
theorem compl_armEvent_eq_iUnion {o : V} {n : ℕ} (hn : 1 ≤ n) :
    (armEvent G o n)ᶜ = ⋃ S ∈ (innerBall hG o n).powerset.filter (o ∈ ·),
      {ω | blockedSet hG ω o n = S} := by
  ext ω
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_filter,
    Finset.mem_powerset, exists_prop]
  constructor
  · intro hω
    refine ⟨blockedSet hG ω o n, ⟨fun z hz => (mem_innerBall hG).2 (mem_blockedSet.1 hz).1,
      mem_blockedSet.2 ⟨by simp; omega, ?_⟩⟩, rfl⟩
    rw [armEvent_eq_reachesSphere hG] at hω
    exact hω
  · rintro ⟨S, ⟨-, hoS⟩, hS⟩
    exact notMem_armEvent_of_mem_blockedSet (hS ▸ hoS)

variable [Countable V]

theorem measure_compl_armEvent_eq_sum {o : V} {n : ℕ} (hn : 1 ≤ n) (p : I) :
    percolation G p (armEvent G o n)ᶜ = ∑ S ∈ (innerBall hG o n).powerset.filter (o ∈ ·),
      percolation G p {ω | blockedSet hG ω o n = S} := by
  rw [compl_armEvent_eq_iUnion hn, measure_biUnion_finset]
  · intro S _ T _ hST
    exact Set.disjoint_left.2 fun ω hS hT => hST (hS.symm.trans hT)
  · exact fun S _ => measurableSet_blockedSet_eq o n S

omit [G.LocallyFinite] [Countable V] in
/-- Being pivotal and failing means being pivotal and closed. -/
theorem pivotalEvent_inter_compl_eq (A : Set (G.edgeSet → Bool)) (e : G.edgeSet) :
    pivotalEvent A e ∩ Aᶜ = pivotalEvent A e ∩ {ω | ω e = false} := by
  ext ω
  simp only [pivotalEvent, updateEvent, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq,
    Set.mem_compl_iff]
  constructor
  · rintro ⟨⟨h1, h0⟩, hω⟩
    refine ⟨⟨h1, h0⟩, ?_⟩
    by_contra hne
    have : ω e = true := by simpa using hne
    exact hω (by rwa [Function.update_eq_self_iff.2 this.symm] at h1)
  · rintro ⟨⟨h1, h0⟩, hω⟩
    exact ⟨⟨h1, h0⟩, fun hA' => h0 (by rwa [Function.update_eq_self_iff.2 hω.symm])⟩

omit [Countable V] in
/-- The boundary pairs of `S` inject into the edges, with images among the edges with an endpoint
at distance `< n` when `S` lies at distance `< n`. -/
theorem sum_boundary_le_sum_innerEdges {o : V} {n : ℕ} {S : Finset V}
    (hSB : ∀ z ∈ S, G.dist o z < n) (F : G.edgeSet → ℝ≥0∞) (f : V → ℝ≥0∞)
    (hf : ∀ x ∈ S, ∀ y (h : G.Adj x y), y ∉ S → f x ≤ F ⟨s(x, y), h⟩) :
    ∑ x ∈ S, ∑ _y ∈ (G.neighborFinset x).filter (· ∉ S), f x ≤
      ∑ e ∈ innerEdgeFinset hG o n, F e := by
  classical
  set T := S.sigma fun x => (G.neighborFinset x).filter (· ∉ S)
  let F' : Sym2 V → ℝ≥0∞ := fun z => if h : z ∈ G.edgeSet then F ⟨z, h⟩ else 0
  let g : (Σ _ : V, V) → Sym2 V := fun t => s(t.1, t.2)
  have hT : ∀ t ∈ T, G.Adj t.1 t.2 ∧ t.1 ∈ S ∧ t.2 ∉ S := by
    intro t ht
    simp only [T, Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at ht
    exact ⟨ht.2.1, ht.1, ht.2.2⟩
  calc ∑ x ∈ S, ∑ _y ∈ (G.neighborFinset x).filter (· ∉ S), f x
      = ∑ t ∈ T, f t.1 := (Finset.sum_sigma S _ (fun t => f t.1)).symm
    _ ≤ ∑ t ∈ T, F' (g t) := by
        refine Finset.sum_le_sum fun t ht => ?_
        obtain ⟨hadj, hx, hy⟩ := hT t ht
        simp only [F', g, dite_eq_left (show s(t.1, t.2) ∈ G.edgeSet from hadj)]
        exact hf t.1 hx t.2 hadj hy
    _ = ∑ z ∈ T.image g, F' z := by
        refine (Finset.sum_image fun t ht t' ht' htt => ?_).symm
        obtain ⟨-, hx, hy⟩ := hT t ht
        obtain ⟨-, hx', hy'⟩ := hT t' ht'
        rcases Sym2.eq_iff.1 htt with ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact Sigma.ext h1 (heq_of_eq h2)
        · exact absurd (h1 ▸ hx) hy'
    _ ≤ ∑ z ∈ (innerEdgeFinset hG o n).map (Function.Embedding.subtype _), F' z := by
        refine Finset.sum_le_sum_of_subset fun z hz => ?_
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hz
        obtain ⟨hadj, hx, -⟩ := hT t ht
        refine Finset.mem_map.2 ⟨⟨s(t.1, t.2), hadj⟩, ?_, rfl⟩
        rw [← Finset.mem_coe, coe_innerEdgeFinset]
        exact ⟨t.1, Sym2.mem_mk_left _ _, hSB _ hx⟩
    _ = ∑ e ∈ innerEdgeFinset hG o n, F e := by
        rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp [F', e.2]

/-- **The differential inequality of Duminil-Copin and Tassion** (arXiv:1502.03051, Lemma 2.1),
before Russo's formula: if `φ_p(S) ≥ c` for every `S ∋ o` at distance `< n`, then
`c (1 - P_p(A)) ≤ p (1 - p) ∑_e P_p(e pivotal)` for the arm event `A`. -/
theorem le_mul_sum_pivotal {o : V} {n : ℕ} (hn : 1 ≤ n) (p : I) {c : ℝ}
    (hc : ∀ S : Finset V, o ∈ S → (∀ z ∈ S, G.dist o z < n) → c ≤ phi G p o S) :
    c * (1 - (percolation G p (armEvent G o n)).toReal) ≤
      p * (1 - p) * ∑ e ∈ innerEdgeFinset hG o n,
        (percolation G p (pivotalEvent (armEvent G o n) e)).toReal := by
  set A := armEvent G o n
  set P := percolation G p
  set 𝓕 := (innerBall hG o n).powerset.filter (o ∈ ·)
  have hAm : MeasurableSet A := measurableSet_armEvent o n
  have hSB : ∀ S ∈ 𝓕, ∀ z ∈ S, G.dist o z < n := by
    intro S hS z hz
    simp only [𝓕, Finset.mem_filter, Finset.mem_powerset] at hS
    exact (mem_innerBall hG).1 (hS.1 hz)
  -- the counting inequality, in `ℝ≥0∞`
  have hcount : ∑ S ∈ 𝓕, ∑ x ∈ S, ∑ _y ∈ (G.neighborFinset x).filter (· ∉ S),
      P {ω | blockedSet hG ω o n = S} * P {ω | OpenConnected G ω (edgesWithin (S : Set V)) o x} ≤
      ENNReal.ofReal (1 - p) * ∑ e ∈ innerEdgeFinset hG o n, P (pivotalEvent A e) := by
    calc ∑ S ∈ 𝓕, ∑ x ∈ S, ∑ _y ∈ (G.neighborFinset x).filter (· ∉ S),
          P {ω | blockedSet hG ω o n = S} *
            P {ω | OpenConnected G ω (edgesWithin (S : Set V)) o x}
        ≤ ∑ S ∈ 𝓕, ∑ e ∈ innerEdgeFinset hG o n,
            P (pivotalEvent A e ∩ Aᶜ ∩ {ω | blockedSet hG ω o n = S}) := by
          refine Finset.sum_le_sum fun S hS => sum_boundary_le_sum_innerEdges (hSB S hS) _ _ ?_
          intro x hx y h hy
          have hoS : o ∈ S := (Finset.mem_filter.1 hS).2
          rw [← measure_inter_eq_mul_of_dependsOn (measurableSet_blockedSet_eq o n S)
            (measurableSet_openConnected _ o x) (dependsOn_blockedSet_eq o n S)
            (dependsOn_openConnected _ o x) ?_ p]
          · refine measure_mono fun ω ⟨hS', hox⟩ => ?_
            obtain ⟨hpiv, hA⟩ := mem_pivotalEvent_of_blockedSet hoS hS' hx h hy hox
            exact ⟨⟨hpiv, hA⟩, hS'⟩
          · rw [Set.disjoint_left]
            exact fun e he he' => he.2 he'
      _ = ∑ e ∈ innerEdgeFinset hG o n, ∑ S ∈ 𝓕,
            P (pivotalEvent A e ∩ Aᶜ ∩ {ω | blockedSet hG ω o n = S}) := Finset.sum_comm
      _ ≤ ∑ e ∈ innerEdgeFinset hG o n, P (pivotalEvent A e ∩ Aᶜ) := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [← measure_biUnion_finset]
          · exact measure_mono (Set.iUnion₂_subset fun S _ => Set.inter_subset_left)
          · intro S _ T _ hST
            exact Set.disjoint_left.2 fun ω hS hT => hST (hS.2.symm.trans hT.2)
          · intro S _
            exact (((measurableSet_updateEvent hAm e true).diff
              (measurableSet_updateEvent hAm e false)).inter hAm.compl).inter
              (measurableSet_blockedSet_eq o n S)
      _ = ENNReal.ofReal (1 - p) * ∑ e ∈ innerEdgeFinset hG o n, P (pivotalEvent A e) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [pivotalEvent_inter_compl_eq,
            bernoulliProduct_pivotalEvent_inter_false hAm]
  -- to real numbers
  have hcount' : ∑ S ∈ 𝓕, (P {ω | blockedSet hG ω o n = S}).toReal *
      (∑ x ∈ S, ∑ _y ∈ (G.neighborFinset x).filter (· ∉ S),
        (P {ω | OpenConnected G ω (edgesWithin (S : Set V)) o x}).toReal) ≤
      (1 - p) * ∑ e ∈ innerEdgeFinset hG o n, (P (pivotalEvent A e)).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.2 fun e _ => measure_ne_top _ _)) hcount
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [p.2.2]),
      ENNReal.toReal_sum fun e _ => measure_ne_top _ _] at h
    refine le_of_eq_of_le ?_ h
    rw [ENNReal.toReal_sum fun S _ => ENNReal.sum_ne_top.2 fun x _ =>
      ENNReal.sum_ne_top.2 fun y _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [ENNReal.toReal_sum fun x _ => ENNReal.sum_ne_top.2 fun y _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_sum fun y _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ENNReal.toReal_mul]
  -- the complement of the arm event
  have hcompl : 1 - (P A).toReal = ∑ S ∈ 𝓕, (P {ω | blockedSet hG ω o n = S}).toReal := by
    rw [← ENNReal.toReal_sum fun S _ => measure_ne_top _ _, ← measure_compl_armEvent_eq_sum hn,
      prob_compl_eq_one_sub hAm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  rw [hcompl, Finset.mul_sum]
  calc ∑ S ∈ 𝓕, c * (P {ω | blockedSet hG ω o n = S}).toReal
      ≤ ∑ S ∈ 𝓕, (P {ω | blockedSet hG ω o n = S}).toReal * phi G p o S := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left
          (hc S (Finset.mem_filter.1 hS).2 (hSB S hS)) ENNReal.toReal_nonneg
    _ = p * ∑ S ∈ 𝓕, (P {ω | blockedSet hG ω o n = S}).toReal *
          (∑ x ∈ S, ∑ _y ∈ (G.neighborFinset x).filter (· ∉ S),
            (P {ω | OpenConnected G ω (edgesWithin (S : Set V)) o x}).toReal) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [phi]; ring
    _ ≤ p * ((1 - p) * ∑ e ∈ innerEdgeFinset hG o n, (P (pivotalEvent A e)).toReal) :=
        mul_le_mul_of_nonneg_left hcount' p.2.1
    _ = p * (1 - p) * ∑ e ∈ innerEdgeFinset hG o n, (P (pivotalEvent A e)).toReal := by ring

/-! ### Integrating the differential inequality -/

/-- The probability polynomial of the arm event (Russo's formula applies to it). -/
noncomputable def armPoly (hG : G.Connected) (o : V) (n : ℕ) : ℝ → ℝ :=
  cylinderPoly (innerEdgeFinset hG o n) (armEvent G o n)

theorem toReal_percolation_armEvent_eq_armPoly (o : V) (n : ℕ) (p : I) :
    (percolation G p (armEvent G o n)).toReal = armPoly hG o n p :=
  toReal_bernoulliProduct_eq_cylinderPoly _ (measurableSet_armEvent o n)
    (dependsOn_armEvent_innerEdgeFinset o n) p

/-- The differential inequality in derivative form, at `c = 1`. -/
theorem armPoly_deriv_ge {o : V} {n : ℕ} (hn : 1 ≤ n) (p : I)
    (hφ : ∀ S : Finset V, o ∈ S → (∀ z ∈ S, G.dist o z < n) → 1 ≤ phi G p o S) :
    ∃ f' : ℝ, HasDerivAt (armPoly hG o n) f' p ∧
      (1 - armPoly hG o n p) ≤ p * (1 - p) * f' := by
  refine ⟨_, hasDerivAt_cylinderPoly_eq_sum_pivotal _ (measurableSet_armEvent o n)
    (dependsOn_armEvent_innerEdgeFinset o n) (isUpperSet_armEvent o n) p, ?_⟩
  have h := le_mul_sum_pivotal (hG := hG) hn p hφ
  rw [one_mul, toReal_percolation_armEvent_eq_armPoly] at h
  exact h

/-- **The mean-field lower bound in finite volume** ([Duminil-Copin and Tassion, §2.2]): if
`φ_p(S) ≥ 1` for every `S ∋ o` and every `p ∈ (q, p₁)`, then
`P_{p₁}(o ↔ distance n) ≥ (p₁ - q)/(p₁ (1 - q))` for every `n`. -/
theorem le_toReal_percolation_armEvent (hG : G.Connected) {o : V} (n : ℕ) {q : ℝ} {p₁ : I}
    (hq : 0 < q)
    (hqp : q ≤ p₁) (hp₁ : (p₁ : ℝ) < 1)
    (hφ : ∀ p : I, q < p → (p : ℝ) < p₁ → ∀ S : Finset V, o ∈ S → 1 ≤ phi G p o S) :
    (p₁ - q) / (p₁ * (1 - q)) ≤ (percolation G p₁ (armEvent G o n)).toReal := by
  have hq1 : q < 1 := hqp.trans_lt hp₁
  have hp₁0 : 0 < (p₁ : ℝ) := hq.trans_le hqp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [armEvent_zero, measure_univ, ENNReal.toReal_one, div_le_one (by
      have : 0 < 1 - q := by linarith
      positivity)]
    nlinarith
  set f := armPoly hG o n
  set u : ℝ → ℝ := fun x => (1 - f x) * (x / (1 - x))
  have hfc : Continuous f := continuous_cylinderPoly _ _
  -- the derivative of `u` is nonpositive on `(q, p₁)`
  have hderiv : ∀ x ∈ Set.Ioo q (p₁ : ℝ), ∃ u' : ℝ, HasDerivAt u u' x ∧ u' ≤ 0 := by
    intro x ⟨hqx, hxp⟩
    have hx0 : 0 < x := hq.trans hqx
    have hx1 : x < 1 := hxp.trans hp₁
    set xI : I := ⟨x, hx0.le, hx1.le⟩
    obtain ⟨f', hf', hle⟩ := armPoly_deriv_ge (hG := hG) hn xI
      fun S hoS _ => hφ xI hqx hxp S hoS
    have hf'' : HasDerivAt f f' x := hf'
    have hle' : 1 - f x ≤ x * (1 - x) * f' := hle
    have h1x : (1 - x) ≠ 0 := by linarith
    have hdiv : HasDerivAt (fun y => y / (1 - y)) (1 / (1 - x) ^ 2) x :=
      ((hasDerivAt_id' x).div ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id' x)) h1x).congr_deriv
        (by simp only [Pi.sub_apply]; field_simp; ring)
    have hu : HasDerivAt u (-f' * (x / (1 - x)) + (1 - f x) * (1 / (1 - x) ^ 2)) x :=
      (((hasDerivAt_const x (1 : ℝ)).sub hf'').mul hdiv).congr_deriv
        (by simp only [Pi.sub_apply]; ring)
    refine ⟨_, hu, ?_⟩
    have h1x' : 0 < 1 - x := by linarith
    have key : -f' * (x / (1 - x)) + (1 - f x) * (1 / (1 - x) ^ 2) =
        ((1 - f x) - x * (1 - x) * f') / (1 - x) ^ 2 := by
      field_simp; ring
    rw [key]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hanti : AntitoneOn u (Set.Icc q p₁) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · refine ((continuous_const.sub hfc).continuousOn).mul ?_
      refine continuousOn_id.div (continuousOn_const.sub continuousOn_id) fun x hx => ?_
      have : x < 1 := hx.2.trans_lt hp₁
      linarith
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨u', hu', -⟩ := hderiv x hx
      exact hu'.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨u', hu', hle⟩ := hderiv x hx
      rw [hu'.deriv]; exact hle
  have hmono := hanti ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
  -- `u q ≤ q / (1 - q)`
  set qI : I := ⟨q, hq.le, hq1.le⟩
  have hfq : 0 ≤ f q := by
    have : f qI = (percolation G qI (armEvent G o n)).toReal :=
      (toReal_percolation_armEvent_eq_armPoly o n qI).symm
    exact this ▸ ENNReal.toReal_nonneg
  have hfp : f p₁ = (percolation G p₁ (armEvent G o n)).toReal :=
    (toReal_percolation_armEvent_eq_armPoly o n p₁).symm
  rw [← hfp]
  have hq1' : 0 < 1 - q := by linarith
  have hp1' : 0 < 1 - (p₁ : ℝ) := by linarith
  simp only [u] at hmono
  have h1 : (1 - f p₁) * (p₁ / (1 - p₁)) ≤ q / (1 - q) :=
    hmono.trans (by
      have : 0 ≤ q / (1 - q) := by positivity
      nlinarith [div_nonneg hq.le hq1'.le])
  rw [div_le_iff₀ (by positivity)]
  rw [mul_div_assoc', div_le_div_iff₀ hp1' hq1'] at h1
  nlinarith

/-- **The mean-field lower bound** ([Duminil-Copin and Tassion, Theorem 1.1(2), with `q` in place
of `p̃_c`]): the cluster of `o` is infinite with probability at least `(p₁ - q)/(p₁ (1 - q))`. -/
theorem le_percolation_infinite (hG : G.Connected) {o : V} {q : ℝ} {p₁ : I} (hq : 0 < q)
    (hqp : q ≤ p₁)
    (hp₁ : (p₁ : ℝ) < 1)
    (hφ : ∀ p : I, q < p → (p : ℝ) < p₁ → ∀ S : Finset V, o ∈ S → 1 ≤ phi G p o S) :
    ENNReal.ofReal ((p₁ - q) / (p₁ * (1 - q))) ≤
      percolation G p₁ {ω | {x | OpenConnected G ω Set.univ o x}.Infinite} := by
  rw [setOf_infinite_eq_iInter_armEvent hG]
  have ht := tendsto_measure_iInter_atTop (μ := percolation G p₁)
    (fun n => (measurableSet_armEvent (G := G) o n).nullMeasurableSet) (armEvent_antitone o)
    ⟨0, measure_ne_top _ _⟩
  refine ge_of_tendsto' ht fun n => ?_
  show _ ≤ percolation G p₁ (armEvent G o n)
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  exact le_toReal_percolation_armEvent hG n hq hqp hp₁ hφ

end Pivotal

end CurvatureVariance.Infra.Percolation
