/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
public import CurvatureVariance.Infra.Geodesics.Basic
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import CurvatureVariance.Infra.FPP.Walks
import CurvatureVariance.Statements.Inputs.MeasureExistsIsPathWalkCostLtLe

/-!
# Slab geodesics and the locality of slab passage times

Deterministic and almost sure facts about the slab passage times `D_{p,q}` used in the proofs of
Lemma `lem:blocks` (the tube property stated before it, and the vanishing of the term of a block `G`
in `Y_i(j,k)` when no geodesic of the old weights uses `G`) and of Lemmas `lem:residual` and
`lem:fewtranslates`.

* `exists_isPath_walkCost_eq_restrictedTime`: deterministically, if from `u` every long
  self-avoiding path is expensive (the conclusion of Kesten's estimate after Borel–Cantelli), then
  every finite restricted passage time from `u` is attained by a self-avoiding path with edges in
  the allowed set. As in `Infra.Geodesics.exists_isPath_walkCost_eq_passageTime`; the
  restriction to an edge set is preserved by loop erasure (`Walk.edges_bypass_subset_edges`).
* `ae_exists_isSlabGeodesic`: almost surely, every finite slab passage time is attained by a slab
  geodesic (`IsSlabGeodesic`); `ae_exists_isSlabGeodesic_of_mem`: in particular for both endpoints
  in a closed slab of width at least two. By Kesten's bound (the text after equation
  `eq:classical`): `CurvatureVariance.measure_exists_isPath_walkCost_lt_le` and
  `Infra.Geodesics.ae_eventually_le_walkCost_of_kesten`.
* `slabTime_le_of_isSlabGeodesic`: if `ω'` agrees with `ω` on the edges of an `ω`-slab geodesic
  from `u` to `v`, then `D_{p,q}(ω')(u, v) ≤ D_{p,q}(ω)(u, v)`; `slabTime_le_of_forall_notMem` for a
  set `G` of edges avoided by the geodesic, off which `ω'` agrees with `ω`.
* Blocks and fine cubes: `blockIndices L o g` (the fine-cube indices `Lg + o + {0,…,L−1}^{d−1}` of a
  block), `mem_block_iff` (an edge of the slab is in the block iff its fine-cube index is),
  `blockOf L o j` (the block containing the fine cube `j`, `L ≥ 1`) and
  `mem_blockIndices_iff_blockOf_eq`.
* `slabTime_le_of_disjoint_tube`: the vanishing of a block's response when the fine cubes of the
  block miss a set of indices containing the fine cubes of every old slab geodesic between two
  sets of endpoints (the tube of `Contracts.TubeStatement`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set SimpleGraph
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Restricted geodesics, deterministically -/

/-- The infimum defining a restricted passage time is finite only if some walk uses allowed edges
only. -/
theorem exists_walk_of_restrictedTime_ne_top {ω : Config m} {E : Set (Sym2 (Vertex m))}
    {u v : Vertex m} (h : restrictedTime ω E u v ≠ ⊤) :
    ∃ γ : (latticeGraph m).Walk u v, ∀ e ∈ γ.edges, e ∈ E := by
  by_contra hne
  push Not at hne
  apply h
  unfold restrictedTime
  refine le_antisymm le_top (le_iInf₂ fun γ hγ => ?_)
  obtain ⟨e, he, heE⟩ := hne γ
  exact absurd (hγ e he) heE

/-- **Restricted geodesics exist, deterministically**: if, from `u`, eventually in `n` every
self-avoiding path with at least `n` edges costs at least `a n` (`a > 0`), then every finite
restricted passage time from `u` is the cost of a self-avoiding path with all edges in `E`. -/
theorem exists_isPath_walkCost_eq_restrictedTime {ω : Config m} {a : ℝ} (ha : 0 < a)
    {u : Vertex m}
    (hω : ∀ᶠ n in atTop, ∀ (v : Vertex m) (γ : (latticeGraph m).Walk u v),
      γ.IsPath → n ≤ γ.length → a * n ≤ walkCost ω γ)
    (E : Set (Sym2 (Vertex m))) {v : Vertex m} (hfin : restrictedTime ω E u v ≠ ⊤) :
    ∃ γ : (latticeGraph m).Walk u v, γ.IsPath ∧ (∀ e ∈ γ.edges, e ∈ E) ∧
      (walkCost ω γ : ℝ≥0∞) = restrictedTime ω E u v := by
  classical
  obtain ⟨q, hqE⟩ := exists_walk_of_restrictedTime_ne_top hfin
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hω
  set n : ℕ := max n₀ (⌈(walkCost ω q : ℝ) / a⌉₊ + 1)
  have hqn : (walkCost ω q : ℝ) < a * n := by
    have h1 : (walkCost ω q : ℝ) / a < n :=
      calc (walkCost ω q : ℝ) / a ≤ ⌈(walkCost ω q : ℝ) / a⌉₊ := Nat.le_ceil _
        _ < ⌈(walkCost ω q : ℝ) / a⌉₊ + 1 := lt_add_one _
        _ ≤ n := by exact_mod_cast le_max_right _ _
    rwa [div_lt_iff₀ ha, mul_comm] at h1
  have hlong := hn₀ n (le_max_left _ _) v
  -- the finite set of candidates: the short self-avoiding paths with allowed edges
  set S := ((latticeGraph m).finsetWalkLengthLT n u v).filter
    (fun r => r.IsPath ∧ ∀ e ∈ r.edges, e ∈ E)
  have hred : ∀ r : (latticeGraph m).Walk u v, (∀ e ∈ r.edges, e ∈ E) →
      r.bypass ∈ S ∨ (walkCost ω q : ℝ) < walkCost ω r := by
    intro r hr
    by_cases hl : r.bypass.length < n
    · exact Or.inl (Finset.mem_filter.2 ⟨(mem_finsetWalkLengthLT_iff).2 hl,
        r.bypass_isPath, fun e he => hr e (r.edges_bypass_subset_edges he)⟩)
    · refine Or.inr (hqn.trans_le ((hlong _ r.bypass_isPath (not_lt.1 hl)).trans ?_))
      exact_mod_cast Infra.Geodesics.walkCost_bypass_le ω r
  have hqS : q.bypass ∈ S := (hred q hqE).resolve_right (lt_irrefl _)
  obtain ⟨p, hpS, hmin⟩ := S.exists_min_image (fun r => walkCost ω r) ⟨_, hqS⟩
  have hp : ∀ r : (latticeGraph m).Walk u v, (∀ e ∈ r.edges, e ∈ E) →
      walkCost ω p ≤ walkCost ω r := by
    intro r hr
    rcases hred r hr with h | h
    · exact (hmin _ h).trans (Infra.Geodesics.walkCost_bypass_le ω r)
    · refine ((hmin _ hqS).trans (Infra.Geodesics.walkCost_bypass_le ω q)).trans ?_
      exact_mod_cast h.le
  have hpS' := (Finset.mem_filter.1 hpS).2
  refine ⟨p, hpS'.1, hpS'.2, le_antisymm ?_ (iInf₂_le p hpS'.2)⟩
  exact le_iInf₂ fun r hr => by exact_mod_cast hp r hr

/-! ### Slab geodesics exist almost surely -/

/-- **Slab geodesics exist almost surely**: under the
standing hypotheses, almost surely, for all `p, q` and all vertices `u, v` with
`D_{p,q}(u, v) < ∞`, there is a slab geodesic from `u` to `v`. -/
theorem ae_exists_isSlabGeodesic {M : Model m} (hM : M.Standing) :
    ∀ᵐ ω ∂M.P, ∀ (p q : ℤ) (u v : Vertex m), slabTime ω p q u v ≠ ⊤ →
      ∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω p q γ := by
  have := hM.probF
  have := hM.probP
  obtain ⟨a, C₉, ha, hC₉, hK⟩ :=
    CurvatureVariance.measure_exists_isPath_walkCost_lt_le hM.one_le_m M.F hM.assumptionW.2
  filter_upwards [Infra.Geodesics.ae_eventually_le_walkCost_of_kesten hC₉ hK M.P hM.iid]
    with ω hω p q u v hfin
  obtain ⟨γ, hγ, hE, hc⟩ :=
    exists_isPath_walkCost_eq_restrictedTime ha (hω u) (slabEdges p q) hfin
  exact ⟨γ, hγ, hE, hc⟩

/-- **Slab geodesics exist almost surely, for endpoints in a closed slab**: almost surely, for every
slab `[p, q]` of width at least two and all vertices `u, v` of the closed slab, there is a slab
geodesic from `u` to `v`. -/
theorem ae_exists_isSlabGeodesic_of_mem {M : Model m} (hM : M.Standing) :
    ∀ᵐ ω ∂M.P, ∀ (p q : ℤ), p + 2 ≤ q → ∀ u v : Vertex m, p ≤ u.1 ∧ u.1 ≤ q →
      p ≤ v.1 ∧ v.1 ≤ q → ∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω p q γ := by
  filter_upwards [ae_exists_isSlabGeodesic hM] with ω hω p q hpq u v hu hv
  exact hω p q u v (Responses.slabTime_ne_top ω hpq hu hv)

/-! ### Locality of slab passage times -/

/-- A slab geodesic has finite slab passage time. -/
theorem slabTime_ne_top_of_isSlabGeodesic {ω : Config m} {p q : ℤ} {u v : Vertex m}
    {γ : (latticeGraph m).Walk u v} (hγ : IsSlabGeodesic ω p q γ) : slabTime ω p q u v ≠ ⊤ := by
  rw [← hγ.2.2]
  exact ENNReal.coe_ne_top

/-- **Locality**: if `ω'` agrees with `ω` on the edges of an `ω`-slab geodesic `γ` from `u` to
`v`, then `D_{p,q}(ω')(u, v) ≤ D_{p,q}(ω)(u, v)`. -/
theorem slabTime_le_of_isSlabGeodesic {ω ω' : Config m} {p q : ℤ} {u v : Vertex m}
    {γ : (latticeGraph m).Walk u v} (hγ : IsSlabGeodesic ω p q γ)
    (h : ∀ e : Edge m, e.1 ∈ γ.edges → ω' e = ω e) :
    slabTime ω' p q u v ≤ slabTime ω p q u v := by
  rw [← hγ.2.2]
  refine (iInf₂_le γ hγ.2.1).trans_eq ?_
  exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (Infra.FPP.walkCost_congr ω' γ fun e he => h e he)

/-- **Locality for a set of edges**: if an `ω`-slab geodesic from `u` to `v` uses no edge of `G` and
`ω'` agrees with `ω` off `G`, then `D_{p,q}(ω')(u, v) ≤ D_{p,q}(ω)(u, v)`. -/
theorem slabTime_le_of_forall_notMem {ω ω' : Config m} {p q : ℤ} {u v : Vertex m}
    {γ : (latticeGraph m).Walk u v} (hγ : IsSlabGeodesic ω p q γ) {G : Set (Sym2 (Vertex m))}
    (hG : ∀ e ∈ γ.edges, e ∉ G) (h : ∀ e : Edge m, e.1 ∉ G → ω' e = ω e) :
    slabTime ω' p q u v ≤ slabTime ω p q u v :=
  slabTime_le_of_isSlabGeodesic hγ fun e he => h e (hG e.1 he)

/-! ### Blocks and fine cubes -/

/-- The fine-cube indices `L g + o + {0, …, L−1}^{d−1}` of the block `g` with offset `o` (Section
`sec:gain`, where the fine cubes are the cells). -/
def blockIndices (L : ℕ) (o g : Fin m → ℤ) : Set (Fin m → ℤ) :=
  {j | ∀ k, (L : ℤ) * g k + o k ≤ j k ∧ j k < (L : ℤ) * g k + o k + L}

/-- An edge is in the block `g` of slab `i` iff it is an edge of the slab whose fine-cube index is
an index of the block. -/
theorem mem_block_iff {n w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {i : ℕ} {o g : Fin m → ℤ}
    {e : Sym2 (Vertex m)} :
    e ∈ block n w L t i o g ↔ e ∈ slabEdges (((i : ℤ) - 1) * n) ((i : ℤ) * n) ∧
      fineIndex w t (edgeMid e) ∈ blockIndices L o g :=
  Iff.rfl

/-- The block containing the fine cube `j` (for `L ≥ 1`): `⌊(j − o)/L⌋`, coordinatewise. -/
def blockOf (L : ℕ) (o j : Fin m → ℤ) : Fin m → ℤ :=
  fun k => (j k - o k) / (L : ℤ)

/-- For `L ≥ 1`, the fine cube `j` is an index of the block `g` iff `g` is its block. -/
theorem mem_blockIndices_iff_blockOf_eq {L : ℕ} (hL : 1 ≤ L) (o g j : Fin m → ℤ) :
    j ∈ blockIndices L o g ↔ blockOf L o j = g := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have key : ∀ k, ((L : ℤ) * g k + o k ≤ j k ∧ j k < (L : ℤ) * g k + o k + L) ↔
      (j k - o k) / (L : ℤ) = g k := by
    intro k
    have e1 : (j k - o k) / (L : ℤ) ≤ g k ↔ j k - o k < (g k + 1) * L := by
      rw [← Int.lt_add_one_iff, Int.ediv_lt_iff_lt_mul hL']
    have e2 : g k ≤ (j k - o k) / (L : ℤ) ↔ g k * L ≤ j k - o k := Int.le_ediv_iff_mul_le hL'
    rw [le_antisymm_iff, e1, e2]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [blockIndices, Set.mem_ofPred_eq, key, blockOf, funext_iff]

/-! ### Blocks missing the tube -/

/-- **A block missing the tube does not raise slab passage times** (the text before Lemma
`lem:blocks`): let `T` be a set of fine-cube indices containing the fine cube of every edge of
every `ω`-slab geodesic of slab `i` (the slab `[(i−1)n, in]`) from `u` to `v`, and let such a
geodesic exist. If the block `g` has no fine cube in `T` and `ω'` agrees with `ω` off the block,
then `D_i(ω')(u, v) ≤ D_i(ω)(u, v)`. -/
theorem slabTime_le_of_disjoint_tube {ω ω' : Config m} {n w L : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {i : ℕ} {o g : Fin m → ℤ} {T : Set (Fin m → ℤ)}
    {u v : Vertex m}
    (hgeo : ∃ γ : (latticeGraph m).Walk u v,
      IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ)
    (htube : ∀ γ : (latticeGraph m).Walk u v,
      IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
      ∀ e ∈ γ.edges, fineIndex w t (edgeMid e) ∈ T)
    (hdisj : Disjoint (blockIndices L o g) T)
    (hω' : ∀ e : Edge m, e.1 ∉ block n w L t i o g → ω' e = ω e) :
    slabTime ω' (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v ≤
      slabTime ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v := by
  obtain ⟨γ, hγ⟩ := hgeo
  refine slabTime_le_of_forall_notMem hγ (fun e he hblock => ?_) hω'
  exact Set.disjoint_left.1 hdisj (mem_block_iff.1 hblock).2 (htube γ hγ e he)

end CurvatureVariance.Paper.Gain
