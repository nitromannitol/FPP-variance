/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Lattice.WalkCost
public import CurvatureVariance.Infra.Kesten.BadBlocks

/-!
# A cheap long path meets many bad blocks

The deterministic half of the block argument for Kesten's estimate. Fix the block side
`L ≥ 1` and a level `ε > 0`, call an edge open when its weight is at most `ε`, and let `Z` be the
set of blocks visited by a self-avoiding path `γ` from the origin with `n ≤ #γ` edges,
`n ≥ (3L)^d`.

* `closedDart_or_badBlock`: from every visited block `B(z)` the path reaches `ℓ^∞` distance `L`;
  either the first such excursion is open, and `B(z)` is bad, or the path crosses an edge of weight
  more than `ε` with an endpoint in a block next to `z`.
* `card_good_le`: so the good visited blocks number at most `2·3^d` times the closed edges of `γ`,
  and these number at most `walkCost ω γ / ε` (`mul_card_closedDarts_le_walkCost`).
* `card_le_two_mul_card_bad`: if `walkCost ω γ < a n` with `a = ε / (4·3^d L^d)`, more than half
  of the visited blocks are bad, and `n + 1 ≤ |Z| L^d`.
-/

@[expose] public section

open Finset
open scoped NNReal

namespace CurvatureVariance.Infra.Kesten

open CurvatureVariance.Infra.Percolation

variable {m : ℕ}

/-! ### Costs -/

/-- Deleting darts cannot increase a cost (the weights are nonnegative). -/
theorem walkCost_le_of_darts_sublist (ω : Config m) {u v x y : Vertex m}
    (p : (latticeGraph m).Walk u v) (q : (latticeGraph m).Walk x y)
    (h : p.darts.Sublist q.darts) : walkCost ω p ≤ walkCost ω q := by
  unfold walkCost
  exact (h.map (fun t => ω ⟨t.edge, t.edge_mem⟩)).sum_le_sum fun _ _ => bot_le

/-- The closed darts of a walk: those whose edge has weight more than `ε`. -/
noncomputable def closedDarts (ω : Config m) (ε : ℝ≥0) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) : Finset (latticeGraph m).Dart := by
  classical
  exact γ.darts.toFinset.filter fun d => ε < ω ⟨d.edge, d.edge_mem⟩

/-- The closed darts of `γ` are its darts of weight more than `ε`. -/
theorem mem_closedDarts {ω : Config m} {ε : ℝ≥0} {u v : Vertex m} {γ : (latticeGraph m).Walk u v}
    {d : (latticeGraph m).Dart} :
    d ∈ closedDarts ω ε γ ↔ d ∈ γ.darts ∧ ε < ω ⟨d.edge, d.edge_mem⟩ := by
  unfold closedDarts
  simp

/-- A self-avoiding path costs at least `ε` times its number of closed edges. -/
theorem mul_card_closedDarts_le_walkCost (ω : Config m) (ε : ℝ≥0) {u v : Vertex m}
    {γ : (latticeGraph m).Walk u v} (hγ : γ.IsPath) :
    ε * (closedDarts ω ε γ).card ≤ walkCost ω γ := by
  classical
  have hnd : γ.darts.Nodup := SimpleGraph.Walk.darts_nodup_of_support_nodup hγ.support_nodup
  have hsum : walkCost ω γ = ∑ d ∈ γ.darts.toFinset, ω ⟨d.edge, d.edge_mem⟩ := by
    rw [walkCost, List.sum_toFinset _ hnd]
  rw [hsum]
  calc ε * (closedDarts ω ε γ).card = ∑ _d ∈ closedDarts ω ε γ, ε := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ d ∈ closedDarts ω ε γ, ω ⟨d.edge, d.edge_mem⟩ := by
        exact Finset.sum_le_sum fun d hd => (mem_closedDarts.1 hd).2.le
    _ ≤ ∑ d ∈ γ.darts.toFinset, ω ⟨d.edge, d.edge_mem⟩ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => bot_le
        intro d hd
        exact List.mem_toFinset.2 (mem_closedDarts.1 hd).1

/-! ### One visited block -/

/-- **The first exit from a block.** Let `q` be a walk from `x ∈ B(z)` whose darts are darts of
`γ` up to orientation, and which reaches `ℓ^∞` distance `L` from `x`. Either `B(z)` is bad for the
`ε`-open edges, or `γ` crosses an edge of weight more than `ε` with an endpoint in a block next to
`z`. -/
theorem closedDart_or_badBlock_of_walk {L : ℕ} (hL : 1 ≤ L) (ω : Config m) (ε : ℝ≥0)
    {u v : Vertex m} (γ : (latticeGraph m).Walk u v) {x x' z : Vertex m} (hxz : block L x = z)
    (q : (latticeGraph m).Walk x x') (hq : ∀ d ∈ q.darts, d ∈ γ.darts ∨ d.symm ∈ γ.darts)
    (hfar : ∃ w ∈ q.support, L ≤ latticeSupNorm (w - x)) :
    openConfig ε ω ∈ badBlock L z ∨
      ∃ d ∈ γ.darts, ε < ω ⟨d.edge, d.edge_mem⟩ ∧
        (latticeSupNorm (block L d.fst - z) ≤ 1 ∨ latticeSupNorm (block L d.snd - z) ≤ 1) := by
  classical
  have hL0 : 0 < L := hL
  have hs : ¬ L ≤ latticeSupNorm (x - x) := by simp [latticeSupNorm_zero]; omega
  obtain ⟨y, r, hy, hpre, hnear, y', hy', hadj⟩ :=
    exists_prefix_exit (far := fun w => L ≤ latticeSupNorm (w - x)) q hs hfar
  by_cases hopen : ∀ d ∈ r.darts, ω ⟨d.edge, d.edge_mem⟩ ≤ ε
  · left
    have hx : x ∈ blockFinset L z := (mem_blockFinset hL0).2 hxz
    simp only [badBlock, Set.mem_iUnion]
    refine ⟨x, hx, y, ?_, r, fun d hd => ⟨⟨d.fst, ?_, ?_⟩, ?_⟩⟩
    · have h1 := latticeSupNorm_sub_le y y' x
      have h2 := latticeSupNorm_sub_le_one_of_adj hadj
      simp only [not_le] at hy'
      simp only [Set.mem_ofPred_eq]
      omega
    · rw [SimpleGraph.Dart.edge, Sym2.mem_iff]; exact Or.inl rfl
    · simpa using hnear d hd
    · simpa [openConfig] using hopen d hd
  · right
    push Not at hopen
    obtain ⟨d, hd, hdε⟩ := hopen
    have hdq : d ∈ q.darts := hpre.subset hd
    have hblock : latticeSupNorm (block L d.fst - z) ≤ 1 := by
      have hn := hnear d hd
      simp only [not_le] at hn
      rw [← hxz]
      exact latticeSupNorm_block_sub_le_one hL0 hn.le
    rcases hq d hdq with hγ | hγ
    · exact ⟨d, hγ, hdε, Or.inl hblock⟩
    · refine ⟨d.symm, hγ, by simpa [SimpleGraph.Dart.edge_symm] using hdε, Or.inr ?_⟩
      simpa using hblock

/-- **Every visited block is bad, or the path crosses a nearby closed edge**, once the path visits
more than `3^d` blocks. -/
theorem closedDart_or_badBlock {L : ℕ} (hL : 1 ≤ L) (ω : Config m) (ε : ℝ≥0)
    {u v : Vertex m} (γ : (latticeGraph m).Walk u v)
    (hZ : 3 ^ (m + 1) < (γ.support.toFinset.image (block L)).card) {z : Vertex m}
    (hz : z ∈ γ.support.toFinset.image (block L)) :
    openConfig ε ω ∈ badBlock L z ∨
      ∃ d ∈ γ.darts, ε < ω ⟨d.edge, d.edge_mem⟩ ∧
        (latticeSupNorm (block L d.fst - z) ≤ 1 ∨ latticeSupNorm (block L d.snd - z) ≤ 1) := by
  classical
  have hL0 : 0 < L := hL
  obtain ⟨x, hx, hxz⟩ := Finset.mem_image.1 hz
  rw [List.mem_toFinset] at hx
  -- some vertex of the path is far from `x`
  obtain ⟨w, hw, hwx⟩ : ∃ w ∈ γ.support, L ≤ latticeSupNorm (w - x) := by
    by_contra hcon
    push Not at hcon
    have hsub : γ.support.toFinset.image (block L) ⊆
        (γ.support.toFinset.image (block L)).filter fun y => latticeSupNorm (y - z) ≤ 1 := by
      intro y hy
      refine Finset.mem_filter.2 ⟨hy, ?_⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
      rw [← hxz]
      exact latticeSupNorm_block_sub_le_one hL0 (hcon w (List.mem_toFinset.1 hw)).le
    have := (Finset.card_le_card hsub).trans (card_filter_latticeSupNorm_sub_le _ z 1)
    norm_num at this
    omega
  have hsplit := γ.take_spec hx
  rw [← hsplit, SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hw | hw
  · -- the far vertex comes before `x`: walk backwards
    refine closedDart_or_badBlock_of_walk hL ω ε γ hxz (γ.takeUntil x hx).reverse ?_
      ⟨w, by simpa using hw, hwx⟩
    intro d hd
    rw [SimpleGraph.Walk.darts_reverse, List.mem_reverse, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    right
    simpa using γ.darts_takeUntil_subset_darts hx hd'
  · refine closedDart_or_badBlock_of_walk hL ω ε γ hxz (γ.dropUntil x hx)
      (fun d hd => Or.inl (γ.darts_dropUntil_subset_darts hx hd)) ⟨w, hw, hwx⟩

/-! ### Counting -/

open Classical in
/-- **The good visited blocks number at most `2·3^d` times the closed edges of the path.** -/
theorem card_good_le {L : ℕ} (hL : 1 ≤ L) (ω : Config m) (ε : ℝ≥0) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v)
    (hZ : 3 ^ (m + 1) < (γ.support.toFinset.image (block L)).card) :
    ((γ.support.toFinset.image (block L)).filter fun z => openConfig ε ω ∉ badBlock L z).card ≤
      2 * 3 ^ (m + 1) * (closedDarts ω ε γ).card := by
  classical
  set Z := γ.support.toFinset.image (block L)
  have hsub : Z.filter (fun z => openConfig ε ω ∉ badBlock L z) ⊆
      (closedDarts ω ε γ).biUnion fun d =>
        cubeFinset (block L d.fst) 1 ∪ cubeFinset (block L d.snd) 1 := by
    intro z hz
    obtain ⟨hzZ, hgood⟩ := Finset.mem_filter.1 hz
    rcases closedDart_or_badBlock hL ω ε γ hZ hzZ with hbad | ⟨d, hd, hdε, hnear⟩
    · exact absurd hbad hgood
    refine Finset.mem_biUnion.2 ⟨d, ?_, ?_⟩
    · exact mem_closedDarts.2 ⟨hd, hdε⟩
    · rcases hnear with h | h
      · exact Finset.mem_union_left _ (mem_cubeFinset (by rwa [latticeSupNorm_sub_comm]))
      · exact Finset.mem_union_right _ (mem_cubeFinset (by rwa [latticeSupNorm_sub_comm]))
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ d ∈ closedDarts ω ε γ,
        (cubeFinset (block L d.fst) 1 ∪ cubeFinset (block L d.snd) 1).card
      ≤ ∑ _d ∈ closedDarts ω ε γ, 2 * 3 ^ (m + 1) := by
        refine Finset.sum_le_sum fun d _ => (Finset.card_union_le _ _).trans ?_
        have h1 := card_cubeFinset_le (block L d.fst) 1
        have h2 := card_cubeFinset_le (block L d.snd) 1
        norm_num at h1 h2
        omega
    _ = 2 * 3 ^ (m + 1) * (closedDarts ω ε γ).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- A self-avoiding path with `N` edges visits at least `(N + 1)/L^d` blocks. -/
theorem length_add_one_le_card_mul {L : ℕ} (hL : 1 ≤ L) {u v : Vertex m}
    {γ : (latticeGraph m).Walk u v} (hγ : γ.IsPath) :
    γ.length + 1 ≤ (γ.support.toFinset.image (block L)).card * L ^ (m + 1) := by
  classical
  have hL0 : 0 < L := hL
  have hcard : γ.support.toFinset.card = γ.length + 1 := by
    rw [List.toFinset_card_of_nodup hγ.support_nodup, SimpleGraph.Walk.length_support]
  have hsub : γ.support.toFinset ⊆
      (γ.support.toFinset.image (block L)).biUnion (blockFinset L) := by
    intro x hx
    exact Finset.mem_biUnion.2 ⟨block L x, Finset.mem_image_of_mem _ hx,
      (mem_blockFinset hL0).2 rfl⟩
  rw [← hcard]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ z ∈ γ.support.toFinset.image (block L), (blockFinset L z).card
      ≤ ∑ _z ∈ γ.support.toFinset.image (block L), L ^ (m + 1) :=
        Finset.sum_le_sum fun z _ => card_blockFinset_le L z
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- **A cheap long path meets mostly bad blocks.** Let `γ` be a self-avoiding path with at least
`n ≥ (3L)^d` edges and `walkCost ω γ < a n`, `a = ε / (4·3^d L^d)`. Then at least half of the
blocks it visits are bad for the `ε`-open edges, and it visits at least `(n + 1)/L^d` blocks. -/
theorem card_le_two_mul_card_bad {L : ℕ} (hL : 1 ≤ L) (ω : Config m) {ε : ℝ≥0} (hε : 0 < ε)
    {u v : Vertex m} {γ : (latticeGraph m).Walk u v} (hγ : γ.IsPath) {n : ℕ}
    (hn : (3 * L) ^ (m + 1) ≤ n) (hnγ : n ≤ γ.length)
    (hcost : (walkCost ω γ : ℝ) < (ε : ℝ) / (4 * 3 ^ (m + 1) * L ^ (m + 1)) * n) :
    (γ.support.toFinset.image (block L)).card ≤
        2 * ((γ.support.toFinset.image (block L)).filter
          fun z => openConfig ε ω ∈ badBlock L z).card ∧
      n + 1 ≤ (γ.support.toFinset.image (block L)).card * L ^ (m + 1) := by
  have hLd : 0 < L ^ (m + 1) := pow_pos hL _
  have hsupp := length_add_one_le_card_mul hL hγ
  set Z := γ.support.toFinset.image (block L)
  have hn1 : n + 1 ≤ Z.card * L ^ (m + 1) := by omega
  refine ⟨?_, hn1⟩
  have hZ : 3 ^ (m + 1) < Z.card := by
    have h3 : 3 ^ (m + 1) * L ^ (m + 1) < Z.card * L ^ (m + 1) := by
      rw [← mul_pow]; omega
    exact Nat.lt_of_mul_lt_mul_right h3
  have hgood := card_good_le hL ω ε γ hZ
  -- the closed edges are few
  have hclosed : 4 * 3 ^ (m + 1) * L ^ (m + 1) * (closedDarts ω ε γ).card < n := by
    have h1 := mul_card_closedDarts_le_walkCost ω ε hγ
    have h1' : (ε : ℝ) * (closedDarts ω ε γ).card ≤ walkCost ω γ := by exact_mod_cast h1
    have hpos : (0 : ℝ) < 4 * 3 ^ (m + 1) * L ^ (m + 1) := by positivity
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have h2 : (ε : ℝ) * (closedDarts ω ε γ).card < (ε : ℝ) / (4 * 3 ^ (m + 1) * L ^ (m + 1)) * n :=
      h1'.trans_lt hcost
    rw [div_mul_eq_mul_div, lt_div_iff₀ hpos] at h2
    have h3 : ((4 * 3 ^ (m + 1) * L ^ (m + 1) * (closedDarts ω ε γ).card : ℕ) : ℝ) < n := by
      push_cast
      nlinarith
    exact_mod_cast h3
  -- so the good blocks are fewer than half
  have hgood2 : 2 * (Z.filter fun z => openConfig ε ω ∉ badBlock L z).card < Z.card := by
    have h4 : 2 * (Z.filter fun z => openConfig ε ω ∉ badBlock L z).card * L ^ (m + 1) <
        Z.card * L ^ (m + 1) := by
      calc 2 * (Z.filter fun z => openConfig ε ω ∉ badBlock L z).card * L ^ (m + 1)
          ≤ 2 * (2 * 3 ^ (m + 1) * (closedDarts ω ε γ).card) * L ^ (m + 1) := by gcongr
        _ = 4 * 3 ^ (m + 1) * L ^ (m + 1) * (closedDarts ω ε γ).card := by ring
        _ < n := hclosed
        _ < Z.card * L ^ (m + 1) := by omega
    exact Nat.lt_of_mul_lt_mul_right h4
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Z) (fun z => openConfig ε ω ∈ badBlock L z)
  omega

end CurvatureVariance.Infra.Kesten
