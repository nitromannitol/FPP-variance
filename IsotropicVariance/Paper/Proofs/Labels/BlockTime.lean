/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.SetVersion
public import IsotropicVariance.Paper.Defs.Blocks
import IsotropicVariance.Paper.Proofs.Labels.Region

/-!
# Step 1 of the proof of Lemma `lem:labels`: the comparison of `T^{(i)}` with `T_G`

For a block `G` of the slab `i` (0-based in Lean), `T_G` is the passage time
`X.setTime b (closure G)` of equation `eq:slabtime`. On `G`, `ρ_G ≥ ρ^{(i)}`, with equality at
distance more than one from the other blocks, so `T_G(u, v) ≥ T^{(i)}(u, v)` for `u, v ∈ G`, with
equality if the curves in `Π_{T^{(i)}}(u, v)` stay at distance more than one from the other blocks.

* `convex_block`, `interior_closure_block_subset`: the closure of a block is convex, and its
  interior lies in the block, so the noise in the block determines `T_G`.
* `HasMargin`: the transverse coordinates of a point are at distance at least `2` from the sides of
  the block. For a point of the slab this is the form in which the paper's "distance more than one
  from the other blocks" is used: a block is cut by its sides from the other blocks of its slab, and
  one family of labels serves every choice of the offsets (`Contracts.LabelsStatement`).
* `setDensity_closure_block`: `ρ_G = ρ^{(i)}` at the points of the slab with a margin.
* `slabTime_le_setTime_closure_block`: `T^{(i)} ≤ T_G` on the closure of the block.
* `setTime_closure_block_eq`: equality if the `1`-optimal curves for `T^{(i)}` keep a margin.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper IsotropicVariance.Infra.Slab

variable {m : ℕ}

/-! ### The closure of a block -/

/-- A block is convex. -/
theorem convex_block (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) : Convex ℝ (block n W L i z) := by
  rintro x ⟨h1, h2, h3⟩ y ⟨h1', h2', h3'⟩ a c ha hc hac
  have hl : a * Pt.lon x + c * Pt.lon y ∈ Icc ((i : ℝ) * n) (((i : ℝ) + 1) * n) :=
    convex_Icc _ _ ⟨h1, h2⟩ ⟨h1', h2'⟩ ha hc hac
  refine ⟨hl.1, hl.2, fun k => ?_⟩
  exact convex_Ico _ _ (h3 k) (h3' k) ha hc hac

/-- A block of positive sizes has a nonempty interior. -/
theorem interior_block_nonempty {n W : ℝ} (hn : 0 < n) (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L) (i : ℕ)
    (z : Fin m → ℤ) : (interior (block n W L i z)).Nonempty := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  refine ⟨Pt.mk (((i : ℝ) + 1 / 2) * n) (WithLp.toLp 2 fun k => W * ((z k : ℝ) + 1 / 2)), ?_⟩
  refine interior_maximal ?_ (Labels.isOpen_blockInterior n W L i z) ?_
  · rintro y ⟨hy1, hy2, hy3⟩
    exact ⟨hy1.le, hy2.le, fun k => ⟨(hy3 k).1.le, (hy3 k).2⟩⟩
  · refine ⟨?_, ?_, fun k => ⟨?_, ?_⟩⟩
    · change (i : ℝ) * n < ((i : ℝ) + 1 / 2) * n
      nlinarith
    · change ((i : ℝ) + 1 / 2) * n < ((i : ℝ) + 1) * n
      nlinarith
    · change W * (z k : ℝ) < W * ((z k : ℝ) + 1 / 2)
      nlinarith
    · change W * ((z k : ℝ) + 1 / 2) < W * ((z k : ℝ) + L)
      nlinarith

/-- **The interior of the closure of a block lies in the block**, so the information of the
interior of `closure G` is part of the information of `G`. -/
theorem interior_closure_block_subset {n W : ℝ} (hn : 0 < n) (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L)
    (i : ℕ) (z : Fin m → ℤ) :
    interior (closure (block n W L i z)) ⊆ block n W L i z := by
  rw [(convex_block n W L i z).interior_closure_eq_interior_of_nonempty_interior
    (interior_block_nonempty hn hW hL i z)]
  exact interior_subset

/-- The closure of a block lies in its slab. -/
theorem closure_block_subset (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    closure (block n W L i z) ⊆ (chainSlab n 0 i).set :=
  closure_minimal (fun _ hx => Labels.mem_chainSlab_set.2 ⟨hx.1, hx.2.1⟩) (isClosed_slab_set _)

/-! ### The densities -/

/-- The transverse coordinates of `x` are at distance at least `2` from the sides of the block of
index `z` (and side `LW`): the condition under which the two densities agree. -/
def HasMargin (W : ℝ) (L : ℕ) (z : Fin m → ℤ) (x : Pt m) : Prop :=
  ∀ k, W * z k + 2 ≤ Pt.tr x k ∧ Pt.tr x k ≤ W * (z k + L) - 2

/-- A point of the slab with a margin lies in the block. -/
theorem mem_block_of_hasMargin {n W : ℝ} {L i : ℕ} {z : Fin m → ℤ} {x : Pt m}
    (hx : x ∈ (chainSlab n 0 i).set) (htr : HasMargin W L z x) : x ∈ block n W L i z := by
  obtain ⟨h1, h2⟩ := Labels.mem_chainSlab_set.1 hx
  exact ⟨h1, h2, fun k => ⟨by linarith only [(htr k).1], by linarith only [(htr k).2]⟩⟩

/-- **`ρ_G = ρ^{(i)}` at the points of the slab with a margin** (Step 1 of the proof of Lemma
`lem:labels`). -/
theorem setDensity_closure_block {n W : ℝ} (hn : 0 < n) {L i : ℕ} {z : Fin m → ℤ} {x : Pt m}
    (hx : x ∈ (chainSlab n 0 i).set) (htr : HasMargin W L z x) (b : ℝ) (σ : Pt m → ℝ) :
    setDensity b σ (closure (block n W L i z)) x = (chainSlab n 0 i).density b σ x := by
  have hxc : x ∈ closure (block n W L i z) := subset_closure (mem_block_of_hasMargin hx htr)
  have hfaces : (chainSlab n 0 i : Slab m).faces.Nonempty := Slab.faces_nonempty _
  have hfr : frontier (chainSlab n 0 i : Slab m).set = (chainSlab n 0 i).faces :=
    Slab.frontier_set _ hn
  by_cases hf : infDist x (chainSlab n 0 i).faces ≤ 1
  · have hf1 : x ∈ cthickening 1 (frontier (chainSlab n 0 i : Slab m).set) := by
      rw [hfr]
      exact (mem_cthickening_one_iff hfaces).2 hf
    have hf2 : x ∈ cthickening 1 (frontier (closure (block n W L i z))) := by
      rw [mem_cthickening_iff] at hf1 ⊢
      exact (infEDist_frontier_le isClosed_closure (closure_block_subset n W L i z) hxc).trans hf1
    simp only [setDensity, hf2, ite_true, Slab.density, hf]
  · have hball := (Labels.infDist_faces_le_one_or_closedBall_subset hx htr).resolve_left hf
    have hf2 : x ∉ cthickening 1 (frontier (closure (block n W L i z))) :=
      notMem_cthickening_of_closedBall_subset_interior
        (hball.trans (interior_mono subset_closure))
    simp only [setDensity, hf2, ite_false, Slab.density, hf]

/-! ### The passage times -/

variable (X : Setting.{u} m)

/-- **`T^{(i)} ≤ T_G`** on the closure of the block (Step 1 of the proof of Lemma `lem:labels`):
`ρ_G ≥ ρ^{(i)}` on `G`, and the curves for `T_G` are curves in the slab. -/
theorem slabTime_le_setTime_closure_block {b : ℝ} (hb : X.IsUpperBound b) {n W : ℝ} (hn : 0 < n)
    {L i : ℕ} {z : Fin m → ℤ} (ω : X.Ω) {u v : Pt m} (hu : u ∈ closure (block n W L i z))
    (hv : v ∈ closure (block n W L i z)) :
    X.slabTime b (chainSlab n 0 i) ω u v ≤ X.setTime b (closure (block n W L i z)) ω u v := by
  rw [← X.setTime_slab (chainSlab n 0 i) hn b ω]
  exact X.setTime_le_setTime hb isClosed_closure (convex_block n W L i z).closure
    (closure_block_subset n W L i z) ω hu hv

/-- **`T_G ≤ T^{(i)}` if the curves in `Π_{T^{(i)}}(u, v)` keep a margin** (Step 1 of the proof of
Lemma `lem:labels`): a curve whose cost is close enough to the infimum is `1`-optimal, so it stays
in `G` and costs the same for the two densities. -/
theorem setTime_closure_block_le {b : ℝ} (hb : X.IsUpperBound b) {n W : ℝ} (hn : 0 < n) {L i : ℕ}
    {z : Fin m → ℤ} (ω : X.Ω) {u v : Pt m} (hu : u ∈ (chainSlab n 0 i).set)
    (hv : v ∈ (chainSlab n 0 i).set)
    (hgood : ∀ γ, IsOneOptimal ((chainSlab n 0 i).density b (X.ρ ω)) (chainSlab n 0 i).set u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, HasMargin W L z (γ.toFun t)) :
    X.setTime b (closure (block n W L i z)) ω u v ≤ X.slabTime b (chainSlab n 0 i) ω u v := by
  have hρ : ∀ x, (chainSlab n 0 i).density b (X.ρ ω) x ≤ b := fun x => by
    unfold Slab.density
    split_ifs
    exacts [le_rfl, hb ω x]
  have hfin := restrictedInf_ne_top hρ (convex_slab_set (chainSlab n 0 i)) hu hv
  have key : restrictedInf (setDensity b (X.ρ ω) (closure (block n W L i z)))
      (closure (block n W L i z)) u v ≤
      restrictedInf ((chainSlab n 0 i).density b (X.ρ ω)) (chainSlab n 0 i).set u v := by
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between (lt_min (ENNReal.lt_add_right hfin one_ne_zero) hcon)
    have hc1' := hc1
    unfold restrictedInf at hc1'
    simp only [iInf_lt_iff] at hc1'
    obtain ⟨γ, h0, h1, hγS, hcost⟩ := hc1'
    have hopt : IsOneOptimal ((chainSlab n 0 i).density b (X.ρ ω)) (chainSlab n 0 i).set u v γ := by
      refine ⟨h0, h1, hγS, ?_⟩
      rw [restrictedPassageTime_eq_toReal, ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
        ENNReal.ofReal_toReal hfin, ENNReal.ofReal_one]
      exact hcost.le.trans (hc2.le.trans (min_le_left _ _))
    have hmar := hgood γ hopt
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ closure (block n W L i z) := fun t ht =>
      subset_closure (mem_block_of_hasMargin (hγS t ht) (hmar t ht))
    have hcostEq : γ.cost (fun x => ENNReal.ofReal
        (setDensity b (X.ρ ω) (closure (block n W L i z)) x)) =
        γ.cost (fun x => ENNReal.ofReal ((chainSlab n 0 i).density b (X.ρ ω) x)) :=
      γ.cost_congr fun t ht => congrArg ENNReal.ofReal
        (setDensity_closure_block hn (hγS t ht) (hmar t ht) b _)
    have hle := restrictedInf_le_cost (σ := setDensity b (X.ρ ω) (closure (block n W L i z)))
      γ h0 h1 hmem
    exact lt_irrefl _ ((hle.trans_eq hcostEq).trans_lt
      (hcost.trans (hc2.trans_le (min_le_right _ _))))
  exact ENNReal.toReal_mono hfin key

/-- **`T_G = T^{(i)}` if the curves in `Π_{T^{(i)}}(u, v)` keep a margin** (Step 1 of the proof of
Lemma `lem:labels`), for `u, v` in the closure of the block. -/
theorem setTime_closure_block_eq {b : ℝ} (hb : X.IsUpperBound b) {n W : ℝ} (hn : 0 < n) {L i : ℕ}
    {z : Fin m → ℤ} (ω : X.Ω) {u v : Pt m} (hu : u ∈ closure (block n W L i z))
    (hv : v ∈ closure (block n W L i z))
    (hgood : ∀ γ, IsOneOptimal ((chainSlab n 0 i).density b (X.ρ ω)) (chainSlab n 0 i).set u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, HasMargin W L z (γ.toFun t)) :
    X.setTime b (closure (block n W L i z)) ω u v = X.slabTime b (chainSlab n 0 i) ω u v :=
  le_antisymm
    (setTime_closure_block_le X hb hn ω (closure_block_subset n W L i z hu)
      (closure_block_subset n W L i z hv) hgood)
    (slabTime_le_setTime_closure_block X hb hn ω hu hv)

end IsotropicVariance.Paper.Proofs.Labels
