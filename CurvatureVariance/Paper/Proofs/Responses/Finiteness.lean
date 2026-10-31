/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Responses.Slabs
import CurvatureVariance.Infra.FPP.Walks

/-!
# Finiteness of slab distances

Coordinate walks inside the slabs of Section `sec:gain`, using the explicit edge ownership in
`slabEdges`.
These lemmas justify taking real parts in the minimum comparison without a probabilistic
finiteness premise.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

open Infra.FPP

variable {m : ℕ}

/-- A longitudinal edge inside the closed slab belongs to the slab. -/
theorem mem_slabEdges_of_adj_of_snd_eq {p q : ℤ} {x y : Vertex m}
    (hxy : (latticeGraph m).Adj x y) (hsnd : x.2 = y.2)
    (hx : p ≤ x.1 ∧ x.1 ≤ q) (hy : p ≤ y.1 ∧ y.1 ≤ q) : s(x, y) ∈ slabEdges p q := by
  rcases latticeGraph_adj.mp hxy with rfl | rfl | ⟨j, rfl | rfl⟩
  · exact ⟨x, Or.inl ⟨rfl, hx.1, by have h := hy.2; simp only [Prod.fst_add] at h; omega⟩⟩
  · refine ⟨x - (1, 0), Or.inl ⟨?_, hy.1, ?_⟩⟩
    · simp only [sub_add_cancel, Sym2.eq_swap]
    · simp only [Prod.fst_sub] at *
      omega
  · have he := congrFun hsnd j
    simp only [Prod.snd_add, Pi.add_apply, Pi.single_eq_same] at he
    omega
  · have he := congrFun hsnd j
    simp only [Prod.snd_sub, Pi.sub_apply, Pi.single_eq_same] at he
    omega

/-- A transverse edge strictly inside the slab belongs to the slab. -/
theorem mem_slabEdges_of_adj_of_fst_eq {p q c : ℤ} (hp : p < c) (hq : c < q)
    {x y : Vertex m} (hxy : (latticeGraph m).Adj x y) (hx : x.1 = c) (hy : y.1 = c) :
    s(x, y) ∈ slabEdges p q := by
  rcases latticeGraph_adj.mp hxy with rfl | rfl | ⟨j, rfl | rfl⟩
  · simp only [Prod.fst_add] at hy
    omega
  · simp only [Prod.fst_sub] at hy
    omega
  · exact ⟨x, Or.inr ⟨j, rfl, hx ▸ hp, hx ▸ hq⟩⟩
  · refine ⟨x - (0, Pi.single j 1), Or.inr ⟨j, ?_, hy ▸ hp, hy ▸ hq⟩⟩
    simp only [sub_add_cancel, Sym2.eq_swap]

/-- A walk at constant transverse coordinate inside the slab uses only owned edges. -/
theorem walk_mem_slabEdges_of_snd_eq {p q : ℤ} {c : Fin m → ℤ} {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v)
    (hγ : ∀ x ∈ γ.support, (p ≤ x.1 ∧ x.1 ≤ q) ∧ x.2 = c) :
    ∀ e ∈ γ.edges, e ∈ slabEdges p q := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have hx := hγ x (γ.fst_mem_support_of_mem_edges he)
    have hy := hγ y (γ.snd_mem_support_of_mem_edges he)
    exact mem_slabEdges_of_adj_of_snd_eq
      ((SimpleGraph.mem_edgeSet _).mp (γ.edges_subset_edgeSet he))
      (hx.2.trans hy.2.symm) hx.1 hy.1

/-- A walk in a transverse hyperplane strictly inside the slab uses only owned edges. -/
theorem walk_mem_slabEdges_of_fst_eq {p q c : ℤ} (hp : p < c) (hq : c < q)
    {u v : Vertex m} (γ : (latticeGraph m).Walk u v)
    (hγ : ∀ x ∈ γ.support, x.1 = c) : ∀ e ∈ γ.edges, e ∈ slabEdges p q := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    exact mem_slabEdges_of_adj_of_fst_eq hp hq
      ((SimpleGraph.mem_edgeSet _).mp (γ.edges_subset_edgeSet he))
      (hγ x (γ.fst_mem_support_of_mem_edges he)) (hγ y (γ.snd_mem_support_of_mem_edges he))

/-- There is a coordinate walk inside every slab of width at least two. -/
theorem exists_walk_slabEdges {p q : ℤ} (hpq : p + 2 ≤ q) {u v : Vertex m}
    (hu : p ≤ u.1 ∧ u.1 ≤ q) (hv : p ≤ v.1 ∧ v.1 ≤ q) :
    ∃ γ : (latticeGraph m).Walk u v, ∀ e ∈ γ.edges, e ∈ slabEdges p q := by
  obtain ⟨a, -, ha⟩ := exists_longitudinal_walk u (p + 1)
  obtain ⟨b, -, hb⟩ := exists_longitudinal_walk v (p + 1)
  have hnn : 0 ≤ ∑ j, |u.2 j - v.2 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c, -, hc⟩ := exists_transverse_walk v.2 (∑ j, |u.2 j - v.2 j|).toNat
    ((p + 1, u.2) : Vertex m) (by simpa using (Int.toNat_of_nonneg hnn).symm)
  refine ⟨a.append (c.append b.reverse), ?_⟩
  intro e he
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_append, List.mem_reverse] at he
  rcases he with he | he | he
  · exact walk_mem_slabEdges_of_snd_eq a
      (fun x hx => by have h := ha x hx; exact ⟨by constructor <;> omega, h.1⟩) e he
  · exact walk_mem_slabEdges_of_fst_eq (by omega : p < p + 1) (by omega : p + 1 < q)
      c hc e he
  · exact walk_mem_slabEdges_of_snd_eq b
      (fun x hx => by have h := hb x hx; exact ⟨by constructor <;> omega, h.1⟩) e he

/-- Slab distances are finite on every configuration when the slab has width at least two. -/
theorem slabTime_ne_top (ω : Config m) {p q : ℤ} (hpq : p + 2 ≤ q) {u v : Vertex m}
    (hu : p ≤ u.1 ∧ u.1 ≤ q) (hv : p ≤ v.1 ∧ v.1 ≤ q) : slabTime ω p q u v ≠ ⊤ := by
  obtain ⟨γ, hγ⟩ := exists_walk_slabEdges hpq hu hv
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (iInf₂_le γ hγ)

/-- Every term in a tuple cost is finite once the slab width is at least two. -/
theorem tuple_slabTime_ne_top (ω : Config m) (u : Vertex m) {n K : ℕ} (hn : 2 ≤ n)
    (Y : Fin (K + 1) → Fin m → ℤ) (i : Fin K) :
    slabTime ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
      (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ) ≠ ⊤ := by
  apply slabTime_ne_top
  · have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith only [hn']
  · simp only [tuplePoint, Fin.val_castSucc]
    constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n]
  · simp only [tuplePoint, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n]

end CurvatureVariance.Paper.Responses
