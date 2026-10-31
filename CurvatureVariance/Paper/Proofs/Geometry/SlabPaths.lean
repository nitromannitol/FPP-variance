/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
public import CurvatureVariance.Infra.FPP.Walks

/-!
# Coordinate paths within slabs

Section `sec:prelim` (the text after equation `eq:classical`): a coordinate path within the slab
`[p, q] × ℝ^{d-1}` makes one longitudinal step into the interior, then the transverse steps, then
the other longitudinal steps; it has at most `|u − v|₁ + 2` edges between two vertices of the slab
and uses no omitted face edge.

* `mem_slabEdges_of_adj`: an edge between vertices of the slab belongs to it unless it is
  transverse in a face;
* `levelWalk u v c`: the coordinate walk from `u` to `v` through the transverse level `c`
  (longitudinal to `(c, u₂)`, transverse to `(c, v₂)`, longitudinal to `v`), and `slabPath u v c`,
  its loop erasure: a path with at most `|u₁ − c| + |u₂ − v₂|₁ + |c − v₁|` edges, all in every slab
  `[p, q]` containing `u`, `v` with `p < c < q` (`slabPath_edges_mem`);
* `slabLevel p q u`: the level used for the slab `[p, q]`: `u₁` inside, `u₁ ± 1` on a face.
-/

@[expose] public section

open scoped NNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- An edge of the lattice between two vertices of the slab `[p, q] × ℝ^{d-1}` is an edge of the
slab, unless it is transverse in one of the faces. -/
theorem mem_slabEdges_of_adj {p q : ℤ} {a b : Vertex m} (h : (latticeGraph m).Adj a b)
    (ha : p ≤ a.1 ∧ a.1 ≤ q) (hb : p ≤ b.1 ∧ b.1 ≤ q) (ht : a.1 = b.1 → p < a.1 ∧ a.1 < q) :
    s(a, b) ∈ slabEdges p q := by
  rcases latticeGraph_adj.1 h with rfl | rfl | ⟨j, rfl | rfl⟩
  · exact ⟨a, Or.inl ⟨rfl, ha.1, by simp at hb; omega⟩⟩
  · refine ⟨a - (1, 0), Or.inl ⟨?_, hb.1, by simp; omega⟩⟩
    rw [Sym2.eq_swap]
    simp
  · have h1 : a.1 = (a + (0, Pi.single j 1)).1 := by simp
    obtain ⟨h2, h3⟩ := ht h1
    exact ⟨a, Or.inr ⟨j, rfl, h2, h3⟩⟩
  · have h1 : a.1 = (a - (0, Pi.single j 1)).1 := by simp
    obtain ⟨h2, h3⟩ := ht h1
    refine ⟨a - (0, Pi.single j 1), Or.inr ⟨j, ?_, by simpa using h2, by simpa using h3⟩⟩
    rw [Sym2.eq_swap]
    simp

/-- The darts of a walk whose endpoints lie in the slab `[p, q]`, strictly inside it when the dart
is transverse. -/
def SlabDart (p q : ℤ) (d : (latticeGraph m).Dart) : Prop :=
  (p ≤ d.fst.1 ∧ d.fst.1 ≤ q) ∧ (p ≤ d.snd.1 ∧ d.snd.1 ≤ q) ∧
    (d.fst.1 = d.snd.1 → p < d.fst.1 ∧ d.fst.1 < q)

theorem edges_mem_slabEdges {p q : ℤ} {u v : Vertex m} (γ : (latticeGraph m).Walk u v)
    (h : ∀ d ∈ γ.darts, SlabDart p q d) : ∀ e ∈ γ.edges, e ∈ slabEdges p q := by
  intro e he
  rw [SimpleGraph.Walk.edges, List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := h d hd
  exact mem_slabEdges_of_adj d.adj h1 h2 h3

/-- A dart between two vertices with the same transverse part is longitudinal. -/
theorem fst_ne_of_snd_eq (d : (latticeGraph m).Dart) (h : d.fst.2 = d.snd.2) :
    d.fst.1 ≠ d.snd.1 := fun h1 => by
  have : d.fst = d.snd := Prod.ext h1 h
  exact (latticeGraph m).ne_of_adj d.adj this

/-- The coordinate walk through the transverse level `c`, with its length and its darts:
longitudinal darts between the levels `u₁` and `c` or `c` and `v₁`, and transverse darts at the
level `c`. -/
theorem exists_levelWalk (u v : Vertex m) (c : ℤ) :
    ∃ γ : (latticeGraph m).Walk u v,
      (γ.length : ℤ) = |u.1 - c| + ∑ j, |u.2 j - v.2 j| + |c - v.1| ∧
      ∀ p q : ℤ, p ≤ u.1 → u.1 ≤ q → p ≤ v.1 → v.1 ≤ q → p < c → c < q →
        ∀ d ∈ γ.darts, SlabDart p q d := by
  obtain ⟨γ₁, hl₁, hs₁⟩ := exists_longitudinal_walk u c
  have hnn : 0 ≤ ∑ j, |u.2 j - v.2 j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨γ₂, hl₂, hs₂⟩ := exists_transverse_walk v.2 (∑ j, |u.2 j - v.2 j|).toNat
    ((c, u.2) : Vertex m) (by simpa using (Int.toNat_of_nonneg hnn).symm)
  obtain ⟨γ₃, hl₃, hs₃⟩ := exists_longitudinal_walk ((c, v.2) : Vertex m) v.1
  refine ⟨γ₁.append (γ₂.append γ₃), ?_, ?_⟩
  · simp only [SimpleGraph.Walk.length_append]
    push_cast
    rw [hl₁, hl₂, hl₃, Int.toNat_of_nonneg hnn]
    ring
  · intro p q hpu huq hpv hvq hpc hcq d hd
    simp only [SimpleGraph.Walk.darts_append, List.mem_append] at hd
    rcases hd with hd | hd | hd
    · have ha := hs₁ d.fst (SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ hd)
      have hb := hs₁ d.snd (SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ hd)
      have hne := fst_ne_of_snd_eq d (ha.1.trans hb.1.symm)
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, fun h => absurd h hne⟩ <;>
        simp only [min_le_iff, le_max_iff] at ha hb <;> omega
    · have ha := hs₂ d.fst (SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ hd)
      have hb := hs₂ d.snd (SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ hd)
      simp only at ha hb
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, fun _ => ⟨?_, ?_⟩⟩ <;> omega
    · have ha := hs₃ d.fst (SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ hd)
      have hb := hs₃ d.snd (SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ hd)
      have hne := fst_ne_of_snd_eq d (ha.1.trans hb.1.symm)
      simp only at ha hb
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, fun h => absurd h hne⟩ <;>
        simp only [min_le_iff, le_max_iff] at ha hb <;> omega

/-- The coordinate walk from `u` to `v` through the transverse level `c`. -/
noncomputable def levelWalk (u v : Vertex m) (c : ℤ) : (latticeGraph m).Walk u v :=
  (exists_levelWalk u v c).choose

/-- The coordinate path from `u` to `v` through the level `c`: the loop erasure of `levelWalk`. -/
noncomputable def slabPath (u v : Vertex m) (c : ℤ) : (latticeGraph m).Walk u v :=
  (levelWalk u v c).bypass

theorem slabPath_isPath (u v : Vertex m) (c : ℤ) : (slabPath u v c).IsPath :=
  SimpleGraph.Walk.bypass_isPath _

theorem slabPath_length_le (u v : Vertex m) (c : ℤ) :
    ((slabPath u v c).length : ℤ) ≤ |u.1 - c| + ∑ j, |u.2 j - v.2 j| + |c - v.1| := by
  rw [← (exists_levelWalk u v c).choose_spec.1]
  exact_mod_cast SimpleGraph.Walk.length_bypass_le_length _

theorem slabPath_edges_mem {p q : ℤ} {u v : Vertex m} {c : ℤ} (hpu : p ≤ u.1) (huq : u.1 ≤ q)
    (hpv : p ≤ v.1) (hvq : v.1 ≤ q) (hpc : p < c) (hcq : c < q) :
    ∀ e ∈ (slabPath u v c).edges, e ∈ slabEdges p q := fun e he =>
  edges_mem_slabEdges (levelWalk u v c)
    ((exists_levelWalk u v c).choose_spec.2 p q hpu huq hpv hvq hpc hcq) e
    (SimpleGraph.Walk.edges_bypass_subset_edges _ he)

/-- The transverse level of the coordinate path within the slab `[p, q]` from `u`: `u₁` if `u` is
inside, the next level inward if `u` is on a face. -/
def slabLevel (p q : ℤ) (u : Vertex m) : ℤ :=
  if u.1 = p then u.1 + 1 else if u.1 = q then u.1 - 1 else u.1

theorem slabLevel_mem (p q : ℤ) (u : Vertex m) :
    slabLevel p q u = u.1 - 1 ∨ slabLevel p q u = u.1 ∨ slabLevel p q u = u.1 + 1 := by
  unfold slabLevel
  split_ifs <;> simp

theorem slabLevel_bounds {p q : ℤ} (hpq : p + 2 ≤ q) {u : Vertex m} (hpu : p ≤ u.1)
    (huq : u.1 ≤ q) : p < slabLevel p q u ∧ slabLevel p q u < q := by
  unfold slabLevel
  split_ifs <;> omega

/-- The length of a coordinate path through a level next to `u₁`: at most `|v − u|₁ + 2`. -/
theorem slabPath_length_le_add_two (u v : Vertex m) {c : ℤ} (hc : |u.1 - c| ≤ 1) :
    ((slabPath u v c).length : ℤ) ≤ |v.1 - u.1| + ∑ j, |v.2 j - u.2 j| + 2 := by
  have h := slabPath_length_le u v c
  have h1 : |c - v.1| ≤ |v.1 - u.1| + 1 := by
    rw [abs_le] at hc ⊢
    constructor <;> cases abs_cases (v.1 - u.1) <;> omega
  have h2 : ∑ j, |u.2 j - v.2 j| = ∑ j, |v.2 j - u.2 j| :=
    Finset.sum_congr rfl fun j _ => abs_sub_comm _ _
  omega

end CurvatureVariance.Paper.Proofs.Geometry
