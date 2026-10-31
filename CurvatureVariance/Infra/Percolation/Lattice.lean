/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Lattice.LatticeGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Fintype.Option

/-!
# The nearest-neighbour graph of `ℤ^d`

Facts about `latticeGraph m` (the graph of `ℤ^d = ℤ × ℤ^m`, `d = m + 1`) needed to apply the
general sharpness theorems of `CurvatureVariance.Infra.Percolation.Sharpness`:

* `latticeGraph_adj_iff`: `x ~ y` iff `y = x + unitStep k b` for one of the `2d` unit steps;
* the instance `LocallyFinite`, and `degree_latticeGraph : degree x = 2 (m + 1)`;
* `latticeShift a`: translation by `a` is a graph automorphism, so the graph is vertex-transitive
  (`exists_latticeShift_eq`);
* `latticeGraph_connected`;
* `latticeSupNorm x ≤ dist 0 x`: the `ℓ^∞` norm (the body of the definition
  `CurvatureVariance.supNorm`) is at most the graph distance from the origin.
-/

@[expose] public section

namespace CurvatureVariance.Infra.Percolation

variable {m : ℕ}

/-! ### Unit steps and adjacency -/

/-- The `2d` unit steps `±e_k`: `k = none` is the longitudinal coordinate, `k = some j` the
transverse coordinate `j`, and `b` the sign. -/
def unitStep : Option (Fin m) → Bool → Vertex m
  | none, true => (1, 0)
  | none, false => (-1, 0)
  | some j, true => (0, Pi.single j 1)
  | some j, false => (0, -Pi.single j 1)

theorem unitStep_ne_zero (k : Option (Fin m)) (b : Bool) : unitStep k b ≠ 0 := by
  rcases k with _ | j <;> cases b <;> simp [unitStep, Prod.ext_iff, funext_iff] <;>
    exact ⟨j, by simp⟩

theorem unitStep_injective : Function.Injective fun kb : Option (Fin m) × Bool =>
    unitStep (m := m) kb.1 kb.2 := by
  rintro ⟨k, b⟩ ⟨k', b'⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := fun i => congrFun (congrArg Prod.snd h) i
  rcases k with _ | j <;> rcases k' with _ | j' <;> cases b <;> cases b' <;>
    simp [unitStep] at h1 h2 ⊢
  all_goals
    first
    | (have := h2 j; simp [Pi.single_apply] at this; done)
    | (have := h2 j; simp [Pi.single_apply] at this; exact this)
    | (have := h2 j; by_cases hjj : j = j' <;> simp [hjj] at this)

/-- **Adjacency in `ℤ^d`**: `y` is obtained from `x` by one of the `2d` unit steps. -/
theorem latticeGraph_adj_iff {x y : Vertex m} :
    (latticeGraph m).Adj x y ↔ ∃ k b, y = x + unitStep k b := by
  rw [latticeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, (h | ⟨j, h⟩) | (h | ⟨j, h⟩)⟩
    · exact ⟨none, true, h⟩
    · exact ⟨some j, true, h⟩
    · exact ⟨none, false, by rw [h]; ext <;> simp [unitStep]⟩
    · exact ⟨some j, false, by rw [h]; ext <;> simp [unitStep]⟩
  · rintro ⟨k, b, rfl⟩
    refine ⟨fun h => unitStep_ne_zero k b (by simpa using h), ?_⟩
    rcases k with _ | j <;> cases b
    · exact .inr (.inl (by ext <;> simp [unitStep]))
    · exact .inl (.inl rfl)
    · exact .inr (.inr ⟨j, by ext <;> simp [unitStep]⟩)
    · exact .inl (.inr ⟨j, rfl⟩)

/-- The neighbours of `x` are its `2d` unit translates. -/
theorem neighborSet_latticeGraph (x : Vertex m) :
    (latticeGraph m).neighborSet x =
      Set.range fun kb : Option (Fin m) × Bool => x + unitStep kb.1 kb.2 := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, latticeGraph_adj_iff, Set.mem_range, Prod.exists]
  exact ⟨fun ⟨k, b, h⟩ => ⟨k, b, h.symm⟩, fun ⟨k, b, h⟩ => ⟨k, b, h.symm⟩⟩

/-- `ℤ^d` is locally finite. -/
noncomputable instance : (latticeGraph m).LocallyFinite := fun x =>
  ((Set.finite_range _).subset (neighborSet_latticeGraph x).le).fintype

/-- **Every vertex of `ℤ^d` has degree `2d = 2 (m + 1)`.** -/
theorem degree_latticeGraph (x : Vertex m) : (latticeGraph m).degree x = 2 * (m + 1) := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hinj : Function.Injective fun kb : Option (Fin m) × Bool => x + unitStep kb.1 kb.2 :=
    fun a b h => unitStep_injective (add_left_cancel h)
  have hN : (latticeGraph m).neighborFinset x =
      Finset.univ.image fun kb : Option (Fin m) × Bool => x + unitStep kb.1 kb.2 := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_neighborSet, neighborSet_latticeGraph]
    simp
  rw [hN, Finset.card_image_of_injective _ hinj]
  simp [Fintype.card_option, mul_comm]

/-! ### Translations -/

/-- Translation by `a ∈ ℤ^d` as an automorphism of the lattice graph. -/
def latticeShift (a : Vertex m) : latticeGraph m ≃g latticeGraph m where
  toEquiv := Equiv.addRight a
  map_rel_iff' := by
    intro x y
    have key : ∀ c x y : Vertex m, y + a = x + a + c ↔ y = x + c := by
      intro c x y
      rw [add_right_comm, add_left_inj]
    simp only [latticeGraph, SimpleGraph.fromRel_adj, Equiv.coe_addRight, ne_eq, add_left_inj, key]

@[simp] theorem latticeShift_apply (a x : Vertex m) : latticeShift a x = x + a := rfl

/-- **`ℤ^d` is vertex-transitive**: the translation by `v` maps the origin to `v`. -/
theorem exists_latticeShift_eq (v : Vertex m) :
    ∃ g : latticeGraph m ≃g latticeGraph m, g 0 = v :=
  ⟨latticeShift v, by simp⟩

/-! ### Connectedness -/

/-- The vertices reachable from the origin form an additive subgroup. -/
def reachableSubgroup (m : ℕ) : AddSubgroup (Vertex m) where
  carrier := {x | (latticeGraph m).Reachable 0 x}
  zero_mem' := SimpleGraph.Reachable.refl _
  add_mem' := by
    intro a b ha hb
    have hb' : (latticeGraph m).Reachable (0 + a) (b + a) := hb.map (latticeShift a).toHom
    simp only [zero_add] at hb'
    exact (show (latticeGraph m).Reachable 0 (a + b) by rw [add_comm]; exact ha.trans hb')
  neg_mem' := by
    intro a ha
    have h : (latticeGraph m).Reachable (0 + -a) (a + -a) := ha.map (latticeShift (-a)).toHom
    simp only [zero_add, add_neg_cancel] at h
    exact h.symm

theorem unitStep_mem_reachableSubgroup (k : Option (Fin m)) (b : Bool) :
    unitStep k b ∈ reachableSubgroup m :=
  (latticeGraph_adj_iff.2 ⟨k, b, by simp⟩).reachable

/-- **`ℤ^d` is connected.** -/
theorem latticeGraph_connected (m : ℕ) : (latticeGraph m).Connected := by
  have hall : ∀ x : Vertex m, x ∈ reachableSubgroup m := by
    intro x
    have hx : x = x.1 • unitStep none true + ∑ j, x.2 j • unitStep (some j) true := by
      ext
      · simp [unitStep, Prod.fst_sum]
      · simp [unitStep, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hx]
    refine add_mem (zsmul_mem (unitStep_mem_reachableSubgroup _ _) _)
      (sum_mem fun j _ => zsmul_mem (unitStep_mem_reachableSubgroup _ _) _)
  refine SimpleGraph.Connected.mk fun x y => ?_
  exact (hall x).symm.trans (hall y)

/-! ### The `ℓ^∞` norm and the graph distance -/

/-- The `ℓ^∞` norm `‖x‖_∞ = max (|s|, maxⱼ |yⱼ|)` of `x = (s, y)` (the body of the definition
`CurvatureVariance.supNorm`). -/
def latticeSupNorm (x : Vertex m) : ℕ :=
  max x.1.natAbs (Finset.univ.sup fun j => (x.2 j).natAbs)

theorem latticeSupNorm_zero : latticeSupNorm (0 : Vertex m) = 0 := by
  simp [latticeSupNorm]

/-- A unit step changes the `ℓ^∞` norm by at most one. -/
theorem latticeSupNorm_add_unitStep_le (x : Vertex m) (k : Option (Fin m)) (b : Bool) :
    latticeSupNorm (x + unitStep k b) ≤ latticeSupNorm x + 1 := by
  have h1 : (unitStep (m := m) k b).1.natAbs ≤ 1 := by
    rcases k with _ | j <;> cases b <;> simp [unitStep]
  have h2 : ∀ j, ((unitStep (m := m) k b).2 j).natAbs ≤ 1 := by
    intro j
    rcases k with _ | i <;> cases b <;> simp [unitStep, Pi.single_apply] <;> split_ifs <;> simp
  unfold latticeSupNorm
  refine max_le ?_ (Finset.sup_le fun j _ => ?_)
  · calc (x + unitStep k b).1.natAbs ≤ x.1.natAbs + (unitStep (m := m) k b).1.natAbs :=
          Int.natAbs_add_le _ _
      _ ≤ max x.1.natAbs (Finset.univ.sup fun j => (x.2 j).natAbs) + 1 := by
          have := le_max_left x.1.natAbs (Finset.univ.sup fun j => (x.2 j).natAbs)
          omega
  · calc ((x + unitStep k b).2 j).natAbs ≤ (x.2 j).natAbs + ((unitStep (m := m) k b).2 j).natAbs :=
          Int.natAbs_add_le _ _
      _ ≤ max x.1.natAbs (Finset.univ.sup fun j => (x.2 j).natAbs) + 1 := by
          have h3 : (x.2 j).natAbs ≤ Finset.univ.sup fun j => (x.2 j).natAbs :=
            Finset.le_sup (f := fun j => (x.2 j).natAbs) (Finset.mem_univ j)
          have := le_max_right x.1.natAbs (Finset.univ.sup fun j => (x.2 j).natAbs)
          have := h2 j
          omega

theorem latticeSupNorm_le_of_adj {x y : Vertex m} (h : (latticeGraph m).Adj x y) :
    latticeSupNorm y ≤ latticeSupNorm x + 1 := by
  obtain ⟨k, b, rfl⟩ := latticeGraph_adj_iff.1 h
  exact latticeSupNorm_add_unitStep_le x k b

theorem latticeSupNorm_le_length {x y : Vertex m} (p : (latticeGraph m).Walk x y) :
    latticeSupNorm y ≤ latticeSupNorm x + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    have := latticeSupNorm_le_of_adj h
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **The `ℓ^∞` norm is at most the graph distance from the origin.** -/
theorem latticeSupNorm_le_dist (x : Vertex m) :
    latticeSupNorm x ≤ (latticeGraph m).dist 0 x := by
  obtain ⟨p, hp⟩ := (latticeGraph_connected m).exists_walk_length_eq_dist 0 x
  have := latticeSupNorm_le_length p
  rw [latticeSupNorm_zero, zero_add, hp] at this
  exact this

end CurvatureVariance.Infra.Percolation
