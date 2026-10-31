/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
public import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# First hits of the hyperplanes `{x₁ = u₁ + i n}`

The first step of the proof of Lemma `lem:slabs` (2): for a walk `γ` from `u` to `v`
with `v₁ = u₁ + K n`, the first vertex of `γ` in the hyperplane `{x₁ = u₁ + i n}`, `0 < i < K`,
exists, because the first coordinate changes by at most one per step; and these first hits come in
order along `γ`. So `hitPoint γ n K i = γ.getVert (k i)` for indices
`0 = k 0 ≤ k 1 ≤ ⋯ ≤ k K = γ.length` with `(γ.getVert (k i))₁ = u₁ + i n` (`exists_hitIndex`).

The first hit is read off `hitPoint` (`List.find?` on the support, through `List.findIdx`).
-/

@[expose] public section

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- Along a lattice walk, the first coordinate increases by at most one per step. -/
theorem fst_getVert_succ_le {u v : Vertex m} (γ : (latticeGraph m).Walk u v) (i : ℕ) :
    (γ.getVert (i + 1)).1 ≤ (γ.getVert i).1 + 1 := by
  rcases lt_or_ge i γ.length with h | h
  · rcases latticeGraph_adj.1 (γ.adj_getVert_succ h) with h' | h' | ⟨j, h' | h'⟩ <;>
      rw [h'] <;> simp only [Prod.fst_add, Prod.fst_sub] <;> omega
  · rw [γ.getVert_of_length_le h, γ.getVert_of_length_le (by omega)]
    omega

/-- **Discrete intermediate values.** If the first coordinate is at most `a` at the start of a walk
and at least `a` at the index `k`, it equals `a` at some index at most `k`. -/
theorem exists_getVert_fst_eq {u v : Vertex m} (γ : (latticeGraph m).Walk u v) {a : ℤ}
    (h0 : u.1 ≤ a) {k : ℕ} (hk : a ≤ (γ.getVert k).1) : ∃ j ≤ k, (γ.getVert j).1 = a := by
  induction k with
  | zero =>
    rw [SimpleGraph.Walk.getVert_zero] at hk
    exact ⟨0, le_rfl, by rw [SimpleGraph.Walk.getVert_zero]; omega⟩
  | succ k ih =>
    by_cases h : a ≤ (γ.getVert k).1
    · obtain ⟨j, hj, hja⟩ := ih h
      exact ⟨j, by omega, hja⟩
    · have := fst_getVert_succ_le γ k
      exact ⟨k + 1, le_rfl, by omega⟩

/-- **First hits.** If `u₁ ≤ a ≤ v₁`, the first vertex of the support of `γ` in the hyperplane
`{x₁ = a}` is `γ.getVert k` for an index `k ≤ γ.length` with `(γ.getVert k)₁ = a`, and the walk
avoids the hyperplane before `k`. -/
theorem exists_find?_eq_getVert {u v : Vertex m} (γ : (latticeGraph m).Walk u v) {a : ℤ}
    (h0 : u.1 ≤ a) (h1 : a ≤ v.1) :
    ∃ k ≤ γ.length, γ.support.find? (fun z => decide (z.1 = a)) = some (γ.getVert k) ∧
      (γ.getVert k).1 = a ∧ ∀ j < k, (γ.getVert j).1 ≠ a := by
  have hex : ∃ x ∈ γ.support, decide (x.1 = a) = true := by
    obtain ⟨j, -, hj⟩ := exists_getVert_fst_eq γ h0 (k := γ.length)
      (by rwa [SimpleGraph.Walk.getVert_length])
    exact ⟨γ.getVert j, γ.getVert_mem_support j, by simp [hj]⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  have hk : γ.support.findIdx (fun z => decide (z.1 = a)) ≤ γ.length := by
    rw [SimpleGraph.Walk.length_support] at hlt
    omega
  refine ⟨_, hk, ?_, ?_, ?_⟩
  · rw [List.find?_eq_getElem?_findIdx, List.getElem?_eq_getElem hlt,
      γ.getVert_eq_support_getElem hk]
  · have := List.findIdx_getElem (w := hlt)
    rw [γ.getVert_eq_support_getElem hk]
    simpa using this
  · intro j hj
    have := List.not_of_lt_findIdx hj
    rw [γ.getVert_eq_support_getElem (by omega)]
    simpa using this

/-- For `0 < i < K` and `v₁ = u₁ + K n`, `hitPoint γ n K i` is `γ.getVert k` for the index `k` of
the first vertex of `γ` in the hyperplane `{x₁ = u₁ + i n}`. -/
theorem exists_hitPoint_eq_getVert {u v : Vertex m} (γ : (latticeGraph m).Walk u v) {n K i : ℕ}
    (hv : v.1 = u.1 + K * n) (hi0 : 0 < i) (hiK : i < K) :
    ∃ k ≤ γ.length, hitPoint γ n K i = γ.getVert k ∧ (γ.getVert k).1 = u.1 + i * n ∧
      ∀ j < k, (γ.getVert j).1 ≠ u.1 + i * n := by
  have h0 : u.1 ≤ u.1 + (i : ℤ) * n := by
    have : (0 : ℤ) ≤ (i : ℤ) * n := by positivity
    linarith
  have h1 : u.1 + (i : ℤ) * n ≤ v.1 := by
    rw [hv]
    have : (i : ℤ) * n ≤ (K : ℤ) * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hiK.le) (by positivity)
    linarith
  obtain ⟨k, hk, hf, hka, hkj⟩ := exists_find?_eq_getVert γ h0 h1
  refine ⟨k, hk, ?_, hka, hkj⟩
  have h1 : i ≠ 0 := Nat.pos_iff_ne_zero.1 hi0
  have h2 : i ≠ K := Nat.ne_of_lt hiK
  simp [hitPoint, h1, h2, hf]

/-- **The hit indices.** For a walk from `u` to `v` with `v₁ = u₁ + K n` and `K ≥ 1`, there are
indices `0 = k 0 ≤ k 1 ≤ ⋯ ≤ k K = γ.length` with `hitPoint γ n K i = γ.getVert (k i)` and
`(γ.getVert (k i))₁ = u₁ + i n` for `i ≤ K`: the first hits come in order along `γ`. -/
theorem exists_hitIndex {u v : Vertex m} (γ : (latticeGraph m).Walk u v) {n K : ℕ} (hK : 1 ≤ K)
    (hv : v.1 = u.1 + K * n) :
    ∃ k : ℕ → ℕ, k 0 = 0 ∧ k K = γ.length ∧ (∀ i < K, k i ≤ k (i + 1)) ∧
      ∀ i ≤ K, hitPoint γ n K i = γ.getVert (k i) ∧ (γ.getVert (k i)).1 = u.1 + i * n := by
  have hspec : ∀ i, ∃ k, (i = 0 → k = 0) ∧ (K ≤ i → k = γ.length) ∧
      (0 < i → i < K → hitPoint γ n K i = γ.getVert k ∧ (γ.getVert k).1 = u.1 + i * n ∧
        ∀ j < k, (γ.getVert j).1 ≠ u.1 + i * n) := by
    intro i
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exact ⟨0, fun _ => rfl, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · by_cases hiK : i < K
      · obtain ⟨k, -, hk⟩ := exists_hitPoint_eq_getVert γ hv hpos hiK
        exact ⟨k, fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ _ => hk⟩
      · exact ⟨γ.length, fun h => absurd h (by omega), fun _ => rfl, fun _ h => absurd h hiK⟩
  choose k hk using hspec
  have hk0 : k 0 = 0 := (hk 0).1 rfl
  have hkK : k K = γ.length := (hk K).2.1 le_rfl
  have hval : ∀ i ≤ K, hitPoint γ n K i = γ.getVert (k i) ∧
      (γ.getVert (k i)).1 = u.1 + i * n := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp [hitPoint, hk0]
    · rcases lt_or_eq_of_le hi with hlt | heq
      · exact ⟨((hk i).2.2 hpos hlt).1, ((hk i).2.2 hpos hlt).2.1⟩
      · subst heq
        refine ⟨?_, by rw [hkK, SimpleGraph.Walk.getVert_length, hv]⟩
        simp [hitPoint, hkK, Nat.pos_iff_ne_zero.1 hpos]
  refine ⟨k, hk0, hkK, fun i hi => ?_, hval⟩
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [h0, hk0]
    exact Nat.zero_le _
  · obtain ⟨-, -, hfirst⟩ := (hk i).2.2 hpos hi
    have hge : u.1 + (i : ℤ) * n ≤ (γ.getVert (k (i + 1))).1 := by
      rw [(hval (i + 1) hi).2]
      have : (i : ℤ) * n ≤ ((i + 1 : ℕ) : ℤ) * n :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith) (by positivity)
      linarith
    have h0' : u.1 ≤ u.1 + (i : ℤ) * n := by
      have : (0 : ℤ) ≤ (i : ℤ) * n := by positivity
      linarith
    obtain ⟨j, hj, hja⟩ := exists_getVert_fst_eq γ h0' hge
    by_contra hlt
    exact hfirst j (by omega) hja

end CurvatureVariance.Paper.Proofs.Geometry
