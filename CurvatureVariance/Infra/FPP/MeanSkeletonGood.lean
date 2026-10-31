/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanSkeleton
import Mathlib.Tactic.Linarith

/-!
# Good skeletons and convex-hull membership

* `exists_good_skeleton`: a self-avoiding path from the origin with at most `K` edges has a
  skeleton at scale `R` whose family contains its edge set;
* `mem_convexHull_of_sum`: averaged lifted increments, padded by the origin, lie in the convex hull
  of the lifted lattice points.
-/

@[expose] public section

namespace CurvatureVariance.Infra.FPP

open SimpleGraph

variable {m : ℕ}

theorem skelVert_eq_of_le {q : ℕ} (v : ℕ → Vertex m) (h0 : v 0 = 0)
    (d : Fin q → Vertex m) (hd : ∀ j : Fin q, d j = v (j + 1) - v j) :
    ∀ i, i ≤ q → skelVert d i = v i := by
  intro i
  induction i with
  | zero => intro _; simp [h0]
  | succ i ih =>
    intro hi
    have hi' : i < q := hi
    have h1 : skelVert d (i + 1) - skelVert d i = v (i + 1) - v i := by
      rw [skelVert_succ_sub d hi', hd]
    rw [ih hi'.le] at h1
    exact sub_left_inj.mp h1

/-- A self-avoiding path from the origin with at most `K` edges has a skeleton at scale `R`
whose family contains its edge set. -/
theorem exists_good_skeleton {X : Vertex m} (π : (latticeGraph m).Walk 0 X) (hπ : π.IsPath)
    {K : ℕ} (hK : π.length ≤ K) (hK1 : 1 ≤ K) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (q : ℕ) (d : Fin q → Vertex m), q ∈ Finset.Icc 1 K ∧ (∀ j, ‖point (d j)‖ ≤ R + 1) ∧
      ∑ j, d j = X ∧ (∀ j : Fin q, (j : ℕ) + 1 < q → R ≤ ‖point (d j)‖) ∧
      walkEdges π ∈ skeletonFamily (skelVert d) q K := by
  obtain ⟨q, v, hq, hqK, hv0, hvq, hup, hlo, hcost⟩ := exists_skeleton π hR
  let d : Fin q → Vertex m := fun j => v (j + 1) - v j
  have hsk : ∀ i, i ≤ q → skelVert d i = v i := skelVert_eq_of_le v hv0 d (fun _ => rfl)
  have hqK' : q ≤ K := hqK.trans (max_le hK hK1)
  refine ⟨q, d, Finset.mem_Icc.mpr ⟨hq, hqK'⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [d, point_sub] using hup j j.2
  · rw [← skelVert_self, hsk q le_rfl, hvq]
  · intro j hj
    simpa [d, point_sub] using hlo j hj
  · simp only [skeletonFamily, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, (card_walkEdges_le π).trans hK, ?_⟩
    · intro e he
      have := walkEdges_subset_edgesNear π he
      rw [mem_edgesNear] at this ⊢
      intro x hx
      have h1 := this x hx
      simp only [point_zero, norm_zero, zero_add] at h1
      have h2 : (π.length : ℝ) ≤ K := by exact_mod_cast hK
      linarith only [h1, h2]
    · intro ω
      refine le_trans (le_of_eq ?_) ((hcost ω).trans_eq
        (sum_walkEdges hπ.isTrail.edges_nodup ω).symm)
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [hsk i hi'.le, hsk (i + 1) hi']

/-- The lifted increments, averaged with weight `1/n` and padded by the origin, lie in the
convex hull of the lifted lattice points. -/
theorem mem_convexHull_of_sum {h : Vertex m → ℝ} (h0 : h 0 = 0) {q n : ℕ} (hqn : q ≤ n)
    (hn : 0 < n) (d : Fin q → Vertex m) {R : ℝ} (hR : 0 ≤ R) (hd : ∀ j, ‖point (d j)‖ ≤ R) :
    ((n : ℝ)⁻¹ • point (∑ j, d j), (n : ℝ)⁻¹ * ∑ j, h (d j)) ∈
      convexHull ℝ (liftedPoints h R) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hqn' : (q : ℝ) ≤ n := by exact_mod_cast hqn
  let w : Option (Fin q) → ℝ := fun o => o.elim (1 - q / n) (fun _ => (n : ℝ)⁻¹)
  let P : Option (Fin q) → Pt m × ℝ := fun o =>
    o.elim (point (0 : Vertex m), h 0) (fun j => (point (d j), h (d j)))
  have hw0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin q))), 0 ≤ w o := by
    intro o _
    cases o with
    | none =>
      show 0 ≤ 1 - (q : ℝ) / n
      rw [sub_nonneg, div_le_one hnpos]; exact hqn'
    | some j => exact inv_nonneg.mpr hnpos.le
  have hw1 : ∑ o, w o = 1 := by
    rw [Fintype.sum_option]
    simp only [w, Option.elim_none, Option.elim_some, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hP : ∀ o ∈ (Finset.univ : Finset (Option (Fin q))), P o ∈ liftedPoints h R := by
    intro o _
    cases o with
    | none => exact ⟨0, by simpa [point_zero] using hR, rfl⟩
    | some j => exact ⟨d j, hd j, rfl⟩
  have key := (convex_convexHull ℝ (liftedPoints h R)).sum_mem hw0 hw1
    (fun o ho => subset_convexHull ℝ _ (hP o ho))
  convert key using 1
  rw [Fintype.sum_option]
  ext
  · simp [w, P, point_sum, Finset.smul_sum, point_zero, Prod.fst_sum]
  · simp [w, P, h0, Finset.mul_sum, Prod.snd_sum]
end CurvatureVariance.Infra.FPP
