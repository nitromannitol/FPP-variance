/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Tuples for Lemma `lem:parent`

Deterministic facts for the proof of Lemma `lem:parent`:

* `passageTime_le_slabMin`: `T(u, v) ≤ F` (concatenation; equation `eq:F`), since a slab
  passage time is at least the passage time and `T` satisfies the triangle inequality.
* `exists_isMinTuple`: a minimizing tuple of equation `eq:F` exists as soon as an admissible
  tuple exists, since the admissible tuples form a finite set (Section `sec:prelim`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Moments.Parent

open CurvatureVariance.Paper

variable {m : ℕ}

/-! ## Concatenation -/

/-- A restricted passage time is at least the passage time. -/
theorem passageTime_le_restrictedTime (ω : Config m) (E : Set (Sym2 (Vertex m)))
    (u v : Vertex m) : (passageTime ω u v : ℝ≥0∞) ≤ restrictedTime ω E u v := by
  unfold restrictedTime
  exact le_iInf₂ fun γ _ => ENNReal.coe_le_coe.mpr (Infra.FPP.passageTime_le_walkCost ω γ)

/-- The triangle inequality along a chain of points. -/
theorem passageTime_le_sum_fin (ω : Config m) : ∀ {K : ℕ} (f : Fin (K + 1) → Vertex m),
    (passageTime ω (f 0) (f (Fin.last K)) : ℝ≥0∞) ≤
      ∑ i : Fin K, (passageTime ω (f i.castSucc) (f i.succ) : ℝ≥0∞)
  | 0, f => by simp
  | K + 1, f => by
    rw [Fin.sum_univ_castSucc]
    have ih := passageTime_le_sum_fin ω (fun i : Fin (K + 1) => f i.castSucc)
    simp only [Fin.castSucc_zero] at ih
    simp only [Fin.succ_castSucc, Fin.succ_last]
    have htri : (passageTime ω (f 0) (f (Fin.last (K + 1))) : ℝ≥0∞) ≤
        passageTime ω (f 0) (f (Fin.last K).castSucc) +
          passageTime ω (f (Fin.last K).castSucc) (f (Fin.last (K + 1))) := by
      exact_mod_cast Infra.FPP.passageTime_triangle ω _ _ _
    exact htri.trans (add_le_add_left ih _)

/-- **Concatenation**: the passage time is at most the cost of every admissible tuple. -/
theorem passageTime_le_tupleCost (ω : Config m) {M : Model m} {n K : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m} {Y : Fin (K + 1) → Fin m → ℤ}
    (hY : IsAdmissibleTuple M n K t u v Y) (hv : v.1 = u.1 + K * n) :
    (passageTime ω u v : ℝ≥0∞) ≤ tupleCost ω u n Y := by
  have h := passageTime_le_sum_fin ω (fun i : Fin (K + 1) => tuplePoint u n Y i)
  have h0 : tuplePoint u n Y 0 = u := Prod.ext (by simp [tuplePoint]) (by simp [tuplePoint, hY.1])
  have hl : tuplePoint u n Y (Fin.last K) = v :=
    Prod.ext (by simp [tuplePoint, hv]) (by simp [tuplePoint, hY.2.1])
  simp only [h0, hl] at h
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  unfold slabTime
  exact passageTime_le_restrictedTime ω _ _ _

/-- **Concatenation** (`T(0, (Ms, Mst)) ≤ F`, in the proof of Lemma `lem:parent`): `T(u, v) ≤ F`. -/
theorem passageTime_le_slabMin (ω : Config m) (M : Model m) {n K : ℕ}
    (t : EuclideanSpace ℝ (Fin m)) {u v : Vertex m} (hv : v.1 = u.1 + K * n) :
    (passageTime ω u v : ℝ≥0∞) ≤ slabMin M ω n K t u v :=
  le_iInf₂ fun _ hY => passageTime_le_tupleCost ω hY hv

/-! ## Minimizing tuples exist -/

/-- The points of an admissible tuple stay in a ball. -/
theorem norm_tuple_le {M : Model m} {n K : ℕ} {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m}
    {Y : Fin (K + 1) → Fin m → ℤ} (hY : IsAdmissibleTuple M n K t u v Y) :
    ∀ (j : ℕ) (hj : j < K + 1), ‖transversePoint (Y ⟨j, hj⟩)‖ ≤
      ‖transversePoint u.2‖ + j * (‖(n : ℝ) • t‖ + (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16)
  | 0, hj => by
    have : (⟨0, hj⟩ : Fin (K + 1)) = 0 := rfl
    rw [this, hY.1]; simp
  | j + 1, hj => by
    have hjK : j < K := by omega
    have ih := norm_tuple_le hY j (by omega)
    have hstep := hY.2.2 ⟨j, hjK⟩
    have e1 : (⟨j, hjK⟩ : Fin K).succ = ⟨j + 1, hj⟩ := rfl
    have e2 : (⟨j, hjK⟩ : Fin K).castSucc = ⟨j, by omega⟩ := rfl
    rw [e1, e2] at hstep
    have hsplit : transversePoint (Y ⟨j + 1, hj⟩) = transversePoint (Y ⟨j, by omega⟩) +
        (transversePoint (Y ⟨j + 1, hj⟩ - Y ⟨j, by omega⟩) - (n : ℝ) • t) + (n : ℝ) • t := by
      rw [Infra.FPP.transversePoint_sub]; abel
    rw [hsplit]
    calc ‖transversePoint (Y ⟨j, by omega⟩) +
          (transversePoint (Y ⟨j + 1, hj⟩ - Y ⟨j, by omega⟩) - (n : ℝ) • t) + (n : ℝ) • t‖
        ≤ ‖transversePoint (Y ⟨j, by omega⟩)‖ +
          ‖transversePoint (Y ⟨j + 1, hj⟩ - Y ⟨j, by omega⟩) - (n : ℝ) • t‖ +
            ‖(n : ℝ) • t‖ := norm_add₃_le
      _ ≤ _ := by push_cast; linarith

/-- **Minimizing tuples exist** (Section `sec:prelim`): the admissible tuples form a finite set,
so if one exists, the minimum of equation `eq:F` is attained. -/
theorem exists_isMinTuple (M : Model m) (ω : Config m) {n K : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {u v : Vertex m} {Y₀ : Fin (K + 1) → Fin m → ℤ} (hY₀ : IsAdmissibleTuple M n K t u v Y₀) :
    ∃ Y, IsMinTuple M ω n K t u v Y := by
  classical
  set L := ‖(n : ℝ) • t‖ + (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 with hL
  have hL0 : 0 ≤ L := by positivity
  set R : ℤ := ⌈‖transversePoint u.2‖ + K * L⌉ with hR
  set S := (Fintype.piFinset fun _ : Fin (K + 1) =>
    Fintype.piFinset fun _ : Fin m => Finset.Icc (-R) R).filter
      (IsAdmissibleTuple M n K t u v) with hS
  have hmem : ∀ Y, IsAdmissibleTuple M n K t u v Y → Y ∈ S := by
    intro Y hY
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i =>
      Fintype.mem_piFinset.mpr fun k => ?_, hY⟩
    have h1 := norm_tuple_le hY i i.isLt
    simp only [Fin.eta] at h1
    rw [← hL] at h1
    have h2 := ExpArray.abs_apply_le_norm (transversePoint (Y i)) k
    rw [Infra.FPP.transversePoint_apply] at h2
    have hi : ((i : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
    have h3 : |(Y i k : ℝ)| ≤ ‖transversePoint u.2‖ + K * L := by
      have : ((i : ℕ) : ℝ) * L ≤ K * L := mul_le_mul_of_nonneg_right hi hL0
      linarith
    have h4 := Int.le_ceil (‖transversePoint u.2‖ + K * L)
    rw [abs_le] at h3
    rw [Finset.mem_Icc]
    constructor
    · have : (-(R : ℝ)) ≤ Y i k := by rw [hR]; linarith
      exact_mod_cast this
    · have : (Y i k : ℝ) ≤ R := by rw [hR]; linarith
      exact_mod_cast this
  obtain ⟨Y, hYS, hYmin⟩ := S.exists_min_image (tupleCost ω u n) ⟨Y₀, hmem Y₀ hY₀⟩
  have hYadm := (Finset.mem_filter.mp hYS).2
  exact ⟨Y, hYadm, le_antisymm (le_iInf₂ fun Y' hY' => hYmin Y' (hmem Y' hY')) (iInf₂_le Y hYadm)⟩

end CurvatureVariance.Paper.Moments.Parent
