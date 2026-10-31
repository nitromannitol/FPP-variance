/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
import CurvatureVariance.Paper.Proofs.Responses.Slabs
import CurvatureVariance.Infra.EfronStein.Coordinates
import CurvatureVariance.Infra.FPP.Model
import Mathlib.Tactic.FunProp
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The independent slab arrays in Lemma `lem:smallmean`

A slab distance reads only the coordinates assigned to its slab. Thus measurable arrays
constructed from disjoint slabs are independent, as the arrays `Z_i` of the proof of Lemma
`lem:smallmean` must be.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Responses

/-- Measurable observables depending on disjoint slabs are independent. -/
theorem iIndepFun_of_slab_local {m K : ℕ} {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} (hIID : IsIIDWeights P F) (u : ℤ) (n : ℕ)
    {β : Fin K → Type*} [∀ i, MeasurableSpace (β i)]
    (X : (i : Fin K) → Config m → β i) (hXm : ∀ i, Measurable (X i))
    (hlocal : ∀ (i : Fin K) (ω ω' : Config m),
      (∀ e : Edge m, e.1 ∈ slabEdges (u + (i : ℤ) * n)
          (u + ((i : ℤ) + 1) * n) → ω e = ω' e) → X i ω = X i ω') :
    iIndepFun X P := by
  classical
  let S : Fin K → Set (Edge m) := fun i =>
    {e | e.1 ∈ slabEdges (u + (i : ℤ) * n) (u + ((i : ℤ) + 1) * n)}
  have hS : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    have hdis := pairwise_disjoint_slabEdges (m := m) u n
      (show (i : ℕ) ≠ (j : ℕ) from fun heq => hij (Fin.ext heq))
    exact Set.disjoint_left.mpr fun e he he' => Set.disjoint_left.mp hdis he he'
  let fill : (i : Fin K) → ((e : S i) → ℝ≥0) → Config m :=
    fun i η e => if he : e ∈ S i then η ⟨e, he⟩ else 0
  have hfill : ∀ i, Measurable (fill i) := by
    intro i
    apply Measurable.of_eval
    intro e
    by_cases he : e ∈ S i
    · simpa only [fill, he, dite_true] using (measurable_pi_apply (⟨e, he⟩ : S i))
    · simpa only [fill, he, dite_false] using
        (measurable_const : Measurable fun _ : (e : S i) → ℝ≥0 => (0 : ℝ≥0))
  let G : (i : Fin K) → ((e : S i) → ℝ≥0) → β i := fun i => X i ∘ fill i
  have hG : ∀ i, Measurable (G i) := fun i => (hXm i).comp (hfill i)
  rw [Infra.FPP.IsIIDWeights.eq_infinitePi hIID]
  have hind := Infra.EfronStein.iIndepFun_comp_restrict_infinitePi
    (fun _ : Edge m => F) S hS G hG
  apply hind.congr
  intro i
  apply Filter.Eventually.of_forall
  intro ω
  apply hlocal i
  intro e he
  change (if hh : e ∈ S i then (fun j : S i => ω j) ⟨e, hh⟩ else 0) = ω e
  simp only [show e ∈ S i from he, dite_true]

/-- The linear supporting terms telescope along an admissible tuple. -/
theorem sum_inner_tuplePoint_sub {m n K : ℕ} {M : Model m}
    {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m}
    {Y : Fin (K + 1) → Fin m → ℤ} (hY : IsAdmissibleTuple M n K t u v Y)
    (hlong : v.1 = u.1 + (K : ℤ) * n) (P : Pt m) :
    ∑ i : Fin K, inner ℝ P (point (tuplePoint u n Y i.succ) -
      point (tuplePoint u n Y i.castSucc)) = inner ℝ P (point v - point u) := by
  have hfirst : tuplePoint u n Y 0 = u := by
    apply Prod.ext
    · simp only [tuplePoint, Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
    · exact hY.1
  have hlast : tuplePoint u n Y (Fin.last K) = v := by
    apply Prod.ext
    · exact hlong.symm
    · exact hY.2.1
  simp only [inner_sub_right, Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ (fun i : Fin (K + 1) => inner ℝ P (point (tuplePoint u n Y i)))
  have h2 := Fin.sum_univ_castSucc (fun i : Fin (K + 1) => inner ℝ P (point (tuplePoint u n Y i)))
  rw [hfirst] at h1
  rw [hlast] at h2
  linarith only [h1, h2]

end CurvatureVariance.Paper.Mean
