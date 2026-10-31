/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Critical
public import CurvatureVariance.Infra.Percolation.Russo

/-!
# Monotonicity in `p` for Bernoulli bond percolation

Increasing events depending on finitely many edges have increasing probability (Russo). Hence
`P_p(u ↔ v in S)`, `φ_p(S)` and the one-arm probability increase with `p`; passing to the limit,
so does `θ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V} {o : V} [Countable V]

omit [Countable V] in
/-- Edges inside a finite set form a finite set. -/
theorem finite_edgesWithin [G.LocallyFinite] (S : Finset V) :
    {e : G.edgeSet | e.1 ∈ edgesWithin (S : Set V)}.Finite := by
  classical
  have hS : (⋃ x ∈ (S : Set V), G.incidenceSet x).Finite :=
    S.finite_toSet.biUnion fun x _ => (G.incidenceSet x).toFinite
  refine (hS.preimage Subtype.val_injective.injOn).subset fun e he => ?_
  obtain ⟨e, h⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
    exact Set.mem_biUnion (x := a) (he a (Sym2.mem_mk_left a b)) ⟨h, Sym2.mem_mk_left a b⟩

/-- `P_p(u ↔ v in S)` increases with `p`. -/
theorem monotone_percolation_openConnected_edgesWithin [G.LocallyFinite] (S : Finset V) (u v : V) :
    Monotone fun p : unitInterval =>
      percolation G p {ω | OpenConnected G ω (edgesWithin (S : Set V)) u v} := by
  classical
  refine monotone_bernoulliProduct_of_isUpperSet (finite_edgesWithin (G := G) S).toFinset
    (measurableSet_openConnected _ u v) ?_ (isUpperSet_openConnected _ u v)
  rw [Set.Finite.coe_toFinset]
  exact dependsOn_openConnected _ u v

/-- **`φ_p(S)` increases with `p`.** -/
theorem monotone_phi [DecidableEq V] [G.LocallyFinite] (v : V) (S : Finset V) :
    Monotone fun p : unitInterval => phi G p v S := by
  intro p q hpq
  unfold phi
  refine mul_le_mul hpq (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) q.2.1
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (monotone_percolation_openConnected_edgesWithin S v x hpq)

/-- **The one-arm probability increases with `p`.** -/
theorem monotone_armProb [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ) :
    Monotone fun p : unitInterval => armProb G o p n := by
  simp_rw [armProb_eq]
  classical
  refine monotone_bernoulliProduct_of_isUpperSet (finite_innerEdges hG o n).toFinset
    (measurableSet_armEvent o n) ?_ (isUpperSet_armEvent o n)
  rw [Set.Finite.coe_toFinset]
  exact dependsOn_armEvent hG o n

omit [Countable V] in
/-- The cluster is infinite only if `o` is joined to every distance. -/
theorem percolationProb_le_armProb [G.LocallyFinite] (hG : G.Connected) (o : V) (p : unitInterval)
    (n : ℕ) : percolationProb G o p ≤ armProb G o p n := by
  rw [percolationProb_eq, armProb_eq, setOf_infinite_eq_iInter_armEvent hG]
  exact measure_mono (Set.iInter_subset _ n)

/-- **`θ` increases with `p`.** -/
theorem monotone_percolationProb [G.LocallyFinite] (hG : G.Connected) (o : V) :
    Monotone (percolationProb G o) := by
  intro p q hpq
  have hlim : Filter.Tendsto (fun n => percolation G q (armEvent G o n)) Filter.atTop
      (nhds (percolation G q (⋂ n, armEvent G o n))) :=
    tendsto_measure_iInter_atTop (fun n => (measurableSet_armEvent o n).nullMeasurableSet)
      (armEvent_antitone o) ⟨0, measure_ne_top _ _⟩
  rw [percolationProb_eq, percolationProb_eq, setOf_infinite_eq_iInter_armEvent hG]
  refine ge_of_tendsto' hlim fun n => ?_
  have h := percolationProb_le_armProb hG o p n
  rw [percolationProb_eq, armProb_eq, setOf_infinite_eq_iInter_armEvent hG] at h
  exact h.trans (by simpa only [armProb_eq] using monotone_armProb hG o n hpq)

end CurvatureVariance.Infra.Percolation
