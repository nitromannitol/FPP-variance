/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonSigma
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.OfFn

/-! # Canonically ordered finite point configurations

Sorting is imposed only as a Borel predicate on finite tuples. The decoded measure remembers
multiplicities, and the ordering makes its finite-cloud representation unique.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace IsotropicVariance.Infra.Instances

variable (E : Type*) [MeasurableSpace E] [StandardBorelSpace E]

/-- Ordered tuples use the fixed Borel embedding into the reals. -/
def PoissonOrderedTuple (n : ℕ) :=
  {x : Fin n → E // Monotone (fun i => embeddingReal E (x i))}

instance (n : ℕ) : MeasurableSpace (PoissonOrderedTuple E n) := inferInstanceAs
  (MeasurableSpace {x : Fin n → E // Monotone (fun i => embeddingReal E (x i))})

lemma measurableSet_poissonOrderedTuple (n : ℕ) :
    MeasurableSet {x : Fin n → E | Monotone (fun i => embeddingReal E (x i))} := by
  change MeasurableSet {x : Fin n → E | ∀ i j, i ≤ j → embeddingReal E (x i) ≤ embeddingReal E (x j)}
  simpa only [Set.ofPred_forall, Function.comp_apply] using
    (MeasurableSet.iInter fun (i : Fin n) => MeasurableSet.iInter fun (j : Fin n) =>
      MeasurableSet.iInter fun (_h : i ≤ j) =>
        measurableSet_le ((measurable_embeddingReal E).comp (measurable_pi_apply i))
          ((measurable_embeddingReal E).comp (measurable_pi_apply j)))

instance (n : ℕ) : StandardBorelSpace (PoissonOrderedTuple E n) :=
  (measurableSet_poissonOrderedTuple E n).standardBorel

/-- A finite cloud is an ordered tuple of variable finite length. -/
abbrev PoissonFiniteCloud := Σ n : ℕ, PoissonOrderedTuple E n

instance : StandardBorelSpace (PoissonFiniteCloud E) := by
  exact poisson_standardBorel_sigma (PoissonOrderedTuple E)

/-- Decode a finite cloud as a finite sum of Dirac masses. -/
noncomputable def poissonFiniteCloudMeasure (c : PoissonFiniteCloud E) : Measure E :=
  ∑ i : Fin c.1, Measure.dirac (c.2.val i)

lemma measurable_poissonFiniteCloudMeasure :
    Measurable (poissonFiniteCloudMeasure E) := by
  apply poisson_measurable_sigma
  intro n
  exact Finset.measurable_sum Finset.univ fun i _ =>
    Measure.measurable_dirac.comp ((measurable_pi_apply i).comp measurable_subtype_coe)

/-- Singleton evaluations of a finite Dirac sum are the multiplicities in its point list. -/
lemma finiteDiracSum_singleton [DecidableEq E] {n : ℕ} (x : Fin n → E) (a : E) :
    (∑ i : Fin n, Measure.dirac (x i)) {a} = ((List.ofFn x).count a : ℝ≥0∞) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, Measure.add_apply, List.ofFn_succ]
    simp only [List.count_cons, Nat.cast_add]
    rw [ih]
    by_cases h : x 0 = a
    · simp [Measure.dirac_apply', h, add_comm]
    · simp [Measure.dirac_apply', h]

/-- Equal decoded measures have equal ordered finite-cloud representations. -/
theorem poissonFiniteCloudMeasure_injective : Function.Injective (poissonFiniteCloudMeasure E) := by
  classical
  rintro ⟨n, x⟩ ⟨k, y⟩ heq
  have hperm : List.Perm (List.ofFn x.val) (List.ofFn y.val) := by
    apply List.perm_iff_count.mpr
    intro a
    have hh := congrArg (fun μ : Measure E => μ {a}) heq
    change (∑ i : Fin n, Measure.dirac (x.val i)) {a} =
      (∑ i : Fin k, Measure.dirac (y.val i)) {a} at hh
    rw [finiteDiracSum_singleton, finiteDiracSum_singleton] at hh
    exact Nat.cast_injective hh
  let r : E → E → Prop := fun a b => embeddingReal E a ≤ embeddingReal E b
  let : Std.Antisymm r := ⟨fun a b hab hba =>
    (measurableEmbedding_embeddingReal E).injective (le_antisymm hab hba)⟩
  have hx : (List.ofFn x.val).Pairwise r := List.pairwise_ofFn.mpr fun _ _ hij => x.property hij.le
  have hy : (List.ofFn y.val).Pairwise r := List.pairwise_ofFn.mpr fun _ _ hij => y.property hij.le
  have hlist := hperm.eq_of_pairwise' hx hy
  have hnk : n = k := by simpa only [List.length_ofFn] using congrArg List.length hlist
  subst k
  have hxy : x = y := Subtype.ext (List.ofFn_injective hlist)
  subst y
  rfl

end IsotropicVariance.Infra.Instances
