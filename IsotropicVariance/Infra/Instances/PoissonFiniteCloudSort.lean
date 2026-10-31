/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonFiniteCloud
public import Mathlib.Data.Multiset.Sort

/-! # Every finite cloud has a unique canonical ordered representation -/

@[expose] public section
open MeasureTheory
namespace IsotropicVariance.Infra.Instances
variable {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]

/-- Reordering a finite cloud preserves the sum of its Dirac masses. -/
theorem exists_poissonFiniteCloud_of_tuple {n : ℕ} (x : Fin n → E) :
    ∃ c : PoissonFiniteCloud E, poissonFiniteCloudMeasure E c = ∑ i : Fin n, Measure.dirac (x i) := by
  classical
  let r : E → E → Prop := fun a b => embeddingReal E a ≤ embeddingReal E b
  let : IsTrans E r := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  let : Std.Total r := ⟨fun a b => le_total _ _⟩
  let : Std.Antisymm r := ⟨fun a b h₁ h₂ =>
    (measurableEmbedding_embeddingReal E).injective (le_antisymm h₁ h₂)⟩
  let l := (List.ofFn x : Multiset E).sort r
  have hl : l.Pairwise r := Multiset.pairwise_sort _ _
  have hperm : List.Perm l (List.ofFn x) := by
    exact Quotient.exact (Multiset.sort_eq _ _)
  have hmono : Monotone (fun i : Fin l.length => embeddingReal E (l.get i)) := by
    have hp : (List.ofFn l.get).Pairwise r := by simpa only [List.ofFn_get] using hl
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · subst j; exact le_rfl
    · exact List.pairwise_ofFn.mp hp h
  refine ⟨⟨l.length, ⟨l.get, hmono⟩⟩, ?_⟩
  have hs := (hperm.map Measure.dirac).sum_eq
  change (∑ i : Fin l.length, Measure.dirac (l.get i)) = ∑ i : Fin n, Measure.dirac (x i)
  calc
    _ = (l.map Measure.dirac).sum := by
      rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]
    _ = ((List.ofFn x).map Measure.dirac).sum := hs
    _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl

/-- Any finite indexed Dirac sum has a canonical finite-cloud representation. -/
theorem exists_poissonFiniteCloud_of_fintype {ι : Type*} [Fintype ι] (x : ι → E) :
    ∃ c : PoissonFiniteCloud E, poissonFiniteCloudMeasure E c = ∑ i, Measure.dirac (x i) := by
  classical
  obtain ⟨c, hc⟩ := exists_poissonFiniteCloud_of_tuple (fun i => x ((Fintype.equivFin ι).symm i))
  refine ⟨c, hc.trans ?_⟩
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => Measure.dirac (x i)))

/-- The empty configuration requires no inhabitant of the point space. -/
instance : Zero (PoissonFiniteCloud E) :=
  ⟨⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩⟩

end IsotropicVariance.Infra.Instances
