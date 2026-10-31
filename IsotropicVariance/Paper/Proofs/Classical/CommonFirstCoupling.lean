/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Resampling.KernelProduct
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # Gluing finitely many replacement pairs over their common old sample -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.Resampling

/-- Pair laws with a common first marginal can be realized with one common
old sample and conditionally independent replacement samples. -/
theorem exists_common_first_coupling {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Fin n → Measure (Ω × Ω)) [∀ i, IsProbabilityMeasure (q i)]
    (hFirst : ∀ i, (q i).map Prod.fst = P) :
    ∃ Q : Measure (Ω × (Fin n → Ω)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = P ∧ ∀ i, Q.map (fun p => (p.1, p.2 i)) = q i := by
  let κ : Fin n → Kernel Ω Ω := fun i => condDistrib Prod.snd Prod.fst (q i)
  have hDis (i : Fin n) : P ⊗ₘ κ i = q i := by
    have hh := compProd_map_condDistrib (μ := q i) measurable_fst.aemeasurable measurable_snd.aemeasurable
    rw [hFirst i] at hh
    change P ⊗ₘ κ i = (q i).map id at hh
    rwa [Measure.map_id] at hh
  let K : Kernel Ω (Fin n → Ω) :=
    (coordinateProductKernel κ).comap (fun ω _ => ω) (Measurable.of_eval fun _ => measurable_id)
  have : IsMarkovKernel K := by unfold K; infer_instance
  have hEval (i : Fin n) : K.map (fun x => x i) = κ i := by
    ext ω A hA
    rw [Kernel.map_apply _ (measurable_pi_apply i)]
    change (Measure.infinitePi (fun j => κ j ω)).map (fun x => x i) A = κ i ω A
    rw [Measure.infinitePi_map_eval]
  refine ⟨P ⊗ₘ K, inferInstance, ?_, ?_⟩
  · exact Measure.fst_compProd P K
  · intro i
    have hh := Measure.compProd_map (μ := P) (κ := K) (measurable_pi_apply i)
    rw [hEval i] at hh
    have heq : Prod.map id (fun x : Fin n → Ω => x i) =
        (fun p : Ω × (Fin n → Ω) => (p.1, p.2 i)) := by
      funext p
      simp only [Prod.map_apply', id_eq]
    rw [heq] at hh
    exact hh.symm.trans (hDis i)

end IsotropicVariance.Paper.Proofs.Classical
