/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonTransfer

/-! # Transferring the Poisson law through exact configuration-law equality -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace IsotropicVariance.Infra.Instances

/-- A Poisson law transfers to a measurable configuration carrier. Counts must be finite
on every target outcome; the canonical carrier proves this deterministically. -/
theorem isPoissonProcess_of_config_law {m : ℕ} {Ω C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace C] {P : Measure Ω} {Q : Measure C}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {lam : ℝ≥0}
    {η : Ω → Measure (Pt m)} {ξ : C → Measure (Pt m)}
    (hη : IsotropicVariance.IsPoissonProcess lam η P) (hξ : Measurable ξ)
    (hcount : ∀ c (B : Set (Pt m)), MeasurableSet B → Bornology.IsBounded B → ∃ n : ℕ, ξ c B = n)
    (heq : P.map η = Q.map ξ) : IsotropicVariance.IsPoissonProcess lam ξ Q := by
  refine ⟨hξ, hcount, fun k B hB hb hd => ?_⟩
  obtain ⟨hind, hlaw⟩ := hη.2.2 k B hB hb hd
  have hms (i : Fin k) : Measurable (fun ω => η ω (B i)) := (Measure.measurable_coe (hB i)).comp hη.1
  have hmt (i : Fin k) : Measurable (fun c => ξ c (B i)) := (Measure.measurable_coe (hB i)).comp hξ
  have hsingle (i : Fin k) : Q.map (fun c => ξ c (B i)) = P.map (fun ω => η ω (B i)) := by
    change Q.map ((fun μ : Measure (Pt m) => μ (B i)) ∘ ξ) =
      P.map ((fun μ : Measure (Pt m) => μ (B i)) ∘ η)
    rw [← Measure.map_map (Measure.measurable_coe (hB i)) hξ,
      ← Measure.map_map (Measure.measurable_coe (hB i)) hη.1, heq]
  have hmjoint : Measurable (fun μ : Measure (Pt m) => fun i : Fin k => μ (B i)) :=
    Measurable.of_eval fun i => Measure.measurable_coe (hB i)
  have hjoint : Q.map (fun c => fun i : Fin k => ξ c (B i)) =
      P.map (fun ω => fun i : Fin k => η ω (B i)) := by
    change Q.map ((fun μ : Measure (Pt m) => fun i : Fin k => μ (B i)) ∘ ξ) =
      P.map ((fun μ : Measure (Pt m) => fun i : Fin k => μ (B i)) ∘ η)
    rw [← Measure.map_map hmjoint hξ, ← Measure.map_map hmjoint hη.1, heq]
  refine ⟨?_, fun i => ⟨(hmt i).aemeasurable, (hsingle i).trans (hlaw i).map_eq⟩⟩
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hmt i).aemeasurable)).mpr
  rw [hjoint]
  simp_rw [hsingle]
  exact (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hms i).aemeasurable)).mp hind

end IsotropicVariance.Infra.Instances
