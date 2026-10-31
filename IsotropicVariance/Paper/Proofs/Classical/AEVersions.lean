/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.RegionalCodes

/-! # Measurable versions under almost-sure transfer of information

The noise union law supplies representatives of events, rather than equality
of sigma algebras. Countably many generating events suffice to reconstruct a
standard Borel valued observable almost surely.
-/

@[expose] public section
open MeasureTheory Set Filter Function
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical

/-- Eventwise almost-sure transfer of information yields a measurable version
of any standard Borel valued observable. -/
theorem exists_measurable_version_of_event_transfer {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] (P : Measure Ω)
    (G H : MeasurableSpace Ω)
    (hTransfer : ∀ A : Set Ω, MeasurableSet[H] A → ∃ B : Set Ω, MeasurableSet[G] B ∧ P (symmDiff A B) = 0)
    {f : Ω → Z} (hf : Measurable[H] f) :
    ∃ g : Ω → Z, Measurable[G] g ∧ f =ᵐ[P] g := by
  let T := MeasurableSpace.natGeneratingSequence Z
  have hE (n : ℕ) := hTransfer (f ⁻¹' T n) (hf (MeasurableSpace.measurableSet_natGeneratingSequence (α := Z) n))
  choose B hB hAB using hE
  let Φ := fun ω n => decide (ω ∈ B n)
  have hΦ : Measurable[G] Φ := by
    let _ : MeasurableSpace Ω := G
    rw [measurable_pi_iff]
    intro n
    apply measurable_to_bool
    have heq : (fun ω => Φ ω n) ⁻¹' {true} = B n := by
      ext ω
      simp only [Φ, mem_preimage, mem_singleton_iff, decide_eq_true_eq]
    rw [heq]
    exact hB n
  have hEmb : MeasurableEmbedding (MeasurableSpace.mapNatBool Z) :=
    (MeasurableSpace.measurable_mapNatBool Z).measurableEmbedding (MeasurableSpace.injective_mapNatBool Z)
  obtain ⟨decode, hDecode, hId⟩ := hEmb.exists_measurable_extend measurable_id (fun _ => ‹Nonempty Z›)
  refine ⟨decode ∘ Φ, hDecode.comp hΦ, ?_⟩
  have hAE (n : ℕ) : (f ⁻¹' T n) =ᵐ[P] B n := measure_symmDiff_eq_zero_iff.mp (hAB n)
  filter_upwards [ae_all_iff.mpr hAE] with ω hω
  have heq : Φ ω = MeasurableSpace.mapNatBool Z (f ω) := by
    funext n
    have hh := hω n
    change (f ω ∈ T n) = (ω ∈ B n) at hh
    change decide (ω ∈ B n) = decide (f ω ∈ T n)
    exact congrArg (fun p : Prop => decide p) hh.symm
  change f ω = decode (Φ ω)
  rw [heq]
  exact (congrFun hId (f ω)).symm

end IsotropicVariance.Paper.Proofs.Classical
