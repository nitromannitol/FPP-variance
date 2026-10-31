/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.SlabVersion

/-! # Countable codes for a function of independent regional information

Countable reduction of a join of sigma algebras provides one Cantor-valued code
per region. No assumption that the full regional sigma algebras are countably
generated is imposed.
-/

@[expose] public section
open MeasureTheory Set
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical

variable {Ω ι : Type*}

/-- Events belonging to joins of countably generated sub-sigma algebras of the
regional information. This is itself a sigma algebra. -/
@[instance_reducible]
noncomputable def reducedRegionalSpace (G : ι → MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B : ι → ℕ → Set Ω, (∀ i n, MeasurableSet[G i] (B i n)) ∧
    MeasurableSet[⨆ i, MeasurableSpace.generateFrom (range (B i))] A
  measurableSet_empty := by
    refine ⟨fun _ _ => ∅, ?_, ?_⟩
    · intro i _n
      exact @MeasurableSet.empty Ω (G i)
    · exact @MeasurableSet.empty Ω (⨆ _i : ι, MeasurableSpace.generateFrom (range (fun _ : ℕ => (∅ : Set Ω))))
  measurableSet_compl := by
    rintro A ⟨B, hB, hA⟩
    exact ⟨B, hB, hA.compl⟩
  measurableSet_iUnion := by
    intro A hA
    choose B hB hAB using hA
    let D := fun i k => B (Nat.unpair k).1 i (Nat.unpair k).2
    have hD (i : ι) (k : ℕ) : MeasurableSet[G i] (D i k) := hB _ _ _
    have hLe (n : ℕ) : (⨆ i, MeasurableSpace.generateFrom (range (B n i))) ≤
        ⨆ i, MeasurableSpace.generateFrom (range (D i)) := by
      apply iSup_le
      intro i
      apply le_iSup_of_le i
      apply MeasurableSpace.generateFrom_mono
      rintro _ ⟨k, rfl⟩
      exact ⟨Nat.pair n k, by simp only [D, Nat.unpair_pair]⟩
    exact ⟨D, hD, MeasurableSet.iUnion fun n => hLe n _ (hAB n)⟩

/-- Every event in the full join has a countable reduction in each region. -/
theorem iSup_le_reducedRegionalSpace (G : ι → MeasurableSpace Ω) :
    (⨆ i, G i) ≤ reducedRegionalSpace G := by
  apply iSup_le
  intro i A hA
  let B := fun j : ι => fun _ : ℕ => if j = i then A else ∅
  have hB (j : ι) (n : ℕ) : MeasurableSet[G j] (B j n) := by
    by_cases h : j = i
    · subst j
      simpa only [B, ite_eq_left rfl] using hA
    · simp only [B, ite_eq_right h, MeasurableSet.empty]
  refine ⟨B, hB, ?_⟩
  have hGen : MeasurableSet[MeasurableSpace.generateFrom (range (B i))] A :=
    MeasurableSpace.measurableSet_generateFrom ⟨0, by simp only [B, ite_eq_left rfl]⟩
  exact (le_iSup (fun j => MeasurableSpace.generateFrom (range (B j))) i) A hGen

/-- A standard Borel valued function measurable for the join factors through jointly measurable
Cantor codes, one measurable for each regional sigma algebra. -/
theorem exists_factor_of_measurable_iSup (G : ι → MeasurableSpace Ω)
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] {f : Ω → Z}
    (hf : Measurable[⨆ i, G i] f) :
    ∃ Φ : ι → Ω → ℕ → Bool, (∀ i, Measurable[G i] (Φ i)) ∧
      ∃ h : (ι → ℕ → Bool) → Z, Measurable h ∧ ∀ ω, f ω = h (fun i => Φ i ω) := by
  let T := MeasurableSpace.natGeneratingSequence Z
  have hPre (n : ℕ) : ∃ B : ι → ℕ → Set Ω, (∀ i k, MeasurableSet[G i] (B i k)) ∧
      MeasurableSet[⨆ i, MeasurableSpace.generateFrom (range (B i))] (f ⁻¹' T n) :=
    iSup_le_reducedRegionalSpace G _ (hf (MeasurableSpace.measurableSet_natGeneratingSequence (α := Z) n))
  choose B hB hAB using hPre
  let C := fun i k => B (Nat.unpair k).1 i (Nat.unpair k).2
  let Φ := fun i ω k => decide (ω ∈ C i k)
  have hΦ (i : ι) : Measurable[G i] (Φ i) := by
    let _ : MeasurableSpace Ω := G i
    rw [measurable_pi_iff]
    intro k
    apply measurable_to_bool
    have hpre : (fun ω => Φ i ω k) ⁻¹' {true} = C i k := by
      ext ω
      simp only [Φ, mem_preimage, mem_singleton_iff, decide_eq_true_eq]
    rw [hpre]
    exact hB _ _ _
  have hLe (n : ℕ) : (⨆ i, MeasurableSpace.generateFrom (range (B n i))) ≤
      ⨆ i, MeasurableSpace.generateFrom (range (C i)) := by
    apply iSup_le
    intro i
    apply le_iSup_of_le i
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨Nat.pair n k, by simp only [C, Nat.unpair_pair]⟩
  have hfC : Measurable[⨆ i, MeasurableSpace.generateFrom (range (C i))] f := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence (α := Z)]
    apply @measurable_generateFrom Ω Z (⨆ i, MeasurableSpace.generateFrom (range (C i))) _ _
    rintro _ ⟨n, rfl⟩
    exact hLe n _ (hAB n)
  let Ψ := fun ω i => Φ i ω
  have hCodes : (⨆ i, MeasurableSpace.generateFrom (range (C i))) ≤
      (inferInstance : MeasurableSpace (ι → ℕ → Bool)).comap Ψ := by
    apply iSup_le
    intro i
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨k, rfl⟩
    have hEval : Measurable[(inferInstance : MeasurableSpace (ι → ℕ → Bool)).comap Ψ]
        (fun ω => Φ i ω k) :=
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp (comap_measurable Ψ))
    have hSet := hEval (measurableSet_singleton true)
    have hpre : (fun ω => Φ i ω k) ⁻¹' {true} = C i k := by
      ext ω
      simp only [Φ, mem_preimage, mem_singleton_iff, decide_eq_true_eq]
    rwa [hpre] at hSet
  obtain ⟨h, hh, hfh⟩ := (hfC.mono hCodes le_rfl).exists_eq_measurable_comp
  exact ⟨Φ, hΦ, h, hh, fun ω => congrFun hfh ω⟩

end IsotropicVariance.Paper.Proofs.Classical
