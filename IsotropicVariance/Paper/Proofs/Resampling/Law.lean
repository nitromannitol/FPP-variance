/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Resampling
public import IsotropicVariance.Paper.Proofs.Resampling.Product

/-!
# The law of the resampling

The characterization of `NoiseModel.resampleKernel` and `NoiseModel.resamplingLaw`, Section
`sec:gain`. For `μ = N.resamplingLaw G σ`, the old noise is `Prod.fst` and the new noise of `i` is
`fun p => p.2 i`.

* `resampleKernel_apply`: for `σ ≤ mΩ`, the kernel is `condExpKernel N.P (N.info Gᶜ ⊔ σ)`
  (`info_compl_sup_inf_eq`: `(info Gᶜ ⊔ σ) ⊓ mΩ = info Gᶜ ⊔ σ`).
* `measurePreserving_old`, `measurePreserving_new`: the old noise and each new noise have the law
  of the noise.
* `map_old_new`: the pair `(old, new i)` has the law `P ⊗ₘ resampleKernel (G i) (σ i)`.
* `exchangeable_resamplingLaw`, `Setting.exchangeable_blockResampling`: **the pair `(ω^G, ω)` has
  the law of `(ω, ω^G)`.**
* `ae_mem_iff_new`, `ae_mem_iff_new_of_compl`, `ae_mem_iff_new_of_sigma`: the old and the new noise
  agree on the events of `info (G i)ᶜ` and of `σ i`.
* `resampleKernel_ae_eq`, `resampleKernel_real_ae_eq`: **the conditional law.** For `G` Borel with
  null frontier, `σ ≤ info G` and `A` in `info G`, `resampleKernel G σ ω A = P[1_A | σ](ω)`
  almost surely.
* `resamplingLaw_old_new_pi`: **conditional independence over blocks.**
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory

universe u

namespace IsotropicVariance.Paper

open Proofs.Resampling Proofs.Gain.Bridge

namespace NoiseModel

variable {m : ℕ} (N : NoiseModel.{u} m)

/-! ### The kernel -/

section Kernel

variable (G : Set (Pt m)) {σ : MeasurableSpace N.Ω}

/-- **The conditioning σ-algebra needs no truncation**: for `σ ≤ mΩ`,
`(info Gᶜ ⊔ σ) ⊓ mΩ = info Gᶜ ⊔ σ`. -/
theorem info_compl_sup_inf_eq (hσ : σ ≤ N.measurableSpace) :
    (N.info Gᶜ ⊔ σ) ⊓ N.measurableSpace = N.info Gᶜ ⊔ σ :=
  inf_eq_left.2 (sup_le (N.info_le _) hσ)

/-- The conditioning σ-algebra is a part of the σ-algebra of the noise. -/
theorem info_compl_sup_le (hσ : σ ≤ N.measurableSpace) :
    N.info Gᶜ ⊔ σ ≤ N.measurableSpace :=
  sup_le (N.info_le _) hσ

/-- For `σ ≤ mΩ`, the kernel is the conditional law `P[· | info Gᶜ ⊔ σ]`. -/
theorem resampleKernel_apply (hσ : σ ≤ N.measurableSpace) (ω : N.Ω) :
    letI := N.measurableSpace
    N.resampleKernel G σ ω = condExpKernel N.P (N.info Gᶜ ⊔ σ) ω := by
  let := N.measurableSpace
  simp only [resampleKernel, Kernel.comap_apply, id_eq]
  rw [N.info_compl_sup_inf_eq G hσ]

variable {G}

/-- **The conditional law.** For `G` Borel with null frontier, `σ ≤ info G` and `A` in `info G`, the
kernel at `A` is almost surely the conditional probability of `A` given `σ`: the noise off `G` is
independent of the noise in `G`. -/
theorem resampleKernel_ae_eq (hG : MeasurableSet G) (hGfr : volume (frontier G) = 0)
    (hσ : σ ≤ N.info G) {A : Set N.Ω} (hA : MeasurableSet[N.info G] A) :
    letI := N.measurableSpace
    ∀ᵐ ω ∂N.P, N.resampleKernel G σ ω A = condExpKernel N.P σ ω A := by
  let := N.measurableSpace
  have h := condExpKernel_sup_ae_eq (P := N.P) (N.info_le G) (N.info_le Gᶜ) hσ
    (indep_info_compl N hG hGfr) hA
  rw [sup_comm] at h
  filter_upwards [h] with ω hω
  rw [N.resampleKernel_apply G (hσ.trans (N.info_le G)), hω]

/-- **The conditional law, as a conditional expectation.** For `G` Borel with null frontier,
`σ ≤ info G` and `A` in `info G`, `resampleKernel G σ ω A = P[1_A | σ](ω)` almost surely. -/
theorem resampleKernel_real_ae_eq (hG : MeasurableSet G) (hGfr : volume (frontier G) = 0)
    (hσ : σ ≤ N.info G) {A : Set N.Ω} (hA : MeasurableSet[N.info G] A) :
    (fun ω => (N.resampleKernel G σ ω).real A) =ᵐ[N.P] N.P⟦A | σ⟧ := by
  let := N.measurableSpace
  have h₁ := N.resampleKernel_ae_eq hG hGfr hσ hA
  have h₂ := condExpKernel_ae_eq_condExp (μ := N.P) (hσ.trans (N.info_le G)) (N.info_le G A hA)
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  rw [← hω₂, measureReal_def, measureReal_def, hω₁]

end Kernel

/-! ### The old and the new noise -/

section Law

variable {ι : Type*} (G : ι → Set (Pt m)) (σ : ι → MeasurableSpace N.Ω)

/-- The old noise has the law of the noise. -/
theorem measurePreserving_old :
    letI := N.measurableSpace
    MeasurePreserving Prod.fst (N.resamplingLaw G σ) N.P := by
  let := N.measurableSpace
  exact ⟨measurable_fst, Measure.fst_compProd N.P (N.resamplingKernel G σ)⟩

/-- The pair of the old noise and the new noise of `i` has the law
`P ⊗ₘ resampleKernel (G i) (σ i)`. -/
theorem map_old_new (i : ι) :
    letI := N.measurableSpace
    (N.resamplingLaw G σ).map (fun p => (p.1, p.2 i)) =
      N.P ⊗ₘ N.resampleKernel (G i) (σ i) := by
  let := N.measurableSpace
  exact Proofs.Resampling.map_old_new (N.resamplingKernel_apply G σ) i

variable {G σ} {i : ι}

/-- The new noise of `i` has the law of the noise. -/
theorem measurePreserving_new (hσ : σ i ≤ N.measurableSpace) :
    letI := N.measurableSpace
    MeasurePreserving (fun p => p.2 i) (N.resamplingLaw G σ) N.P := by
  let := N.measurableSpace
  have hm : Measurable fun p : N.Ω × (ι → N.Ω) => (p.1, p.2 i) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  refine ⟨(measurable_pi_apply i).comp measurable_snd, ?_⟩
  have h := map_snd_compProd (N.info_compl_sup_le (G i) hσ) (N.resampleKernel_apply (G i) hσ)
  rw [← N.map_old_new G σ i, Measure.map_map measurable_snd hm] at h
  exact h

/-- **Exchangeability**: the pair `(ω^G, ω)` has the law of `(ω, ω^G)`. -/
theorem exchangeable_resamplingLaw (hσ : σ i ≤ N.measurableSpace) :
    letI := N.measurableSpace
    (N.resamplingLaw G σ).map (fun p => (p.1, p.2 i)) =
      (N.resamplingLaw G σ).map fun p => (p.2 i, p.1) := by
  let := N.measurableSpace
  have hm : Measurable fun p : N.Ω × (ι → N.Ω) => (p.1, p.2 i) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have h := map_swap_compProd (N.info_compl_sup_le (G i) hσ) (N.resampleKernel_apply (G i) hσ)
  rw [← N.map_old_new G σ i, Measure.map_map measurable_swap hm] at h
  exact h.symm

/-- **Agreement.** The old and the new noise of `i` agree on the events of the noise off `G i` and
of `σ i`: every such event happens for both or for neither, almost surely. -/
theorem ae_mem_iff_new (hσ : σ i ≤ N.measurableSpace) {A : Set N.Ω}
    (hA : MeasurableSet[N.info (G i)ᶜ ⊔ σ i] A) :
    ∀ᵐ p ∂(N.resamplingLaw G σ), (p.1 ∈ A ↔ p.2 i ∈ A) := by
  let := N.measurableSpace
  have hm : Measurable fun p : N.Ω × (ι → N.Ω) => (p.1, p.2 i) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have h := ae_mem_iff_compProd (N.info_compl_sup_le (G i) hσ)
    (N.resampleKernel_apply (G i) hσ) hA
  rw [← N.map_old_new G σ i] at h
  exact ae_of_ae_map hm.aemeasurable h

/-- Every event of the noise off `G i` happens for the old noise and the new noise of `i`, or for
neither, almost surely. -/
theorem ae_mem_iff_new_of_compl (hσ : σ i ≤ N.measurableSpace) {A : Set N.Ω}
    (hA : MeasurableSet[N.info (G i)ᶜ] A) :
    ∀ᵐ p ∂(N.resamplingLaw G σ), (p.1 ∈ A ↔ p.2 i ∈ A) :=
  N.ae_mem_iff_new hσ (le_sup_left (a := N.info (G i)ᶜ) (b := σ i) A hA)

/-- Every event of `σ i` happens for the old noise and the new noise of `i`, or for neither, almost
surely: the label is unchanged. -/
theorem ae_mem_iff_new_of_sigma (hσ : σ i ≤ N.measurableSpace) {A : Set N.Ω}
    (hA : MeasurableSet[σ i] A) :
    ∀ᵐ p ∂(N.resamplingLaw G σ), (p.1 ∈ A ↔ p.2 i ∈ A) :=
  N.ae_mem_iff_new hσ (le_sup_right (a := N.info (G i)ᶜ) (b := σ i) A hA)

/-- **Conditional independence over blocks.** Given the old noise, the new noises of a finite set of
indices are independent, with the laws `resampleKernel (G i) (σ i) ω`. -/
theorem resamplingLaw_old_new_pi (G : ι → Set (Pt m)) (σ : ι → MeasurableSpace N.Ω) (s : Finset ι)
    {C : Set N.Ω} (hC : MeasurableSet[N.measurableSpace] C) {A : ι → Set N.Ω}
    (hA : ∀ i ∈ s, MeasurableSet[N.measurableSpace] (A i)) :
    N.resamplingLaw G σ {p | p.1 ∈ C ∧ ∀ i ∈ s, p.2 i ∈ A i} =
      ∫⁻ ω in C, ∏ i ∈ s, N.resampleKernel (G i) (σ i) ω (A i) ∂N.P := by
  let := N.measurableSpace
  have hset : {p : N.Ω × (ι → N.Ω) | p.1 ∈ C ∧ ∀ i ∈ s, p.2 i ∈ A i} = C ×ˢ (s : Set ι).pi A := by
    ext p
    simp
  rw [hset]
  exact compProd_prod_pi (N.resamplingKernel_apply G σ) hC s hA

end Law

end NoiseModel

namespace Setting

variable {m : ℕ} (X : Setting.{u} m)

/-- **Exchangeability of the resampling of a block**: the pair `(ω^G, ω)` has the law of
`(ω, ω^G)`. -/
theorem exchangeable_blockResampling (n W : ℝ) (L : ℕ) {σ : BlockIdx m → MeasurableSpace X.Ω}
    (c : BlockIdx m) (hσ : σ c ≤ X.measurableSpace) :
    letI := X.measurableSpace
    (X.blockResampling n W L σ).map (fun p => (p.1, p.2 c)) =
      (X.blockResampling n W L σ).map fun p => (p.2 c, p.1) :=
  X.exchangeable_resamplingLaw hσ

end Setting

end IsotropicVariance.Paper
