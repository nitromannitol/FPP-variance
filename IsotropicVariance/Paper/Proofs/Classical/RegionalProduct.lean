/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.FiniteUnionInfo
public import IsotropicVariance.Infra.Noise.EfronStein

/-! # Independent regional coordinates with the correct product law

The finite union law is used only modulo null events. The resulting independent
Cantor codes have their own marginal laws; no identical-distribution assumption
is made.
-/

@[expose] public section
open MeasureTheory Set
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- An observable of a finite union is almost surely a Borel function of
independent regional codes whose joint law is the product of their marginals. -/
theorem exists_product_representation {m n : ℕ} (N : NoiseModel m) (hn : 0 < n)
    (S : Fin n → Set (Pt m)) (hS : ∀ i, MeasurableSet (S i))
    (hNull : ∀ i, volume (frontier (S i)) = 0)
    (hDisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    {f : N.Ω → Z} (hf : Measurable[N.info (⋃ i, S i)] f) :
    ∃ Φ : Fin n → N.Ω → ℕ → Bool, (∀ i, Measurable[N.info (S i)] (Φ i)) ∧
      ∃ h : (Fin n → ℕ → Bool) → Z, Measurable h ∧
        (f =ᵐ[N.P] fun ω => h (fun i => Φ i ω)) ∧
        N.P.map (fun ω i => Φ i ω) = Measure.pi (fun i => N.P.map (Φ i)) := by
  obtain ⟨g, hg, hfg⟩ := exists_version_finite_union N hn S hS hNull hDisjoint hf
  obtain ⟨Φ, hΦ, h, hh, hgh⟩ := exists_factor_of_measurable_iSup (fun i => N.info (S i)) hg
  refine ⟨Φ, hΦ, h, hh, hfg.trans (Filter.Eventually.of_forall hgh), ?_⟩
  have hd : Pairwise (fun i j => Disjoint (interior (S i)) (interior (S j))) :=
    fun i j hij => (hDisjoint hij).mono interior_subset interior_subset
  simpa only [Measure.infinitePi_eq_pi] using
    Noise.map_regionCoordinates_eq_infinitePi N S hS hNull hd Φ hΦ

end IsotropicVariance.Paper.Proofs.Classical
