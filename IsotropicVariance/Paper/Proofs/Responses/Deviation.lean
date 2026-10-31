/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.ProfileResponse
public import IsotropicVariance.Paper.Proofs.Localization.Measurable
import Mathlib.Tactic.Linarith
import IsotropicVariance.Paper.Proofs.Modulus.RadiusPointwise
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# Individual curves are bounded by the localization supremum

The real-valued localization supremum is bounded because the density has a positive lower bound
and the endpoint cubes are bounded. Thus every individual 1-optimal curve is controlled by it,
as used in the tube reduction of the proof of Lemma `lem:blocks`.
-/

@[expose] public section

open Set Metric MeasureTheory

namespace IsotropicVariance.Paper.Proofs.Responses

open Contracts
open Infra.Slab

variable {m : ℕ}

/-- A uniform upper bound justifies evaluating all four real suprema. -/
lemma le_maxSegmentDeviation_of_bound {σ : Pt m → ℝ} {S I I' : Set (Pt m)} {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ u ∈ I, ∀ v ∈ I', ∀ γ : RectifiableCurve (Pt m), IsOneOptimal σ S u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ u v) ≤ B)
    {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I') {γ : RectifiableCurve (Pt m)}
    (hγ : IsOneOptimal σ S u v γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    infDist (γ.toFun t) (segment ℝ u v) ≤ maxSegmentDeviation σ S I I' := by
  let F (u : I) (v : I') (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ})
      (t : Icc (0 : ℝ) 1) := infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m))
  have h1 (u : I) (v : I') (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ}) :
      BddAbove (range (F u v γ)) := ⟨B, by rintro _ ⟨t, rfl⟩; exact hB u u.2 v v.2 γ γ.2 t t.2⟩
  have h2 (u : I) (v : I') : BddAbove (range fun γ => ⨆ t, F u v γ t) :=
    ⟨B, by rintro _ ⟨γ, rfl⟩; exact Real.iSup_le (fun t => hB u u.2 v v.2 γ γ.2 t t.2) hB0⟩
  have h3 (u : I) : BddAbove (range fun v => ⨆ γ, ⨆ t, F u v γ t) :=
    ⟨B, by rintro _ ⟨v, rfl⟩; exact Real.iSup_le (fun γ =>
      Real.iSup_le (fun t => hB u u.2 v v.2 γ γ.2 t t.2) hB0) hB0⟩
  have h4 : BddAbove (range fun u => ⨆ v, ⨆ γ, ⨆ t, F u v γ t) :=
    ⟨B, by rintro _ ⟨u, rfl⟩; exact Real.iSup_le (fun v => Real.iSup_le (fun γ =>
      Real.iSup_le (fun t => hB u u.2 v v.2 γ γ.2 t t.2) hB0) hB0) hB0⟩
  exact (le_ciSup (h1 ⟨u, hu⟩ ⟨v, hv⟩ ⟨γ, hγ⟩) ⟨t, ht⟩).trans
    ((le_ciSup (h2 ⟨u, hu⟩ ⟨v, hv⟩) ⟨γ, hγ⟩).trans
      ((le_ciSup (h3 ⟨u, hu⟩) ⟨v, hv⟩).trans (le_ciSup h4 ⟨u, hu⟩)))

/-- A slab setting supplies the deterministic upper bound needed for its localization supremum. -/
lemma le_maxSegmentDeviation_slab (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) {I I' : Set (Pt m)} (hI : Bornology.IsBounded I)
    (hI' : Bornology.IsBounded I') (ω : X.Ω) {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I')
    {γ : RectifiableCurve (Pt m)} (hγ : IsOneOptimal (sl.density b (X.ρ ω)) sl.set u v γ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    infDist (γ.toFun t) (segment ℝ u v) ≤
      maxSegmentDeviation (sl.density b (X.ρ ω)) sl.set I I' := by
  obtain ⟨a, b', ha, hab⟩ := X.bounds
  obtain ⟨B, hB⟩ := Localization.exists_dist_le_of_isOneOptimal hI hI' ha
    (Localization.le_slabDensity X hb (fun ω x => (hab ω x).1) sl)
    (fun ω u hu v hv => slabTime_le_mul_dist X hb sl ω hu hv)
  apply le_maxSegmentDeviation_of_bound (le_max_right B 0) (B := max B 0) _ hu hv hγ ht
  intro u hu v hv γ hγ t ht
  exact (infDist_le_dist_of_mem (left_mem_segment ℝ u v)).trans
    ((hB ω u hu v hv γ hγ t ht).trans (le_max_left B 0))

end IsotropicVariance.Paper.Proofs.Responses
