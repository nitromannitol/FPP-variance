/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Translation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import IsotropicVariance.Infra.TimeConstant.Mean

/-!
# Tools for the almost sure covariance of labels (the proof of Lemma `lem:labels`)

The covariance clause of Lemma `lem:labels` (`IsCovariantAE`: `X_{G+τ}(u+τ, v+τ)`, computed with `ω`
translated by `τ`, equals `X_G(u, v)`) asks, for two blocks of one slab and one choice of the
offset, that moving the noise by the translation `g` taking the corner of one to the corner of the
other moves the label of the first to the label of the second, almost surely. The labels of the
proof of Lemma `lem:labels` do this between any two blocks `(i, z)` and `(i', z')`. The tools:

* `image_constVAdd_block`: the translation maps the block `(i, z)` onto the block `(i', z')`;
* `measure_preimage_eq_of_comp_ae_eq`, `ae_fiberRule_comp_eq`: random variables that agree almost
  surely after moving the noise have the same law on fibers, so a rule reading the fiber
  probabilities (merging the rare values into a most likely one) moves with the noise;
* `isCovariantAE_of_blockTranslation`: the covariance clause from the same fact, in terms of
  `blockTranslation`, for every pair of blocks.

The translation between the corners is `blockTranslation n W i z i' z'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

variable {m : ℕ}

/-- The translation taking the corner of the block `(i, z)` to the corner of the block `(i', z')`.
For `i = i'` and `z' − z` a multiple of `L`, it is the motion of the covariance clause of Lemma
`lem:labels` (`IsCovariantAE`). -/
noncomputable def blockTranslation (n W : ℝ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ) (z' : Fin m → ℤ) :
    Pt m ≃ᵃⁱ[ℝ] Pt m :=
  AffineIsometryEquiv.constVAdd ℝ (Pt m) (blockCorner n W i' z' - blockCorner n W i z)

theorem blockTranslation_apply (n W : ℝ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ) (z' : Fin m → ℤ)
    (x : Pt m) :
    blockTranslation n W i z i' z' x = x + (blockCorner n W i' z' - blockCorner n W i z) := by
  simp [blockTranslation, add_comm]

/-- The translation between corners is a proper rigid motion. -/
theorem isProperRigidMotion_blockTranslation (n W : ℝ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ)
    (z' : Fin m → ℤ) : IsProperRigidMotion (blockTranslation n W i z i' z') :=
  Infra.TimeConstant.isProperRigidMotion_translation _

/-- The longitudinal part of the translation between corners. -/
theorem lon_blockCorner_sub (n W : ℝ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ) (z' : Fin m → ℤ) :
    Pt.lon (blockCorner n W i' z' - blockCorner n W i z) = (i' : ℝ) * n - (i : ℝ) * n := by
  simp [blockCorner]

/-- The transverse part of the translation between corners. -/
theorem tr_blockCorner_sub (n W : ℝ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ) (z' : Fin m → ℤ)
    (k : Fin m) :
    Pt.tr (blockCorner n W i' z' - blockCorner n W i z) k = W * z' k - W * z k := by
  simp [blockCorner]

/-- **The translation between corners maps the block `(i, z)` onto the block `(i', z')`.** -/
theorem image_constVAdd_block (n W : ℝ) (L : ℕ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ)
    (z' : Fin m → ℤ) :
    blockTranslation n W i z i' z' '' block n W L i z = block n W L i' z' := by
  set w := blockCorner n W i' z' - blockCorner n W i z with hw
  have hlon := lon_blockCorner_sub n W i z i' z'
  have htr := tr_blockCorner_sub n W i z i' z'
  ext y
  constructor
  · rintro ⟨x, ⟨h1, h2, h3⟩, rfl⟩
    rw [blockTranslation_apply]
    refine ⟨?_, ?_, fun k => ?_⟩
    · rw [Pt.lon_add, hlon]; linarith
    · rw [Pt.lon_add, hlon]; linarith
    · have hk : Pt.tr (x + w) k = Pt.tr x k + Pt.tr w k := by simp
      rw [hk, htr k]
      obtain ⟨h4, h5⟩ := h3 k
      constructor <;> linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨y - w, ⟨?_, ?_, fun k => ?_⟩, ?_⟩
    · rw [Pt.lon_sub, hlon]; linarith
    · rw [Pt.lon_sub, hlon]; linarith
    · have hk : Pt.tr (y - w) k = Pt.tr y k - Pt.tr w k := by simp
      rw [hk, htr k]
      obtain ⟨h4, h5⟩ := h3 k
      constructor <;> linarith
    · rw [blockTranslation_apply, sub_add_cancel]

/-- **Fibers of random variables that agree after moving the noise have the same probability**:
if `T` preserves `P` and `c' ∘ T = c` almost surely, then `P(c' = v) = P(c = v)`. -/
theorem measure_preimage_eq_of_comp_ae_eq {Ω V : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T P P) {c c' : Ω → V}
    (hc' : ∀ v, MeasurableSet (c' ⁻¹' {v})) (hcc' : (fun ω => c' (T ω)) =ᵐ[P] c) (v : V) :
    P (c' ⁻¹' {v}) = P (c ⁻¹' {v}) := by
  rw [← hT.measure_preimage (hc' v).nullMeasurableSet]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 (hcc'.mono fun ω hω => ?_))
  simp only [mem_preimage, mem_singleton_iff, hω]

/-- **A rule of the fiber probabilities moves with the noise**: if `c' ∘ T = c` almost surely
and `T` preserves `P`, then for any rule `R` that reads the fiber probabilities of a code (such as
merging its rare values into a most likely one), `R(P ∘ c'⁻¹)(c' ∘ T) = R(P ∘ c⁻¹)(c)` almost
surely. -/
theorem ae_fiberRule_comp_eq {Ω V : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {T : Ω → Ω} (hT : MeasurePreserving T P P) {c c' : Ω → V}
    (hc' : ∀ v, MeasurableSet (c' ⁻¹' {v})) (hcc' : (fun ω => c' (T ω)) =ᵐ[P] c)
    (R : (V → ℝ≥0∞) → V → V) :
    (fun ω => R (fun v => P (c' ⁻¹' {v})) (c' (T ω))) =ᵐ[P]
      fun ω => R (fun v => P (c ⁻¹' {v})) (c ω) := by
  have hfib : (fun v => P (c' ⁻¹' {v})) = fun v => P (c ⁻¹' {v}) :=
    funext (measure_preimage_eq_of_comp_ae_eq hT hc' hcc')
  rw [hfib]
  filter_upwards [hcc'] with ω hω
  rw [hω]

/-- **Labels that move with the noise between every pair of blocks are covariant almost
surely**: the clause `IsCovariantAE` is the instance `i = i'`, `z' − z` a multiple of `L`. -/
theorem isCovariantAE_of_blockTranslation {X : Setting.{u} m} (Λ : X.LabelFamily) (n W : ℝ)
    (L : ℕ) (h : ∀ (i i' : ℕ) (z z' : Fin m → ℤ), ∀ᵐ ω ∂X.P,
      Λ.label i' z' (X.act (blockTranslation n W i z i' z') ω) = Λ.label i z ω) :
    IsCovariantAE Λ n W L :=
  fun i z z' _ => h i i z z'

end IsotropicVariance.Paper.Proofs.Gain
