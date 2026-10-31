/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Law
public import IsotropicVariance.Infra.WhiteNoiseProps.Independence
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rigid-motion invariance of the white-noise configuration law

A moved distribution is characterized by `WhiteNoiseConfig.IsMovedBy`. Its test evaluations
are pullbacks, and preservation of spatial volume preserves their Gaussian variances.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace IsotropicVariance.Infra.WhiteNoiseProps

open Example

/-- Pull back a test function by an affine isometry. -/
noncomputable def pullbackTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E ≃ᵃⁱ[ℝ] E) (φ : 𝓓((⊤ : Opens E), ℝ)) : 𝓓((⊤ : Opens E), ℝ) where
  toFun x := φ (g x)
  contDiff' := φ.contDiff.comp g.toAffineIsometry.toContinuousAffineMap.contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph g.toHomeomorph
  tsupport_subset' := by simp

/-- Cylinder measurability can be checked at each test evaluation. -/
theorem measurable_of_evaluations {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace Ω] {V : Ω → WhiteNoiseConfig E}
    (h : ∀ φ : 𝓓((⊤ : Opens E), ℝ), Measurable (fun ω => V ω φ)) : Measurable V := by
  rw [measurable_iff_comap_le]
  change (⨆ φ : 𝓓((⊤ : Opens E), ℝ),
    (inferInstance : MeasurableSpace ℝ).comap (fun ν : WhiteNoiseConfig E => ν φ)).comap V ≤ _
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro φ
  rw [MeasurableSpace.comap_comp]
  exact (h φ).comap_le

/-- Moving by a volume-preserving affine isometry preserves the white-noise predicate. -/
theorem isWhiteNoise_of_isMovedBy {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [MeasurableSpace Ω]
    {W V : Ω → WhiteNoiseConfig E} {P : Measure Ω} (h : IsWhiteNoise W P)
    (g : E ≃ᵃⁱ[ℝ] E) (hg : MeasurePreserving g volume volume)
    (hmoved : ∀ ω, WhiteNoiseConfig.IsMovedBy g (W ω) (V ω)) : IsWhiteNoise V P := by
  have heq (φ : 𝓓((⊤ : Opens E), ℝ)) :
      (fun ω => V ω φ) = (fun ω => W ω (pullbackTest g φ)) := by
    funext ω
    exact hmoved ω φ (pullbackTest g φ) rfl
  refine ⟨measurable_of_evaluations (fun φ => (heq φ).symm ▸ measurable_eval h (pullbackTest g φ)), ?_⟩
  intro φ
  rw [heq φ]
  have hint : (∫ x, pullbackTest g φ x ^ 2) = ∫ x, φ x ^ 2 :=
    hg.integral_comp g.toHomeomorph.measurableEmbedding (fun x => φ x ^ 2)
  simpa only [hint] using h.2 (pullbackTest g φ)

/-- Volume-preserving rigid motions preserve the exact white-noise configuration law. -/
theorem moved_law_eq {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [MeasurableSpace Ω]
    {W V : Ω → WhiteNoiseConfig E} {P : Measure Ω} (h : IsWhiteNoise W P)
    (g : E ≃ᵃⁱ[ℝ] E) (hg : MeasurePreserving g volume volume)
    (hmoved : ∀ ω, WhiteNoiseConfig.IsMovedBy g (W ω) (V ω)) : P.map V = P.map W :=
  law_eq (isWhiteNoise_of_isMovedBy h g hg hmoved) h

/-- Every rigid motion of the paper's Euclidean ambient space preserves Lebesgue volume. -/
theorem measurePreserving_rigidMotion {m : ℕ} (g : Pt m ≃ᵃⁱ[ℝ] Pt m) :
    MeasurePreserving g volume volume := by
  have hg := (measurePreserving_add_right volume (g 0)).comp g.linearIsometryEquiv.measurePreserving
  have heq : (fun x => g.linearIsometryEquiv x + g 0) = g := by
    funext x
    have hh := g.map_vadd (0 : Pt m) x
    simpa only [vadd_eq_add, add_zero] using hh.symm
  simpa only [Function.comp_def, heq] using hg

/-- Every rigid motion, in particular every proper one, preserves the white-noise law on `Pt m`. -/
theorem rigidMotion_law_eq {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W V : Ω → WhiteNoiseConfig (Pt m)} {P : Measure Ω} (h : IsWhiteNoise W P)
    (g : Pt m ≃ᵃⁱ[ℝ] Pt m)
    (hmoved : ∀ ω, WhiteNoiseConfig.IsMovedBy g (W ω) (V ω)) : P.map V = P.map W :=
  moved_law_eq h g (measurePreserving_rigidMotion g) hmoved

/-- Pullback transports topological supports by inverse image. -/
theorem tsupport_pullbackTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E ≃ᵃⁱ[ℝ] E) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    tsupport ⇑(pullbackTest g φ) = g ⁻¹' tsupport ⇑φ :=
  tsupport_comp_eq_preimage φ g.toHomeomorph

/-- Moving the configuration moves its exact regional information. -/
theorem info_of_isMovedBy {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W V : Ω → WhiteNoiseConfig E) (g : E ≃ᵃⁱ[ℝ] E)
    (hmoved : ∀ ω, WhiteNoiseConfig.IsMovedBy g (W ω) (V ω)) (S : Set E) :
    info V (g '' S) = info W S := by
  apply le_antisymm
  · apply iSup_le
    intro φ
    have hs : tsupport ⇑(pullbackTest g φ.val) ⊆ S := by
      rw [tsupport_pullbackTest]
      intro x hx
      obtain ⟨y, hy, hyx⟩ := φ.property hx
      exact g.injective hyx ▸ hy
    have heq : (fun ω => V ω φ.val) = (fun ω => W ω (pullbackTest g φ.val)) := by
      funext ω
      exact hmoved ω φ.val (pullbackTest g φ.val) rfl
    rw [heq]
    exact le_iSup_of_le (⟨pullbackTest g φ.val, hs⟩ : SupportedTests S) le_rfl
  · apply iSup_le
    intro ψ
    have hs : tsupport ⇑(pullbackTest g.symm ψ.val) ⊆ g '' S := by
      rw [tsupport_pullbackTest]
      intro x hx
      exact ⟨g.symm x, ψ.property hx, g.apply_symm_apply x⟩
    have heq : (fun ω => W ω ψ.val) = (fun ω => V ω (pullbackTest g.symm ψ.val)) := by
      funext ω
      symm
      apply hmoved ω (pullbackTest g.symm ψ.val) ψ.val
      funext x
      change ψ.val x = ψ.val (g.symm (g x))
      rw [g.symm_apply_apply]
    rw [heq]
    exact le_iSup_of_le (⟨pullbackTest g.symm ψ.val, hs⟩ : SupportedTests (g '' S)) le_rfl

/-- An action realizing the distributional motion has the exact information comap law. -/
theorem comap_info_act {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Ω → WhiteNoiseConfig E) (g : E ≃ᵃⁱ[ℝ] E) (act : Ω → Ω)
    (hmoved : ∀ ω, WhiteNoiseConfig.IsMovedBy g (W ω) (W (act ω))) (S : Set E) :
    (info W (g '' S)).comap act = info W S := by
  have hh := info_of_isMovedBy W (W ∘ act) g hmoved S
  simpa only [info, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def] using hh

end IsotropicVariance.Infra.WhiteNoiseProps
