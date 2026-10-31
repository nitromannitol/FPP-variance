/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Motion
public import IsotropicVariance.Infra.Example.LocalDensity

/-!
# Rigid motions of white-noise configurations

The pullback `φ ↦ φ ∘ g` by an affine isometry `g` is a continuous linear map of the test
functions (`pullbackCLM`): on each block `𝓓_K` it maps into `𝓓_{g⁻¹ K}` without changing any
seminorm. Its dual `whiteAct g ν = ν ∘ pullbackCLM g` is defined on every configuration, moves
`ν` by `g` in the sense of `WhiteNoiseConfig.IsMovedBy`, and is measurable for the
cylinder σ-algebra.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

namespace IsotropicVariance.Paper.Proofs.Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An affine isometry is its linear part followed by the translation by `g 0`. -/
theorem affineIsometry_eq_add (g : E ≃ᵃⁱ[ℝ] E) (x : E) : g x = g.linearIsometryEquiv x + g 0 := by
  have hh := g.map_vadd (0 : E) x
  simpa only [vadd_eq_add, add_zero] using hh

/-- Composition with an affine isometry preserves the norms of the iterated derivatives. -/
theorem norm_iteratedFDeriv_comp_affineIsometry (g : E ≃ᵃⁱ[ℝ] E) (f : E → ℝ) (x : E) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (f ∘ g) x‖ = ‖iteratedFDeriv ℝ i f (g x)‖ := by
  have heq : (f ∘ g) = (fun z => f (z + g 0)) ∘ g.linearIsometryEquiv := by
    funext z
    simp only [Function.comp_apply, affineIsometry_eq_add g z]
  rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, iteratedFDeriv_comp_add_right,
    ← affineIsometry_eq_add]

/-- The compact set `g⁻¹ K`. -/
noncomputable def pullbackCompacts (g : E ≃ᵃⁱ[ℝ] E) (K : Compacts E) : Compacts E :=
  K.map g.symm g.symm.continuous

theorem mem_pullbackCompacts {g : E ≃ᵃⁱ[ℝ] E} {K : Compacts E} {x : E} :
    x ∈ (pullbackCompacts g K : Set E) ↔ g x ∈ (K : Set E) := by
  change x ∈ g.symm '' (K : Set E) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [g.apply_symm_apply]
  · intro hx
    exact ⟨g x, hx, g.symm_apply_apply x⟩

/-- The pullback by `g` on a block of test functions. -/
noncomputable def pullbackSupportedIn (g : E ≃ᵃⁱ[ℝ] E) (K : Compacts E) :
    𝓓_{K}(E, ℝ) →L[ℝ] 𝓓_{pullbackCompacts g K}(E, ℝ) :=
  ContDiffMapSupportedIn.mkCLM ℝ (fun f => f ∘ g) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun f => f.contDiff.comp g.toAffineIsometry.toContinuousAffineMap.contDiff)
    (fun f x hx => f.zero_on_compl (fun h => hx (mem_pullbackCompacts.mpr h)))
    (fun i _ => ⟨{i}, 1, zero_le_one, fun f x _ => by
      rw [norm_iteratedFDeriv_comp_affineIsometry, Finset.sup_singleton, one_mul]
      exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ⟩)

/-- **The pullback by an affine isometry** as a continuous linear map of the test functions. -/
noncomputable def pullbackCLM (g : E ≃ᵃⁱ[ℝ] E) :
    𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓((⊤ : Opens E), ℝ) :=
  TestFunction.limitCLM ℝ (Infra.WhiteNoiseProps.pullbackTest g)
    (fun K _ => TestFunction.ofSupportedInCLM ℝ (subset_univ _) ∘L pullbackSupportedIn g K)
    (fun _ _ _ => rfl)

@[simp]
theorem pullbackCLM_apply (g : E ≃ᵃⁱ[ℝ] E) (φ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    pullbackCLM g φ x = φ (g x) := rfl

/-- **The action of a rigid motion** on the configurations: `(g · ν)(φ) = ν(φ ∘ g)`. -/
noncomputable def whiteAct (g : E ≃ᵃⁱ[ℝ] E) (ν : WhiteNoiseConfig E) : WhiteNoiseConfig E :=
  ν.comp (pullbackCLM g)

theorem whiteAct_apply (g : E ≃ᵃⁱ[ℝ] E) (ν : WhiteNoiseConfig E) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    whiteAct g ν φ = ν (pullbackCLM g φ) := rfl

/-- The action moves every configuration by `g` (`WhiteNoiseConfig.IsMovedBy`). -/
theorem isMovedBy_whiteAct (g : E ≃ᵃⁱ[ℝ] E) (ν : WhiteNoiseConfig E) :
    WhiteNoiseConfig.IsMovedBy g ν (whiteAct g ν) := by
  intro φ ψ hψ
  rw [whiteAct_apply]
  congr 1
  ext x
  rw [pullbackCLM_apply, hψ, Function.comp_apply]

/-- The action is measurable for the cylinder σ-algebra. -/
theorem measurable_whiteAct (g : E ≃ᵃⁱ[ℝ] E) : Measurable (whiteAct g) :=
  Infra.WhiteNoiseProps.measurable_of_evaluations fun φ =>
    Infra.Example.measurable_whiteNoise_eval (pullbackCLM g φ)

end IsotropicVariance.Paper.Proofs.Bridge
