/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusCover
public import IsotropicVariance.Paper.Proofs.Modulus.ModulusCurves
public import IsotropicVariance.Paper.Contracts.Localization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The modulus on the event of localization (the proof of Lemma `lem:modulus`)

`ModulusData`: the deterministic data of the cut of the 1-optimal curves of a pair of cubes at the
hyperplanes at distance `κn` from the faces, on the event where every such curve stays within `λ` of
its segment. It is abstract in the passage time: `D` is the restricted passage time of a density
`σ ≥ ρ` on a set `S`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Modulus

open Infra.Slab

variable {m : ℕ}

/-- The standing data of the pointwise bound. -/
structure ModulusData (p : CubePair m) (ρ σ : Pt m → ℝ) (S : Set (Pt m)) (B κn lam U : ℝ) :
    Prop where
  hσm : Measurable σ
  hσB : ∀ x, σ x ≤ B
  hρσ : ∀ x, ρ x ≤ σ x
  hopt : ∀ u ∈ p.first, ∀ v ∈ p.second, ∃ γ : RectifiableCurve (Pt m), IsOneOptimal σ S u v γ
  hgood : ∀ u ∈ p.first, ∀ v ∈ p.second, ∀ γ : RectifiableCurve (Pt m),
    IsOneOptimal σ S u v γ → ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ u v) ≤ lam
  hnear : ∀ u ∈ p.first, ∀ x ∈ S, slabCoord p.slab x = κn →
    ‖Pt.tr (p.motion.symm x) - (κn / p.dist) • p.offset‖ ≤
      3 / 2 * lam + Real.sqrt m * ((p.side₁ + p.side₂) / 2) →
    restrictedPassageTime σ S u x - dist u x ≤ U ∧ dist u x - passageTime ρ u x ≤ U
  hfar : ∀ y ∈ S, slabCoord p.slab y = p.dist - κn →
    ‖Pt.tr (p.motion.symm y) - ((p.dist - κn) / p.dist) • p.offset‖ ≤
      3 / 2 * lam + Real.sqrt m * ((p.side₁ + p.side₂) / 2) →
    ∀ v ∈ p.second, restrictedPassageTime σ S y v - dist y v ≤ U ∧
      dist y v - passageTime ρ y v ≤ U

end IsotropicVariance.Paper.Proofs.Modulus
