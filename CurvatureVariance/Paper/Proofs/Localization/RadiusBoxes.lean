/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.RadiusGeometry
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:localization`: the boxes

The boxes of the proof of Lemma `lem:localization`: in the frame of the auxiliary point `a`, a
lattice point `x` has longitudinal coordinate `x₁ − a₁` and transverse offset
`off t a x = transOff t (x − a)` from the line through `a` of slope `t`. Its box index is
`j = ⌊off / W⌋ ∈ ℤ^m` (the level `|j|₁`) and `k = ⌊(x₁ − a₁ − s₀) / ρ_j⌋`, where the longitudinal
length `ρ_j ≈ ℓ / (2²⁰ (|j|₁ + m + 1))` of the boxes decreases with the level, so that the
thickening along the slopes of the boxes stays inside a transverse cube of side `2W` (the paper's
thickenings by `c₀ℓ/β`).

Each box is inside the transverse cube `boxCube` thickened along the slope from `a` (pair 1) and
along the slope to `a'` (pair 2); both pairs satisfy `IsCubePair`, so Proposition `prop:profiles`
controls `T(a, x)` and `T(x, a')` on the box with one `O₁` variable each.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Radius

open CurvatureVariance.Paper

variable {m : ℕ}

/-! ## Boxes inside thickened cubes -/

/-- Thickening is monotone in the radius. -/
theorem thicken_mono {I : Set (Vertex m)} {t : EuclideanSpace ℝ (Fin m)} {r r' : ℝ} (h : r ≤ r') :
    thicken I t r ⊆ thicken I t r' := by
  rintro x ⟨u, hu, τ, hτ, hx⟩
  exact ⟨u, hu, τ, hτ.trans h, hx⟩

end CurvatureVariance.Paper.Localization.Radius
