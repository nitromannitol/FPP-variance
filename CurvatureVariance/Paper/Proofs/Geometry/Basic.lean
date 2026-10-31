/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Geometry.SupportSubgradient
public import CurvatureVariance.Infra.FPP.Walks

/-!
# Section `sec:prelim`: the deterministic interface between the events and the cone bounds

Two predicates shared by the proofs of the contracts of Section `sec:prelim`:

* `AngularSupport μ t₀ δ c C r₁`: at every slope `τ` with `‖τ − t₀‖ ≤ r₁` there is a subgradient
  `p` of `μ` at `(1, τ)` satisfying the angular bound, equation `eq:angular`:
  `μ(z) − p·z ≥ c|z| ∠(z,(1,τ))² − C|z||τ − t₀|^{2+δ}`; it follows from the second clause of
  `SupportStatement` at `t₀ = M.t₀` and the existence of subgradients
  (`angularSupport_of_support`);
* `ConcentrationOn ω μ B A S`: for all vertices `x, y` of `B`,
  `|T(x,y) − μ(y − x)| ≤ A (S |y − x|^{1/2} + S²)`, the bound (1) of Lemma `lem:good`, which holds
  on the events `𝒢_N(S)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InnerProductGeometry
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- At every slope `τ` with `‖τ − t₀‖ ≤ r₁`, the norm `μ` has a subgradient `p` at `(1, τ)` with the
angular bound, equation `eq:angular`: `c|z| ∠(z,(1,τ))² − C|z||τ − t₀|^{2+δ} ≤ μ(z) − p·z` for
`z ≠ 0`. -/
def AngularSupport (μ : Seminorm ℝ (Pt m)) (t₀ : EuclideanSpace ℝ (Fin m)) (δ c C r₁ : ℝ) :
    Prop :=
  ∀ τ : EuclideanSpace ℝ (Fin m), ‖τ - t₀‖ ≤ r₁ → ∃ p : Pt m,
    inner ℝ p (slopeVec τ) = μ (slopeVec τ) ∧ (∀ z, inner ℝ p z ≤ μ z) ∧
    ∀ z : Pt m, z ≠ 0 →
      c * ‖z‖ * angle z (slopeVec τ) ^ 2 - C * ‖z‖ * ‖τ - t₀‖ ^ (2 + δ) ≤ μ z - inner ℝ p z

/-- Concentration of the passage time on the vertex set `B` at scale `S` with constant `A`:
`|T(x,y) − μ(y − x)| ≤ A (S |y − x|^{1/2} + S²)` for `x, y ∈ B`. -/
def ConcentrationOn (ω : Config m) (μ : Seminorm ℝ (Pt m)) (B : Set (Vertex m)) (A S : ℝ) :
    Prop :=
  ∀ x ∈ B, ∀ y ∈ B, |passageTimeReal ω x y - μ (point y - point x)| ≤
    A * (S * Real.sqrt ‖point y - point x‖ + S ^ 2)

end CurvatureVariance.Paper.Proofs.Geometry
