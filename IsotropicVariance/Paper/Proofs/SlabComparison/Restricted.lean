/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Geometry
public import IsotropicVariance.Infra.Curves.Main
public import IsotropicVariance.Infra.Measurability.PassageBounds
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
public import IsotropicVariance.Paper.Defs.Restricted

/-! # Deterministic bounds for passage times restricted to a convex set -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace IsotropicVariance.Paper.Proofs.SlabComparison

variable {m : ℕ}

/-- A straight segment gives the deterministic upper bound in a convex domain. -/
lemma restrictedPassageTime_le_dist {S : Set (Pt m)} (hS : Convex ℝ S) (σ : Pt m → ℝ)
    {b : ℝ} (hb : ∀ x, σ x ≤ b) (hb0 : 0 ≤ b) {u v : Pt m} (hu : u ∈ S) (hv : v ∈ S) :
    restrictedPassageTime σ S u v ≤ b * dist u v := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top _ _))
    (Paper.restrictedInf_le hb hS hu hv)
  simpa only [restrictedInf, restrictedPassageTime, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hb0, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h

/-- Raising the density and restricting the admissible curves can only increase passage time. -/
lemma passageTime_le_restrictedPassageTime {S : Set (Pt m)} (hS : Convex ℝ S)
    (σ τ : Pt m → ℝ) (hστ : ∀ x, σ x ≤ τ x)
    {b : ℝ} (hb : ∀ x, τ x ≤ b) {u v : Pt m} (hu : u ∈ S) (hv : v ∈ S) :
    IsotropicVariance.passageTime σ u v ≤ restrictedPassageTime τ S u v := by
  apply ENNReal.toReal_mono (Paper.restrictedInf_ne_top hb hS hu hv)
  refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun _ => ?_
  exact (iInf_le_of_le γ (iInf_le_of_le h0 (iInf_le _ h1))).trans
    (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hστ (γ.toFun t)))

end IsotropicVariance.Paper.Proofs.SlabComparison
