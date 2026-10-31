/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Locality
public import IsotropicVariance.Paper.Proofs.Localization.Curves
import Mathlib.Tactic.Linarith

/-!
# Passage-time comparison away from a replaced block

The competitor step of Section `sec:gain`, before Lemma `lem:blocks`: agreement along all
old 1-optimal curves gives a nonpositive change in the restricted passage time. This uses curves
arbitrarily close to the infimum, rather than assuming that a geodesic exists for a Borel density.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace IsotropicVariance.Paper.Proofs.Responses

variable {m : ℕ}

/-- Agreement of two densities along every old 1-optimal curve prevents the restricted passage
time from increasing. -/
theorem restrictedPassageTime_le_of_oneOptimal_congr {σ σ' : Pt m → ℝ} {S : Set (Pt m)}
    (hS : Convex ℝ S) {B B' : ℝ} (hB : ∀ x, σ x ≤ B) (hB' : ∀ x, σ' x ≤ B')
    {u v : Pt m} (hu : u ∈ S) (hv : v ∈ S)
    (h : ∀ γ : RectifiableCurve (Pt m), IsOneOptimal σ S u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, σ (γ.toFun t) = σ' (γ.toFun t)) :
    restrictedPassageTime σ' S u v ≤ restrictedPassageTime σ S u v := by
  have hfin := restrictedInf_ne_top hB hS hu hv
  have hfin' := restrictedInf_ne_top hB' hS hu hv
  by_contra hnot
  have hlt : restrictedPassageTime σ S u v < restrictedPassageTime σ' S u v :=
    lt_of_not_ge hnot
  let r := min (restrictedPassageTime σ S u v + 1) (restrictedPassageTime σ' S u v)
  have hr : restrictedPassageTime σ S u v < r :=
    lt_min (lt_add_one _) hlt
  have hinf : restrictedInf σ S u v < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hr
  simp only [restrictedInf, iInf_lt_iff] at hinf
  obtain ⟨γ, h0, h1, hγS, hcost⟩ := hinf
  have hγ : IsOneOptimal σ S u v γ := by
    refine ⟨h0, h1, hγS, hcost.le.trans ?_⟩
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hsame := γ.cost_congr (ρ := fun x => ENNReal.ofReal (σ x))
    (σ := fun x => ENNReal.ofReal (σ' x))
    (fun t ht => congrArg ENNReal.ofReal (h γ hγ t ht))
  have hnew : restrictedInf σ' S u v < ENNReal.ofReal r :=
    (restrictedInf_le_cost γ h0 h1 hγS).trans_lt (hsame ▸ hcost)
  have hrnew : r ≤ restrictedPassageTime σ' S u v := min_le_right _ _
  have hle : ENNReal.ofReal r ≤ restrictedInf σ' S u v := by
    rw [← ENNReal.ofReal_toReal hfin']
    exact ENNReal.ofReal_le_ofReal hrnew
  exact hnew.not_ge hle

/-- If a block misses the unit neighborhood of every old 1-optimal curve, replacing its noise
cannot increase the slab passage time. -/
theorem IsBlockCoupling.ae_slabTime_le_of_oneOptimal_far {X : Setting m} {G : Set (Pt m)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hcpl : X.IsBlockCoupling G P' old new) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) (hsl : Convex ℝ sl.set) :
    ∀ᵐ ω ∂P', ∀ u ∈ sl.set, ∀ v ∈ sl.set,
      (∀ γ : RectifiableCurve (Pt m), IsOneOptimal (sl.density b (X.ρ (old ω))) sl.set u v γ →
        ∀ t ∈ Icc (0 : ℝ) 1, 1 < infDist (γ.toFun t) G) →
      X.slabTime b sl (new ω) u v ≤ X.slabTime b sl (old ω) u v := by
  filter_upwards [Gain.IsBlockCoupling.ae_rho_eq hcpl] with ω hω u hu v hv hfar
  apply restrictedPassageTime_le_of_oneOptimal_congr hsl
    (fun x => (sl.density_le b (hb (old ω)) x).trans (max_self b).le)
    (fun x => (sl.density_le b (hb (new ω)) x).trans (max_self b).le) hu hv
  intro γ hγ t ht
  unfold Slab.density
  split_ifs
  · rfl
  · exact hω _ (hfar γ hγ t ht)

end IsotropicVariance.Paper.Proofs.Responses
