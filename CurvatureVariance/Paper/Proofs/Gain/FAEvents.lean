/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.FALocalize
public import CurvatureVariance.Paper.Proofs.Gain.FARate
public import CurvatureVariance.Paper.Proofs.Gain.FAMesh
import CurvatureVariance.Paper.Proofs.Gain.FAClip
import CurvatureVariance.Paper.Proofs.Gain.FACore
import CurvatureVariance.Paper.Proofs.Gain.TubeGeodesics
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The mesh error in one block

An estimate of the finite approximation, equation `eq:labelprofile`, in the proof of Lemma
`lem:labels`: the change of the normalized slab passage time when the endpoints move to the
representatives of their mesh cells is at most `(X_mod + 2c + 2 max(X_pd, 0))/Q_n`, from the
continuity estimate, equation `eq:modulus`, and the comparison, equation `eq:profiledifference`, on
the pair of cubes containing the two faces; its `L^k` norm is bounded by `eLpNorm_meshError_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- **The `L^k` norm of the mesh error** `(X_mod + 2c + 2 max(X_pd, 0))/Q`. -/
theorem eLpNorm_meshError_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Xmod Xpd : Ω → ℝ} {Qn η c Cp : ℝ} (hQ : 0 < Qn) {k : ℕ}
    (hk : 1 ≤ k) (hη : 0 ≤ η) (hc : 0 ≤ c) (hCp : 0 ≤ Cp)
    (hmod : eLpNorm Xmod k P ≤ ENNReal.ofReal (η * Qn))
    (hpd : eLpNorm (fun ω => max (Xpd ω) 0) k P ≤ ENNReal.ofReal Cp) :
    eLpNorm (fun ω => (Xmod ω + 2 * c + 2 * max (Xpd ω) 0) / Qn) k P ≤
      ENNReal.ofReal (η + (2 * c / Qn + 2 * Cp / Qn)) := by
  have hQi : 0 < Qn⁻¹ := inv_pos.mpr hQ
  have hsmul : ∀ (a : ℝ) (f : Ω → ℝ) (b : ℝ), 0 < a → 0 ≤ b →
      eLpNorm f k P ≤ ENNReal.ofReal b → eLpNorm (fun ω => a * f ω) k P ≤ ENNReal.ofReal (a * b) := by
    intro a f b ha hb hf
    have heq : (fun ω => a * f ω) = a • f := rfl
    rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos ha,
      ENNReal.ofReal_mul ha.le]
    gcongr
  have h1 := hsmul Qn⁻¹ Xmod (η * Qn) hQi (by positivity) hmod
  have h2 := hsmul (2 * Qn⁻¹) (fun ω => max (Xpd ω) 0) Cp (by positivity) hCp hpd
  have h3 := eLpNorm_const_le_ofReal (P := P) (by positivity : 0 ≤ 2 * c / Qn) hk
  have h12 := eLpNorm_add_le_ofReal hk (by positivity) (by positivity) h3 h2
  have h := eLpNorm_add_le_ofReal hk (by positivity) (by positivity) h1 h12
  have hη' : Qn⁻¹ * (η * Qn) = η := by field_simp
  have hC' : 2 * Qn⁻¹ * Cp = 2 * Cp / Qn := by field_simp
  rw [hη', hC'] at h
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · congr 1
    funext ω
    field_simp
    ring
  · congr 1

end CurvatureVariance.Paper.Gain
