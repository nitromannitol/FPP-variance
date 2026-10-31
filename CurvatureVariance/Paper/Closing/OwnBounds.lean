/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
import CurvatureVariance.Paper.Proofs.Geometry.PosDef

/-!
# The closing: the bounds of one model

`ownBoundsStatement_holds` proves `Contracts.OwnBoundsStatement`: a model with the standing
hypotheses fits the valid bounds made of its own data. They are its law, `rrem = M.rrem`,
`Crem = max(M.Crem, 0)`, a lower bound `lam > 0` of `q₀` on the unit sphere (positive
definiteness and compactness, `Proofs.Geometry.exists_pos_mul_norm_sq_le_of_posDef`), an upper
bound `Lam ≥ 0` (`Proofs.Geometry.exists_abs_le_mul_norm_sq_of_quadraticForm`), and `T = |t₀|`.
With it the uniform contracts give the theorem at one direction (`Closing.mainTheoremStatement`).
-/

@[expose] public section

namespace CurvatureVariance.Paper.Closing

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- **Every model fits bounds of its own** (`Contracts.OwnBoundsStatement`). -/
theorem ownBoundsStatement_holds (m : ℕ) : OwnBoundsStatement m := by
  intro M hM
  obtain ⟨lam, hlam, hlo⟩ := Proofs.Geometry.exists_pos_mul_norm_sq_le_of_posDef hM.q₀_posDef
  obtain ⟨Lam, hLam, hup⟩ := Proofs.Geometry.exists_abs_le_mul_norm_sq_of_quadraticForm M.q₀
  refine ⟨⟨M.toLaw, M.rrem, max M.Crem 0, lam, Lam, ‖M.t₀‖⟩,
    ⟨⟨hM.one_le_m, hM.probF, hM.assumptionW, hM.probP, hM.iid, hM.timeConstant, hM.delta_pos,
      hM.delta_le_one⟩, hM.rrem_pos, le_max_right _ _, hlam, hLam, norm_nonneg _⟩,
    ⟨rfl, le_rfl, le_max_left _ _, hlo, fun h => (le_abs_self _).trans (hup h), le_rfl⟩⟩

end CurvatureVariance.Paper.Closing
