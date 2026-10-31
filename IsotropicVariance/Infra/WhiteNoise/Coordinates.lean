/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Orthonormal coordinates on a finite-dimensional inner product space

For a finite-dimensional real inner product space `E` (for example `Pt m`), `coordBasis E` is a
fixed orthonormal basis indexed by `Coord E = Fin (finrank ℝ E)`, and `coord x i = ⟪bᵢ, x⟫`. The
coordinate map is a volume-preserving measurable equivalence onto `Coord E → ℝ` with Lebesgue
measure (`measurePreserving_coordEquiv`), linear and `1`-Lipschitz in each coordinate.
-/

@[expose] public section

open MeasureTheory

namespace IsotropicVariance.Infra.WhiteNoise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in
/-- The index type of the orthonormal coordinates of `E`. -/
abbrev Coord : Type := Fin (Module.finrank ℝ E)

variable (E) in
/-- The fixed orthonormal basis of `E`. -/
noncomputable def coordBasis : OrthonormalBasis (Coord E) ℝ E :=
  stdOrthonormalBasis ℝ E

/-- The orthonormal coordinates `coord x i = ⟪bᵢ, x⟫`. -/
noncomputable def coord (x : E) : Coord E → ℝ :=
  WithLp.ofLp ((coordBasis E).repr x)

theorem coord_apply (x : E) (i : Coord E) : coord x i = inner ℝ (coordBasis E i) x := by
  simp [coord, OrthonormalBasis.repr_apply_apply]

variable (E) in
/-- The coordinate map as a continuous linear map. -/
noncomputable def coordCLM : E →L[ℝ] Coord E → ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Coord E => ℝ).toContinuousLinearMap.comp
    (coordBasis E).repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem coordCLM_apply (x : E) : coordCLM E x = coord x := rfl

/-- A coordinate is bounded by the norm. -/
theorem abs_coord_le (x : E) (i : Coord E) : |coord x i| ≤ ‖x‖ := by
  rw [coord_apply]
  calc |inner ℝ (coordBasis E i) x| ≤ ‖coordBasis E i‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ = ‖x‖ := by rw [(coordBasis E).orthonormal.1 i, one_mul]

/-- The coordinates of a basis vector. -/
theorem coord_coordBasis (i j : Coord E) :
    coord (coordBasis E j) i = if i = j then 1 else 0 := by
  rw [coord_apply, orthonormal_iff_ite.1 (coordBasis E).orthonormal]

/-- A coordinate is a continuous linear functional. -/
theorem contDiff_coord (i : Coord E) {n : WithTop ℕ∞} : ContDiff ℝ n fun x : E => coord x i := by
  simp_rw [coord_apply]
  exact contDiff_const.inner ℝ contDiff_id

variable [MeasurableSpace E] [BorelSpace E]

variable (E) in
/-- The coordinate map as a measurable equivalence onto `Coord E → ℝ`. -/
noncomputable def coordEquiv : E ≃ᵐ (Coord E → ℝ) :=
  (coordBasis E).measurableEquiv.trans (MeasurableEquiv.toLp 2 (Coord E → ℝ)).symm

theorem coe_coordEquiv : ⇑(coordEquiv E) = coord := rfl

/-- **The orthonormal coordinates preserve volume.** -/
theorem measurePreserving_coordEquiv : MeasurePreserving (coordEquiv E) volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Coord E)).comp
    (coordBasis E).measurePreserving_measurableEquiv

theorem measurable_coord : Measurable (coord : E → Coord E → ℝ) := by
  rw [← coe_coordEquiv]; exact (coordEquiv E).measurable

end IsotropicVariance.Infra.WhiteNoise
