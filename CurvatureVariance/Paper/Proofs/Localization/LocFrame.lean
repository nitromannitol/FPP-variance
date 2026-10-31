/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.RadiusCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Shear
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes

/-!
# Lemma `lem:localization`: the line through the center of `I`

The proof of Lemma `lem:localization` measures the vertices of the paths from the line `ū + ℝ(1, t)`
through the center `ū = (p, c)` of `I`:

* `Loc.ofs t p c x`: the offset `x₂ − c − (x₁ − p) t` of `x` from the line, in its hyperplane;
* `Loc.lineSet`, `Loc.distLine`: the line and the Euclidean distance to it, which defines the
  annuli of the paper;
* `distLine_le_norm_ofs`, `norm_ofs_le`: the two are comparable, up to the factor `1 + T`,
  `‖t‖ ≤ T`.
* `dist_segment_le`: the distance to `[u, v]` from the offset and the first coordinate.
-/

@[expose] public section

open MeasureTheory Set InnerProductGeometry
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper Radius

variable {m : ℕ}

/-- The point `ū = (p, c)`. -/
def basePt (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) : Pt m := WithLp.toLp 2 ((p : ℝ), c)

@[simp] theorem basePt_fst (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) :
    (basePt p c).fst = (p : ℝ) := rfl

@[simp] theorem basePt_snd (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) : (basePt p c).snd = c := rfl

/-- The offset of `x` from the line `ū + ℝ(1, t)`, in the hyperplane of `x`. -/
noncomputable def ofs (t : EuclideanSpace ℝ (Fin m)) (p : ℤ) (c : EuclideanSpace ℝ (Fin m))
    (x : Vertex m) : EuclideanSpace ℝ (Fin m) :=
  transOff t (point x - basePt p c)

theorem ofs_apply (t : EuclideanSpace ℝ (Fin m)) (p : ℤ) (c : EuclideanSpace ℝ (Fin m))
    (x : Vertex m) (i : Fin m) :
    ofs t p c x i = (x.2 i : ℝ) - c i - ((x.1 : ℝ) - p) * t i := by
  simp [ofs, transOff, transversePoint]

theorem ofs_sub_ofs (t : EuclideanSpace ℝ (Fin m)) (p : ℤ) (c : EuclideanSpace ℝ (Fin m))
    (x y : Vertex m) : ofs t p c x - ofs t p c y = transOff t (point x - point y) := by
  simp only [ofs, ← transOff_sub]
  congr 1
  abel

/-- `(1, t)` has no offset from `ℝ(1, t)`. -/
theorem transOff_smul_slopeVec (t : EuclideanSpace ℝ (Fin m)) (r : ℝ) :
    transOff t (r • slopeVec t) = 0 := by
  simp [transOff, slopeVec]

/-- The offset is at most `(1 + T)` times the norm, for `‖t‖ ≤ T`. -/
theorem norm_transOff_le {t : EuclideanSpace ℝ (Fin m)} {T : ℝ} (ht : ‖t‖ ≤ T) (z : Pt m) :
    ‖transOff t z‖ ≤ (1 + T) * ‖z‖ := by
  have h1 : ‖transOff t z‖ ≤ ‖z.snd‖ + ‖z.fst • t‖ := norm_sub_le _ _
  have h2 := Proofs.Geometry.norm_snd_le_norm z
  have h3 := Proofs.Geometry.abs_fst_le_norm z
  rw [norm_smul, Real.norm_eq_abs] at h1
  have h4 : |z.fst| * ‖t‖ ≤ ‖z‖ * T := mul_le_mul h3 ht (norm_nonneg _) (norm_nonneg _)
  linarith only [h1, h2, h4]

/-- The line `ū + ℝ(1, t)`. -/
def lineSet (t : EuclideanSpace ℝ (Fin m)) (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) : Set (Pt m) :=
  Set.range fun r : ℝ => basePt p c + r • slopeVec t

/-- The Euclidean distance from `x` to the line `ū + ℝ(1, t)`. -/
noncomputable def distLine (t : EuclideanSpace ℝ (Fin m)) (p : ℤ) (c : EuclideanSpace ℝ (Fin m))
    (x : Vertex m) : ℝ :=
  Metric.infDist (point x) (lineSet t p c)

theorem distLine_nonneg (t : EuclideanSpace ℝ (Fin m)) (p : ℤ) (c : EuclideanSpace ℝ (Fin m))
    (x : Vertex m) : 0 ≤ distLine t p c x :=
  Metric.infDist_nonneg

/-- The distance to the line is at most the offset. -/
theorem distLine_le_norm_ofs (t : EuclideanSpace ℝ (Fin m)) (p : ℤ)
    (c : EuclideanSpace ℝ (Fin m)) (x : Vertex m) : distLine t p c x ≤ ‖ofs t p c x‖ := by
  have hmem : basePt p c + (point x - basePt p c).fst • slopeVec t ∈ lineSet t p c := ⟨_, rfl⟩
  refine (Metric.infDist_le_dist_of_mem hmem).trans ?_
  rw [dist_eq_norm]
  have e : point x - (basePt p c + (point x - basePt p c).fst • slopeVec t) =
      transVec (ofs t p c x) := by
    have h := eq_fst_smul_add_transVec t (point x - basePt p c)
    have e2 : point x - (basePt p c + (point x - basePt p c).fst • slopeVec t) =
        (point x - basePt p c) - (point x - basePt p c).fst • slopeVec t := by abel
    rw [e2]
    conv_lhs => rw [h]
    simp [ofs]
  rw [e, norm_transVec]

/-- The offset is at most `1 + T` times the distance to the line, for `‖t‖ ≤ T`. -/
theorem norm_ofs_le {t : EuclideanSpace ℝ (Fin m)} {T : ℝ} (ht : ‖t‖ ≤ T) (p : ℤ)
    (c : EuclideanSpace ℝ (Fin m)) (x : Vertex m) :
    ‖ofs t p c x‖ ≤ (1 + T) * distLine t p c x := by
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  have hT1 : 0 < 1 + T := by linarith only [hT]
  have hne : (lineSet t p c).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  rw [← div_le_iff₀' hT1, distLine, Metric.le_infDist hne]
  rintro _ ⟨r, rfl⟩
  rw [div_le_iff₀' hT1, dist_eq_norm]
  have e : ofs t p c x = transOff t (point x - (basePt p c + r • slopeVec t)) := by
    have e2 : point x - basePt p c = (point x - (basePt p c + r • slopeVec t)) +
        r • slopeVec t := by abel
    rw [ofs, e2, transOff_add, transOff_smul_slopeVec, add_zero]
  rw [e]
  exact norm_transOff_le ht _

/-- **The distance to `[u, v]`** from the offset and the first coordinate: for `u₁ < v₁`, offsets of
`u` and `v` at most `Γ`, and first coordinate of `x` within `Ω` of `[u₁, v₁]`,
`dist(x, [u, v]) ≤ ‖ofs x‖ + Γ + (1 + T) Ω`. -/
theorem dist_segment_le {t : EuclideanSpace ℝ (Fin m)} {T : ℝ} (ht : ‖t‖ ≤ T) {p : ℤ}
    {c : EuclideanSpace ℝ (Fin m)} {x u v : Vertex m} {Γ Ω : ℝ} (huv : u.1 < v.1)
    (hu : ‖ofs t p c u‖ ≤ Γ) (hv : ‖ofs t p c v‖ ≤ Γ) (hΩ : 0 ≤ Ω)
    (hxv : (x.1 : ℝ) - v.1 ≤ Ω) (hux : (u.1 : ℝ) - x.1 ≤ Ω) :
    Metric.infDist (point x) (segment ℝ (point u) (point v)) ≤
      ‖ofs t p c x‖ + Γ + (1 + T) * Ω :=
  infDist_segment_le t ht (X := point x) (U := point u) (V := point v) (A := basePt p c)
    (by simpa using (show (u.1 : ℝ) < v.1 by exact_mod_cast huv)) hu hv hΩ
    (by simpa using hxv) (by simpa using hux)

end CurvatureVariance.Paper.Localization.Loc
