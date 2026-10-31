/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Mean.MeanArrays
public import CurvatureVariance.Paper.Defs.Cubes
import CurvatureVariance.Paper.Proofs.Responses.Basic
import CurvatureVariance.Infra.FPP.Model
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Canonical centered suprema on slab rows

The centered-profile majorants need not themselves depend only on a slab. The supremum of the actual
slab deviations does, and inherits their moment bounds. This makes the independence required in the
proof of Lemma `lem:smallmean` explicit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Responses

/-- The nonnegative supremum of the centered slab deviations on two consecutive rows. -/
noncomputable def meanSlabSup {m : ℕ} (P : Measure (Config m)) (s w : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j k : Fin m → ℤ) (ω : Config m) : ℝ≥0∞ :=
  ⨆ (u : Vertex m) (_ : u ∈ rowCube s w t i j)
    (v : Vertex m) (_ : v ∈ rowCube s w t (i + 1) k),
    ENNReal.ofReal |slabTimeReal ω (i * s) ((i + 1) * s) u v -
      ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂P|

/-- The actual centered supremum is measurable. -/
theorem measurable_meanSlabSup {m : ℕ} (P : Measure (Config m)) (s w : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j k : Fin m → ℤ) :
    Measurable (meanSlabSup P s w t i j k) := by
  unfold meanSlabSup
  apply Measurable.iSup
  intro u
  apply Measurable.iSup
  intro _hu
  apply Measurable.iSup
  intro v
  apply Measurable.iSup
  intro _hv
  exact (continuous_abs.measurable.comp
    ((measurable_restrictedTime (slabEdges (i * s) ((i + 1) * s)) u v).ennreal_toReal.sub
      measurable_const)).ennreal_ofReal

/-- A slab-local supremum is unchanged when the weights outside the slab are changed. -/
theorem meanSlabSup_congr {m : ℕ} (P : Measure (Config m)) (s w : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j k : Fin m → ℤ)
    {ω ω' : Config m} (hω : ∀ e : Edge m, e.1 ∈ slabEdges (i * s) ((i + 1) * s) → ω e = ω' e) :
    meanSlabSup P s w t i j k ω = meanSlabSup P s w t i j k ω' := by
  unfold meanSlabSup
  congr 1
  funext u
  congr 1
  funext _hu
  congr 1
  funext v
  congr 1
  funext _hv
  have hd := restrictedTime_congr (slabEdges (i * s) ((i + 1) * s)) u v hω
  exact congrArg (fun D : ℝ≥0∞ => ENNReal.ofReal |D.toReal -
    ∫ η, passageTimeReal η 0 ((s : ℤ), v.2 - u.2) ∂P|) hd

/-- Any simultaneous almost sure majorant also bounds the extended supremum. -/
theorem meanSlabSup_le_of_majorant {m : ℕ} (P : Measure (Config m)) (s w : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j k : Fin m → ℤ) {X : Config m → ℝ}
    (hX : ∀ᵐ ω ∂P, ∀ u ∈ rowCube s w t i j, ∀ v ∈ rowCube s w t (i + 1) k,
      |slabTimeReal ω (i * s) ((i + 1) * s) u v -
        ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂P| ≤ X ω) :
    ∀ᵐ ω ∂P, meanSlabSup P s w t i j k ω ≤ ENNReal.ofReal (X ω) := by
  filter_upwards [hX] with ω hω
  exact iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv =>
    ENNReal.ofReal_le_ofReal (hω u hu v hv)

/-- The real supremum inherits every finite moment bound of a simultaneous majorant. -/
theorem eLpNorm_meanSlabSup_le_of_majorant {m : ℕ} (P : Measure (Config m)) (s w : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j k : Fin m → ℤ) {X : Config m → ℝ}
    (hX : ∀ᵐ ω ∂P, ∀ u ∈ rowCube s w t i j, ∀ v ∈ rowCube s w t (i + 1) k,
      |slabTimeReal ω (i * s) ((i + 1) * s) u v -
        ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂P| ≤ X ω)
    (p : ℝ≥0∞) :
    eLpNorm (fun ω => (meanSlabSup P s w t i j k ω).toReal) p P ≤ eLpNorm X p P := by
  apply eLpNorm_mono_ae (measurable_meanSlabSup P s w t i j k).ennreal_toReal.aestronglyMeasurable
  filter_upwards [meanSlabSup_le_of_majorant P s w t i j k hX] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, Real.norm_eq_abs]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hω.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at hb

/-- The real supremum dominates each actual centered deviation wherever a majorant exists. -/
theorem ae_le_meanSlabSup_of_majorant {m : ℕ} (P : Measure (Config m)) (s w : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j k : Fin m → ℤ) {X : Config m → ℝ}
    (hX : ∀ᵐ ω ∂P, ∀ u ∈ rowCube s w t i j, ∀ v ∈ rowCube s w t (i + 1) k,
      |slabTimeReal ω (i * s) ((i + 1) * s) u v -
        ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂P| ≤ X ω) :
    ∀ᵐ ω ∂P, ∀ u ∈ rowCube s w t i j, ∀ v ∈ rowCube s w t (i + 1) k,
      |slabTimeReal ω (i * s) ((i + 1) * s) u v -
        ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂P| ≤
        (meanSlabSup P s w t i j k ω).toReal := by
  filter_upwards [meanSlabSup_le_of_majorant P s w t i j k hX] with ω hω
  intro u hu v hv
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
  exact le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le v (le_iSup_of_le hv le_rfl)))

/-- Dividing by a positive norm bound produces a unit moment bound. -/
theorem eLpNorm_div_le_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : Ω → ℝ) (p : ℝ≥0∞) {B : ℝ} (hB : 0 < B)
    (hf : eLpNorm f p P ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => f ω / B) p P ≤ 1 := by
  have hh : eLpNorm (B⁻¹ • f) p P ≤ 1 := by
    rw [eLpNorm_const_smul]
    calc
      ‖B⁻¹‖ₑ * eLpNorm f p P ≤ ‖B⁻¹‖ₑ * ENNReal.ofReal B := mul_le_mul' le_rfl hf
      _ = 1 := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.2 hB),
          ← ENNReal.ofReal_mul (inv_pos.2 hB).le, inv_mul_cancel₀ hB.ne', ENNReal.ofReal_one]
  change eLpNorm (fun ω => B⁻¹ * f ω) p P ≤ 1 at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- A nonnegative variable of unit `Lᵖ` norm has moment at most one. -/
theorem integral_pow_le_one_of_eLpNorm_le_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ} {p : ℕ} (hp : 0 < p)
    (hpos : ∀ ω, 0 ≤ f ω) (hLp : eLpNorm f p P ≤ 1) :
    Integrable (fun ω => f ω ^ p) P ∧ ∫ ω, f ω ^ p ∂P ≤ 1 := by
  have hmem : MemLp f p P := hLp.trans_lt ENNReal.one_lt_top
  have hint : Integrable (fun ω => f ω ^ p) P := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _)] using hmem.integrable_norm_pow hp.ne'
  have hI : 0 ≤ ∫ ω, f ω ^ p ∂P := integral_nonneg fun ω => pow_nonneg (hpos ω) _
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hroot : eLpNorm f p P =
      ENNReal.ofReal ((∫ ω, f ω ^ p ∂P) ^ (p : ℝ)⁻¹) := by
    simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_of_nonneg (hpos _),
      Real.rpow_natCast] using hmem.eLpNorm_eq_integral_rpow_norm (by positivity) (by simp)
  rw [hroot] at hLp
  have hrootle : (∫ ω, f ω ^ p ∂P) ^ (p : ℝ)⁻¹ ≤ 1 :=
    (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp (by simpa only [ENNReal.ofReal_one] using hLp)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hrootle (Nat.cast_nonneg (α := ℝ) p)
  rw [← Real.rpow_mul hI, inv_mul_cancel₀ hpR, Real.rpow_one, Real.one_rpow] at hh
  exact ⟨hint, hh⟩

open Classical in
/-- Normalized actual slab suprema, set to zero outside a deterministic set of row pairs. -/
noncomputable def meanSlabArray {m K : ℕ} (P : Measure (Config m)) (s w : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (B : ℝ) (adm : (Fin m → ℤ) → (Fin m → ℤ) → Prop)
    (i : Fin K) (j k : Fin m → ℤ) : Config m → ℝ :=
  if adm j k then fun ω => (meanSlabSup P s w t i j k ω).toReal / B else fun _ => 0

end CurvatureVariance.Paper.Mean
