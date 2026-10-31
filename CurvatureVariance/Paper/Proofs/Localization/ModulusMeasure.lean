/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
public import CurvatureVariance.Infra.Os.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CurvatureVariance.Infra.FPP.Walks
import CurvatureVariance.Infra.Os.Moments
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Positivity

/-!
# Measure-theoretic steps of the continuity estimate (Lemma `lem:modulus`)

For the proof of Lemma `lem:modulus`, equation `eq:modulus`:

* the localization radius `R` of Lemma `lem:localization` is measurable, and Markov's
  inequality turns its moment bound into `P(R > 1/g) ≤ (g C)^q` (`measure_lt_locRadius_le`);
* on `{R ≤ r}`, every vertex of a geodesic between the cubes is within `r W` of the segment joining
  its endpoints (`infDist_le_of_locRadius_le`);
* `L^p` norms of positive parts of `O₁(θ)` variables are at most `2(1 + p!) θ`, and Hölder's
  inequality on an event (`eLpNorm_indicator_le`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-! ## The localization radius -/

/-- The largest deviation of the geodesics between two sets of vertices is measurable. -/
theorem measurable_deviation_isGeodesic (I I' : Set (Vertex m)) :
    Measurable fun ω : Config m => deviation (fun γ => IsGeodesic ω γ) I I' := by
  classical
  unfold deviation
  refine Measurable.iSup fun u => Measurable.iSup fun _ => Measurable.iSup fun v =>
    Measurable.iSup fun _ => Measurable.iSup fun γ => ?_
  have heq : (fun ω : Config m => ⨆ (_ : IsGeodesic ω γ) (x : Vertex m) (_ : x ∈ γ.support),
      ENNReal.ofReal (Metric.infDist (point x) (segment ℝ (point u) (point v)))) =
      fun ω => if IsGeodesic ω γ then ⨆ (x : Vertex m) (_ : x ∈ γ.support),
        ENNReal.ofReal (Metric.infDist (point x) (segment ℝ (point u) (point v))) else ⊥ := by
    funext ω; exact iSup_eq_if _
  rw [heq]
  refine Measurable.ite ?_ measurable_const measurable_const
  change MeasurableSet ({ω : Config m | γ.IsPath} ∩
    {ω : Config m | walkCost ω γ = passageTime ω u v})
  exact (MeasurableSet.const _).inter (measurableSet_eq_fun (Infra.FPP.measurable_walkCost γ)
    (Infra.FPP.measurable_passageTime u v))

/-- The localization radius `R` of Lemma `lem:localization` is measurable. -/
theorem measurable_locRadius (I I' : Set (Vertex m)) (Wl : ℝ) :
    Measurable fun ω : Config m => locRadius ω I I' Wl :=
  ((measurable_deviation_isGeodesic I I').div_const _).const_add 1

/-- Markov's inequality for the localization radius. -/
theorem measure_lt_locRadius_le {P : Measure (Config m)} {I I' : Set (Vertex m)}
    {Wl g Cb : ℝ} {q : ℕ} (hg : 0 < g)
    (h : ∫⁻ ω, locRadius ω I I' Wl ^ q ∂P ≤ ENNReal.ofReal (Cb ^ q)) :
    P {ω | ENNReal.ofReal g⁻¹ < locRadius ω I I' Wl} ≤ ENNReal.ofReal ((g * Cb) ^ q) := by
  have hsub : {ω | ENNReal.ofReal g⁻¹ < locRadius ω I I' Wl} ⊆
      {ω | ENNReal.ofReal (g⁻¹ ^ q) ≤ locRadius ω I I' Wl ^ q} := by
    intro ω hω
    rw [mem_ofPred_eq, ENNReal.ofReal_pow (inv_nonneg.mpr hg.le)]
    exact pow_le_pow_left₀ zero_le hω.le q
  have hne : ENNReal.ofReal (g⁻¹ ^ q) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc P {ω | ENNReal.ofReal g⁻¹ < locRadius ω I I' Wl}
      ≤ P {ω | ENNReal.ofReal (g⁻¹ ^ q) ≤ locRadius ω I I' Wl ^ q} := measure_mono hsub
    _ ≤ (∫⁻ ω, locRadius ω I I' Wl ^ q ∂P) / ENNReal.ofReal (g⁻¹ ^ q) :=
        meas_ge_le_lintegral_div ((measurable_locRadius I I' Wl).pow_const q).aemeasurable hne
          ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Cb ^ q) / ENNReal.ofReal (g⁻¹ ^ q) := by gcongr
    _ = ENNReal.ofReal ((g * Cb) ^ q) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        rw [inv_pow, div_inv_eq_mul, mul_pow, mul_comm]

/-- On `{R ≤ r}`, every vertex of a geodesic between the cubes is within `r W` of the segment
joining its endpoints. -/
theorem infDist_le_of_locRadius_le {ω : Config m} {I I' : Set (Vertex m)} {Wl r : ℝ}
    (hW : 0 < Wl) (hr : 0 ≤ r) (hR : locRadius ω I I' Wl ≤ ENNReal.ofReal r) {u v : Vertex m}
    (hu : u ∈ I) (hv : v ∈ I') {γ : (latticeGraph m).Walk u v} (hγ : IsGeodesic ω γ)
    {x : Vertex m} (hx : x ∈ γ.support) :
    Metric.infDist (point x) (segment ℝ (point u) (point v)) ≤ r * Wl := by
  have h1 : ENNReal.ofReal (Metric.infDist (point x) (segment ℝ (point u) (point v))) ≤
      deviation (fun γ => IsGeodesic ω γ) I I' :=
    le_iSup₂_of_le u hu (le_iSup₂_of_le v hv (le_iSup₂_of_le γ hγ (le_iSup₂_of_le x hx le_rfl)))
  have h2 : deviation (fun γ => IsGeodesic ω γ) I I' / ENNReal.ofReal Wl ≤ ENNReal.ofReal r :=
    le_add_self.trans hR
  have h3 : ENNReal.ofReal (Metric.infDist (point x) (segment ℝ (point u) (point v))) ≤
      ENNReal.ofReal r * ENNReal.ofReal Wl := by
    refine h1.trans ?_
    rwa [ENNReal.div_le_iff (by simpa using hW) ENNReal.ofReal_ne_top] at h2
  rw [← ENNReal.ofReal_mul hr] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hr hW.le)).mp h3

/-! ## `L^p` norms -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The `L^p` norm of the positive part of an `O₁(θ)` variable is at most `2(1 + p!) θ`. -/
theorem eLpNorm_max_le_of_isOs {X : Ω → ℝ} {θ : ℝ} (hX : CurvatureVariance.IsOs P 1 θ X) (hθ : 0 < θ)
    {p : ℕ} (hp : 1 ≤ p) :
    eLpNorm (fun ω => max (X ω) 0) p P ≤
      ENNReal.ofReal (2 * (1 + (p.factorial : ℝ)) * θ) := by
  have hp0 : ((p : ℝ≥0∞)) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hp)
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (ENNReal.natCast_ne_top p)
    (hX.1.max aemeasurable_const).aestronglyMeasurable, ENNReal.toReal_natCast]
  have hint : (∫⁻ ω, ‖max (X ω) 0‖ₑ ^ (p : ℝ) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ (p : ℝ)) ∂P := by
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_of_nonneg (le_max_right _ _), ENNReal.ofReal_rpow_of_nonneg
      (le_max_right _ _) hpr.le]
  rw [hint]
  have hb := hX.lintegral_pos_rpow_le one_pos hθ hpr.le
  rw [div_one, Nat.ceil_natCast] at hb
  have hB : 0 ≤ 2 * (1 + (p.factorial : ℝ)) * θ ^ (p : ℝ) := by positivity
  calc (∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ (p : ℝ)) ∂P) ^ (1 / (p : ℝ))
      ≤ ENNReal.ofReal (2 * (1 + (p.factorial : ℝ)) * θ ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal ((2 * (1 + (p.factorial : ℝ)) * θ ^ (p : ℝ)) ^ (1 / (p : ℝ))) :=
        ENNReal.ofReal_rpow_of_nonneg hB (by positivity)
    _ ≤ ENNReal.ofReal (2 * (1 + (p.factorial : ℝ)) * θ) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hθ.le,
          mul_one_div_cancel hpr.ne', Real.rpow_one]
        apply mul_le_mul_of_nonneg_right _ hθ.le
        have h1 : (1 : ℝ) ≤ 2 * (1 + (p.factorial : ℝ)) := by
          have := (Nat.factorial_pos p); have : (0 : ℝ) ≤ p.factorial := by positivity
          linarith only [this]
        calc (2 * (1 + (p.factorial : ℝ))) ^ (1 / (p : ℝ))
            ≤ (2 * (1 + (p.factorial : ℝ))) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1
                ((div_le_one hpr).mpr (by exact_mod_cast hp))
          _ = 2 * (1 + (p.factorial : ℝ)) := Real.rpow_one _

/-- Hölder's inequality on an event: `‖1_E Z‖_p ≤ ‖Z‖_{2p} P(E)^{1/(2p)}`. -/
theorem eLpNorm_indicator_le {E : Set Ω} (hE : MeasurableSet E) {Z : Ω → ℝ}
    (hZ : AEStronglyMeasurable Z P) {p : ℕ} (hp : 1 ≤ p) :
    eLpNorm (E.indicator Z) p P ≤ eLpNorm Z (2 * p : ℕ) P * P E ^ (1 / (2 * p : ℝ)) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hE]
  have hle : ((p : ℕ) : ℝ≥0∞) ≤ ((2 * p : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : p ≤ 2 * p)
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hle hZ.restrict).trans ?_
  rw [Measure.restrict_apply_univ, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hexp : 1 / (p : ℝ) - 1 / ((2 * p : ℕ) : ℝ) = 1 / (2 * p : ℝ) := by
    push_cast; field_simp; ring
  rw [hexp]
  gcongr
  exact Measure.restrict_le_self

end CurvatureVariance.Paper.Localization.Modulus
