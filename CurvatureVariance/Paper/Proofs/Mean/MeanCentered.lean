/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centered suprema through a finite mesh

The finite-mesh step of the bound on the fluctuations in the proof of Lemma `lem:smallmean` (the
second paragraph of the proof of [AB26, Lemma 7.1]). Centering a modulus costs at most its
expectation; the finite mesh costs its number of points times the individual norm.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace CurvatureVariance.Paper.Mean

variable {m : ℕ}

/-- The mean of the absolute value of an `L²` variable is at most its `L²` norm bound. -/
theorem integral_norm_le_of_eLpNorm_two_le {P : Measure (Config m)}
    [IsProbabilityMeasure P] {Ω : Config m → ℝ} (hΩm : AEMeasurable Ω P) {BΩ : ℝ}
    (hBΩ : 0 ≤ BΩ) (hΩ2 : eLpNorm Ω 2 P ≤ ENNReal.ofReal BΩ) :
    Integrable Ω P ∧ ∫ ω, ‖Ω ω‖ ∂P ≤ BΩ := by
  have hlt : eLpNorm Ω 2 P < ⊤ := lt_of_le_of_lt hΩ2 ENNReal.ofReal_lt_top
  have h1 : eLpNorm Ω 1 P ≤ eLpNorm Ω 2 P :=
    eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num)
  have hint : Integrable Ω P := by
    refine ⟨hΩm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← eLpNorm_one_eq_lintegral_enorm]
    · exact h1.trans_lt hlt
    · exact hΩm.aestronglyMeasurable
  refine ⟨hint, ?_⟩
  have h2 : ENNReal.ofReal (∫ ω, ‖Ω ω‖ ∂P) = eLpNorm Ω 1 P := by
    rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_norm_eq_lintegral_enorm hint]
    exact hΩm.aestronglyMeasurable
  have := h2.le.trans (h1.trans hΩ2)
  exact (ENNReal.ofReal_le_ofReal_iff hBΩ).1 this


/-- A finite mesh and a uniform modulus bound the centered supremum. The deterministic
profile cancels upon centering. -/
theorem exists_centered_majorant_of_mesh {P : Measure (Config m)} [IsProbabilityMeasure P]
    {p : ℝ≥0∞} (hp : 2 ≤ p)
    {ι : Type*} [DecidableEq ι] (F : ι → Config m → ℝ) (profile : ι → ℝ)
    (hFm : ∀ i, Measurable (F i)) (hFi : ∀ i, Integrable (F i) P)
    (I : Set ι) (G : Finset ι) (select : ι → ι) (hselect : ∀ i ∈ I, select i ∈ G)
    (Z : Config m → ℝ) (hZm : AEMeasurable Z P)
    (hmod : ∀ᵐ ω ∂P, ∀ i ∈ I,
      |(F i ω - profile i) - (F (select i) ω - profile (select i))| ≤ Z ω)
    {B BZ : ℝ} (hB : 0 ≤ B) (hBZ : 0 ≤ BZ)
    (hmesh : ∀ j ∈ G, eLpNorm (fun ω => F j ω - ∫ ω', F j ω' ∂P) p P ≤
      ENNReal.ofReal B)
    (hZ : eLpNorm Z p P ≤ ENNReal.ofReal BZ) :
    ∃ Y : Config m → ℝ, AEMeasurable Y P ∧ (∀ ω, 0 ≤ Y ω) ∧
      (∀ᵐ ω ∂P, ∀ i ∈ I, |F i ω - ∫ ω', F i ω' ∂P| ≤ Y ω) ∧
      eLpNorm Y p P ≤ ENNReal.ofReal ((G.card : ℝ) * B + 2 * BZ) := by
  classical
  have hp1 : 1 ≤ p := (by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp
  have hZ2 : eLpNorm Z 2 P ≤ ENNReal.ofReal BZ :=
    (eLpNorm_le_eLpNorm_of_exponent_le hp).trans hZ
  obtain ⟨hZi, hZE⟩ := integral_norm_le_of_eLpNorm_two_le hZm hBZ hZ2
  let E : ι → ℝ := fun i => ∫ ω, F i ω ∂P
  let V : ι → Config m → ℝ := fun i ω => |F i ω - E i|
  have hVm (i : ι) : Measurable (V i) := (hFm i |>.sub measurable_const).norm
  let M : Config m → ℝ := fun ω => ∑ j ∈ G, V j ω
  have hMm : Measurable M := Finset.measurable_sum G (fun i _ => hVm i)
  have hM0 (ω : Config m) : 0 ≤ M ω := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hDE (i : ι) (hi : i ∈ I) :
      |E i - E (select i) - (profile i - profile (select i))| ≤ BZ := by
    let D : Config m → ℝ := fun ω =>
      F i ω - F (select i) ω - (profile i - profile (select i))
    have hDi : Integrable D P := ((hFi i).sub (hFi (select i))).sub (integrable_const _)
    have hDid : (∫ ω, D ω ∂P) = E i - E (select i) - (profile i - profile (select i)) := by
      dsimp only [D, E]
      rw [integral_sub (f := fun ω => F i ω - F (select i) ω)
          (g := fun _ => profile i - profile (select i))
          ((hFi i).sub (hFi (select i))) (integrable_const _),
        integral_sub (hFi i) (hFi (select i)), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [← hDid]
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans (le_trans _ hZE)
    apply integral_mono_ae hDi.norm hZi.norm
    filter_upwards [hmod] with ω hω
    have hh := hω i hi
    dsimp only [D]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hd : F i ω - F (select i) ω - (profile i - profile (select i)) =
        (F i ω - profile i) - (F (select i) ω - profile (select i)) := by ring
    rw [hd]
    exact hh.trans (le_abs_self _)
  refine ⟨fun ω => M ω + ‖Z ω‖ + BZ, (hMm.aemeasurable.add hZm.norm).add_const _,
    fun ω => by have := hM0 ω; positivity, ?_, ?_⟩
  · filter_upwards [hmod] with ω hω
    intro i hi
    have hle : V (select i) ω ≤ M ω :=
      Finset.single_le_sum (fun j _ => abs_nonneg (F j ω - E j)) (hselect i hi)
    have hh := hω i hi
    have he := hDE i hi
    have hs : F i ω - E i = (F (select i) ω - E (select i)) +
        ((F i ω - profile i) - (F (select i) ω - profile (select i))) -
        (E i - E (select i) - (profile i - profile (select i))) := by ring
    rw [show (∫ ω', F i ω' ∂P) = E i from rfl, hs]
    have ht : |(F (select i) ω - E (select i)) +
        ((F i ω - profile i) - (F (select i) ω - profile (select i))) -
        (E i - E (select i) - (profile i - profile (select i)))| ≤
        |F (select i) ω - E (select i)| +
          |(F i ω - profile i) - (F (select i) ω - profile (select i))| +
          |E i - E (select i) - (profile i - profile (select i))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    apply ht.trans
    dsimp only [V] at hle
    rw [Real.norm_eq_abs]
    linarith only [hle, hh, he, le_abs_self (Z ω)]
  · have hMn : eLpNorm M p P ≤ ENNReal.ofReal ((G.card : ℝ) * B) := by
      have hh := eLpNorm_sum_le (μ := P) (p := p) (f := V) (s := G) hp1
      have hV (j : ι) (hj : j ∈ G) : eLpNorm (V j) p P ≤ ENNReal.ofReal B := by
        have hn := eLpNorm_norm (μ := P) (p := p) (fun ω => F j ω - E j)
          ((hFm j).sub measurable_const).aestronglyMeasurable
        exact hn.le.trans (hmesh j hj)
      have hb := Finset.sum_le_sum (fun j hj => hV j hj)
      have heq : (∑ j ∈ G, ENNReal.ofReal B) = ENNReal.ofReal ((G.card : ℝ) * B) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      have hMeq : M = ∑ j ∈ G, V j := by
        funext ω
        simp only [M, Finset.sum_apply]
      rw [hMeq]
      exact hh.trans (hb.trans_eq heq)
    have hZn : eLpNorm (fun ω => ‖Z ω‖) p P ≤ ENNReal.ofReal BZ :=
      (eLpNorm_norm _ hZm.aestronglyMeasurable).le.trans hZ
    have hBn : eLpNorm (fun _ : Config m => BZ) p P = ENNReal.ofReal BZ := by
      rw [eLpNorm_const _ (ne_of_gt (zero_lt_one.trans_le hp1)) (IsProbabilityMeasure.ne_zero P)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one,
        Real.enorm_eq_ofReal_abs, abs_of_nonneg hBZ]
    have hh := (eLpNorm_add_le (μ := P) (p := p) (f := fun ω => M ω + ‖Z ω‖)
      (g := fun _ => BZ) hp1).trans
      (add_le_add ((eLpNorm_add_le hp1).trans (add_le_add hMn hZn)) hBn.le)
    apply hh.trans_eq
    rw [← ENNReal.ofReal_add (by positivity) hBZ,
      ← ENNReal.ofReal_add (by positivity) hBZ]
    congr 1
    ring

end CurvatureVariance.Paper.Mean
