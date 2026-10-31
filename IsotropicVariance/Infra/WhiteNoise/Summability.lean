/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Summability facts for the white noise construction

* `summable_inv_one_add_sum_pow`: the weights `(1 + ∑ᵢ kᵢ^{2n})⁻¹` are summable over `ℤ^ι`;
* `measurableSet_setOf_summable_abs_mul`: the set where `∑ⱼ |ωⱼ| uⱼ` converges is measurable;
* `ae_summable_abs_mul`: it has full measure under independent standard Gaussians if `∑ uⱼ < ∞`;
* `measurable_tsum_mul`: random series `ω ↦ ∑' j, aⱼ ωⱼ` are measurable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace IsotropicVariance.Infra.WhiteNoise

/-- A product of summable nonnegative families over a pi type is summable. -/
lemma summable_prod_pi {ι : Type*} [Fintype ι] (g : ℤ → ℝ) (hg0 : ∀ j, 0 ≤ g j)
    (hg : Summable g) : Summable (fun k : ι → ℤ => ∏ i, g (k i)) := by
  classical
  refine summable_of_sum_le (c := (∑' j, g j) ^ Fintype.card ι)
    (fun k => Finset.prod_nonneg fun i _ => hg0 _) fun s => ?_
  set t : ι → Finset ℤ := fun i => s.image (fun k => k i) with ht
  have hsub : s ⊆ Fintype.piFinset t := fun k hk =>
    Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hk
  calc ∑ k ∈ s, ∏ i, g (k i) ≤ ∑ k ∈ Fintype.piFinset t, ∏ i, g (k i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
          Finset.prod_nonneg fun i _ => hg0 _
    _ = ∏ i, ∑ j ∈ t i, g j := (Finset.prod_univ_sum t fun _ => g).symm
    _ ≤ ∏ _i : ι, ∑' j, g j :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => hg0 _)
          fun i _ => hg.sum_le_tsum _ fun j _ => hg0 j
    _ = _ := by simp

/-- The one-dimensional weights `((1 + |j|)²)⁻¹` are summable over `ℤ`. -/
lemma summable_inv_one_add_abs_sq :
    Summable (fun j : ℤ => (((1 : ℝ) + |(j : ℝ)|) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => (((1 : ℝ) + n) ^ 2)⁻¹) := by
    have := (summable_nat_add_iff 1).2 ((Real.summable_nat_pow_inv (p := 2)).2 (by norm_num))
    simpa [add_comm] using this
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h

/-- For `tᵢ ≥ 0`, `∏ᵢ (1 + tᵢ)² ≤ 4ⁿ (1 + ∑ᵢ tᵢ^{2n})`, `n = card ι`. -/
lemma prod_one_add_sq_le {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∏ i, (1 + t i) ^ 2 ≤ 4 ^ Fintype.card ι * (1 + ∑ i, t i ^ (2 * Fintype.card ι)) := by
  have hS : 0 ≤ ∑ i, t i ^ (2 * Fintype.card ι) :=
    Finset.sum_nonneg fun i _ => pow_nonneg (ht i) _
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ t Finset.univ_nonempty
  set T := max 1 (t j) with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have h1 : ∀ i, (1 + t i) ^ 2 ≤ (2 * T) ^ 2 := fun i => by
    have : t i ≤ T := (hj i (Finset.mem_univ i)).trans (le_max_right _ _)
    have : (1 + t i) ≤ 2 * T := by linarith
    exact pow_le_pow_left₀ (by linarith [ht i]) this 2
  have h2 : T ^ (2 * Fintype.card ι) ≤ 1 + ∑ i, t i ^ (2 * Fintype.card ι) := by
    have hsingle : t j ^ (2 * Fintype.card ι) ≤ ∑ i, t i ^ (2 * Fintype.card ι) :=
      Finset.single_le_sum (f := fun i => t i ^ (2 * Fintype.card ι))
        (fun i _ => pow_nonneg (ht i) _) (Finset.mem_univ j)
    rcases max_cases 1 (t j) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [hT, h]; simp only [one_pow]; linarith
    · rw [hT, h]; linarith
  calc ∏ i, (1 + t i) ^ 2 ≤ ∏ _i : ι, (2 * T) ^ 2 :=
        Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) fun i _ => h1 i
    _ = 4 ^ Fintype.card ι * T ^ (2 * Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ]
        ring
    _ ≤ _ := by gcongr

/-- The weights `(1 + ∑ᵢ kᵢ^{2n})⁻¹`, `n = card ι`, are summable over `ℤ^ι`. -/
theorem summable_inv_one_add_sum_pow (ι : Type*) [Fintype ι] :
    Summable (fun k : ι → ℤ => (1 + ∑ i, (k i : ℝ) ^ (2 * Fintype.card ι))⁻¹) := by
  have hs := (summable_prod_pi (ι := ι) _ (fun j => by positivity)
    summable_inv_one_add_abs_sq).mul_left (4 ^ Fintype.card ι)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hs
  · have : 0 ≤ ∑ i, (k i : ℝ) ^ (2 * Fintype.card ι) :=
      Finset.sum_nonneg fun i _ => (even_two_mul _).pow_nonneg _
    positivity
  · have hev : ∀ i, (k i : ℝ) ^ (2 * Fintype.card ι) = |(k i : ℝ)| ^ (2 * Fintype.card ι) :=
      fun i => ((even_two_mul _).pow_abs _).symm
    have key := prod_one_add_sq_le (fun i => |(k i : ℝ)|) fun i => abs_nonneg _
    simp only [← hev] at key
    have hP : 0 < ∏ i, (1 + |(k i : ℝ)|) ^ 2 :=
      Finset.prod_pos fun i _ => by positivity
    have hS : 0 ≤ ∑ i, (k i : ℝ) ^ (2 * Fintype.card ι) :=
      Finset.sum_nonneg fun i _ => (even_two_mul _).pow_nonneg _
    rw [Finset.prod_inv_distrib]
    have h4 : (0 : ℝ) < 4 ^ Fintype.card ι := by positivity
    calc (1 + ∑ i, (k i : ℝ) ^ (2 * Fintype.card ι))⁻¹
        ≤ ((∏ i, (1 + |(k i : ℝ)|) ^ 2) / 4 ^ Fintype.card ι)⁻¹ :=
          inv_anti₀ (by positivity) (by rw [div_le_iff₀ h4]; linarith)
      _ = _ := by field_simp

/-- A nonnegative real family is summable iff the `ℝ≥0∞`-valued sum of its values is finite. -/
lemma summable_iff_tsum_ofReal_ne_top {J : Type*} {f : J → ℝ} (hf : ∀ j, 0 ≤ f j) :
    Summable f ↔ ∑' j, ENNReal.ofReal (f j) ≠ ∞ := by
  have h : ∀ j, ENNReal.ofReal (f j) = ((f j).toNNReal : ℝ≥0∞) := fun j => rfl
  simp_rw [h]
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp [Real.coe_toNNReal _ (hf _)]

lemma measurable_abs_coord {J : Type*} (j : J) (u : J → ℝ) :
    Measurable (fun ω : J → ℝ => ENNReal.ofReal (|ω j| * u j)) :=
  ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun ω : J → ℝ => |ω j| * u j)

/-- The set where `∑ⱼ |ωⱼ| uⱼ` converges is measurable. -/
theorem measurableSet_setOf_summable_abs_mul {J : Type*} [Countable J] {u : J → ℝ}
    (hu0 : ∀ j, 0 ≤ u j) :
    MeasurableSet {ω : J → ℝ | Summable (fun j => |ω j| * u j)} := by
  have h : {ω : J → ℝ | Summable (fun j => |ω j| * u j)} =
      (fun ω : J → ℝ => ∑' j, ENNReal.ofReal (|ω j| * u j)) ⁻¹' {∞}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact summable_iff_tsum_ofReal_ne_top fun j => mul_nonneg (abs_nonneg _) (hu0 j)
  rw [h]
  refine (Measurable.tsum fun j => ?_) (measurableSet_singleton _).compl
  exact measurable_abs_coord j u

/-- Under independent standard Gaussian coordinates, `∑ⱼ |ωⱼ| uⱼ` converges almost surely when
`∑ uⱼ` does. -/
theorem ae_summable_abs_mul {J : Type*} [Countable J] {u : J → ℝ} (hu0 : ∀ j, 0 ≤ u j)
    (hu : Summable u) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : J => gaussianReal 0 1), Summable (fun j => |ω j| * u j) := by
  set P : Measure (J → ℝ) := Measure.infinitePi fun _ : J => gaussianReal 0 1 with hP
  have hc : ∫⁻ x, ENNReal.ofReal |x| ∂(gaussianReal 0 1) < ∞ := by
    have := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by simp)
    have h2 : ∫⁻ x, ‖(id x : ℝ)‖ₑ ∂(gaussianReal 0 1) < ∞ := this.2
    simpa [Real.enorm_eq_ofReal_abs] using h2
  have hmarg : ∀ j, ∫⁻ ω, ENNReal.ofReal |ω j| ∂P = ∫⁻ x, ENNReal.ofReal |x| ∂(gaussianReal 0 1) := by
    intro j
    have hmp := measurePreserving_eval_infinitePi (fun _ : J => gaussianReal 0 1) j
    rw [← hmp.map_eq]
    exact (lintegral_map (f := fun x : ℝ => ENNReal.ofReal |x|)
      (ENNReal.measurable_ofReal.comp continuous_abs.measurable) (measurable_pi_apply j)).symm
  have hint : ∫⁻ ω, ∑' j, ENNReal.ofReal (|ω j| * u j) ∂P < ∞ := by
    rw [lintegral_tsum (f := fun j (ω : J → ℝ) => ENNReal.ofReal (|ω j| * u j))
      fun j => (measurable_abs_coord j u).aemeasurable]
    have : ∀ j, ∫⁻ ω, ENNReal.ofReal (|ω j| * u j) ∂P =
        ENNReal.ofReal (u j) * ∫⁻ x, ENNReal.ofReal |x| ∂(gaussianReal 0 1) := by
      intro j
      simp_rw [ENNReal.ofReal_mul (abs_nonneg _)]
      rw [lintegral_mul_const _ (by fun_prop : Measurable fun ω : J → ℝ =>
        ENNReal.ofReal |ω j|), hmarg j, mul_comm]
    simp_rw [this]
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_lt_top ?_ hc
    exact lt_top_iff_ne_top.2 ((summable_iff_tsum_ofReal_ne_top hu0).1 hu)
  have hmeas : AEMeasurable (fun ω : J → ℝ => ∑' j, ENNReal.ofReal (|ω j| * u j)) P :=
    (Measurable.tsum fun j => measurable_abs_coord j u).aemeasurable
  filter_upwards [ae_lt_top' hmeas hint.ne] with ω hω
  exact (summable_iff_tsum_ofReal_ne_top fun j => mul_nonneg (abs_nonneg _) (hu0 j)).2 hω.ne

/-- Increasing finite sets exhausting a countable type. -/
lemma exists_finset_seq' (J : Type*) [Countable J] :
    ∃ F : ℕ → Finset J, Monotone F ∧ ∀ j, ∃ n, j ∈ F n := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat J
  refine ⟨fun n => (Finset.range n).preimage e he.injOn, fun m n hmn j hj => ?_, fun j => ?_⟩
  · simp only [Finset.mem_preimage, Finset.mem_range] at hj ⊢
    omega
  · exact ⟨e j + 1, by simp⟩

/-- A random series `ω ↦ ∑' j, aⱼ ωⱼ` is measurable (it is `0` where the series diverges). -/
theorem measurable_tsum_mul {J : Type*} [Countable J] (a : J → ℝ) :
    Measurable (fun ω : J → ℝ => ∑' j, a j * ω j) := by
  classical
  set S : Set (J → ℝ) := {ω | Summable (fun j => a j * ω j)} with hS
  have hSm : MeasurableSet S := by
    have h := measurableSet_setOf_summable_abs_mul (J := J) (u := fun j => |a j|)
      (fun j => abs_nonneg _)
    convert h using 1
    ext ω
    simp only [hS, Set.mem_ofPred_eq]
    rw [← summable_abs_iff]
    simp [abs_mul, mul_comm]
  obtain ⟨F, hFm, hFj⟩ := exists_finset_seq' J
  have hFt : Tendsto F atTop atTop := tendsto_atTop_finset_of_monotone hFm hFj
  refine measurable_of_tendsto_metrizable (f := fun n ω => S.indicator
    (fun ω => ∑ j ∈ F n, a j * ω j) ω) (fun n => ?_) (tendsto_pi_nhds.2 fun ω => ?_)
  · refine Measurable.indicator ?_ hSm
    exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _
  · by_cases hω : ω ∈ S
    · simp only [Set.indicator_of_mem hω]
      exact hω.hasSum.comp hFt
    · simp only [Set.indicator_of_notMem hω]
      rw [tsum_eq_zero_of_not_summable hω]
      exact tendsto_const_nhds

end IsotropicVariance.Infra.WhiteNoise
