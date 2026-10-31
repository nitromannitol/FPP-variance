/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Cutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# L² approximation by test functions in the pieces of a partition

Finite diagonal sums of smooth interior cutoffs converge away from the pieces' boundaries.
Disjointness makes each point belong to at most one nonzero summand, giving a uniform L² bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Filter
open scoped Distributions ENNReal Topology BigOperators

namespace IsotropicVariance.Infra.WhiteNoiseProps

/-- Evaluate a finite sum of test functions pointwise. -/
theorem test_sum_apply {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Finset ι) (ψ : ι → 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    (∑ i ∈ F, ψ i) x = ∑ i ∈ F, ψ i x := by
  let ev : 𝓓((⊤ : Opens E), ℝ) →ₗ[ℝ] ℝ :=
    { toFun φ := φ x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact map_sum ev ψ F

/-- The diagonal finite sum of the first `n+1` regional cutoffs. -/
noncomputable def partitionTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℕ → ℕ → 𝓓((⊤ : Opens E), ℝ)) (n : ℕ) : 𝓓((⊤ : Opens E), ℝ) :=
  ∑ i ∈ Finset.range (n + 1), ψ i n

/-- At a point where one region's test is nonzero, all other disjoint-region tests vanish. -/
theorem other_region_test_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : ℕ → Set E} (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (ψ : ℕ → ℕ → 𝓓((⊤ : Opens E), ℝ)) (hs : ∀ i n, tsupport ⇑(ψ i n) ⊆ S i)
    {i j n : ℕ} {x : E} (hi : ψ i n x ≠ 0) (hji : j ≠ i) : ψ j n x = 0 := by
  by_contra hj
  exact Set.disjoint_left.mp (hd hji) (hs j n (subset_tsupport _ hj)) (hs i n (subset_tsupport _ hi))

/-- The diagonal sum of disjoint-region cutoffs obeys the original pointwise absolute bound. -/
theorem abs_partitionTest_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : ℕ → Set E} (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (φ : 𝓓((⊤ : Opens E), ℝ)) (ψ : ℕ → ℕ → 𝓓((⊤ : Opens E), ℝ))
    (hs : ∀ i n, tsupport ⇑(ψ i n) ⊆ S i) (hb : ∀ i n x, |ψ i n x| ≤ |φ x|)
    (n : ℕ) (x : E) : |partitionTest ψ n x| ≤ |φ x| := by
  classical
  rw [partitionTest, test_sum_apply]
  by_cases hx : ∃ i ∈ Finset.range (n + 1), ψ i n x ≠ 0
  · obtain ⟨i, hi, hix⟩ := hx
    rw [Finset.sum_eq_single i]
    · exact hb i n x
    · intro j _ hji
      exact other_region_test_eq_zero hd ψ hs hix hji
    · exact fun hh => (hh hi).elim
  · have hz : ∀ i ∈ Finset.range (n + 1), ψ i n x = 0 := by
      intro i hi
      by_contra hh
      exact hx ⟨i, hi, hh⟩
    rw [Finset.sum_eq_zero hz, abs_zero]
    exact abs_nonneg _

/-- Outside all region boundaries the diagonal approximation converges pointwise. -/
theorem partitionTest_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : ℕ → Set E} (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (φ : 𝓓((⊤ : Opens E), ℝ)) (hφ : tsupport ⇑φ ⊆ ⋃ i, S i)
    (ψ : ℕ → ℕ → 𝓓((⊤ : Opens E), ℝ))
    (hs : ∀ i n, tsupport ⇑(ψ i n) ⊆ interior (S i))
    (hb : ∀ i n x, |ψ i n x| ≤ |φ x|)
    (he : ∀ i x, x ∈ interior (S i) → ∀ᶠ n in atTop, ψ i n x = φ x)
    {x : E} (hx : x ∉ ⋃ i, frontier (S i)) :
    Tendsto (fun n => partitionTest ψ n x) atTop (𝓝 (φ x)) := by
  classical
  have hs' (i n) : tsupport ⇑(ψ i n) ⊆ S i := (hs i n).trans interior_subset
  by_cases hz : φ x = 0
  · have hh (n) : partitionTest ψ n x = 0 := by
      have h := abs_partitionTest_le hd φ ψ hs' hb n x
      rw [hz, abs_zero] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    simpa only [hh, hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hφ (subset_tsupport _ hz))
    have hxb : x ∉ frontier (S i) := fun hh => hx (Set.mem_iUnion.mpr ⟨i, hh⟩)
    have hxi' : x ∈ interior (S i) := by
      by_contra hh
      exact hxb ⟨subset_closure hxi, hh⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [he i x hxi', eventually_ge_atTop i] with n hn hni
    rw [partitionTest, test_sum_apply, Finset.sum_eq_single i, hn]
    · intro j _ hji
      exact other_region_test_eq_zero hd ψ hs' (hn.symm ▸ hz) hji
    · intro hh
      exact (hh (Finset.mem_range.mpr (Nat.lt_succ_of_le hni))).elim

/-- The diagonal approximation converges in spatial mean square for null-boundary partitions. -/
theorem partitionTest_sq_integral_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)]
    {S : ℕ → Set E} (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hfront : ∀ i, volume (frontier (S i)) = 0)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (hφ : tsupport ⇑φ ⊆ ⋃ i, S i)
    (ψ : ℕ → ℕ → 𝓓((⊤ : Opens E), ℝ))
    (hs : ∀ i n, tsupport ⇑(ψ i n) ⊆ interior (S i))
    (hb : ∀ i n x, |ψ i n x| ≤ |φ x|)
    (he : ∀ i x, x ∈ interior (S i) → ∀ᶠ n in atTop, ψ i n x = φ x) :
    Tendsto (fun n => ∫ x, (partitionTest ψ n x - φ x) ^ 2) atTop (𝓝 0) := by
  have hφ2 : Integrable (fun x => φ x ^ 2) := by
    simpa only [pow_two] using integrable_test_mul φ φ
  have hdom (n) (x) : ‖(partitionTest ψ n x - φ x) ^ 2‖ ≤ 4 * φ x ^ 2 := by
    have hb' := abs_partitionTest_le hd φ ψ
      (fun i n => (hs i n).trans interior_subset) hb n x
    have ha := abs_sub (partitionTest ψ n x) (φ x)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh : |partitionTest ψ n x - φ x| ≤ 2 * |φ x| := by linarith only [ha, hb']
    have hh2 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * |φ x|)).mpr hh
    nlinarith only [hh2, sq_abs (partitionTest ψ n x - φ x), sq_abs (φ x)]
  have hnull : volume (⋃ i, frontier (S i)) = 0 := measure_iUnion_null hfront
  have hlim : ∀ᵐ x : E, Tendsto (fun n => (partitionTest ψ n x - φ x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((partitionTest_tendsto hd φ hφ ψ hs hb he hx).sub_const (φ x)).pow 2
  have hcont (n) : Continuous (fun x => (partitionTest ψ n x - φ x) ^ 2) := by fun_prop
  have hh := tendsto_integral_of_dominated_convergence (F := fun n x => (partitionTest ψ n x - φ x) ^ 2)
    (fun x => 4 * φ x ^ 2) (fun n => (hcont n).aestronglyMeasurable)
    (hφ2.const_mul 4) (fun n => Filter.Eventually.of_forall (hdom n)) hlim
  simpa only [integral_zero] using hh

end IsotropicVariance.Infra.WhiteNoiseProps
