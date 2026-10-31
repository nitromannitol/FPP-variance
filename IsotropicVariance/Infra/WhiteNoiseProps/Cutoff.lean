/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoiseProps.Independence
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth interior cutoffs for regional white-noise information

A smooth positive defining function for an open set gives cutoffs with topological support
inside that set. Multiplication by a test function keeps their supports compact.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Filter
open scoped Distributions ENNReal Topology

namespace IsotropicVariance.Infra.WhiteNoiseProps

/-- Cut off a test function away from the zero set of a smooth nonnegative defining function. -/
noncomputable def cutoffTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓓((⊤ : Opens E), ℝ)) (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    𝓓((⊤ : Opens E), ℝ) where
  toFun x := φ x * Real.smoothTransition (((n : ℝ) + 1) * f x - 1)
  contDiff' := φ.contDiff.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul hf).sub contDiff_const))
  hasCompactSupport' := φ.hasCompactSupport.mul_right
  tsupport_subset' := by simp

/-- A cutoff is bounded by its original test function. -/
theorem abs_cutoffTest_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓓((⊤ : Opens E), ℝ)) (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : E) :
    |cutoffTest φ f hf n x| ≤ |φ x| := by
  change |φ x * Real.smoothTransition (((n : ℝ) + 1) * f x - 1)| ≤ _
  rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.le_one _)

/-- The topological support of the cutoff lies where its defining function is strictly positive. -/
theorem tsupport_cutoffTest_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓓((⊤ : Opens E), ℝ)) (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    tsupport ⇑(cutoffTest φ f hf n) ⊆ Function.support f := by
  have hc : IsClosed {x : E | 1 ≤ ((n : ℝ) + 1) * f x} :=
    isClosed_le continuous_const (continuous_const.mul hf.continuous)
  have hs : Function.support ⇑(cutoffTest φ f hf n) ⊆ {x | 1 ≤ ((n : ℝ) + 1) * f x} := by
    intro x hx
    by_contra hn
    have hz : Real.smoothTransition (((n : ℝ) + 1) * f x - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr (le_of_not_ge hn))
    exact hx (by change φ x * Real.smoothTransition _ = 0; rw [hz, mul_zero])
  have hts : tsupport ⇑(cutoffTest φ f hf n) ⊆ {x | 1 ≤ ((n : ℝ) + 1) * f x} :=
    closure_minimal hs hc
  intro x hx
  have hh := hts hx
  change f x ≠ 0
  intro hz
  simp only [Set.mem_ofPred_eq, hz, mul_zero] at hh
  exact (not_le_of_gt zero_lt_one) hh

/-- At every point where the defining function is positive the cutoff is eventually exact. -/
theorem cutoffTest_eventually_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : 𝓓((⊤ : Opens E), ℝ)) (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {x : E}
    (hx : 0 < f x) : ∀ᶠ n : ℕ in atTop, cutoffTest φ f hf n x = φ x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / f x)
  filter_upwards [eventually_ge_atTop N] with n hn
  have ha : 2 ≤ ((n : ℝ) + 1) * f x := by
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hh : 2 < (N : ℝ) * f x := (div_lt_iff₀ hx).mp hN
    nlinarith only [hcast, hh, hx]
  change φ x * Real.smoothTransition _ = φ x
  rw [Real.smoothTransition.one_of_one_le (by linarith only [ha]), mul_one]

/-- Every open region admits interior-supported test cutoffs eventually equal at each point. -/
theorem exists_open_cutoffs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {O : Set E} (hO : IsOpen O) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    ∃ ψ : ℕ → 𝓓((⊤ : Opens E), ℝ),
      (∀ n, tsupport ⇑(ψ n) ⊆ O) ∧ (∀ n x, |ψ n x| ≤ |φ x|) ∧
      (∀ x ∈ O, ∀ᶠ n in atTop, ψ n x = φ x) := by
  obtain ⟨f, hfs, hf, hfb⟩ := hO.exists_contDiff_support_eq (n := ⊤)
  refine ⟨cutoffTest φ f hf, ?_, abs_cutoffTest_le φ f hf, ?_⟩
  · intro n
    rw [← hfs]
    exact tsupport_cutoffTest_subset φ f hf n
  · intro x hx
    have hn : f x ≠ 0 := by
      change x ∈ Function.support f
      rwa [hfs]
    have hp : 0 < f x := lt_of_le_of_ne (hfb ⟨x, rfl⟩).1 hn.symm
    exact cutoffTest_eventually_eq φ f hf hp

end IsotropicVariance.Infra.WhiteNoiseProps
