/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Concentration.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Bounded refresh differences

The pointwise unit-difference condition in BLM Theorem 7 bounds the oscillation
on the whole finite product. Thus every exponential moment exists. Convexity
of the exponential gives the scalar estimate on `[0,1]` used for `K = 1`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set Filter
namespace IsotropicVariance.Infra.Concentration

/-- Unit coordinate refresh differences bound the total oscillation by the
number of coordinates. -/
theorem abs_sub_le_of_update_le {n : ℕ} {A : Type*} (f : (Fin n → A) → ℝ)
    (h : ∀ x i y, |f x - f (Function.update x i y)| ≤ 1) (x y : Fin n → A) :
    |f x - f y| ≤ n := by
  let R := fun k : ℕ => fun i : Fin n => if (i : ℕ) < k then x i else y i
  have hR0 : R 0 = y := by funext i; simp only [R, Nat.not_lt_zero, ite_false]
  have hRn : R n = x := by funext i; exact ite_eq_left i.isLt
  have hStep (i : Fin n) : |f (R (i + 1)) - f (R i)| ≤ 1 := by
    have hUpd : Function.update (R (i + 1)) i (y i) = R i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, R, lt_self_iff_false, ite_false]
      · have hv : (j : ℕ) ≠ i := fun hh => hji (Fin.ext hh)
        have hh : (j : ℕ) < (i : ℕ) + 1 ↔ (j : ℕ) < i := by omega
        simp only [Function.update_of_ne hji, R, hh]
    simpa only [hUpd] using h (R (i + 1)) i (y i)
  have he : f x - f y = ∑ i : Fin n, (f (R (i + 1)) - f (R i)) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => f (R (k + 1)) - f (R k)) n,
      Finset.sum_range_sub (fun k => f (R k)) n, hRn, hR0]
  rw [he]
  calc
    _ ≤ ∑ i : Fin n, |f (R (i + 1)) - f (R i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hStep i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- On a product probability space the unit-difference condition implies a
global absolute bound. -/
theorem exists_abs_le_of_update_le {n : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (h : ∀ x i y, |f x - f (Function.update x i y)| ≤ 1) :
    ∃ B : ℝ, ∀ x, |f x| ≤ B := by
  obtain ⟨y, _⟩ := (Eventually.of_forall (fun _ : Fin n → A => True.intro) :
    ∀ᵐ _x ∂Measure.pi μ, True).exists
  refine ⟨(n : ℝ) + |f y|, fun x => ?_⟩
  calc
    |f x| = |(f x - f y) + f y| := by rw [sub_add_cancel]
    _ ≤ |f x - f y| + |f y| := abs_add_le _ _
    _ ≤ _ := add_le_add_left (abs_sub_le_of_update_le f h x y) _

/-- An absolutely bounded measurable function has every exponential moment. -/
theorem integrable_exp_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (θ : ℝ) : Integrable (fun x => exp (θ * f x)) P := by
  apply Integrable.mono' (integrable_const (exp (|θ| * B))) (hf.const_mul θ).exp.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  apply exp_le_exp.mpr
  calc
    θ * f x ≤ |θ * f x| := le_abs_self _
    _ = |θ| * |f x| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB x) (abs_nonneg θ)

/-- The scalar bound for the `K = 1` case of BLM Proposition 10. -/
theorem mul_exp_sub_one_le_sq_mul_exp_one {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    u * (exp u - 1) ≤ (exp 1 - 1) * u ^ 2 := by
  have hc := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (sub_nonneg.mpr hu1) hu (sub_add_cancel 1 u)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, exp_zero] at hc
  have he : exp u - 1 ≤ (exp 1 - 1) * u := by
    calc
      _ ≤ ((1 - u) + u * exp 1) - 1 := sub_le_sub_right hc 1
      _ = _ := by ring
  calc
    _ ≤ u * ((exp 1 - 1) * u) := mul_le_mul_of_nonneg_left he hu
    _ = _ := by ring

end IsotropicVariance.Infra.Concentration
