/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SlabsEvents
public import CurvatureVariance.Paper.Proofs.Geometry.ClassicalTails

/-!
# The events `𝒢_N(S)`: one pair of vertices at a time

The failure probabilities of (H1) and (H2) for one pair of vertices, Gaussian in `S`:

* `measure_concentration_fail_le`: if the mean gap `E T(x,y) − μ(y − x)` lies in
  `[0, C_g S |y − x|^{1/2}]` and `A ≥ 2C_g`, then
  `P(|T(x,y) − μ(y − x)| > A(S|y − x|^{1/2} + S²)) ≤ 2 e^{-ρ' S²}`, by the two tails of
  `exists_tails_of_law` at `z = (A/2)(S|y − x|^{1/2} + S²)` (the proof of Lemma `lem:good`);
* `IsIIDWeights.measure_lt_walkCost_le`: a path with at most `L + 2` edges costs more than
  `A(L + S²)` with probability at most `M² e^{-αAS²}` when `αA ≥ log M` (Chernoff).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

variable {m : ℕ}

theorem point_sub (x y : Vertex m) : point (y - x) = point y - point x := by
  apply WithLp.ofLp_injective
  simp only [point, transversePoint, WithLp.ofLp_sub, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub,
    Int.cast_sub]
  congr 1
  apply WithLp.ofLp_injective
  ext j
  simp

theorem l1Dist_eq_l1Dist_zero_sub (x y : Vertex m) : l1Dist x y = l1Dist 0 (y - x) := by
  simp only [l1Dist, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, zero_sub, Prod.fst_sub,
    Prod.snd_sub, Pi.sub_apply, Int.natAbs_neg]
  congr 1
  · rw [← Int.natAbs_neg]; congr 1; ring
  · exact Finset.sum_congr rfl fun j _ => by rw [← Int.natAbs_neg]; congr 1; ring

theorem l1Dist_le_mul_norm (x y : Vertex m) :
    (l1Dist x y : ℝ) ≤ ((m : ℝ) + 1) * ‖point y - point x‖ := by
  rw [l1Dist_eq_l1Dist_zero_sub, ← point_sub]
  exact l1Dist_zero_le_norm_point _

theorem oneNorm_sub_eq_l1Dist (x y : Vertex m) : oneNorm (y - x) = (l1Dist x y : ℝ) := by
  rw [l1Dist_eq_l1Dist_zero_sub, oneNorm, l1Dist_zero_eq]

/-- The rate of the failures of (H1), for tails at the rate `ρ`. -/
noncomputable def concRate (ρ A : ℝ) (m : ℕ) : ℝ :=
  ρ * min (A ^ 2 / (4 * ((m : ℝ) + 1))) (A / 2)

theorem concRate_pos {ρ A : ℝ} (hρ : 0 < ρ) (hA : 0 < A) : 0 < concRate ρ A m :=
  mul_pos hρ (lt_min (by positivity) (by positivity))

/-- **(H1) for one pair**, Gaussian in `S`: the tails of `T(x, y) − E T(x, y)` and the mean bound
(the proof of Lemma `lem:good`). -/
theorem measure_concentration_fail_le {P : Measure (Config m)} (μ : Seminorm ℝ (Pt m))
    {x y : Vertex m} (hn1 : 1 ≤ l1Dist x y) {ρ A S Cg : ℝ} (hρ : 0 < ρ) (hA : 0 < A) (hS : 0 ≤ S)
    (hCg : 2 * Cg ≤ A)
    (hgap0 : μ (point y - point x) ≤ ∫ ω, passageTimeReal ω x y ∂P)
    (hgap : (∫ ω, passageTimeReal ω x y ∂P) - μ (point y - point x) ≤
      Cg * S * Real.sqrt ‖point y - point x‖)
    (htail : ∀ z : ℝ, 0 ≤ z →
      P {ω | passageTimeReal ω x y - ∫ ω', passageTimeReal ω' x y ∂P ≤ -z} ≤
          ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / oneNorm (y - x)) z))) ∧
      P {ω | z ≤ passageTimeReal ω x y - ∫ ω', passageTimeReal ω' x y ∂P} ≤
          ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / oneNorm (y - x)) z)))) :
    P {ω | A * (S * Real.sqrt ‖point y - point x‖ + S ^ 2) <
        |passageTimeReal ω x y - μ (point y - point x)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(concRate ρ A m * S ^ 2))) := by
  have hn1' : (1 : ℝ) ≤ (l1Dist x y : ℝ) := by exact_mod_cast hn1
  set r := ‖point y - point x‖ with hr
  set n : ℝ := (l1Dist x y : ℝ) with hn
  have hnr : n ≤ ((m : ℝ) + 1) * r := l1Dist_le_mul_norm x y
  have hr0 : 0 < r := by
    by_contra hcon
    push Not at hcon
    have : ((m : ℝ) + 1) * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
    linarith only [this, hnr, hn1']
  set ET := ∫ ω, passageTimeReal ω x y ∂P with hET
  set z := A / 2 * (S * Real.sqrt r + S ^ 2) with hz
  have hsq : 0 ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hSr : 0 ≤ S * Real.sqrt r := mul_nonneg hS hsq
  have hz0 : 0 ≤ z := by positivity
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  -- the failure event lies in the union of the two tails at level `z`
  have hsub : {ω | A * (S * Real.sqrt r + S ^ 2) < |passageTimeReal ω x y - μ (point y - point x)|}
      ⊆ {ω | passageTimeReal ω x y - ET ≤ -z} ∪ {ω | z ≤ passageTimeReal ω x y - ET} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    have hgap' : ET - μ (point y - point x) ≤ A / 2 * (S * Real.sqrt r) := by
      have : Cg * S * Real.sqrt r ≤ A / 2 * (S * Real.sqrt r) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith only [hCg]) hSr
      linarith only [this, hgap]
    have hA2 : A * (S * Real.sqrt r + S ^ 2) = 2 * z := by rw [hz]; ring
    have hhalf : 0 ≤ A / 2 * S ^ 2 := by positivity
    have hz' : z = A / 2 * (S * Real.sqrt r) + A / 2 * S ^ 2 := by rw [hz]; ring
    rw [hA2] at hω
    rcases lt_abs.1 hω with h1 | h1
    · right
      linarith only [h1, hgap', hz', hhalf]
    · left
      linarith only [h1, hgap0, hz0]
  -- the exponents
  have hκ1 : A ^ 2 / (4 * ((m : ℝ) + 1)) * S ^ 2 ≤ z ^ 2 / n := by
    have hz2 : A ^ 2 / 4 * S ^ 2 * r ≤ z ^ 2 := by
      have h1 : (S * Real.sqrt r) ^ 2 = S ^ 2 * r := by
        rw [mul_pow, Real.sq_sqrt hr0.le]
      have h2 : S * Real.sqrt r ≤ S * Real.sqrt r + S ^ 2 := by linarith only [hS2]
      have h3 := pow_le_pow_left₀ hSr h2 2
      rw [hz, mul_pow, div_pow]
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ A ^ 2 / 2 ^ 2)
      rw [h1] at h4
      linarith only [h4]
    rw [le_div_iff₀ (by linarith only [hn1'])]
    calc A ^ 2 / (4 * ((m : ℝ) + 1)) * S ^ 2 * n
        ≤ A ^ 2 / (4 * ((m : ℝ) + 1)) * S ^ 2 * (((m : ℝ) + 1) * r) :=
          mul_le_mul_of_nonneg_left hnr (by positivity)
      _ = A ^ 2 / 4 * S ^ 2 * r := by field_simp
      _ ≤ z ^ 2 := hz2
  have hκ2 : A / 2 * S ^ 2 ≤ z := by
    rw [hz]
    have h1 := mul_nonneg (by positivity : 0 ≤ A / 2) hSr
    linarith only [h1, mul_add (A / 2) (S * Real.sqrt r) (S ^ 2)]
  have hexp : concRate ρ A m * S ^ 2 ≤ ρ * min (z ^ 2 / oneNorm (y - x)) z := by
    rw [concRate, mul_assoc]
    refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) hρ.le
    · rw [oneNorm_sub_eq_l1Dist]
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hS2).trans hκ1
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hS2).trans hκ2
  obtain ⟨hlow, hup⟩ := htail z hz0
  have hmono : ENNReal.ofReal (Real.exp (-(ρ * min (z ^ 2 / oneNorm (y - x)) z))) ≤
      ENNReal.ofReal (Real.exp (-(concRate ρ A m * S ^ 2))) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg hexp))
  calc P {ω | A * (S * Real.sqrt r + S ^ 2) < |passageTimeReal ω x y - μ (point y - point x)|}
      ≤ P {ω | passageTimeReal ω x y - ET ≤ -z} + P {ω | z ≤ passageTimeReal ω x y - ET} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-(concRate ρ A m * S ^ 2))) +
          ENNReal.ofReal (Real.exp (-(concRate ρ A m * S ^ 2))) :=
        add_le_add (hlow.trans hmono) (hup.trans hmono)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **(H2) for one path** (Chernoff): a path with at most `L + 2` edges costs more than
`A(L + S²)` with probability at most `M² e^{-αAS²}` when `αA ≥ log M`, `M = E e^{ατ}`. -/
theorem IsIIDWeights.measure_lt_walkCost_le {P : Measure (Config m)} {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] (hP : IsIIDWeights P F) {α : ℝ} (hα : 0 < α)
    (hexp : Integrable (fun x : ℝ≥0 => Real.exp (α * x)) F) {u v : Vertex m}
    (p : (latticeGraph m).Walk u v) (hp : p.IsPath) {A L S : ℝ} (hL : 0 ≤ L)
    (hlen : (p.length : ℝ) ≤ L + 2) (hA : Real.log (expMom F α) ≤ α * A) :
    P {ω | A * (L + S ^ 2) < (walkCost ω p : ℝ)} ≤
      ENNReal.ofReal (expMom F α ^ 2 * Real.exp (-(α * A * S ^ 2))) := by
  have hM1 : 1 ≤ expMom F α := one_le_expMom hα.le hexp
  have hM0 : 0 < expMom F α := by linarith
  have hch := IsIIDWeights.measure_le_walkCost_le hP p hp.isTrail.edges_nodup hα.le hexp
    (A * (L + S ^ 2))
  have hsub : {ω | A * (L + S ^ 2) < (walkCost ω p : ℝ)} ⊆
      {ω | A * (L + S ^ 2) ≤ (walkCost ω p : ℝ)} := fun ω hω => by
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact hω.le
  refine (measure_mono hsub).trans (hch.trans (ENNReal.ofReal_le_ofReal ?_))
  have hlog : 0 ≤ Real.log (expMom F α) := Real.log_nonneg hM1
  rw [show (∫ x : ℝ≥0, Real.exp (α * x) ∂F) = expMom F α from rfl,
    ← Real.exp_log hM0, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul,
    ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : (p.length : ℝ) * Real.log (expMom F α) ≤ (L + 2) * Real.log (expMom F α) :=
    mul_le_mul_of_nonneg_right hlen hlog
  have h2 : L * Real.log (expMom F α) ≤ L * (α * A) := mul_le_mul_of_nonneg_left hA hL
  push_cast
  nlinarith

end CurvatureVariance.Paper.Proofs.Geometry
