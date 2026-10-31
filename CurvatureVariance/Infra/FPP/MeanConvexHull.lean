/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanSkeletonTail
public import CurvatureVariance.Infra.FPP.MeanSkeletonGood
public import CurvatureVariance.Infra.FPP.MeanAlexander
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Linarith

/-!
# Alexander's convex-hull approximation property for the mean passage time

This is the skeleton step of Alexander's method ([ADH, Prop. 3.32], for [ADH, Thm 3.33]).
Kesten's (4.13) is replaced by the Gaussian lower tail
of least costs over bounded edge sets (`MinCostLowerTail`), so no BK inequality is needed.

Fix `x = z/k` with `r = |x|` large, put `X = N z` and `n = N k`, and let `K` be the cheap-path
length at cost `n(μ(x) + 1) + 1`. Three bad events have probability at most `1/4` each:
- `T(0, X) > n(μ(x) + 1)`, small for large `N` since `T(0, N z)/N → μ(z)` (`hμ`);
- a cheap path of `K` edges from the origin (`CheapPaths`, with `e^{-cK} ≤ 1/4` once `K ≥ 3/c`);
- the deficit `q C₂ φ(r)` of some skeleton (`measure_skeletonBadUnion_le_quarter`).

So some configuration avoids all three. Then:
1. a near-optimal path from `0` to `X` has fewer than `K` edges;
2. its skeleton at scale `K₀ r` dominates, giving `∑ h(y_i) ≤ n(μ(x)+1) + 1 + q C₂ φ(r)` with
   `q ≤ n`;
3. so `(x, ∑ h(y_i)/n)` lies in the convex hull of the lifted lattice points of the ball of radius
   `M r` (`convexHullApprox_meanTime`).

The cheap-path bound is `e^{-cK}` (`CheapPaths P a c`), and the scale `N` is taken large enough
that `K ≥ 3/c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Infra.FPP


variable {m : ℕ} {P : Measure (Config m)}

/-- The numerics of one layer of the skeleton union bound: with the deficit constant
`C₂ = ((m + 2) M (μhi + 5)/(c a))^{1/2}` the `q`-th term is at most `C ρ^q`,
`ρ = (3M)^{m+1}/(2 + r)`. -/
theorem skeleton_term_le {C c a μhi M r n Kr : ℝ} (q : ℕ) (hC : 0 ≤ C) (hc : 0 < c)
    (ha : 0 < a) (hμhi : 0 < μhi) (hM : 1 ≤ M) (hr : 1 ≤ r) (hn : 0 < n) (hK0 : 0 ≤ Kr)
    (hK : a * (Kr + 1) ≤ (μhi + 5) * n * r) :
    (2 * (M * r) + 1) ^ ((m + 1) * q) *
        (C * Real.exp (-(c * (q * (n * r / (M * r)) *
          (Real.sqrt (((m : ℝ) + 2) * M * (μhi + 5) / (c * a)) * meanRate r) ^ 2 /
            (Kr + 1))))) ≤
      C * ((3 * M) ^ (m + 1) / (2 + r)) ^ q := by
  set L := Real.log (2 + r) with hL
  have hr0 : 0 < r := by linarith only [hr]
  have hM0 : 0 < M := by linarith only [hM]
  have h2r : 0 < 2 + r := by linarith only [hr]
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith only [hr])
  have hφ : meanRate r ^ 2 = r * L := Real.sq_sqrt (mul_nonneg hr0.le hL0)
  have hB : 0 ≤ ((m : ℝ) + 2) * M * (μhi + 5) / (c * a) := by positivity
  have hs : Real.sqrt (((m : ℝ) + 2) * M * (μhi + 5) / (c * a)) ^ 2 =
      ((m : ℝ) + 2) * M * (μhi + 5) / (c * a) := Real.sq_sqrt hB
  have hK1 : 0 < Kr + 1 := by linarith only [hK0]
  -- the exponent is at least `q (m + 2) log(2 + r)`
  have hexp : (q : ℝ) * (((m + 2 : ℕ) : ℝ) * L) ≤
      c * (q * (n * r / (M * r)) *
        (Real.sqrt (((m : ℝ) + 2) * M * (μhi + 5) / (c * a)) * meanRate r) ^ 2 / (Kr + 1)) := by
    rw [mul_pow, hs, hφ]
    have key : c * (q * (n * r / (M * r)) *
        (((m : ℝ) + 2) * M * (μhi + 5) / (c * a) * (r * L)) / (Kr + 1)) =
        ((q : ℝ) * (((m + 2 : ℕ) : ℝ) * L)) * ((μhi + 5) * n * r / (a * (Kr + 1))) := by
      push_cast
      field_simp
    rw [key]
    have h1 : 1 ≤ (μhi + 5) * n * r / (a * (Kr + 1)) := by
      rw [one_le_div (by positivity)]; exact hK
    have h0 : 0 ≤ (q : ℝ) * (((m + 2 : ℕ) : ℝ) * L) := by positivity
    calc (q : ℝ) * (((m + 2 : ℕ) : ℝ) * L) = ((q : ℝ) * (((m + 2 : ℕ) : ℝ) * L)) * 1 :=
          (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h0
  have hexp' : Real.exp (-(c * (q * (n * r / (M * r)) *
        (Real.sqrt (((m : ℝ) + 2) * M * (μhi + 5) / (c * a)) * meanRate r) ^ 2 / (Kr + 1)))) ≤
      (((2 + r) ^ (m + 2))⁻¹) ^ q := by
    refine (Real.exp_le_exp.2 (neg_le_neg hexp)).trans_eq ?_
    rw [← mul_neg, Real.exp_nat_mul, Real.exp_neg, Real.exp_nat_mul, hL, Real.exp_log h2r]
  have h2Mr : 0 < 2 * (M * r) + 1 := by linarith only [mul_pos hM0 hr0]
  have hbase : (2 * (M * r) + 1) ^ (m + 1) / (2 + r) ^ (m + 2) ≤ (3 * M) ^ (m + 1) / (2 + r) := by
    rw [pow_succ (2 + r) (m + 1), ← div_div, ← div_pow]
    refine div_le_div_of_nonneg_right (pow_le_pow_left₀ (div_nonneg h2Mr.le h2r.le) ?_ _) h2r.le
    rw [div_le_iff₀ h2r]
    linarith only [mul_pos hM0 hr0, hM]
  calc (2 * (M * r) + 1) ^ ((m + 1) * q) *
        (C * Real.exp (-(c * (q * (n * r / (M * r)) *
          (Real.sqrt (((m : ℝ) + 2) * M * (μhi + 5) / (c * a)) * meanRate r) ^ 2 /
            (Kr + 1)))))
      ≤ (2 * (M * r) + 1) ^ ((m + 1) * q) * (C * (((2 + r) ^ (m + 2))⁻¹) ^ q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp' hC) (pow_nonneg h2Mr.le _)
    _ = C * ((2 * (M * r) + 1) ^ (m + 1) / (2 + r) ^ (m + 2)) ^ q := by
        rw [pow_mul, div_eq_mul_inv, mul_pow]; ring
    _ ≤ C * ((3 * M) ^ (m + 1) / (2 + r)) ^ q :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg (pow_nonneg h2Mr.le _) (pow_nonneg h2r.le _)) hbase q) hC

/-- **The skeleton union bound**: with `‖X‖ = n r`, `a (K + 1) ≤ (μhi + 5) n r` and
`ρ = (3M)^{m+1}/(2 + r) ≤ 1/(8(C + 1))`, the deficit events at `C₂ φ(r)` per step have
probability at most `1/4`. -/
theorem measure_skeletonBadUnion_le_quarter [IsProbabilityMeasure P]
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    (hE : ∀ e : Edge m, Integrable (fun ω : Config m => (ω e : ℝ)) P)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hlow : MinCostLowerTail P C c)
    {a μhi M r : ℝ} (ha : 0 < a) (hμhi : 0 < μhi) (hM : 1 ≤ M) (hr : 1 ≤ r)
    {X : Vertex m} (hX : X ≠ 0) {n : ℝ} (hn : 0 < n) (hXn : ‖point X‖ = n * r) {K : ℕ}
    (hK : a * ((K : ℝ) + 1) ≤ (μhi + 5) * n * r)
    (hρ : (3 * M) ^ (m + 1) / (2 + r) ≤ 1 / (8 * (C + 1))) :
    P (skeletonBadUnion P X (M * r) K
      (Real.sqrt (((m : ℝ) + 2) * M * (μhi + 5) / (c * a)) * meanRate r)) ≤
      ENNReal.ofReal (1 / 4) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hM0 : 0 < M := by linarith only [hM]
  set ρ : ℝ := (3 * M) ^ (m + 1) / (2 + r) with hρdef
  have hρ0 : 0 ≤ ρ :=
    div_nonneg (pow_nonneg (mul_nonneg (by norm_num) hM0.le) _) (by linarith only [hr])
  have hC1 : 0 < C + 1 := by linarith only [hC]
  have hρ8 : ρ ≤ 1 / 8 := hρ.trans (by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hC1) (by norm_num)]; linarith only [hC])
  refine (measure_skeletonBadUnion_le hT hI hE hC hc.le hlow hX (mul_pos hM0 hr0)
    (mul_nonneg (Real.sqrt_nonneg _) (meanRate_nonneg r)) K).trans ?_
  calc ∑ q ∈ Finset.Icc 1 K, ENNReal.ofReal ((2 * (M * r) + 1) ^ ((m + 1) * q) *
        (C * Real.exp (-(c * (q * (‖point X‖ / (M * r)) *
          (Real.sqrt (((m : ℝ) + 2) * M * (μhi + 5) / (c * a)) * meanRate r) ^ 2 /
            ((K : ℝ) + 1))))))
      ≤ ∑ q ∈ Finset.Icc 1 K, ENNReal.ofReal (C * ρ ^ q) := by
        refine Finset.sum_le_sum fun q _ => ENNReal.ofReal_le_ofReal ?_
        rw [hXn]
        exact skeleton_term_le q hC hc ha hμhi hM hr hn (Nat.cast_nonneg K) hK
    _ = ENNReal.ofReal (∑ q ∈ Finset.Icc 1 K, C * ρ ^ q) :=
        (ENNReal.ofReal_sum_of_nonneg fun q _ => mul_nonneg hC (pow_nonneg hρ0 q)).symm
    _ ≤ ENNReal.ofReal (1 / 4) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        have hsub : ∑ q ∈ Finset.Icc 1 K, ρ ^ q ≤ ∑ q ∈ Finset.Ico 1 (K + 1), ρ ^ q :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun q hq => by
              rw [Finset.mem_Icc] at hq; rw [Finset.mem_Ico]; omega)
            (fun q _ _ => pow_nonneg hρ0 q)
        have hgeom := geom_sum_Ico_le_of_lt_one (m := 1) (n := K + 1) hρ0
          (by linarith only [hρ8] : ρ < 1)
        have h2 : ρ ^ 1 / (1 - ρ) ≤ 2 * ρ := by
          rw [pow_one, div_le_iff₀ (by linarith only [hρ8])]
          linarith only [mul_nonneg hρ0 (by linarith only [hρ8] : 0 ≤ 1 - 2 * ρ)]
        have h3 : C * (2 * ρ) ≤ 1 / 4 := by
          have : C * ρ ≤ C * (1 / (8 * (C + 1))) := mul_le_mul_of_nonneg_left hρ hC
          have h4 : C * (1 / (8 * (C + 1))) ≤ 1 / 8 := by
            rw [mul_one_div, div_le_div_iff₀ (mul_pos (by norm_num) hC1) (by norm_num)]
            linarith only [hC]
          linarith only [this, h4]
        calc C * ∑ q ∈ Finset.Icc 1 K, ρ ^ q ≤ C * (2 * ρ) :=
              mul_le_mul_of_nonneg_left (hsub.trans (hgeom.trans h2)) hC
          _ ≤ 1 / 4 := h3

/-- Three events of probability at most `1/4` each leave a configuration outside all three. -/
theorem exists_not_mem_of_measure_le [IsProbabilityMeasure P] {B₁ B₂ B₃ : Set (Config m)}
    (h₁ : P B₁ ≤ ENNReal.ofReal (1 / 4)) (h₂ : P B₂ ≤ ENNReal.ofReal (1 / 4))
    (h₃ : P B₃ ≤ ENNReal.ofReal (1 / 4)) : ∃ ω, ω ∉ B₁ ∧ ω ∉ B₂ ∧ ω ∉ B₃ := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set (Config m)) ⊆ B₁ ∪ B₂ ∪ B₃ := fun ω _ => by
    by_cases g₁ : ω ∈ B₁
    · exact Or.inl (Or.inl g₁)
    by_cases g₂ : ω ∈ B₂
    · exact Or.inl (Or.inr g₂)
    exact Or.inr (hcon ω g₁ g₂)
  have h : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) +
      ENNReal.ofReal (1 / 4) := by
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ ≤ P (B₁ ∪ B₂ ∪ B₃) := measure_mono hsub
      _ ≤ P (B₁ ∪ B₂) + P B₃ := measure_union_le _ _
      _ ≤ P B₁ + P B₂ + P B₃ := add_le_add_left (measure_union_le _ _) _
      _ ≤ _ := add_le_add (add_le_add h₁ h₂) h₃
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at h
  have h' : ENNReal.ofReal (1 / 4 + 1 / 4 + 1 / 4) < 1 := by
    rw [ENNReal.ofReal_lt_one]; norm_num
  exact absurd h (not_le.2 h')

/-- Outside the cheap-path event at length `K`, a path of cost below `W ≤ a K` is shorter than `K`;
so a near-optimal path from the origin to `X` with `T(0, X) + 1 ≤ W` exists with at most `K`
edges. -/
theorem exists_short_path {ω : Config m} {X : Vertex m} {K : ℕ} {a W : ℝ}
    (hTW : (passageTime ω 0 X : ℝ) + 1 ≤ W) (hWK : W ≤ a * K)
    (hcheap : ω ∉ {ω : Config m | ∃ (v : Vertex m) (p : (latticeGraph m).Walk 0 v), p.IsPath ∧
      p.length = K ∧ (walkCost ω p : ℝ) ≤ a * K}) :
    ∃ π : (latticeGraph m).Walk 0 X, π.IsPath ∧ π.length ≤ K ∧ (walkCost ω π : ℝ) < W := by
  obtain ⟨p, hp⟩ := exists_walkCost_lt (ω := ω) (0 : Vertex m) X (ε := 1) one_pos
  have hπ : (p.toPath : (latticeGraph m).Walk 0 X).IsPath := p.toPath.2
  have hcost : (walkCost ω (p.toPath : (latticeGraph m).Walk 0 X) : ℝ) < W := by
    have h1 : (walkCost ω (p.toPath : (latticeGraph m).Walk 0 X) : ℝ) ≤ walkCost ω p := by
      exact_mod_cast walkCost_toPath_le ω p
    have h2 : (walkCost ω p : ℝ) < passageTime ω 0 X + 1 := by exact_mod_cast hp
    linarith only [h1, h2, hTW]
  refine ⟨_, hπ, ?_, hcost⟩
  by_contra hlt
  push Not at hlt
  apply hcheap
  set π : (latticeGraph m).Walk 0 X := (p.toPath : (latticeGraph m).Walk 0 X)
  refine ⟨π.getVert K, π.take K, hπ.take K, ?_, ?_⟩
  · rw [SimpleGraph.Walk.take_length]; omega
  · have h1 := walkCost_take_add_drop ω π K
    have h2 : walkCost ω (π.take K) ≤ walkCost ω π := by
      rw [← h1]; exact le_add_of_nonneg_right bot_le
    have h3 : (walkCost ω (π.take K) : ℝ) ≤ walkCost ω π := by exact_mod_cast h2
    linarith only [h3, hcost, hWK]

/-- A sum over the steps of a skeleton, all but the last at least `B`, is at least `(q - 1) B`. -/
theorem sub_one_mul_le_sum {q : ℕ} (hq : 1 ≤ q) (f : Fin q → ℝ) (hf : ∀ j, 0 ≤ f j) {B : ℝ}
    (hB : ∀ j : Fin q, (j : ℕ) + 1 < q → B ≤ f j) : ((q : ℝ) - 1) * B ≤ ∑ j, f j := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  have hsum : ∑ _j : Fin q', B ≤ ∑ j : Fin q', f j.castSucc :=
    Finset.sum_le_sum fun j _ => hB j.castSucc (by simp)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  push_cast
  linarith only [hsum, hf (Fin.last q')]

/-- The arithmetic bounding the number of skeleton steps: `q ≤ n`. -/
theorem steps_le {q n : ℕ} {S W D μlo K₀ r μhi μx : ℝ} (hn4 : (4 : ℝ) ≤ n) (hr1 : 1 ≤ r)
    (hμhi : 0 < μhi) (hμx : μx ≤ μhi * r) (hloK₀ : μlo * K₀ = 4 * (μhi + 2))
    (hDr : D ≤ μlo * K₀ * r / 2) (hlow : ((q : ℝ) - 1) * (μlo * K₀ * r) ≤ S)
    (hS : S ≤ W + q * D) (hW : W < n * (μx + 1) + 1) : q ≤ n := by
  set A : ℝ := (μhi + 2) * r with hA
  have hA0 : 0 < A := by positivity
  have hDA : D ≤ 2 * A := by
    have e : 4 * (μhi + 2) * r / 2 = 2 * ((μhi + 2) * r) := by ring
    rw [hloK₀, e] at hDr; rw [hA]; exact hDr
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqD : (q : ℝ) * D ≤ q * (2 * A) := mul_le_mul_of_nonneg_left hDA hq0
  have hlo4 : ((q : ℝ) - 1) * (μlo * K₀ * r) = ((q : ℝ) - 1) * (4 * A) := by
    rw [hA, hloK₀]; ring
  have hn0 : (0 : ℝ) ≤ n := by linarith only [hn4]
  have hnA : (n : ℝ) * (μx + 1) + 1 ≤ n * A := by
    have h3 : (n : ℝ) * μx ≤ n * (μhi * r) := mul_le_mul_of_nonneg_left hμx hn0
    have h4 : (n : ℝ) ≤ n * r := le_mul_of_one_le_right hn0 hr1
    have h6 : (n : ℝ) * A = n * (μhi * r) + 2 * (n * r) := by rw [hA]; ring
    have h7 : (n : ℝ) * (μx + 1) + 1 = n * μx + n + 1 := by ring
    linarith only [h3, h4, h6, h7, hn4]
  have key : (2 * (q : ℝ)) * A ≤ ((n : ℝ) + 4) * A := by
    have e1 : ((q : ℝ) - 1) * (4 * A) = 4 * ((q : ℝ) * A) - 4 * A := by ring
    have e2 : (q : ℝ) * (2 * A) = 2 * ((q : ℝ) * A) := by ring
    have e3 : (2 * (q : ℝ)) * A = 2 * ((q : ℝ) * A) := by ring
    have e4 : ((n : ℝ) + 4) * A = n * A + 4 * A := by ring
    linarith only [hlow, hlo4, hS, hW, hqD, hnA, e1, e2, e3, e4]
  have h2q : 2 * (q : ℝ) ≤ n + 4 := le_of_mul_le_mul_right key hA0
  have : (q : ℝ) ≤ n := by linarith only [h2q, hn4]
  exact_mod_cast this

/-- The final height bound: `S/n ≤ μ(x) + (C₂ + 2) φ(r)`. -/
theorem inv_mul_le_height {q n : ℕ} {S W D C₂ φ μx : ℝ} (hn : (1 : ℝ) ≤ n) (hqn : q ≤ n)
    (hD : D = C₂ * φ) (hD0 : 0 ≤ D) (hφ : 1 ≤ φ) (hS : S ≤ W + q * D)
    (hW : W < n * (μx + 1) + 1) : (n : ℝ)⁻¹ * S ≤ μx + (C₂ + 2) * φ := by
  have hn0 : (0 : ℝ) < n := by linarith only [hn]
  rw [inv_mul_le_iff₀ hn0]
  have hqD : (q : ℝ) * D ≤ n * D := mul_le_mul_of_nonneg_right (by exact_mod_cast hqn) hD0
  have hnφ : (n : ℝ) ≤ n * φ := le_mul_of_one_le_right hn0.le hφ
  have hexpand : (n : ℝ) * (μx + (C₂ + 2) * φ) = n * μx + n * D + 2 * (n * φ) := by
    rw [hD]; ring
  have h7 : (n : ℝ) * (μx + 1) + 1 = n * μx + n + 1 := by ring
  rw [hexpand]
  linarith only [hS, hW, hqD, hnφ, h7, hn]

/-- **The deterministic part of the skeleton argument**: in a configuration with
`T(0, X) ≤ n(μ(x) + 1)`, no cheap path of length `K` from the origin and no skeleton deficit,
`(x, v)` lies in the convex hull of the lifted lattice points of the ball of radius `(K₀ + 1) r`
for some `v ≤ μ(x) + (C₂ + 2) φ(r)`. -/
theorem exists_mem_convexHull_of_good [IsProbabilityMeasure P]
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    {μ : PtNorm m}
    (hμ : IsTimeConstant P μ)
    {μlo μhi a K₀ C₂ : ℝ} (hlo0 : 0 < μlo) (hμhi : 0 < μhi) (hlo : ∀ x, μlo * ‖x‖ ≤ μ.1 x)
    (hhi : ∀ x, μ.1 x ≤ μhi * ‖x‖) (hloK₀ : μlo * K₀ = 4 * (μhi + 2)) (hK₀0 : 0 < K₀)
    (hC₂0 : 0 ≤ C₂) {x : Pt m} (hr1 : 1 ≤ ‖x‖)
    (hDr : C₂ * meanRate ‖x‖ ≤ μlo * K₀ * ‖x‖ / 2)
    {n K : ℕ} (hn4 : (4 : ℝ) ≤ n) {X : Vertex m} (hpX : point X = (n : ℝ) • x) (hK1 : 1 ≤ K)
    (hKa : (n : ℝ) * (μ.1 x + 1) + 1 ≤ a * K) {ω : Config m}
    (hT1 : (passageTime ω 0 X : ℝ) ≤ n * (μ.1 x + 1))
    (h₂ : ω ∉ {ω : Config m | ∃ (v : Vertex m) (p : (latticeGraph m).Walk 0 v), p.IsPath ∧
      p.length = K ∧ (walkCost ω p : ℝ) ≤ a * K})
    (h₃ : ω ∉ skeletonBadUnion P X ((K₀ + 1) * ‖x‖) K (C₂ * meanRate ‖x‖)) :
    ∃ v : ℝ, v ≤ μ.1 x + (C₂ + 2) * meanRate ‖x‖ ∧
      (x, v) ∈ convexHull ℝ (liftedPoints (meanTime P) ((K₀ + 1) * ‖x‖)) := by
  set r : ℝ := ‖x‖ with hr
  set W : ℝ := (n : ℝ) * (μ.1 x + 1) + 1 with hWdef
  set D : ℝ := C₂ * meanRate r with hD
  have hD0 : 0 ≤ D := mul_nonneg hC₂0 (meanRate_nonneg r)
  have hn0 : (0 : ℝ) < n := by linarith only [hn4]
  obtain ⟨π, hπ, hlen, hcost⟩ := exists_short_path (X := X) (W := W) (by linarith only [hT1])
    hKa h₂
  obtain ⟨q, d, hq, hd, hsum, hlong, hfam⟩ :=
    exists_good_skeleton π hπ hlen hK1 (R := K₀ * r) (mul_nonneg hK₀0.le (norm_nonneg x))
  have hdM : ∀ j, ‖point (d j)‖ ≤ (K₀ + 1) * r := fun j => by
    have h1 := hd j
    have h2 : K₀ * r + 1 ≤ (K₀ + 1) * r := by
      have : (K₀ + 1) * r = K₀ * r + r := by ring
      linarith only [this, hr1]
    linarith only [h1, h2]
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hq).1
  have hqK : q ≤ K := (Finset.mem_Icc.1 hq).2
  have hnot : ω ∉ skeletonBad P (skelVert d) q K (q * D) := fun hb => h₃ (by
    simp only [skeletonBadUnion, Set.mem_iUnion]
    exact ⟨q, Finset.mem_range.2 (by omega), d, Finset.mem_filter.2
      ⟨Fintype.mem_piFinset.2 fun j => mem_latticeBall.2 (hdM j), hsum⟩, hb⟩)
  have hS : ∑ j, meanTime P (d j) ≤ walkCost ω π + q * D := by
    simp only [skeletonBad, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hnot
    generalize skeletonFamily (skelVert d) q K = S at hfam hnot
    have h := hnot (walkEdges π) hfam
    rw [sum_walkEdges hπ.isTrail.edges_nodup ω, sum_range_skelVert_sub d (meanTime P)] at h
    linarith only [h]
  have hlow : ((q : ℝ) - 1) * (μlo * K₀ * r) ≤ ∑ j, meanTime P (d j) := by
    refine sub_one_mul_le_sum hq1 _ (fun j => meanTime_nonneg _) fun j hj => ?_
    have hj' := hlong j hj
    calc μlo * K₀ * r = μlo * (K₀ * r) := by ring
      _ ≤ μlo * ‖point (d j)‖ := mul_le_mul_of_nonneg_left hj' hlo0.le
      _ ≤ μ.1 (point (d j)) := hlo _
      _ ≤ meanTime P (d j) := le_meanTime hT hI hμ _
  have hqn : q ≤ n := steps_le hn4 hr1 hμhi (hhi x) hloK₀ hDr hlow hS hcost
  have hmem := mem_convexHull_of_sum (h := meanTime P) meanTime_zero hqn (by exact_mod_cast hn0)
    d (R := (K₀ + 1) * r) (mul_nonneg (by linarith only [hK₀0]) (norm_nonneg x)) hdM
  rw [hsum, hpX, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul] at hmem
  exact ⟨_, inv_mul_le_height (by linarith only [hn4]) hqn hD hD0 (one_le_meanRate hr1) hS hcost,
    hmem⟩

/-- **Alexander's convex-hull approximation property** for the mean passage time `h = E T(0, ·)`
under a translation-invariant law with integrable passage times and weights, the time-constant
property for a norm `μ` with equivalence constants `μlo, μhi`, the cheap-path estimate and the
Gaussian lower tail of least costs over bounded edge sets. -/
theorem convexHullApprox_meanTime [IsProbabilityMeasure P]
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    (hE : ∀ e : Edge m, Integrable (fun ω : Config m => (ω e : ℝ)) P)
    {μ : PtNorm m}
    (hμ : IsTimeConstant P μ)
    {μlo μhi : ℝ} (hlo0 : 0 < μlo) (hhi0 : 0 < μhi) (hlo : ∀ x, μlo * ‖x‖ ≤ μ.1 x)
    (hhi : ∀ x, μ.1 x ≤ μhi * ‖x‖)
    {a c₀ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hc₀ : 0 < c₀) (hcheap : CheapPaths P a c₀)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hlow : MinCostLowerTail P C c) :
    ∃ M C₁ r₀ : ℝ, 0 < M ∧ 0 ≤ C₁ ∧ 0 < r₀ ∧ ConvexHullApprox (meanTime P) μ.1 M C₁ r₀ := by
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 4 * (μhi + 2) / μlo := ⟨_, rfl⟩
  have hK₀0 : 0 < K₀ := by rw [hK₀]; positivity
  have hloK₀ : μlo * K₀ = 4 * (μhi + 2) := by rw [hK₀]; field_simp
  have hM1 : 1 ≤ K₀ + 1 := by linarith only [hK₀0]
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = Real.sqrt (((m : ℝ) + 2) * (K₀ + 1) * (μhi + 5) / (c * a)) :=
    ⟨_, rfl⟩
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; exact Real.sqrt_nonneg _
  obtain ⟨r₂, hr₂⟩ := eventually_atTop.1
    (eventually_meanRate_le (ε := μlo * K₀ / (2 * (C₂ + 1))) (by positivity))
  refine ⟨K₀ + 1, C₂ + 2, max (max 1 r₂) (8 * (C + 1) * (3 * (K₀ + 1)) ^ (m + 1)),
    by linarith only [hK₀0], by linarith only [hC₂0],
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro z k hk hr
  obtain ⟨x, hx⟩ : ∃ x : Pt m, x = (k : ℝ)⁻¹ • point z := ⟨_, rfl⟩
  rw [← hx] at hr ⊢
  have hr1 : 1 ≤ ‖x‖ := ((le_max_left _ _).trans (le_max_left _ _)).trans hr
  have hr2 : r₂ ≤ ‖x‖ := ((le_max_right _ _).trans (le_max_left _ _)).trans hr
  have hr3 : 8 * (C + 1) * (3 * (K₀ + 1)) ^ (m + 1) ≤ ‖x‖ := (le_max_right _ _).trans hr
  have hr0 : 0 < ‖x‖ := by linarith only [hr1]
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hpz : point z = (k : ℝ) • x := by
    rw [hx, smul_smul, mul_inv_cancel₀ hk0.ne', one_smul]
  have hμz : μ.1 (point z) = k * μ.1 x := by
    rw [hpz, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hk0]
  have hμx0 : 0 ≤ μ.1 x := apply_nonneg _ _
  have hDr : C₂ * meanRate ‖x‖ ≤ μlo * K₀ * ‖x‖ / 2 := by
    have h := hr₂ ‖x‖ hr2
    calc C₂ * meanRate ‖x‖ ≤ (C₂ + 1) * meanRate ‖x‖ :=
          mul_le_mul_of_nonneg_right (by linarith only) (meanRate_nonneg _)
      _ ≤ (C₂ + 1) * (μlo * K₀ / (2 * (C₂ + 1)) * ‖x‖) :=
          mul_le_mul_of_nonneg_left h (by linarith only [hC₂0])
      _ = μlo * K₀ * ‖x‖ / 2 := by field_simp
  have hρ : (3 * (K₀ + 1)) ^ (m + 1) / (2 + ‖x‖) ≤ 1 / (8 * (C + 1)) := by
    rw [div_le_div_iff₀ (by linarith only [hr0]) (by linarith only [hC])]
    calc (3 * (K₀ + 1)) ^ (m + 1) * (8 * (C + 1)) =
          8 * (C + 1) * (3 * (K₀ + 1)) ^ (m + 1) := by ring
      _ ≤ ‖x‖ := hr3
      _ ≤ 1 * (2 + ‖x‖) := by linarith only
  -- the first bad event, for large `N`
  have hE1 := tendsto_measure_lt_passageTime (hμ z) (δ := (k : ℝ)) hk0
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    ((tendsto_order.1 hE1).2 (ENNReal.ofReal (1 / 4)) (by norm_num))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max (max N₁ 4) ⌈3 / c₀⌉₊ := ⟨_, rfl⟩
  have hN4 : 4 ≤ N := hN ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hN3 : 3 / c₀ ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (hN ▸ le_max_right _ _ : ⌈3 / c₀⌉₊ ≤ N))
  have hB1 : P {ω | (N : ℝ) * (μ.1 (point z) + k) < passageTime ω 0 (N • z)} ≤
      ENNReal.ofReal (1 / 4) := (hN₁ N (hN ▸ (le_max_left _ _).trans (le_max_left _ _))).le
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = N * k := ⟨_, rfl⟩
  have hn : (n : ℝ) = N * k := by rw [hndef]; push_cast; ring
  have hn4 : (4 : ℝ) ≤ n := by
    have h4 : (4 : ℝ) ≤ N := by exact_mod_cast hN4
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [hn]
    calc (4 : ℝ) = 4 * 1 := by ring
      _ ≤ N * k := mul_le_mul h4 h1 zero_le_one (by linarith only [h4])
  have hn0 : (0 : ℝ) < n := by linarith only [hn4]
  have hn3 : 3 / c₀ ≤ (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : (N : ℝ) ≤ n := by
      rw [hn]; exact le_mul_of_one_le_right (Nat.cast_nonneg N) h1
    exact hN3.trans h2
  have hpX : point (N • z) = (n : ℝ) • x := by
    rw [point_nsmul, hpz, smul_smul, hn]
  have hXn : ‖point (N • z)‖ = n * ‖x‖ := by
    rw [hpX, norm_smul, Real.norm_of_nonneg hn0.le]
  have hX0 : N • z ≠ 0 := by
    intro h0
    have h : ‖point (N • z)‖ = 0 := by rw [h0, point_zero, norm_zero]
    rw [hXn] at h
    exact (mul_pos hn0 hr0).ne' h
  -- the cheap-path length
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ((n : ℝ) * (μ.1 x + 1) + 1) / a := ⟨_, rfl⟩
  have hY0 : 0 < Y := by
    rw [hY]
    exact div_pos (add_pos_of_nonneg_of_pos
      (mul_nonneg hn0.le (by linarith only [hμx0])) one_pos) ha
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈Y⌉₊ + 1 := ⟨_, rfl⟩
  have hKY : Y + 1 ≤ (K : ℝ) := by
    rw [hK]; push_cast; linarith only [Nat.le_ceil Y]
  have hKY' : (K : ℝ) < Y + 2 := by
    rw [hK]; push_cast; linarith only [Nat.ceil_lt_add_one hY0.le]
  have hK1 : 1 ≤ K := by rw [hK]; omega
  have hKa : (n : ℝ) * (μ.1 x + 1) + 1 ≤ a * K := by
    have e : (n : ℝ) * (μ.1 x + 1) + 1 = a * Y := by rw [hY]; field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left (by linarith only [hKY]) ha.le
  have hKbound : a * ((K : ℝ) + 1) ≤ (μhi + 5) * n * ‖x‖ := by
    have h1 : a * ((K : ℝ) + 1) ≤ a * (Y + 3) :=
      mul_le_mul_of_nonneg_left (by linarith only [hKY']) ha.le
    have h2 : a * (Y + 3) = (n : ℝ) * (μ.1 x + 1) + 1 + 3 * a := by rw [hY]; field_simp
    have h3 : (n : ℝ) * μ.1 x ≤ n * (μhi * ‖x‖) := mul_le_mul_of_nonneg_left (hhi x) hn0.le
    have h4 : (n : ℝ) ≤ n * ‖x‖ := le_mul_of_one_le_right hn0.le hr1
    have h5 : (1 : ℝ) ≤ n * ‖x‖ := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ n * ‖x‖ := mul_le_mul (by linarith only [hn4]) hr1 zero_le_one hn0.le
    have e1 : (n : ℝ) * (μhi * ‖x‖) = μhi * n * ‖x‖ := by ring
    have e2 : (μhi + 5) * n * ‖x‖ = μhi * n * ‖x‖ + 5 * (n * ‖x‖) := by ring
    have e3 : (n : ℝ) * (μ.1 x + 1) = n * μ.1 x + n := by ring
    linarith only [h1, h2, h3, h4, h5, e1, e2, e3, ha1]
  have hB2 : P {ω | ∃ (v : Vertex m) (p : (latticeGraph m).Walk 0 v), p.IsPath ∧ p.length = K ∧
      (walkCost ω p : ℝ) ≤ a * K} ≤ ENNReal.ofReal (1 / 4) := by
    refine (hcheap 0 K).trans (ENNReal.ofReal_le_ofReal ?_)
    have hYn : (n : ℝ) ≤ Y := by
      rw [hY, le_div_iff₀ ha]
      have h1 : (n : ℝ) * a ≤ n := mul_le_of_le_one_right hn0.le ha1
      have h2 : (n : ℝ) ≤ n * (μ.1 x + 1) :=
        le_mul_of_one_le_right hn0.le (by linarith only [hμx0])
      linarith only [h1, h2]
    have hcK : 3 ≤ c₀ * K := by
      have h1 : 3 / c₀ ≤ (K : ℝ) := hn3.trans (hYn.trans (by linarith only [hKY]))
      rwa [div_le_iff₀ hc₀, mul_comm] at h1
    have he := Real.add_one_le_exp (c₀ * K)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 4)]
    norm_num
    linarith only [he, hcK]
  have hB3 := measure_skeletonBadUnion_le_quarter hT hI hE hC hc hlow ha hhi0 hM1 hr1 hX0 hn0
    hXn hKbound hρ
  rw [← hC₂] at hB3
  obtain ⟨ω, hω₁, hω₂, hω₃⟩ := exists_not_mem_of_measure_le hB1 hB2 hB3
  have hT1 : (passageTime ω 0 (N • z) : ℝ) ≤ n * (μ.1 x + 1) := by
    have h : ¬ ((N : ℝ) * (μ.1 (point z) + k) < passageTime ω 0 (N • z)) := hω₁
    rw [not_lt, hμz] at h
    calc (passageTime ω 0 (N • z) : ℝ) ≤ (N : ℝ) * (k * μ.1 x + k) := h
      _ = n * (μ.1 x + 1) := by rw [hn]; ring
  exact exists_mem_convexHull_of_good hT hI hμ hlo0 hhi0 hlo hhi hloK₀ hK₀0 hC₂0 hr1 hDr hn4 hpX
    hK1 hKa hT1 hω₂ hω₃

end CurvatureVariance.Infra.FPP
