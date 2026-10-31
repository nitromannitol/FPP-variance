/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanBasic
public import CurvatureVariance.Infra.FPP.MeanSkeleton
import Mathlib.Tactic.Linarith

/-!
# Probability bounds for the skeleton deficit events

* `le_integral_inf'_skeletonFamily`: the mean of the least weight over a skeleton family
  dominates the mean skeleton sum;
* `measure_skeletonBad_le`: Gaussian bound for one skeleton's deficit event;
* `measure_skeletonBadUnion_le`: union bound over skeletons from the origin to `X ≠ 0`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP


variable {m : ℕ} {P : Measure (Config m)}

theorem measurable_inf'_edgeSum (𝓕 : Finset (Finset (Edge m))) (h𝓕 : 𝓕.Nonempty) :
    Measurable fun ω : Config m => 𝓕.inf' h𝓕 (fun F => ∑ e ∈ F, (ω e : ℝ)) := by
  have hF : ∀ F : Finset (Edge m), Measurable fun ω : Config m => ∑ e ∈ F, (ω e : ℝ) := fun F =>
    Finset.measurable_sum _ (fun e _ => measurable_coe_nnreal_real.comp (measurable_pi_apply e))
  induction h𝓕 using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hF a
  | cons a s ha hs ih =>
    simp only [Finset.inf'_cons hs]
    exact (hF a).inf ih

/-- The expected least weight over the family of a skeleton dominates the mean skeleton sum. -/
theorem le_integral_inf'_skeletonFamily [IsProbabilityMeasure P]
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    (hE : ∀ e : Edge m, Integrable (fun ω : Config m => (ω e : ℝ)) P)
    (v : ℕ → Vertex m) (q K : ℕ) (h𝓕 : (skeletonFamily v q K).Nonempty) :
    ∑ i ∈ Finset.range q, meanTime P (v (i + 1) - v i) ≤
      ∫ ω, (skeletonFamily v q K).inf' h𝓕 (fun F => ∑ e ∈ F, (ω e : ℝ)) ∂P := by
  have hpt : ∀ ω : Config m, ∑ i ∈ Finset.range q, (passageTime ω (v i) (v (i + 1)) : ℝ) ≤
      (skeletonFamily v q K).inf' h𝓕 (fun F => ∑ e ∈ F, (ω e : ℝ)) := by
    intro ω
    refine Finset.le_inf' _ _ (fun F hF => ?_)
    unfold skeletonFamily at hF
    classical
    exact (Finset.mem_filter.1 hF).2.2 ω
  obtain ⟨F₀, hF₀⟩ := h𝓕
  have hint : Integrable
      (fun ω : Config m => (skeletonFamily v q K).inf' ⟨F₀, hF₀⟩ (fun F => ∑ e ∈ F, (ω e : ℝ)))
      P := by
    refine Integrable.mono' (g := fun ω : Config m => ∑ e ∈ F₀, (ω e : ℝ))
      (integrable_finsetSum _ (fun e _ => hE e))
      (measurable_inf'_edgeSum _ _).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have h0 : 0 ≤ (skeletonFamily v q K).inf' ⟨F₀, hF₀⟩ (fun F => ∑ e ∈ F, (ω e : ℝ)) :=
      Finset.le_inf' _ _ (fun F _ => Finset.sum_nonneg (fun e _ => (ω e).2))
    rw [Real.norm_of_nonneg h0]
    exact Finset.inf'_le (fun F => ∑ e ∈ F, (ω e : ℝ)) hF₀
  calc ∑ i ∈ Finset.range q, meanTime P (v (i + 1) - v i)
      = ∫ ω, ∑ i ∈ Finset.range q, (passageTime ω (v i) (v (i + 1)) : ℝ) ∂P := by
        rw [integral_finsetSum _ (fun i _ => hI _ _)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_passageTime_eq_meanTime hT]
    _ ≤ _ := integral_mono (integrable_finsetSum _ (fun i _ => hI _ _)) hint hpt

/-- The deficit event of one skeleton has a Gaussian bound. -/
theorem measure_skeletonBad_le [IsProbabilityMeasure P]
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    (hE : ∀ e : Edge m, Integrable (fun ω : Config m => (ω e : ℝ)) P)
    {C c : ℝ} (hlow : MinCostLowerTail P C c) (v : ℕ → Vertex m) (q K : ℕ) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) :
    P (skeletonBad P v q K Δ) ≤ ENNReal.ofReal (C * Real.exp (-(c * (Δ ^ 2 / ((K : ℝ) + 1))))) := by
  by_cases h𝓕 : (skeletonFamily v q K).Nonempty
  · refine le_trans (measure_mono ?_) (hlow _ h𝓕 K (fun F hF => ?_) Δ hΔ)
    · rintro ω ⟨F, hF, hlt⟩
      have h1 := le_integral_inf'_skeletonFamily hT hI hE v q K h𝓕
      have h2 : (skeletonFamily v q K).inf' h𝓕 (fun F => ∑ e ∈ F, (ω e : ℝ)) ≤
          ∑ e ∈ F, (ω e : ℝ) := Finset.inf'_le (fun F => ∑ e ∈ F, (ω e : ℝ)) hF
      show _ ≤ _
      linarith only [h1, h2, hlt]
    · unfold skeletonFamily at hF
      classical
      exact (Finset.mem_filter.1 hF).2.1
  · rw [Finset.not_nonempty_iff_eq_empty] at h𝓕
    have : skeletonBad P v q K Δ = ∅ := by
      ext ω
      simp [skeletonBad, h𝓕]
    rw [this]
    simp

lemma norm_point_le_of_sum {q : ℕ} {R : ℝ} (d : Fin q → Vertex m)
    (hd : d ∈ Fintype.piFinset fun _ : Fin q => latticeBall m R) :
    ‖point (∑ j, d j)‖ ≤ q * R := by
  rw [point_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖point (d j)‖ ≤ ∑ _j : Fin q, R :=
        Finset.sum_le_sum (fun j _ =>
          mem_latticeBall.1 (Fintype.mem_piFinset.1 hd j))
    _ = q * R := by simp

/-- One `q ≥ 1` layer of the union bound. -/
lemma measure_skeletonBadUnion_layer [IsProbabilityMeasure P]
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    (hE : ∀ e : Edge m, Integrable (fun ω : Config m => (ω e : ℝ)) P)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hlow : MinCostLowerTail P C c)
    {X : Vertex m} {R D : ℝ} (hR : 0 < R) (hD : 0 ≤ D) (K q : ℕ) :
    (∑ d ∈ (Fintype.piFinset fun _ : Fin q => latticeBall m R).filter (fun d => ∑ j, d j = X),
        P (skeletonBad P (skelVert d) q K (q * D))) ≤
      ENNReal.ofReal ((2 * R + 1) ^ ((m + 1) * q) *
        (C * Real.exp (-(c * (q * (‖point X‖ / R) * D ^ 2 / ((K : ℝ) + 1)))))) := by
  set S := (Fintype.piFinset fun _ : Fin q => latticeBall m R).filter (fun d => ∑ j, d j = X)
  set b : ℝ := C * Real.exp (-(c * (q * (‖point X‖ / R) * D ^ 2 / ((K : ℝ) + 1)))) with hb
  have hb0 : 0 ≤ b := mul_nonneg hC (Real.exp_nonneg _)
  have hterm : ∀ d ∈ S, P (skeletonBad P (skelVert d) q K (q * D)) ≤ ENNReal.ofReal b := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    refine (measure_skeletonBad_le hT hI hE hlow _ q K (mul_nonneg hq0 hD)).trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
    have hn := norm_point_le_of_sum d hd.1
    rw [hd.2] at hn
    have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have h1 : (q : ℝ) * (‖point X‖ / R) ≤ q * q := by
      refine mul_le_mul_of_nonneg_left ?_ hq0
      rw [div_le_iff₀ hR]; linarith only [hn]
    have h2 : (q : ℝ) * (‖point X‖ / R) * D ^ 2 ≤ (q * D) ^ 2 := by
      calc _ ≤ (q : ℝ) * q * D ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg D)
        _ = _ := by ring
    have h3 := div_le_div_of_nonneg_right h2 hK.le
    have h4 := mul_le_mul_of_nonneg_left h3 hc
    linarith only [h4]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≤ (2 * R + 1) ^ ((m + 1) * q) := by
    have h1 : S.card ≤ ((latticeBall m R).card) ^ q :=
      (Finset.card_filter_le _ _).trans (by simp [Fintype.card_piFinset])
    have h2 := card_latticeBall_le (m := m) hR.le
    calc (S.card : ℝ) ≤ (((latticeBall m R).card : ℕ) : ℝ) ^ q := by exact_mod_cast h1
      _ ≤ ((2 * R + 1) ^ (m + 1)) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 q
      _ = _ := by rw [← pow_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hb0)

/-- The union bound over skeletons from the origin to `X ≠ 0`. -/
theorem measure_skeletonBadUnion_le [IsProbabilityMeasure P]
    (hT : ∀ a : Vertex m, MeasurePreserving (translate a) P P)
    (hI : ∀ u v : Vertex m, Integrable (fun ω => (passageTime ω u v : ℝ)) P)
    (hE : ∀ e : Edge m, Integrable (fun ω : Config m => (ω e : ℝ)) P)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hlow : MinCostLowerTail P C c)
    {X : Vertex m} (hX : X ≠ 0) {R D : ℝ} (hR : 0 < R) (hD : 0 ≤ D) (K : ℕ) :
    P (skeletonBadUnion P X R K D) ≤
      ∑ q ∈ Finset.Icc 1 K, ENNReal.ofReal ((2 * R + 1) ^ ((m + 1) * q) *
        (C * Real.exp (-(c * (q * (‖point X‖ / R) * D ^ 2 / ((K : ℝ) + 1)))))) := by
  classical
  have hr : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
    ext q; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  unfold skeletonBadUnion
  refine (measure_biUnion_finset_le _ _).trans ?_
  rw [hr, Finset.sum_insert (by simp)]
  have h0 : P (⋃ d ∈ (Fintype.piFinset fun _ : Fin 0 => latticeBall m R).filter
      (fun d => ∑ j, d j = X), skeletonBad P (skelVert d) 0 K (((0 : ℕ) : ℝ) * D)) = 0 := by
    have : (Fintype.piFinset fun _ : Fin 0 => latticeBall m R).filter
        (fun d => ∑ j, d j = X) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun d hd => hX ?_)
      simpa using (Finset.mem_filter.1 hd).2.symm
    rw [this]; simp
  rw [h0, zero_add]
  refine Finset.sum_le_sum (fun q hq => ?_)
  exact (measure_biUnion_finset_le _ _).trans
    (measure_skeletonBadUnion_layer hT hI hE hC hc hlow hR hD K q)

end CurvatureVariance.Infra.FPP
