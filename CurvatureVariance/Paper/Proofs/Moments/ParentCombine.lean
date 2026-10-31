/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ParentBounds
public import CurvatureVariance.Paper.Proofs.Moments.ParentGeometry
public import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Statements.Inputs.IsOsMul
import CurvatureVariance.Paper.Proofs.Responses.Basic
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:parent`: the combination and the scales

The proof of Lemma `lem:parent`:

* `parent_combine`: from equation `eq:rowenergy` at `(Ms, Mst)` (`|F − μ| ≤ C M Q_s + O₁(Q_ℓ/200)`),
  concatenation `T(0,(Ms,Mst)) ≤ F`, Lemma `lem:slabs` (2) on `𝒢` (`F ≤ T + C M S²`),
  `μ ≤ E T` off `𝒢`, the product `1_{𝒢ᶜ} (E T − T)₊ ≤ O₁(Q_ℓ/400)` ([AKM, Lemma A.3(ii)]) and the
  coordinate path
  `T((Ms,Mst),(ℓ,y)) ≤ O₁(Q_ℓ/400)`, [AKM, Lemma A.4] gives `|T − μ| ≤ C Q_ℓ + O₁(Q_ℓ/100)`.
* `scale_E`, `Q_ge_of_E5`, `prod_scale_le`: the comparisons of the scales.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments.Parent

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

/-! ## The combination -/

/-- **The combination** (the proof of Lemma `lem:parent`). -/
theorem parent_combine {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {ℓ Ms s : ℕ}
    {y z : Fin m → ℤ} (hs2 : 2 ≤ s)
    {Qℓ BE cE : ℝ} (hQ : 0 < Qℓ) (hcE : 0 ≤ cE) (hQs : 0 ≤ Q M K A s)
    {X : Config m → ℝ} (hX : IsOs M.P 1 (Qℓ / 200) X)
    (hXae : ∀ᵐ ω ∂M.P, ∀ Y : Fin (Ms + 1) → Fin m → ℤ,
      IsMinTuple M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) Y →
      |(slabMin M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)).toReal -
          M.μ.1 (point (((Ms * s : ℕ) : ℤ), z))| +
        cE * Q M K A s * ∑ i : Fin Ms,
          indexJumpSq s (wInt M K A s) (targetSlope (Ms * s) z) Y i ≤ BE + X ω)
    {Y₀ : Fin (Ms + 1) → Fin m → ℤ}
    (hY₀ : IsAdmissibleTuple M s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) Y₀)
    {G : Set (Config m)} {BS : ℝ} (hBS : 0 ≤ BS)
    (hGF : ∀ ω ∈ G, slabMin M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) ≤
      (passageTime ω 0 (((Ms * s : ℕ) : ℤ), z) : ℝ≥0∞) + ENNReal.ofReal BS)
    {θi θd : ℝ} (hθi : 0 < θi) (hθd : 0 < θd)
    (hind : IsOs M.P 2 θi (Gᶜ.indicator fun _ => (1 : ℝ)))
    (hdev : IsOs M.P 2 θd (fun ω => max ((∫ ω', passageTimeReal ω' 0 (((Ms * s : ℕ) : ℤ), z) ∂M.P) -
      passageTimeReal ω 0 (((Ms * s : ℕ) : ℤ), z)) 0))
    (hθ : θi * θd ≤ Qℓ / 400)
    (hEμ : M.μ.1 (point (((Ms * s : ℕ) : ℤ), z)) ≤
      ∫ ω', passageTimeReal ω' 0 (((Ms * s : ℕ) : ℤ), z) ∂M.P)
    (hTc : IsOs M.P 1 (Qℓ / 400)
      (fun ω => passageTimeReal ω (((Ms * s : ℕ) : ℤ), z) ((ℓ : ℤ), y)))
    {d : ℝ} (hd : |M.μ.1 (point ((ℓ : ℤ), y)) - M.μ.1 (point (((Ms * s : ℕ) : ℤ), z))| ≤ d)
    {C : ℝ} (hC : BE + d + BS ≤ C * Qℓ) :
    IsOs M.P 1 (Qℓ / 100) (fun ω =>
      |passageTimeReal ω 0 ((ℓ : ℤ), y) - M.μ.1 (point ((ℓ : ℤ), y))| - C * Qℓ) := by
  have := hM.probP
  set x₀ : Vertex m := (((Ms * s : ℕ) : ℤ), z) with hx₀
  set x₁ : Vertex m := ((ℓ : ℤ), y) with hx₁
  set t := targetSlope (Ms * s) z with ht
  set E₀ := ∫ ω', passageTimeReal ω' 0 x₀ ∂M.P with hE₀
  -- the product rule `IsOs.mul` of [AKM, Lemma A.3(ii)], which the paper takes from [AB26]
  have hprod : IsOs M.P 1 (θi * θd) (fun ω => (Gᶜ.indicator (fun _ => (1 : ℝ))) ω *
      max ((∫ ω', passageTimeReal ω' 0 (((Ms * s : ℕ) : ℤ), z) ∂M.P) -
        passageTimeReal ω 0 (((Ms * s : ℕ) : ℤ), z)) 0) := by
    simpa only [show (2 : ℝ) * 2 / (2 + 2) = 1 by norm_num] using
      IsOs.mul hind hdev two_pos two_pos hθi hθd
        (fun ω => by by_cases h : ω ∈ Gᶜ <;> simp [Set.indicator, h])
        (fun ω => le_max_right _ _)
  have hsum := isOs_add (isOs_add hX hTc (by positivity) (by positivity))
    (hprod.mono_scale zero_le_one (by positivity) hθ) (by positivity) (by positivity)
  have hscale : Qℓ / 200 + Qℓ / 400 + Qℓ / 400 = Qℓ / 100 := by ring
  rw [hscale] at hsum
  refine hsum.mono zero_le_one (by positivity)
    ((continuous_abs.measurable.comp
      ((measurable_passageTimeReal 0 x₁).sub_const _)).sub_const _).aemeasurable ?_
  filter_upwards [hXae] with ω hω
  -- the minimizing tuple
  obtain ⟨Y, hY⟩ := exists_isMinTuple M ω hY₀
  have hsumJ : 0 ≤ cE * Q M K A s * ∑ i : Fin Ms, indexJumpSq s (wInt M K A s) t Y i :=
    mul_nonneg (mul_nonneg hcE hQs) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hB := hω Y hY
  set F := (slabMin M ω s Ms t 0 x₀).toReal with hF
  have hFB : |F - M.μ.1 (point x₀)| ≤ BE + X ω := by linarith
  -- concatenation
  have hfin : slabMin M ω s Ms t 0 x₀ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ =>
      Responses.tuple_slabTime_ne_top ω 0 hs2 Y₀ i) (Responses.slabMin_le_tupleCost hY₀ ω)
  have hT₀F : passageTimeReal ω 0 x₀ ≤ F := by
    have h := passageTime_le_slabMin ω M t (u := 0) (v := x₀) (n := s) (K := Ms)
      (by simp [hx₀])
    have h' := ENNReal.toReal_mono hfin h
    simpa [passageTimeReal] using h'
  -- the triangle inequalities
  have hT1 := passageTimeReal_triangle ω 0 x₀ x₁
  have hT2 := passageTimeReal_triangle ω 0 x₁ x₀
  rw [passageTimeReal_symm ω x₁ x₀] at hT2
  have hTc0 := passageTimeReal_nonneg ω x₀ x₁
  -- the event
  have hι : (Gᶜ.indicator (fun _ => (1 : ℝ)) ω = 0 ∧ F ≤ passageTimeReal ω 0 x₀ + BS) ∨
      Gᶜ.indicator (fun _ => (1 : ℝ)) ω = 1 := by
    by_cases hG : ω ∈ G
    · left
      refine ⟨by simp [Set.indicator, hG], ?_⟩
      have h := hGF ω hG
      have h' := ENNReal.toReal_mono (by finiteness) h
      rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hBS] at h'
      simpa [passageTimeReal] using h'
    · right; simp [Set.indicator, hG]
  have hmain := abs_le_of_parts hT1 hT2 hd hT₀F hFB hEμ hBS hι
  linarith

/-! ## The scales -/

section Scales

variable {M : Model m} {K : ℕ} {A : ℝ}

/-- `C Q_s ≤ Q_ℓ/200` once `C M^{−1/3} ≤ 1/200`. -/
theorem scale_E (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 1 ≤ A) {CE : ℝ} (hCE : 0 ≤ CE)
    {s ℓ Ms : ℝ} (hs1 : 1 ≤ s) (hMs : 1 ≤ Ms) (hℓ : Ms * s ≤ ℓ)
    (hMsCE : CE * (1 / Ms) ^ ((1 : ℝ) / 3) ≤ 1 / 200) :
    CE * Q M K A s ≤ Q M K A ℓ / 200 := by
  have hs : 0 < s := by linarith
  have h1 := Q_le_of_mul_le (A := A) hM hK (by linarith) hs hMs hℓ
  have hℓ1 : 1 ≤ ℓ := by nlinarith
  have hQ : 0 ≤ Q M K A ℓ := by
    have := rpow_third_le_Q hM hK hA hℓ1; have : 0 ≤ ℓ ^ ((1 : ℝ) / 3) := by positivity
    linarith
  calc CE * Q M K A s ≤ CE * ((1 / Ms) ^ ((1 : ℝ) / 3) * Q M K A ℓ) :=
        mul_le_mul_of_nonneg_left h1 hCE
    _ = (CE * (1 / Ms) ^ ((1 : ℝ) / 3)) * Q M K A ℓ := by ring
    _ ≤ 1 / 200 * Q M K A ℓ := mul_le_mul_of_nonneg_right hMsCE hQ
    _ = Q M K A ℓ / 200 := by ring

/-- `Q_ℓ ≥ B N^{δ/500}` for `ℓ ≥ κN` once `B ≤ κ^{1/3} N^{1/3 − δ/500}`. -/
theorem Q_ge_of_E5 (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 1 ≤ A) {κ B : ℝ} (hκ : 0 < κ)
    {N ℓ : ℝ} (hN : 1 ≤ N) (hℓ : κ * N ≤ ℓ) (hℓ1 : 1 ≤ ℓ)
    (hB : B ≤ κ ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3 - M.δ / 500)) :
    B * N ^ (M.δ / 500) ≤ Q M K A ℓ := by
  have hN0 : 0 < N := by linarith
  have h1 := rpow_third_le_Q hM hK hA hℓ1
  have h2 : (κ * N) ^ ((1 : ℝ) / 3) ≤ ℓ ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) hℓ (by norm_num)
  have h3 : (κ * N) ^ ((1 : ℝ) / 3) =
      κ ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3 - M.δ / 500) * N ^ (M.δ / 500) := by
    rw [Real.mul_rpow hκ.le hN0.le, mul_assoc, ← Real.rpow_add hN0]
    congr 2; ring
  have h4 : 0 ≤ N ^ (M.δ / 500) := by positivity
  have h5 : B * N ^ (M.δ / 500) ≤
      κ ^ ((1 : ℝ) / 3) * N ^ ((1 : ℝ) / 3 - M.δ / 500) * N ^ (M.δ / 500) :=
    mul_le_mul_of_nonneg_right hB h4
  linarith

/-- **The product scale**: `(C/S) · 2√(L/C₁) ≤ Q_ℓ/400` for `S = N^{δ/1000}`, `L ≤ B ℓ`,
`ℓ ≤ 3N` once `2400 C √(B/C₁) ≤ N^{9δ/10⁴}`. -/
theorem prod_scale_le (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 1 ≤ A) {Csl C₁ L B : ℝ}
    (hCsl : 0 < Csl) (hC₁ : 0 < C₁) (hB : 0 < B) {N ℓ : ℝ} (hN : 1 ≤ N) (hℓ1 : 1 ≤ ℓ)
    (hℓN : ℓ ≤ 3 * N) (hL : L ≤ B * ℓ)
    (hE6 : 2400 * Csl * Real.sqrt (B / C₁) ≤ N ^ (9 * M.δ / 10000)) :
    Csl / N ^ (M.δ / 1000) * (2 * Real.sqrt (L / C₁)) ≤ Q M K A ℓ / 400 := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  obtain ⟨-, hδK⟩ := Q_exponent_bounds hM hK
  have hN0 : 0 < N := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set α := 2400 * Csl * Real.sqrt (B / C₁) with hα
  have hα0 : 0 < α := by
    have : 0 < Real.sqrt (B / C₁) := Real.sqrt_pos.mpr (by positivity)
    positivity
  -- the lower bound on `Q_ℓ`
  have hQ1 := sqrt_mul_rpow_le_Q (M := M) (K := K) hA hℓ0
  have hq1 : (3 * N) ^ (-(M.δ / K)) ≤ ℓ ^ (-(M.δ / K)) :=
    Real.rpow_le_rpow_of_nonpos hℓ0 hℓN (by
      have : 0 ≤ M.δ / K := by positivity
      linarith)
  have hq2 : (3 * N) ^ (-(M.δ / 10000)) ≤ (3 * N) ^ (-(M.δ / K)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hq3 : (3 * N) ^ (-(M.δ / 10000)) = (3 : ℝ) ^ (-(M.δ / 10000)) * N ^ (-(M.δ / 10000)) :=
    Real.mul_rpow (by norm_num) hN0.le
  have hq4 : (1 : ℝ) / 3 ≤ (3 : ℝ) ^ (-(M.δ / 10000)) := by
    calc (1 : ℝ) / 3 = (3 : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]; norm_num
      _ ≤ (3 : ℝ) ^ (-(M.δ / 10000)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hsq0 : 0 ≤ Real.sqrt ℓ := Real.sqrt_nonneg _
  have hNe0 : 0 < N ^ (-(M.δ / 10000)) := by positivity
  have hQ2 : Real.sqrt ℓ * N ^ (-(M.δ / 10000)) / 3 ≤ Q M K A ℓ := by
    have h1 : N ^ (-(M.δ / 10000)) / 3 ≤ ℓ ^ (-(M.δ / K)) := by
      have : N ^ (-(M.δ / 10000)) / 3 ≤ (3 : ℝ) ^ (-(M.δ / 10000)) * N ^ (-(M.δ / 10000)) := by
        nlinarith
      linarith
    calc Real.sqrt ℓ * N ^ (-(M.δ / 10000)) / 3 = Real.sqrt ℓ * (N ^ (-(M.δ / 10000)) / 3) := by
          ring
      _ ≤ Real.sqrt ℓ * ℓ ^ (-(M.δ / K)) := mul_le_mul_of_nonneg_left h1 hsq0
      _ ≤ Q M K A ℓ := hQ1
  -- the upper bound on the product scale
  have hS : N ^ (M.δ / 1000) = N ^ (9 * M.δ / 10000) * N ^ (M.δ / 10000) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hNinv : N ^ (-(M.δ / 10000)) * N ^ (M.δ / 10000) = 1 := by
    rw [← Real.rpow_add hN0]; simp
  have hS0 : 0 < N ^ (M.δ / 1000) := by positivity
  have hsqL : Real.sqrt (L / C₁) ≤ Real.sqrt (B / C₁) * Real.sqrt ℓ := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hL hC₁.le
  have hαS : α * N ^ (M.δ / 10000) ≤ N ^ (M.δ / 1000) := by
    rw [hS]; exact mul_le_mul_of_nonneg_right hE6 (by positivity)
  have hNp : 0 < N ^ (M.δ / 10000) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hS0]
  have h1 : Csl * (2 * Real.sqrt (L / C₁)) ≤ α / 1200 * Real.sqrt ℓ := by
    rw [hα]
    have := mul_le_mul_of_nonneg_left hsqL (by positivity : (0 : ℝ) ≤ 2 * Csl)
    nlinarith
  have h2 : α / 1200 * Real.sqrt ℓ ≤ Q M K A ℓ / 400 * N ^ (M.δ / 1000) := by
    have h3 : α / 1200 * Real.sqrt ℓ = Real.sqrt ℓ * N ^ (-(M.δ / 10000)) / 3 / 400 *
        (α * N ^ (M.δ / 10000)) := by
      field_simp
      rw [mul_assoc, hNinv]
      norm_num
    rw [h3]
    have h4 : Real.sqrt ℓ * N ^ (-(M.δ / 10000)) / 3 / 400 ≤ Q M K A ℓ / 400 := by linarith
    have h5 : 0 ≤ Real.sqrt ℓ * N ^ (-(M.δ / 10000)) / 3 / 400 := by positivity
    have h6 : 0 ≤ Q M K A ℓ / 400 := by linarith
    calc Real.sqrt ℓ * N ^ (-(M.δ / 10000)) / 3 / 400 * (α * N ^ (M.δ / 10000))
        ≤ Q M K A ℓ / 400 * (α * N ^ (M.δ / 10000)) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ ≤ Q M K A ℓ / 400 * N ^ (M.δ / 1000) := mul_le_mul_of_nonneg_left hαS h6
  linarith

end Scales

end CurvatureVariance.Paper.Moments.Parent
