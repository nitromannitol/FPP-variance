/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Inputs
public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Statements.Inputs.AeExistsIsPathWalkCostEqPassageTime
import CurvatureVariance.Paper.Proofs.Localization.ModulusFixed
import CurvatureVariance.Paper.Proofs.Moments.Scales
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# Lemma `lem:modulus`

`modulusStatement`: Lemma `lem:modulus`, `ModulusStatement`, from Proposition `prop:profiles`,
Lemma `lem:localization` at `p = 16d`, equations `eq:support` and `eq:scales`, and the union bound
`eq:union`, following the paper's proof of Lemma `lem:modulus`, which is the proof of
[AB26, Lemma 5.2] with the changes of the paper.

The choice of the parameters is the paper's, with `g` for its `γ`, `h = g⁴` for its `h = γ³`, and
the exponent `1/3` for its `2/5` in the bound of `Q_{⌈gℓ⌉}`. The number `g ∈ (0, 1/128)`, and
`h = g⁴`, depend only on `b`, `η` and the bounds, through the closing line of the proof, and come
before `K` and `κ`, since the constants of the premises do; the cubes of Proposition
`prop:profiles` at length `s = ⌈gℓ⌉` have `b = 1`, so `g` is not circular. The threshold depends on
`K`, `b`, `κ` and `η`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Localization

open Modulus

variable {m : ℕ}

/-- **Lemma `lem:modulus`**, with its proof, equation `eq:modulus`: one `h(b, η)`, from the premises
of the edge `lem:modulus` of the graph in `Closing.Main`. -/
theorem modulusStatement (hProf : Contracts.ProfilesStatement m)
    (hLoc : Contracts.LocalizationStatement m) (hSup : Contracts.SupportStatement m)
    (hScales : Contracts.ScalesStatement m) (hUnion : Contracts.OsUnionStatement.{0, 0}) :
    Contracts.ModulusStatement m := by
  intro bd hbd Cstar b hb η hη
  set q : ℕ := 2 * (8 * (m + 1)) with hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := by omega
    exact_mod_cast this
  -- the constants, before `g`
  obtain ⟨C₁, hC₁, hP1⟩ := hProf bd hbd Cstar 1 le_rfl
  obtain ⟨Cb, hCb, hPb⟩ := hProf bd hbd Cstar b hb
  obtain ⟨Cr₀, hCr₀, hRb⟩ := hLoc bd hbd Cstar b hb q hq1
  obtain ⟨cs, Cs, r₁, -, hCs, hr₁, -, hSupM⟩ := hSup bd hbd
  obtain ⟨CU, hCU, hU⟩ := hUnion 1 one_pos
  obtain ⟨r₂, hr₂, hcost⟩ := Moments.exists_slope_cost hScales bd hbd Cstar
  -- the slope bound `|t| ≤ T₀ + 1`, for the bound `|t₀| ≤ T₀` of `bd`
  set T : ℝ := bd.T + 1 with hTdef
  have hT : 1 ≤ T := by have := hbd.T_nonneg; linarith only [this]
  set Cr : ℝ := Cr₀ ^ ((q : ℝ)⁻¹) with hCrdef
  have hCr : 0 ≤ Cr := Real.rpow_nonneg hCr₀.le _
  have hCrq : Cr ^ q = Cr₀ := Real.rpow_inv_natCast_pow hCr₀.le (by omega)
  -- the number `g`, and `h = g⁴`
  obtain ⟨g, hg, hg128, hgη⟩ := exists_scale_le (rateConst_pos m hT hb hC₁ hCb hCs hCr hCU) hη
  refine ⟨g ^ 4, by positivity, fun K hK κ hκ hκ1 => ?_⟩
  set n := gridSize T b g with hndef
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg1 : g ≤ 1 := by linarith only [hg128]
  have hgκ : 0 < g * κ := mul_pos hg hκ
  have hb1 : 0 ≤ b + 1 := by linarith only [hb]
  -- the margin in `eq:scales`
  have hC₂ : 0 ≤ offsetConst m T b := by
    unfold offsetConst
    have hT0 : 0 ≤ T := by linarith only [hT]
    have hb3 : 0 ≤ b + 3 := by linarith only [hb]
    positivity
  set ηw : ℝ := min (min (1 / (8 * m * n + 1)) (g ^ 2 / 2))
    (min (r₁ * g ^ 2 / (2 * offsetConst m T b + 1)) (r₁ / (2 * m * (b + 1) + 1))) with hηwdef
  have hηw : 0 < ηw := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by positivity) (by positivity))
  have hηw1 : ηw * (2 * m * n) ≤ 1 / 4 := by
    have h1 : ηw ≤ 1 / (8 * m * n + 1) := (min_le_left _ _).trans (min_le_left _ _)
    calc ηw * (2 * m * n) ≤ 1 / (8 * m * n + 1) * (2 * m * n) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 1 / 4 := by
          rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]; linarith only
  have hηw2 : ηw ≤ g ^ 2 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hηw3 : 2 * offsetConst m T b * ηw ≤ r₁ * g ^ 2 := by
    have h1 : ηw ≤ r₁ * g ^ 2 / (2 * offsetConst m T b + 1) :=
      (min_le_right _ _).trans (min_le_left _ _)
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans
      (mul_div_add_one_le (by positivity) (by positivity))
  have hηw4 : 2 * m * (b + 1) * ηw ≤ r₁ := by
    have h1 : ηw ≤ r₁ / (2 * m * (b + 1) + 1) := (min_le_right _ _).trans (min_le_right _ _)
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans
      (mul_div_add_one_le (by positivity) hr₁.le)
  -- the thresholds
  obtain ⟨Nw, hNw⟩ := Moments.exists_width_margin hScales bd hbd Cstar hηw
  obtain ⟨N₁, hN₁⟩ := hP1 κ hκ K hK
  obtain ⟨N₂, hN₂⟩ := hPb κ hκ K hK
  obtain ⟨N₃, hN₃⟩ := hRb κ hκ K hK
  -- the slope bound `ℓ^{δ/100−1/4} → 0`
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      x ^ (bd.law.δ / 100 - 1 / 4) ≤ min 1 r₁ := by
    have hy : 0 < 1 / 4 - bd.law.δ / 100 := by have := hbd.law.delta_le_one; linarith only [this]
    have hlim := tendsto_rpow_neg_atTop hy
    have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < min 1 r₁ by positivity))
    obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
    exact ⟨x₀, fun x hx => by have := hx₀ x hx; rw [neg_sub] at this; exact this.le⟩
  set X₀ : ℝ := max (max x₀ r₂) (max (1 / g) (16 * ((m : ℝ) + 1))) with hX₀
  refine ⟨max (max N₁ N₂) (max (max N₃ Nw) (⌈X₀ / κ⌉₊ + ⌈(1 / (g * κ)) ^ 2⌉₊ + 2)),
    fun M hM hfit N hN A hA hprem hrange ℓ hℓ1 hℓ2 t I I' hII ht P hP => ?_⟩
  -- the model, after every constant and threshold
  have hPp : IsProbabilityMeasure M.P := hM.probP
  have hFp : IsProbabilityMeasure M.F := hM.probF
  have hδ : M.δ = bd.law.δ := hfit.δ_eq
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN4 : Nw ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN5 : ⌈X₀ / κ⌉₊ + ⌈(1 / (g * κ)) ^ 2⌉₊ + 2 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN22 : 2 ≤ N := by omega
  have hN5r : ((⌈X₀ / κ⌉₊ + ⌈(1 / (g * κ)) ^ 2⌉₊ + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN5
  push_cast at hN5r
  have hc1 : (0 : ℝ) ≤ ⌈X₀ / κ⌉₊ := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ ⌈(1 / (g * κ)) ^ 2⌉₊ := Nat.cast_nonneg _
  have hNX : X₀ / κ ≤ N := by
    have := Nat.le_ceil (X₀ / κ)
    linarith only [this, hN5r, hc2]
  have hNg : (1 / (g * κ)) ^ 2 ≤ N := by
    have := Nat.le_ceil ((1 / (g * κ)) ^ 2)
    linarith only [this, hN5r, hc1]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsqN : 1 / (g * κ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hNg
  -- consequences for `ℓ`
  have hℓX : X₀ ≤ ℓ := by
    have : X₀ ≤ κ * N := by rw [div_le_iff₀ hκ] at hNX; linarith only [hNX]
    linarith only [this, hℓ1]
  have hℓx₀ : x₀ ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hℓX
  have hℓr₂ : r₂ ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hℓX
  have hℓg : 1 / g ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hℓX
  have hℓm : 16 * ((m : ℝ) + 1) ≤ ℓ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hℓX
  have hℓone : (1 : ℝ) ≤ ℓ := by linarith only [hℓr₂, hr₂]
  have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hℓone]
  have hx₀ℓ : (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ min 1 r₁ := by rw [hδ]; exact hx₀ ℓ hℓx₀
  have htmin := ht.trans hx₀ℓ
  have ht1 : ‖t - M.t₀‖ ≤ 1 := htmin.trans (min_le_left _ _)
  have htr : ‖t - M.t₀‖ ≤ r₁ := htmin.trans (min_le_right _ _)
  have htT : ‖t‖ ≤ T := by
    have := norm_sub_norm_le t M.t₀
    rw [hTdef]; linarith only [this, ht1, hfit.t₀_le]
  -- the length `s = ⌈gℓ⌉`
  have hgℓ1 : 1 ≤ g * ℓ := by
    have := (div_le_iff₀ hg).mp hℓg
    linarith only [this]
  obtain ⟨hs0, hsg, hs2g⟩ := ceil_facts hgℓ1
  set s := ⌈g * ℓ⌉₊ with hsdef
  have hs2g' : (s : ℝ) ≤ 2 * g * ℓ := by linarith only [hs2g]
  have hsℓ : (s : ℝ) ≤ ℓ / 64 := by
    have := mul_le_mul_of_nonneg_right hg128.le hℓ0.le
    linarith only [this, hs2g]
  have hℓN : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓ2
  have hsqN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt N ≤ s := by
    have h1 : 1 ≤ g * κ * Real.sqrt N := by
      have := (div_le_iff₀ hgκ).mp hsqN
      linarith only [this]
    have h2 : Real.sqrt N ≤ g * κ * N := by
      have e : g * κ * N = (g * κ * Real.sqrt N) * Real.sqrt N := by
        rw [mul_assoc (g * κ), Real.mul_self_sqrt hN0]
      rw [e]
      linarith only [mul_le_mul_of_nonneg_right h1 hsqN0]
    have h3 : g * κ * N ≤ g * ℓ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hℓ1 hg.le
    linarith only [h2, h3, hsg]
  have hs32 : (s : ℝ) ≤ N / 2 := by linarith only [hsℓ, hℓN, hN0]
  have hs0r : (0 : ℝ) < s := by exact_mod_cast hs0
  have hsqrt16 : Real.sqrt N / 16 ≤ s := by linarith only [hsqrt, hsqN0]
  have hℓsqrt : Real.sqrt N / 16 ≤ ℓ := by linarith only [hsqrt16, hsℓ, hs0r]
  -- equation `eq:scales` at `ℓ` and at `s`
  have hWℓ : W M K A ℓ ≤ ηw * ℓ := by
    refine (hNw K hK M hM hfit N hN4 A hA hrange ℓ hℓsqrt).trans
      (mul_le_mul_of_nonneg_left ?_ hηw.le)
    calc (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) ≤ (ℓ : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hℓone
            (by have := hM.delta_le_one; linarith only [this])
      _ = ℓ := Real.rpow_one _
  have hWs := hNw K hK M hM hfit N hN4 A hA hrange s hsqrt16
  have htp : 0 ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) := Real.rpow_nonneg hℓ0.le _
  have hcostℓ := hcost K hK M hM hfit N hN22 A hA hrange ℓ hℓsqrt hℓr₂ t
    (by linarith only [ht, htp])
  -- Proposition `prop:profiles` at `ℓ`, in its second case, and at `s`, in its first case
  have hXi := hN₂ M hM hfit N hN2 A hA hprem hrange ℓ t I I' hII
    (Or.inr ⟨hℓ1, by linarith only [hℓN, hN0], by linarith only [ht, htp]⟩)
  have hS1 : ∀ (τ : EuclideanSpace ℝ (Fin m)) (J J' : Set (Vertex m)),
      IsCubePair M K A s 1 τ J J' → ‖τ - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
      Contracts.ShortConclusion M K A s C₁ τ J J' := fun τ J J' hJ hτ =>
    hN₁ M hM hfit N hN1 A hA hprem hrange s τ J J' hJ (Or.inl ⟨hsqrt, hs32, hτ⟩)
  -- Lemma `lem:localization` at `p = 16d`
  have hR : ∫⁻ ω, locRadius ω I I' (W M K A ℓ) ^ q ∂M.P ≤ ENNReal.ofReal (Cr ^ q) := by
    have h := (hN₃ M hM hfit N hN3 A hA hprem hrange ℓ hℓ1 hℓ2 t I I' hII ht).1
    simp only [ENNReal.rpow_natCast] at h
    rwa [hCrq]
  have hgeo := CurvatureVariance.ae_exists_isPath_walkCost_eq_passageTime hM.one_le_m M.F
    hM.assumptionW.2 M.P hM.iid
  have hsup' : ∀ h' : EuclideanSpace ℝ (Fin m), ‖h'‖ ≤ r₁ →
      supportExcess M.μ P (slopeVec (t + h')) ≤ Cs * ‖h'‖ ^ 2 + Cs * ‖t - M.t₀‖ ^ (2 + M.δ) :=
    fun h' hh' => ((hSupM M hM hfit).1 t h' htr hh' P hP).2
  obtain ⟨X, hXb, hXd⟩ := modulus_fixed M hM hK hA hb hT hg hg128.le hCb hC₁ hCr hCs hCU
    hr₁.le hU hs0 hsg hs2g' hℓm ht htT hcostℓ hηw1 hηw2 hηw3 hηw4 hWℓ hWs hII hP hsup' hgeo hXi hS1
    hR
  refine ⟨X, hXb.trans (ENNReal.ofReal_le_ofReal ?_), hXd⟩
  have hQ : 0 ≤ Q M K A ℓ := by unfold Q; positivity
  exact mul_le_mul_of_nonneg_right hgη hQ

end CurvatureVariance.Paper.Localization
