/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Restricted
public import IsotropicVariance.Infra.Curves.Concat
public import IsotropicVariance.Infra.Curves.Congr
public import IsotropicVariance.Infra.Curves.Bounds
import Mathlib.Tactic.Linarith

/-!
# 1-optimal curves

The facts about 1-optimal curves that the proof of Lemma `lem:localization` uses: a subarc of a
1-optimal curve is 1-optimal between its endpoints (Section `ssec:overview`), a 1-optimal curve
for a density bounded below by `a > 0` has length at most `(D + 1)/a`, and its points are within
that length of its endpoints.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace IsotropicVariance.Paper.Proofs.Localization

variable {m : ℕ}

/-- The concatenation of two curves in `S` stays in `S`. -/
lemma concat_mem {S : Set (Pt m)} {γ δ : RectifiableCurve (Pt m)} (hend : γ.toFun 1 = δ.toFun 0)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S) (hδ : ∀ t ∈ Icc (0 : ℝ) 1, δ.toFun t ∈ S) :
    ∀ t ∈ Icc (0 : ℝ) 1, (γ.concat δ hend).toFun t ∈ S := by
  intro t _
  change RectifiableCurve.concatFun γ δ t ∈ S
  rcases le_total t (1 / 2) with h | h
  · rw [RectifiableCurve.concatFun_left _ _ h]
    exact hγ _ (projIcc 0 1 zero_le_one _).2
  · rw [RectifiableCurve.concatFun_right _ _ hend h]
    exact hδ _ (projIcc 0 1 zero_le_one _).2

/-- A subcurve of a curve in `S` stays in `S`. -/
lemma subcurve_mem {S : Set (Pt m)} {γ : RectifiableCurve (Pt m)}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) : ∀ t ∈ Icc (0 : ℝ) 1, (γ.subcurve a b ha hab hb).toFun t ∈ S := by
  intro t ht
  obtain ⟨h1, h2⟩ := Infra.Curves.subParam_mapsTo hab ht
  exact hγ _ ⟨ha.trans h1, h2.trans hb⟩

lemma cost_subcurve_zero_one (γ : RectifiableCurve (Pt m)) (ρ : Pt m → ℝ≥0∞) :
    (γ.subcurve 0 1 le_rfl zero_le_one le_rfl).cost ρ = γ.cost ρ :=
  RectifiableCurve.cost_congr_curve (fun t _ => by
    simp [RectifiableCurve.subcurve, Infra.Curves.subParam]) ρ

lemma cost_ne_top {σ : Pt m → ℝ} {B : ℝ} (hB : ∀ x, σ x ≤ B) (γ : RectifiableCurve (Pt m)) :
    γ.cost (fun x => ENNReal.ofReal (σ x)) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top γ.length_ne_top)
    (γ.cost_le_mul_length fun x => ENNReal.ofReal_le_ofReal (hB x))

/-- 1-optimality in `[0, ∞]`: the cost is at most the restricted infimum plus one. -/
lemma isOneOptimal_iff {σ : Pt m → ℝ} {B : ℝ} (hB : ∀ x, σ x ≤ B) {S : Set (Pt m)}
    {u v : Pt m} {γ : RectifiableCurve (Pt m)} :
    IsOneOptimal σ S u v γ ↔ γ.toFun 0 = u ∧ γ.toFun 1 = v ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S) ∧
      γ.cost (fun x => ENNReal.ofReal (σ x)) ≤ restrictedInf σ S u v + 1 := by
  unfold IsOneOptimal
  constructor
  · rintro ⟨h0, h1, hS, hc⟩
    refine ⟨h0, h1, hS, hc.trans_eq ?_⟩
    have hfin : restrictedInf σ S u v ≠ ⊤ := ne_top_of_le_ne_top (cost_ne_top hB γ)
      (restrictedInf_le_cost γ h0 h1 hS)
    rw [restrictedPassageTime_eq_toReal, ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
      ENNReal.ofReal_toReal hfin, ENNReal.ofReal_one]
  · rintro ⟨h0, h1, hS, hc⟩
    refine ⟨h0, h1, hS, hc.trans_eq ?_⟩
    have hfin : restrictedInf σ S u v ≠ ⊤ := ne_top_of_le_ne_top (cost_ne_top hB γ)
      (restrictedInf_le_cost γ h0 h1 hS)
    rw [restrictedPassageTime_eq_toReal, ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
      ENNReal.ofReal_toReal hfin, ENNReal.ofReal_one]

/-- The length of a curve in `[0, ∞)`. -/
lemma length_toReal_le_of_cost {σ : Pt m → ℝ} {a : ℝ} (ha : 0 < a) (haσ : ∀ x, a ≤ σ x)
    {γ : RectifiableCurve (Pt m)} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : γ.cost (fun x => ENNReal.ofReal (σ x)) ≤ ENNReal.ofReal c) :
    γ.length.toReal ≤ c / a := by
  have h := (γ.mul_length_le_cost (a := ENNReal.ofReal a)
    fun x => ENNReal.ofReal_le_ofReal (haσ x)).trans hc
  rw [le_div_iff₀ ha, mul_comm]
  calc a * γ.length.toReal = (ENNReal.ofReal a * γ.length).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le]
    _ ≤ (ENNReal.ofReal c).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = c := ENNReal.toReal_ofReal hc0

/-- Points of a curve are within its length of each other. -/
lemma dist_le_length {γ : RectifiableCurve (Pt m)} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1) : dist (γ.toFun s) (γ.toFun t) ≤ γ.length.toReal := by
  have h := (γ.subcurve s t hs hst ht).edist_endpoints_le_length
  rw [RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end,
    RectifiableCurve.length_subcurve] at h
  have h2 : γ.arcLengthMeasure (Icc s t) ≤ γ.length := by
    rw [← RectifiableCurve.arcLengthMeasure_univ]
    exact measure_mono (subset_univ _)
  rw [edist_dist] at h
  have := (ENNReal.ofReal_le_iff_le_toReal γ.length_ne_top).1 (h.trans h2)
  exact this

/-- A curve whose cost is at most `c`, for a density at least `a > 0`, keeps within `c/a` of its
starting point. -/
lemma dist_start_le {σ : Pt m → ℝ} {a : ℝ} (ha : 0 < a) (haσ : ∀ x, a ≤ σ x)
    {γ : RectifiableCurve (Pt m)} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : γ.cost (fun x => ENNReal.ofReal (σ x)) ≤ ENNReal.ofReal c) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : dist (γ.toFun 0) (γ.toFun t) ≤ c / a :=
  (dist_le_length le_rfl ht.1 ht.2).trans (length_toReal_le_of_cost ha haσ hc0 hc)

end IsotropicVariance.Paper.Proofs.Localization
