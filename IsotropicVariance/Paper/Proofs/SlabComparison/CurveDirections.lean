/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.CurveNoReturn
public import IsotropicVariance.Paper.Proofs.SlabComparison.RadialHits
public import IsotropicVariance.Paper.Proofs.SlabComparison.DirectionStep
public import IsotropicVariance.Paper.Proofs.SlabComparison.Dyadic
public import IsotropicVariance.Paper.Proofs.SlabComparison.ExistsNearOptimal
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Uniform directional control of ordered points on a 1-optimal curve -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {m : ℕ}

/-- The angle bound of Lemma `lem:straight`, whose proof makes the argument of [HN, Theorem 2.6]
and [HN, Lemma 2.7] uniform, expressed as a bound on unit vectors. It applies after any earlier
parameter `a`, not just the starting endpoint. -/
theorem curve_direction_close (X : Setting m) (ω : X.Ω)
    (γ : IsotropicVariance.RectifiableCurve (Pt m)) {u v : Pt m}
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {A S R ε : ℝ}
    (hA : 0 ≤ A) (hS : 1 ≤ S) (hR : 0 < R) (hscale : S ^ 2 ≤ R) (hε : 0 ≤ ε)
    (hNR : noReturnScale A * S ^ 2 < R)
    (hsmall : (6 * (3 * A + 1)) ^ 2 * S ^ 2 ≤ ε ^ 4 * R)
    (hmetric : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      |X.passTime ω (γ.toFun a) (γ.toFun b) - dist (γ.toFun a) (γ.toFun b)| ≤
        A * (S * Real.sqrt (dist (γ.toFun a) (γ.toFun b)) + S ^ 2))
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1)
    (hfirst : dist (γ.toFun a) (γ.toFun b) = R) :
    ‖direction (γ.toFun b - γ.toFun a) - direction (γ.toFun c - γ.toFun a)‖ ≤ 8 * ε := by
  classical
  let p := γ.toFun a
  let D := dist p (γ.toFun c)
  have hD : 0 < D := by
    have h := curve_no_return X ω γ hγ hA hS hR.le hmetric ha hab hbc hc hfirst hNR
    change R / 2 < D at h
    linarith
  have hmem (t : ℝ) (ht : t ∈ Icc a c) : t ∈ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc ha hc ht
  have hstep (t t' : ℝ) (ht : t ∈ Icc b c) (htt' : t ≤ t') (ht' : t' ≤ c)
      (r : ℝ) (hr : 0 < r) (hrS : S ^ 2 ≤ r)
      (hrT : dist p (γ.toFun t) = r) (hrT' : dist p (γ.toFun t') ≤ 2 * r)
      (hne : γ.toFun t' ≠ p) :
      ‖direction (γ.toFun t - p) - direction (γ.toFun t' - p)‖ ^ 4 * r ≤
        (6 * (3 * A + 1)) ^ 2 * S ^ 2 := by
    have ht0 : t ∈ Icc (0 : ℝ) 1 := hmem t ⟨hab.trans ht.1, ht.2⟩
    have ht1 : t' ∈ Icc (0 : ℝ) 1 := hmem t' ⟨(hab.trans ht.1).trans htt', ht'⟩
    have ha0 : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans (hbc.trans hc)⟩
    exact direction_step_fourth hA hS hr hrS hrT hne hrT'
      (hmetric a ha0 t ht0) (hmetric t ht0 t' ht1) (hmetric a ha0 t' ht1)
      (ordered_passTime_defect X ω γ hγ ha (hab.trans ht.1) htt' (ht'.trans hc))
  by_cases hRD : R < D
  · obtain ⟨t, ht0, htmono, ht⟩ := exists_dyadic_radial_hits γ p (ha.trans hab) hbc hc
      hR hRD hfirst rfl
    have hex : ∃ n : ℕ, D ≤ R * 2 ^ n := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D / R) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, (div_le_iff₀ hR).mp hn.le |>.trans_eq (mul_comm _ _)⟩
    let n := Nat.find hex
    have hn : D ≤ R * 2 ^ n := Nat.find_spec hex
    have hlast : t n = c := (ht n).2.2 hn
    have hbefore (j : ℕ) (hj : j < n) : R * 2 ^ j < D :=
      lt_of_not_ge (Nat.find_min hex hj)
    have hbound := dyadic_chain_direction_bound
      (fun j => direction (γ.toFun (t j) - p)) n hε hR
      (fun j hj => ?_) hsmall
    · simpa only [ht0, hlast, norm_sub_rev, p] using hbound
    · have hrj : 0 < R * (2 : ℝ) ^ j := by positivity
      have hrjS : S ^ 2 ≤ R * (2 : ℝ) ^ j := hscale.trans
        (le_mul_of_one_le_right hR.le (one_le_pow₀ (by norm_num)))
      have hrad : dist p (γ.toFun (t j)) = R * 2 ^ j :=
        (ht j).2.1.trans (min_eq_left (hbefore j hj).le)
      have hrad' : dist p (γ.toFun (t (j + 1))) ≤ 2 * (R * 2 ^ j) := by
        rw [(ht (j + 1)).2.1]
        apply (min_le_left _ _).trans_eq
        rw [pow_succ]
        ring
      have hne : γ.toFun (t (j + 1)) ≠ p := by
        intro heq
        have hh := (ht (j + 1)).2.1
        rw [heq, dist_self] at hh
        have hp : 0 < min (R * (2 : ℝ) ^ (j + 1)) D := lt_min (by positivity) hD
        linarith
      simpa only [norm_sub_rev] using hstep (t j) (t (j + 1)) (ht j).1 (htmono (Nat.le_succ _)) (ht (j + 1)).1.2
        _ hrj hrjS hrad hrad' hne
  · have hDC : D ≤ 2 * R := by linarith [le_of_not_gt hRD]
    have hne : γ.toFun c ≠ p := by intro h; change 0 < dist p (γ.toFun c) at hD; simp [h] at hD
    have hs := hstep b c ⟨le_rfl, hbc⟩ hbc le_rfl R hR hscale hfirst hDC hne
    have hsmall' := fourth_power_dyadic_le hε hR 0 (by simpa using hs) hsmall
    simp only [pow_zero, mul_one] at hsmall'
    exact hsmall'.trans (by linarith)

/-- The same direction bound applies at every radius beyond the chosen threshold. -/
theorem curve_direction_close_of_radius (X : Setting m) (ω : X.Ω)
    (γ : IsotropicVariance.RectifiableCurve (Pt m)) {u v : Pt m}
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {A S R ε : ℝ}
    (hA : 0 ≤ A) (hS : 1 ≤ S) (hR : 0 < R) (hscale : S ^ 2 ≤ R) (hε : 0 ≤ ε)
    (hNR : noReturnScale A * S ^ 2 < R)
    (hsmall : (6 * (3 * A + 1)) ^ 2 * S ^ 2 ≤ ε ^ 4 * R)
    (hmetric : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      |X.passTime ω (γ.toFun a) (γ.toFun b) - dist (γ.toFun a) (γ.toFun b)| ≤
        A * (S * Real.sqrt (dist (γ.toFun a) (γ.toFun b)) + S ^ 2))
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1)
    (hfirst : R ≤ dist (γ.toFun a) (γ.toFun b)) :
    ‖direction (γ.toFun b - γ.toFun a) - direction (γ.toFun c - γ.toFun a)‖ ≤ 8 * ε := by
  exact curve_direction_close X ω γ hγ hA hS (hR.trans_le hfirst)
    (hscale.trans hfirst) hε (hNR.trans_le hfirst)
    (hsmall.trans (mul_le_mul_of_nonneg_left hfirst (by positivity)))
    hmetric ha hab hbc hc rfl

end IsotropicVariance.Paper.Proofs.SlabComparison
