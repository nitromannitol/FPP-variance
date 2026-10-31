/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parameters for the near-pair moment bound

First choose a localization cutoff, then a small profile error and a large block side.
All choices depend only on the fixed moment and constants, not on the number of slabs.
The formula is exactly the one obtained in `NearAverage` for the proof of Lemma `lem:residual`.
-/

@[expose] public section

namespace IsotropicVariance.Paper.Proofs.LabelResidual

/-- Uniform numerical choices make the near-pair `p`-th moment at most `λ^p`. -/
theorem exists_near_moment_parameters (m p : ℕ) (hp : 1 ≤ p) {C Cr lam D : ℝ}
    (hC : 0 < C) (hCr : 0 < Cr) (hlam : 0 < lam) (hD : 0 ≤ D) :
    ∃ ε₀ R : ℝ, 0 < ε₀ ∧ 0 ≤ R ∧ ∃ L₀ : ℕ,
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ → ∀ L : ℕ+, L₀ ≤ (L : ℕ) →
        ∀ r : ℝ, 0 ≤ r → r ≤ D →
          (2*ε)^(2*p) + (C*(1+r))^p *
            (2*Real.exp (-(R/Cr)^2) + (m : ℝ) *
              (r + 2*(2*Real.sqrt m+2+R) + 2*Real.sqrt (L : ℕ) + 2) / (L : ℝ)) ^
                (3/4 : ℝ) ≤ lam^p := by
  set B : ℝ := (C*(1+D))^p with hB
  have hB0 : 0 ≤ B := by positivity
  set x : ℝ := lam^p / (2*(B+1)) with hx
  have hx0 : 0 < x := by positivity
  set δ : ℝ := min 1 (x^(4/3 : ℝ)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (Real.rpow_pos_of_pos hx0 _)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hBδ : B*δ^(3/4 : ℝ) ≤ lam^p/2 := by
    have h1 : δ^(3/4 : ℝ) ≤ x := by
      calc
        _ ≤ (x^(4/3 : ℝ))^(3/4 : ℝ) :=
          Real.rpow_le_rpow hδ0.le (min_le_right _ _) (by norm_num)
        _ = x := by rw [← Real.rpow_mul hx0.le]; norm_num
    calc
      _ ≤ B*x := mul_le_mul_of_nonneg_left h1 hB0
      _ ≤ (B+1)*x := by nlinarith only [hx0]
      _ = lam^p/2 := by rw [hx]; field_simp
  have hq : 0 < 4/δ := by positivity
  have hlog : 0 ≤ Real.log (4/δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  set R : ℝ := Cr*Real.sqrt (Real.log (4/δ)) with hRdef
  have hR : 0 ≤ R := by positivity
  have htail : 2*Real.exp (-(R/Cr)^2) = δ/2 := by
    have heq : R/Cr = Real.sqrt (Real.log (4/δ)) := by rw [hRdef]; field_simp
    rw [heq, Real.sq_sqrt hlog, Real.exp_neg, Real.exp_log hq]
    field_simp
    norm_num
  set U : ℝ := D+2*(2*Real.sqrt m+2+R)+2 with hU
  have hU0 : 0 ≤ U := by positivity
  set A : ℝ := m*(U+2) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨min 1 (Real.sqrt lam/4), R, lt_min one_pos (by positivity), hR,
    ⌈(2*A/δ)^2⌉₊+1, ?_⟩
  intro ε hε0 hε L hL r hr0 hrD
  have hLr : (1 : ℝ) ≤ (L : ℕ) := by exact_mod_cast L.pos
  have hLp : (0 : ℝ) < (L : ℕ) := by linarith only [hLr]
  have hεs : ε ≤ Real.sqrt lam/4 := hε.trans (min_le_right _ _)
  have hε2 : (2*ε)^2 ≤ lam/4 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ 2*ε)
      (show 2*ε ≤ Real.sqrt lam/2 by linarith only [hεs]) 2
    nlinarith only [H, Real.sq_sqrt hlam.le]
  have hεp : (2*ε)^(2*p) ≤ lam^p/2 := by
    rw [pow_mul]
    calc
      _ ≤ (lam/4)^p := pow_le_pow_left₀ (sq_nonneg _) hε2 p
      _ = lam^p*(1/4 : ℝ)^p := by rw [← mul_pow]; ring_nf
      _ ≤ lam^p*(1/4 : ℝ) := mul_le_mul_of_nonneg_left
        (pow_le_of_le_one (by norm_num) (by norm_num) (by omega)) (by positivity)
      _ ≤ lam^p/2 := by nlinarith only [pow_pos hlam p]
  have hLN : (2*A/δ)^2 ≤ ((L : ℕ) : ℝ) := by
    have H : ((⌈(2*A/δ)^2⌉₊+1 : ℕ) : ℝ) ≤ ((L : ℕ) : ℝ) := by exact_mod_cast hL
    push_cast at H
    linarith only [H, Nat.le_ceil ((2*A/δ)^2)]
  have hs1 : 1 ≤ Real.sqrt ((L : ℕ) : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hLr
  have hsL := Real.mul_self_sqrt hLp.le
  have hs : 2*A/δ ≤ Real.sqrt ((L : ℕ) : ℝ) := Real.le_sqrt_of_sq_le hLN
  have hAs : A ≤ δ/2*Real.sqrt ((L : ℕ) : ℝ) := by
    rw [div_le_iff₀ hδ0] at hs
    nlinarith only [hs]
  have hnum : r+2*(2*Real.sqrt m+2+R)+2*Real.sqrt (L : ℕ)+2 ≤
      (U+2)*Real.sqrt ((L : ℕ) : ℝ) := by
    have H := mul_nonneg hU0 (sub_nonneg.mpr hs1)
    dsimp only [U] at H ⊢
    nlinarith only [H, hrD, hs1]
  have hfrac : (m : ℝ)*(r+2*(2*Real.sqrt m+2+R)+2*Real.sqrt (L : ℕ)+2) /
      ((L : ℕ) : ℝ) ≤ δ/2 := by
    rw [div_le_iff₀ hLp]
    calc
      _ ≤ (m : ℝ)*((U+2)*Real.sqrt ((L : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)
      _ = A*Real.sqrt ((L : ℕ) : ℝ) := by rw [hA]; ring
      _ ≤ (δ/2*Real.sqrt ((L : ℕ) : ℝ))*Real.sqrt ((L : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hAs (Real.sqrt_nonneg _)
      _ = δ/2*((L : ℕ) : ℝ) := by rw [mul_assoc, hsL]
  have hpar : 2*Real.exp (-(R/Cr)^2) + (m : ℝ)*
      (r+2*(2*Real.sqrt m+2+R)+2*Real.sqrt (L : ℕ)+2)/(L : ℝ) ≤ δ := by
    rw [htail]
    linarith only [hfrac]
  have hbase : 0 ≤ 2*Real.exp (-(R/Cr)^2) + (m : ℝ)*
      (r+2*(2*Real.sqrt m+2+R)+2*Real.sqrt (L : ℕ)+2)/(L : ℝ) := by positivity
  have hrpow := Real.rpow_le_rpow hbase hpar (by norm_num : (0 : ℝ) ≤ 3/4)
  have hCB : (C*(1+r))^p ≤ B :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith only [hrD]) hC.le) p
  have hprod := mul_le_mul hCB hrpow (Real.rpow_nonneg hbase _) hB0
  linarith only [hεp,hprod,hBδ]

end IsotropicVariance.Paper.Proofs.LabelResidual
