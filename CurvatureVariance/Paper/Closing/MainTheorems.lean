/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
import CurvatureVariance.Infra.FPP.Lattice
import CurvatureVariance.Paper.Closing.VarianceSentence
import CurvatureVariance.Paper.Proofs.Reduction.Transport

/-!
# The closing: the theorem at `⌊nξ⌋` and the theorem at one direction

Neither theorem is in the paper.

* `mainUniformStatement`: `Contracts.MainUniformStatement`, a corollary of the variance sentence
  after Theorem `thm:main`. With
  `ε₁ = min(ε, 1/2)`, `ε' = ε₁/2`, `n₀ = max(2d, ⌈(4C²)^{1/ε'}⌉)`, `n ≥ n₀` and `x = ⌊nξ⌋`:
  `|x − nξ| ≤ √d`, `n/2 ≤ |x| ≤ 2n`, `β = n` witnesses the ray (`floorVertex_near_ray`), and
  `Var T ≤ 2C²|x|^{1−ε} ≤ 4C²n^{1−ε₁} ≤ n^{1−ε'}` (`two_mul_sq_mul_rpow_le`). `ε'` and `n₀` depend
  only on `ε, C, d`, so they come before `ξ`.
* `mainTheoremStatement`: `Contracts.MainTheoremStatement`, at the level of the model. It is not
  derived from Theorem `thm:main`: its hypothesis `AssumptionCAt` is on a transverse `H` at a
  direction that need not be a unit vector. The proof takes the model and the map `Φ` of the
  choice of coordinates (`ReductionStatement`), the bounds of the model itself
  (`OwnBoundsStatement`) and the final target (`FinalTargetStatement`), with the variance from
  equation `eq:premise` at every length (`evariance_passageTime_le_of_premise`): the constants are
  `ε = δ/K` and `C = 2A²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Closing

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- For `n ≥ 2d` and a unit vector `ξ`, `x = ⌊nξ⌋` satisfies `n/2 ≤ |x| ≤ 2n`, and it lies within
`|x|^{3/4}` of `nξ`: `|x − nξ| ≤ √d ≤ d^{3/4} ≤ |x|^{3/4}`. -/
theorem floorVertex_near_ray {ξ : Pt m} (hξ : ‖ξ‖ = 1) {n : ℕ} (hn : 2 * (m + 1) ≤ n) :
    (n : ℝ) / 2 ≤ ‖point (floorVertex ((n : ℝ) • ξ))‖ ∧
      ‖point (floorVertex ((n : ℝ) • ξ))‖ ≤ 2 * n ∧
      ‖point (floorVertex ((n : ℝ) • ξ)) - (n : ℝ) • ξ‖ ≤
        ‖point (floorVertex ((n : ℝ) • ξ))‖ ^ ((3 : ℝ) / 4) := by
  set x := floorVertex ((n : ℝ) • ξ)
  have hfl : ‖point x - (n : ℝ) • ξ‖ ≤ Real.sqrt ((m : ℝ) + 1) :=
    Proofs.Reduction.norm_point_floorVertex_sub_le _
  have hd1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hnd : 2 * ((m : ℝ) + 1) ≤ n := by exact_mod_cast hn
  have hSd : Real.sqrt ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_self_of_one_le hd1 (by norm_num)
  have hnorm : ‖(n : ℝ) • ξ‖ = n := by
    rw [norm_smul, hξ, mul_one, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have h1 : ‖(n : ℝ) • ξ‖ - ‖point x‖ ≤ ‖point x - (n : ℝ) • ξ‖ := by
    rw [norm_sub_rev (point x)]
    exact norm_sub_norm_le _ _
  have h2 : ‖point x‖ - ‖(n : ℝ) • ξ‖ ≤ ‖point x - (n : ℝ) • ξ‖ := norm_sub_norm_le _ _
  rw [hnorm] at h1 h2
  have hlo : (n : ℝ) / 2 ≤ ‖point x‖ := by linarith only [h1, hfl, hSd, hnd]
  refine ⟨hlo, by linarith only [h2, hfl, hSd, hnd], hfl.trans ?_⟩
  calc Real.sqrt ((m : ℝ) + 1) = ((m : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    _ ≤ ((m : ℝ) + 1) ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
    _ ≤ ‖point x‖ ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow (by linarith only [hd1]) (by linarith only [hlo, hnd]) (by norm_num)

/-- The arithmetic of the corollary: for `1 ≤ R ≤ 2n`, `0 < 2e ≤ ε`, `2e ≤ 1/2` and `4C² ≤ n^e`,
`2C² R^{1−ε} ≤ n^{1−e}`. Here `2e` is the `ε₁` of the route. -/
theorem two_mul_sq_mul_rpow_le {C ε e R n : ℝ} (hR1 : 1 ≤ R) (hRn : R ≤ 2 * n) (he0 : 0 < e)
    (he : 2 * e ≤ ε) (he2 : 2 * e ≤ 1 / 2) (hnB : 4 * C ^ 2 ≤ n ^ e) :
    2 * C ^ 2 * R ^ (1 - ε) ≤ n ^ (1 - e) := by
  have hn : 0 < n := by linarith only [hR1, hRn]
  have hR0 : 0 ≤ R := by linarith only [hR1]
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have hpow : 0 ≤ n ^ (1 - 2 * e) := Real.rpow_nonneg hn.le _
  have h1 : R ^ (1 - ε) ≤ R ^ (1 - 2 * e) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by linarith only [he])
  have h2 : R ^ (1 - 2 * e) ≤ 2 * n ^ (1 - 2 * e) := by
    calc R ^ (1 - 2 * e) ≤ (2 * n) ^ (1 - 2 * e) :=
          Real.rpow_le_rpow hR0 hRn (by linarith only [he2])
      _ = (2 : ℝ) ^ (1 - 2 * e) * n ^ (1 - 2 * e) := Real.mul_rpow zero_le_two hn.le
      _ ≤ 2 * n ^ (1 - 2 * e) := by
          refine mul_le_mul_of_nonneg_right ?_ hpow
          exact Real.rpow_le_self_of_one_le one_le_two (by linarith only [he0])
  have h3 : n ^ e * n ^ (1 - 2 * e) = n ^ (1 - e) := by
    rw [← Real.rpow_add hn]
    ring_nf
  calc 2 * C ^ 2 * R ^ (1 - ε) ≤ 2 * C ^ 2 * (2 * n ^ (1 - 2 * e)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = 4 * C ^ 2 * n ^ (1 - 2 * e) := by ring
    _ ≤ n ^ e * n ^ (1 - 2 * e) := mul_le_mul_of_nonneg_right hnB hpow
    _ = n ^ (1 - e) := h3

/-- **The statement of `CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`**, a
corollary of the variance sentence after Theorem `thm:main`. -/
theorem mainUniformStatement {m : ℕ} (hV : VarianceSentenceStatement m) :
    MainUniformStatement m := by
  intro hm F _ hW P _ hP μ hμ δ r M c hδ hδ₁ hr hM hc
  obtain ⟨ε, hε, C, hC, hb⟩ := hV hm F hW P hP μ hμ δ r M c hδ hδ₁ hr hM hc
  set ε₁ : ℝ := min ε (1 / 2) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε (by norm_num)
  set e : ℝ := ε₁ / 2 with he
  have he0 : 0 < e := by positivity
  have hB : 0 < 4 * C ^ 2 := by positivity
  refine ⟨e, he0, max (2 * (m + 1)) ⌈(4 * C ^ 2) ^ (1 / e)⌉₊, fun ξ hξ hCξ n hn => ?_⟩
  have hnB : 4 * C ^ 2 ≤ (n : ℝ) ^ e := le_rpow_of_ceil_le hB he0 ((le_max_right _ _).trans hn)
  obtain ⟨hlo, hhi, hnear⟩ := floorVertex_near_ray hξ ((le_max_left _ _).trans hn)
  set x := floorVertex ((n : ℝ) • ξ) with hxdef
  have hd : (2 : ℝ) ≤ n := by
    have h1 : 2 * (m + 1) ≤ n := (le_max_left _ _).trans hn
    have h2 : 2 ≤ n := by omega
    exact_mod_cast h2
  have hx1 : 1 ≤ ‖point x‖ := by linarith only [hlo, hd]
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, Infra.FPP.point_zero, norm_zero] at hx1
    exact absurd hx1 (by norm_num)
  have hbx := (hb ξ hξ hCξ x hx ⟨n, Nat.cast_nonneg n, hnear⟩).2.2
  refine hbx.trans (ENNReal.ofReal_le_ofReal ?_)
  exact two_mul_sq_mul_rpow_le hx1 hhi he0 (by rw [he]; linarith only [min_le_left ε (1 / 2 : ℝ)])
    (by rw [he]; linarith only [min_le_right ε (1 / 2 : ℝ)]) hnB

/-- **The statement of `CurvatureVariance.evariance_passageTime_floorVertex_le`** (the theorem at
one direction, not in the paper), at the level of the model: the variance from equation
`eq:premise` at every length, with the bounds of the model itself, through the choice of
coordinates at one direction and the final target. -/
theorem mainTheoremStatement {m : ℕ} (hD : DomainExpStatement m)
    (hO : OwnBoundsStatement m) (hR : ReductionStatement m) (hF : FinalTargetStatement m) :
    MainTheoremStatement m := by
  intro hm F _ hW P _ hP μ hμ ξ hξ H hH hC
  obtain ⟨M, Φ, a, C₀, hM, ha, hvar, hdist⟩ := hR hm F hW P hP μ hμ ξ hξ H hH hC
  have := hM.probP
  obtain ⟨bd, hbd, hfit⟩ := hO M hM
  obtain ⟨K₀, hK₀⟩ := hD bd hbd
  set K : ℕ := max K₀ (10 ^ 4) with hKdef
  have hK4 : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast (le_max_right K₀ (10 ^ 4))
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK4
  obtain ⟨A, hA1, hprem⟩ := hK₀ K (le_max_left _ _) (le_max_right _ _)
  obtain ⟨n₁, hn₁⟩ := hF bd hbd a a C₀ ha le_rfl
  have hε : 0 < M.δ / K := div_pos hM.delta_pos hK0
  set e := min (M.δ / K) (1 / 4) with hedef
  have he : 0 < e := lt_min hε (by norm_num)
  set B := max (2 * A ^ 2) 1 * (a + 1) with hBdef
  have hB0 : 0 < B := mul_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) (by linarith only [ha])
  refine ⟨e, he, max n₁ ⌈B ^ (1 / e)⌉₊, fun n hn => ?_⟩
  obtain ⟨s, hs1, hsle, hz1, hz2⟩ :=
    hn₁ M hM hfit a le_rfl le_rfl _ hdist n ((le_max_left _ _).trans hn)
  set z := Φ (floorVertex ((n : ℝ) • ξ)) with hzdef
  have hzeq : z = ((s : ℤ), z.2) := Prod.ext hz1 rfl
  have hBn : B ≤ (n : ℝ) ^ e := le_rpow_of_ceil_le hB0 he ((le_max_right _ _).trans hn)
  rw [hvar n, ← hzdef, hzeq]
  refine (evariance_passageTime_le_of_premise hA1 (hprem M hM hfit) hs1 hz2).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_rpow_le_rpow_of_le he (min_le_right _ _) (min_le_left _ _) ha
    (by exact_mod_cast hs1) hsle hBn

end CurvatureVariance.Paper.Closing
