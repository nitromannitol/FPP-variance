/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.UniformMetric
public import IsotropicVariance.Paper.Proofs.SlabComparison.PolynomialMesh
public import IsotropicVariance.Paper.Proofs.SlabComparison.ScaleBounds

/-! # The pathwise uniform metric scale in the containing cube

This is the probabilistic construction of the random scale `W` in the proof of Lemma
`lem:straight`, using the classical contract, proper-motion covariance, a finite mesh, and endpoint
Lipschitz continuity.
-/

@[expose] public section
open MeasureTheory Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Contracts
universe u
variable {m : ℕ}

/-- One sub-Gaussian scale controls every pair in the containing cube, on every outcome. -/
theorem uniform_metric_scale_of (hclassical : ClassicalBoundsStatement.{u}) (hm : 1 ≤ m)
    (X : Setting.{u} m) (hnorm : X.IsNormalized) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : Pt m,
      ∃ S : X.Ω → ℝ, (∀ ω, 1 + Real.log (2 + R) ≤ S ω) ∧
        Cited.IsOs X.P 2 (C * Real.log (2 + R)) S ∧
        ∀ ω, ∀ x ∈ cubeAround z (R ^ 3), ∀ y ∈ cubeAround z (R ^ 3),
          |X.passTime ω x y - dist x y| ≤
            A * (S ω * Real.sqrt (dist x y) + S ω ^ 2) := by
  obtain ⟨B, hB, hbound⟩ := Profiles.exists_upperBound X
  obtain ⟨Cb, Cz, hCb, hCz, hfinite⟩ := finite_metric_scale_of hclassical hm X hnorm
  let BN := 4 * (m + 2 : ℝ) ^ (2 * (m + 1))
  let BD := 2 * (m + 1 : ℝ) + 3
  have hBN : 1 ≤ BN := by
    have hh : (1 : ℝ) ≤ (m + 2 : ℝ) ^ (2 * (m + 1)) := one_le_pow₀ (by have hh : (0 : ℝ) ≤ m := Nat.cast_nonneg _; linarith)
    dsimp [BN]
    linarith
  have hBD : 1 ≤ BD := by dsimp [BD]; have hh : (0 : ℝ) ≤ m := Nat.cast_nonneg _; linarith
  obtain ⟨C, hC, hscale⟩ := exists_logarithmic_scale_bound (qN := 6 * (m + 1)) (qD := 3)
    hBN hBD hCb hCz
  refine ⟨5 * B + 8, C, by positivity, hC, fun R hR z => ?_⟩
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  obtain ⟨G, hGne, hGcard, hGinside, hcover⟩ := exists_unit_mesh z hR3
  let T := meshPairs z G
  have hT : T.Nonempty := meshPairs_nonempty z G
  let D := 2 * (m + 1 : ℝ) * R ^ 3 + 1
  have hD : 1 ≤ D := by
    have hh : 0 ≤ 2 * (m + 1 : ℝ) * R ^ 3 := by positivity
    dsimp [D]
    linarith
  have hlog : 0 < Real.log (2 + R) := Real.log_pos (by linarith)
  obtain ⟨S, hfloor, hOs, hmetric⟩ := hfinite T hT D (1 + Real.log (2 + R)) hD
    (by linarith) (fun p hp => meshPairs_dist_bounds (by positivity) hGinside hp)
  refine ⟨S, hfloor, ?_, fun ω => ?_⟩
  · have hN : (1 : ℝ) ≤ 2 * (T.card : ℝ) := by
      have hh : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
      linarith
    have hpolyN : 2 * (T.card : ℝ) ≤ BN * (2 + R) ^ (6 * (m + 1)) :=
      card_meshPairs_polynomial hR z G hGcard
    have hpolyD : 2 + D ≤ BD * (2 + R) ^ 3 := mesh_diameter_polynomial hR
    have hsc := hscale R (2 * (T.card : ℝ)) D hR hN (by linarith) hpolyN hpolyD
    have hcard : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
    have hlogN : 0 < Real.log (2 * (T.card : ℝ)) := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    apply hOs.mono_scale (by norm_num) (by positivity)
    convert hsc using 1; congr 2; ring
  · apply uniform_metric_of_mesh X ω hbound hB.le (by linarith [hfloor ω]) hcover
    intro x hx y hy hxy
    exact hmetric ω (x, y) (mem_meshPairs hx hy hxy)

end IsotropicVariance.Paper.Proofs.SlabComparison
