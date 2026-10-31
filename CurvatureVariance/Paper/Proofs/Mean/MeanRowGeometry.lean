/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Mean.MeanRows
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cube pairs covering consecutive rows

The reference displacement in the mean lemma is integral, so rounding the successive
row centers introduces no extra error. Width margin puts all displacements of the
closed cube pairs inside the variance domain.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP

/-- The transverse-domain power is length times the slope power. -/
theorem mean_length_mul_slope_power {δ s : ℝ} (hs : 0 < s) :
    s * s ^ (δ / 100 - 1 / 4) = s ^ ((3 : ℝ) / 4 + δ / 100) := by
  rw [show (3 : ℝ) / 4 + δ / 100 = 1 + (δ / 100 - 1 / 4) by ring,
    Real.rpow_add hs, Real.rpow_one]

/-- The reference slope at a quarter length has a fixed strict margin inside the domain. -/
theorem mean_reference_slope_bound {δ N s : ℝ} (hδ : δ ≤ 1) (hs : 0 < s) (hsN : s ≤ N / 4) :
    N ^ (δ / 100 - 1 / 4) ≤ (13 : ℝ) / 16 * s ^ (δ / 100 - 1 / 4) := by
  let α := δ / 100 - 1 / 4
  have hα : α ≤ -(1 : ℝ) / 6 := by dsimp only [α]; linarith only [hδ]
  have hα0 : α ≤ 0 := by linarith only [hα]
  have h4 : (4 : ℝ) ^ α ≤ 13 / 16 := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      (by norm_num : (6 : ℕ) ≠ 0)).mp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have he : α * 6 ≤ -1 := by linarith only [hα]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) he).trans
      (by norm_num)
  have hNs : 4 * s ≤ N := by linarith only [hsN]
  calc
    N ^ α ≤ (4 * s) ^ α := Real.rpow_le_rpow_of_nonpos (by positivity) hNs hα0
    _ = (4 : ℝ) ^ α * s ^ α := Real.mul_rpow (by norm_num) hs.le
    _ ≤ 13 / 16 * s ^ α := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hs.le _)

/-- A closed cube pair containing consecutive rows, with its exact slope and variance-domain
margin. -/
theorem exists_row_cube_pair {m : ℕ} (M : Model m) {K s w : ℕ} {A : ℝ}
    (hs : 0 < s) (hw : 0 < w) (hwW : (w : ℝ) ≤ 2 * W M K A s)
    (hwidth : Real.sqrt m * w ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16)
    {y₀ : Fin m → ℤ} {t : EuclideanSpace ℝ (Fin m)}
    (hst : (s : ℝ) • t = transversePoint y₀)
    (ht : ‖t - M.t₀‖ ≤ (13 : ℝ) / 16 * (s : ℝ) ^ (M.δ / 100 - 1 / 4))
    (i : ℤ) (j k : Fin m → ℤ)
    (hjump : (w : ℝ) * ‖transversePoint (k - j)‖ ≤
      (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 8) :
    ∃ (τ : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
      rowCube s w t i j ⊆ I ∧ rowCube s w t (i + 1) k ⊆ I' ∧
      IsCubePair M K A s 2 τ I I' ∧ ‖τ - M.t₀‖ ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) ∧
      (∀ u ∈ I, ∀ v ∈ I', (v - u).2 ∈ premiseDomain M s) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  let center : ℤ → (Fin m → ℤ) → EuclideanSpace ℝ (Fin m) := fun q l =>
    WithLp.toLp 2 (fun a => (q : ℝ) * y₀ a + (w : ℝ) * ((l a : ℝ) + 1 / 2))
  let τ := t + ((w : ℝ) / s) • transversePoint (k - j)
  let I := transverseCube (i * s) (center i j) w
  let I' := transverseCube ((i + 1) * s) (center (i + 1) k) w
  have hcent (q : ℤ) (l : Fin m → ℤ) (a : Fin m) :
      center q l a = (q : ℝ) * y₀ a + (w : ℝ) * ((l a : ℝ) + 1 / 2) := rfl
  have hstc (a : Fin m) : (s : ℝ) * t a = (y₀ a : ℝ) := by
    change ((s : ℝ) • t) a = transversePoint y₀ a
    rw [hst]
  have hpower := mean_length_mul_slope_power (δ := M.δ) hsR
  have hcover (q : ℤ) (l : Fin m → ℤ) : rowCube s w t q l ⊆
      transverseCube (q * s) (center q l) w := by
    intro u hu
    refine ⟨hu.1, fun a => ?_⟩
    have hh := rowCube_coord_bounds hw hst hu a
    rw [hcent, abs_le]
    constructor <;> linarith only [hh.1, hh.2]
  have hpair : IsCubePair M K A s 2 τ I I' := by
    refine ⟨i * s, center i j, center (i + 1) k, w, w, rfl, ?_,
      Nat.cast_nonneg _, hwW, Nat.cast_nonneg _, hwW, ?_⟩
    · dsimp only [I']
      congr 1
      ring
    · have he : center (i + 1) k - center i j - (s : ℝ) • τ = 0 := by
        ext a
        simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.zero_apply, hcent,
          τ, PiLp.add_apply, transversePoint_apply, Pi.sub_apply, smul_eq_mul, Int.cast_add,
          Int.cast_one, Int.cast_sub]
        simp only [mul_add]
        rw [hstc]
        field_simp
        ring
      rw [he, norm_zero]
      positivity
  have hτ : ‖τ - M.t₀‖ ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
    have hj : (w : ℝ) / s * ‖transversePoint (k - j)‖ ≤
        (s : ℝ) ^ (M.δ / 100 - 1 / 4) / 8 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hsR]
      rw [← hpower] at hjump
      nlinarith only [hjump]
    have hh := norm_add_le (t - M.t₀) (((w : ℝ) / s) • transversePoint (k - j))
    rw [show t - M.t₀ + ((w : ℝ) / s) • transversePoint (k - j) =
      τ - M.t₀ by dsimp only [τ]; abel] at hh
    rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (w : ℝ) / s)] at hh
    dsimp only [τ]
    have hp := Real.rpow_nonneg hsR.le (M.δ / 100 - 1 / 4)
    linarith only [hh, ht, hj, hp]
  refine ⟨τ, I, I', hcover i j, hcover (i + 1) k, hpair, hτ, ?_⟩
  intro u hu v hv
  let E := transversePoint (v.2 - u.2) - transversePoint y₀ - (w : ℝ) • transversePoint (k - j)
  have hE : ‖E‖ ≤ Real.sqrt m * w := by
    apply norm_le_sqrt_mul_of_coord_le
    intro a
    have hu' := abs_le.mp (hu.2 a)
    have hv' := abs_le.mp (hv.2 a)
    simp only [hcent] at hu' hv'
    simp only [Int.cast_add, Int.cast_one] at hv'
    dsimp only [E]
    simp only [PiLp.sub_apply, PiLp.smul_apply, transversePoint_apply, Pi.sub_apply,
      smul_eq_mul, Int.cast_sub]
    rw [abs_le]
    constructor <;> nlinarith only [hu'.1, hu'.2, hv'.1, hv'.2]
  have hy : ‖transversePoint y₀ - (s : ℝ) • M.t₀‖ ≤ (13 : ℝ) / 16 *
      (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
    rw [← hst, ← smul_sub, norm_smul, Real.norm_of_nonneg hsR.le]
    have hh := mul_le_mul_of_nonneg_left ht hsR.le
    rw [← hpower]
    nlinarith only [hh]
  have heq : transversePoint (v.2 - u.2) = transversePoint y₀ +
      (w : ℝ) • transversePoint (k - j) + E := by dsimp only [E]; abel
  change ‖transversePoint (v.2 - u.2) - (s : ℝ) • M.t₀‖ ≤ _
  rw [heq, show transversePoint y₀ + (w : ℝ) • transversePoint (k - j) + E -
    (s : ℝ) • M.t₀ = (transversePoint y₀ - (s : ℝ) • M.t₀) +
      (w : ℝ) • transversePoint (k - j) + E by abel]
  have hh := (norm_add_le ((transversePoint y₀ - (s : ℝ) • M.t₀) +
      (w : ℝ) • transversePoint (k - j)) E).trans
    (add_le_add (norm_add_le _ _) hE)
  rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)] at hh
  linarith only [hh, hy, hjump, hwidth]

end CurvatureVariance.Paper.Mean
