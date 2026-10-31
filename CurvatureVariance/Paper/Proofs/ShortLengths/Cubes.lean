/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes

/-!
# Pairs of transverse cubes: displacements and powers of `s`

Deterministic facts used by equation `eq:profiledifference` and Proposition `prop:profiles`, kept
apart from the events of Lemma `lem:good` so that the proof of Proposition `prop:profiles` does
not import them:

* `transversePoint_sub`, `point_sub_eq_smul_slopeVec`: the displacement of two vertices at
  longitudinal distance `s` is `s (1, t)`;
* `norm_transverse_sub_le_of_cubes`: the transverse displacement of a pair `u ∈ I`, `v ∈ I'`
  differs from `s t` by at most `√m bW + 2√d`;
* `rpow_le_self_of_one_le`, `rpow_slope_le_one`, `inv_mul_rpow_eq`: powers of `s`.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Paper

variable {m : ℕ}

/-! ### Displacements -/

theorem transversePoint_sub (y y' : Fin m → ℤ) :
    transversePoint (y' - y) = transversePoint y' - transversePoint y := by
  apply WithLp.ofLp_injective
  ext j
  simp [transversePoint]

/-- The displacement of two vertices with `v₁ = u₁ + s`, `s > 0`, as `s (1, t)`. -/
theorem point_sub_eq_smul_slopeVec {u v : Vertex m} {s : ℕ} (hs : 0 < s) (hv : v.1 = u.1 + s) :
    point v - point u =
      (s : ℝ) • slopeVec ((s : ℝ)⁻¹ • transversePoint (v.2 - u.2)) := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · simp only [point, slopeVec, WithLp.ofLp_sub, WithLp.ofLp_smul, Prod.fst_sub, Prod.smul_fst,
      smul_eq_mul, mul_one, hv]
    push_cast
    ring
  · simp only [point, slopeVec, WithLp.ofLp_sub, WithLp.ofLp_smul, Prod.snd_sub, Prod.smul_snd]
    rw [smul_inv_smul₀ hs', transversePoint_sub]

/-! ### Geometry of a pair of transverse cubes -/

/-- A vector of `ℝ^m` with coordinates at most `r` has norm at most `√m r`. -/
theorem norm_le_sqrt_mul_of_abs_le {x : EuclideanSpace ℝ (Fin m)} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ j, |x j| ≤ r) : ‖x‖ ≤ Real.sqrt m * r := by
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ j, ‖x j‖ ^ 2) ≤ Real.sqrt (∑ _j : Fin m, r ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
    _ = Real.sqrt m * r := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hr]

theorem transversePoint_sub_apply (y : Fin m → ℤ) (c : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    (transversePoint y - c) j = (y j : ℝ) - c j := by
  simp [transversePoint]

/-- The transverse displacement of a pair `u ∈ I`, `v ∈ I'` differs from `s t` by at most
`√m bW + 2√d`. -/
theorem norm_transverse_sub_le_of_cubes {p : ℤ} {s : ℕ} {c c' t : EuclideanSpace ℝ (Fin m)}
    {a a' w : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (haw : a ≤ w) (haw' : a' ≤ w)
    (hcc : ‖c' - c - (s : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1)) {u v : Vertex m}
    (hu : u ∈ transverseCube p c a) (hv : v ∈ transverseCube (p + s) c' a') :
    ‖transversePoint (v.2 - u.2) - (s : ℝ) • t‖ ≤
      Real.sqrt m * w + 2 * Real.sqrt ((m : ℝ) + 1) := by
  have h1 : ‖transversePoint v.2 - c'‖ ≤ Real.sqrt m * (a' / 2) :=
    norm_le_sqrt_mul_of_abs_le (by positivity) fun j => by
      rw [transversePoint_sub_apply]; exact hv.2 j
  have h2 : ‖transversePoint u.2 - c‖ ≤ Real.sqrt m * (a / 2) :=
    norm_le_sqrt_mul_of_abs_le (by positivity) fun j => by
      rw [transversePoint_sub_apply]; exact hu.2 j
  have heq : transversePoint (v.2 - u.2) - (s : ℝ) • t =
      (transversePoint v.2 - c') + (c' - c - (s : ℝ) • t) - (transversePoint u.2 - c) := by
    rw [transversePoint_sub]; abel
  rw [heq]
  have h3 := norm_sub_le ((transversePoint v.2 - c') + (c' - c - (s : ℝ) • t))
    (transversePoint u.2 - c)
  have h4 := norm_add_le (transversePoint v.2 - c') (c' - c - (s : ℝ) • t)
  have hm := Real.sqrt_nonneg (m : ℝ)
  have h5 : Real.sqrt m * (a' / 2) + Real.sqrt m * (a / 2) ≤ Real.sqrt m * w := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hm
  linarith

/-! ### Powers of `s` -/

theorem rpow_le_self_of_one_le {s δ : ℝ} (hs : 1 ≤ s) (hδ1 : δ ≤ 1) :
    s ^ ((3 : ℝ) / 4 + δ / 100) ≤ s := by
  calc s ^ ((3 : ℝ) / 4 + δ / 100) ≤ s ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hs (by linarith)
    _ = s := Real.rpow_one s

theorem rpow_slope_le_one {s δ : ℝ} (hs : 1 ≤ s) (hδ1 : δ ≤ 1) :
    s ^ (δ / 100 - 1 / 4) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)

theorem inv_mul_rpow_eq {s δ : ℝ} (hs : 0 < s) :
    s⁻¹ * s ^ ((3 : ℝ) / 4 + δ / 100) = s ^ (δ / 100 - 1 / 4) := by
  rw [show (3 : ℝ) / 4 + δ / 100 = (δ / 100 - 1 / 4) + 1 by ring, Real.rpow_add hs,
    Real.rpow_one]
  field_simp

end CurvatureVariance.Paper.Proofs.ShortLengths
