/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.Basic
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# Deterministic geometry of equation `eq:rowenergy`: cubes, entries, supporting hyperplanes

The deterministic part of the proof of equation `eq:rowenergy` (the proof of Lemma
`lem:rowenergy`):

* every norm on `ℝ^d` has a subgradient at every point (`Proofs.Geometry.exists_isSubgradient`,
  Hahn–Banach), so a slope `t` has some `P_t` (the text before Lemma `lem:support`).
* `mem_rowCube_iff`, `rowCube_eq_transverseCube`: the cube `I_i(j)` of the text before Lemma
  `lem:rowenergy` is the transverse cube with corner `⌊ist⌋ + wj` and side `w − 1` (its lattice
  points).
* `entry_geometry`: for `u ∈ I_i(j)`, `v ∈ I_{i+1}(k)`, `v − u = (s, s t + w (k − j) + e)` with
  `|e| ≤ √m (w + 1)`.
* `support_bounds`: equation `eq:support` rescaled to a vector `(σ, y)`.
* `rpow_128_le`, `mul_norm_rpow_le_Q`: the numerology `128^{δ/100−1/4} ≤ 8/25` and
  `s |τ|^{2+δ} ≤ 8 Q_s` for `|τ| ≤ 2 s^{δ/100−1/4}` (applied to `τ = t − t₀`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Moments.ExpArray

open CurvatureVariance.Paper

variable {m : ℕ}

/-! ## Euclidean coordinates -/

/-- A coordinate is at most the Euclidean norm. -/
theorem abs_apply_le_norm (y : EuclideanSpace ℝ (Fin m)) (j : Fin m) : |y j| ≤ ‖y‖ := by
  have := PiLp.norm_apply_le y j
  rwa [Real.norm_eq_abs] at this

/-- The squared norm of a lattice vector is the sum of the squares of its coordinates. -/
theorem norm_transversePoint_sq (z : Fin m → ℤ) :
    ‖transversePoint z‖ ^ 2 = ∑ j, ((z j : ℤ) : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

/-! ## The cubes `I_i(j)` of the text before Lemma `lem:rowenergy` -/

/-- Membership in `I_i(j)`: `x₁ = is` and `w j ≤ x₂ − ⌊ist⌋ < w (j + 1)` coordinatewise. -/
theorem mem_rowCube_iff {s w : ℕ} (hw : 0 < w) {t : EuclideanSpace ℝ (Fin m)} {i : ℤ}
    {j : Fin m → ℤ} {x : Vertex m} :
    x ∈ rowCube s w t i j ↔ x.1 = i * s ∧ ∀ k, (j k : ℝ) * w ≤ (x.2 k : ℝ) - ⌊(i : ℝ) * s * t k⌋ ∧
      (x.2 k : ℝ) - ⌊(i : ℝ) * s * t k⌋ < ((j k : ℝ) + 1) * w := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  simp only [rowCube, rowIndex, Set.mem_ofPred_eq, funext_iff, Int.floor_eq_iff,
    le_div_iff₀ hw', div_lt_iff₀ hw']

/-- The centre of the transverse cube `I_i(j)`: `⌊ist⌋ + wj + (w − 1)/2`. -/
noncomputable def rowCentre (s w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j : Fin m → ℤ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun k => (⌊(i : ℝ) * s * t k⌋ : ℝ) + w * j k + ((w : ℝ) - 1) / 2

/-- `I_i(j)` is the transverse cube of side `w − 1` centred at `rowCentre`. -/
theorem rowCube_eq_transverseCube {s w : ℕ} (hw : 0 < w) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ)
    (j : Fin m → ℤ) :
    rowCube s w t i j = transverseCube (i * s) (rowCentre s w t i j) ((w : ℝ) - 1) := by
  ext x
  rw [mem_rowCube_iff hw]
  simp only [transverseCube, Set.mem_ofPred_eq, rowCentre, PiLp.toLp_apply]
  refine and_congr_right fun _ => forall_congr' fun k => ?_
  set n : ℤ := x.2 k - ⌊(i : ℝ) * s * t k⌋ - w * j k with hn
  have hn' : (n : ℝ) = (x.2 k : ℝ) - ⌊(i : ℝ) * s * t k⌋ - w * j k := by
    rw [hn]; push_cast; ring
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (n : ℝ) < w := by rw [hn']; linarith
    have h4 : n < (w : ℤ) := by exact_mod_cast h3
    have h5 : n ≤ (w : ℤ) - 1 := by omega
    have h6 : (n : ℝ) ≤ (w : ℝ) - 1 := by exact_mod_cast h5
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- The geometry of an entry: for `u ∈ I_i(j)` and `v ∈ I_{i+1}(k)`,
`|v₂ − u₂ − s t − w (k − j)| ≤ √m (w + 1)`. -/
theorem entry_geometry {s w : ℕ} (hw : 0 < w) {t : EuclideanSpace ℝ (Fin m)} {i : ℤ}
    {j k : Fin m → ℤ} {u v : Vertex m} (hu : u ∈ rowCube s w t i j)
    (hv : v ∈ rowCube s w t (i + 1) k) :
    ‖transversePoint (v.2 - u.2) - (s : ℝ) • t - (w : ℝ) • transversePoint (k - j)‖ ≤
      Real.sqrt m * ((w : ℝ) + 1) := by
  rw [mem_rowCube_iff hw] at hu hv
  apply Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (by positivity)
  intro c
  obtain ⟨a1, a2⟩ := hu.2 c
  obtain ⟨b1, b2⟩ := hv.2 c
  have f1 := Int.floor_le ((i : ℝ) * s * t c)
  have f2 := Int.lt_floor_add_one ((i : ℝ) * s * t c)
  have f3 := Int.floor_le (((i + 1 : ℤ) : ℝ) * s * t c)
  have f4 := Int.lt_floor_add_one (((i + 1 : ℤ) : ℝ) * s * t c)
  have e : ((i + 1 : ℤ) : ℝ) * s * t c = (i : ℝ) * s * t c + s * t c := by push_cast; ring
  simp only [PiLp.sub_apply, PiLp.smul_apply, Infra.FPP.transversePoint_apply, Pi.sub_apply,
    Int.cast_sub, smul_eq_mul]
  rw [abs_le]
  constructor <;> nlinarith

/-- The point difference of two vertices on hyperplanes at distance `s`. -/
theorem point_sub_eq {s : ℕ} {u v : Vertex m} (h : v.1 = u.1 + s) :
    point v - point u = WithLp.toLp 2 ((s : ℝ), transversePoint (v.2 - u.2)) := by
  rw [← Infra.FPP.point_sub]
  unfold point
  congr 2
  simp only [Prod.fst_sub, h, add_sub_cancel_left, Int.cast_natCast]

/-! ## Supporting hyperplanes, rescaled -/

/-- **Equation `eq:support` rescaled**: for a subgradient `P` of `μ` at `(1, t)`, `σ > 0` and `y`
with `|t − t₀| ≤ r₁` and `|y/σ − t| ≤ r₁`:
`c|y − σ t|²/σ − Cσ|t − t₀|^{2+δ} ≤ μ(σ, y) − P·(σ, y) ≤ C|y − σ t|²/σ + Cσ|t − t₀|^{2+δ}`. -/
theorem support_bounds {μ : PtNorm m} {t₀ : EuclideanSpace ℝ (Fin m)} {c₀ C₀ r₁ δ : ℝ}
    (hsupp : ∀ t h : EuclideanSpace ℝ (Fin m), ‖t - t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient μ (slopeVec t) p →
        c₀ * ‖h‖ ^ 2 - C₀ * ‖t - t₀‖ ^ (2 + δ) ≤
            μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            C₀ * ‖h‖ ^ 2 + C₀ * ‖t - t₀‖ ^ (2 + δ))
    {t : EuclideanSpace ℝ (Fin m)} {P : Pt m} (hP : IsSubgradient μ (slopeVec t) P) {σ : ℝ}
    (hσ : 0 < σ) (y : EuclideanSpace ℝ (Fin m)) (ht : ‖t - t₀‖ ≤ r₁)
    (hy : ‖σ⁻¹ • y - t‖ ≤ r₁) :
    c₀ * ‖y - σ • t‖ ^ 2 / σ - C₀ * σ * ‖t - t₀‖ ^ (2 + δ) ≤
        μ.1 (WithLp.toLp 2 (σ, y)) - inner ℝ P (WithLp.toLp 2 (σ, y)) ∧
      μ.1 (WithLp.toLp 2 (σ, y)) - inner ℝ P (WithLp.toLp 2 (σ, y)) ≤
        C₀ * ‖y - σ • t‖ ^ 2 / σ + C₀ * σ * ‖t - t₀‖ ^ (2 + δ) := by
  set h := σ⁻¹ • y - t with hh
  have hth : t + h = σ⁻¹ • y := by rw [hh]; abel
  have hpt : (WithLp.toLp 2 (σ, y) : Pt m) = σ • slopeVec (t + h) := by
    rw [hth]
    unfold slopeVec
    rw [← WithLp.toLp_smul, Prod.smul_mk, smul_eq_mul, mul_one, smul_inv_smul₀ hσ.ne']
  have hnorm : ‖h‖ ^ 2 * σ = ‖y - σ • t‖ ^ 2 / σ := by
    have : h = σ⁻¹ • (y - σ • t) := by
      rw [hh, smul_sub, inv_smul_smul₀ hσ.ne']
    rw [this, norm_smul, norm_inv, Real.norm_of_nonneg hσ.le]
    field_simp
  have hkey : μ.1 (WithLp.toLp 2 (σ, y)) - inner ℝ P (WithLp.toLp 2 (σ, y)) =
      σ * (μ.1 (slopeVec (t + h)) - inner ℝ P (slopeVec (t + h))) := by
    rw [hpt, map_smul_eq_mul, inner_smul_right, Real.norm_of_nonneg hσ.le]
    ring
  obtain ⟨hl, hu⟩ := hsupp t h ht hy P hP
  have e1 : c₀ * ‖y - σ • t‖ ^ 2 / σ = σ * (c₀ * ‖h‖ ^ 2) := by
    rw [mul_div_assoc, ← hnorm]; ring
  have e2 : C₀ * ‖y - σ • t‖ ^ 2 / σ = σ * (C₀ * ‖h‖ ^ 2) := by
    rw [mul_div_assoc, ← hnorm]; ring
  rw [hkey, e1, e2]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl hσ.le]
  · nlinarith [mul_le_mul_of_nonneg_left hu hσ.le]

/-! ## Numerology -/

/-- `128^{δ/100 − 1/4} ≤ 8/25` for `δ ≤ 1`. -/
theorem rpow_128_le {δ : ℝ} (hδ1 : δ ≤ 1) : (128 : ℝ) ^ (δ / 100 - 1 / 4) ≤ 8 / 25 := by
  have he : δ / 100 - 1 / 4 ≤ -(6 / 25) := by linarith
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) he).trans ?_
  set x := (128 : ℝ) ^ (-(6 / 25 : ℝ)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hpow : x ^ (25 : ℕ) = 1 / 128 ^ 6 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h25 : x ^ (25 : ℕ) ≤ (8 / 25 : ℝ) ^ (25 : ℕ) := by
    rw [hpow]; norm_num
  exact (pow_le_pow_iff_left₀ hx0 (by norm_num) (by norm_num)).mp h25

/-- The exponent comparison behind `s|t − t₀|^{2+δ} = o(Q_s)`:
`1 + (δ/100 − 1/4)(2 + δ) ≤ 1/2 − δ/K` for `0 < δ ≤ 1` and `K ≥ 10⁴`. -/
theorem exponent_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {K : ℝ} (hK : 10000 ≤ K) :
    1 + (δ / 100 - 1 / 4) * (2 + δ) ≤ 1 / 2 - δ / K := by
  have hδK : δ / K ≤ δ / 10000 := div_le_div_of_nonneg_left hδ.le (by norm_num) hK
  nlinarith [mul_le_mul_of_nonneg_left hδ1 hδ.le]

/-- `s |τ|^{2+δ} ≤ 8 Q_s` when `|τ| ≤ 2 s^{δ/100−1/4}`, `s ≥ 1`, `A ≥ 1`; it is applied to the
slope deviation `τ = t − t₀`. -/
theorem mul_norm_rpow_le_Q (M : Model m) (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {s : ℝ} (hs : 1 ≤ s) {τ : EuclideanSpace ℝ (Fin m)}
    (hτ : ‖τ‖ ≤ 2 * s ^ (M.δ / 100 - 1 / 4)) :
    s * ‖τ‖ ^ (2 + M.δ) ≤ 8 * Q M K A s := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hK' : (10000 : ℝ) ≤ K := by exact_mod_cast hK
  have hs0 : 0 < s := by linarith
  have h1 : ‖τ‖ ^ (2 + M.δ) ≤ (2 * s ^ (M.δ / 100 - 1 / 4)) ^ (2 + M.δ) :=
    Real.rpow_le_rpow (norm_nonneg _) hτ (by linarith)
  have h2 : (2 * s ^ (M.δ / 100 - 1 / 4)) ^ (2 + M.δ) =
      (2 : ℝ) ^ (2 + M.δ) * s ^ ((M.δ / 100 - 1 / 4) * (2 + M.δ)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hs0.le]
  have h3 : (2 : ℝ) ^ (2 + M.δ) ≤ 8 := by
    calc (2 : ℝ) ^ (2 + M.δ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := by norm_num
  have h4 : s * s ^ ((M.δ / 100 - 1 / 4) * (2 + M.δ)) ≤ s ^ ((1 : ℝ) / 2 - M.δ / K) := by
    rw [← Real.rpow_one_add' hs0.le (by
      have := exponent_le hδ hδ1 hK'
      nlinarith)]
    exact Real.rpow_le_rpow_of_exponent_le hs (exponent_le hδ hδ1 hK')
  have h5 : s ^ ((1 : ℝ) / 2 - M.δ / K) ≤ Q M K A s := by
    unfold Q
    exact le_mul_of_one_le_left (by positivity) hA
  have hpos : 0 ≤ s ^ ((M.δ / 100 - 1 / 4) * (2 + M.δ)) := by positivity
  calc s * ‖τ‖ ^ (2 + M.δ) ≤ s * ((2 : ℝ) ^ (2 + M.δ) * s ^ ((M.δ / 100 - 1 / 4) * (2 + M.δ))) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hs0.le
    _ ≤ s * (8 * s ^ ((M.δ / 100 - 1 / 4) * (2 + M.δ))) := by gcongr
    _ = 8 * (s * s ^ ((M.δ / 100 - 1 / 4) * (2 + M.δ))) := by ring
    _ ≤ 8 * Q M K A s := by linarith

end CurvatureVariance.Paper.Moments.ExpArray
