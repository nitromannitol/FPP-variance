/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry
public import CurvatureVariance.Paper.Proofs.Moments.ExpArrayMoments
import CurvatureVariance.Infra.Arrays.Estimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes
import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet

/-!
# The entries of equation `eq:rowenergy`: one slab at a time

For the proof of equation `eq:rowenergy` (the proof of Lemma `lem:rowenergy`), at slab width `s`
with `w = ⌈W_s⌉`:

* `Scale`: the standing facts at the scale `s` for `N` large (width margin, the first bound of
  equation `eq:scales`, `s` large, the slope bound `|t − t₀| ≤ 2(Ms)^{δ/100−1/4}`, `M ≥ 128`), and
  their consequences: `|t − t₀| ≤ (16/25)s^{δ/100−1/4}` (from `2 · 128^{δ/100−1/4} ≤ 16/25`),
  `w² ≥ s Q_s`, `(w + 1)² ≤ 9 s Q_s`, `√m (w + 2) ≤ s^{3/4+δ/100}/16`.
* `entry_lower`: `μ(v − u) − P_t·(v − u) ≥ (c/2) Q_s |k − j|² − C Q_s` for consecutive points of an
  admissible tuple in `I_i(j) × I_{i+1}(k)` (equation `eq:support` in the form `SupportAt`,
  `w² ≥ s Q_s`, `s|t − t₀|^{2+δ} ≤ 8 Q_s`);
  `entry_upper`: `μ(v − u) − P_t·(v − u) ≤ C Q_s` for the floor tuple.
* `rowE`, `lintegral_rowE_le`: the slab variable
  `sup_{I_i(j)×I_{i+1}(k)} e^{(μ(v−u) − D_i(u,v))/θ}`, `θ = C(1) Q_s`, has mean at most two, by
  Proposition `prop:profiles` for the pair `I_i(j), I_{i+1}(k)` with the pair slope
  (`2 · 128^{δ/100−1/4} + 1/8 < 4/5`, for the deviation of the pair slope from `t₀`).
* `isOs_slabStep`: `D_i(u, v) − μ(v − u) ≤ O₁(C(1) Q_s)` for the singleton cubes of the floor tuple.
* `sum_gaussian_le`: `∑_{z ∈ B} 2 e^{−c|z|²} ≤ 2 (4/√min(c,1))^m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Moments.ExpArray

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

/-! ## The scale -/

/-- The facts at slab width `s` used in the proof of equation `eq:rowenergy`, for `N` large. -/
structure Scale (M : Model m) (K : ℕ) (A : ℝ) (s Ms : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (r₁ : ℝ) : Prop where
  hK : 10 ^ 4 ≤ K
  hA : 1 ≤ A
  two_le : 2 ≤ s
  hMs : 128 ≤ Ms
  ht : ‖t - M.t₀‖ ≤ 2 * ((Ms * s : ℕ) : ℝ) ^ (M.δ / 100 - 1 / 4)
  hW : W M K A s ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / (32 * (Real.sqrt m + 1))
  hsa : 96 * Real.sqrt m ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)
  hr : (s : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ r₁

namespace Scale

variable {M : Model m} {K : ℕ} {A : ℝ} {s Ms : ℕ} {t : EuclideanSpace ℝ (Fin m)} {r₁ : ℝ}

theorem one_le_s (h : Scale M K A s Ms t r₁) : (1 : ℝ) ≤ s := by
  have := h.two_le
  exact_mod_cast (by omega : 1 ≤ s)

theorem s_pos (h : Scale M K A s Ms t r₁) : (0 : ℝ) < s := lt_of_lt_of_le one_pos h.one_le_s

/-- `s^{3/4+δ/100} = s · s^{δ/100−1/4}`. -/
theorem rpow_a (h : Scale M K A s Ms t r₁) :
    (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) = s * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  rw [show (3 : ℝ) / 4 + M.δ / 100 = 1 + (M.δ / 100 - 1 / 4) by ring,
    Real.rpow_add h.s_pos, Real.rpow_one]

/-- `|t − t₀| ≤ (16/25) s^{δ/100−1/4}`, from `M ≥ 128`. -/
theorem norm_t_le (hM : M.Standing) (h : Scale M K A s Ms t r₁) :
    ‖t - M.t₀‖ ≤ 16 / 25 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  have hs := h.s_pos
  have he : M.δ / 100 - 1 / 4 ≤ 0 := by linarith [hM.delta_le_one]
  have hMs : (128 : ℝ) ≤ Ms := by exact_mod_cast h.hMs
  have h1 : ((Ms * s : ℕ) : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ ((128 : ℝ) * s) ^ (M.δ / 100 - 1 / 4) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; nlinarith) he
  rw [Real.mul_rpow (by norm_num) hs.le] at h1
  have h2 := rpow_128_le hM.delta_le_one
  have h3 : 0 ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by positivity
  calc ‖t - M.t₀‖ ≤ 2 * ((Ms * s : ℕ) : ℝ) ^ (M.δ / 100 - 1 / 4) := h.ht
    _ ≤ 2 * ((128 : ℝ) ^ (M.δ / 100 - 1 / 4) * (s : ℝ) ^ (M.δ / 100 - 1 / 4)) := by gcongr
    _ ≤ 2 * (8 / 25 * (s : ℝ) ^ (M.δ / 100 - 1 / 4)) := by gcongr
    _ = 16 / 25 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by ring

/-- `|t − t₀| ≤ 2 s^{δ/100−1/4}`. -/
theorem norm_t_le_two (hM : M.Standing) (h : Scale M K A s Ms t r₁) :
    ‖t - M.t₀‖ ≤ 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  have h1 := h.norm_t_le hM
  have h2 : 0 ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by have := h.s_pos; positivity
  linarith

theorem one_le_Q (hM : M.Standing) (h : Scale M K A s Ms t r₁) : 1 ≤ Q M K A s :=
  Proofs.ShortLengths.one_le_Q hM h.hK h.hA h.one_le_s

theorem W_sq (hM : M.Standing) (h : Scale M K A s Ms t r₁) :
    W M K A s ^ 2 = s * Q M K A s := by
  have h1 := h.one_le_Q hM
  have h2 := h.s_pos
  exact Real.sq_sqrt (mul_nonneg h2.le (by linarith))

theorem one_le_W (hM : M.Standing) (h : Scale M K A s Ms t r₁) : 1 ≤ W M K A s := by
  have hQ := h.one_le_Q hM
  have hs := h.one_le_s
  unfold W
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (s * Q M K A s) := Real.sqrt_le_sqrt (by nlinarith)

theorem W_le_w (_h : Scale M K A s Ms t r₁) : W M K A s ≤ wInt M K A s := Nat.le_ceil _

theorem w_lt (hM : M.Standing) (h : Scale M K A s Ms t r₁) :
    (wInt M K A s : ℝ) < W M K A s + 1 :=
  Nat.ceil_lt_add_one (by linarith [h.one_le_W hM])

theorem w_pos (hM : M.Standing) (h : Scale M K A s Ms t r₁) : 0 < wInt M K A s :=
  Nat.ceil_pos.mpr (by linarith [h.one_le_W hM])

/-- `w² ≥ W_s² = s Q_s`. -/
theorem sQ_le_w_sq (hM : M.Standing) (h : Scale M K A s Ms t r₁) :
    s * Q M K A s ≤ (wInt M K A s : ℝ) ^ 2 := by
  rw [← h.W_sq hM]
  have := h.one_le_W hM
  exact pow_le_pow_left₀ (by linarith) h.W_le_w 2

/-- `(w + 1)² ≤ 9 s Q_s`, since `w + 1 < W_s + 2 ≤ 3 W_s`. -/
theorem w_succ_sq_le (hM : M.Standing) (h : Scale M K A s Ms t r₁) :
    ((wInt M K A s : ℝ) + 1) ^ 2 ≤ 9 * (s * Q M K A s) := by
  rw [← h.W_sq hM]
  have h1 := h.one_le_W hM
  have h2 := h.w_lt hM
  have h3 : (0 : ℝ) ≤ wInt M K A s := Nat.cast_nonneg _
  nlinarith

/-- `√m (w + 2) ≤ s^{3/4+δ/100}/16`. -/
theorem margin (hM : M.Standing) (h : Scale M K A s Ms t r₁) :
    Real.sqrt m * ((wInt M K A s : ℝ) + 2) ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 := by
  have h1 := h.w_lt hM
  have h2 := h.hW
  have h3 := h.hsa
  have hm : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  set a := (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)
  have ha : 0 ≤ a := by positivity
  have h4 : Real.sqrt m * W M K A s ≤ a / 32 := by
    calc Real.sqrt m * W M K A s ≤ Real.sqrt m * (a / (32 * (Real.sqrt m + 1))) :=
          mul_le_mul_of_nonneg_left h2 hm
      _ = Real.sqrt m / (Real.sqrt m + 1) * (a / 32) := by field_simp
      _ ≤ 1 * (a / 32) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = a / 32 := one_mul _
  nlinarith

/-- For `|y − s t| ≤ s^{3/4+δ/100}/16`: `|t − t₀| ≤ r₁` and `|y/s − t| ≤ r₁`. -/
theorem norm_le_r₁ (hM : M.Standing) (h : Scale M K A s Ms t r₁) {y : EuclideanSpace ℝ (Fin m)}
    (hy : ‖y - (s : ℝ) • t‖ ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16) :
    ‖t - M.t₀‖ ≤ r₁ ∧ ‖(s : ℝ)⁻¹ • y - t‖ ≤ r₁ := by
  have hs := h.s_pos
  have hte := h.norm_t_le hM
  have he : 0 ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by positivity
  have hr := h.hr
  refine ⟨by linarith, ?_⟩
  have heq : (s : ℝ)⁻¹ • y - t = (s : ℝ)⁻¹ • (y - (s : ℝ) • t) := by
    rw [smul_sub, inv_smul_smul₀ hs.ne']
  rw [heq]
  have h1 : ‖(s : ℝ)⁻¹ • (y - (s : ℝ) • t)‖ ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) / 16 := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_le_iff₀ hs]
    calc ‖y - (s : ℝ) • t‖ ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 := hy
      _ = s * ((s : ℝ) ^ (M.δ / 100 - 1 / 4) / 16) := by rw [h.rpow_a]; ring
  linarith

end Scale

/-! ## The floor tuple -/

/-- The lattice point `⌊ist⌋` (coordinatewise) of the hyperplane `{x₁ = is}`. -/
noncomputable def floorPt (s : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) : Fin m → ℤ :=
  fun k => ⌊(i : ℝ) * s * t k⌋

/-- `|⌊(i+1)st⌋ − ⌊ist⌋ − st| ≤ √m`. -/
theorem norm_floorPt_sub_le (s : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) :
    ‖transversePoint (floorPt s t (i + 1) - floorPt s t i) - (s : ℝ) • t‖ ≤ Real.sqrt m := by
  rw [← mul_one (Real.sqrt m)]
  apply Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le zero_le_one
  intro c
  have f1 := Int.floor_le ((i : ℝ) * s * t c)
  have f2 := Int.lt_floor_add_one ((i : ℝ) * s * t c)
  have f3 := Int.floor_le (((i + 1 : ℤ) : ℝ) * s * t c)
  have f4 := Int.lt_floor_add_one (((i + 1 : ℤ) : ℝ) * s * t c)
  have e : ((i + 1 : ℤ) : ℝ) * s * t c = (i : ℝ) * s * t c + s * t c := by push_cast; ring
  simp only [floorPt, PiLp.sub_apply, PiLp.smul_apply, Infra.FPP.transversePoint_apply,
    Pi.sub_apply, Int.cast_sub, smul_eq_mul]
  rw [abs_le]
  constructor <;> linarith

/-- The centres of `I_{i+1}(k)` and `I_i(j)` differ by `⌊(i+1)st⌋ − ⌊ist⌋ + w(k − j)`. -/
theorem rowCentre_sub (s w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ) (j k : Fin m → ℤ) :
    rowCentre s w t (i + 1) k - rowCentre s w t i j =
      transversePoint (floorPt s t (i + 1) - floorPt s t i) +
        (w : ℝ) • transversePoint (k - j) := by
  ext c
  simp only [rowCentre, floorPt, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    Infra.FPP.transversePoint_apply, Pi.sub_apply, Int.cast_sub, smul_eq_mul]
  ring

/-! ## Deterministic bounds for one slab -/

/-- The first half of equation `eq:support` (the first conjunct of `Contracts.SupportStatement`),
with constants `c₀, C₀, r₁`: at slopes `|t − t₀| ≤ r₁`, for `|h| ≤ r₁` and every subgradient `p`
at `(1, t)`, `c₀|h|² − C₀|t − t₀|^{2+δ} ≤ μ(1, t + h) − p·(1, t + h) ≤ C₀|h|² + C₀|t − t₀|^{2+δ}`.
-/
def SupportAt (M : Model m) (c₀ C₀ r₁ : ℝ) : Prop :=
  ∀ t h : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
    ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
      c₀ * ‖h‖ ^ 2 - C₀ * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
        M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
          C₀ * ‖h‖ ^ 2 + C₀ * ‖t - M.t₀‖ ^ (2 + M.δ)

section Entries

variable {M : Model m} {K : ℕ} {A : ℝ} {s Ms : ℕ} {t : EuclideanSpace ℝ (Fin m)} {r₁ : ℝ}
  {c₀ C₀ : ℝ}

/-- **The lower bound of an entry** (equation `eq:rowenergy`): for consecutive points `u ∈ I_i(j)`,
`v ∈ I_{i+1}(k)` of an admissible tuple, `μ(v − u) − P_t·(v − u) ≥ (c/2) Q_s|k − j|² − C Q_s`. -/
theorem entry_lower (hM : M.Standing) (h : Scale M K A s Ms t r₁) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hsupp : SupportAt M c₀ C₀ r₁)
    {P : Pt m} (hP : IsSubgradient M.μ (slopeVec t) P) {i : ℤ} {j k : Fin m → ℤ}
    {u v : Vertex m} (hu : u ∈ rowCube s (wInt M K A s) t i j)
    (hv : v ∈ rowCube s (wInt M K A s) t (i + 1) k)
    (hadm : ‖transversePoint (v.2 - u.2) - (s : ℝ) • t‖ ≤
      (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16) :
    c₀ / 2 * Q M K A s * ‖transversePoint (k - j)‖ ^ 2 - (9 * c₀ * m + 8 * C₀) * Q M K A s ≤
      M.μ.1 (point v - point u) - inner ℝ P (point v - point u) := by
  have hs := h.s_pos
  have hv1 : v.1 = u.1 + s := by rw [hv.1, hu.1]; ring
  rw [point_sub_eq hv1]
  set w := wInt M K A s with hw
  set Qs := Q M K A s with hQs
  set y := transversePoint (v.2 - u.2) with hy
  obtain ⟨hrt, hry⟩ := h.norm_le_r₁ hM hadm
  obtain ⟨hl, -⟩ := support_bounds hsupp hP hs y hrt hry
  have hg := entry_geometry (h.w_pos hM) hu hv
  rw [← hy] at hg
  set κ := transversePoint (k - j) with hκ
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  set b := ‖y - (s : ℝ) • t‖ with hb
  set e := Real.sqrt m * ((w : ℝ) + 1) with he
  have hb0 : 0 ≤ b := norm_nonneg _
  have he0 : 0 ≤ e := by positivity
  have hwk : (w : ℝ) * ‖κ‖ ≤ b + e := by
    have h1 := norm_sub_norm_le ((w : ℝ) • κ) (y - (s : ℝ) • t)
    rw [norm_smul, Real.norm_of_nonneg hw0] at h1
    have h2 : ‖(w : ℝ) • κ - (y - (s : ℝ) • t)‖ = ‖y - (s : ℝ) • t - (w : ℝ) • κ‖ := by
      rw [← norm_neg]; congr 1; abel
    linarith
  have hwk0 : 0 ≤ (w : ℝ) * ‖κ‖ := by positivity
  have hsq : e ^ 2 = m * ((w : ℝ) + 1) ^ 2 := by
    rw [he, mul_pow, Real.sq_sqrt hm0]
  have hz : (w : ℝ) ^ 2 * ‖κ‖ ^ 2 / 2 - m * ((w : ℝ) + 1) ^ 2 ≤ b ^ 2 := by
    have h1 : ((w : ℝ) * ‖κ‖) ^ 2 ≤ (b + e) ^ 2 := pow_le_pow_left₀ hwk0 hwk 2
    linarith only [h1, sq_nonneg (b - e), hsq]
  have hw2 := h.sQ_le_w_sq hM
  have hw1 := h.w_succ_sq_le hM
  have hk0 : 0 ≤ ‖κ‖ ^ 2 := sq_nonneg _
  have hQ := h.one_le_Q hM
  have hA1 : (s : ℝ) * Qs * ‖κ‖ ^ 2 ≤ (w : ℝ) ^ 2 * ‖κ‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hw2 hk0
  have hA2 : (m : ℝ) * ((w : ℝ) + 1) ^ 2 ≤ m * (9 * (s * Qs)) :=
    mul_le_mul_of_nonneg_left hw1 hm0
  have hkey : c₀ / 2 * Qs * ‖κ‖ ^ 2 - 9 * c₀ * m * Qs ≤ c₀ * b ^ 2 / s := by
    rw [le_div_iff₀ hs]
    have h3 : c₀ * ((s : ℝ) * Qs * ‖κ‖ ^ 2 / 2 - m * (9 * (s * Qs))) ≤ c₀ * b ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hc₀.le
      linarith only [hA1, hA2, hz]
    linarith only [h3]
  have hcurv : C₀ * s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 8 * C₀ * Qs := by
    have h4 := mul_le_mul_of_nonneg_left
      (mul_norm_rpow_le_Q M hM h.hK h.hA h.one_le_s (h.norm_t_le_two hM)) hC₀.le
    linarith only [h4]
  linarith

/-- **The upper bound of an entry**: for `v₁ = u₁ + s` and `|v₂ − u₂ − s t| ≤ √m`,
`μ(v − u) − P_t·(v − u) ≤ (C m + 8C) Q_s`. -/
theorem entry_upper (hM : M.Standing) (h : Scale M K A s Ms t r₁) (hC₀ : 0 < C₀)
    (hsupp : SupportAt M c₀ C₀ r₁)
    {P : Pt m} (hP : IsSubgradient M.μ (slopeVec t) P) {u v : Vertex m} (hv1 : v.1 = u.1 + s)
    (hadm : ‖transversePoint (v.2 - u.2) - (s : ℝ) • t‖ ≤ Real.sqrt m) :
    M.μ.1 (point v - point u) - inner ℝ P (point v - point u) ≤
      (C₀ * m + 8 * C₀) * Q M K A s := by
  have hs := h.s_pos
  have hs1 := h.one_le_s
  rw [point_sub_eq hv1]
  set y := transversePoint (v.2 - u.2) with hy
  have hadm' : ‖y - (s : ℝ) • t‖ ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 := by
    have := h.hsa; have := Real.sqrt_nonneg m; linarith
  obtain ⟨hrt, hry⟩ := h.norm_le_r₁ hM hadm'
  obtain ⟨-, hu⟩ := support_bounds hsupp hP hs y hrt hry
  have hQ := h.one_le_Q hM
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hb : ‖y - (s : ℝ) • t‖ ^ 2 ≤ m := by
    calc ‖y - (s : ℝ) • t‖ ^ 2 ≤ Real.sqrt m ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hadm 2
      _ = m := Real.sq_sqrt hm0
  have h1 : C₀ * ‖y - (s : ℝ) • t‖ ^ 2 / s ≤ C₀ * m * Q M K A s := by
    rw [div_le_iff₀ hs]
    have h2 : C₀ * ‖y - (s : ℝ) • t‖ ^ 2 ≤ C₀ * m := mul_le_mul_of_nonneg_left hb hC₀.le
    have h3 : C₀ * m * 1 ≤ C₀ * m * (Q M K A s * s) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ hs1) (by positivity)
    linarith only [h2, h3]
  have hcurv : C₀ * s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 8 * C₀ * Q M K A s := by
    have h4 := mul_le_mul_of_nonneg_left
      (mul_norm_rpow_le_Q M hM h.hK h.hA h.one_le_s (h.norm_t_le_two hM)) hC₀.le
    linarith only [h4]
  linarith

end Entries

/-! ## The slab variables and Proposition `prop:profiles` -/

/-- The slab variable of equation `eq:rowenergy`:
`sup_{u ∈ I_i(j), v ∈ I_{i+1}(k)} e^{(μ(v − u) − D_i(u, v))/θ}`, with `D_i` the slab passage time of
the slab `[is, (i+1)s]`. -/
noncomputable def rowE (M : Model m) (s w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (θ : ℝ) (i : ℕ)
    (j k : Fin m → ℤ) (ω : Config m) : ℝ≥0∞ :=
  ⨆ (u : Vertex m) (_ : u ∈ rowCube s w t i j) (v : Vertex m)
    (_ : v ∈ rowCube s w t ((i : ℤ) + 1) k),
    ENNReal.ofReal (Real.exp
      ((M.μ.1 (point v - point u) - slabTimeReal ω ((i : ℤ) * s) (((i : ℤ) + 1) * s) u v) / θ))

theorem measurable_rowE (M : Model m) (s w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (θ : ℝ) (i : ℕ)
    (j k : Fin m → ℤ) : Measurable (rowE M s w t θ i j k) := by
  unfold rowE
  exact Measurable.iSup fun u => Measurable.iSup fun _ => Measurable.iSup fun v =>
    Measurable.iSup fun _ =>
      ((measurable_const.sub (measurable_slabTimeReal _ _ u v)).div_const θ).exp.ennreal_ofReal

/-- The slab variable reads only the weights of its slab. -/
theorem rowE_congr (M : Model m) (s w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (θ : ℝ) (i : ℕ)
    (j k : Fin m → ℤ) {ω ω' : Config m} (h : ∀ e ∈ slabSet (m := m) s i, ω e = ω' e) :
    rowE M s w t θ i j k ω = rowE M s w t θ i j k ω' := by
  unfold rowE
  congr 1; funext u; congr 1; funext _; congr 1; funext v; congr 1; funext _
  rw [slabTimeReal_congr u v (fun e he => h e he)]

/-- `I_{i+1}(k)` is the transverse cube on the hyperplane `{x₁ = is + s}`. -/
theorem rowCube_succ_eq {s w : ℕ} (hw : 0 < w) (t : EuclideanSpace ℝ (Fin m)) (i : ℤ)
    (k : Fin m → ℤ) :
    rowCube s w t (i + 1) k =
      transverseCube (i * s + s) (rowCentre s w t (i + 1) k) ((w : ℝ) - 1) := by
  rw [rowCube_eq_transverseCube hw, add_mul, one_mul]

section Short

variable {M : Model m} {K : ℕ} {A : ℝ} {s Ms : ℕ} {t : EuclideanSpace ℝ (Fin m)} {r₁ : ℝ}
  {Cb : ℝ}

/-- **The mean of a slab variable** (equation `eq:rowenergy`): for an allowed jump,
`w|k − j| ≤ s^{3/4+δ/100}/16 + √m (w + 1)`, Proposition `prop:profiles` for the pair
`I_i(j), I_{i+1}(k)` with its pair slope gives `E sup e^{(μ(v−u) − D_i(u,v))/θ} ≤ 2` for
`θ = C(1) Q_s`. -/
theorem lintegral_rowE_le (hM : M.Standing) (h : Scale M K A s Ms t r₁) (hCb : 0 < Cb)
    (hShortK : ∀ (t' : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
      IsCubePair M K A s 1 t' I I' → ‖t' - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
        Contracts.ShortConclusion M K A s Cb t' I I')
    (i : ℕ) {j k : Fin m → ℤ}
    (hjk : (wInt M K A s : ℝ) * ‖transversePoint (k - j)‖ ≤
      (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 + Real.sqrt m * ((wInt M K A s : ℝ) + 1)) :
    ∫⁻ ω, rowE M s (wInt M K A s) t (Cb * Q M K A s) i j k ω ∂M.P ≤ 2 := by
  have hs := h.s_pos
  have hw := h.w_pos hM
  set w := wInt M K A s with hwdef
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  set c := rowCentre s w t (i : ℤ) j with hc
  set c' := rowCentre s w t ((i : ℤ) + 1) k with hc'
  set t' : EuclideanSpace ℝ (Fin m) := (s : ℝ)⁻¹ • (c' - c) with ht'
  have hpair : IsCubePair M K A s 1 t' (rowCube s w t (i : ℤ) j)
      (rowCube s w t ((i : ℤ) + 1) k) := by
    refine ⟨(i : ℤ) * s, c, c', (w : ℝ) - 1, (w : ℝ) - 1, rowCube_eq_transverseCube hw t _ j,
      rowCube_succ_eq hw t _ k, by linarith, ?_, by linarith, ?_, ?_⟩
    · have := h.w_lt hM; linarith
    · have := h.w_lt hM; linarith
    · rw [ht', smul_inv_smul₀ hs.ne', sub_self, norm_zero]; positivity
  have hslope : ‖t' - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
    have ht'eq : t' - M.t₀ = (s : ℝ)⁻¹ • (c' - c - (s : ℝ) • M.t₀) := by
      rw [ht', smul_sub _ (c' - c), inv_smul_smul₀ hs.ne']
    have hdiff : c' - c - (s : ℝ) • M.t₀ =
        (transversePoint (floorPt s t ((i : ℤ) + 1) - floorPt s t (i : ℤ)) - (s : ℝ) • t) +
          (s : ℝ) • (t - M.t₀) + (w : ℝ) • transversePoint (k - j) := by
      rw [hc, hc', rowCentre_sub, smul_sub]; abel
    have hnorm : ‖c' - c - (s : ℝ) • M.t₀‖ ≤ Real.sqrt m + s * ‖t - M.t₀‖ +
        ((s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 + Real.sqrt m * ((w : ℝ) + 1)) := by
      rw [hdiff]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_floorPt_sub_le s t _) ?_)) ?_
      · rw [norm_smul, Real.norm_of_nonneg hs.le]
      · rw [norm_smul, Real.norm_of_nonneg (by positivity)]; exact hjk
    have hmar := h.margin hM
    have hte := h.norm_t_le hM
    have hra := h.rpow_a
    rw [ht'eq, norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_le_iff₀ hs]
    have he0 : 0 ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by positivity
    calc ‖c' - c - (s : ℝ) • M.t₀‖ ≤ Real.sqrt m + s * ‖t - M.t₀‖ +
          ((s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 + Real.sqrt m * ((w : ℝ) + 1)) := hnorm
      _ ≤ s * (16 / 25 * (s : ℝ) ^ (M.δ / 100 - 1 / 4)) +
          (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 8 := by
          have := mul_le_mul_of_nonneg_left hte hs.le
          linarith only [this, hmar]
      _ ≤ s * (4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4)) := by
          rw [hra]; linarith only [mul_nonneg hs.le he0]
  obtain ⟨X, hX, hae⟩ := hShortK t' _ _ hpair hslope
  have hθ : 0 < Cb * Q M K A s := mul_pos hCb (by linarith [h.one_le_Q hM])
  refine le_trans (lintegral_mono_ae ?_) (lintegral_exp_le_two hX hθ)
  filter_upwards [hae] with ω hω
  unfold rowE
  refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hθ.le
  have h1 := hω.2 u hu v hv
  rw [hu.1, hv.1] at h1
  have h2 := neg_abs_le (slabTimeReal ω ((i : ℤ) * s) (((i : ℤ) + 1) * s) u v -
    M.μ.1 (point v - point u))
  linarith

/-- **One slab of the floor tuple**: for `y, y'` with `|y' − y − s t| ≤ √m`,
`D_i((is, y), ((i+1)s, y')) − μ(s, y' − y) ≤ O₁(C(1) Q_s)` (Proposition `prop:profiles` for
singleton cubes). -/
theorem isOs_slabStep (hM : M.Standing) (h : Scale M K A s Ms t r₁) (hCb : 0 < Cb)
    (hShortK : ∀ (t' : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
      IsCubePair M K A s 1 t' I I' → ‖t' - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
        Contracts.ShortConclusion M K A s Cb t' I I')
    (i : ℤ) {u v : Vertex m} (hu1 : u.1 = i * s) (hv1 : v.1 = (i + 1) * s)
    (hyy : ‖transversePoint (v.2 - u.2) - (s : ℝ) • t‖ ≤ Real.sqrt m) :
    IsOs M.P 1 (Cb * Q M K A s) (fun ω =>
      slabTimeReal ω (i * s) ((i + 1) * s) u v - M.μ.1 (point v - point u)) := by
  have hs := h.s_pos
  set t' : EuclideanSpace ℝ (Fin m) := (s : ℝ)⁻¹ • (transversePoint v.2 - transversePoint u.2)
    with ht'
  have hpair : IsCubePair M K A s 1 t' (transverseCube (i * s) (transversePoint u.2) 0)
      (transverseCube (i * s + s) (transversePoint v.2) 0) := by
    refine ⟨i * s, transversePoint u.2, transversePoint v.2, 0, 0, rfl, rfl, le_rfl, ?_, le_rfl,
      ?_, ?_⟩
    · have := h.one_le_W hM; linarith
    · have := h.one_le_W hM; linarith
    · rw [ht', smul_inv_smul₀ hs.ne', sub_self, norm_zero]; positivity
  have hslope : ‖t' - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
    have hte := h.norm_t_le hM
    have hsa := h.hsa
    have hra := h.rpow_a
    have ht'eq : t' - M.t₀ =
        (s : ℝ)⁻¹ • (transversePoint v.2 - transversePoint u.2 - (s : ℝ) • M.t₀) := by
      rw [ht', smul_sub _ (transversePoint v.2 - transversePoint u.2), inv_smul_smul₀ hs.ne']
    have hnorm : ‖transversePoint v.2 - transversePoint u.2 - (s : ℝ) • M.t₀‖ ≤
        Real.sqrt m + s * ‖t - M.t₀‖ := by
      have : transversePoint v.2 - transversePoint u.2 - (s : ℝ) • M.t₀ =
          (transversePoint (v.2 - u.2) - (s : ℝ) • t) + (s : ℝ) • (t - M.t₀) := by
        rw [Infra.FPP.transversePoint_sub, smul_sub]; abel
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add hyy ?_)
      rw [norm_smul, Real.norm_of_nonneg hs.le]
    rw [ht'eq, norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_le_iff₀ hs]
    have he0 : 0 ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by positivity
    have := mul_le_mul_of_nonneg_left hte hs.le
    have hsm : Real.sqrt m ≤ s * ((s : ℝ) ^ (M.δ / 100 - 1 / 4) / 16) := by
      have h2 : 0 ≤ (s : ℝ) * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by positivity
      rw [hra] at hsa
      linarith
    linarith only [hnorm, this, hsm, mul_nonneg hs.le he0]
  obtain ⟨X, hX, hae⟩ := hShortK t' _ _ hpair hslope
  have hθ : 0 < Cb * Q M K A s := mul_pos hCb (by linarith [h.one_le_Q hM])
  refine hX.mono zero_le_one hθ ((measurable_slabTimeReal _ _ _ _).sub_const _).aemeasurable ?_
  filter_upwards [hae] with ω hω
  have hu : u ∈ transverseCube (i * s) (transversePoint u.2) 0 := ⟨hu1, fun j => by simp⟩
  have hv : v ∈ transverseCube (i * s + s) (transversePoint v.2) 0 :=
    ⟨by rw [hv1]; ring, fun j => by simp⟩
  have h1 := hω.2 _ hu _ hv
  rw [hu1, hv1] at h1
  exact (le_abs_self _).trans h1

end Short

/-! ## Gaussian sums -/

/-- `∑_{z ∈ B} 2 e^{−c|z|²} ≤ 2 (4/√min(c, 1))^m` for every finite set `B` and `c > 0`. -/
theorem sum_gaussian_le (B : Finset (Fin m → ℤ)) {c : ℝ} (hc : 0 < c) :
    ∑ z ∈ B, 2 * ENNReal.ofReal (Real.exp (-c * ‖transversePoint z‖ ^ 2)) ≤
      ENNReal.ofReal (2 * (4 / Real.sqrt (min c 1)) ^ m) := by
  have ht0 : 0 < min c 1 := lt_min hc one_pos
  have ht1 : min c 1 ≤ 1 := min_le_right _ _
  rw [← Finset.mul_sum, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  gcongr
  calc ∑ z ∈ B, ENNReal.ofReal (Real.exp (-c * ‖transversePoint z‖ ^ 2))
      ≤ ∑ z ∈ B, ENNReal.ofReal (Real.exp (-min c 1 * ∑ j, ((z j : ℤ) : ℝ) ^ 2)) := by
        refine Finset.sum_le_sum fun z _ => ENNReal.ofReal_le_ofReal ?_
        rw [Real.exp_le_exp, norm_transversePoint_sq]
        have : 0 ≤ ∑ j, ((z j : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have := min_le_left c 1
        nlinarith
    _ ≤ ∑' z : Fin m → ℤ, ENNReal.ofReal (Real.exp (-min c 1 * ∑ j, ((z j : ℤ) : ℝ) ^ 2)) :=
        ENNReal.sum_le_tsum _
    _ ≤ ENNReal.ofReal ((4 / Real.sqrt (min c 1)) ^ m) :=
        Infra.Arrays.tsum_lattice_gaussian_le ht0 ht1 m

/-! ## The allowed jumps -/

open Classical in
/-- The allowed jumps `{z : w|z| ≤ L}`, as a finite set. -/
noncomputable def allowedSet (w : ℕ) (L : ℝ) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-⌈L⌉) ⌈L⌉).filter
    fun z => (w : ℝ) * ‖transversePoint z‖ ≤ L

theorem mem_allowedSet {w : ℕ} (hw : 0 < w) {L : ℝ} {z : Fin m → ℤ} :
    z ∈ allowedSet w L ↔ (w : ℝ) * ‖transversePoint z‖ ≤ L := by
  classical
  unfold allowedSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨Fintype.mem_piFinset.mpr fun k => ?_, h⟩⟩
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have h1 := abs_apply_le_norm (transversePoint z) k
  rw [Infra.FPP.transversePoint_apply] at h1
  have h2 : ‖transversePoint z‖ ≤ L := by
    have := norm_nonneg (transversePoint z); nlinarith
  have h3 := Int.le_ceil L
  rw [abs_le] at h1
  rw [Finset.mem_Icc]
  constructor
  · have : (-(⌈L⌉ : ℝ)) ≤ (z k : ℝ) := by linarith
    exact_mod_cast this
  · have : (z k : ℝ) ≤ (⌈L⌉ : ℝ) := by linarith
    exact_mod_cast this

end CurvatureVariance.Paper.Moments.ExpArray
