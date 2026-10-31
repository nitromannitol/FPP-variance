/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocFrame
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.SlabsTwo
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# Lemma `lem:localization`: the first change, the confinement

The proof of Lemma `lem:localization`: on `𝒢_N(log N) ⊆ 𝒢_N(C log N)`, Lemma
`lem:slabs` (1) and Lemma `lem:cone` with `S = C log N` confine the vertices of the paths `π` to
distance `C log²N` from `P` along `e₁`, and to distance at most
`C(b(ℓQ_ℓ)^{1/2} + ℓ^{3/4}(log N)^{1/2} + ℓ^{1+(δ/100−1/4)(1+δ/2)} log N)` from the line
`ū + ℝ(1, t)`.

The cone bound is at the slope `t'` of `v − u`, and the vertices are measured from `u`:

* `angle_le_of_coneBound`, `norm_transOff_of_angle_le`: far from the endpoints, the cone bound gives
  a small angle, so a small offset from `u + ℝ(1, t')` (`fst_pos_and_norm_slope_sub_le`, and the
  bound `‖z − u‖ ≤ 2(1 + T)ℓ`);
* `cone_confine`: one vertex, with the radius `Loc.coneRadius`;
* `ofs_le_of_confine`: from `u + ℝ(1, t')` to `ū + ℝ(1, t)`, which costs the term `b(ℓQ_ℓ)^{1/2}`.
* `norm_ofs_left_le`, `norm_ofs_right_le`: the offsets of the points of `I` and `I'`.
-/

@[expose] public section

open MeasureTheory Set InnerProductGeometry
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts
  CurvatureVariance.Paper.Proofs.Geometry Radius

variable {m : ℕ}

/-- `S^{1/2} ‖a‖^{−1/4}` is small at distance `K₁ S²`: the first half of the proof of
`Geometry.fst_pos_of_coneBound`. The angle at such a vector is at most the right side of equation
`eq:cone`, which is at most the aperture. -/
theorem angle_le_of_coneBound {M : Model m} {C S K₁ T : ℝ} {N : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {a : Pt m} (hC : 0 < C) (hS : 1 ≤ S) (hK₁ : C ≤ K₁)
    (hK₁' : (C / (aperture T / 2)) ^ 4 ≤ K₁) (hT : 0 ≤ T)
    (htlog : C * (‖t - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N) ≤ aperture T / 2)
    (hcb : ConeBound M C S N t a) (ha : K₁ * S ^ 2 ≤ ‖a‖) :
    angle a (slopeVec t) ≤ C * (S ^ ((1 : ℝ) / 2) * ‖a‖ ^ (-(1 : ℝ) / 4) +
        ‖t - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N) ∧
      C * (S ^ ((1 : ℝ) / 2) * ‖a‖ ^ (-(1 : ℝ) / 4) +
        ‖t - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N) ≤ aperture T := by
  set q := aperture T / 2 with hqdef
  have hq : 0 < q := by have := aperture_pos hT; positivity
  have hS2 : 0 < S ^ 2 := by positivity
  have hK₁0 : 0 < K₁ := lt_of_lt_of_le hC hK₁
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le (by positivity) ha
  have hangle := hcb ((mul_le_mul_of_nonneg_right hK₁ hS2.le).trans ha)
  refine ⟨hangle, ?_⟩
  set x := S ^ ((1 : ℝ) / 2) * ‖a‖ ^ (-(1 : ℝ) / 4) with hx
  have hx0 : 0 ≤ x := by positivity
  have e1 : (S ^ ((1 : ℝ) / 2)) ^ 4 = S ^ 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by linarith)]
  have e2 : (‖a‖ ^ (-(1 : ℝ) / 4)) ^ 4 = ‖a‖⁻¹ := by
    rw [← Real.rpow_mul_natCast ha0.le, ← Real.rpow_neg_one]
    norm_num
  have hx4 : x ^ 4 = S ^ 2 / ‖a‖ := by
    rw [hx, mul_pow, e1, e2, div_eq_mul_inv]
  have hCx : C * x ≤ q := by
    have h1 : (C * x) ^ 4 ≤ q ^ 4 := by
      rw [mul_pow, hx4]
      have h2 : C ^ 4 * S ^ 2 ≤ q ^ 4 * (K₁ * S ^ 2) := by
        have : C ^ 4 ≤ q ^ 4 * K₁ := by
          have h8 : (C / q) ^ 4 = C ^ 4 / q ^ 4 := by rw [div_pow]
          rw [h8, div_le_iff₀ (by positivity)] at hK₁'
          linarith
        have := mul_le_mul_of_nonneg_right this hS2.le
        linarith
      calc C ^ 4 * (S ^ 2 / ‖a‖) = C ^ 4 * S ^ 2 / ‖a‖ := by ring
        _ ≤ q ^ 4 * (K₁ * S ^ 2) / ‖a‖ := div_le_div_of_nonneg_right h2 ha0.le
        _ ≤ q ^ 4 * ‖a‖ / ‖a‖ :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by positivity)) ha0.le
        _ = q ^ 4 := by field_simp
    exact (pow_le_pow_iff_left₀ (by positivity) hq.le (by norm_num)).1 h1
  rw [mul_add]
  linarith only [hCx, htlog, hqdef]

/-- A vector at angle at most `θ` from `(1, t)`, with first coordinate at most `ℓ`: its offset is at
most `w₁ · 2(1 + T)²θ`, and its norm at most `2(1 + T)ℓ`. -/
theorem norm_transOff_of_angle_le {w : Pt m} {t : EuclideanSpace ℝ (Fin m)} {T θ ℓ : ℝ}
    (ht : ‖t‖ ≤ T) (hθ : θ ≤ aperture T) (hw : angle w (slopeVec t) ≤ θ) (hℓ : w.fst ≤ ℓ) :
    ‖transOff t w‖ ≤ w.fst * (slopeFactor T * θ) ∧ ‖w‖ ≤ 2 * (1 + T) * ℓ := by
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  obtain ⟨hpos, hs⟩ := fst_pos_and_norm_slope_sub_le ht hθ hw
  have e : transOff t w = w.fst • (w.fst⁻¹ • w.snd - t) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, transOff]
  have h1 : ‖transOff t w‖ ≤ w.fst * (slopeFactor T * θ) := by
    rw [e, norm_smul, Real.norm_of_nonneg hpos.le]
    exact mul_le_mul_of_nonneg_left hs hpos.le
  refine ⟨h1, ?_⟩
  have h2 : slopeFactor T * θ ≤ 1 + T := by
    have h3 : slopeFactor T * θ ≤ slopeFactor T * aperture T :=
      mul_le_mul_of_nonneg_left hθ (slopeFactor_pos hT).le
    have h4 : slopeFactor T * aperture T = 1 + T := by
      unfold slopeFactor aperture; field_simp
    linarith only [h3, h4]
  have h5 := norm_le_of_transOff t w
  rw [abs_of_pos hpos] at h5
  have h6 : w.fst * ‖slopeVec t‖ ≤ ℓ * (1 + T) :=
    mul_le_mul hℓ (norm_slopeVec_le ht) (norm_nonneg _) (hpos.le.trans hℓ)
  have h7 : w.fst * (slopeFactor T * θ) ≤ ℓ * (1 + T) :=
    mul_le_mul hℓ h2 ((mul_nonneg (slopeFactor_pos hT).le ((angle_nonneg _ _).trans hw)))
      (hpos.le.trans hℓ)
  linarith only [h1, h5, h6, h7]

/-- The radius of the first confinement: the paper's
`C (ℓ^{3/4} S^{1/2} + ℓ^{1+(δ/100−1/4)(1+δ/2)} log N)`, with `τ` a bound of the slope deviation,
and a term `C S²` for the vertices near the endpoints. -/
noncomputable def coneRadius (δ C K₁ T S lg ℓ τ : ℝ) : ℝ :=
  (1 + T) * (K₁ * S ^ 2) + slopeFactor T * C *
    (S ^ ((1 : ℝ) / 2) * (2 * (1 + T) * ℓ) ^ ((3 : ℝ) / 4) + ℓ * (τ ^ (1 + δ / 2) * lg))

/-- **The confinement at one vertex**, from the cone bounds at the slope `t'` of `v − u`, with
`‖t' − t₀‖ ≤ τ`: its first coordinate is within `K₁ S²` of `[u₁, v₁]`, and its offset from
`u + ℝ(1, t')` is at most `coneRadius`. -/
theorem cone_confine {M : Model m} (hM : M.Standing) {C S K₁ T τ : ℝ} {N : ℕ}
    {t' : EuclideanSpace ℝ (Fin m)} {u v z : Vertex m} {ℓ : ℕ} (hC : 0 < C) (hS : 1 ≤ S)
    (hK₁ : C ≤ K₁) (hK₁' : (C / (aperture T / 2)) ^ 4 ≤ K₁) (htT : ‖t'‖ ≤ T)
    (hlg : 0 ≤ Real.log N) (hτ : ‖t' - M.t₀‖ ≤ τ)
    (htlog : C * (τ ^ (1 + M.δ / 2) * Real.log N) ≤ aperture T / 2)
    (huv : point v - point u = (ℓ : ℝ) • slopeVec t')
    (hcb₁ : ConeBound M C S N t' (point v - point z))
    (hcb₂ : ConeBound M C S N t' (point z - point u)) :
    (u.1 : ℝ) - K₁ * S ^ 2 ≤ z.1 ∧ (z.1 : ℝ) ≤ v.1 + K₁ * S ^ 2 ∧
      ‖transOff t' (point z - point u)‖ ≤ coneRadius M.δ C K₁ T S (Real.log N) ℓ τ := by
  have hT : 0 ≤ T := (norm_nonneg t').trans htT
  have hδ := hM.delta_pos
  have hexp : 0 ≤ 1 + M.δ / 2 := by positivity
  have hpw : ‖t' - M.t₀‖ ^ (1 + M.δ / 2) ≤ τ ^ (1 + M.δ / 2) :=
    Real.rpow_le_rpow (norm_nonneg _) hτ hexp
  have hlog0 : ‖t' - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N ≤ τ ^ (1 + M.δ / 2) * Real.log N :=
    mul_le_mul_of_nonneg_right hpw hlg
  have htlog' : C * (‖t' - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N) ≤ aperture T / 2 :=
    (mul_le_mul_of_nonneg_left hlog0 hC.le).trans htlog
  set w := point z - point u with hw
  set w' := point v - point z with hw'
  have hsum : w + w' = (ℓ : ℝ) • slopeVec t' := by rw [← huv, hw, hw']; abel
  have hfst : w.fst + w'.fst = ℓ := by
    have := congrArg (fun y : Pt m => y.fst) hsum
    simpa [slopeVec] using this
  have hwfst : w.fst = (z.1 : ℝ) - u.1 := by simp [hw]
  have hw'fst : w'.fst = (v.1 : ℝ) - z.1 := by simp [hw']
  have hS2 : 0 ≤ S ^ 2 := by positivity
  have hK₁0 : 0 ≤ K₁ * S ^ 2 := mul_nonneg (hC.le.trans hK₁) hS2
  have hab1 := Proofs.Geometry.abs_fst_le_norm w
  have hab2 := Proofs.Geometry.abs_fst_le_norm w'
  refine ⟨?_, ?_, ?_⟩
  · by_cases hA : K₁ * S ^ 2 ≤ ‖w‖
    · have := fst_pos_of_coneBound (M := M) hC hS hK₁ hK₁' htT htlog' hcb₂ hA
      linarith only [this, hwfst, hK₁0]
    · have h1 := (abs_le.1 hab1).1
      linarith only [h1, hA, hwfst]
  · by_cases hB : K₁ * S ^ 2 ≤ ‖w'‖
    · have := fst_pos_of_coneBound (M := M) hC hS hK₁ hK₁' htT htlog' hcb₁ hB
      linarith only [this, hw'fst, hK₁0]
    · have h1 := (abs_le.1 hab2).1
      linarith only [h1, hB, hw'fst]
  -- the offset
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hτ
  have hsf := slopeFactor_pos hT
  have hrest : 0 ≤ slopeFactor T * C *
      (S ^ ((1 : ℝ) / 2) * (2 * (1 + T) * (ℓ : ℝ)) ^ ((3 : ℝ) / 4) +
        (ℓ : ℝ) * (τ ^ (1 + M.δ / 2) * Real.log N)) := by positivity
  have hfirst : 0 ≤ (1 + T) * (K₁ * S ^ 2) := by positivity
  unfold coneRadius
  by_cases hA : K₁ * S ^ 2 ≤ ‖w‖
  · by_cases hB : K₁ * S ^ 2 ≤ ‖w'‖
    · -- away from both endpoints
      obtain ⟨hang, hθ⟩ := angle_le_of_coneBound (M := M) hC hS hK₁ hK₁' hT htlog' hcb₂ hA
      have hpos' := fst_pos_of_coneBound (M := M) hC hS hK₁ hK₁' htT htlog' hcb₁ hB
      have hlt : w.fst ≤ ℓ := by linarith only [hpos', hfst]
      obtain ⟨h1, h2⟩ := norm_transOff_of_angle_le htT hθ hang hlt
      have hwpos : 0 < w.fst := (fst_pos_and_norm_slope_sub_le htT hθ hang).1
      have hwn : 0 < ‖w‖ := lt_of_lt_of_le hwpos ((le_abs_self _).trans hab1)
      have hfstn : w.fst ≤ ‖w‖ := (le_abs_self _).trans hab1
      set x := ‖w‖ ^ (-(1 : ℝ) / 4) with hx
      have hx0 : 0 ≤ x := by positivity
      have e34 : ‖w‖ * x = ‖w‖ ^ ((3 : ℝ) / 4) := by
        rw [hx]
        nth_rewrite 1 [← Real.rpow_one ‖w‖]
        rw [← Real.rpow_add hwn]
        norm_num
      have h34 : ‖w‖ ^ ((3 : ℝ) / 4) ≤ (2 * (1 + T) * (ℓ : ℝ)) ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow (norm_nonneg _) h2 (by norm_num)
      have hS12 : 0 ≤ S ^ ((1 : ℝ) / 2) := by positivity
      set ε := ‖t' - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N with hε
      have hε0 : 0 ≤ ε := by positivity
      have hb1 : w.fst * (S ^ ((1 : ℝ) / 2) * x + ε) ≤
          S ^ ((1 : ℝ) / 2) * (2 * (1 + T) * (ℓ : ℝ)) ^ ((3 : ℝ) / 4) +
            (ℓ : ℝ) * (τ ^ (1 + M.δ / 2) * Real.log N) := by
        have a1 : w.fst * (S ^ ((1 : ℝ) / 2) * x) ≤
            S ^ ((1 : ℝ) / 2) * (2 * (1 + T) * (ℓ : ℝ)) ^ ((3 : ℝ) / 4) := by
          calc w.fst * (S ^ ((1 : ℝ) / 2) * x) = S ^ ((1 : ℝ) / 2) * (w.fst * x) := by ring
            _ ≤ S ^ ((1 : ℝ) / 2) * (‖w‖ * x) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfstn hx0) hS12
            _ ≤ _ := by rw [e34]; exact mul_le_mul_of_nonneg_left h34 hS12
        have a2 : w.fst * ε ≤ (ℓ : ℝ) * (τ ^ (1 + M.δ / 2) * Real.log N) :=
          mul_le_mul hlt hlog0 hε0 (hwpos.le.trans hlt)
        rw [mul_add]
        exact add_le_add a1 a2
      have hb2 : w.fst * (slopeFactor T * (C * (S ^ ((1 : ℝ) / 2) * x + ε))) =
          slopeFactor T * C * (w.fst * (S ^ ((1 : ℝ) / 2) * x + ε)) := by ring
      have hb3 := mul_le_mul_of_nonneg_left hb1 (mul_pos hsf hC).le
      rw [← hb2] at hb3
      linarith only [h1, hb3, hfirst]
    · -- near `v`
      have e : transOff t' w = -transOff t' w' := by
        have := congrArg (transOff t') hsum
        rw [transOff_add, transOff_smul_slopeVec t'] at this
        exact eq_neg_of_add_eq_zero_left this
      rw [e, norm_neg]
      have h1 := norm_transOff_le htT w'
      have h2 : (1 + T) * ‖w'‖ ≤ (1 + T) * (K₁ * S ^ 2) :=
        mul_le_mul_of_nonneg_left (le_of_not_ge hB) (by positivity)
      linarith only [h1, h2, hrest]
  · -- near `u`
    have h1 := norm_transOff_le htT w
    have h2 : (1 + T) * ‖w‖ ≤ (1 + T) * (K₁ * S ^ 2) :=
      mul_le_mul_of_nonneg_left (le_of_not_ge hA) (by positivity)
    linarith only [h1, h2, hrest]

/-- `ℓ (t' − t) = ofs v − ofs u`, for `v − u = ℓ(1, t')`. -/
theorem smul_slope_sub_eq {t t' : EuclideanSpace ℝ (Fin m)} {p : ℤ}
    {c : EuclideanSpace ℝ (Fin m)} {u v : Vertex m} {ℓ : ℝ}
    (huv : point v - point u = ℓ • slopeVec t') :
    ℓ • (t' - t) = ofs t p c v - ofs t p c u := by
  rw [ofs_sub_ofs, huv]
  simp [transOff, slopeVec, smul_sub]

/-- **The change of line**: from the offset from `u + ℝ(1, t')` to the offset from `ū + ℝ(1, t)`,
at the cost `4Γ`, for offsets of `u` and `v` at most `Γ`. -/
theorem ofs_le_of_confine {t t' : EuclideanSpace ℝ (Fin m)} {p : ℤ}
    {c : EuclideanSpace ℝ (Fin m)} {u v z : Vertex m} {ℓ : ℕ} {Γ L R : ℝ} (hℓ : 0 < ℓ)
    (huv : point v - point u = (ℓ : ℝ) • slopeVec t') (hu : ‖ofs t p c u‖ ≤ Γ)
    (hv : ‖ofs t p c v‖ ≤ Γ) (hL : L ≤ ℓ) (hz1 : (u.1 : ℝ) - L ≤ z.1)
    (hz2 : (z.1 : ℝ) ≤ v.1 + L) (hR : ‖transOff t' (point z - point u)‖ ≤ R) :
    ‖ofs t p c z‖ ≤ 5 * Γ + R := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans hu
  have hfst : (v.1 : ℝ) - u.1 = ℓ := by
    have := congrArg (fun y : Pt m => y.fst) huv
    simpa [slopeVec] using this
  have hsl := smul_slope_sub_eq (t := t) (p := p) (c := c) huv
  have hsl2 : (ℓ : ℝ) * ‖t' - t‖ ≤ 2 * Γ := by
    have := congrArg norm hsl
    rw [norm_smul, Real.norm_of_nonneg hℓ0.le] at this
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith only [hu, hv])
  set w := point z - point u with hw
  have hwfst : w.fst = (z.1 : ℝ) - u.1 := by simp [hw]
  have hwab : |w.fst| ≤ 2 * ℓ := by
    rw [hwfst, abs_le]
    have hL0 : -L ≤ (ℓ : ℝ) := by linarith only [hℓ0, hL, hz1, hz2, hfst]
    constructor <;> linarith only [hz1, hz2, hfst, hL, hℓ0]
  have e : ofs t p c z = ofs t p c u + transOff t' w + w.fst • (t' - t) := by
    have h1 := ofs_sub_ofs t p c z u
    have h2 : transOff t w = transOff t' w + w.fst • (t' - t) := by
      simp only [transOff, smul_sub]; abel
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, h2]; abel
  have h3 : ‖w.fst • (t' - t)‖ ≤ 4 * Γ := by
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_right hwab (norm_nonneg (t' - t))
    linarith only [this, hsl2]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h4 := norm_add_le (ofs t p c u) (transOff t' w)
  linarith only [h3, h4, hu, hR]

/-- The offset of a point of the cube of center `c` in `{x₁ = p}`. -/
theorem norm_ofs_left_le {t c : EuclideanSpace ℝ (Fin m)} {p : ℤ} {a : ℝ} (ha : 0 ≤ a)
    {u : Vertex m} (hu : u ∈ transverseCube p c a) :
    ‖ofs t p c u‖ ≤ Real.sqrt m * a := by
  have h := Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (x := ofs t p c u) (r := a) ha
    fun j => by
      rw [ofs_apply, hu.1]
      have := hu.2 j
      simp only [sub_self, zero_mul, sub_zero]
      linarith only [this, ha]
  exact h

/-- The offset of a point of the cube of center `c'` in `{x₁ = p + ℓ}`, with
`|c' − c − ℓ t| ≤ 2√d`. -/
theorem norm_ofs_right_le {t c c' : EuclideanSpace ℝ (Fin m)} {p : ℤ} {ℓ : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (hcc : ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1)) {v : Vertex m}
    (hv : v ∈ transverseCube (p + ℓ) c' a) :
    ‖ofs t p c v‖ ≤ Real.sqrt m * a + 2 * Real.sqrt ((m : ℝ) + 1) := by
  have e : ofs t p c v = (transversePoint v.2 - c') + (c' - c - (ℓ : ℝ) • t) := by
    ext i
    have := hv.1
    simp only [ofs_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Infra.FPP.transversePoint_apply, this]
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hcc)
  refine Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le ha fun j => ?_
  have := hv.2 j
  rw [Proofs.ShortLengths.transversePoint_sub_apply]
  linarith only [this, ha]

end CurvatureVariance.Paper.Localization.Loc
