/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.LocalSteps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The tilt bound, the last step of the proof of Lemma `lem:localization`

In the frame `g` of a pair of cubes as in equation `eq:cubepair` with `s = n` and `|y| ≤ κn`
(`g 0`, `g (r e₁)` the centers), write `z = g (t, w)`. Lemma `lem:localization` has `κ = 1/2`, and
display `eq:transverse` of the overview has `κ = 1`.

* `tilt_of_mem_slab`: the normal of `S` makes an angle at most `arctan κ` with `e₁`, so the
  points of `S` satisfy `−κ|w| ≤ t ≤ r + κ|w|` (in the proof of the lemma, with `κ = 1/2`).
* `infDist_segment_le_of_tilt`: hence, for `κ ≤ 1`, a point of `S` with `|w| ≤ Y` lies within
  `2Y + ε` of `[u, v]` if `u`, `v` lie within `ε` of the centers.
-/

@[expose] public section

open Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Localization

variable {m : ℕ}

/-- The inner product of `ℝ × ℝ^m`. -/
lemma inner_eq_lon_tr (x y : Pt m) : ⟪x, y⟫ = Pt.lon x * Pt.lon y + ⟪Pt.tr x, Pt.tr y⟫ := by
  rw [WithLp.prod_inner_apply]
  simp [Pt.lon, Pt.tr, mul_comm]

/-- The arithmetic of the tilt bound: `ν = (ν₁, τ)` is the unit normal of `S` in the frame, with
`rν₁ = n` and `r² = n² + y²`, and `s = tν₁ + e`, `|e| ≤ wτ`, is the coordinate of the point along
the normal, in `[0, n]`. -/
lemma tilt_core {r n s t ν₁ τ y w e κ : ℝ} (hn : 0 < n) (hr : 0 < r) (h1 : r * ν₁ = n)
    (h2 : r ^ 2 = n ^ 2 + y ^ 2) (h3 : ν₁ ^ 2 + τ ^ 2 = 1) (hτ : 0 ≤ τ) (hy : 0 ≤ y)
    (hyn : y ≤ κ * n) (hw : 0 ≤ w) (hs0 : 0 ≤ s) (hs1 : s ≤ n) (hs : s = t * ν₁ + e)
    (he : |e| ≤ w * τ) : -(κ * w) ≤ t ∧ t ≤ r + κ * w := by
  have hrτ : r * τ = y := by
    have e1 : (r * τ) ^ 2 = y ^ 2 := by
      have e2 : (r * ν₁) ^ 2 + (r * τ) ^ 2 = r ^ 2 := by
        rw [mul_pow, mul_pow, ← mul_add, h3, mul_one]
      rw [h1, h2] at e2
      linarith only [e2]
    exact (sq_eq_sq₀ (by positivity) hy).1 e1
  have hle : r * |e| ≤ w * (κ * n) := by
    calc r * |e| ≤ r * (w * τ) := mul_le_mul_of_nonneg_left he hr.le
      _ = w * y := by rw [← hrτ]; ring
      _ ≤ w * (κ * n) := mul_le_mul_of_nonneg_left hyn hw
  have hrs : r * s = t * n + r * e := by rw [hs, ← h1]; ring
  have hle1 : -(r * |e|) ≤ r * e := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le e) hr.le
    linarith only [this]
  have hle2 : r * e ≤ r * |e| := mul_le_mul_of_nonneg_left (le_abs_self e) hr.le
  have hs0' : 0 ≤ r * s := mul_nonneg hr.le hs0
  have hs1' : r * s ≤ r * n := mul_le_mul_of_nonneg_left hs1 hr.le
  constructor
  · refine le_of_mul_le_mul_right ?_ hn
    linarith only [hrs, hle, hle1, hle2, hs0', hs1']
  · refine le_of_mul_le_mul_right ?_ hn
    have : (r + κ * w) * n = r * n + w * (κ * n) := by ring
    linarith only [this, hrs, hle, hle1, hle2, hs0', hs1']

/-- **The tilt bound** (in the proof of Lemma `lem:localization`, with `κ = 1/2`): if `|y| ≤ κn`,
the normal of `S` makes an angle at most `arctan κ` with the frame direction, so the points
`z = g (t, w)` of `S` satisfy `−κ|w| ≤ t ≤ r + κ|w|`. -/
theorem tilt_of_mem_slab {p : CubePair m} {n r κ : ℝ} (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (hd : p.dist = n)
    (hn : 0 < n) (hoff : ‖p.offset‖ ≤ κ * n) (hr : 0 < r) (hg0 : g 0 = p.center₁)
    (hgr : g (r • e₁) = p.center₂) {z : Pt m} (hz : z ∈ p.slab.set) :
    -(κ * ‖Pt.tr (g.symm z)‖) ≤ Pt.lon (g.symm z) ∧
      Pt.lon (g.symm z) ≤ r + κ * ‖Pt.tr (g.symm z)‖ := by
  obtain ⟨x, ⟨hx0, hx1⟩, rfl⟩ := hz
  change Pt.lon x ≤ p.dist at hx1
  change -(κ * ‖Pt.tr (g.symm (p.motion x))‖) ≤ Pt.lon (g.symm (p.motion x)) ∧
    Pt.lon (g.symm (p.motion x)) ≤ r + κ * ‖Pt.tr (g.symm (p.motion x))‖
  set h : Pt m ≃ᵃⁱ[ℝ] Pt m := p.motion.trans g.symm with hhdef
  have hsymm : ∀ q, g.symm (p.motion q) = h q := fun q => rfl
  set L := h.linearIsometryEquiv with hLdef
  have hh0 : h 0 = 0 := by
    rw [← hsymm, ← CubePair.center₁, ← hg0, g.symm_apply_apply]
  have hL : ∀ q, h q = L q := fun q => by
    have := frame_sub h 0 q
    rwa [hh0, sub_zero, sub_zero] at this
  set q : Pt m := Pt.mk p.dist p.offset with hqdef
  have hLq : L q = r • e₁ := by
    rw [← hL, ← hsymm, ← CubePair.center₂, ← hgr, g.symm_apply_apply]
  set ν : Pt m := L e₁ with hν
  rw [hsymm, hL]
  set ζ := L x with hζ
  have hlonq : Pt.lon q = n := by simp [q, hd]
  have htrq : Pt.tr q = p.offset := by simp [q]
  -- the normal in the frame
  have h1 : r * Pt.lon ν = n := by
    have e1 : ⟪ν, L q⟫ = ⟪(e₁ : Pt m), q⟫ := L.inner_map_map _ _
    rw [hLq, real_inner_smul_right, inner_e₁, real_inner_comm, inner_e₁, hlonq] at e1
    exact e1
  have h2 : r ^ 2 = n ^ 2 + ‖p.offset‖ ^ 2 := by
    have e1 : ‖L q‖ = ‖q‖ := L.norm_map q
    rw [hLq, norm_smul, norm_e₁, mul_one, Real.norm_of_nonneg hr.le] at e1
    rw [e1, Profiles.norm_sq_eq_lon_tr, hlonq, htrq]
  have h3 : Pt.lon ν ^ 2 + ‖Pt.tr ν‖ ^ 2 = 1 := by
    rw [← Profiles.norm_sq_eq_lon_tr, L.norm_map, norm_e₁, one_pow]
  have hs : Pt.lon x = Pt.lon ζ * Pt.lon ν + ⟪Pt.tr ζ, Pt.tr ν⟫ := by
    rw [← inner_eq_lon_tr, ← inner_e₁]
    exact (L.inner_map_map _ _).symm
  have hle := abs_real_inner_le_norm (Pt.tr ζ) (Pt.tr ν)
  exact tilt_core hn hr h1 h2 h3 (norm_nonneg _) (norm_nonneg _) hoff (norm_nonneg _) hx0
    (hx1.trans_eq hd) hs hle

/-- A point of the segment `[u', v']` is within `ε` of `[u, v]` if the endpoints are. -/
lemma infDist_segment_le_of_near (x : Pt m) {u v u' v' : Pt m} {ε : ℝ} (hu : dist u u' ≤ ε)
    (hv : dist v v' ≤ ε) : infDist x (segment ℝ u v) ≤ infDist x (segment ℝ u' v') + ε := by
  have hne : (segment ℝ u' v').Nonempty := ⟨u', left_mem_segment ℝ u' v'⟩
  suffices h : infDist x (segment ℝ u v) - ε ≤ infDist x (segment ℝ u' v') by linarith only [h]
  refine (le_infDist hne).2 fun w' hw' => ?_
  rw [sub_le_iff_le_add]
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hw'
  have hw : p • u + q • v ∈ segment ℝ u v := ⟨p, q, hp, hq, hpq, rfl⟩
  refine (infDist_le_dist_of_mem hw).trans ?_
  have hd : dist (p • u + q • v) (p • u' + q • v') ≤ ε := by
    rw [dist_eq_norm, show p • u + q • v - (p • u' + q • v') = p • (u - u') + q • (v - v') by
      simp only [smul_sub]; abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hp, Real.norm_of_nonneg hq, ← dist_eq_norm,
      ← dist_eq_norm]
    have e1 := mul_le_mul_of_nonneg_left hu hp
    have e2 := mul_le_mul_of_nonneg_left hv hq
    have e3 : p * ε + q * ε = ε := by rw [← add_mul, hpq, one_mul]
    linarith only [e1, e2, e3]
  have h3 := dist_triangle x (p • u' + q • v') (p • u + q • v)
  rw [dist_comm (p • u' + q • v') (p • u + q • v)] at h3
  linarith only [h3, hd]

/-- The distance to the segment between the centers of a point with `|w| ≤ Y` and
`−κ|w| ≤ t ≤ r + κ|w|`, for `κ ≤ 1`. -/
lemma infDist_centerSegment_le_of_tilt (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {r Y κ : ℝ} (hr : 0 < r) (hκ : κ ≤ 1)
    {x : Pt m} (hY : ‖Pt.tr (g.symm x)‖ ≤ Y) (h0 : -(κ * ‖Pt.tr (g.symm x)‖) ≤ Pt.lon (g.symm x))
    (h1 : Pt.lon (g.symm x) ≤ r + κ * ‖Pt.tr (g.symm x)‖) :
    infDist x (segment ℝ (g 0) (g (r • e₁))) ≤ 2 * Y := by
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans hY
  have hκw : κ * ‖Pt.tr (g.symm x)‖ ≤ ‖Pt.tr (g.symm x)‖ :=
    mul_le_of_le_one_left (norm_nonneg _) hκ
  rcases lt_or_ge (Pt.lon (g.symm x)) 0 with hneg | hnn
  · refine (infDist_le_dist_of_mem (left_mem_segment ℝ (g 0) (g (r • e₁)))).trans ?_
    have h2 : dist x (g 0) = ‖g.symm x‖ := by
      rw [← g.symm.dist_map, g.symm_apply_apply, dist_zero_right]
    rw [h2]
    have h3 := Pt.lon_tr_norm_le (g.symm x)
    rw [abs_of_neg hneg] at h3
    linarith only [h3, h0, hY, hκw]
  · rcases le_or_gt (Pt.lon (g.symm x)) r with hle | hgt
    · have := infDist_centerSegment_le g hr hnn hle
      linarith only [this, hY, hY0]
    · refine (infDist_le_dist_of_mem (right_mem_segment ℝ (g 0) (g (r • e₁)))).trans ?_
      have h2 : dist x (g (r • e₁)) = ‖g.symm x - r • e₁‖ := by
        rw [← g.symm.dist_map, g.symm_apply_apply, dist_eq_norm]
      rw [h2]
      have h3 := Pt.lon_tr_norm_le (g.symm x - r • e₁)
      rw [Pt.lon_sub, Pt.lon_smul, Pt.lon_e₁, mul_one, Pt.tr_sub, Pt.tr_smul_e₁, sub_zero,
        abs_of_pos (by linarith only [hgt])] at h3
      linarith only [h3, h1, hY, hκw]

/-- **The last step of the proof of Lemma `lem:localization`**: a point
`x = g (t, w)` with `|w| ≤ Y` and `−κ|w| ≤ t ≤ r + κ|w|`, for `κ ≤ 1`, satisfies
`dist(x, [u, v]) ≤ 2Y + ε`, if `u`, `v` lie within `ε` of `0` and `r e₁` in the frame. -/
theorem infDist_segment_le_of_tilt (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {r Y ε κ : ℝ} (hr : 0 < r) (hκ : κ ≤ 1)
    {x u v : Pt m} (hu : dist u (g 0) ≤ ε) (hv : dist v (g (r • e₁)) ≤ ε)
    (hY : ‖Pt.tr (g.symm x)‖ ≤ Y) (h0 : -(κ * ‖Pt.tr (g.symm x)‖) ≤ Pt.lon (g.symm x))
    (h1 : Pt.lon (g.symm x) ≤ r + κ * ‖Pt.tr (g.symm x)‖) :
    infDist x (segment ℝ u v) ≤ 2 * Y + ε :=
  (infDist_segment_le_of_near x hu hv).trans
    (add_le_add_left (infDist_centerSegment_le_of_tilt g hr hκ hY h0 h1) ε)

end IsotropicVariance.Paper.Proofs.Localization
