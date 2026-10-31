/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusCover
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Euclidean part of the proof of Lemma `lem:modulus`

The third paragraph of the proof. The paper places the centers of `I` and `I'` at `0` and `re₁`;
here `axis p` is the unit vector from the first center to the second, and it plays the part of
`e₁`.

* `phi e x`: the function `φ(x) = |x| − e·x`.
* `dist_terms_eq_phi_terms`: "the terms `e₁ · x` cancel".
* `norm_gradPhi_le`, `abs_phi_sub_le`: the bound of `∇φ` and the mean value inequality.
* `phi_terms_le`: the six `φ` terms for the points of a pair of cubes, at the sizes used in
  the proof.
-/

@[expose] public section

open Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Modulus

open Infra.Slab

variable {m : ℕ}

/-- The function `φ(x) = |x| − e·x` of the proof of Lemma `lem:modulus`. -/
noncomputable def phi (e x : Pt m) : ℝ := ‖x‖ - ⟪e, x⟫

/-- **The components along `e₁` cancel**: the Euclidean terms of the
rerouting are the six `φ` terms. -/
lemma dist_terms_eq_phi_terms (e u u₁ v v₁ x y : Pt m) :
    (dist u₁ x - dist u x) + (dist y v₁ - dist y v) - (dist u₁ v₁ - dist u v) =
      phi e (x - u₁) - phi e (x - u) + (phi e (v₁ - y) - phi e (v - y)) -
        (phi e (v₁ - u₁) - phi e (v - u)) := by
  simp only [phi, inner_sub_right, dist_comm u₁ x, dist_comm u x, dist_comm u₁ v₁, dist_comm u v,
    dist_comm y v₁, dist_comm y v, dist_eq_norm]
  ring

/-- The derivative of `φ` off the origin. -/
lemma hasFDerivAt_phi (e : Pt m) {x : Pt m} (hx : x ≠ 0) :
    HasFDerivAt (phi e) (innerSL ℝ (‖x‖⁻¹ • x - e)) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 : HasFDerivAt (fun y : Pt m => ‖y‖) ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x)) x := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  refine (h1.sub (innerSL ℝ e).hasFDerivAt).congr_fderiv ?_
  ext y
  simp only [sub_apply, smul_apply, innerSL_apply_apply,
    inner_sub_left, inner_smul_left, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat, conj_trivial,
    map_inv₀]
  field_simp

/-- **The gradient of `φ`**: `|∇φ(x)| ≤ 2|x − μe|/|x|` for `μ ≥ 0`. The paper
states it at `μ = e·x ≥ 0`. -/
lemma norm_gradPhi_le {e x : Pt m} (he : ‖e‖ = 1) (hx : x ≠ 0) {μ : ℝ} (hμ : 0 ≤ μ) :
    ‖‖x‖⁻¹ • x - e‖ ≤ 2 * ‖x - μ • e‖ / ‖x‖ :=
  norm_normalize_sub_le hx he hμ le_rfl

/-- **The mean value inequality for `φ`**: if every point `z` of `[a, b]` has `|z| ≥ g` and is
within `w` of a nonnegative multiple of `e`, then `|φ(a) − φ(b)| ≤ (2w/g)|a − b|`. -/
theorem abs_phi_sub_le {e a b : Pt m} (he : ‖e‖ = 1) {w g : ℝ} (hg : 0 < g)
    (h : ∀ z ∈ segment ℝ a b, g ≤ ‖z‖ ∧ ∃ μ : ℝ, 0 ≤ μ ∧ ‖z - μ • e‖ ≤ w) :
    |phi e a - phi e b| ≤ 2 * w / g * ‖a - b‖ := by
  have hz : ∀ z ∈ segment ℝ a b, z ≠ 0 := fun z hz => norm_pos_iff.mp (hg.trans_le (h z hz).1)
  have hb : ∀ z ∈ segment ℝ a b, ‖innerSL ℝ (‖z‖⁻¹ • z - e)‖ ≤ 2 * w / g := by
    intro z hz'
    obtain ⟨hgz, μ, hμ, hw⟩ := h z hz'
    rw [innerSL_apply_norm]
    have h0 : 0 ≤ w := (norm_nonneg _).trans hw
    calc ‖‖z‖⁻¹ • z - e‖ ≤ 2 * ‖z - μ • e‖ / ‖z‖ := norm_gradPhi_le he (hz z hz') hμ
      _ ≤ 2 * w / g :=
        div_le_div₀ (mul_nonneg zero_le_two h0) (mul_le_mul_of_nonneg_left hw zero_le_two) hg hgz
  have := (convex_segment a b).norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ) (f := phi e)
    (f' := fun z => innerSL ℝ (‖z‖⁻¹ • z - e))
    (fun z hz' => (hasFDerivAt_phi e (hz z hz')).hasFDerivWithinAt) hb
    (right_mem_segment ℝ a b) (left_mem_segment ℝ a b)
  rwa [Real.norm_eq_abs] at this

/-- The mean value inequality for differences `q' − q`, with `q ∈ [a, b]` and `q' ∈ [a', b']`. -/
lemma abs_phi_sub_sub_le {e a a' b b' : Pt m} (he : ‖e‖ = 1) {w g : ℝ} (hg : 0 < g)
    (h : ∀ q ∈ segment ℝ a b, ∀ q' ∈ segment ℝ a' b',
      g ≤ ‖q' - q‖ ∧ ∃ μ : ℝ, 0 ≤ μ ∧ ‖q' - q - μ • e‖ ≤ w) :
    |phi e (a' - a) - phi e (b' - b)| ≤ 2 * w / g * ‖(a' - a) - (b' - b)‖ := by
  refine abs_phi_sub_le he hg fun z hz => ?_
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
  have hsub := h _ ⟨α, β, hα, hβ, hαβ, rfl⟩ _ ⟨α, β, hα, hβ, hαβ, rfl⟩
  rwa [show α • a' + β • b' - (α • a + β • b) = α • (a' - a) + β • (b' - b) by
    simp only [smul_sub]; abel] at hsub

/-! ## The direction of the centers -/

/-- The unit vector from the center of `I` to the center of `I'`: the paper's `e₁`
in the proof of Lemma `lem:modulus`. -/
noncomputable def axis (p : CubePair m) : Pt m :=
  ‖p.center₂ - p.center₁‖⁻¹ • (p.center₂ - p.center₁)

lemma center₁_ne_center₂ {p : CubePair m} (hn : 0 < p.dist) : p.center₁ ≠ p.center₂ := by
  intro h
  have h0 := congrArg Pt.lon (p.motion.injective h)
  simp only [Pt.lon_zero, Pt.lon_mk] at h0
  linarith

lemma norm_axis {p : CubePair m} (hn : 0 < p.dist) : ‖axis p‖ = 1 := by
  have h : 0 < ‖p.center₂ - p.center₁‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (center₁_ne_center₂ hn).symm)
  rw [axis, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h.ne']

lemma smul_axis {p : CubePair m} (hn : 0 < p.dist) :
    ‖p.center₂ - p.center₁‖ • axis p = p.center₂ - p.center₁ := by
  have h : ‖p.center₂ - p.center₁‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (center₁_ne_center₂ hn).symm)
  rw [axis, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- The points of `I` lie near the center of `I`. -/
lemma norm_sub_center₁_le {p : CubePair m} (h1 : 0 ≤ p.side₁) {q : Pt m} (hq : q ∈ p.first) :
    ‖q - p.center₁‖ ≤ Real.sqrt m * (p.side₁ / 2) := by
  obtain ⟨z, ⟨hz0, hz⟩, rfl⟩ := hq
  rw [← dist_eq_norm, CubePair.center₁, p.motion.dist_map, dist_zero_right]
  exact Profiles.norm_le_of_lon_zero (by positivity) hz0 hz

/-- The points of `I'` lie near the center of `I'`. -/
lemma norm_sub_center₂_le {p : CubePair m} (h2 : 0 ≤ p.side₂) {q : Pt m} (hq : q ∈ p.second) :
    ‖q - p.center₂‖ ≤ Real.sqrt m * (p.side₂ / 2) := by
  obtain ⟨z, ⟨hz0, hz⟩, rfl⟩ := hq
  rw [← dist_eq_norm, CubePair.center₂, p.motion.dist_map, dist_eq_norm]
  refine Profiles.norm_le_of_lon_zero (by positivity) (by simp [hz0]) fun k => ?_
  simpa using hz k

/-- **Off `E`, the cut points are near the segment between the centers**. -/
lemma infDist_center_segment_le {p : CubePair m} {u v x : Pt m} {lam R₀ : ℝ}
    (hu : ‖u - p.center₁‖ ≤ R₀) (hv : ‖v - p.center₂‖ ≤ R₀)
    (hx : infDist x (segment ℝ u v) ≤ lam) :
    infDist x (segment ℝ p.center₁ p.center₂) ≤ lam + R₀ := by
  obtain ⟨s, hs, hd⟩ := (isCompact_segment' u v).exists_infDist_eq_dist
    ⟨u, left_mem_segment ℝ u v⟩ x
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hs
  have h1 : dist (a • u + b • v) (a • p.center₁ + b • p.center₂) ≤ R₀ := by
    rw [dist_eq_norm, show a • u + b • v - (a • p.center₁ + b • p.center₂) =
      a • (u - p.center₁) + b • (v - p.center₂) by simp only [smul_sub]; abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    calc a * ‖u - p.center₁‖ + b * ‖v - p.center₂‖ ≤ a * R₀ + b * R₀ :=
          add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
      _ = R₀ := by rw [← add_mul, hab, one_mul]
  calc infDist x (segment ℝ p.center₁ p.center₂)
      ≤ dist x (a • p.center₁ + b • p.center₂) := infDist_le_dist_of_mem ⟨a, b, ha, hb, hab, rfl⟩
    _ ≤ dist x (a • u + b • v) + dist (a • u + b • v) (a • p.center₁ + b • p.center₂) :=
        dist_triangle _ _ _
    _ ≤ lam + R₀ := add_le_add (hd ▸ hx) h1

/-! ## The six `φ` terms -/

lemma slabCoord_of_mem_segment {sl : Slab m} {a b q : Pt m} {c : ℝ} (ha : slabCoord sl a = c)
    (hb : slabCoord sl b = c) (hq : q ∈ segment ℝ a b) : slabCoord sl q = c :=
  ((convex_singleton c).affine_preimage (slabCoordAffine sl)).segment_subset ha hb hq

lemma le_norm_of_slabCoord (sl : Slab m) {x y : Pt m} {g : ℝ}
    (h : g ≤ slabCoord sl x - slabCoord sl y) : g ≤ ‖x - y‖ := by
  rw [← dist_eq_norm]
  exact h.trans ((le_abs_self _).trans (abs_slabCoord_sub_le sl x y))

lemma norm_sub_center_of_mem_segment {a b q c : Pt m} {R : ℝ} (ha : ‖a - c‖ ≤ R) (hb : ‖b - c‖ ≤ R)
    (hq : q ∈ segment ℝ a b) : ‖q - c‖ ≤ R := by
  have h := (convex_closedBall c R).segment_subset (by rwa [mem_closedBall, dist_eq_norm])
    (by rwa [mem_closedBall, dist_eq_norm]) hq
  rwa [mem_closedBall, dist_eq_norm] at h

/-- **The six `φ` terms**. The first two pairs have gradient at most
`2(λ + 2R₀)/a` on their segments, and the last pair `4R₀/s`, for `s` the width; the arguments of
each of the first two pairs differ by at most `δ`, and those of the last pair by at most `2δ`. -/
theorem phi_terms_le {p : CubePair m} (hn : 0 < p.dist) {a lam R₀ δ : ℝ} (ha : 0 < a)
    (hR₁ : ∀ q ∈ p.first, ‖q - p.center₁‖ ≤ R₀) (hR₂ : ∀ q ∈ p.second, ‖q - p.center₂‖ ≤ R₀)
    {u u₁ v v₁ x y : Pt m} (hu : u ∈ p.first) (hu₁ : u₁ ∈ p.first) (hv : v ∈ p.second)
    (hv₁ : v₁ ∈ p.second) (hx : slabCoord p.slab x = a) (hy : slabCoord p.slab y = p.dist - a)
    (hxt : infDist x (segment ℝ u v) ≤ lam) (hyt : infDist y (segment ℝ u v) ≤ lam)
    (hdu : dist u₁ u ≤ δ) (hdv : dist v₁ v ≤ δ) :
    phi (axis p) (x - u₁) - phi (axis p) (x - u) +
        (phi (axis p) (v₁ - y) - phi (axis p) (v - y)) -
        (phi (axis p) (v₁ - u₁) - phi (axis p) (v - u)) ≤
      4 * (lam + 2 * R₀) / a * δ + 8 * R₀ / p.dist * δ := by
  have he := norm_axis hn
  have hne := center₁_ne_center₂ hn
  have hcu := (frame_first hu).1
  have hcu₁ := (frame_first hu₁).1
  have hcv := (frame_second hv).1
  have hcv₁ := (frame_second hv₁).1
  have hR₀ : 0 ≤ R₀ := (norm_nonneg _).trans (hR₁ u hu)
  have hδ : 0 ≤ δ := dist_nonneg.trans hdu
  have hlam : 0 ≤ lam := infDist_nonneg.trans hxt
  have hdu' : ‖u₁ - u‖ ≤ δ := by rwa [← dist_eq_norm]
  have hdv' : ‖v₁ - v‖ ≤ δ := by rwa [← dist_eq_norm]
  have hxc := infDist_center_segment_le (hR₁ u hu) (hR₂ v hv) hxt
  have hyc := infDist_center_segment_le (hR₁ u hu) (hR₂ v hv) hyt
  obtain ⟨μ, -, hμ, -, hxμ, -⟩ := exists_ray_near hne hxc
  obtain ⟨-, μ', -, hμ', -, hyμ⟩ := exists_ray_near hne hyc
  replace hxμ : ‖x - p.center₁ - μ • axis p‖ ≤ lam + R₀ := hxμ
  replace hyμ : ‖p.center₂ - y - μ' • axis p‖ ≤ lam + R₀ := hyμ
  -- the first pair
  have t₁ : |phi (axis p) (x - u₁) - phi (axis p) (x - u)| ≤
      2 * (lam + 2 * R₀) / a * ‖(x - u₁) - (x - u)‖ := by
    refine abs_phi_sub_sub_le he ha fun q hq q' hq' => ?_
    rw [segment_same, mem_singleton_iff] at hq'
    subst hq'
    have hq0 : slabCoord p.slab q = 0 :=
      slabCoord_of_mem_segment hcu₁ hcu hq
    have hqR := norm_sub_center_of_mem_segment (hR₁ _ hu₁) (hR₁ _ hu) hq
    refine ⟨le_norm_of_slabCoord p.slab (by rw [hx, hq0, sub_zero]), μ, hμ, ?_⟩
    rw [show q' - q - μ • axis p = (q' - p.center₁ - μ • axis p) - (q - p.center₁) by abel]
    refine (norm_sub_le _ _).trans ?_
    linarith only [hxμ, hqR]
  -- the second pair
  have t₂ : |phi (axis p) (v₁ - y) - phi (axis p) (v - y)| ≤
      2 * (lam + 2 * R₀) / a * ‖(v₁ - y) - (v - y)‖ := by
    refine abs_phi_sub_sub_le he ha fun q hq q' hq' => ?_
    rw [segment_same, mem_singleton_iff] at hq
    subst hq
    have hq0 : slabCoord p.slab q' = p.dist :=
      slabCoord_of_mem_segment hcv₁ hcv hq'
    have hqR := norm_sub_center_of_mem_segment (hR₂ _ hv₁) (hR₂ _ hv) hq'
    refine ⟨le_norm_of_slabCoord p.slab (by rw [hy, hq0]; linarith only), μ', hμ', ?_⟩
    rw [show q' - q - μ' • axis p = (q' - p.center₂) + (p.center₂ - q - μ' • axis p) by abel]
    refine (norm_add_le _ _).trans ?_
    linarith only [hyμ, hqR]
  -- the last pair
  have t₃ : |phi (axis p) (v₁ - u₁) - phi (axis p) (v - u)| ≤
      2 * (2 * R₀) / p.dist * ‖(v₁ - u₁) - (v - u)‖ := by
    refine abs_phi_sub_sub_le he hn fun q hq q' hq' => ?_
    have hq0 : slabCoord p.slab q = 0 :=
      slabCoord_of_mem_segment hcu₁ hcu hq
    have hq0' : slabCoord p.slab q' = p.dist :=
      slabCoord_of_mem_segment hcv₁ hcv hq'
    have hqR := norm_sub_center_of_mem_segment (hR₁ _ hu₁) (hR₁ _ hu) hq
    have hqR' := norm_sub_center_of_mem_segment (hR₂ _ hv₁) (hR₂ _ hv) hq'
    refine ⟨le_norm_of_slabCoord p.slab (by rw [hq0, hq0', sub_zero]),
      ‖p.center₂ - p.center₁‖, norm_nonneg _, ?_⟩
    rw [smul_axis hn, show q' - q - (p.center₂ - p.center₁) =
      (q' - p.center₂) - (q - p.center₁) by abel]
    refine (norm_sub_le _ _).trans ?_
    linarith only [hqR, hqR']
  -- the arguments
  have d₁ : ‖(x - u₁) - (x - u)‖ ≤ δ := by
    rw [show (x - u₁) - (x - u) = -(u₁ - u) by abel, norm_neg]; exact hdu'
  have d₂ : ‖(v₁ - y) - (v - y)‖ ≤ δ := by
    rw [show (v₁ - y) - (v - y) = v₁ - v by abel]; exact hdv'
  have d₃ : ‖(v₁ - u₁) - (v - u)‖ ≤ 2 * δ := by
    rw [show (v₁ - u₁) - (v - u) = (v₁ - v) - (u₁ - u) by abel]
    exact (norm_sub_le _ _).trans (by linarith only [hdu', hdv'])
  have c₁ : 0 ≤ 2 * (lam + 2 * R₀) / a := by positivity
  have c₂ : 0 ≤ 2 * (2 * R₀) / p.dist := by positivity
  have b₁ := (le_abs_self _).trans (t₁.trans (mul_le_mul_of_nonneg_left d₁ c₁))
  have b₂ := (le_abs_self _).trans (t₂.trans (mul_le_mul_of_nonneg_left d₂ c₁))
  have b₃ := (neg_abs_le _).trans' (neg_le_neg (t₃.trans (mul_le_mul_of_nonneg_left d₃ c₂)))
  have e₁ : 4 * (lam + 2 * R₀) / a * δ = 2 * (lam + 2 * R₀) / a * δ +
      2 * (lam + 2 * R₀) / a * δ := by ring
  have e₂ : 8 * R₀ / p.dist * δ = 2 * (2 * R₀) / p.dist * (2 * δ) := by ring
  linarith only [b₁, b₂, b₃, e₁, e₂]

end IsotropicVariance.Paper.Proofs.Modulus
