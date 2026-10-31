/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.TreeSetting
public import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Passage times between transverse cubes (the proof of Proposition `prop:profiles` for `s ≤ N/4`)

Let `(I, I')` be a pair of transverse cubes at distance `s`, of sides
at most `4W_s`, whose centers `c₁, c₂` have slope at most one, so that `r = |c₂ − c₁| ∈ [s, √2 s]`;
let `e = (c₂ − c₁)/r`. With the points `c₁ ∓ (s/16)e` and `c₂ ± (s/16)e`, the triangle inequality
gives, for `u ∈ I`, `v ∈ I'`,
* `T(u, v) ≥ T(c₁ − (s/16)e, c₂ + (s/16)e) − T(c₁ − (s/16)e, u) − T(v, c₂ + (s/16)e)`,
* `T(u, v) ≤ T(u, c₁ + (s/16)e) + T(c₁ + (s/16)e, c₂ − (s/16)e) + T(c₂ − (s/16)e, v)`.
The tree bound, equation `eq:tree`, at `t = s/16` controls the four passage times to the cubes
(each cube is a rectangular box centered at `c₁` or `c₂`), a line bound controls the two passage
times along `e` (of lengths `r ± s/8`), the components along `e` cancel, and
`|v − u| − (v − u)·e ≤ 16 m Q_s`. Hence `sup_{u ∈ I, v ∈ I'} |T(u, v) − |v − u|| ≤ O_1(C Q_s)`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os

variable {m : ℕ}

/-- `W_{s/16} ≥ W_s/8`. -/
lemma W_div16_ge {K : ℕ} (hK : 10 ≤ K) {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) :
    W K A s / 8 ≤ W K A (s / 16) := by
  have hQ : Q K A s / 4 ≤ Q K A (s / 16) := by
    have h := Q_le_sqrt_mul (K := K) hA (r := s / 16) (t := s)
    rcases hs.eq_or_lt with h0 | hpos
    · subst h0; simp [Q_eq, Real.zero_rpow (qExp_pos hK).ne']
    have h' := h (by positivity) (by linarith)
    have : (s / (s / 16)) ^ (1 / 2 : ℝ) = 4 := by
      rw [show s / (s / 16) = 16 by field_simp, show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [this] at h'
    linarith
  have h2 : (W K A s / 8) ^ 2 ≤ W K A (s / 16) ^ 2 := by
    rw [div_pow, W_sq hA hs, W_sq hA (by positivity)]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by have := W_nonneg K A s; positivity) (W_nonneg _ _ _)
    two_ne_zero).mp h2

/-- A function of the form `T(x, z) − (z − x)·e` is bounded above on a bounded set. -/
lemma bddAbove_passTime_sub {X : Setting m} {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd)
    (hBd0 : 0 ≤ Bd) (ω : X.Ω) {x e : Pt m} (he : ‖e‖ = 1) {B : Set (Pt m)} {R : ℝ}
    (hR : ∀ z ∈ B, dist x z ≤ R) :
    BddAbove (range fun z : B => X.passTime ω x z - ⟪(z : Pt m) - x, e⟫) := by
  refine ⟨(Bd + 1) * R, ?_⟩
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  have h1 := passTime_le_mul_dist hBd hBd0 ω x z
  have h4 : -⟪z - x, e⟫ ≤ dist x z := by
    have := abs_real_inner_le_norm (z - x) e
    rw [he, mul_one, ← dist_eq_norm, dist_comm] at this
    linarith [neg_abs_le ⟪z - x, e⟫]
  have := hR z hz
  simp only
  nlinarith [dist_nonneg (x := x) (y := z)]

/-- The constant of the profile bound. -/
noncomputable def profileConst (m : ℕ) (Ct Cl : ℝ) : ℝ :=
  4 * Ct + 2 * Cl + (16 * m + 1) / Real.log 2

lemma le_iSup_passTime_sub {X : Setting m} {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd)
    (hBd0 : 0 ≤ Bd) (ω : X.Ω) {x e : Pt m} (he : ‖e‖ = 1) {B : Set (Pt m)} {R : ℝ}
    (hR : ∀ z ∈ B, dist x z ≤ R) {z : Pt m} (hz : z ∈ B) :
    X.passTime ω x z - ⟪z - x, e⟫ ≤
      max (⨆ z : B, (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫)) 0 :=
  (le_ciSup (bddAbove_passTime_sub hBd hBd0 ω he hR) (⟨z, hz⟩ : B)).trans (le_max_left _ _)

/-- The two-sided chain bound of the proof of Proposition `prop:profiles`, for one outcome: with
the triangle inequalities through `a, b` (outer points) and `a', b'` (inner points) on the line of
the centers, `|T(u, v) − |v − u||` is at most the sum of the tree excesses, the two line excesses
and the curvature defect `|v − u| − (v − u)·e`. -/
lemma profile_pointwise {X : Setting m} {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (ω : X.Ω)
    {e a b a' b' u v : Pt m} {Za Za' Zb Zb' E : ℝ}
    (hinab : ⟪b - a, e⟫ = dist a b) (hinab' : ⟪b' - a', e⟫ = dist a' b')
    (h_a : X.passTime ω a u - ⟪u - a, e⟫ ≤ Za) (h_a' : X.passTime ω a' u + ⟪u - a', e⟫ ≤ Za')
    (h_b : X.passTime ω b v + ⟪v - b, e⟫ ≤ Zb) (h_b' : X.passTime ω b' v - ⟪v - b', e⟫ ≤ Zb')
    (hex : dist u v - ⟪v - u, e⟫ ≤ E) (hinle : ⟪v - u, e⟫ ≤ dist u v)
    (hZa : 0 ≤ Za) (hZa' : 0 ≤ Za') (hZb : 0 ≤ Zb) (hZb' : 0 ≤ Zb') :
    |X.passTime ω u v - dist u v| ≤ Za + Za' + Zb + Zb' + |X.passTime ω a b - dist a b| +
      |X.passTime ω a' b' - dist a' b'| + E := by
  have hY1 := neg_abs_le (X.passTime ω a b - dist a b)
  have hY2 := le_abs_self (X.passTime ω a' b' - dist a' b')
  have hA1 := abs_nonneg (X.passTime ω a b - dist a b)
  have hA2 := abs_nonneg (X.passTime ω a' b' - dist a' b')
  have t1 := passTime_triangle hBd ω u a' b'
  have t2 := passTime_triangle hBd ω u b' v
  have t3 := passTime_triangle hBd ω a u v
  have t4 := passTime_triangle hBd ω a v b
  rw [passTime_comm ω u a'] at t1
  rw [passTime_comm ω v b] at t4
  have i1 : ⟪v - u, e⟫ = ⟪v - b', e⟫ + ⟪b' - a', e⟫ - ⟪u - a', e⟫ := by
    rw [show v - u = (v - b') + (b' - a') - (u - a') by abel, inner_sub_left, inner_add_left]
  have i2 : ⟪b - a, e⟫ = -⟪v - b, e⟫ + ⟪v - u, e⟫ + ⟪u - a, e⟫ := by
    rw [show b - a = -(v - b) + (v - u) + (u - a) by abel, inner_add_left, inner_add_left,
      inner_neg_left]
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The curvature defect of the proof of Proposition `prop:profiles`: for `u` within `δ` of `c₁`,
`v` within `δ` of `c₂`, `c₂ − c₁ = r e` with `r ≥ s` and `4δ ≤ s`, `|v − u| − (v − u)·e ≤ 4δ²/s`,
and `(v − u)·e ≥ s/2`. -/
lemma profile_excess {e c₁ c₂ u v : Pt m} (he : ‖e‖ = 1) {r s δ : ℝ} (hs : 0 < s)
    (hc21 : c₂ - c₁ = r • e) (hrs : s ≤ r) (hδ : 4 * δ ≤ s) (hu : dist u c₁ ≤ δ)
    (hv : dist v c₂ ≤ δ) :
    s / 2 ≤ ⟪v - u, e⟫ ∧ dist u v - ⟪v - u, e⟫ ≤ 4 * δ ^ 2 / s := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hδ0 : 0 ≤ δ := dist_nonneg.trans hu
  have hperp : ‖perp e (v - u)‖ ≤ 2 * δ := by
    have : perp e (v - u) = perp e (v - c₂) - perp e (u - c₁) := by
      rw [show v - u = (v - c₂) - (u - c₁) + (c₂ - c₁) by abel, perp_add, perp_sub, hc21,
        perp_smul, perp_self he, smul_zero, add_zero]
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_perp_le_norm he (v - c₂)
    have h2 := norm_perp_le_norm he (u - c₁)
    rw [← dist_eq_norm] at h1 h2
    linarith
  have hin : s / 2 ≤ ⟪v - u, e⟫ := by
    have : ⟪v - u, e⟫ = ⟪v - c₂, e⟫ - ⟪u - c₁, e⟫ + r := by
      rw [show v - u = (v - c₂) - (u - c₁) + (c₂ - c₁) by abel, inner_add_left, inner_sub_left,
        hc21, real_inner_smul_left, hee, mul_one]
    have h1 := abs_real_inner_le_norm (v - c₂) e
    have h2 := abs_real_inner_le_norm (u - c₁) e
    rw [he, mul_one, ← dist_eq_norm] at h1 h2
    rw [this]
    linarith [abs_le.mp (h1.trans hv), abs_le.mp (h2.trans hu)]
  refine ⟨hin, ?_⟩
  have h := norm_sub_inner_le he (lt_of_lt_of_le (by positivity) hin)
  rw [dist_comm, dist_eq_norm]
  refine h.trans ?_
  rw [div_le_div_iff₀ (by linarith) hs]
  have hp2 : ‖perp e (v - u)‖ ^ 2 ≤ (2 * δ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hperp 2
  nlinarith

/-- The auxiliary points of the proof of Proposition `prop:profiles` on the line of the centers. -/
lemma exists_profile_points {c₁ c₂ : Pt m} {s : ℝ} (hs : 0 < s) (hrs : s ≤ dist c₁ c₂) :
    ∃ e a b a' b' : Pt m, ‖e‖ = 1 ∧ c₂ - c₁ = dist c₁ c₂ • e ∧
      dist a b = dist c₁ c₂ + s / 8 ∧ dist a' b' = dist c₁ c₂ - s / 8 ∧
      ⟪b - a, e⟫ = dist a b ∧ ⟪b' - a', e⟫ = dist a' b' ∧
      a + (s / 16) • e = c₁ ∧ a' + (s / 16) • (-e) = c₁ ∧
      b + (s / 16) • (-e) = c₂ ∧ b' + (s / 16) • e = c₂ ∧
      dist a c₁ = s / 16 ∧ dist a' c₁ = s / 16 ∧ dist b c₂ = s / 16 ∧ dist b' c₂ = s / 16 := by
  set r := dist c₁ c₂ with hr
  have hrpos : 0 < r := by linarith
  set e : Pt m := r⁻¹ • (c₂ - c₁) with he_def
  have hc21 : c₂ - c₁ = r • e := by
    rw [he_def, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hrpos, ← dist_eq_norm,
      dist_comm, ← hr, inv_mul_cancel₀ hrpos.ne']
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hnorm (t : ℝ) (ht : 0 ≤ t) : ‖t • e‖ = t := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg ht]
  have hv1 : c₂ + (s / 16) • e - (c₁ - (s / 16) • e) = (r + s / 8) • e := by
    rw [add_smul, ← hc21, show s / 8 = s / 16 + s / 16 by ring, add_smul]; abel
  have hv2 : c₂ - (s / 16) • e - (c₁ + (s / 16) • e) = (r - s / 8) • e := by
    rw [sub_smul, ← hc21, show s / 8 = s / 16 + s / 16 by ring, add_smul]; abel
  refine ⟨e, c₁ - (s / 16) • e, c₂ + (s / 16) • e, c₁ + (s / 16) • e, c₂ - (s / 16) • e,
    he, hc21, ?_, ?_, ?_, ?_, by abel, by rw [smul_neg]; abel, by rw [smul_neg]; abel,
    by abel, ?_, ?_, ?_, ?_⟩
  · rw [dist_comm, dist_eq_norm, hv1, hnorm _ (by positivity)]
  · rw [dist_comm, dist_eq_norm, hv2, hnorm _ (by linarith)]
  · rw [dist_comm, dist_eq_norm, hv1, hnorm _ (by positivity), real_inner_smul_left, hee,
      mul_one]
  · rw [dist_comm, dist_eq_norm, hv2, hnorm _ (by linarith), real_inner_smul_left, hee,
      mul_one]
  · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, hnorm _ (by positivity)]
  · rw [dist_eq_norm, add_sub_cancel_left, hnorm _ (by positivity)]
  · rw [dist_eq_norm, add_sub_cancel_left, hnorm _ (by positivity)]
  · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, hnorm _ (by positivity)]

/-- Six `O_1` bounds and a constant bound a random variable that is at most the sum of their
positive parts plus the constant. -/
lemma isOs_of_le_six {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z₁ Z₂ Z₃ Z₄ Z₅ Z₆ : Ω → ℝ} {θ₁ θ₂ θ₃ θ₄ θ₅ θ₆ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂)
    (h₃ : 0 < θ₃) (h₄ : 0 < θ₄) (h₅ : 0 < θ₅) (h₆ : 0 < θ₆)
    (H₁ : IsOs P 1 θ₁ Z₁) (H₂ : IsOs P 1 θ₂ Z₂) (H₃ : IsOs P 1 θ₃ Z₃) (H₄ : IsOs P 1 θ₄ Z₄)
    (H₅ : IsOs P 1 θ₅ Z₅) (H₆ : IsOs P 1 θ₆ Z₆)
    {E : ℝ} (hE : 0 ≤ E) {F : Ω → ℝ} (hF : AEMeasurable F P)
    (hle : ∀ ω, F ω ≤ max (Z₁ ω) 0 + max (Z₂ ω) 0 + max (Z₃ ω) 0 + max (Z₄ ω) 0 +
      max (Z₅ ω) 0 + max (Z₆ ω) 0 + E) :
    IsOs P 1 (θ₁ + θ₂ + θ₃ + θ₄ + θ₅ + θ₆ + (E + 1) / Real.log 2) F := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have G := isOs_add (isOs_add (isOs_add (isOs_add (isOs_add (isOs_pos H₁) (isOs_pos H₂) h₁ h₂)
    (isOs_pos H₃) (by positivity) h₃) (isOs_pos H₄) (by positivity) h₄) (isOs_pos H₅)
      (by positivity) h₅) (isOs_pos H₆) (by positivity) h₆
  have G' := isOs_add_const G (by positivity) hE
  exact IsOs.mono G' zero_le_one (by positivity) hF (ae_of_all _ hle)

lemma continuous_abs_passTime_sub_dist {X : Setting m} {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd)
    (ω : X.Ω) (I I' : Set (Pt m)) :
    Continuous fun q : I × I' => |X.passTime ω q.1 q.2 - dist (q.1 : Pt m) q.2| := by
  have h1 : Continuous fun q : I × I' => ((q.1 : Pt m), (q.2 : Pt m)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  exact (((continuous_passTime hBd ω).comp h1).sub (continuous_dist.comp h1)).abs

lemma aemeasurable_abs_passTime_sub_dist (X : Setting m) (u v : Pt m) :
    AEMeasurable (fun ω => |X.passTime ω u v - dist u v|) X.P :=
  continuous_abs.measurable.comp_aemeasurable ((aemeasurable_passTime u v).sub_const _)

/-- The conclusion of the proof of Proposition `prop:profiles` for two sets `I`, `I'` near the
centers `c₁`, `c₂`, given the six `O_1` bounds of the tree and line passage times. -/
lemma profile_conclude {X : Setting m} {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd)
    {I I' : Set (Pt m)} {c₁ c₂ e a b a' b' : Pt m} {r s δ : ℝ} (hs : 0 < s)
    (hI : c₁ ∈ I) (hI' : c₂ ∈ I') (hu_c : ∀ u ∈ I, dist u c₁ ≤ δ)
    (hv_c : ∀ v ∈ I', dist v c₂ ≤ δ) (he : ‖e‖ = 1) (hc21 : c₂ - c₁ = r • e) (hrs : s ≤ r)
    (hr32 : r ≤ 3 / 2 * s) (hδ : 4 * δ ≤ s)
    (hinab : ⟪b - a, e⟫ = dist a b) (hinab' : ⟪b' - a', e⟫ = dist a' b')
    (hRa : ∀ z ∈ I, dist a z ≤ s) (hRa' : ∀ z ∈ I, dist a' z ≤ s)
    (hRb : ∀ z ∈ I', dist b z ≤ s) (hRb' : ∀ z ∈ I', dist b' z ≤ s)
    {θ₁ θ₂ θ₃ θ₄ θ₅ θ₆ : ℝ} (h₁ : 0 < θ₁) (h₂ : 0 < θ₂) (h₃ : 0 < θ₃) (h₄ : 0 < θ₄)
    (h₅ : 0 < θ₅) (h₆ : 0 < θ₆)
    (HZa : IsOs X.P 1 θ₁ fun ω => ⨆ z : I, (X.passTime ω a z - ⟪(z : Pt m) - a, e⟫))
    (HZa' : IsOs X.P 1 θ₂ fun ω => ⨆ z : I, (X.passTime ω a' z - ⟪(z : Pt m) - a', -e⟫))
    (HZb : IsOs X.P 1 θ₃ fun ω => ⨆ z : I', (X.passTime ω b z - ⟪(z : Pt m) - b, -e⟫))
    (HZb' : IsOs X.P 1 θ₄ fun ω => ⨆ z : I', (X.passTime ω b' z - ⟪(z : Pt m) - b', e⟫))
    (HY1 : IsOs X.P 1 θ₅ fun ω => |X.passTime ω a b - dist a b|)
    (HY2 : IsOs X.P 1 θ₆ fun ω => |X.passTime ω a' b' - dist a' b'|) :
    IsOs X.P 1 (θ₁ + θ₂ + θ₃ + θ₄ + θ₅ + θ₆ + (4 * δ ^ 2 / s + 1) / Real.log 2) fun ω =>
      ⨆ (u : I) (v : I'), |X.passTime ω u v - dist (u : Pt m) v| := by
  have hne : ‖-e‖ = 1 := by rw [norm_neg, he]
  have hδ0 : 0 ≤ δ := dist_nonneg.trans (hu_c c₁ hI)
  -- measurability of the supremum
  have hbdd : ∀ ω, BddAbove (range fun q : I × I' =>
      |X.passTime ω q.1 q.2 - dist (q.1 : Pt m) q.2|) := by
    intro ω
    refine ⟨(Bd + 1) * (3 * s), ?_⟩
    rintro _ ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, rfl⟩
    have h1 := passTime_le_mul_dist hBd hBd0 ω u v
    have h0 := passTime_nonneg ω u v
    have hd : dist u v ≤ 3 * s := by
      have := dist_triangle4 u c₁ c₂ v
      have hc : dist c₁ c₂ = r := by
        rw [dist_comm, dist_eq_norm, hc21, norm_smul, he, mul_one, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      rw [dist_comm c₂ v] at this
      linarith [hu_c u hu, hv_c v hv]
    have hd0 := dist_nonneg (x := u) (y := v)
    have hm := mul_le_mul_of_nonneg_left hd hBd0
    have hm0 := mul_nonneg hBd0 hd0
    simp only
    rw [abs_le]
    constructor <;> linarith only [h1, h0, hd, hd0, hm, hm0]
  have hmeas : AEMeasurable (fun ω => ⨆ (u : I) (v : I'),
      |X.passTime ω u v - dist (u : Pt m) v|) X.P := by
    exact aemeasurable_iSup₂_of_continuous (continuous_abs_passTime_sub_dist hBd · I I') hbdd
      fun u v => aemeasurable_abs_passTime_sub_dist X u v
  refine isOs_of_le_six h₁ h₂ h₃ h₄ h₅ h₆ HZa HZa' HZb HZb' HY1 HY2 (by positivity) hmeas
    fun ω => ?_
  have : Nonempty I := ⟨⟨c₁, hI⟩⟩
  have : Nonempty I' := ⟨⟨c₂, hI'⟩⟩
  refine ciSup_le fun ⟨u, hu⟩ => ciSup_le fun ⟨v, hv⟩ => ?_
  obtain ⟨hin, hex⟩ := profile_excess he hs hc21 hrs hδ (hu_c u hu) (hv_c v hv)
  have h_a := le_iSup_passTime_sub hBd hBd0 ω he hRa hu
  have h_a' := le_iSup_passTime_sub hBd hBd0 ω hne hRa' hu
  have h_b := le_iSup_passTime_sub hBd hBd0 ω hne hRb hv
  have h_b' := le_iSup_passTime_sub hBd hBd0 ω he hRb' hv
  rw [inner_neg_right, sub_neg_eq_add] at h_a' h_b
  have hinle : ⟪v - u, e⟫ ≤ dist u v := by
    rw [dist_comm, dist_eq_norm]; exact inner_le_norm he _
  have H := profile_pointwise hBd ω hinab hinab' h_a h_a' h_b h_b' hex hinle
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
  have h5 := le_max_left |X.passTime ω a b - dist a b| 0
  have h6 := le_max_left |X.passTime ω a' b' - dist a' b'| 0
  linarith

/-- **the proof of Proposition `prop:profiles` for `s ≤ N/4`**, for `D = T`: the supremum over a
pair of transverse cubes at distance `s` of `|T(u, v) − |v − u||` is `O_1(C Q_s)`, given the tree
bound, equation `eq:tree`, at `t = s/16` and a bound on `|T(a, b) − |b − a||` for
`|b − a| ∈ [7s/8, 2s]`. -/
theorem profile_passTime (X : Setting m) {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd)
    {K : ℕ} (hK : 10 ≤ K) {A : ℝ} (hA : 1 ≤ A) {s Ct Cl : ℝ} (hs : 256 ≤ s) (hCt : 0 < Ct)
    (hCl : 0 < Cl) (hW : 4 * Real.sqrt m * W K A s ≤ s / 128)
    (htree : ∀ x e : Pt m, ‖e‖ = 1 → ∀ B : Set (Pt m), IsRectBox B (x + (s / 16) • e) →
      (∀ z ∈ B, ∀ z' ∈ B, dist z z' ≤ s / 16 / 8) →
      (∀ z ∈ B, infDist z (range fun r : ℝ => x + r • e) ≤
        16 * Real.sqrt (m + 1) * W K A (s / 16)) →
      IsOs X.P 1 (Ct * Q K A (s / 16))
        fun ω => ⨆ z : B, (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫))
    (hline : ∀ a b : Pt m, 7 / 8 * s ≤ dist a b → dist a b ≤ 2 * s →
      IsOs X.P 1 (Cl * Q K A s) fun ω => |X.passTime ω a b - dist a b|)
    (p : CubePair m) (hp : p.IsAdmissible s (W K A s) 1) :
    IsOs X.P 1 (profileConst m Ct Cl * Q K A s) fun ω =>
      ⨆ (u : p.first) (v : p.second), |X.passTime ω u v - dist (u : Pt m) v| := by
  obtain ⟨hdist, h1₀, h1, h2₀, h2, hslope⟩ := hp
  have hspos : 0 < s := by linarith only [hs]
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hQs : 1 ≤ Q K A s := one_le_Q hK hA (by linarith only [hs])
  have hQ16 : Q K A (s / 16) ≤ Q K A s :=
    Q_mono hK (by linarith only [hA]) (by positivity) (by linarith only [hs])
  have hQ16p : 0 < Q K A (s / 16) := Q_pos (by linarith only [hA]) (by positivity)
  have hWnn := W_nonneg K A s
  have hsqm := Real.sqrt_nonneg (m : ℝ)
  have hoff : ‖p.offset‖ ≤ s := by
    have : ‖p.offset‖ / p.dist ≤ 1 := hslope
    rw [hdist, div_le_one hspos] at this; exact this
  have hr_eq : dist p.center₁ p.center₂ = Real.sqrt (s ^ 2 + ‖p.offset‖ ^ 2) := by
    rw [cubePair_dist_centers, hdist]
  have hrs : s ≤ dist p.center₁ p.center₂ := by
    rw [hr_eq]; exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  have hr32 : dist p.center₁ p.center₂ ≤ 3 / 2 * s := by
    rw [hr_eq, Real.sqrt_le_left (by positivity)]
    have h := pow_le_pow_left₀ (norm_nonneg _) hoff 2
    linarith only [h, sq_nonneg s]
  obtain ⟨e, a, b, a', b', he, hc21, hdab, hdab', hinab, hinab', hca, hca', hcb, hcb',
    hdac, hdac', hdbc, hdbc'⟩ := exists_profile_points hspos hrs
  have hne : ‖-e‖ = 1 := by rw [norm_neg, he]
  have hu_c : ∀ u ∈ p.first, dist u p.center₁ ≤ 2 * Real.sqrt m * W K A s := fun u hu =>
    (cubePair_dist_center₁_le p hu h1₀).trans ((mul_le_mul_of_nonneg_left
      (show p.side₁ / 2 ≤ 2 * W K A s by linarith only [h1]) hsqm).trans_eq (by ring))
  have hv_c : ∀ v ∈ p.second, dist v p.center₂ ≤ 2 * Real.sqrt m * W K A s := fun v hv =>
    (cubePair_dist_center₂_le p hv h2₀).trans ((mul_le_mul_of_nonneg_left
      (show p.side₂ / 2 ≤ 2 * W K A s by linarith only [h2]) hsqm).trans_eq (by ring))
  have hW16 := W_div16_ge hK (A := A) (s := s) (by linarith only [hA]) hspos.le
  have hsqm1 : Real.sqrt m ≤ Real.sqrt (m + 1) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right zero_le_one)
  have hdiamI : ∀ B : Set (Pt m), ∀ c : Pt m, (∀ z ∈ B, dist z c ≤ 2 * Real.sqrt m * W K A s) →
      ∀ z ∈ B, ∀ z' ∈ B, dist z z' ≤ s / 16 / 8 := fun B c hB z hz z' hz' => by
    have := dist_triangle_right z z' c
    linarith only [this, hB z hz, hB z' hz', hW]
  have hlineI : ∀ B : Set (Pt m), ∀ c x f : Pt m, c ∈ range (fun r : ℝ => x + r • f) →
      (∀ z ∈ B, dist z c ≤ 2 * Real.sqrt m * W K A s) →
      ∀ z ∈ B, infDist z (range fun r : ℝ => x + r • f) ≤
        16 * Real.sqrt (m + 1) * W K A (s / 16) := fun B c x f hc hB z hz => by
    refine (infDist_le_dist_of_mem hc).trans ((hB z hz).trans ?_)
    calc 2 * Real.sqrt m * W K A s ≤ 2 * Real.sqrt (m + 1) * W K A s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqm1 (by norm_num)) hWnn
      _ = 16 * Real.sqrt (m + 1) * (W K A s / 8) := by ring
      _ ≤ 16 * Real.sqrt (m + 1) * W K A (s / 16) :=
          mul_le_mul_of_nonneg_left hW16 (by positivity)
  have HZa := htree a e he p.first (hca ▸ cubePair_isRectBox_first p h1₀)
    (hdiamI _ _ hu_c) (hlineI _ _ a e ⟨s / 16, hca⟩ hu_c)
  have HZa' := htree a' (-e) hne p.first (hca' ▸ cubePair_isRectBox_first p h1₀)
    (hdiamI _ _ hu_c) (hlineI _ _ a' (-e) ⟨s / 16, hca'⟩ hu_c)
  have HZb := htree b (-e) hne p.second (hcb ▸ cubePair_isRectBox_second p h2₀)
    (hdiamI _ _ hv_c) (hlineI _ _ b (-e) ⟨s / 16, hcb⟩ hv_c)
  have HZb' := htree b' e he p.second (hcb' ▸ cubePair_isRectBox_second p h2₀)
    (hdiamI _ _ hv_c) (hlineI _ _ b' e ⟨s / 16, hcb'⟩ hv_c)
  have HY1 := hline a b (by rw [hdab]; linarith only [hrs, hspos])
    (by rw [hdab]; linarith only [hr32, hspos])
  have HY2 := hline a' b' (by rw [hdab']; linarith only [hrs])
    (by rw [hdab']; linarith only [hr32, hspos])
  have hRI : ∀ x : Pt m, dist x p.center₁ = s / 16 → ∀ z ∈ p.first, dist x z ≤ s :=
    fun x hx z hz => by
      have := dist_triangle_right x z p.center₁; linarith only [this, hx, hu_c z hz, hW, hspos]
  have hRI' : ∀ x : Pt m, dist x p.center₂ = s / 16 → ∀ z ∈ p.second, dist x z ≤ s :=
    fun x hx z hz => by
      have := dist_triangle_right x z p.center₂; linarith only [this, hx, hv_c z hz, hW, hspos]
  have hCtQ : 0 < Ct * Q K A (s / 16) := by positivity
  have hClQ : 0 < Cl * Q K A s := by positivity
  have H := profile_conclude hBd hBd0 hspos (cubePair_center₁_mem p h1₀)
    (cubePair_center₂_mem p h2₀) hu_c hv_c he hc21 hrs hr32 (by linarith only [hW, hspos])
    hinab hinab'
    (hRI a hdac) (hRI a' hdac') (hRI' b hdbc) (hRI' b' hdbc') hCtQ hCtQ hCtQ hCtQ hClQ hClQ
    HZa HZa' HZb HZb' HY1 HY2
  refine IsOs.mono_scale H zero_le_one (by positivity) ?_
  unfold profileConst
  have hδ2 : 4 * (2 * Real.sqrt m * W K A s) ^ 2 / s = 16 * m * Q K A s := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), W_sq (by linarith) hspos.le]
    field_simp; ring
  rw [hδ2]
  have h16 : (16 * (m : ℝ) + 1) * Q K A s = 16 * m * Q K A s + Q K A s := by ring
  have h3 : (16 * m * Q K A s + 1) / Real.log 2 ≤ (16 * m + 1) / Real.log 2 * Q K A s := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) hl.le
  have h4 : Ct * Q K A (s / 16) ≤ Ct * Q K A s := mul_le_mul_of_nonneg_left hQ16 hCt.le
  have h5 : (4 * Ct + 2 * Cl + (16 * m + 1) / Real.log 2) * Q K A s = 4 * (Ct * Q K A s) +
      2 * (Cl * Q K A s) + (16 * m + 1) / Real.log 2 * Q K A s := by ring
  rw [h5]
  linarith only [h3, h4]

end IsotropicVariance.Paper.Proofs.Profiles
