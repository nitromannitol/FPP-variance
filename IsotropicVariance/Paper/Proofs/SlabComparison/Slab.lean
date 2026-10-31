/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.ChainStraight
import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
import IsotropicVariance.Paper.Defs.SetTime
import IsotropicVariance.Paper.Proofs.SlabComparison.Containment
import IsotropicVariance.Paper.Proofs.Profiles.Scales
import IsotropicVariance.Paper.Proofs.SlabComparison.Logarithms
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Lemma `lem:slab`: slab passage times and `T`

The steps of the paper's proof:

1. Stationarity: `exists_straight_scale`.
2. The lower bounds, from `T_P ≥ T` and the triangle inequality.
3. `W` from Lemma `lem:straight`, with `r = 4s` for `eq:slab` and `r = cℓ` for `eq:columns`, so that
   `W² ≤ O_1(C log²(2 + r))`: `isOs_of_le_mul_sq`, `log_two_add_four_mul_le`.
4. Equation `eq:slab`: `slab_pair_bound`, `isOs_iSup_slabPair`.
5. Equation `eq:columns`: `chain_bound`, `isOs_F_sub_passTime`.

The thresholds of the two cases are `2R` for `eq:slab` and `R` for `eq:columns`, for
`R = (C + 9) W²`, with `C` the constant of Lemma `lem:straight`.
-/

@[expose] public section
open MeasureTheory Set Metric
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Contracts Infra.Slab Cited Infra.Os
universe u
variable {m : ℕ}

/-- `log(2 + 4s) ≤ 2 log(2 + s)`: the scale of `r = 4s` in the proof of `eq:slab`. -/
lemma log_two_add_four_mul_le {s : ℝ} (hs : 0 ≤ s) :
    Real.log (2 + 4 * s) ≤ 2 * Real.log (2 + s) := by
  have hle : 2 + 4 * s ≤ (2 + s) ^ 2 := by nlinarith only [hs]
  calc Real.log (2 + 4 * s) ≤ Real.log ((2 + s) ^ 2) := Real.log_le_log (by positivity) hle
    _ = 2 * Real.log (2 + s) := by rw [Real.log_pow, Nat.cast_ofNat]

/-- `W² ≤ O_1(θ²)`: a random variable below `K W²`, for `W ≤ O_2(θ)`, is at most `O_1(K θ²)`
(first paragraph of the proof of Lemma `lem:slab`). -/
lemma isOs_of_le_mul_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θ K : ℝ} {W Y : Ω → ℝ}
    (hθ : 0 < θ) (hK : 0 < K) (hW : IsOs P 2 θ W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hY : AEMeasurable Y P) (hle : ∀ ω, Y ω ≤ K * W ω ^ 2) : IsOs P 1 (K * θ ^ 2) Y :=
  ((isOs_mul_iff hK).mpr (Profiles.isOs_sq hW hW0)).mono zero_le_one (by positivity) hY
    (Filter.Eventually.of_forall hle)

/-- The constant of the two pathwise bounds, as a coefficient of `W²`. -/
lemma coefficient_le {b R₀ w : ℝ} (hR₀ : 0 ≤ R₀) (hw : 1 ≤ w) :
    6 * b * (R₀ * w) + 2 ≤ (6 * |b| * R₀ + 2) * w := by
  have h := mul_le_mul_of_nonneg_right (le_abs_self b) (mul_nonneg hR₀ (zero_le_one.trans hw))
  linarith only [h, hw]

/-- **Equation `eq:slab`, the bound in probability**, for a `W` of Lemma `lem:straight` on the
ball of radius `4s` around `z`. -/
theorem isOs_iSup_slabPair (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m)
    (hw : 2 < sl.width) (z : Pt m) {W : X.Ω → ℝ} {θ R₀ : ℝ} (hθ : 0 < θ) (hW : ∀ ω, 1 ≤ W ω)
    (hOs : IsOs X.P 2 θ W) (hR₀ : 9 ≤ R₀)
    (hstraight : ∀ ω, StraightOn X ω (closedBall z (4 * sl.width)) (R₀ * W ω ^ 2)) :
    IsOs X.P 1 ((6 * |b| * R₀ + 2) * θ ^ 2) (fun ω =>
      ⨆ p : {p : Pt m × Pt m // IsSlabPair sl z p.1 p.2},
        (X.slabTime b sl ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2)) := by
  have hwidth : 0 < sl.width := by linarith only [hw]
  have hK : 0 < 6 * |b| * R₀ + 2 := by
    have := mul_nonneg (abs_nonneg b) (by linarith only [hR₀] : 0 ≤ R₀)
    linarith only [this]
  refine isOs_of_le_mul_sq hθ hK hOs (fun ω => zero_le_one.trans (hW ω))
    (aemeasurable_iSup_slabPair X hb sl hwidth.le z) (fun ω => ?_)
  have hsq : 1 ≤ W ω ^ 2 := one_le_pow₀ (hW ω)
  refine Real.iSup_le (fun p => ?_) (by positivity)
  obtain ⟨hf, hxz, hd⟩ := id p.2
  have hsqrt : Real.sqrt 5 ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hxB : p.1.1 ∈ closedBall z (4 * sl.width) := by
    rw [mem_closedBall_iff_norm]
    linarith only [hxz, hwidth]
  have hyB : p.1.2 ∈ closedBall z (4 * sl.width) := by
    rw [mem_closedBall_iff_norm]
    have htri := norm_add_le (p.1.2 - p.1.1) (p.1.1 - z)
    rw [sub_add_sub_cancel] at htri
    have hmul := mul_le_mul_of_nonneg_right hsqrt hwidth.le
    linarith only [htri, hxz, hd, hmul]
  have hR : 9 ≤ R₀ * W ω ^ 2 := by nlinarith only [hR₀, hsq]
  have hh := slab_pair_bound X ω hb sl hwidth p.2 (hstraight ω) hxB hyB hR
  have hco := coefficient_le (b := b) (by linarith only [hR₀] : 0 ≤ R₀) hsq
  linarith only [hh, hco]

/-- **Equation `eq:columns`, the bound in probability**, for a `W` of Lemma `lem:straight` on a
set containing the near-geodesics from `τ` to `τ + ℓe₁`. -/
theorem isOs_F_sub_passTime (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (M : ℕ) (hM : 1 ≤ M)
    {s : ℝ} (hs : 0 < s) (τ : Pt m) {W : X.Ω → ℝ} {θ R₀ : ℝ} (hθ : 0 < θ) (hW : ∀ ω, 1 ≤ W ω)
    (hOs : IsOs X.P 2 θ W) (hR₀ : 9 ≤ R₀) {B : Set (Pt m)}
    (hstraight : ∀ ω, StraightOn X ω B (R₀ * W ω ^ 2))
    (hB : ∀ ω, ∀ γ : IsotropicVariance.RectifiableCurve (Pt m),
      IsOneOptimal (X.ρ ω) univ τ (τ + ((M : ℝ) * s) • e₁) γ →
        ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ B) :
    IsOs X.P 1 (M * (6 * |b| * R₀ + 2) * θ ^ 2) (fun ω =>
      X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hK : 0 < (M : ℝ) * (6 * |b| * R₀ + 2) := by
    have := mul_nonneg (abs_nonneg b) (by linarith only [hR₀] : 0 ≤ R₀)
    exact mul_pos hM0 (by linarith only [this])
  refine isOs_of_le_mul_sq hθ hK hOs (fun ω => zero_le_one.trans (hW ω))
    ((aemeasurable_F X hb hs τ M).sub (Profiles.aemeasurable_passTime _ _)) (fun ω => ?_)
  have hsq : 1 ≤ W ω ^ 2 := one_le_pow₀ (hW ω)
  have hR : 9 ≤ R₀ * W ω ^ 2 := by nlinarith only [hR₀, hsq]
  have hh := chain_bound X ω hb M hM hs τ (hstraight ω) (hB ω) hR
  have hco := mul_le_mul_of_nonneg_left
    (coefficient_le (b := b) (by linarith only [hR₀] : 0 ≤ R₀) hsq) hM0.le
  linarith only [hh, hco, mul_assoc (M : ℝ) (6 * |b| * R₀ + 2) (W ω ^ 2)]

/-- The near-geodesics from `u` to `v` lie in the ball of radius `cℓ` around `u`, if
`|v − u| ≤ ℓ` and `ℓ ≥ 1`: `r = cℓ` in the proof of `eq:columns`. -/
theorem exists_near_geodesic_ball (X : Setting m) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ ℓ : ℝ, 1 ≤ ℓ → ∀ ω : X.Ω, ∀ u v : Pt m, dist u v ≤ ℓ →
      ∀ γ : IsotropicVariance.RectifiableCurve (Pt m), IsOneOptimal (X.ρ ω) univ u v γ →
        ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ closedBall u (c * ℓ) := by
  obtain ⟨a₀, b₀, ha₀, hbound⟩ := Infra.TimeConstant.setting_passTime_bounds X
  have hquot : 0 ≤ (|b₀| + 1) / a₀ := by positivity
  refine ⟨1 + (|b₀| + 1) / a₀, by linarith only [hquot], fun ℓ hℓ ω u v huv γ hγ t ht => ?_⟩
  have hcurve := oneOptimal_image_bound X ω (hbound ω) γ hγ ht
  have hb₀ : b₀ * dist u v ≤ |b₀| * ℓ :=
    (mul_le_mul_of_nonneg_right (le_abs_self b₀) dist_nonneg).trans
      (mul_le_mul_of_nonneg_left huv (abs_nonneg b₀))
  have hmul : a₀ * dist u (γ.toFun t) ≤ (|b₀| + 1) * ℓ := by
    linarith only [hcurve, hb₀, hℓ]
  have hd : dist u (γ.toFun t) ≤ (|b₀| + 1) / a₀ * ℓ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha₀, mul_comm]
    exact hmul
  rw [mem_closedBall, dist_comm, add_mul, one_mul]
  linarith only [hd, hℓ]

/-- **Lemma `lem:slab`**, from Lemma `lem:straight`. -/
theorem slabStatement_of (h : StraightStatement.{u}) : SlabStatement.{u} := by
  intro m hm X hnorm b hb
  obtain ⟨C₀, hC₀, hscale⟩ := exists_straight_scale h hm X hnorm
  obtain ⟨c, hc, hball⟩ := exists_near_geodesic_ball X
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc' : 1 ≤ Real.log c / Real.log 2 + 1 := by
    have := div_nonneg (Real.log_nonneg hc) hl2.le
    linarith only [this]
  have hR₀ : 9 ≤ C₀ + 9 := by linarith only [hC₀]
  have hK : 0 < 6 * |b| * (C₀ + 9) + 2 := by
    have := mul_nonneg (abs_nonneg b) (by linarith only [hC₀] : 0 ≤ C₀ + 9)
    linarith only [this]
  set c' := Real.log c / Real.log 2 + 1 with hc'def
  set K := 6 * |b| * (C₀ + 9) + 2 with hKdef
  have hC₀R (W : ℝ) : C₀ * W ^ 2 ≤ (C₀ + 9) * W ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith only) (sq_nonneg W)
  refine ⟨K * C₀ ^ 2 * (4 + c' ^ 2), by positivity, fun sl z hw => ⟨?_, ?_⟩,
    fun M s τ hM hs => ⟨?_, ?_⟩⟩
  · intro ω x y hp
    obtain ⟨hf, -⟩ := hp
    have hmem : x ∈ sl.set ∧ y ∈ sl.set := by
      rcases hf with hf | hf
      · exact ⟨face₀_subset_slab sl (by linarith only [hw]) hf.1,
          face₁_subset_slab sl (by linarith only [hw]) hf.2⟩
      · exact ⟨face₁_subset_slab sl (by linarith only [hw]) hf.1,
          face₀_subset_slab sl (by linarith only [hw]) hf.2⟩
    have hle := X.passTime_le_setTime hb (isClosed_slab_set sl) (convex_slab_set sl) ω hmem.1 hmem.2
    rw [X.setTime_slab sl (by linarith only [hw])] at hle
    exact sub_nonneg.mpr hle
  · have hr : 1 ≤ 4 * sl.width := by linarith only [hw]
    obtain ⟨W, hlog, hOs, hstraight⟩ := hscale _ hr z
    have hL : 1 ≤ Real.log (2 + 4 * sl.width) := Profiles.one_le_log_two_add hr
    have hθ : 0 < C₀ * Real.log (2 + 4 * sl.width) := by positivity
    have hOs' := isOs_iSup_slabPair X hb sl hw z hθ (fun ω => hL.trans (hlog ω)) hOs hR₀
      (fun ω => (hstraight ω).mono (hC₀R _))
    refine hOs'.mono_scale zero_le_one (by positivity) ?_
    have hs0 : 0 ≤ Real.log (2 + sl.width) := Real.log_nonneg (by linarith only [hw])
    have hlog2 := log_two_add_four_mul_le (s := sl.width) (by linarith only [hw])
    have hsq : Real.log (2 + 4 * sl.width) ^ 2 ≤ (2 * Real.log (2 + sl.width)) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hL]) hlog2 2
    calc K * (C₀ * Real.log (2 + 4 * sl.width)) ^ 2
        = K * C₀ ^ 2 * Real.log (2 + 4 * sl.width) ^ 2 := by ring
      _ ≤ K * C₀ ^ 2 * (2 * Real.log (2 + sl.width)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = K * C₀ ^ 2 * 4 * Real.log (2 + sl.width) ^ 2 := by ring
      _ ≤ K * C₀ ^ 2 * (4 + c' ^ 2) * Real.log (2 + sl.width) ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (sq_nonneg _)
        nlinarith only [sq_nonneg c']
  · intro ω
    exact sub_nonneg.mpr (passTime_le_slabMinimum X ω M (by linarith only [hs]) τ hb)
  · have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hℓ : 1 ≤ (M : ℝ) * s := by nlinarith only [hM1, hs]
    have hr : 1 ≤ c * ((M : ℝ) * s) := one_le_mul_of_one_le_of_one_le hc hℓ
    obtain ⟨W, hlog, hOs, hstraight⟩ := hscale _ hr τ
    have hL : 1 ≤ Real.log (2 + c * ((M : ℝ) * s)) := Profiles.one_le_log_two_add hr
    have hθ : 0 < C₀ * Real.log (2 + c * ((M : ℝ) * s)) := by positivity
    have hdist : dist τ (τ + ((M : ℝ) * s) • e₁) ≤ (M : ℝ) * s := by
      rw [dist_self_add_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith only [hℓ]),
        Paper.norm_e₁, mul_one]
    have hOs' := isOs_F_sub_passTime X hb M hM (by linarith only [hs] : 0 < s) τ hθ
      (fun ω => hL.trans (hlog ω)) hOs hR₀ (fun ω => (hstraight ω).mono (hC₀R _))
      (fun ω => hball _ hℓ ω _ _ hdist)
    refine hOs'.mono_scale zero_le_one (by positivity) ?_
    have hpoly := log_le_of_polynomial_bound (q := 1) (R := (M : ℝ) * s)
      (N := 2 + c * ((M : ℝ) * s)) hc hℓ (by linarith only [hr]) (by
        rw [pow_one]
        nlinarith only [hc, hℓ])
    rw [Nat.cast_one, ← hc'def] at hpoly
    have hsq : Real.log (2 + c * ((M : ℝ) * s)) ^ 2 ≤
        (c' * Real.log (2 + (M : ℝ) * s)) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hL]) hpoly 2
    have hM0 : (0 : ℝ) ≤ M := by linarith only [hM1]
    calc M * K * (C₀ * Real.log (2 + c * ((M : ℝ) * s))) ^ 2
        = M * K * C₀ ^ 2 * Real.log (2 + c * ((M : ℝ) * s)) ^ 2 := by ring
      _ ≤ M * K * C₀ ^ 2 * (c' * Real.log (2 + (M : ℝ) * s)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = K * C₀ ^ 2 * c' ^ 2 * M * Real.log (2 + (M : ℝ) * s) ^ 2 := by ring
      _ ≤ K * C₀ ^ 2 * (4 + c' ^ 2) * M * Real.log (2 + (M : ℝ) * s) ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ?_ (by positivity)) hM0) (sq_nonneg _)
        linarith only

end IsotropicVariance.Paper.Proofs.SlabComparison
