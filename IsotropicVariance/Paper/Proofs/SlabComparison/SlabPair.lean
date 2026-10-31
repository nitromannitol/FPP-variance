/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.Surgery
public import IsotropicVariance.Paper.Proofs.SlabComparison.AngleCones
public import IsotropicVariance.Paper.Proofs.SlabComparison.EndpointExits
public import IsotropicVariance.Paper.Proofs.SlabComparison.Stationary
public import IsotropicVariance.Paper.Proofs.Profiles.OsTools

/-! # Equation `eq:slab` on one outcome, and the measurability of its supremum

The second paragraph of the proof of Lemma `lem:slab`, on one outcome, for a threshold `R` of
Lemma `lem:straight`.

* `slab_comparison_straight`: if `s ≥ 2R`, the end pieces of a near-geodesic are replaced by
  segments, and `T_P(x, y) ≤ T(x, y) + 2bR + 1`.
* `slabTime_sub_passTime_le`: with the case `s < 2R`, by the segment `[x, y]`.
* `slab_pair_bound`: for the two orders of the faces in `IsSlabPair`.

The supremum of equation `eq:slab` over the uncountable set of pairs is a random variable, by
continuity in the pair: `aemeasurable_iSup_slabPair`, on the model of `aemeasurable_modulusSup`.
-/

@[expose] public section
open MeasureTheory Set Metric
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Contracts Infra.Slab
variable {m : ℕ}

/-- The slab passage time is symmetric on the slab. -/
lemma slabTime_comm (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) (ω : X.Ω)
    {u v : Pt m} (hu : u ∈ sl.set) (hv : v ∈ sl.set) :
    X.slabTime b sl ω u v = X.slabTime b sl ω v u := by
  rw [slabTime_eq_passageTime_ext X hb sl ω hu hv, slabTime_eq_passageTime_ext X hb sl ω hv hu]
  exact Profiles.passageTime_comm (measurable_extDensity sl b (Profiles.measurable_ρ_apply X ω)) u v

/-- `|y − x| ≤ 5^{1/2} s` is the slope bound `2` (the angle `arctan 2` of the proof of equation
`eq:slab`). -/
lemma slope_le_two_of_dist_le (sl : Slab m) (hw : 0 < sl.width) {x y : Pt m}
    (h : dist x y ≤ Real.sqrt 5 * sl.width) : sl.slope x y ≤ 2 := by
  have hsq : dist x y ^ 2 ≤ 5 * sl.width ^ 2 := by
    calc dist x y ^ 2 ≤ (Real.sqrt 5 * sl.width) ^ 2 := pow_le_pow_left₀ dist_nonneg h 2
      _ = 5 * sl.width ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
  unfold Slab.slope
  rw [div_le_iff₀ hw]
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  linarith only [hsq, show (2 * sl.width) ^ 2 = 4 * sl.width ^ 2 by ring]

/-- **Equation `eq:slab`, the case of a large width**, on one outcome: if
`s ≥ 2R`, with `R ≥ 9` a threshold of Lemma `lem:straight` on a set containing `x` and `y`, the
points of a near-geodesic from `x` to `y` at distance at least `R` from `x` and `y` are at distance
more than one from `∂P`, and replacing its two end pieces by segments gives
`T_P(x, y) ≤ T(x, y) + 2bR + 1`. -/
theorem slab_comparison_straight (X : Setting m) (ω : X.Ω) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) (hw : 0 < sl.width) {x y : Pt m} (hx : x ∈ sl.face₀) (hy : y ∈ sl.face₁)
    (hs : sl.slope x y ≤ 2) {B : Set (Pt m)} {R : ℝ} (hstraight : StraightOn X ω B R)
    (hxB : x ∈ B) (hyB : y ∈ B) (hR : 9 ≤ R) (hRs : 2 * R ≤ sl.width) :
    X.slabTime b sl ω x y - X.passTime ω x y ≤ 2 * b * R + 1 := by
  obtain ⟨γ, hγ, hγrev⟩ := exists_oneOptimal_lipschitz X ω x y
  have hwidth : sl.width ≤ dist x y := by
    have h := abs_slabLinear_le sl (y - x)
    rw [slabLinear_sub, coord_face₁ sl hy, coord_face₀ sl hx, sub_zero, abs_of_pos hw,
      ← dist_eq_norm'] at h
    exact h
  have hne : x ≠ y := dist_pos.mp (by linarith only [hw, hwidth])
  obtain ⟨a, c, ha, hac, hc, hrad, hrad', hmid⟩ := exists_endpoint_exits γ (r := R)
    (by linarith only [hR]) (hRs.trans hwidth)
  have hrev (t : ℝ) : γ.reverse.toRectifiable.toFun (1 - t) = γ.toFun t := by
    change γ.toFun (1 - (1 - t)) = γ.toFun t
    rw [sub_sub_cancel]
  have hpoint (t : ℝ) (ht : t ∈ Icc a c) :
      γ.toFun t ∈ sl.set ∧ 1 < infDist (γ.toFun t) sl.faces := by
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1, ht.2.trans hc⟩
    obtain ⟨hd₁, hd₂⟩ := hmid t ht
    refine interior_of_endpoint_angles sl hw hx hy hs (hR.trans hd₁) (hR.trans hd₂) ?_ ?_
    · exact hstraight x hxB y hyB hne γ.toRectifiable hγ t ht01 (hd₁.trans_eq (dist_eq_norm' _ _))
    · have hh := hstraight y hyB x hxB hne.symm γ.reverse.toRectifiable hγrev (1 - t)
        ⟨by linarith only [ht01.2], by linarith only [ht01.1]⟩
      rw [hrev] at hh
      exact hh (hd₂.trans_eq (dist_eq_norm' _ _))
  have hmiddle (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (γ.toRectifiable.subcurve a c ha hac hc).toFun t ∈ sl.set ∧
        1 < infDist ((γ.toRectifiable.subcurve a c ha hac hc).toFun t) sl.faces :=
    hpoint _ (Infra.Curves.subParam_mapsTo hac ht)
  have hh := slab_comparison_of_middle X ω hb sl
    (face₀_subset_slab sl hw.le hx) (face₁_subset_slab sl hw.le hy) γ.toRectifiable hγ
    ha hac hc (fun t ht => (hmiddle t ht).1) (fun t ht => (hmiddle t ht).2)
  change X.slabTime b sl ω x y - X.passTime ω x y ≤
    b * (dist x (γ.toFun a) + dist y (γ.toFun c)) + 1 at hh
  rw [hrad, hrad'] at hh
  linarith only [hh]

/-- **Equation `eq:slab`, both cases**, on one outcome, for `x` on the first face and `y` on the
second. If `s < 2R`, the segment `[x, y]` gives the bound. -/
theorem slabTime_sub_passTime_le (X : Setting m) (ω : X.Ω) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) (hw : 0 < sl.width) {x y : Pt m} (hx : x ∈ sl.face₀) (hy : y ∈ sl.face₁)
    (hs : sl.slope x y ≤ 2) {B : Set (Pt m)} {R : ℝ} (hstraight : StraightOn X ω B R)
    (hxB : x ∈ B) (hyB : y ∈ B) (hR : 9 ≤ R) :
    X.slabTime b sl ω x y - X.passTime ω x y ≤ 6 * b * R + 1 := by
  have hb0 := upperBound_nonneg X hb ω
  have hbR : 0 ≤ b * R := mul_nonneg hb0 (by linarith only [hR])
  by_cases hRs : 2 * R ≤ sl.width
  · have hh := slab_comparison_straight X ω hb sl hw hx hy hs hstraight hxB hyB hR hRs
    linarith only [hh, hbR]
  · have hupper := SlabComparison.slabTime_le_mul_dist sl hw.le (X.ρ ω) (hb ω) hb0 hx hy
    have hT0 : 0 ≤ X.passTime ω x y := Profiles.passTime_nonneg ω x y
    have hd : dist x y ≤ 6 * R := by
      linarith only [dist_le_three_mul_width sl hw hs, not_le.mp hRs]
    have hdist : b * dist x y ≤ b * (6 * R) := mul_le_mul_of_nonneg_left hd hb0
    change X.slabTime b sl ω x y ≤ b * dist x y at hupper
    linarith only [hupper, hT0, hdist]

/-- **Equation `eq:slab` on one outcome**, for the two orders of the faces. -/
theorem slab_pair_bound (X : Setting m) (ω : X.Ω) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) (hw : 0 < sl.width) {z x y : Pt m} (hp : IsSlabPair sl z x y)
    {B : Set (Pt m)} {R : ℝ} (hstraight : StraightOn X ω B R) (hxB : x ∈ B) (hyB : y ∈ B)
    (hR : 9 ≤ R) : X.slabTime b sl ω x y - X.passTime ω x y ≤ 6 * b * R + 1 := by
  obtain ⟨hf, -, hd⟩ := hp
  rw [← dist_eq_norm'] at hd
  rcases hf with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact slabTime_sub_passTime_le X ω hb sl hw hx hy (slope_le_two_of_dist_le sl hw hd)
      hstraight hxB hyB hR
  · rw [slabTime_comm X hb sl ω (face₁_subset_slab sl hw.le hx) (face₀_subset_slab sl hw.le hy),
      Profiles.passTime_comm ω x y]
    exact slabTime_sub_passTime_le X ω hb sl hw hy hx
      (slope_le_two_of_dist_le sl hw (by rwa [dist_comm])) hstraight hyB hxB hR

/-- **The supremum of equation `eq:slab` is a random variable**: the two passage times are
continuous in the pair, and the set of pairs is separable. -/
theorem aemeasurable_iSup_slabPair (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m)
    (hw : 0 ≤ sl.width) (z : Pt m) :
    AEMeasurable (fun ω => ⨆ p : {p : Pt m × Pt m // IsSlabPair sl z p.1 p.2},
      (X.slabTime b sl ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2)) X.P := by
  obtain ⟨B, -, hB⟩ := Profiles.exists_upperBound X
  have hmem (p : {p : Pt m × Pt m // IsSlabPair sl z p.1 p.2}) :
      p.1.1 ∈ sl.set ∧ p.1.2 ∈ sl.set := by
    rcases p.2.1 with h | h
    · exact ⟨face₀_subset_slab sl hw h.1, face₁_subset_slab sl hw h.2⟩
    · exact ⟨face₁_subset_slab sl hw h.1, face₀_subset_slab sl hw h.2⟩
  refine Profiles.aemeasurable_iSup_of_continuous (fun ω => ?_)
    (fun ω => ⟨b * (Real.sqrt 5 * sl.width), ?_⟩)
    (fun p => (aemeasurable_slabTime X hb sl _ _).sub (Profiles.aemeasurable_passTime _ _))
  · have heq : (fun p : {p : Pt m × Pt m // IsSlabPair sl z p.1 p.2} =>
        X.slabTime b sl ω p.1.1 p.1.2) = fun p =>
          passageTime (extDensity sl b (X.ρ ω)) p.1.1 p.1.2 :=
      funext fun p => slabTime_eq_passageTime_ext X hb sl ω (hmem p).1 (hmem p).2
    have h₁ : Continuous fun p : {p : Pt m × Pt m // IsSlabPair sl z p.1 p.2} =>
        X.slabTime b sl ω p.1.1 p.1.2 := by
      rw [heq]
      exact (Profiles.continuous_passageTime
        (measurable_extDensity sl b (Profiles.measurable_ρ_apply X ω))
        (extDensity_le sl (hb ω))).comp continuous_subtype_val
    exact h₁.sub ((Profiles.continuous_passTime hB ω).comp continuous_subtype_val)
  · rintro _ ⟨p, rfl⟩
    have h := Infra.Slab.slabTime_le_mul_dist X hb sl ω (hmem p).1 (hmem p).2
    have hd : dist p.1.1 p.1.2 ≤ Real.sqrt 5 * sl.width :=
      (dist_eq_norm' _ _).trans_le p.2.2.2
    have hmul := mul_le_mul_of_nonneg_left hd (upperBound_nonneg X hb ω)
    have hT0 : 0 ≤ X.passTime ω p.1.1 p.1.2 := Profiles.passTime_nonneg ω _ _
    change X.slabTime b sl ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2 ≤ _
    linarith only [h, hmul, hT0]

end IsotropicVariance.Paper.Proofs.SlabComparison
