/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Geometry
public import IsotropicVariance.Infra.Geometry.PtCoords
public import IsotropicVariance.Infra.Curves.Concat
public import IsotropicVariance.Infra.Curves.Bounds
public import IsotropicVariance.Infra.Curves.LipschitzBounds
import Mathlib.Tactic.Linarith

/-!
# Restricted passage times are Lipschitz in their endpoints

For a closed convex set `S` (a slab, or the whole space) and a measurable density bounded above
by `B ≥ 0`, the passage time over the curves in `S` is at most `B|u − v|`, and moving an endpoint
inside `S` by `r` changes it by at most `Br`: a segment in `S` is prepended or appended. These are
the facts behind the existence of the minimizing points of the slab minimum (equation `eq:F`),
proved in `IsotropicVariance.Paper.Defs.Minimum` (`exists_isLexLeastMinimizer`). Also the
coordinate `t = x · e₁` and the slabs `[a, a + s] × ℝ^m`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace IsotropicVariance.Paper

variable {m : ℕ}

namespace Pt

lemma continuous_lon : Continuous (lon : Pt m → ℝ) := by
  unfold lon
  fun_prop

end Pt

/-- The slab `[a, a + s] × ℝ^m` in coordinates. -/
lemma e1Slab_set (a s : ℝ) :
    (e1Slab (m := m) a s).set = {x | a ≤ Pt.lon x ∧ Pt.lon x ≤ a + s} := by
  ext x
  simp only [Slab.set, e1Slab, AffineIsometryEquiv.coe_constVAdd, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
    simp only [vadd_eq_add, Pt.lon_add, Pt.lon_smul, Pt.lon_e₁, mul_one]
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    refine ⟨x - a • e₁, ⟨?_, ?_⟩, by simp⟩ <;>
      simp only [Pt.lon_sub, Pt.lon_smul, Pt.lon_e₁, mul_one] <;> linarith

lemma convex_e1Slab_set (a s : ℝ) : Convex ℝ (e1Slab (m := m) a s).set := by
  rw [e1Slab_set]
  intro x hx y hy p q hp hq hpq
  obtain rfl : q = 1 - p := by linarith
  simp only [mem_ofPred_eq, Pt.lon_add, Pt.lon_smul] at hx hy ⊢
  constructor <;> nlinarith [mul_nonneg hp (sub_nonneg.2 hx.1), mul_nonneg hq (sub_nonneg.2 hy.1),
    mul_nonneg hp (sub_nonneg.2 hx.2), mul_nonneg hq (sub_nonneg.2 hy.2)]

/-- The slab density is measurable when the density is. -/
lemma Slab.measurable_density (sl : Slab m) (b : ℝ) {σ : Pt m → ℝ} (hσ : Measurable σ) :
    Measurable (sl.density b σ) :=
  Measurable.ite (measurableSet_le (continuous_infDist_pt _).measurable measurable_const)
    measurable_const hσ

/-- The slab density is bounded by the larger of `b` and a bound of the density. -/
lemma Slab.density_le (sl : Slab m) (b : ℝ) {σ : Pt m → ℝ} {B : ℝ} (hB : ∀ x, σ x ≤ B)
    (x : Pt m) : sl.density b σ x ≤ max b B := by
  unfold Slab.density
  split_ifs
  · exact le_max_left _ _
  · exact (hB x).trans (le_max_right _ _)

/-- The infimum defining the restricted passage time, in `[0, ∞]`. -/
noncomputable def restrictedInf (σ : Pt m → ℝ) (S : Set (Pt m)) (u v : Pt m) : ℝ≥0∞ :=
  ⨅ (γ : RectifiableCurve (Pt m)) (_ : γ.toFun 0 = u) (_ : γ.toFun 1 = v)
      (_ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S),
    γ.cost (fun x => ENNReal.ofReal (σ x))

lemma restrictedPassageTime_eq_toReal (σ : Pt m → ℝ) (S : Set (Pt m)) (u v : Pt m) :
    restrictedPassageTime σ S u v = (restrictedInf σ S u v).toReal := rfl

lemma restrictedPassageTime_nonneg (σ : Pt m → ℝ) (S : Set (Pt m)) (u v : Pt m) :
    0 ≤ restrictedPassageTime σ S u v :=
  ENNReal.toReal_nonneg

lemma restrictedInf_le_cost {σ : Pt m → ℝ} {S : Set (Pt m)} {u v : Pt m}
    (γ : RectifiableCurve (Pt m)) (h0 : γ.toFun 0 = u) (h1 : γ.toFun 1 = v)
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S) :
    restrictedInf σ S u v ≤ γ.cost (fun x => ENNReal.ofReal (σ x)) :=
  (iInf_le _ γ).trans <| (iInf_le _ h0).trans <| (iInf_le _ h1).trans <| iInf_le _ hS

private lemma segment_toFun (u v : Pt m) (t : ℝ) :
    (Infra.Curves.segment u v).toRectifiable.toFun t = u + t • (v - u) := rfl

private lemma segment_start (u v : Pt m) : (Infra.Curves.segment u v).toRectifiable.toFun 0 = u := by
  rw [segment_toFun]; simp

private lemma segment_end (u v : Pt m) : (Infra.Curves.segment u v).toRectifiable.toFun 1 = v := by
  rw [segment_toFun]; simp

/-- A segment as a rectifiable curve costs at most `B` times its length. -/
private lemma segment_cost_le {σ : Pt m → ℝ} {B : ℝ} (hB : ∀ x, σ x ≤ B) (u v : Pt m) :
    (Infra.Curves.segment u v).toRectifiable.cost (fun x => ENNReal.ofReal (σ x)) ≤
      ENNReal.ofReal B * edist u v := by
  refine ((Infra.Curves.segment u v).toRectifiable.cost_le_mul_length
    (b := ENNReal.ofReal B) fun x => ENNReal.ofReal_le_ofReal (hB x)).trans_eq ?_
  rw [Infra.Curves.rectifiable_length_segment, edist_comm, edist_eq_enorm_sub]

private lemma segment_mem {S : Set (Pt m)} (hS : Convex ℝ S) {u v : Pt m} (hu : u ∈ S)
    (hv : v ∈ S) (t : ℝ) : (Infra.Curves.segment u v).toRectifiable.clamped t ∈ S :=
  Infra.Curves.segment_mem_of_convex hS hu hv _ (projIcc 0 1 zero_le_one t).2

/-- The restricted passage time is at most `B |u − v|`. -/
lemma restrictedInf_le {σ : Pt m → ℝ} {B : ℝ} (hB : ∀ x, σ x ≤ B) {S : Set (Pt m)}
    (hS : Convex ℝ S) {u v : Pt m} (hu : u ∈ S) (hv : v ∈ S) :
    restrictedInf σ S u v ≤ ENNReal.ofReal B * edist u v := by
  refine (restrictedInf_le_cost _ (segment_start u v) (segment_end u v)
    fun t ht => ?_).trans (segment_cost_le hB u v)
  exact Infra.Curves.segment_mem_of_convex hS hu hv t ht

lemma restrictedInf_ne_top {σ : Pt m → ℝ} {B : ℝ} (hB : ∀ x, σ x ≤ B) {S : Set (Pt m)}
    (hS : Convex ℝ S) {u v : Pt m} (hu : u ∈ S) (hv : v ∈ S) : restrictedInf σ S u v ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top u v))
    (restrictedInf_le hB hS hu hv)

/-- Prepending a segment in `S`. -/
lemma restrictedInf_prepend {σ : Pt m → ℝ} (hσ : Measurable σ) {B : ℝ} (hB : ∀ x, σ x ≤ B)
    {S : Set (Pt m)} (hS : Convex ℝ S) {u u' v : Pt m} (hu' : u' ∈ S) (hu : u ∈ S) :
    restrictedInf σ S u' v ≤ ENNReal.ofReal B * edist u' u + restrictedInf σ S u v := by
  simp only [restrictedInf, ENNReal.add_iInf]
  refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hγ => ?_
  set δ := (Infra.Curves.segment u' u).toRectifiable
  have hend : δ.toFun 1 = γ.toFun 0 := by rw [segment_end, h0]
  have hρ : Measurable fun x => ENNReal.ofReal (σ x) := ENNReal.measurable_ofReal.comp hσ
  refine (iInf_le _ (δ.concat γ hend)).trans ?_
  refine (iInf_le _ ?_).trans <| (iInf_le _ ?_).trans <| (iInf_le _ ?_).trans ?_
  · rw [RectifiableCurve.concat_start, segment_start]
  · rw [RectifiableCurve.concat_end, h1]
  · intro t ht
    change RectifiableCurve.concatFun δ γ t ∈ S
    rcases le_total t (1 / 2) with h | h
    · rw [RectifiableCurve.concatFun_left _ _ h]
      exact segment_mem hS hu' hu _
    · rw [RectifiableCurve.concatFun_right _ _ hend h]
      exact hγ _ (projIcc 0 1 zero_le_one _).2
  · rw [RectifiableCurve.cost_concat _ _ hend hρ]
    exact add_le_add (segment_cost_le hB u' u) le_rfl

/-- Appending a segment in `S`. -/
lemma restrictedInf_append {σ : Pt m → ℝ} (hσ : Measurable σ) {B : ℝ} (hB : ∀ x, σ x ≤ B)
    {S : Set (Pt m)} (hS : Convex ℝ S) {u v v' : Pt m} (hv : v ∈ S) (hv' : v' ∈ S) :
    restrictedInf σ S u v' ≤ restrictedInf σ S u v + ENNReal.ofReal B * edist v v' := by
  simp only [restrictedInf, ENNReal.iInf_add]
  refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hγ => ?_
  set δ := (Infra.Curves.segment v v').toRectifiable
  have hend : γ.toFun 1 = δ.toFun 0 := by rw [segment_start, h1]
  have hρ : Measurable fun x => ENNReal.ofReal (σ x) := ENNReal.measurable_ofReal.comp hσ
  refine (iInf_le _ (γ.concat δ hend)).trans ?_
  refine (iInf_le _ ?_).trans <| (iInf_le _ ?_).trans <| (iInf_le _ ?_).trans ?_
  · rw [RectifiableCurve.concat_start, h0]
  · rw [RectifiableCurve.concat_end, segment_end]
  · intro t ht
    change RectifiableCurve.concatFun γ δ t ∈ S
    rcases le_total t (1 / 2) with h | h
    · rw [RectifiableCurve.concatFun_left _ _ h]
      exact hγ _ (projIcc 0 1 zero_le_one _).2
    · rw [RectifiableCurve.concatFun_right _ _ hend h]
      exact segment_mem hS hv hv' _
  · rw [RectifiableCurve.cost_concat _ _ hend hρ]
    exact add_le_add le_rfl (segment_cost_le hB v v')

/-- **Restricted passage times are Lipschitz in their endpoints** inside a convex set, for a
measurable density bounded by `B ≥ 0`. -/
lemma restrictedPassageTime_le_add {σ : Pt m → ℝ} (hσ : Measurable σ) {B : ℝ}
    (hB : ∀ x, σ x ≤ B) (hB0 : 0 ≤ B) {S : Set (Pt m)} (hS : Convex ℝ S) {u u' v v' : Pt m}
    (hu : u ∈ S) (hu' : u' ∈ S) (hv : v ∈ S) (hv' : v' ∈ S) :
    restrictedPassageTime σ S u' v' ≤
      restrictedPassageTime σ S u v + B * (dist u' u + dist v v') := by
  rw [restrictedPassageTime_eq_toReal, restrictedPassageTime_eq_toReal]
  have h1 := restrictedInf_prepend hσ hB hS (v := v') hu' hu
  have h2 := restrictedInf_append hσ hB hS (u := u) hv hv'
  have hfin := restrictedInf_ne_top hB hS hu hv
  have hle : restrictedInf σ S u' v' ≤
      restrictedInf σ S u v + ENNReal.ofReal (B * (dist u' u + dist v v')) := by
    refine h1.trans ((add_le_add le_rfl h2).trans_eq ?_)
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_mul hB0, mul_add,
      ENNReal.ofReal_add (by positivity) (by positivity)]
    ring
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) hle).trans ?_
  rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)]

/-- The two-sided form. -/
lemma abs_restrictedPassageTime_sub_le {σ : Pt m → ℝ} (hσ : Measurable σ) {B : ℝ}
    (hB : ∀ x, σ x ≤ B) (hB0 : 0 ≤ B) {S : Set (Pt m)} (hS : Convex ℝ S) {u u' v v' : Pt m}
    (hu : u ∈ S) (hu' : u' ∈ S) (hv : v ∈ S) (hv' : v' ∈ S) :
    |restrictedPassageTime σ S u v - restrictedPassageTime σ S u' v'| ≤
      B * (dist u u' + dist v v') := by
  have h1 := restrictedPassageTime_le_add hσ hB hB0 hS hu hu' hv hv'
  have h2 := restrictedPassageTime_le_add hσ hB hB0 hS hu' hu hv' hv
  rw [abs_le]
  rw [dist_comm u' u] at h1
  rw [dist_comm v' v] at h2
  constructor <;> linarith

end IsotropicVariance.Paper
