/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum
public import IsotropicVariance.Infra.Measurability.PassageBounds
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith

/-!
# The slab passage time is a passage time of an extended density

The slab passage time `D(u, v)` of equation `eq:slabtime` is the infimum of the costs of the
curves from `u` to `v` that stay in the slab, for the slab density (the upper bound `b` within
distance one of the faces, the density `ρ` elsewhere). Extend the slab density by `b` outside the
slab (`extDensity`). Then, for endpoints in the slab, `D(u, v)` is the unrestricted passage time
of the extended density (`passTime_eq_passageTime_extDensity`):

* a curve in the slab has the same cost for both densities;
* conversely, composing a curve with the nearest-point projection `slabProj` onto the slab (clamp
  the coordinate across the slab) gives a curve in the slab with the same endpoints, whose
  arc-length measure is at most that of the curve (the projection is `1`-Lipschitz,
  `arcLengthMeasure_mapCurve_le`), and the extended density does not increase under the
  projection (the projection maps each point outside the slab to a face, where the slab density
  is `b`).

Through this identity the triangle inequality, the endpoint Lipschitz bound and the measurability of
the passage times of `IsotropicVariance.Infra.Measurability` apply to `D`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace IsotropicVariance.Infra.Slab

open IsotropicVariance.Paper

/-- The passage time `IsotropicVariance.passageTime` is the real part of the passage time
`Infra.Measurability.passageTime` of the density `x ↦ ofReal (σ x)`, over the same curves. -/
lemma passageTime_eq_infra {m : ℕ} (σ : Pt m → ℝ) (u v : Pt m) :
    passageTime σ u v =
      (Infra.Measurability.passageTime (fun x => ENNReal.ofReal (σ x)) u v).toReal := rfl

/-! ## Curves composed with `1`-Lipschitz maps -/

section MapCurve

variable {E : Type*} [PseudoMetricSpace E]

/-- The image of a rectifiable curve under a `1`-Lipschitz map. -/
def mapCurve (f : E → E) (hf : LipschitzWith 1 f) (γ : RectifiableCurve E) :
    RectifiableCurve E where
  toFun := f ∘ γ.toFun
  continuousOn := hf.continuous.comp_continuousOn γ.continuousOn
  boundedVariationOn := hf.comp_boundedVariationOn γ.boundedVariationOn

@[simp]
lemma mapCurve_toFun (f : E → E) (hf : LipschitzWith 1 f) (γ : RectifiableCurve E)
    (t : ℝ) : (mapCurve f hf γ).toFun t = f (γ.toFun t) := rfl

/-- The length of the image curve along any parameter interval is at most that of the curve. -/
lemma cumulativeLength_mapCurve_sub_le (f : E → E) (hf : LipschitzWith 1 f)
    (γ : RectifiableCurve E) {s t : ℝ} (hst : s ≤ t) :
    (mapCurve f hf γ).cumulativeLength t - (mapCurve f hf γ).cumulativeLength s ≤
      γ.cumulativeLength t - γ.cumulativeLength s := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have hs' := (projIcc 0 1 zero_le_one s).2
  have ht' := (projIcc 0 1 zero_le_one t).2
  have hst' : (projIcc 0 1 zero_le_one s : ℝ) ≤ projIcc 0 1 zero_le_one t :=
    monotone_projIcc zero_le_one hst
  have hγ := γ.boundedVariationOn.locallyBoundedVariationOn
  have hδ := (mapCurve f hf γ).boundedVariationOn.locallyBoundedVariationOn
  simp only [RectifiableCurve.cumulativeLength]
  rw [variationOnFromTo.sub_right hγ h0 ht' hs', variationOnFromTo.sub_right hδ h0 ht' hs',
    variationOnFromTo.eq_of_le _ _ hst', variationOnFromTo.eq_of_le _ _ hst']
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top γ.boundedVariationOn (eVariationOn.mono _ inter_subset_left)
  · have h := (hf.lipschitzOnWith (s := univ)).comp_eVariationOn_le
      (mapsTo_univ γ.toFun (Icc 0 1 ∩ Icc (projIcc 0 1 zero_le_one s : ℝ)
        (projIcc 0 1 zero_le_one t)))
    rw [ENNReal.coe_one, one_mul] at h
    exact h

/-- The arc-length measure of the image of a curve under a `1`-Lipschitz map is at most the
arc-length measure of the curve: the difference of the two cumulative lengths is nondecreasing,
so it is a Stieltjes function, and Stieltjes measures are additive. -/
lemma arcLengthMeasure_mapCurve_le (f : E → E) (hf : LipschitzWith 1 f)
    (γ : RectifiableCurve E) :
    (mapCurve f hf γ).arcLengthMeasure ≤ γ.arcLengthMeasure := by
  set δ := mapCurve f hf γ
  let H : StieltjesFunction ℝ :=
    { toFun := fun t => γ.cumulativeLength t - δ.cumulativeLength t
      mono' := fun s t hst => by
        have := cumulativeLength_mapCurve_sub_le f hf γ hst
        linarith
      right_continuous' := fun t =>
        (γ.continuous_cumulativeLength.sub δ.continuous_cumulativeLength).continuousAt
          |>.continuousWithinAt }
  have hsum : γ.lengthFunction = δ.lengthFunction + H := by
    refine StieltjesFunction.ext fun t => ?_
    rw [StieltjesFunction.add_apply]
    change γ.cumulativeLength t = δ.cumulativeLength t +
      (γ.cumulativeLength t - δ.cumulativeLength t)
    ring
  unfold RectifiableCurve.arcLengthMeasure
  rw [hsum, StieltjesFunction.measure_add]
  exact Measure.le_add_right le_rfl

/-- The cost of the image curve for `ρ` is at most the cost of the curve for `σ` when
`ρ ∘ f ≤ σ`. -/
lemma cost_mapCurve_le (f : E → E) (hf : LipschitzWith 1 f)
    (γ : RectifiableCurve E) {ρ σ : E → ℝ≥0∞} (h : ∀ x, ρ (f x) ≤ σ x) :
    (mapCurve f hf γ).cost ρ ≤ γ.cost σ :=
  lintegral_mono' (arcLengthMeasure_mapCurve_le f hf γ) fun t => h (γ.toFun t)

end MapCurve

/-! ## Slab geometry -/

variable {m : ℕ}

/-- The first coordinate is `1`-Lipschitz. -/
lemma abs_lon_sub_le (x y : Pt m) : |Pt.lon x - Pt.lon y| ≤ dist x y := by
  rw [WithLp.prod_dist_eq_of_L2]
  apply Real.abs_le_sqrt
  have h : dist x.fst y.fst = |Pt.lon x - Pt.lon y| := Real.dist_eq _ _
  rw [h, sq_abs]
  nlinarith [sq_nonneg (dist x.snd y.snd)]

/-- Two points with the same transverse coordinates are at the distance of their first
coordinates. -/
lemma dist_eq_abs_lon_sub {x y : Pt m} (h : Pt.tr x = Pt.tr y) :
    dist x y = |Pt.lon x - Pt.lon y| := by
  rw [WithLp.prod_dist_eq_of_L2]
  have h1 : dist x.fst y.fst = |Pt.lon x - Pt.lon y| := Real.dist_eq _ _
  have h2 : x.snd = y.snd := h
  rw [h1, h2, dist_self, sq_abs]
  simp [Real.sqrt_sq_eq_abs]

/-- The coordinate across the slab: the first coordinate in the frame of the slab. -/
noncomputable def slabCoord (sl : Slab m) (x : Pt m) : ℝ :=
  Pt.lon (sl.motion.symm x)

/-- The coordinate across the slab, as an affine map. -/
noncomputable def slabCoordAffine (sl : Slab m) : Pt m →ᵃ[ℝ] ℝ :=
  (WithLp.fstₗ 2 ℝ ℝ (EuclideanSpace ℝ (Fin m))).toAffineMap.comp sl.motion.symm.toAffineMap

lemma lipschitzWith_slabCoord (sl : Slab m) : LipschitzWith 1 (slabCoord sl) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, slabCoord, slabCoord,
      ← sl.motion.symm.dist_map x y]
    exact abs_lon_sub_le _ _

lemma continuous_slabCoord (sl : Slab m) : Continuous (slabCoord sl) :=
  (lipschitzWith_slabCoord sl).continuous

lemma mem_slab_set_iff (sl : Slab m) {x : Pt m} :
    x ∈ sl.set ↔ 0 ≤ slabCoord sl x ∧ slabCoord sl x ≤ sl.width := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [slabCoord] using hz
  · intro h
    exact ⟨sl.motion.symm x, h, sl.motion.apply_symm_apply x⟩

lemma mem_slab_faces_iff (sl : Slab m) {x : Pt m} :
    x ∈ sl.faces ↔ slabCoord sl x = 0 ∨ slabCoord sl x = sl.width := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [slabCoord] using hz
  · intro h
    exact ⟨sl.motion.symm x, h, sl.motion.apply_symm_apply x⟩

/-- The slab is the preimage of `[0, width]` under the coordinate across it. -/
lemma slab_set_eq_preimage (sl : Slab m) : sl.set = slabCoord sl ⁻¹' Icc 0 sl.width := by
  ext x
  rw [mem_slab_set_iff]
  rfl

lemma isClosed_slab_set (sl : Slab m) : IsClosed sl.set := by
  rw [slab_set_eq_preimage]
  exact isClosed_Icc.preimage (continuous_slabCoord sl)

lemma measurableSet_slab_set (sl : Slab m) : MeasurableSet sl.set :=
  (isClosed_slab_set sl).measurableSet

lemma convex_slab_set (sl : Slab m) : Convex ℝ sl.set := by
  rw [slab_set_eq_preimage]
  exact (convex_Icc 0 sl.width).affine_preimage (slabCoordAffine sl)

lemma width_nonneg_of_mem (sl : Slab m) {x : Pt m} (hx : x ∈ sl.set) : 0 ≤ sl.width := by
  rw [mem_slab_set_iff] at hx
  exact hx.1.trans hx.2

/-! ## The projection onto the slab -/

/-- Clamping to `[0, w]`. -/
def clampTo (w t : ℝ) : ℝ := max 0 (min w t)

lemma abs_clampTo_sub_le (w s t : ℝ) : |clampTo w s - clampTo w t| ≤ |s - t| := by
  unfold clampTo
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

lemma clampTo_of_mem {w t : ℝ} (h : t ∈ Icc 0 w) : clampTo w t = t := by
  simp [clampTo, h.1, h.2]

lemma clampTo_mem {w : ℝ} (hw : 0 ≤ w) (t : ℝ) : clampTo w t ∈ Icc 0 w :=
  ⟨le_max_left _ _, max_le hw (min_le_left _ _)⟩

lemma clampTo_eq_zero_or_eq {w t : ℝ} (hw : 0 ≤ w) (h : t ∉ Icc 0 w) :
    clampTo w t = 0 ∨ clampTo w t = w := by
  simp only [mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · left
    simp [clampTo, min_eq_right_of_lt (h.trans_le hw), h.le]
  · right
    simp [clampTo, min_eq_left h.le, hw]

/-- The nearest-point projection onto the slab: clamp the coordinate across the slab. -/
noncomputable def slabProj (sl : Slab m) (x : Pt m) : Pt m :=
  sl.motion (WithLp.toLp 2 (clampTo sl.width (slabCoord sl x), Pt.tr (sl.motion.symm x)))

lemma slabCoord_slabProj (sl : Slab m) (x : Pt m) :
    slabCoord sl (slabProj sl x) = clampTo sl.width (slabCoord sl x) := by
  simp [slabCoord, slabProj, Pt.lon]

lemma slabProj_mem (sl : Slab m) (hw : 0 ≤ sl.width) (x : Pt m) : slabProj sl x ∈ sl.set := by
  rw [mem_slab_set_iff, slabCoord_slabProj]
  exact clampTo_mem hw _

lemma slabProj_eq_self (sl : Slab m) {x : Pt m} (hx : x ∈ sl.set) : slabProj sl x = x := by
  rw [mem_slab_set_iff] at hx
  rw [slabProj, clampTo_of_mem hx]
  conv_rhs => rw [← sl.motion.apply_symm_apply x]
  rfl

lemma slabProj_mem_faces (sl : Slab m) (hw : 0 ≤ sl.width) {x : Pt m} (hx : x ∉ sl.set) :
    slabProj sl x ∈ sl.faces := by
  rw [slab_set_eq_preimage] at hx
  rw [mem_slab_faces_iff, slabCoord_slabProj]
  exact clampTo_eq_zero_or_eq hw hx

/-- The projection onto the slab is `1`-Lipschitz. -/
lemma lipschitzWith_slabProj (sl : Slab m) : LipschitzWith 1 (slabProj sl) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, slabProj, slabProj, sl.motion.dist_map,
      ← sl.motion.symm.dist_map x y, WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
    apply Real.sqrt_le_sqrt
    have h : dist (clampTo sl.width (slabCoord sl x)) (clampTo sl.width (slabCoord sl y)) ≤
        dist (sl.motion.symm x).fst (sl.motion.symm y).fst := by
      rw [Real.dist_eq, Real.dist_eq]
      exact abs_clampTo_sub_le _ _ _
    have h' := pow_le_pow_left₀ dist_nonneg h 2
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    change dist (clampTo sl.width (slabCoord sl x)) (clampTo sl.width (slabCoord sl y)) ^ 2 +
        dist (sl.motion.symm x).snd (sl.motion.symm y).snd ^ 2 ≤ _
    linarith

/-! ## The extended density -/

open scoped Classical in
/-- The slab density extended by the upper bound `b` outside the slab. -/
noncomputable def extDensity (sl : Slab m) (b : ℝ) (σ : Pt m → ℝ) (x : Pt m) : ℝ :=
  if x ∈ sl.set then sl.density b σ x else b

lemma extDensity_of_mem (sl : Slab m) (b : ℝ) (σ : Pt m → ℝ) {x : Pt m} (hx : x ∈ sl.set) :
    extDensity sl b σ x = sl.density b σ x := by
  simp [extDensity, hx]

lemma extDensity_of_notMem (sl : Slab m) (b : ℝ) (σ : Pt m → ℝ) {x : Pt m} (hx : x ∉ sl.set) :
    extDensity sl b σ x = b := by
  simp [extDensity, hx]

lemma density_of_mem_faces (sl : Slab m) (b : ℝ) (σ : Pt m → ℝ) {x : Pt m}
    (hx : x ∈ sl.faces) : sl.density b σ x = b := by
  simp [Slab.density, infDist_zero_of_mem hx]

/-- The extended density does not increase under the projection onto the slab. -/
lemma extDensity_slabProj (sl : Slab m) (hw : 0 ≤ sl.width) (b : ℝ) (σ : Pt m → ℝ)
    (x : Pt m) : extDensity sl b σ (slabProj sl x) = extDensity sl b σ x := by
  by_cases hx : x ∈ sl.set
  · rw [slabProj_eq_self sl hx]
  · rw [extDensity_of_mem sl b σ (slabProj_mem sl hw x),
      density_of_mem_faces sl b σ (slabProj_mem_faces sl hw hx), extDensity_of_notMem sl b σ hx]

lemma extDensity_le (sl : Slab m) {b : ℝ} {σ : Pt m → ℝ} (hσ : ∀ x, σ x ≤ b) (x : Pt m) :
    extDensity sl b σ x ≤ b := by
  unfold extDensity Slab.density
  split_ifs <;> simp [hσ]

lemma measurable_extDensity (sl : Slab m) (b : ℝ) {σ : Pt m → ℝ} (hσ : Measurable σ) :
    Measurable (extDensity sl b σ) := by
  unfold extDensity Slab.density
  refine Measurable.ite (measurableSet_slab_set sl) (Measurable.ite ?_ measurable_const hσ)
    measurable_const
  exact measurableSet_le (continuous_infDist_pt _).measurable measurable_const

/-- The extended density of the density of a setting is jointly measurable. -/
lemma measurable_extDensity_uncurry {Ω : Type*} [MeasurableSpace Ω] (sl : Slab m) (b : ℝ)
    {ρ : Ω → Pt m → ℝ} (hρ : Measurable (Function.uncurry ρ)) :
    Measurable fun p : Ω × Pt m => extDensity sl b (ρ p.1) p.2 := by
  unfold extDensity Slab.density
  refine Measurable.ite ((measurableSet_slab_set sl).preimage measurable_snd)
    (Measurable.ite ?_ measurable_const hρ) measurable_const
  exact measurableSet_le ((continuous_infDist_pt _).measurable.comp measurable_snd)
    measurable_const

/-! ## The slab passage time as a passage time -/

/-- **The slab passage time is the passage time of the extended density.** For endpoints in the
slab, the infimum of the costs of the curves in the slab for the slab density equals the
infimum of the costs of all curves for the slab density extended by `b` outside the slab. -/
theorem passTime_eq_passageTime_extDensity (sl : Slab m) (b : ℝ) (σ : Pt m → ℝ) {u v : Pt m}
    (hu : u ∈ sl.set) (hv : v ∈ sl.set) :
    sl.passTime b σ u v = passageTime (extDensity sl b σ) u v := by
  have hw := width_nonneg_of_mem sl hu
  unfold Slab.passTime restrictedPassageTime passageTime
  congr 1
  apply le_antisymm
  · refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => ?_
    let δ := mapCurve (slabProj sl) (lipschitzWith_slabProj sl) γ
    have hδ0 : δ.toFun 0 = u := by
      rw [mapCurve_toFun, h0, slabProj_eq_self sl hu]
    have hδ1 : δ.toFun 1 = v := by
      rw [mapCurve_toFun, h1, slabProj_eq_self sl hv]
    have hδS : ∀ t ∈ Icc (0 : ℝ) 1, δ.toFun t ∈ sl.set :=
      fun t _ => slabProj_mem sl hw _
    refine iInf_le_of_le δ (iInf_le_of_le hδ0 (iInf_le_of_le hδ1 (iInf_le_of_le hδS ?_)))
    calc δ.cost (fun x => ENNReal.ofReal (sl.density b σ x))
        = δ.cost (fun x => ENNReal.ofReal (extDensity sl b σ x)) :=
          δ.cost_congr fun t ht => congrArg ENNReal.ofReal
            (extDensity_of_mem sl b σ (hδS t ht)).symm
      _ ≤ γ.cost (fun x => ENNReal.ofReal (extDensity sl b σ x)) :=
          cost_mapCurve_le _ _ _ fun x => by rw [extDensity_slabProj sl hw]
  · refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hS => ?_
    refine iInf_le_of_le γ (iInf_le_of_le h0 (iInf_le_of_le h1 ?_))
    exact (γ.cost_congr fun t ht =>
      congrArg ENNReal.ofReal (extDensity_of_mem sl b σ (hS t ht))).le

/-- For an endpoint outside the slab there is no curve in the slab: the slab passage time is
`(⊤).toReal = 0`. -/
lemma passTime_of_not_mem (sl : Slab m) (b : ℝ) (σ : Pt m → ℝ) {u v : Pt m}
    (h : u ∉ sl.set ∨ v ∉ sl.set) : sl.passTime b σ u v = 0 := by
  unfold Slab.passTime restrictedPassageTime
  rw [iInf_eq_top.mpr, ENNReal.toReal_top]
  intro γ
  refine iInf_eq_top.mpr fun h0 => iInf_eq_top.mpr fun h1 => iInf_eq_top.mpr fun hS => ?_
  exfalso
  rcases h with h | h
  · exact h (h0 ▸ hS 0 (left_mem_Icc.2 zero_le_one))
  · exact h (h1 ▸ hS 1 (right_mem_Icc.2 zero_le_one))

/-! ## Consequences for the slab passage times of a setting -/

variable (X : Setting m)

lemma ofReal_extDensity_le {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) (ω : X.Ω)
    (x : Pt m) : ENNReal.ofReal (extDensity sl b (X.ρ ω) x) ≤ (b.toNNReal : ℝ≥0∞) :=
  ENNReal.ofReal_le_ofReal (extDensity_le sl (hb ω) x)

lemma measurable_ofReal_extDensity (b : ℝ) (sl : Slab m) (ω : X.Ω) :
    Measurable fun x => ENNReal.ofReal (extDensity sl b (X.ρ ω) x) :=
  (measurable_extDensity sl b (X.measurable_ρ.comp (measurable_const.prodMk measurable_id))
    ).ennreal_ofReal

lemma upperBound_nonneg {b : ℝ} (hb : X.IsUpperBound b) (ω : X.Ω) : 0 ≤ b := by
  obtain ⟨a, _, ha, hab⟩ := X.bounds
  exact ha.le.trans ((hab ω 0).1.trans (hb ω 0))

/-- The slab passage time of a setting, for endpoints in the slab, is the passage time of the
extended density. -/
theorem slabTime_eq_passageTime_ext {b : ℝ} (_hb : X.IsUpperBound b) (sl : Slab m) (ω : X.Ω)
    {u v : Pt m} (hu : u ∈ sl.set) (hv : v ∈ sl.set) :
    X.slabTime b sl ω u v = passageTime (extDensity sl b (X.ρ ω)) u v :=
  passTime_eq_passageTime_extDensity sl b (X.ρ ω) hu hv

lemma slabTime_eq_infra {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) (ω : X.Ω) {u v : Pt m}
    (hu : u ∈ sl.set) (hv : v ∈ sl.set) :
    X.slabTime b sl ω u v = (Infra.Measurability.passageTime
      (fun x => ENNReal.ofReal (extDensity sl b (X.ρ ω) x)) u v).toReal := by
  rw [slabTime_eq_passageTime_ext X hb sl ω hu hv, passageTime_eq_infra]

/-- The slab passage time is at most `b` times the distance (the segment stays in the convex
slab; here it follows from the identity with the extended density). -/
theorem slabTime_le_mul_dist {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) (ω : X.Ω)
    {u v : Pt m} (hu : u ∈ sl.set) (hv : v ∈ sl.set) :
    X.slabTime b sl ω u v ≤ b * dist u v := by
  have hb0 := upperBound_nonneg X hb ω
  rw [slabTime_eq_infra X hb sl ω hu hv]
  have h := Infra.Measurability.passageTime_le_edist (ofReal_extDensity_le X hb sl ω) u v
  have hne : ((b.toNNReal : ℝ≥0∞) * edist u v) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)
  refine (ENNReal.toReal_mono hne h).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ hb0, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]

/-- **The endpoint Lipschitz bound for the slab passage time.** -/
theorem abs_slabTime_sub_le {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) (ω : X.Ω)
    {u v u' v' : Pt m} (hu : u ∈ sl.set) (hv : v ∈ sl.set) (hu' : u' ∈ sl.set)
    (hv' : v' ∈ sl.set) :
    |X.slabTime b sl ω u v - X.slabTime b sl ω u' v'| ≤ b * (dist u u' + dist v v') := by
  have hb0 := upperBound_nonneg X hb ω
  rw [slabTime_eq_infra X hb sl ω hu hv, slabTime_eq_infra X hb sl ω hu' hv']
  have h1 := Infra.Measurability.passageTime_endpoint_bound
    (measurable_ofReal_extDensity X b sl ω) (ofReal_extDensity_le X hb sl ω) u v u' v'
  have h2 := Infra.Measurability.passageTime_endpoint_bound
    (measurable_ofReal_extDensity X b sl ω) (ofReal_extDensity_le X hb sl ω) u' v' u v
  rw [Real.coe_toNNReal _ hb0] at h1 h2
  rw [dist_comm u' u, dist_comm v' v] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **The triangle inequality for the slab passage time.** -/
theorem slabTime_triangle {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) (ω : X.Ω)
    {u v w : Pt m} (hu : u ∈ sl.set) (hv : v ∈ sl.set) (hw : w ∈ sl.set) :
    X.slabTime b sl ω u w ≤ X.slabTime b sl ω u v + X.slabTime b sl ω v w := by
  rw [slabTime_eq_infra X hb sl ω hu hw, slabTime_eq_infra X hb sl ω hu hv,
    slabTime_eq_infra X hb sl ω hv hw]
  have h := Infra.Measurability.passageTime_triangle (measurable_ofReal_extDensity X b sl ω) u v w
  have hne := Infra.Measurability.passageTime_ne_top (ofReal_extDensity_le X hb sl ω)
  rw [← ENNReal.toReal_add (hne u v) (hne v w)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hne u v, hne v w⟩) h

/-- The slab passage time is nonnegative. -/
theorem slabTime_nonneg (b : ℝ) (sl : Slab m) (ω : X.Ω) (u v : Pt m) :
    0 ≤ X.slabTime b sl ω u v :=
  ENNReal.toReal_nonneg

/-- **The slab passage time is a random variable.** -/
theorem aemeasurable_slabTime {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) (u v : Pt m) :
    AEMeasurable (fun ω => X.slabTime b sl ω u v) X.P := by
  by_cases h : u ∈ sl.set ∧ v ∈ sl.set
  · have heq : (fun ω => X.slabTime b sl ω u v) = fun ω =>
        (Infra.Measurability.passageTime
          (fun x => ENNReal.ofReal (extDensity sl b (X.ρ ω) x)) u v).toReal := by
      funext ω
      exact slabTime_eq_infra X hb sl ω h.1 h.2
    rw [heq]
    exact (Infra.Measurability.nullMeasurable_passageTime X.P
      (measurable_extDensity_uncurry sl b X.measurable_ρ).ennreal_ofReal u v
      ).aemeasurable.ennreal_toReal
  · have heq : (fun ω => X.slabTime b sl ω u v) = fun _ => 0 := by
      funext ω
      exact passTime_of_not_mem sl b (X.ρ ω) (not_and_or.mp h)
    rw [heq]
    exact aemeasurable_const

end IsotropicVariance.Infra.Slab
