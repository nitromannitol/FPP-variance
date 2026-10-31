/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum

/-!
# The density `ρ_P` and the passage time `T_P` of a closed set

Equation `eq:slabtime`: for a closed set `P`, the density `ρ_P` equals `ρ` at distance more than
one from the boundary of `P` and an upper bound of `ρ` elsewhere, and `T_P(x, y)` is the infimum of
`∫_π ρ_P` over the curves `π` from `x` to `y` in `P`.

* `setDensity b σ P`: the density `ρ_P`, for the density `σ` and the upper bound `b`.
* `Setting.setTime b P ω`: the passage time `T_P` of an outcome.
* Bridges: `setDensity_univ`, `Setting.setTime_univ` (the whole space gives `ρ` and `T`),
  `Slab.density_eq_setDensity`, `Setting.setTime_slab` (a slab of positive width gives
  `Slab.density` and `Setting.slabTime`; its frontier is the pair of faces, `Slab.frontier_set`).
* Monotonicity in `P`: `setDensity_mono`, on `P` for `P ⊆ P'`; hence `T_P ≥ T_{P'}`
  (`Setting.setTime_le_setTime`) and `T_P ≥ T` (`Setting.passTime_le_setTime`, Section
  `sec:prelim`). Both need `T_P` finite: see the docstring of `Setting.setTime`.
* `cost_congr_setDensity`: the costs of a curve for two densities `ρ_P` and `ρ_{P'}` agree when the
  densities agree along it (Step 1 of the proof of Lemma `lem:labels`).

The near-geodesics `Π_{T_P}(u, v)` are the curves `γ` with
`IsOneOptimal (setDensity b (X.ρ ω) P) P u v γ`, and the passage time `T_G` of Lemma `lem:labels`
is `X.setTime b (closure G)`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper

variable {m : ℕ}

namespace Pt

/-- The longitudinal coordinate is an open map. -/
theorem isOpenMap_lon : IsOpenMap (lon : Pt m → ℝ) :=
  isOpenMap_fst.comp (WithLp.homeomorphProd 2 ℝ (EuclideanSpace ℝ (Fin m))).isOpenMap

end Pt

/-! ### Costs along a curve -/

/-- The cost of a curve is monotone in the density along the curve. -/
theorem cost_mono_of_forall_mem {ρ ρ' : Pt m → ℝ≥0∞} (γ : RectifiableCurve (Pt m))
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ρ (γ.toFun t) ≤ ρ' (γ.toFun t)) : γ.cost ρ ≤ γ.cost ρ' :=
  lintegral_mono_ae (γ.ae_mem_Icc.mono h)

/-! ### The density `ρ_P` -/

open scoped Classical in
/-- `ρ_P`: the upper bound `b` within distance one of `∂P`, `σ` elsewhere (equation
`eq:slabtime`). The paper's upper bound is `sup ρ`; here `b` is any deterministic upper bound of
which `sup ρ` is an instance. The set is `cthickening 1 (frontier P)` and not
`{x | infDist x (frontier P) ≤ 1}`, because `infDist x ∅ = 0` would put `b` everywhere for
`P = univ`. -/
noncomputable def setDensity (b : ℝ) (σ : Pt m → ℝ) (P : Set (Pt m)) (x : Pt m) : ℝ :=
  if x ∈ cthickening 1 (frontier P) then b else σ x

/-- For the whole space, `ρ_P = ρ`. -/
@[simp] theorem setDensity_univ (b : ℝ) (σ : Pt m → ℝ) : setDensity b σ univ = σ := by
  funext x
  simp [setDensity]

/-- The density `ρ_P` is measurable when the density is. -/
theorem measurable_setDensity (b : ℝ) {σ : Pt m → ℝ} (hσ : Measurable σ) (P : Set (Pt m)) :
    Measurable (setDensity b σ P) :=
  Measurable.ite isClosed_cthickening.measurableSet measurable_const hσ

/-- `ρ ≤ ρ_P` for an upper bound `b` of `ρ`. -/
theorem le_setDensity {b : ℝ} {σ : Pt m → ℝ} (hb : ∀ y, σ y ≤ b) (P : Set (Pt m)) (x : Pt m) :
    σ x ≤ setDensity b σ P x := by
  unfold setDensity
  split_ifs
  · exact hb x
  · exact le_rfl

/-- `ρ_P ≤ b` for an upper bound `b` of `ρ`. -/
theorem setDensity_le {b : ℝ} {σ : Pt m → ℝ} (hb : ∀ y, σ y ≤ b) (P : Set (Pt m)) (x : Pt m) :
    setDensity b σ P x ≤ b := by
  unfold setDensity
  split_ifs
  · exact le_rfl
  · exact hb x

/-- A preconnected set meeting a closed set `P` and its complement meets `∂P`. -/
theorem exists_mem_frontier_of_isPreconnected {P s : Set (Pt m)} (hP : IsClosed P)
    (hs : IsPreconnected s) {x y : Pt m} (hx : x ∈ s) (hxP : x ∈ P) (hy : y ∈ s) (hyP : y ∉ P) :
    ∃ w ∈ s, w ∈ frontier P := by
  by_contra hcon
  have hsub : s ⊆ interior P ∪ Pᶜ := fun w hw => by
    by_cases hwP : w ∈ P
    · refine Or.inl ?_
      by_contra hint
      exact hcon ⟨w, hw, subset_closure hwP, hint⟩
    · exact Or.inr hwP
  have hxint : x ∈ interior P := (hsub hx).resolve_right (not_not.2 hxP)
  exact hyP (interior_subset (hs.subset_left_of_subset_union isOpen_interior hP.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hsub ⟨x, hx, hxint⟩ hy))

/-- A point of a closed set `P ⊆ P'` is at least as close to `∂P` as to `∂P'`: a point of `∂P'`
in `P` is a point of `∂P`, and the segment from the point to a point of `∂P'` off `P` crosses
`∂P`. -/
theorem infEDist_frontier_le {P P' : Set (Pt m)} (hP : IsClosed P) (hPP' : P ⊆ P') {x : Pt m}
    (hx : x ∈ P) : infEDist x (frontier P) ≤ infEDist x (frontier P') := by
  refine le_infEDist.2 fun y hy => ?_
  have hyint : y ∉ interior P := fun h => hy.2 (interior_mono hPP' h)
  by_cases hyP : y ∈ P
  · exact infEDist_le_edist_of_mem ⟨subset_closure hyP, hyint⟩
  · obtain ⟨w, hwseg, hwfr⟩ := exists_mem_frontier_of_isPreconnected hP
      (convex_segment x y).isPreconnected (left_mem_segment ℝ x y) hx (right_mem_segment ℝ x y) hyP
    refine (infEDist_le_edist_of_mem hwfr).trans ?_
    have hw : w ∈ closedBall x (dist y x) :=
      (convex_closedBall x (dist y x)).segment_subset (mem_closedBall_self dist_nonneg)
        (mem_closedBall.2 le_rfl) hwseg
    rw [edist_dist, edist_dist, dist_comm x w, dist_comm x y]
    exact ENNReal.ofReal_le_ofReal hw

/-- **`ρ_P` is antitone in `P`, on `P`.** For `P ⊆ P'` closed and `x ∈ P`, `ρ_{P'}(x) ≤ ρ_P(x)`. -/
theorem setDensity_mono {b : ℝ} {σ : Pt m → ℝ} (hb : ∀ y, σ y ≤ b) {P P' : Set (Pt m)}
    (hP : IsClosed P) (hPP' : P ⊆ P') {x : Pt m} (hx : x ∈ P) :
    setDensity b σ P' x ≤ setDensity b σ P x := by
  by_cases hx' : x ∈ cthickening 1 (frontier P')
  · have hxP : x ∈ cthickening 1 (frontier P) := by
      rw [mem_cthickening_iff] at hx' ⊢
      exact (infEDist_frontier_le hP hPP' hx).trans hx'
    simp only [setDensity, hx', hxP, ite_true, le_refl]
  · simp only [setDensity, hx', ite_false]
    exact le_setDensity hb P x

/-! ### Slabs -/

namespace Slab

variable (sl : Slab m)

/-- The frontier of the standard slab of positive width is the pair of its faces. -/
theorem frontier_standard {s : ℝ} (hs : 0 < s) :
    frontier {x : Pt m | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ s} = {x | Pt.lon x = 0 ∨ Pt.lon x = s} := by
  have h := Pt.isOpenMap_lon.preimage_frontier_eq_frontier_preimage (Pt.continuous_lon (m := m))
    (Icc 0 s)
  rw [frontier_Icc hs.le] at h
  exact h.symm

/-- The frontier of a slab of positive width is the pair of its faces. -/
theorem frontier_set (hw : 0 < sl.width) : frontier sl.set = sl.faces := by
  unfold set faces
  rw [← frontier_standard hw]
  exact (sl.motion.toHomeomorph.image_frontier _).symm

/-- The faces of a slab are nonempty. -/
theorem faces_nonempty : sl.faces.Nonempty :=
  ⟨sl.motion 0, 0, Or.inl Pt.lon_zero, rfl⟩

/-- For a slab of positive width, the density of equation `eq:slabtime` is the slab density. -/
theorem density_eq_setDensity (hw : 0 < sl.width) (b : ℝ) (σ : Pt m → ℝ) :
    sl.density b σ = setDensity b σ sl.set := by
  funext x
  have hx : x ∈ cthickening 1 sl.faces ↔ infDist x sl.faces ≤ 1 := by
    rw [mem_cthickening_iff, infDist, ENNReal.le_ofReal_iff_toReal_le
      (infEDist_ne_top sl.faces_nonempty) zero_le_one]
  simp only [density, setDensity, sl.frontier_set hw, hx]

end Slab

/-! ### The passage time `T_P` -/

namespace Setting

variable (X : Setting.{u} m)

/-- `T_P(u, v)` of an outcome (equation `eq:slabtime`): the infimum of the cost for `ρ_P` over the
curves from `u` to `v` in `P`. Here `b` is any deterministic upper bound of the density, of which
the paper's `sup ρ` is an instance. The value is the `toReal` of the infimum
(`restrictedPassageTime`), which is `0` when no curve in `P` joins `u` and `v`; no use reaches
that case, because every `P` used is convex. -/
noncomputable def setTime (b : ℝ) (P : Set (Pt m)) (ω : X.Ω) (u v : Pt m) : ℝ :=
  restrictedPassageTime (setDensity b (X.ρ ω) P) P u v

/-- For the whole space, `T_P = T`. -/
@[simp] theorem setTime_univ (b : ℝ) (ω : X.Ω) (u v : Pt m) :
    X.setTime b univ ω u v = X.passTime ω u v := by
  simp [setTime, passTime, restrictedPassageTime, IsotropicVariance.passageTime]

/-- For a slab of positive width, `T_P` is the slab passage time. -/
theorem setTime_slab (sl : Slab m) (hw : 0 < sl.width) (b : ℝ) (ω : X.Ω) :
    X.setTime b sl.set ω = X.slabTime b sl ω := by
  funext u v
  simp only [setTime, slabTime, Slab.passTime, sl.density_eq_setDensity hw]

/-- The infimum defining `T_P` is antitone in `P`, in `[0, ∞]`. -/
theorem restrictedInf_setDensity_le {b : ℝ} (hb : X.IsUpperBound b) {P P' : Set (Pt m)}
    (hP : IsClosed P) (hPP' : P ⊆ P') (ω : X.Ω) (u v : Pt m) :
    restrictedInf (setDensity b (X.ρ ω) P') P' u v ≤
      restrictedInf (setDensity b (X.ρ ω) P) P u v := by
  refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hS => ?_
  refine (restrictedInf_le_cost γ h0 h1 fun t ht => hPP' (hS t ht)).trans ?_
  exact cost_mono_of_forall_mem γ fun t ht =>
    ENNReal.ofReal_le_ofReal (setDensity_mono (hb ω) hP hPP' (hS t ht))

/-- `T_{P'} ≤ T_P` for `P ⊆ P'` closed, at endpoints joined in `P` by a curve of finite cost. -/
theorem setTime_le_setTime_of_ne_top {b : ℝ} (hb : X.IsUpperBound b) {P P' : Set (Pt m)}
    (hP : IsClosed P) (hPP' : P ⊆ P') (ω : X.Ω) {u v : Pt m}
    (hfin : restrictedInf (setDensity b (X.ρ ω) P) P u v ≠ ⊤) :
    X.setTime b P' ω u v ≤ X.setTime b P ω u v :=
  ENNReal.toReal_mono hfin (X.restrictedInf_setDensity_le hb hP hPP' ω u v)

/-- **`T_P ≥ T_{P'}`** for `P ⊆ P'` with `P` closed and convex, on endpoints in `P`. -/
theorem setTime_le_setTime {b : ℝ} (hb : X.IsUpperBound b) {P P' : Set (Pt m)}
    (hP : IsClosed P) (hconv : Convex ℝ P) (hPP' : P ⊆ P') (ω : X.Ω) {u v : Pt m}
    (hu : u ∈ P) (hv : v ∈ P) : X.setTime b P' ω u v ≤ X.setTime b P ω u v :=
  X.setTime_le_setTime_of_ne_top hb hP hPP' ω
    (restrictedInf_ne_top (setDensity_le (hb ω) P) hconv hu hv)

/-- **`T_P ≥ T`** for `P` closed and convex, on endpoints in `P` (Section `sec:prelim`). -/
theorem passTime_le_setTime {b : ℝ} (hb : X.IsUpperBound b) {P : Set (Pt m)}
    (hP : IsClosed P) (hconv : Convex ℝ P) (ω : X.Ω) {u v : Pt m} (hu : u ∈ P) (hv : v ∈ P) :
    X.passTime ω u v ≤ X.setTime b P ω u v := by
  rw [← X.setTime_univ b]
  exact X.setTime_le_setTime hb hP hconv (subset_univ P) ω hu hv

end Setting

/-- If `ρ_P` and `ρ_{P'}` agree along a curve, its costs for the two densities agree (Step 1 of
the proof of Lemma `lem:labels`). -/
theorem cost_congr_setDensity {b : ℝ} {σ : Pt m → ℝ} {P P' : Set (Pt m)}
    (γ : RectifiableCurve (Pt m))
    (h : ∀ t ∈ Icc (0 : ℝ) 1, setDensity b σ P (γ.toFun t) = setDensity b σ P' (γ.toFun t)) :
    γ.cost (fun x => ENNReal.ofReal (setDensity b σ P x)) =
      γ.cost (fun x => ENNReal.ofReal (setDensity b σ P' x)) :=
  (cost_mono_of_forall_mem γ fun t ht => by rw [h t ht]).antisymm
    (cost_mono_of_forall_mem γ fun t ht => by rw [h t ht])

end IsotropicVariance.Paper
