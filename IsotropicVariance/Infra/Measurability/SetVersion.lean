/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.SlabVersion
public import IsotropicVariance.Paper.Defs.SetTime
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# The passage time of a closed convex set is determined by the noise in its interior

Step 1 of the proof of Lemma `lem:labels`: the passage time `T_G`, defined by
equation `eq:slabtime` for the closure of a block `G`, is determined by the noise in `G`. Only
slabs have such a version in `IsotropicVariance.Infra.Measurability.SlabVersion`; this file gives
it for every closed convex set `P`, by the same route.

* The nearest-point projection onto a closed convex set of a Hilbert space (`convexProj`) is
  `1`-Lipschitz, is the identity on the set, and maps the complement of the set to its frontier.
* Extend `ρ_P` by the bound `b` off `P` (`extSetDensity`). For endpoints in `P`, `T_P(u, v)` is the
  unrestricted passage time of the extended density
  (`restrictedPassageTime_eq_passageTime_ext`): compose a curve with the projection.
* `closedBall_subset_interior_of_notMem_cthickening`: a point of `P` at distance more than one from
  `∂P` has its closed unit ball in the interior of `P`. So the extended density is jointly
  measurable for the information of the interior of `P` and the Borel sets.
* `exists_setTime_version`: a version of `T_P`, jointly measurable, continuous in the endpoints,
  measurable for the information of the interior of `P`, and equal to `T_P` at all endpoints in `P`
  on one full-measure event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace IsotropicVariance.Infra.Slab

open IsotropicVariance.Paper

/-! ## The nearest-point projection onto a closed convex set -/

section Proj

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {K : Set F}

/-- The nearest point of a closed convex set, by its variational characterization. -/
theorem exists_convexProj (hne : K.Nonempty) (hK : IsClosed K) (hconv : Convex ℝ K) (u : F) :
    ∃ v ∈ K, ∀ w ∈ K, ⟪u - v, w - v⟫ ≤ 0 := by
  obtain ⟨v, hv, h⟩ := exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hconv u
  exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hconv hv).1 h⟩

/-- The nearest-point projection onto a closed convex set. -/
noncomputable def convexProj (hne : K.Nonempty) (hK : IsClosed K) (hconv : Convex ℝ K) (u : F) :
    F :=
  (exists_convexProj hne hK hconv u).choose

theorem convexProj_mem (hne : K.Nonempty) (hK : IsClosed K) (hconv : Convex ℝ K) (u : F) :
    convexProj hne hK hconv u ∈ K :=
  (exists_convexProj hne hK hconv u).choose_spec.1

theorem inner_sub_convexProj_le (hne : K.Nonempty) (hK : IsClosed K) (hconv : Convex ℝ K) (u : F)
    {w : F} (hw : w ∈ K) :
    ⟪u - convexProj hne hK hconv u, w - convexProj hne hK hconv u⟫ ≤ 0 :=
  (exists_convexProj hne hK hconv u).choose_spec.2 w hw

/-- The projection is the identity on the set. -/
theorem convexProj_eq_self (hne : K.Nonempty) (hK : IsClosed K) (hconv : Convex ℝ K) {u : F}
    (hu : u ∈ K) : convexProj hne hK hconv u = u := by
  have h := inner_sub_convexProj_le hne hK hconv u hu
  rw [real_inner_self_eq_norm_sq] at h
  have h0 : ‖u - convexProj hne hK hconv u‖ = 0 := by
    have := sq_nonneg ‖u - convexProj hne hK hconv u‖
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h this)
  exact (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm

/-- **The projection is `1`-Lipschitz.** -/
theorem lipschitzWith_convexProj (hne : K.Nonempty) (hK : IsClosed K) (hconv : Convex ℝ K) :
    LipschitzWith 1 (convexProj hne hK hconv) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  obtain ⟨p, hp⟩ : ∃ p, p = convexProj hne hK hconv x := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = convexProj hne hK hconv y := ⟨_, rfl⟩
  have h1 : ⟪x - p, q - p⟫ ≤ 0 := by
    rw [hp, hq]
    exact inner_sub_convexProj_le hne hK hconv x (convexProj_mem hne hK hconv y)
  have h2 : ⟪y - q, p - q⟫ ≤ 0 := by
    rw [hp, hq]
    exact inner_sub_convexProj_le hne hK hconv y (convexProj_mem hne hK hconv x)
  have h3 : ⟪x - y, p - q⟫ = ‖p - q‖ ^ 2 - ⟪x - p, q - p⟫ - ⟪y - q, p - q⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have e' : q - p = -(p - q) := (neg_sub p q).symm
    rw [e', inner_neg_right]
    have e2 : x - y = (p - q) + (x - p) - (y - q) := by abel
    rw [e2, inner_sub_left, inner_add_left]
    ring
  have h4 : ⟪x - y, p - q⟫ ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm _ _
  have h5 : ‖p - q‖ ^ 2 ≤ ‖x - y‖ * ‖p - q‖ := by linarith only [h1, h2, h3, h4]
  rw [dist_eq_norm, dist_eq_norm, ← hp, ← hq]
  rcases (norm_nonneg (p - q)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · have h6 : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ := by rwa [← sq]
    exact le_of_mul_le_mul_right h6 h0

/-- The projection maps the complement of the set to its frontier: a point of the interior can be
moved towards `x`. -/
theorem convexProj_mem_frontier (hne : K.Nonempty) (hK : IsClosed K) (hconv : Convex ℝ K) {x : F}
    (hx : x ∉ K) : convexProj hne hK hconv x ∈ frontier K := by
  refine ⟨subset_closure (convexProj_mem hne hK hconv x), fun hint => hx ?_⟩
  obtain ⟨p, hp⟩ : ∃ p, p = convexProj hne hK hconv x := ⟨_, rfl⟩
  rw [← hp] at hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior p hint
  have hne0 : 0 < ‖x - p‖ + 1 := by positivity
  obtain ⟨t, ht⟩ : ∃ t, t = ε / (2 * (‖x - p‖ + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have hw : p + t • (x - p) ∈ K := by
    refine interior_subset (hball ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le, ht,
      div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (x - p)]
  have h := inner_sub_convexProj_le hne hK hconv x hw
  rw [← hp, add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have h0 : ‖x - p‖ ^ 2 ≤ 0 := by
    by_contra hc
    exact absurd h (not_le.2 (mul_pos ht0 (not_le.1 hc)))
  have h1 : ‖x - p‖ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h0 (sq_nonneg _))
  rw [sub_eq_zero.1 (norm_eq_zero.1 h1), hp]
  exact convexProj_mem hne hK hconv x

end Proj

/-! ## The unit neighborhood of the frontier -/

variable {m : ℕ}

/-- A point of a closed set at distance more than one from its frontier has its closed unit ball
in the interior of the set. -/
theorem closedBall_subset_interior_of_notMem_cthickening {P : Set (Pt m)} (hP : IsClosed P)
    {x : Pt m} (hx : x ∈ P) (h : x ∉ cthickening 1 (frontier P)) :
    closedBall x 1 ⊆ interior P := by
  intro y hy
  by_contra hyint
  have hex : ∃ w ∈ closedBall x 1, w ∈ frontier P := by
    by_cases hyP : y ∈ P
    · exact ⟨y, hy, subset_closure hyP, hyint⟩
    · exact exists_mem_frontier_of_isPreconnected hP (convex_closedBall x 1).isPreconnected
        (mem_closedBall_self zero_le_one) hx hy hyP
  obtain ⟨w, hw, hwf⟩ := hex
  exact h (mem_cthickening_of_dist_le x w 1 _ hwf (mem_closedBall'.1 hw))

/-- The unit neighborhood of a nonempty set, by the distance to the set. -/
theorem mem_cthickening_one_iff {s : Set (Pt m)} (hne : s.Nonempty) {x : Pt m} :
    x ∈ cthickening 1 s ↔ infDist x s ≤ 1 := by
  rw [mem_cthickening_iff, infDist, ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hne)
    zero_le_one]

/-- The converse: a point whose closed unit ball lies in the interior of a set is at distance more
than one from its frontier. -/
theorem notMem_cthickening_of_closedBall_subset_interior {P : Set (Pt m)} {x : Pt m}
    (h : closedBall x 1 ⊆ interior P) : x ∉ cthickening 1 (frontier P) := by
  intro hx
  rcases (frontier P).eq_empty_or_nonempty with he | hne
  · rw [he, cthickening_empty] at hx
    exact hx
  obtain ⟨y, hy, hxy⟩ := isClosed_frontier.exists_infDist_eq_dist hne x
  rw [mem_cthickening_one_iff hne, hxy] at hx
  exact hy.2 (h (mem_closedBall'.2 hx))

/-! ## The extended density -/

open scoped Classical in
/-- The density `ρ_P` of a set, extended by the upper bound `b` off the set. -/
noncomputable def extSetDensity (P : Set (Pt m)) (b : ℝ) (σ : Pt m → ℝ) (x : Pt m) : ℝ :=
  if x ∈ P then setDensity b σ P x else b

theorem extSetDensity_of_mem {P : Set (Pt m)} (b : ℝ) (σ : Pt m → ℝ) {x : Pt m} (hx : x ∈ P) :
    extSetDensity P b σ x = setDensity b σ P x := by
  simp [extSetDensity, hx]

theorem extSetDensity_of_notMem {P : Set (Pt m)} (b : ℝ) (σ : Pt m → ℝ) {x : Pt m}
    (hx : x ∉ P) : extSetDensity P b σ x = b := by
  simp [extSetDensity, hx]

/-- The extended density does not change under the projection onto a closed convex set. -/
theorem extSetDensity_convexProj {P : Set (Pt m)} (hne : P.Nonempty) (hP : IsClosed P)
    (hconv : Convex ℝ P) (b : ℝ) (σ : Pt m → ℝ) (x : Pt m) :
    extSetDensity P b σ (convexProj hne hP hconv x) = extSetDensity P b σ x := by
  by_cases hx : x ∈ P
  · rw [convexProj_eq_self hne hP hconv hx]
  · have hf : convexProj hne hP hconv x ∈ cthickening 1 (frontier P) :=
      self_subset_cthickening _ (convexProj_mem_frontier hne hP hconv hx)
    rw [extSetDensity_of_mem b σ (convexProj_mem hne hP hconv x), extSetDensity_of_notMem b σ hx]
    simp [setDensity, hf]

theorem extSetDensity_le {P : Set (Pt m)} {b : ℝ} {σ : Pt m → ℝ} (hσ : ∀ x, σ x ≤ b) (x : Pt m) :
    extSetDensity P b σ x ≤ b := by
  unfold extSetDensity
  split_ifs
  · exact setDensity_le hσ P x
  · exact le_rfl

/-! ## The passage time of a closed convex set as a passage time -/

/-- **`T_P` is the passage time of the extended density.** For a closed convex set `P` and
endpoints in `P`, the infimum of the costs of the curves in `P` for `ρ_P` equals the infimum of the
costs of all curves for `ρ_P` extended by `b` off `P`: compose a curve with the projection. -/
theorem restrictedPassageTime_eq_passageTime_ext {P : Set (Pt m)} (hP : IsClosed P)
    (hconv : Convex ℝ P) (b : ℝ) (σ : Pt m → ℝ) {u v : Pt m} (hu : u ∈ P) (hv : v ∈ P) :
    restrictedPassageTime (setDensity b σ P) P u v = passageTime (extSetDensity P b σ) u v := by
  have hne : P.Nonempty := ⟨u, hu⟩
  unfold restrictedPassageTime passageTime
  congr 1
  apply le_antisymm
  · refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => ?_
    let δ := mapCurve (convexProj hne hP hconv) (lipschitzWith_convexProj hne hP hconv) γ
    have hδ0 : δ.toFun 0 = u := by
      rw [mapCurve_toFun, h0, convexProj_eq_self hne hP hconv hu]
    have hδ1 : δ.toFun 1 = v := by
      rw [mapCurve_toFun, h1, convexProj_eq_self hne hP hconv hv]
    have hδS : ∀ t ∈ Icc (0 : ℝ) 1, δ.toFun t ∈ P := fun t _ => convexProj_mem hne hP hconv _
    refine iInf_le_of_le δ (iInf_le_of_le hδ0 (iInf_le_of_le hδ1 (iInf_le_of_le hδS ?_)))
    calc δ.cost (fun x => ENNReal.ofReal (setDensity b σ P x))
        = δ.cost (fun x => ENNReal.ofReal (extSetDensity P b σ x)) :=
          δ.cost_congr fun t ht => congrArg ENNReal.ofReal
            (extSetDensity_of_mem b σ (hδS t ht)).symm
      _ ≤ γ.cost (fun x => ENNReal.ofReal (extSetDensity P b σ x)) :=
          cost_mapCurve_le _ _ _ fun x => by rw [extSetDensity_convexProj hne hP hconv]
  · refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hS => ?_
    refine iInf_le_of_le γ (iInf_le_of_le h0 (iInf_le_of_le h1 ?_))
    exact (γ.cost_congr fun t ht =>
      congrArg ENNReal.ofReal (extSetDensity_of_mem b σ (hS t ht))).le

/-! ## Determined by the noise in the interior -/

variable (X : Setting m)

/-- The extended density is jointly measurable for the information of the interior of the set and
the Borel sets: it is `b` off `P` and near `∂P`, and elsewhere the density at a point whose closed
unit ball lies in the interior of `P` (Assumption `ass:local` (1), jointly). -/
theorem measurable_extSetDensity_info (b : ℝ) {P : Set (Pt m)} (hP : IsClosed P) :
    Measurable[(X.info (interior P)).prod inferInstance]
      fun p : X.Ω × Pt m => extSetDensity P b (X.ρ p.1) p.2 := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A : Set (Pt m), A = {x | x ∈ P ∧ x ∉ cthickening 1 (frontier P)} :=
    ⟨_, rfl⟩
  have hA : MeasurableSet A := by
    rw [hAdef]
    exact hP.measurableSet.inter isClosed_cthickening.measurableSet.compl
  have hAP : ∀ x ∈ A, closedBall x 1 ⊆ interior P := fun x hx => by
    rw [hAdef] at hx
    exact closedBall_subset_interior_of_notMem_cthickening hP hx.1 hx.2
  have heq : (fun p : X.Ω × Pt m => extSetDensity P b (X.ρ p.1) p.2) = fun p =>
      if h : p.2 ∈ A then
        X.ρ p.1 (⟨p.2, hAP _ h⟩ : {x : Pt m // closedBall x 1 ⊆ interior P})
      else b := by
    funext p
    by_cases hS : p.2 ∈ P
    · by_cases hd : p.2 ∈ cthickening 1 (frontier P)
      · have hpA : p.2 ∉ A := fun h => by
          rw [hAdef] at h
          exact h.2 hd
        simp [extSetDensity_of_mem b _ hS, setDensity, hd, hpA]
      · have hpA : p.2 ∈ A := by
          rw [hAdef]
          exact ⟨hS, hd⟩
        simp [extSetDensity_of_mem b _ hS, setDensity, hd, hpA]
    · have hpA : p.2 ∉ A := fun h => by
        rw [hAdef] at h
        exact hS h.1
      simp [extSetDensity_of_notMem b _ hS, hpA]
  rw [heq]
  have hg := X.determined_joint (interior P) isOpen_interior
  exact @measurable_dite_mem X.Ω (Pt m) _ (X.info (interior P)) _ A _ hA hAP
    (fun p => X.ρ p.1 p.2) hg b

/-- **A version of `T_P` determined by the noise in the interior of `P`**, for `P` closed and
convex: jointly measurable, continuous in the endpoints, measurable (as a random function of the
endpoints) for the information of the interior of `P`, and equal to `T_P` at all endpoints in `P`
on one full-measure event. -/
theorem exists_setTime_version {b : ℝ} (hb : X.IsUpperBound b) {P : Set (Pt m)} (hP : IsClosed P)
    (hconv : Convex ℝ P) :
    ∃ V : X.Ω → Pt m × Pt m → ℝ, Measurable (Function.uncurry V) ∧ (∀ ω, Continuous (V ω)) ∧
      Measurable[X.info (interior P)] V ∧
      ∀ᵐ ω ∂X.P, ∀ u ∈ P, ∀ v ∈ P, V ω (u, v) = X.setTime b P ω u v := by
  obtain ⟨Φ, hΦ, h, hh, hfh⟩ := exists_factor_of_measurable_prod
    (measurable_extSetDensity_info X b hP)
  have hΦm : Measurable Φ := hΦ.mono (X.info_le _) le_rfl
  let ρ' : (ℕ → Bool) × Pt m → ℝ≥0∞ := fun q => ENNReal.ofReal (min (h q) b)
  have hρ' : Measurable ρ' := (hh.min measurable_const).ennreal_ofReal
  have hbd : ∀ y x, ρ' (y, x) ≤ (b.toNNReal : ℝ≥0∞) :=
    fun _ _ => ENNReal.ofReal_le_ofReal (min_le_right _ _)
  obtain ⟨T, hTm, hTc, hTae⟩ :=
    Infra.Measurability.exists_jointlyMeasurable_passageTime_version (X.P.map Φ) hρ' hbd
  refine ⟨fun ω => T (Φ ω), ?_, fun ω => hTc (Φ ω), ?_, ?_⟩
  · exact hTm.comp (hΦm.prodMap measurable_id)
  · have hT : Measurable T :=
      Measurable.of_eval fun p => hTm.comp (measurable_id.prodMk measurable_const)
    exact hT.comp hΦ
  · filter_upwards [ae_of_ae_map hΦm.aemeasurable hTae] with ω hω u hu v hv
    rw [hω (u, v), Setting.setTime, restrictedPassageTime_eq_passageTime_ext hP hconv b _ hu hv,
      passageTime_eq_infra]
    congr 2
    funext x
    have hx := hfh ω x
    simp only at hx
    simp only [ρ', ← hx, min_eq_left (extSetDensity_le (hb ω) x)]

end IsotropicVariance.Infra.Slab
