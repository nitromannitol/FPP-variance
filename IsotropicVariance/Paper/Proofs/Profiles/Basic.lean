/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.SlabTime
public import IsotropicVariance.Infra.TimeConstant.Mean
public import IsotropicVariance.Infra.Curves.Main
public import IsotropicVariance.Infra.Curves.SpeedMeasure
public import IsotropicVariance.Infra.Curves.LipschitzReparam
public import IsotropicVariance.Infra.Os.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Passage times of a setting: bounds, symmetry, rigid motions

For a setting `X` (`Paper.Setting`) and an outcome `ω`, the passage time
`T(u, v) = X.passTime ω u v` (the introduction) is nonnegative, symmetric, at most `B|u − v|`
for an upper bound `B` of the density, satisfies the triangle inequality and the Lipschitz
bound in the endpoints, and is an almost everywhere measurable function of the outcome
(equation `eq:passage`). Moving the noise and the endpoints by a proper rigid
motion does not change it (part (3) of Assumption `ass:local`,
`Infra.TimeConstant.setting_passTime_covariant`), and every pair of points is the
image of `0` and `r e₁`, `r = |v − u|`, under a proper rigid motion (`d ≥ 2`). Hence `T(u, v)`
has the law of `T_r` ("stationarity and isotropy", the proof of Lemma `lem:tree`), and every `O_s`
bound on a function of `T_r` transfers to `T(u, v)`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

variable {m : ℕ}

/-! ## Passage times of a density -/

section Density

variable {σ : Pt m → ℝ}

lemma measurable_ofReal_comp (hσ : Measurable σ) : Measurable fun x => ENNReal.ofReal (σ x) :=
  ENNReal.measurable_ofReal.comp hσ

lemma passageTime_nonneg (σ : Pt m → ℝ) (u v : Pt m) : 0 ≤ passageTime σ u v :=
  ENNReal.toReal_nonneg

lemma ofReal_le_toNNReal {B : ℝ} (hB : ∀ x, σ x ≤ B) (x : Pt m) :
    ENNReal.ofReal (σ x) ≤ ((B.toNNReal : ℝ≥0) : ℝ≥0∞) :=
  ENNReal.ofReal_le_ofReal (hB x)

lemma infraPassageTime_ne_top {B : ℝ} (hB : ∀ x, σ x ≤ B) (u v : Pt m) :
    Infra.Measurability.passageTime (fun x => ENNReal.ofReal (σ x)) u v ≠ ⊤ :=
  Infra.Measurability.passageTime_ne_top (ofReal_le_toNNReal hB) u v

/-- `T(u, v) ≤ B |u − v|` for an upper bound `B ≥ 0` of the density. -/
lemma passageTime_le_mul_dist {B : ℝ} (hB : ∀ x, σ x ≤ B) (hB0 : 0 ≤ B) (u v : Pt m) :
    passageTime σ u v ≤ B * dist u v := by
  rw [Infra.Slab.passageTime_eq_infra]
  have h := Infra.Measurability.passageTime_le_edist (ofReal_le_toNNReal hB) u v
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) h
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal B hB0,
    edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h'

/-- The triangle inequality for passage times. -/
lemma passageTime_triangle (hσ : Measurable σ) {B : ℝ} (hB : ∀ x, σ x ≤ B) (u v w : Pt m) :
    passageTime σ u w ≤ passageTime σ u v + passageTime σ v w := by
  simp only [Infra.Slab.passageTime_eq_infra]
  rw [← ENNReal.toReal_add (infraPassageTime_ne_top hB u v) (infraPassageTime_ne_top hB v w)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨infraPassageTime_ne_top hB u v, infraPassageTime_ne_top hB v w⟩)
    (Infra.Measurability.passageTime_triangle (measurable_ofReal_comp hσ) u v w)

/-- The Lipschitz bound in the endpoints. -/
lemma passageTime_le_add (hσ : Measurable σ) {B : ℝ} (hB : ∀ x, σ x ≤ B) (hB0 : 0 ≤ B)
    (u v u' v' : Pt m) :
    passageTime σ u v ≤ passageTime σ u' v' + B * (dist u u' + dist v v') := by
  simp only [Infra.Slab.passageTime_eq_infra]
  have h := Infra.Measurability.passageTime_endpoint_bound (measurable_ofReal_comp hσ)
    (ofReal_le_toNNReal hB) u v u' v'
  simpa only [Real.coe_toNNReal B hB0] using h

lemma abs_passageTime_sub_le (hσ : Measurable σ) {B : ℝ} (hB : ∀ x, σ x ≤ B) (hB0 : 0 ≤ B)
    (u v u' v' : Pt m) :
    |passageTime σ u v - passageTime σ u' v'| ≤ B * (dist u u' + dist v v') := by
  rw [abs_sub_le_iff]
  have h1 := passageTime_le_add hσ hB hB0 u v u' v'
  have h2 := passageTime_le_add hσ hB hB0 u' v' u v
  rw [dist_comm u' u, dist_comm v' v] at h2
  constructor <;> linarith

lemma continuous_passageTime (hσ : Measurable σ) {B : ℝ} (hB : ∀ x, σ x ≤ B) :
    Continuous fun p : Pt m × Pt m => passageTime σ p.1 p.2 := by
  have h := Infra.Measurability.lipschitzWith_passageTime (measurable_ofReal_comp hσ)
    (ofReal_le_toNNReal hB)
  simp only [Infra.Slab.passageTime_eq_infra]
  exact h.continuous

/-- Passage times are symmetric: reversal of curves. -/
lemma passageTime_comm (hσ : Measurable σ) (u v : Pt m) :
    passageTime σ u v = passageTime σ v u := by
  have hρ : Measurable fun x => Real.toNNReal (σ x) := measurable_real_toNNReal.comp hσ
  have key (a b : Pt m) : Infra.Measurability.passageTime (fun x => ENNReal.ofReal (σ x)) a b =
      ⨅ γ : Infra.Curves.LipCurve (Pt m) a b, γ.cost fun x => Real.toNNReal (σ x) := by
    unfold Infra.Measurability.passageTime
    exact Infra.Curves.iInf_cost_rectifiable_eq_derivative hρ a b
  have hle (a b : Pt m) :
      (⨅ γ : Infra.Curves.LipCurve (Pt m) b a, γ.cost fun x => Real.toNNReal (σ x)) ≤
        ⨅ γ : Infra.Curves.LipCurve (Pt m) a b, γ.cost fun x => Real.toNNReal (σ x) :=
    le_iInf fun γ => (iInf_le _ γ.reverse).trans_eq (γ.cost_reverse _)
  simp only [Infra.Slab.passageTime_eq_infra, key]
  rw [le_antisymm (hle v u) (hle u v)]

end Density

/-! ## Proper rigid motions -/

/-- A linear isometry equivalence of determinant one, followed by a translation, is a proper
rigid motion. -/
lemma isProperRigidMotion_of_linear (L : Pt m ≃ₗᵢ[ℝ] Pt m)
    (hL : LinearMap.det (L.toLinearEquiv : Pt m →ₗ[ℝ] Pt m) = 1) (p : Pt m) :
    IsProperRigidMotion (L.toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.constVAdd ℝ (Pt m) p)) := by
  unfold IsProperRigidMotion
  convert hL using 2
  ext x
  rfl

/-- A reflection in the hyperplane orthogonal to a nonzero vector has determinant `-1`. -/
lemma det_reflection_singleton {v : Pt m} (hv : v ≠ 0) :
    LinearMap.det ((ℝ ∙ v)ᗮ.reflection.toLinearEquiv : Pt m →ₗ[ℝ] Pt m) = -1 := by
  have h := Submodule.det_reflection (𝕜 := ℝ) (ℝ ∙ v)ᗮ
  rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hv, pow_one] at h
  exact h

lemma finrank_pt (m : ℕ) : Module.finrank ℝ (Pt m) = m + 1 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × EuclideanSpace ℝ (Fin m))).finrank_eq,
    Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self, add_comm]

/-- In dimension `d ≥ 2`, every unit vector is the image of `e₁` under a linear isometry of
determinant one: the composition of the reflection exchanging `e₁` and `c` with a reflection
fixing `c`. -/
lemma exists_rotation (hm : 1 ≤ m) {c : Pt m} (hc : ‖c‖ = 1) :
    ∃ L : Pt m ≃ₗᵢ[ℝ] Pt m, LinearMap.det (L.toLinearEquiv : Pt m →ₗ[ℝ] Pt m) = 1 ∧
      L e₁ = c := by
  by_cases h : (e₁ : Pt m) = c
  · exact ⟨LinearIsometryEquiv.refl ℝ (Pt m), by simp, by simp [h]⟩
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  have hfin : Module.finrank ℝ (ℝ ∙ c)ᗮ = m := by
    have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ c)
    rw [finrank_span_singleton hc0, finrank_pt] at this
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (ℝ ∙ c)ᗮ) (fun hbot => by
    rw [hbot, finrank_bot] at hfin
    omega)
  have hsub : (e₁ : Pt m) - c ≠ 0 := sub_ne_zero.mpr h
  refine ⟨((ℝ ∙ ((e₁ : Pt m) - c))ᗮ.reflection).trans (ℝ ∙ w)ᗮ.reflection, ?_, ?_⟩
  · have hcomp : (((ℝ ∙ ((e₁ : Pt m) - c))ᗮ.reflection.trans (ℝ ∙ w)ᗮ.reflection).toLinearEquiv :
        Pt m →ₗ[ℝ] Pt m) = ((ℝ ∙ w)ᗮ.reflection.toLinearEquiv : Pt m →ₗ[ℝ] Pt m) ∘ₗ
          ((ℝ ∙ ((e₁ : Pt m) - c))ᗮ.reflection.toLinearEquiv : Pt m →ₗ[ℝ] Pt m) := rfl
    rw [hcomp, LinearMap.det_comp, det_reflection_singleton hw0, det_reflection_singleton hsub]
    norm_num
  · have h1 : (ℝ ∙ ((e₁ : Pt m) - c))ᗮ.reflection e₁ = c :=
      Submodule.reflection_sub (by rw [norm_e₁, hc])
    have h2 : c ∈ (ℝ ∙ w)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
      exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp hw
    simp only [LinearIsometryEquiv.trans_apply, h1]
    exact Submodule.reflection_mem_subspace_eq_self h2

/-- Every pair of points is the image of `0` and `|v − u| e₁` under a proper rigid motion. -/
lemma exists_properRigidMotion (hm : 1 ≤ m) (u v : Pt m) :
    ∃ g : Pt m ≃ᵃⁱ[ℝ] Pt m, IsProperRigidMotion g ∧ g 0 = u ∧ g (dist u v • e₁) = v := by
  by_cases huv : u = v
  · refine ⟨(LinearIsometryEquiv.refl ℝ (Pt m)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.constVAdd ℝ (Pt m) u),
      isProperRigidMotion_of_linear _ (by simp) u, by simp, by simp [huv]⟩
  have hd : 0 < dist u v := dist_pos.mpr huv
  obtain ⟨L, hL, hLe⟩ := exists_rotation hm (c := (dist u v)⁻¹ • (v - u)) (by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hd, dist_comm, dist_eq_norm]
    exact inv_mul_cancel₀ (by rw [← dist_eq_norm, dist_comm]; exact hd.ne'))
  refine ⟨L.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ (Pt m) u),
    isProperRigidMotion_of_linear L hL u, by simp, ?_⟩
  simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply,
    LinearIsometryEquiv.coe_toAffineIsometryEquiv, map_smul, hLe,
    AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  abel

/-! ## The passage times of a setting -/

section Setting

variable (X : Setting m)

lemma measurable_ρ_apply (ω : X.Ω) : Measurable (X.ρ ω) :=
  X.measurable_ρ.comp measurable_prodMk_left

/-- The density has a positive upper bound. -/
lemma exists_upperBound : ∃ B : ℝ, 0 < B ∧ ∀ ω x, X.ρ ω x ≤ B := by
  obtain ⟨a, b, ha, h⟩ := X.bounds
  rcases isEmpty_or_nonempty X.Ω with hΩ | hΩ
  · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
  · obtain ⟨ω⟩ := hΩ
    exact ⟨b, ha.trans_le ((h ω 0).1.trans (h ω 0).2), fun ω x => (h ω x).2⟩

variable {X}

lemma passTime_nonneg (ω : X.Ω) (u v : Pt m) : 0 ≤ X.passTime ω u v :=
  passageTime_nonneg _ u v

lemma passTime_le_mul_dist {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (hB0 : 0 ≤ B) (ω : X.Ω)
    (u v : Pt m) : X.passTime ω u v ≤ B * dist u v :=
  passageTime_le_mul_dist (hB ω) hB0 u v

lemma passTime_triangle {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (ω : X.Ω) (u v w : Pt m) :
    X.passTime ω u w ≤ X.passTime ω u v + X.passTime ω v w :=
  passageTime_triangle (measurable_ρ_apply X ω) (hB ω) u v w

lemma abs_passTime_sub_le {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (hB0 : 0 ≤ B) (ω : X.Ω)
    (u v u' v' : Pt m) :
    |X.passTime ω u v - X.passTime ω u' v'| ≤ B * (dist u u' + dist v v') :=
  abs_passageTime_sub_le (measurable_ρ_apply X ω) (hB ω) hB0 u v u' v'

lemma passTime_comm (ω : X.Ω) (u v : Pt m) : X.passTime ω u v = X.passTime ω v u :=
  passageTime_comm (measurable_ρ_apply X ω) u v

lemma continuous_passTime {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (ω : X.Ω) :
    Continuous fun p : Pt m × Pt m => X.passTime ω p.1 p.2 :=
  continuous_passageTime (measurable_ρ_apply X ω) (hB ω)

/-- Passage times are almost everywhere measurable functions of the outcome
(equation `eq:passage`). -/
lemma aemeasurable_passTime (u v : Pt m) : AEMeasurable (fun ω => X.passTime ω u v) X.P := by
  have hρ : Measurable fun p : X.Ω × Pt m => ENNReal.ofReal (X.ρ p.1 p.2) :=
    ENNReal.measurable_ofReal.comp X.measurable_ρ
  have h := Infra.Measurability.nullMeasurable_passageTime X.P hρ u v
  simp only [Setting.passTime, Infra.Slab.passageTime_eq_infra]
  exact h.aemeasurable.ennreal_toReal

/-- An `O_s` bound transfers along a measure-preserving map. -/
lemma isOs_of_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {φ : Ω → Ω}
    (hφ : MeasurePreserving φ P P) {s θ : ℝ} {Y : Ω → ℝ} (hY : AEMeasurable Y P)
    (h : Cited.IsOs P s θ (Y ∘ φ)) : Cited.IsOs P s θ Y := by
  refine ⟨hY, ?_⟩
  have hF := Infra.Os.aemeasurable_exp_pos_rpow hY s θ
  rw [← hφ.map_eq] at hF
  rw [← hφ.map_eq, lintegral_map' hF hφ.measurable.aemeasurable]
  exact h.2

/-- **Stationarity and isotropy** (the proof of Lemma `lem:tree`): an `O_s`
bound on a measurable function of `T_r`, `r = |v − u|`, holds for the same function of
`T(u, v)`. -/
lemma isOs_passTime_of_TRV (hm : 1 ≤ m) {s θ : ℝ} {f : ℝ → ℝ} (hf : Measurable f) (u v : Pt m)
    (h : Cited.IsOs X.P s θ fun ω => f (X.TRV (dist u v) ω)) :
    Cited.IsOs X.P s θ fun ω => f (X.passTime ω u v) := by
  obtain ⟨g, hg, hg0, hgv⟩ := exists_properRigidMotion hm u v
  refine isOs_of_comp (X.measurePreserving_act g hg)
    (hf.comp_aemeasurable (aemeasurable_passTime u v)) ?_
  convert h using 2 with ω
  have key := Infra.TimeConstant.setting_passTime_covariant X g hg ω 0 (dist u v • e₁)
  rw [hg0, hgv] at key
  simp only [Function.comp_apply, Setting.TRV, key]

/-- **Stationarity and isotropy**: `T(u, v)` has the law of `T_r`, `r = |v − u|`. -/
lemma map_passTime_eq_map_TRV (hm : 1 ≤ m) (u v : Pt m) :
    X.P.map (fun ω => X.passTime ω u v) = X.P.map (X.TRV (dist u v)) := by
  obtain ⟨g, hg, hg0, hgv⟩ := exists_properRigidMotion hm u v
  have hmp := X.measurePreserving_act g hg
  have key : (fun ω => X.passTime ω u v) ∘ X.act g = X.TRV (dist u v) := by
    funext ω
    have h := Infra.TimeConstant.setting_passTime_covariant X g hg ω 0 (dist u v • e₁)
    rw [hg0, hgv] at h
    exact h
  have hF : AEMeasurable (fun ω => X.passTime ω u v) (X.P.map (X.act g)) := by
    rw [hmp.map_eq]
    exact aemeasurable_passTime u v
  rw [← key, ← AEMeasurable.map_map_of_aemeasurable hF hmp.measurable.aemeasurable, hmp.map_eq]

end Setting

end IsotropicVariance.Paper.Proofs.Profiles
