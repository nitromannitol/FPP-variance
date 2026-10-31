/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Slab
public import IsotropicVariance.Paper.Proofs.SlabComparison.SubcurveOptimal
public import IsotropicVariance.Infra.TimeConstant.Isometry
public import IsotropicVariance.Infra.TimeConstant.Mean

/-! # Lemma `lem:straight` around any center

The proof of Lemma `lem:slab` opens with "By stationarity, we may assume that `z = 0` and `τ = 0`".
Lean keeps `z` and `τ`, and moves the scale `W` of Lemma `lem:straight` instead: `W ∘ act (−z)` is
the scale of the ball around `z`, with the same law. This is `exists_straight_scale`, and it is the
only use of stationarity in the proof.

* `StraightOn X ω B R`: the conclusion of Lemma `lem:straight` on one outcome, for endpoints in the
  set `B`, at distance at least `R` from the first endpoint.
* `StraightOn.angle_subarc`: the same for a subarc ending at the second endpoint, since subarcs of
  near-geodesics are near-geodesics (proof of equation `eq:columns`).
-/

@[expose] public section
open MeasureTheory Set Metric InnerProductGeometry
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Contracts
universe u
variable {m : ℕ}

/-- The conclusion of Lemma `lem:straight` on one outcome, for
near-geodesics between two distinct points of `B`, at the points at distance at least `R` from the
first one. -/
def StraightOn (X : Setting m) (ω : X.Ω) (B : Set (Pt m)) (R : ℝ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a ≠ b → ∀ γ : RectifiableCurve (Pt m), IsOneOptimal (X.ρ ω) univ a b γ →
    ∀ t ∈ Icc (0 : ℝ) 1, R ≤ ‖γ.toFun t - a‖ → angle (γ.toFun t - a) (b - a) ≤ 1 / 10

/-- The threshold can be raised. -/
lemma StraightOn.mono {X : Setting m} {ω : X.Ω} {B : Set (Pt m)} {R R' : ℝ}
    (h : StraightOn X ω B R) (hR : R ≤ R') : StraightOn X ω B R' :=
  fun a ha b hb hab γ hγ t ht hfar => h a ha b hb hab γ hγ t ht (hR.trans hfar)

/-- Moving the noise and a near-geodesic by a proper rigid motion gives a near-geodesic. -/
theorem isOneOptimal_act (X : Setting m) {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g)
    (ω : X.Ω) {u v : Pt m} {γ : RectifiableCurve (Pt m)}
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) :
    IsOneOptimal (X.ρ (X.act g ω)) univ (g u) (g v)
      (Infra.TimeConstant.mapCurve g.toIsometryEquiv γ) := by
  have heq (ω' : X.Ω) (a b : Pt m) :
      restrictedPassageTime (X.ρ ω') univ a b = X.passTime ω' a b := by
    simp [restrictedPassageTime, Setting.passTime, IsotropicVariance.passageTime]
  refine ⟨congrArg g hγ.1, congrArg g hγ.2.1, fun _ _ => mem_univ _, ?_⟩
  have hdensity : (fun x => ENNReal.ofReal (X.ρ (X.act g ω) x)) ∘ g.toIsometryEquiv =
      fun x => ENNReal.ofReal (X.ρ ω x) := by
    funext x
    exact congrArg ENNReal.ofReal (X.covariant g hg ω x)
  rw [heq, Infra.TimeConstant.setting_passTime_covariant X g hg, Infra.TimeConstant.cost_mapCurve,
    hdensity]
  simpa only [heq] using hγ.2.2.2

/-- An `O_s` bound is preserved by composing with a measure-preserving map. -/
lemma isOs_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {φ : Ω → Ω}
    (hφ : MeasurePreserving φ P P) {s θ : ℝ} {Y : Ω → ℝ} (hY : Cited.IsOs P s θ Y) :
    Cited.IsOs P s θ (Y ∘ φ) := by
  refine ⟨hY.1.comp_quasiMeasurePreserving hφ.quasiMeasurePreserving, ?_⟩
  have hF := Infra.Os.aemeasurable_exp_pos_rpow hY.1 s θ
  rw [← hφ.map_eq] at hF
  have hmap := lintegral_map' hF hφ.measurable.aemeasurable
  rw [hφ.map_eq] at hmap
  exact hmap.symm.le.trans hY.2

/-- **Lemma `lem:straight` around any center**, by stationarity (first paragraph of the proof of
Lemma `lem:slab`). -/
theorem exists_straight_scale (h : StraightStatement.{u}) (hm : 1 ≤ m) (X : Setting.{u} m)
    (hnorm : X.IsNormalized) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ∀ z : Pt m,
      ∃ W : X.Ω → ℝ, (∀ ω, Real.log (2 + r) ≤ W ω) ∧
        Cited.IsOs X.P 2 (C * Real.log (2 + r)) W ∧
        ∀ ω, StraightOn X ω (closedBall z r) (C * W ω ^ 2) := by
  obtain ⟨C, hC, hscale⟩ := h m hm X hnorm
  refine ⟨C, hC, fun r hr z => ?_⟩
  obtain ⟨W, hlog, hOs, hstraight⟩ := hscale r hr
  let g : Pt m ≃ᵃⁱ[ℝ] Pt m := AffineIsometryEquiv.constVAdd ℝ (Pt m) (-z)
  have hg : IsProperRigidMotion g := Infra.TimeConstant.isProperRigidMotion_translation (-z)
  have hgapp (x : Pt m) : g x = x - z := by
    change -z +ᵥ x = x - z
    rw [vadd_eq_add]
    abel
  have hball {x : Pt m} (hx : x ∈ closedBall z r) : g x ∈ closedBall (0 : Pt m) r := by
    rw [mem_closedBall_zero_iff, hgapp]
    rwa [mem_closedBall_iff_norm] at hx
  refine ⟨W ∘ X.act g, fun ω => hlog _, isOs_comp (X.measurePreserving_act g hg) hOs,
    fun ω a ha b hb hab γ hγ t ht hfar => ?_⟩
  have hsub (x y : Pt m) : g x - g y = x - y := by
    rw [hgapp, hgapp]
    abel
  have hmap : (Infra.TimeConstant.mapCurve g.toIsometryEquiv γ).toFun t = g (γ.toFun t) := rfl
  have hh := hstraight (X.act g ω) (g a) (hball ha) (g b) (hball hb)
    (fun heq => hab (g.injective heq)) _ (isOneOptimal_act X hg ω hγ) t ht
  rw [hmap, hsub, hsub] at hh
  exact hh hfar

/-- **Subarcs of near-geodesics are near-geodesics** (proof of equation `eq:columns`): the
conclusion of Lemma `lem:straight` for the subarc of `γ` from `γ a` to the end of `γ`. -/
theorem StraightOn.angle_subarc {X : Setting m} {ω : X.Ω} {B : Set (Pt m)} {R : ℝ}
    (h : StraightOn X ω B R) (γ : RectifiableCurve (Pt m)) {u v : Pt m}
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (haB : γ.toFun a ∈ B) (hvB : v ∈ B) (hne : γ.toFun a ≠ v)
    (hfar : R ≤ ‖γ.toFun c - γ.toFun a‖) :
    angle (γ.toFun c - γ.toFun a) (v - γ.toFun a) ≤ 1 / 10 := by
  have ha1 : a < 1 := by
    refine lt_of_le_of_ne (hac.trans hc) fun heq => hne ?_
    rw [heq, hγ.2.1]
  have hsub := oneOptimal_subcurve X ω γ hγ ha ha1.le le_rfl
  rw [hγ.2.1] at hsub
  have h1a : 0 < 1 - a := sub_pos.mpr ha1
  have hparam : Infra.Curves.subParam a 1 ((c - a) / (1 - a)) = c := by
    unfold Infra.Curves.subParam
    rw [div_mul_cancel₀ _ h1a.ne']
    ring
  have hpoint : (γ.subcurve a 1 ha ha1.le le_rfl).toFun ((c - a) / (1 - a)) = γ.toFun c :=
    congrArg γ.toFun hparam
  have hu : (c - a) / (1 - a) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hac) h1a.le,
      (div_le_one h1a).mpr (by linarith only [hc])⟩
  have hh := h _ haB v hvB hne _ hsub _ hu
  rw [hpoint] at hh
  exact hh hfar

end IsotropicVariance.Paper.Proofs.SlabComparison
