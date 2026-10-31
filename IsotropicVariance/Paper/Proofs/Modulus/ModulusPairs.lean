/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
public import IsotropicVariance.Paper.Proofs.Profiles.Basic
public import IsotropicVariance.Infra.Measurability.SlabTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum

/-!
# The small pairs of cubes of the proof of Lemma `lem:modulus`

The proof of Lemma `lem:modulus` reads: "These pairs of points lie in at most `Cγ^{−4d}` pairs of
cubes as in `eq:cubepair` with `s = γn` and `|y| ≤ γn`".

In the frame of a pair `p` (motion `g`, so that `I ⊆ g{t = 0}`, `I' ⊆ g{t = n}`), with `κn` the
cut distance and `σ` the side of the small cubes:
* `nearPair p κn σ c a b`: the cube of side `σ` centered at transverse position `σa` in the face
  of `I`, and the cube centered at `c + σb` in the hyperplane `{t = κn}`;
* `farPair p κn σ c b a`: the cube centered at `c + σb` in `{t = n − κn}` and the cube
  centered at `off + σa` in the face of `I'`.
Their slabs are the thin slabs `g{0 ≤ t ≤ κn}` and `g{n − κn ≤ t ≤ n}`, and the slab passage time
of the pair `p` is at most that of a thin slab between points of the thin slab.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

open IsotropicVariance.Paper.Proofs.Responses (transverseIntegerPoint)
namespace IsotropicVariance.Paper.Proofs.Modulus

open Infra.Slab

variable {m : ℕ}

@[simp] lemma intVec_apply (a : Fin m → ℤ) (k : Fin m) : transverseIntegerPoint a k = a k := rfl

/-- The near pair: a small cube in the face of `I` and a small cube in `{t = κn}`. -/
noncomputable def nearPair (p : CubePair m) (κn σ : ℝ) (c : EuclideanSpace ℝ (Fin m))
    (a b : Fin m → ℤ) : CubePair m :=
  ⟨(AffineIsometryEquiv.constVAdd ℝ (Pt m) (Pt.mk 0 (σ • transverseIntegerPoint a))).trans p.motion,
    κn, σ, σ, (c + σ • transverseIntegerPoint b) - σ • transverseIntegerPoint a⟩

/-- The far pair: a small cube in `{t = n − κn}` and a small cube in the face of `I'`. -/
noncomputable def farPair (p : CubePair m) (κn σ : ℝ) (c : EuclideanSpace ℝ (Fin m))
    (b a : Fin m → ℤ) : CubePair m :=
  ⟨(AffineIsometryEquiv.constVAdd ℝ (Pt m)
      (Pt.mk (p.dist - κn) (c + σ • transverseIntegerPoint b))).trans p.motion, κn, σ, σ,
    (p.offset + σ • transverseIntegerPoint a) - (c + σ • transverseIntegerPoint b)⟩

/-- Membership in the image of a translated set under `g`. -/
lemma mem_motion_image_iff (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (c : Pt m) (A : Set (Pt m)) (x : Pt m) :
    x ∈ ((AffineIsometryEquiv.constVAdd ℝ (Pt m) c).trans g) '' A ↔ g.symm x - c ∈ A := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro h
    refine ⟨g.symm x - c, h, ?_⟩
    simp

lemma mem_nearPair_first (p : CubePair m) (κn σ : ℝ) (c : EuclideanSpace ℝ (Fin m))
    (a b : Fin m → ℤ) {x : Pt m} (h₀ : Pt.lon (p.motion.symm x) = 0)
    (h : ∀ k, |Pt.tr (p.motion.symm x) k - σ * a k| ≤ σ / 2) :
    x ∈ (nearPair p κn σ c a b).first := by
  rw [Paper.CubePair.first, nearPair, mem_motion_image_iff]
  refine ⟨by simp [h₀], fun k => ?_⟩
  simpa using h k

lemma mem_nearPair_second (p : CubePair m) (κn σ : ℝ) (c : EuclideanSpace ℝ (Fin m))
    (a b : Fin m → ℤ) {x : Pt m} (h₀ : Pt.lon (p.motion.symm x) = κn)
    (h : ∀ k, |Pt.tr (p.motion.symm x) k - (c k + σ * b k)| ≤ σ / 2) :
    x ∈ (nearPair p κn σ c a b).second := by
  rw [Paper.CubePair.second, nearPair, mem_motion_image_iff]
  refine ⟨by simp [h₀], fun k => ?_⟩
  have := h k
  simp only [Pt.tr_sub, Pt.tr_mk, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    intVec_apply]
  convert this using 2
  ring

lemma mem_farPair_first (p : CubePair m) (κn σ : ℝ) (c : EuclideanSpace ℝ (Fin m))
    (b a : Fin m → ℤ) {x : Pt m} (h₀ : Pt.lon (p.motion.symm x) = p.dist - κn)
    (h : ∀ k, |Pt.tr (p.motion.symm x) k - (c k + σ * b k)| ≤ σ / 2) :
    x ∈ (farPair p κn σ c b a).first := by
  rw [Paper.CubePair.first, farPair, mem_motion_image_iff]
  refine ⟨by simp [h₀], fun k => ?_⟩
  simpa using h k

lemma mem_farPair_second (p : CubePair m) (κn σ : ℝ) (c : EuclideanSpace ℝ (Fin m))
    (b a : Fin m → ℤ) {x : Pt m} (h₀ : Pt.lon (p.motion.symm x) = p.dist)
    (h : ∀ k, |Pt.tr (p.motion.symm x) k - (p.offset k + σ * a k)| ≤ σ / 2) :
    x ∈ (farPair p κn σ c b a).second := by
  rw [Paper.CubePair.second, farPair, mem_motion_image_iff]
  refine ⟨by simp [h₀], fun k => ?_⟩
  have := h k
  simp only [Pt.tr_sub, Pt.tr_mk, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    intVec_apply]
  convert this using 2
  ring

lemma nearPair_isAdmissible (p : CubePair m) {κn σ W : ℝ} {c : EuclideanSpace ℝ (Fin m)}
    {a b : Fin m → ℤ} (hσ : 0 ≤ σ) (hσW : σ ≤ 4 * W)
    (hoff : ‖(c + σ • transverseIntegerPoint b) - σ • transverseIntegerPoint a‖ ≤ κn) :
    (nearPair p κn σ c a b).IsAdmissible κn W 1 :=
  ⟨rfl, hσ, hσW, hσ, hσW, div_le_one_of_le₀ hoff ((norm_nonneg _).trans hoff)⟩

lemma farPair_isAdmissible (p : CubePair m) {κn σ W : ℝ} {c : EuclideanSpace ℝ (Fin m)}
    {a b : Fin m → ℤ} (hσ : 0 ≤ σ) (hσW : σ ≤ 4 * W)
    (hoff : ‖(p.offset + σ • transverseIntegerPoint a) - (c + σ • transverseIntegerPoint b)‖ ≤ κn) :
    (farPair p κn σ c b a).IsAdmissible κn W 1 :=
  ⟨rfl, hσ, hσW, hσ, hσW, div_le_one_of_le₀ hoff ((norm_nonneg _).trans hoff)⟩

/-! ## Thin slabs -/

lemma slabCoord_translate (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (c : Pt m) (w : ℝ) (x : Pt m) :
    slabCoord ⟨(AffineIsometryEquiv.constVAdd ℝ (Pt m) c).trans g, w⟩ x =
      slabCoord ⟨g, w⟩ x - Pt.lon c := by
  have h : (AffineIsometryEquiv.constVAdd ℝ (Pt m) c).symm (g.symm x) = g.symm x - c := by
    rw [AffineIsometryEquiv.symm_apply_eq]
    simp [vadd_eq_add]
  simp only [slabCoord, AffineIsometryEquiv.coe_symm_trans, Function.comp_apply, h]
  rfl

lemma slabCoord_nearPair (p : CubePair m) (κn σ : ℝ) (c : EuclideanSpace ℝ (Fin m))
    (a b : Fin m → ℤ) (x : Pt m) :
    slabCoord (nearPair p κn σ c a b).slab x = slabCoord p.slab x := by
  have := slabCoord_translate p.motion (Pt.mk 0 (σ • transverseIntegerPoint a)) κn x
  simp only [Pt.lon_mk, sub_zero] at this
  exact this

lemma slabCoord_farPair (p : CubePair m) (κn σ : ℝ) (c : EuclideanSpace ℝ (Fin m))
    (b a : Fin m → ℤ) (x : Pt m) :
    slabCoord (farPair p κn σ c b a).slab x = slabCoord p.slab x - (p.dist - κn) := by
  have := slabCoord_translate p.motion (Pt.mk (p.dist - κn) (c + σ • transverseIntegerPoint b)) κn x
  simp only [Pt.lon_mk] at this
  exact this

/-- The passage time `T_σ` is monotone in the density. -/
lemma passageTime_mono {σ τ : Pt m → ℝ} (hστ : ∀ x, σ x ≤ τ x) {B : ℝ} (hτB : ∀ x, τ x ≤ B)
    (u v : Pt m) : passageTime σ u v ≤ passageTime τ u v := by
  rw [passageTime_eq_infra, passageTime_eq_infra]
  refine ENNReal.toReal_mono (Profiles.infraPassageTime_ne_top hτB u v) ?_
  unfold Infra.Measurability.passageTime
  exact iInf_mono fun γ => iInf_mono fun _ => iInf_mono fun _ =>
    lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hστ _)

/-- **A thin slab bounds the slab passage time**: if a slab `thin` of the same direction lies
in `big` (coordinates `t − t₀`) and every point of `thin` at distance more than one from its
faces is at distance more than one from the faces of `big`, then `D_big ≤ D_thin` on `thin`. -/
theorem slabTime_le_thin (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (big thin : Slab m)
    {t₀ : ℝ} (hcoord : ∀ x, slabCoord thin x = slabCoord big x - t₀) (ht₀ : 0 ≤ t₀)
    (hw : t₀ + thin.width ≤ big.width)
    (hfaces : ∀ x ∈ thin.set, 1 < infDist x thin.faces → 1 < infDist x big.faces)
    (ω : X.Ω) {u v : Pt m} (hu : u ∈ thin.set) (hv : v ∈ thin.set) :
    X.slabTime b big ω u v ≤ X.slabTime b thin ω u v := by
  have hsub : thin.set ⊆ big.set := fun x hx => by
    rw [mem_slab_set_iff] at hx ⊢
    rw [hcoord] at hx
    constructor <;> linarith [hx.1, hx.2]
  rw [slabTime_eq_passageTime_ext X hb big ω (hsub hu) (hsub hv),
    slabTime_eq_passageTime_ext X hb thin ω hu hv]
  refine passageTime_mono ?_ (fun x => extDensity_le thin (hb ω) x) u v
  intro x
  by_cases hx : x ∈ thin.set
  · rw [extDensity_of_mem _ _ _ hx, extDensity_of_mem _ _ _ (hsub hx)]
    unfold Slab.density
    by_cases hd : infDist x thin.faces ≤ 1
    · simp only [hd, ↓reduceIte]
      split_ifs
      · exact le_rfl
      · exact hb ω x
    · have h2 := hfaces x hx (not_le.mp hd)
      simp only [hd, not_le.mpr h2, ↓reduceIte, le_refl]
  · rw [extDensity_of_notMem _ _ _ hx]
    exact extDensity_le big (hb ω) x

end IsotropicVariance.Paper.Proofs.Modulus
