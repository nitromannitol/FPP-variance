/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusPairs
public import IsotropicVariance.Paper.Proofs.Modulus.ModulusGeometry
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum
import IsotropicVariance.Paper.Defs.SetTime

/-!
# Covering the cut points by small pairs of cubes (the proof of Lemma `lem:modulus`)

For a pair `p` with centers of slope at most `1/2`, a point `x` at coordinate `ℓ₀` across the slab
of `p` and within `λ` of a segment `[u, v]`, `u ∈ I`, `v ∈ I'`, has transverse coordinate within
`3λ/2 + √m(side₁ + side₂)/2` of `(ℓ₀/n) · offset` (`transverse_near_segment`). Rounding to the grid
of mesh `σ` (`round`) puts the cut points and the endpoints into the small cubes of the near and
far pairs of `ModulusPairs`, with indices in a finite box. The faces of the thin slabs are far from
the other face of the slab of `p`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Modulus

open Infra.Slab

variable {m : ℕ}

/-! ## Coordinates in the frame of a pair -/

lemma frame_first {p : CubePair m} {u : Pt m} (hu : u ∈ p.first) :
    Pt.lon (p.motion.symm u) = 0 ∧ ∀ k, |Pt.tr (p.motion.symm u) k| ≤ p.side₁ / 2 := by
  obtain ⟨z, hz, rfl⟩ := hu
  simpa using hz

lemma frame_second {p : CubePair m} {v : Pt m} (hv : v ∈ p.second) :
    Pt.lon (p.motion.symm v) = p.dist ∧
      ∀ k, |Pt.tr (p.motion.symm v) k - p.offset k| ≤ p.side₂ / 2 := by
  obtain ⟨z, hz, rfl⟩ := hv
  simpa using hz

/-- **The transverse position of a point near a segment between the cubes.** -/
theorem transverse_near_segment {p : CubePair m} (hn : 0 < p.dist)
    (hoff : ‖p.offset‖ ≤ p.dist / 2) (h1 : 0 ≤ p.side₁) (h2 : 0 ≤ p.side₂)
    {u v x : Pt m} (hu : u ∈ p.first) (hv : v ∈ p.second) {lam ℓ₀ : ℝ}
    (hx : infDist x (segment ℝ u v) ≤ lam) (hℓ₀ : Pt.lon (p.motion.symm x) = ℓ₀) :
    ‖Pt.tr (p.motion.symm x) - (ℓ₀ / p.dist) • p.offset‖ ≤
      3 / 2 * lam + Real.sqrt m * ((p.side₁ + p.side₂) / 2) := by
  obtain ⟨hu0, hu1⟩ := frame_first hu
  obtain ⟨hv0, hv1⟩ := frame_second hv
  set g := p.motion.symm with hg
  obtain ⟨s, hs, hd⟩ := (isCompact_segment' u v).exists_infDist_eq_dist
    ⟨u, left_mem_segment ℝ u v⟩ x
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hs
  have hxs : dist x (a • u + b • v) ≤ lam := hd ▸ hx
  have hgs : g (a • u + b • v) = a • g u + b • g v :=
    Convex.combo_affine_apply (f := g.toAffineEquiv.toAffineMap) hab
  have hdist : ‖g x - (a • g u + b • g v)‖ ≤ lam := by
    rw [← hgs, ← dist_eq_norm, g.dist_map]; exact hxs
  have hlon : |ℓ₀ - b * p.dist| ≤ lam := by
    have := Profiles.abs_lon_le_norm (g x - (a • g u + b • g v))
    rw [Pt.lon_sub, Pt.lon_add, Pt.lon_smul, Pt.lon_smul, hℓ₀, hu0, hv0] at this
    simp only [mul_zero, zero_add] at this
    exact this.trans hdist
  have htr_u : ‖Pt.tr (g u)‖ ≤ Real.sqrt m * (p.side₁ / 2) :=
    Profiles.norm_le_of_abs_le (by positivity) hu1
  have htr_v : ‖Pt.tr (g v) - p.offset‖ ≤ Real.sqrt m * (p.side₂ / 2) :=
    Profiles.norm_le_of_abs_le (by positivity) fun k => by simpa using hv1 k
  have hid : Pt.tr (g x) - (ℓ₀ / p.dist) • p.offset =
      (Pt.tr (g x) - Pt.tr (a • g u + b • g v)) + (a • Pt.tr (g u) +
        b • (Pt.tr (g v) - p.offset)) + ((b - ℓ₀ / p.dist) • p.offset) := by
    simp only [Pt.tr_add, Pt.tr_smul, smul_sub, sub_smul]
    abel
  rw [hid]
  have e1 : ‖Pt.tr (g x) - Pt.tr (a • g u + b • g v)‖ ≤ lam := by
    rw [← Pt.tr_sub]; exact (Profiles.norm_tr_le_norm _).trans hdist
  have e2 : ‖a • Pt.tr (g u) + b • (Pt.tr (g v) - p.offset)‖ ≤
      Real.sqrt m * ((p.side₁ + p.side₂) / 2) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg hb]
    have ha1 : a ≤ 1 := by linarith
    have hb1 : b ≤ 1 := by linarith
    have k1 := mul_le_of_le_one_left (norm_nonneg (Pt.tr (g u))) ha1
    have k2 := mul_le_of_le_one_left (norm_nonneg (Pt.tr (g v) - p.offset)) hb1
    have k3 : Real.sqrt m * ((p.side₁ + p.side₂) / 2) =
        Real.sqrt m * (p.side₁ / 2) + Real.sqrt m * (p.side₂ / 2) := by ring
    linarith
  have e3 : ‖(b - ℓ₀ / p.dist) • p.offset‖ ≤ lam / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have h3 : |b - ℓ₀ / p.dist| ≤ lam / p.dist := by
      rw [show b - ℓ₀ / p.dist = -(ℓ₀ - b * p.dist) / p.dist by field_simp; ring, abs_div,
        abs_neg, abs_of_pos hn]
      exact div_le_div_of_nonneg_right hlon hn.le
    calc |b - ℓ₀ / p.dist| * ‖p.offset‖ ≤ lam / p.dist * (p.dist / 2) :=
          mul_le_mul h3 hoff (norm_nonneg _) (by
            have : 0 ≤ lam := infDist_nonneg.trans hx; positivity)
      _ = lam / 2 := by field_simp
  calc _ ≤ ‖Pt.tr (g x) - Pt.tr (a • g u + b • g v) + (a • Pt.tr (g u) +
        b • (Pt.tr (g v) - p.offset))‖ + ‖(b - ℓ₀ / p.dist) • p.offset‖ := norm_add_le _ _
    _ ≤ (lam + Real.sqrt m * ((p.side₁ + p.side₂) / 2)) + lam / 2 :=
        add_le_add ((norm_add_le _ _).trans (add_le_add e1 e2)) e3
    _ = 3 / 2 * lam + Real.sqrt m * ((p.side₁ + p.side₂) / 2) := by ring

/-! ## Rounding to the grid -/

/-- Rounding a transverse position to the grid of mesh `σ`. -/
lemma exists_round (y : EuclideanSpace ℝ (Fin m)) {σ : ℝ} (hσ : 0 < σ) :
    ∃ a : Fin m → ℤ, (∀ k, |y k - σ * a k| ≤ σ / 2) ∧ ∀ k, |(a k : ℝ)| ≤ ‖y‖ / σ + 1 / 2 := by
  refine ⟨fun k => round (y k / σ), fun k => ?_, fun k => ?_⟩
  · have h := abs_sub_round (y k / σ)
    have : y k - σ * (round (y k / σ) : ℝ) = σ * (y k / σ - round (y k / σ)) := by
      field_simp
    rw [this, abs_mul, abs_of_pos hσ]
    nlinarith
  · have h := abs_sub_round (y k / σ)
    have hy : |y k| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le y k
    have h2 : |y k / σ| ≤ ‖y‖ / σ := by
      rw [abs_div, abs_of_pos hσ]; exact div_le_div_of_nonneg_right hy hσ.le
    have h3 := abs_sub_abs_le_abs_sub (round (y k / σ) : ℝ) (y k / σ)
    rw [abs_sub_comm] at h3
    linarith

/-- The integer vectors with coordinates in `[−L, L]`. -/
noncomputable def box (m L : ℕ) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(L : ℤ)) L

lemma mem_box {L : ℕ} {a : Fin m → ℤ} (h : ∀ k, |(a k : ℝ)| ≤ L) : a ∈ box m L := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro k
  have hk := h k
  rw [← Int.cast_abs, ← Int.cast_natCast, Int.cast_le] at hk
  exact abs_le.mp hk

lemma norm_intVec_le {L : ℕ} {a : Fin m → ℤ} (ha : a ∈ box m L) :
    ‖Responses.transverseIntegerPoint a‖ ≤ Real.sqrt m * L := by
  refine Profiles.norm_le_of_abs_le (Nat.cast_nonneg L) fun k => ?_
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc] at ha
  rw [intVec_apply, ← Int.cast_abs, ← Int.cast_natCast]
  exact Int.cast_le.mpr (abs_le.mpr (ha k))

/-! ## The thin slabs are far from the other face -/

lemma abs_slabCoord_sub_le (sl : Slab m) (x y : Pt m) :
    |slabCoord sl x - slabCoord sl y| ≤ dist x y := by
  have hl := (lipschitzWith_slabCoord sl).dist_le_mul x y
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hl

/-- The thin slab of a near pair is far from the second face. -/
lemma hfaces_near (p : CubePair m) {κn σ : ℝ} (c : EuclideanSpace ℝ (Fin m)) (a b : Fin m → ℤ)
    (hκ : κn + 1 < p.dist) :
    ∀ x ∈ (nearPair p κn σ c a b).slab.set,
      1 < infDist x (nearPair p κn σ c a b).slab.faces → 1 < infDist x p.slab.faces := by
  intro x hx hd
  rw [mem_slab_set_iff, slabCoord_nearPair] at hx
  have hle : min (infDist x (nearPair p κn σ c a b).slab.faces) (p.dist - κn) ≤
      infDist x p.slab.faces := by
    refine (le_infDist p.slab.faces_nonempty).mpr fun y hy => ?_
    rcases (mem_slab_faces_iff _).mp hy with h | h
    · refine (min_le_left _ _).trans (infDist_le_dist_of_mem ?_)
      rw [mem_slab_faces_iff, slabCoord_nearPair]
      exact Or.inl h
    · have hl := abs_slabCoord_sub_le p.slab x y
      have hw : (nearPair p κn σ c a b).slab.width = κn := rfl
      have hy' : slabCoord p.slab y = p.dist := h
      rw [abs_le] at hl
      refine (min_le_right _ _).trans ?_
      rw [hw] at hx
      linarith [hx.2, hl.1]
  exact lt_of_lt_of_le (lt_min hd (by linarith)) hle

/-- The thin slab of a far pair is far from the first face. -/
lemma hfaces_far (p : CubePair m) {κn σ : ℝ} (c : EuclideanSpace ℝ (Fin m)) (b a : Fin m → ℤ)
    (hκ : κn + 1 < p.dist) :
    ∀ x ∈ (farPair p κn σ c b a).slab.set,
      1 < infDist x (farPair p κn σ c b a).slab.faces → 1 < infDist x p.slab.faces := by
  intro x hx hd
  rw [mem_slab_set_iff, slabCoord_farPair] at hx
  have hle : min (infDist x (farPair p κn σ c b a).slab.faces) (p.dist - κn) ≤
      infDist x p.slab.faces := by
    refine (le_infDist p.slab.faces_nonempty).mpr fun y hy => ?_
    rcases (mem_slab_faces_iff _).mp hy with h | h
    · have hl := abs_slabCoord_sub_le p.slab x y
      rw [abs_le] at hl
      refine (min_le_right _ _).trans ?_
      linarith [hx.1, hl.2]
    · refine (min_le_left _ _).trans (infDist_le_dist_of_mem ?_)
      rw [mem_slab_faces_iff, slabCoord_farPair]
      right
      rw [h]
      have : (farPair p κn σ c b a).slab.width = κn := rfl
      rw [this, show p.slab.width = p.dist from rfl]
      ring
  exact lt_of_lt_of_le (lt_min hd (by linarith)) hle

end IsotropicVariance.Paper.Proofs.Modulus
