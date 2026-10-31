/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusPointwise
public import IsotropicVariance.Paper.Proofs.Profiles.RowEnergySetup
public import IsotropicVariance.Infra.Os.Maximum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The union bound over the small pairs (the proof of Lemma `lem:modulus`)

The proof of Lemma `lem:modulus` reads: "`eq:profiles` and the union bound `eq:union` give
`D ≤ O_1(C Q_{γn} log(2/γ))`".

For a pair `p`, the cut distance `κn` and the side `σ` of the small cubes, the family
`smallFamily` collects, over the indices of the index box `box m L`, the profile suprema
`sup |D − |·||` of the near and far small pairs, for `D = T` and for their thin-slab passage
times. Its maximum `smallMax` is `O_1` by the union bound. A cut point near its expected
transverse position, and an endpoint in a cube, lie in one small pair (`near_mem`, `far_mem`), so
the end-piece deviations are at most `smallMax` (`le_pairSup`, `le_smallMax`).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Modulus

open Infra.Slab Cited Infra.Os

variable {m : ℕ}

/-- The supremum of `|D(u, v) − |v − u||` over `I × I'`. -/
noncomputable def pairSup (D : Pt m → Pt m → ℝ) (I I' : Set (Pt m)) : ℝ :=
  ⨆ (u : I) (v : I'), |D u v - dist (u : Pt m) v|

/-- The expected transverse position of the near cut point. -/
noncomputable def nearCenter (p : CubePair m) (κn : ℝ) : EuclideanSpace ℝ (Fin m) :=
  (κn / p.dist) • p.offset

/-- The expected transverse position of the far cut point. -/
noncomputable def farCenter (p : CubePair m) (κn : ℝ) : EuclideanSpace ℝ (Fin m) :=
  ((p.dist - κn) / p.dist) • p.offset

/-- The family of the union bound. -/
noncomputable def smallFamily (X : Setting m) (b : ℝ) (p : CubePair m) (κn σ : ℝ)
    (q : Fin 4 × ((Fin m → ℤ) × (Fin m → ℤ))) (ω : X.Ω) : ℝ :=
  (![pairSup (X.passTime ω) (nearPair p κn σ (nearCenter p κn) q.2.1 q.2.2).first
      (nearPair p κn σ (nearCenter p κn) q.2.1 q.2.2).second,
    pairSup (X.slabTime b (nearPair p κn σ (nearCenter p κn) q.2.1 q.2.2).slab ω)
      (nearPair p κn σ (nearCenter p κn) q.2.1 q.2.2).first
      (nearPair p κn σ (nearCenter p κn) q.2.1 q.2.2).second,
    pairSup (X.passTime ω) (farPair p κn σ (farCenter p κn) q.2.1 q.2.2).first
      (farPair p κn σ (farCenter p κn) q.2.1 q.2.2).second,
    pairSup (X.slabTime b (farPair p κn σ (farCenter p κn) q.2.1 q.2.2).slab ω)
      (farPair p κn σ (farCenter p κn) q.2.1 q.2.2).first
      (farPair p κn σ (farCenter p κn) q.2.1 q.2.2).second] : Fin 4 → ℝ) q.1

/-- The indices of the union bound. -/
noncomputable def smallIndex (m L : ℕ) : Finset (Fin 4 × ((Fin m → ℤ) × (Fin m → ℤ))) :=
  Finset.univ ×ˢ (box m L ×ˢ box m L)

lemma smallIndex_nonempty (m L : ℕ) : (smallIndex m L).Nonempty := by
  refine ⟨(0, (0, 0)), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
    ⟨mem_box fun k => by simp, mem_box fun k => by simp⟩⟩⟩

lemma card_smallIndex (m L : ℕ) :
    ((smallIndex m L).card : ℝ) = 4 * ((box m L).card : ℝ) ^ 2 := by
  simp [smallIndex, Finset.card_product, sq]

/-- The maximum of the family. -/
noncomputable def smallMax (X : Setting m) (b : ℝ) (p : CubePair m) (κn σ : ℝ) (L : ℕ)
    (ω : X.Ω) : ℝ :=
  (smallIndex m L).sup' (smallIndex_nonempty m L) (fun q => smallFamily X b p κn σ q ω)

lemma le_smallMax (X : Setting m) (b : ℝ) (p : CubePair m) (κn σ : ℝ) {L : ℕ}
    {q : Fin 4 × ((Fin m → ℤ) × (Fin m → ℤ))} (hq : q ∈ smallIndex m L) (ω : X.Ω) :
    smallFamily X b p κn σ q ω ≤ smallMax X b p κn σ L ω :=
  Finset.le_sup' (fun q => smallFamily X b p κn σ q ω) hq

/-- **The union bound**: if every member of the family is `O_1(θ)`, their maximum is
`O_1(2θ log(2 + 4|box|²)/log 2)`. -/
theorem isOs_smallMax (X : Setting m) (b : ℝ) (p : CubePair m) (κn σ : ℝ) (L : ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hfam : ∀ q ∈ smallIndex m L, IsOs X.P 1 θ (smallFamily X b p κn σ q)) :
    IsOs X.P 1 (2 / Real.log 2 * θ * Real.log (2 + 4 * ((box m L).card : ℝ) ^ 2))
      (smallMax X b p κn σ L) := by
  have h := isOs_finset_sup'_log one_pos hθ (smallIndex m L) (smallIndex_nonempty m L)
    (smallFamily X b p κn σ) hfam
  simp only [div_one, Real.rpow_one, card_smallIndex] at h
  have heq : (smallIndex m L).sup' (smallIndex_nonempty m L) (smallFamily X b p κn σ) =
      smallMax X b p κn σ L := by
    funext ω
    rw [Finset.sup'_apply]
    rfl
  rwa [heq] at h

/-! ## Membership in a small pair -/

lemma round_box {y : EuclideanSpace ℝ (Fin m)} {σ R : ℝ} {L : ℕ} (hσ : 0 < σ)
    (hy : ‖y‖ ≤ R) (hL : R / σ + 1 / 2 ≤ L) :
    ∃ a : Fin m → ℤ, a ∈ box m L ∧ ∀ k, |y k - σ * a k| ≤ σ / 2 := by
  obtain ⟨a, ha, hab⟩ := exists_round y hσ
  refine ⟨a, mem_box fun k => (hab k).trans ?_, ha⟩
  have : ‖y‖ / σ ≤ R / σ := div_le_div_of_nonneg_right hy hσ.le
  linarith

lemma mem_smallIndex {L : ℕ} (i : Fin 4) {a b : Fin m → ℤ} (ha : a ∈ box m L)
    (hb : b ∈ box m L) : (i, (a, b)) ∈ smallIndex m L :=
  Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨ha, hb⟩⟩

lemma near_mem {p : CubePair m} {κn σ R : ℝ} {L : ℕ} (hσ : 0 < σ) (h1 : 0 ≤ p.side₁)
    (hLu : Real.sqrt m * (p.side₁ / 2) / σ + 1 / 2 ≤ L) (hLx : R / σ + 1 / 2 ≤ L)
    {u x : Pt m} (hu : u ∈ p.first) (hx : slabCoord p.slab x = κn)
    (hxt : ‖Pt.tr (p.motion.symm x) - nearCenter p κn‖ ≤ R) :
    ∃ a b : Fin m → ℤ, a ∈ box m L ∧ b ∈ box m L ∧
      u ∈ (nearPair p κn σ (nearCenter p κn) a b).first ∧
      x ∈ (nearPair p κn σ (nearCenter p κn) a b).second := by
  obtain ⟨hu0, hu1⟩ := frame_first hu
  obtain ⟨a, ha, hau⟩ := round_box hσ (Profiles.norm_le_of_abs_le (by positivity) hu1) hLu
  obtain ⟨b, hb, hbx⟩ := round_box hσ hxt hLx
  refine ⟨a, b, ha, hb, mem_nearPair_first p κn σ _ a b hu0 hau,
    mem_nearPair_second p κn σ _ a b hx fun k => ?_⟩
  have := hbx k
  simp only [PiLp.sub_apply] at this
  rw [show Pt.tr (p.motion.symm x) k - (nearCenter p κn k + σ * b k) =
    Pt.tr (p.motion.symm x) k - nearCenter p κn k - σ * b k by ring]
  exact this

lemma far_mem {p : CubePair m} {κn σ R : ℝ} {L : ℕ} (hσ : 0 < σ) (h2 : 0 ≤ p.side₂)
    (hLv : Real.sqrt m * (p.side₂ / 2) / σ + 1 / 2 ≤ L) (hLy : R / σ + 1 / 2 ≤ L)
    {y v : Pt m} (hy : slabCoord p.slab y = p.dist - κn)
    (hyt : ‖Pt.tr (p.motion.symm y) - farCenter p κn‖ ≤ R) (hv : v ∈ p.second) :
    ∃ b a : Fin m → ℤ, b ∈ box m L ∧ a ∈ box m L ∧
      y ∈ (farPair p κn σ (farCenter p κn) b a).first ∧
      v ∈ (farPair p κn σ (farCenter p κn) b a).second := by
  obtain ⟨hv0, hv1⟩ := frame_second hv
  obtain ⟨b, hb, hby⟩ := round_box hσ hyt hLy
  obtain ⟨a, ha, hav⟩ := round_box (y := Pt.tr (p.motion.symm v) - p.offset) hσ
    (Profiles.norm_le_of_abs_le (by positivity) fun k => by simpa using hv1 k) hLv
  refine ⟨b, a, hb, ha, mem_farPair_first p κn σ _ b a hy fun k => ?_,
    mem_farPair_second p κn σ _ b a hv0 fun k => ?_⟩
  · have := hby k
    simp only [PiLp.sub_apply] at this
    rw [show Pt.tr (p.motion.symm y) k - (farCenter p κn k + σ * b k) =
      Pt.tr (p.motion.symm y) k - farCenter p κn k - σ * b k by ring]
    exact this
  · have := hav k
    simp only [PiLp.sub_apply] at this
    rw [show Pt.tr (p.motion.symm v) k - (p.offset k + σ * a k) =
      Pt.tr (p.motion.symm v) k - p.offset k - σ * a k by ring]
    exact this

/-- A point of `I × I'` is below the profile supremum, if the deviations are bounded. -/
lemma le_pairSup {D : Pt m → Pt m → ℝ} {I I' : Set (Pt m)} {c : ℝ}
    (hc : ∀ u ∈ I, ∀ v ∈ I', |D u v - dist u v| ≤ c) {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I') :
    |D u v - dist u v| ≤ pairSup D I I' := by
  have hb : BddAbove (range fun q : I × I' => |D q.1 q.2 - dist (q.1 : Pt m) q.2|) :=
    ⟨c, by rintro _ ⟨q, rfl⟩; exact hc q.1 q.1.2 q.2 q.2.2⟩
  unfold pairSup
  rw [Profiles.iSup_iSup_eq_iSup_prod hb]
  exact le_ciSup (f := fun q : I × I' => |D q.1 q.2 - dist (q.1 : Pt m) q.2|) hb
    (⟨u, hu⟩, ⟨v, hv⟩)

end IsotropicVariance.Paper.Proofs.Modulus
