/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusUnion
public import IsotropicVariance.Paper.Proofs.Modulus.RadiusPointwise
public import IsotropicVariance.Paper.Proofs.SlabComparison.ExistsNearOptimal
public import IsotropicVariance.Paper.Proofs.Localization.Measurable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The pointwise modulus bound for the slab passage time

The abstract `ModulusData` of `ModulusPointwise` holds, on the event where the 1-optimal curves
stay within `λ` of their segments, for the slab passage time of the pair (the slab density on the
slab), with `U` the maximum of the union bound (`smallMax`): `modulusData_slabTime`. The geometric
thresholds are collected in `CutData`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Modulus

open Infra.Slab Infra.Os

variable {m : ℕ}

/-- The geometric thresholds of the proof of Lemma `lem:modulus`. -/
structure CutData (p : CubePair m) (κn σ lam : ℝ) (L : ℕ) : Prop where
  hn : 0 < p.dist
  hoff : ‖p.offset‖ ≤ p.dist / 2
  h1 : 0 ≤ p.side₁
  h2 : 0 ≤ p.side₂
  hκ0 : 0 < κn
  hκ : 2 * κn ≤ p.dist
  hκ1 : κn + 1 < p.dist
  hσ : 0 < σ
  hlam : 0 ≤ lam
  hLu : Real.sqrt m * (p.side₁ / 2) / σ + 1 / 2 ≤ L
  hLv : Real.sqrt m * (p.side₂ / 2) / σ + 1 / 2 ≤ L
  hLx : (3 / 2 * lam + Real.sqrt m * ((p.side₁ + p.side₂) / 2)) / σ + 1 / 2 ≤ L

/-- Distances between two cubes of a pair are bounded. -/
lemma exists_dist_bound (q : CubePair m) (h1 : 0 ≤ q.side₁) (h2 : 0 ≤ q.side₂) :
    ∃ C, ∀ u ∈ q.first, ∀ v ∈ q.second, dist u v ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1
    ((Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_first q h1)).isBounded.union
      (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_second q h2)).isBounded)
  exact ⟨C, fun u hu v hv => hC (mem_union_left _ hu) (mem_union_right _ hv)⟩

lemma pairBound_passTime (X : Setting m) {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd)
    (q : CubePair m) (h1 : 0 ≤ q.side₁) (h2 : 0 ≤ q.side₂) (ω : X.Ω) :
    ∃ c, ∀ u ∈ q.first, ∀ v ∈ q.second, |X.passTime ω u v - dist u v| ≤ c := by
  obtain ⟨C, hC⟩ := exists_dist_bound q h1 h2
  refine ⟨(Bd + 1) * C, fun u hu v hv => ?_⟩
  have hT := Profiles.passTime_le_mul_dist hBd hBd0 ω u v
  have hT0 := Profiles.passTime_nonneg ω u v
  have hd := hC u hu v hv
  have hd0 := dist_nonneg (x := u) (y := v)
  rw [abs_le]; constructor <;> nlinarith

lemma pairBound_slabTime (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (q : CubePair m)
    (h1 : 0 ≤ q.side₁) (h2 : 0 ≤ q.side₂) (hq : 0 ≤ q.dist) (ω : X.Ω) :
    ∃ c, ∀ u ∈ q.first, ∀ v ∈ q.second, |X.slabTime b q.slab ω u v - dist u v| ≤ c := by
  obtain ⟨C, hC⟩ := exists_dist_bound q h1 h2
  have hb0 := upperBound_nonneg X hb ω
  refine ⟨(b + 1) * C, fun u hu v hv => ?_⟩
  have hD := slabTime_le_mul_dist X hb q.slab ω (Profiles.cubePair_first_subset_set q hq hu)
    (Profiles.cubePair_second_subset_set q hq hv)
  have hD0 := slabTime_nonneg X b q.slab ω u v
  have hd := hC u hu v hv
  have hd0 := dist_nonneg (x := u) (y := v)
  rw [abs_le]; constructor <;> nlinarith

/-- A 1-optimal curve exists in a convex set for a bounded density. -/
lemma exists_isOneOptimal_restricted {σ : Pt m → ℝ} {B : ℝ} (hB : ∀ x, σ x ≤ B)
    {S : Set (Pt m)} (hS : Convex ℝ S) {u v : Pt m} (hu : u ∈ S) (hv : v ∈ S) :
    ∃ γ : RectifiableCurve (Pt m), IsOneOptimal σ S u v γ := by
  have hfin := restrictedInf_ne_top hB hS hu hv
  have hlt : restrictedInf σ S u v < restrictedInf σ S u v + 1 :=
    ENNReal.lt_add_right hfin one_ne_zero
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
  obtain ⟨h0, hγ⟩ := iInf_lt_iff.mp hγ
  obtain ⟨h1, hγ⟩ := iInf_lt_iff.mp hγ
  obtain ⟨hS', hγ⟩ := iInf_lt_iff.mp hγ
  exact ⟨γ, (Localization.isOneOptimal_iff hB).2 ⟨h0, h1, hS', hγ.le⟩⟩

/-- The deviation bound of `hgood` from the localization functional. -/
lemma hgood_of_le {σ : Pt m → ℝ} {S : Set (Pt m)} {p : CubePair m} {a B lam : ℝ} (ha : 0 < a)
    (haσ : ∀ x, a ≤ σ x) (hT : ∀ u ∈ S, ∀ v ∈ S, restrictedPassageTime σ S u v ≤ B * dist u v)
    (h1 : 0 ≤ p.side₁) (h2 : 0 ≤ p.side₂)
    (hgood : Contracts.maxSegmentDeviation σ S p.first p.second ≤ lam) :
    ∀ u ∈ p.first, ∀ v ∈ p.second, ∀ γ : RectifiableCurve (Pt m),
      IsOneOptimal σ S u v γ → ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ u v) ≤ lam := by
  obtain ⟨R, hR⟩ := Localization.exists_dist_le_of_isOneOptimal (Θ := Unit) (σ := fun _ => σ) (S := S)
    (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_first p h1)).isBounded
    (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_second p h2)).isBounded ha
    (fun _ x => haσ x) (fun _ => hT)
  intro u hu v hv γ hγ t ht
  refine (infDist_le_maxSegmentDeviation (B := R) (fun u hu v hv γ hγ t ht =>
    (infDist_le_dist_of_mem (left_mem_segment ℝ u v)).trans (hR () u hu v hv γ hγ t ht))
    hu hv hγ ht).trans hgood

/-- **The pointwise data for the slab passage time of the pair.** -/
theorem modulusData_slabTime (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {Bd : ℝ}
    (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd) {p : CubePair m} {κn σ lam : ℝ} {L : ℕ}
    (H : CutData p κn σ lam L) (ω : X.Ω)
    (hgood : Contracts.maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first
      p.second ≤ lam) :
    ModulusData p (X.ρ ω) (p.slab.density b (X.ρ ω)) p.slab.set b κn lam
      (max (smallMax X b p κn σ L ω) 0) := by
  obtain ⟨a, b', ha, hab⟩ := X.bounds
  have hσB : ∀ x, p.slab.density b (X.ρ ω) x ≤ b := fun x => by
    have := Slab.density_le p.slab b (hb ω) x
    rwa [max_self] at this
  have hIS := Profiles.cubePair_first_subset_set p H.hn.le
  have hI'S := Profiles.cubePair_second_subset_set p H.hn.le
  have hdT : ∀ q : CubePair m, q.side₁ = σ → q.side₂ = σ → ∀ i : Fin 4,
      ∀ (ij : (Fin m → ℤ) × (Fin m → ℤ)), ij ∈ box m L ×ˢ box m L →
      ∀ u ∈ q.first, ∀ v ∈ q.second,
      pairSup (X.passTime ω) q.first q.second = smallFamily X b p κn σ (i, ij) ω →
      |passageTime (X.ρ ω) u v - dist u v| ≤ max (smallMax X b p κn σ L ω) 0 := by
    intro q hq1 hq2 i ij hij u hu v hv heq
    obtain ⟨c, hc⟩ := pairBound_passTime X hBd hBd0 q (hq1 ▸ H.hσ.le) (hq2 ▸ H.hσ.le) ω
    refine (le_pairSup hc hu hv).trans ((le_of_eq heq).trans
      ((le_smallMax X b p κn σ (Finset.mem_product.mpr ⟨Finset.mem_univ i, hij⟩) ω).trans
        (le_max_left _ _)))
  have hdD : ∀ q : CubePair m, q.side₁ = σ → q.side₂ = σ → 0 ≤ q.dist → ∀ i : Fin 4,
      ∀ (ij : (Fin m → ℤ) × (Fin m → ℤ)), ij ∈ box m L ×ˢ box m L →
      ∀ u ∈ q.first, ∀ v ∈ q.second,
      pairSup (X.slabTime b q.slab ω) q.first q.second = smallFamily X b p κn σ (i, ij) ω →
      |X.slabTime b q.slab ω u v - dist u v| ≤ max (smallMax X b p κn σ L ω) 0 := by
    intro q hq1 hq2 hq0 i ij hij u hu v hv heq
    obtain ⟨c, hc⟩ := pairBound_slabTime X hb q (hq1 ▸ H.hσ.le) (hq2 ▸ H.hσ.le) hq0 ω
    refine (le_pairSup hc hu hv).trans ((le_of_eq heq).trans
      ((le_smallMax X b p κn σ (Finset.mem_product.mpr ⟨Finset.mem_univ i, hij⟩) ω).trans
        (le_max_left _ _)))
  exact {
    hσm := Slab.measurable_density p.slab b (Profiles.measurable_ρ_apply X ω)
    hσB := hσB
    hρσ := fun x => by
      unfold Slab.density
      split_ifs
      · exact hb ω x
      · exact le_rfl
    hopt := fun u hu v hv =>
      exists_isOneOptimal_restricted hσB (convex_slab_set p.slab) (hIS hu) (hI'S hv)
    hgood := hgood_of_le ha (Localization.le_slabDensity X hb (fun ω x => (hab ω x).1) p.slab ω)
      (fun u hu v hv => slabTime_le_mul_dist X hb p.slab ω hu hv) H.h1 H.h2 hgood
    hnear := fun u hu x _ hx hxt => by
      obtain ⟨i, j, hi, hj, hu', hx'⟩ := near_mem H.hσ H.h1 H.hLu H.hLx hu hx hxt
      set q := nearPair p κn σ (nearCenter p κn) i j with hq
      have hthin := slabTime_le_thin X hb p.slab q.slab (t₀ := 0)
        (fun z => by rw [hq, slabCoord_nearPair, sub_zero]) le_rfl
        (by change 0 + κn ≤ p.dist; linarith [H.hκ, H.hκ0])
        (hfaces_near p _ i j H.hκ1) ω
        (Profiles.cubePair_first_subset_set q H.hκ0.le hu')
        (Profiles.cubePair_second_subset_set q H.hκ0.le hx')
      have h1 := abs_le.mp (hdD q rfl rfl H.hκ0.le 1 (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
        u hu' x hx' (by simp [smallFamily, q]))
      have h0 := abs_le.mp (hdT q rfl rfl 0 (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
        u hu' x hx' (by simp [smallFamily, q]))
      change X.slabTime b p.slab ω u x - dist u x ≤ _ ∧ _
      exact ⟨by linarith [h1.2], by linarith [h0.1]⟩
    hfar := fun y _ hy hyt v hv => by
      obtain ⟨i, j, hi, hj, hy', hv'⟩ := far_mem H.hσ H.h2 H.hLv H.hLx hy hyt hv
      set q := farPair p κn σ (farCenter p κn) i j with hq
      have hthin := slabTime_le_thin X hb p.slab q.slab (t₀ := p.dist - κn)
        (fun z => by rw [hq, slabCoord_farPair]) (by linarith [H.hκ, H.hκ0])
        (by change p.dist - κn + κn ≤ p.dist; linarith)
        (hfaces_far p _ i j H.hκ1) ω
        (Profiles.cubePair_first_subset_set q H.hκ0.le hy')
        (Profiles.cubePair_second_subset_set q H.hκ0.le hv')
      have h1 := abs_le.mp (hdD q rfl rfl H.hκ0.le 3 (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
        y hy' v hv' (by simp [smallFamily, q]))
      have h0 := abs_le.mp (hdT q rfl rfl 2 (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
        y hy' v hv' (by simp [smallFamily, q]))
      change X.slabTime b p.slab ω y v - dist y v ≤ _ ∧ _
      exact ⟨by linarith [h1.2], by linarith [h0.1]⟩ }

end IsotropicVariance.Paper.Proofs.Modulus
