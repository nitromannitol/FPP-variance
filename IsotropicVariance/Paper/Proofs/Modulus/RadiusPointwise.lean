/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
public import IsotropicVariance.Paper.Proofs.Profiles.RowEnergySetup
public import IsotropicVariance.Paper.Proofs.Localization.Measurable
public import IsotropicVariance.Paper.Proofs.Localization.Frame
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Gain.Locality
import IsotropicVariance.Paper.Proofs.Gain.Tube
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# The radii `R_i(j, k)` of Lemma `lem:blocks`: a pointwise bound

For `W|k − j| ≤ n/2`, the radius `R_i(j, k)` of Section `sec:gain` is at most a constant
plus the quantity `1 + W⁻¹ sup dist(x, [u, v])` of Lemma `lem:localization` for the pair of
transverse cubes `gridPair n W i j k` containing `I_i(j)` and `I_{i+1}(k)` (`radius_le`): the
slab of the pair is the chain slab (same set and faces), the cubes lie in the faces of the pair,
and moving the endpoints of the segment from the centers of the cubes to `u, v` costs at most
`√m W` (`Localization.infDist_segment_le`).

The suprema over 1-optimal curves depend on the density only on the set (`maxDeviation_congr`).
-/

@[expose] public section

open MeasureTheory Set Metric

namespace IsotropicVariance.Paper.Proofs.Modulus

open Contracts Infra.Slab

variable {m : ℕ}

/-! ## Suprema over 1-optimal curves -/

/-- 1-optimality only sees the density on the set. -/
lemma isOneOptimal_congr {σ₁ σ₂ : Pt m → ℝ} {S : Set (Pt m)} (h : ∀ y ∈ S, σ₁ y = σ₂ y) :
    IsOneOptimal σ₁ S = IsOneOptimal σ₂ S := by
  funext u v γ
  apply propext
  unfold IsOneOptimal
  rw [Gain.restrictedPassageTime_congr h]
  have hc (hS : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S) :
      γ.cost (fun x => ENNReal.ofReal (σ₁ x)) = γ.cost (fun x => ENNReal.ofReal (σ₂ x)) :=
    γ.cost_congr fun t ht => by rw [h _ (hS t ht)]
  constructor
  · rintro ⟨h0, h1, hS, hcost⟩
    exact ⟨h0, h1, hS, (hc hS).symm.trans_le hcost⟩
  · rintro ⟨h0, h1, hS, hcost⟩
    exact ⟨h0, h1, hS, (hc hS).trans_le hcost⟩

lemma maxDeviation_congr {σ₁ σ₂ : Pt m → ℝ} {S : Set (Pt m)} (h : ∀ y ∈ S, σ₁ y = σ₂ y)
    (I I' : Set (Pt m)) (p q : Pt m) :
    maxDeviation σ₁ S I I' p q = maxDeviation σ₂ S I I' p q := by
  unfold maxDeviation
  rw [isOneOptimal_congr h]

lemma maxSegmentDeviation_nonneg (σ : Pt m → ℝ) (S I I' : Set (Pt m)) :
    0 ≤ maxSegmentDeviation σ S I I' :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => infDist_nonneg

/-- A distance to `[u, v]` from a point of a 1-optimal curve is at most the supremum, when the
distances are bounded. -/
lemma infDist_le_maxSegmentDeviation {σ : Pt m → ℝ} {S J J' : Set (Pt m)} {B : ℝ}
    (hB : ∀ u ∈ J, ∀ v ∈ J', ∀ γ : RectifiableCurve (Pt m), IsOneOptimal σ S u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ u v) ≤ B)
    {u v : Pt m} (hu : u ∈ J) (hv : v ∈ J') {γ : RectifiableCurve (Pt m)}
    (hγ : IsOneOptimal σ S u v γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    infDist (γ.toFun t) (segment ℝ u v) ≤ maxSegmentDeviation σ S J J' := by
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have h4 : ∀ (u : J) (v : J') (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ})
      (t : Icc (0 : ℝ) 1), infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m)) ≤ max B 0 :=
    fun u v γ t => (hB u u.2 v v.2 γ.1 γ.2 t t.2).trans (le_max_left _ _)
  have h3 : ∀ (u : J) (v : J') (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ}),
      ⨆ t : Icc (0 : ℝ) 1, infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m)) ≤ max B 0 :=
    fun u v γ => Real.iSup_le (h4 u v γ) hB0
  have h2 : ∀ (u : J) (v : J'),
      ⨆ (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ}) (t : Icc (0 : ℝ) 1),
        infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m)) ≤ max B 0 :=
    fun u v => Real.iSup_le (h3 u v) hB0
  have hb1 : BddAbove (range fun u : J => ⨆ (v : J')
      (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ}) (t : Icc (0 : ℝ) 1),
        infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m))) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨u', rfl⟩
    exact Real.iSup_le (h2 u') hB0
  have hb2 (u : J) : BddAbove (range fun v : J' =>
      ⨆ (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ}) (t : Icc (0 : ℝ) 1),
        infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m))) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨v', rfl⟩
    exact h2 u v'
  have hb3 (u : J) (v : J') : BddAbove (range fun γ : {γ : RectifiableCurve (Pt m) //
      IsOneOptimal σ S u v γ} => ⨆ t : Icc (0 : ℝ) 1,
        infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m))) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨γ', rfl⟩
    exact h3 u v γ'
  have hb4 (u : J) (v : J') (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ}) :
      BddAbove (range fun t : Icc (0 : ℝ) 1 =>
        infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m))) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨t', rfl⟩
    exact h4 u v γ t'
  have s4 := le_ciSup (hb4 ⟨u, hu⟩ ⟨v, hv⟩ ⟨γ, hγ⟩) ⟨t, ht⟩
  have s3 := le_ciSup (hb3 ⟨u, hu⟩ ⟨v, hv⟩) ⟨γ, hγ⟩
  have s2 := le_ciSup (hb2 ⟨u, hu⟩) ⟨v, hv⟩
  have s1 := le_ciSup hb1 ⟨u, hu⟩
  exact s4.trans (s3.trans (s2.trans s1))

/-- Moving the segment from `[p, q]` to the endpoints: the deviation from `[p, q]` is at most the
deviation from the segments `[u, v]` plus twice the distance of the endpoints to `p`, `q`. -/
lemma maxDeviation_le_maxSegmentDeviation_add {σ : Pt m → ℝ} {S I I' J J' : Set (Pt m)}
    {p q : Pt m} {r B : ℝ} (hr : 0 ≤ r) (hIJ : I ⊆ J) (hIJ' : I' ⊆ J')
    (hp : ∀ u ∈ I, dist p u ≤ r) (hq : ∀ v ∈ I', dist q v ≤ r)
    (hB : ∀ u ∈ J, ∀ v ∈ J', ∀ γ : RectifiableCurve (Pt m), IsOneOptimal σ S u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ u v) ≤ B) :
    maxDeviation σ S I I' p q ≤ maxSegmentDeviation σ S J J' + 2 * r := by
  have h0 := maxSegmentDeviation_nonneg σ S J J'
  have hM : 0 ≤ maxSegmentDeviation σ S J J' + 2 * r := by linarith
  unfold maxDeviation
  refine Real.iSup_le (fun u => Real.iSup_le (fun v => Real.iSup_le (fun γ =>
    Real.iSup_le (fun t => ?_) hM) hM) hM) hM
  have h1 := Localization.infDist_segment_le (γ.1.toFun t) p q u v
  have h2 := infDist_le_maxSegmentDeviation hB (hIJ u.2) (hIJ' v.2) γ.2 t.2
  linarith [hp u u.2, hq v v.2]

/-! ## The cubes of equation `eq:cubes` -/

/-- The points of a cube are within `√m W/2` of its center. -/
lemma dist_gridCubeCenter_le {s W : ℝ} (hW : 0 ≤ W) {i : ℕ} {j : Fin m → ℤ} {u : Pt m}
    (hu : u ∈ gridCube s W 0 i j) : dist (gridCubeCenter s W 0 i j) u ≤ Real.sqrt m * (W / 2) := by
  rw [dist_comm, dist_eq_norm]
  have h1 := hu.1
  simp only [sub_zero] at h1
  refine Profiles.norm_le_of_lon_zero (by positivity) ?_ fun l => ?_
  · simp [gridCubeCenter, h1]
  · have h := hu.2 l
    simp only [sub_zero] at h
    have e : Pt.tr (u - gridCubeCenter s W 0 i j) l = Pt.tr u l - W * ((j l : ℝ) + 1 / 2) := by
      simp [gridCubeCenter]
    rw [e, abs_le]
    constructor <;> linarith [h.1, h.2]

/-! ## The pointwise bound -/

/-- **The pointwise bound on the radii**: for `W|k − j| ≤ n/2`, `R_i(j, k)` is at most
`radiusConst m + √m − 1` plus the quantity of Lemma `lem:localization` for the slab passage time
of the pair of cubes `gridPair n W i j k`. -/
theorem radius_le (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {n W : ℝ} (hW : 0 < W) (ω : X.Ω) (i : ℕ) {j k : Fin m → ℤ} (hjk : W * zNorm (k - j) ≤ n / 2) :
    X.R b n W ω i j k ≤ (radiusConst m + Real.sqrt m - 1) +
      (1 + W⁻¹ * maxSegmentDeviation ((Profiles.gridPair n W i j k).slab.density b (X.ρ ω))
        (Profiles.gridPair n W i j k).slab.set (Profiles.gridPair n W i j k).first
        (Profiles.gridPair n W i j k).second) := by
  set p := Profiles.gridPair n W i j k
  set sl := chainSlab n 0 i
  rw [Profiles.gridPair_slab_density, Profiles.gridPair_slab_set]
  unfold Setting.R
  simp only [hjk, ↓reduceIte]
  -- a deterministic bound of the distances to the segments
  obtain ⟨a, b', ha, hab⟩ := X.bounds
  have hfirst : IsCompact p.first :=
    Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_first p hW.le)
  have hsecond : IsCompact p.second :=
    Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_second p hW.le)
  obtain ⟨R₀, hR₀⟩ := Localization.exists_dist_le_of_isOneOptimal (σ := fun ω => sl.density b (X.ρ ω))
    (S := sl.set) hfirst.isBounded hsecond.isBounded ha
    (Localization.le_slabDensity X hb (fun ω x => (hab ω x).1) sl) (B := b)
    (fun ω u hu v hv => slabTime_le_mul_dist X hb sl ω hu hv)
  have hB : ∀ u ∈ p.first, ∀ v ∈ p.second, ∀ γ : RectifiableCurve (Pt m),
      IsOneOptimal (sl.density b (X.ρ ω)) sl.set u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ u v) ≤ R₀ :=
    fun u hu v hv γ hγ t ht => (infDist_le_dist_of_mem (left_mem_segment ℝ u v)).trans
      (hR₀ ω u hu v hv γ hγ t ht)
  have hdev := maxDeviation_le_maxSegmentDeviation_add (r := Real.sqrt m * (W / 2))
    (by positivity) (Profiles.gridCube_subset_first n W hW.le i j k)
    (Profiles.gridCube_subset_second n W hW.le i j k) (fun u hu => dist_gridCubeCenter_le hW.le hu)
    (fun v hv => dist_gridCubeCenter_le hW.le hv) hB
  have hWinv : 0 ≤ W⁻¹ := inv_nonneg.mpr hW.le
  have h := mul_le_mul_of_nonneg_left hdev hWinv
  have e : W⁻¹ * (2 * (Real.sqrt m * (W / 2))) = Real.sqrt m := by
    field_simp
  rw [mul_add, e] at h
  linarith

end IsotropicVariance.Paper.Proofs.Modulus
