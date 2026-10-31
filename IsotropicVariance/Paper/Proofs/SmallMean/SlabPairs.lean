/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.SmallMean

/-!
# Equation `eq:slab` for the pairs of cubes of Lemma `lem:smallmean`

The second paragraph of the proof of Lemma `lem:smallmean` uses equation
`eq:slab` for the pairs of cubes `I_{i−1}(j)`, `I_i(k)` with `(sQ_s)^{1/2}|k − j| ≤ s/2`. The
statement `SlabStatement` is in the `O_1` form, over the pairs `IsSlabPair`.

* `isSlabPair_gridCube`: two points of such cubes are a pair of equation `eq:slab`, with `z` the
  corner of the first cube.
* `sub_le_iSup_slabPair`: the supremum of equation `eq:slab` dominates each of its terms.
* `isOs_two_sqrt`: `Y ≤ O_1(θ²)` gives `Y^{1/2} ≤ O_2(θ)`, the form of the moment bound of one pair
  (`lintegral_fluct_pow_le_of_pair`).
* `slabSupSqrt`: that square root for the pair of cubes; its bounds are `isOs_slabSupSqrt` and
  `slabTime_sub_passTime_le_slabSupSqrt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.SmallMean

open Infra.Slab

variable {m : ℕ}

/-- `Y ≤ O_1(θ²)` gives `Y^{1/2} ≤ O_2(θ)`. -/
theorem isOs_two_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ} {θ : ℝ}
    (h : Cited.IsOs P 1 (θ ^ 2) Y) : Cited.IsOs P 2 θ fun ω => Real.sqrt (Y ω) := by
  refine ⟨Real.continuous_sqrt.measurable.comp_aemeasurable h.1, le_of_eq_of_le
    (lintegral_congr fun ω => ?_) h.2⟩
  have hsq : Real.sqrt (Y ω) ^ 2 = max (Y ω) 0 := by
    rcases le_total 0 (Y ω) with hY | hY
    · rw [Real.sq_sqrt hY, max_eq_left hY]
    · rw [Real.sqrt_eq_zero_of_nonpos hY, max_eq_right hY]
      norm_num
  rw [max_eq_left (Real.sqrt_nonneg _), Real.rpow_two, Real.rpow_one, div_pow, hsq]

/-- Two points of the cubes `I_{i−1}(j)`, `I_i(k)` with `W(|k − j| + √(d−1)) ≤ s` are a pair of
equation `eq:slab` for the slab `i`, with `z` the corner of the first cube. -/
theorem isSlabPair_gridCube {s W : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W) (hWm : W * Real.sqrt m ≤ s)
    {i : ℕ} {j k : Fin m → ℤ} (hjk : W * (zNorm (k - j) + Real.sqrt m) ≤ s) {u v : Pt m}
    (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k) :
    Contracts.IsSlabPair (chainSlab s 0 i) (meshPt s W i j 0) u v := by
  refine ⟨Or.inl ⟨gridCube_subset_face₀ s W i j hu, gridCube_subset_face₁ s W i k hv⟩, ?_, ?_⟩
  · rw [chainSlab_width]
    obtain ⟨hlon, htr⟩ := hu
    have hlon' : Pt.lon (u - meshPt s W i j 0) = 0 := by
      simp only [sub_zero] at hlon
      simp [meshPt, hlon]
    have htr' : ∀ l, |Pt.tr (u - meshPt s W i j 0) l| ≤ W := by
      intro l
      obtain ⟨h₁, h₂⟩ := htr l
      simp only [sub_zero] at h₁ h₂
      have e : Pt.tr (u - meshPt s W i j 0) l = Pt.tr u l - W * (j l : ℝ) := by
        simp [meshPt]
      rw [e, abs_le]
      constructor <;> linarith only [h₁, h₂, hW, mul_add W (j l : ℝ) 1, mul_one W]
    have hn := Profiles.norm_sq_eq_lon_tr (u - meshPt s W i j 0)
    rw [hlon'] at hn
    have heq : ‖u - meshPt s W i j 0‖ = ‖Pt.tr (u - meshPt s W i j 0)‖ :=
      (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by rw [hn]; ring)
    rw [heq]
    exact (Profiles.norm_le_of_abs_le hW htr').trans ((mul_comm _ _).trans_le hWm)
  · rw [chainSlab_width, ← dist_eq_norm, dist_comm]
    have h2 : (2 : ℝ) ≤ Real.sqrt 5 := Real.le_sqrt_of_sq_le (by norm_num)
    exact (dist_gridCube_le hs hW hu hv hjk).trans (mul_le_mul_of_nonneg_right h2 hs)

/-- The supremum of equation `eq:slab` dominates each of its terms: `T_P − T ≤ b|y − x|` bounds
the family. -/
theorem sub_le_iSup_slabPair (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {sl : Slab m}
    (hw : 0 ≤ sl.width) (z : Pt m) (ω : X.Ω) {x y : Pt m} (hxy : Contracts.IsSlabPair sl z x y) :
    X.slabTime b sl ω x y - X.passTime ω x y ≤
      ⨆ p : {p : Pt m × Pt m // Contracts.IsSlabPair sl z p.1 p.2},
        (X.slabTime b sl ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2) := by
  have hb0 : 0 ≤ b := upperBound_nonneg X hb ω
  have hface₀ : sl.face₀ ⊆ sl.set := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨hu.ge, by rw [mem_ofPred_eq.mp hu]; exact hw⟩, rfl⟩
  have hface₁ : sl.face₁ ⊆ sl.set := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨by rw [mem_ofPred_eq.mp hu]; exact hw, hu.le⟩, rfl⟩
  have hbdd : BddAbove (range fun p : {p : Pt m × Pt m // Contracts.IsSlabPair sl z p.1 p.2} =>
      X.slabTime b sl ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2) := by
    refine ⟨b * (Real.sqrt 5 * sl.width), ?_⟩
    rintro _ ⟨⟨⟨x', y'⟩, hf, -, hd⟩, rfl⟩
    have hmem : x' ∈ sl.set ∧ y' ∈ sl.set := by
      rcases hf with hf | hf
      · exact ⟨hface₀ hf.1, hface₁ hf.2⟩
      · exact ⟨hface₁ hf.1, hface₀ hf.2⟩
    have h₁ := slabTime_le_mul_dist X hb sl ω hmem.1 hmem.2
    have h₂ := Profiles.passTime_nonneg (X := X) ω x' y'
    have h₃ : b * dist x' y' ≤ b * (Real.sqrt 5 * sl.width) := by
      refine mul_le_mul_of_nonneg_left ?_ hb0
      rw [dist_comm, dist_eq_norm]
      exact hd
    exact (sub_le_self _ h₂).trans (h₁.trans h₃)
  exact le_ciSup hbdd (⟨(x, y), hxy⟩ : {p : Pt m × Pt m // Contracts.IsSlabPair sl z p.1 p.2})

/-- The square root of the supremum of equation `eq:slab` for the slab `i` and the corner of the
cube `I_{i−1}(j)`. -/
noncomputable def slabSupSqrt (X : Setting.{u} m) (b s W : ℝ) (i : ℕ) (j : Fin m → ℤ) (ω : X.Ω) :
    ℝ :=
  Real.sqrt (⨆ p : {p : Pt m × Pt m //
      Contracts.IsSlabPair (chainSlab s 0 i) (meshPt s W i j 0) p.1 p.2},
    (X.slabTime b (chainSlab s 0 i) ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2))

theorem slabSupSqrt_nonneg (X : Setting.{u} m) (b s W : ℝ) (i : ℕ) (j : Fin m → ℤ) (ω : X.Ω) :
    0 ≤ slabSupSqrt X b s W i j ω :=
  Real.sqrt_nonneg _

/-- `T_P − T ≤ O_1(θ²)` over the pairs of equation `eq:slab` is the `O_2(θ)` bound of
`slabSupSqrt`. -/
theorem isOs_slabSupSqrt (X : Setting.{u} m) (b s W : ℝ) (i : ℕ) (j : Fin m → ℤ) {θ : ℝ}
    (h : Cited.IsOs X.P 1 (θ ^ 2) (fun ω =>
      ⨆ p : {p : Pt m × Pt m //
          Contracts.IsSlabPair (chainSlab s 0 i) (meshPt s W i j 0) p.1 p.2},
        (X.slabTime b (chainSlab s 0 i) ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2))) :
    Cited.IsOs X.P 2 θ (slabSupSqrt X b s W i j) :=
  isOs_two_sqrt h

/-- The bounds of `T_P − T` at the points of a pair of cubes with `W|k − j| ≤ s/2`, for the
comparison of the second moments. -/
theorem slabTime_sub_passTime_le_slabSupSqrt (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b)
    {s W : ℝ} (hs : 0 < s) (hW : 0 ≤ W) (hWs : W * (1 + Real.sqrt m) ≤ s / 4)
    (hlow : ∀ (i : ℕ) (j : Fin m → ℤ) (ω : X.Ω) (x y : Pt m),
      Contracts.IsSlabPair (chainSlab s 0 i) (meshPt s W i j 0) x y →
        0 ≤ X.slabTime b (chainSlab s 0 i) ω x y - X.passTime ω x y)
    (i : ℕ) (j k : Fin m → ℤ) (hjk : W * zNorm (k - j) ≤ s / 2) :
    ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 (i + 1) k, ∀ ω,
      0 ≤ X.slabTime b (chainSlab s 0 i) ω u v - X.passTime ω u v ∧
        X.slabTime b (chainSlab s 0 i) ω u v - X.passTime ω u v ≤
          1 * slabSupSqrt X b s W i j ω ^ 2 := by
  intro u hu v hv ω
  have h₁ : W * Real.sqrt m ≤ s := by linarith only [hWs, hW, hs, mul_add W 1 (Real.sqrt m)]
  have h₂ : W * (zNorm (k - j) + Real.sqrt m) ≤ s := by
    linarith only [hWs, hjk, hW, hs, mul_add W 1 (Real.sqrt m),
      mul_add W (zNorm (k - j)) (Real.sqrt m)]
  have hp := isSlabPair_gridCube hs.le hW h₁ h₂ hu hv
  refine ⟨hlow i j ω u v hp, ?_⟩
  have hw : 0 ≤ (chainSlab (m := m) s 0 i).width := by
    rw [chainSlab_width]
    exact hs.le
  have hsup := sub_le_iSup_slabPair X hb hw (meshPt s W i j 0) ω hp
  have hY0 : 0 ≤ ⨆ p : {p : Pt m × Pt m //
      Contracts.IsSlabPair (chainSlab s 0 i) (meshPt s W i j 0) p.1 p.2},
      (X.slabTime b (chainSlab s 0 i) ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2) :=
    Real.iSup_nonneg fun p => hlow i j ω _ _ p.2
  rw [one_mul, slabSupSqrt, Real.sq_sqrt hY0]
  exact hsup

end IsotropicVariance.Paper.Proofs.SmallMean
