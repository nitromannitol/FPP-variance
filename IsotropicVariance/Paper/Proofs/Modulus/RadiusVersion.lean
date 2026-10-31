/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.RadiusPointwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import IsotropicVariance.Paper.Proofs.Gain.Tube
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# Independent versions of the radii `R_i(j, k)`

In the proof of Lemma `lem:blocks`, "`R_i(j, k)` is determined by the noise in the `i`th slab, so
the arrays `R_i²` are independent over `i`." The radius is a supremum over 1-optimal curves,
measurable only for the completed probability, so we take versions:

* the extended density of a slab factors through `Φ : Ω → (ℕ → Bool)`, measurable for the
  information of the slab (`Infra.Slab.exists_factor_of_measurable_prod`);
* on the standard Borel space `ℕ → Bool`, under the law of `Φ`, the supremum over 1-optimal
  curves for the factored slab density is almost everywhere measurable
  (`Localization.aemeasurable_iSup_oneOptimal`); a measurable modification composed with `Φ` is a
  version measurable for the information of the slab (`exists_measurable_maxDeviation_factor`);
* the slabs of the chain have disjoint interiors and null boundaries, so the versions are
  independent (`exists_radius_versions`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Metric

namespace IsotropicVariance.Paper.Proofs.Modulus

open Contracts Infra.Slab

variable {m : ℕ}

/-- The slab density of the extended slab density is the slab density, on the slab. -/
lemma density_extDensity_of_mem (sl : Slab m) (b : ℝ) (σ : Pt m → ℝ) {y : Pt m}
    (hy : y ∈ sl.set) : sl.density b (extDensity sl b σ) y = sl.density b σ y := by
  unfold Slab.density
  split_ifs with h1
  · rfl
  · rw [extDensity_of_mem sl b σ hy]
    simp [Slab.density, h1]

/-- **A version of the deviation of the 1-optimal curves of a slab, determined by the noise in
the slab.** Given a factorization `extDensity sl b (X.ρ ω) y = h (Φ ω, y)`, there is a measurable
nonnegative `g` on `ℕ → Bool` with `g (Φ ω) = maxDeviation …` almost surely. -/
theorem exists_measurable_maxDeviation_factor (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) {Φ : X.Ω → ℕ → Bool} (hΦ : Measurable Φ) {h : (ℕ → Bool) × Pt m → ℝ}
    (hh : Measurable h) (hfac : ∀ ω y, extDensity sl b (X.ρ ω) y = h (Φ ω, y))
    {I I' : Set (Pt m)} (hI : IsCompact I) (hI' : IsCompact I') (p q : Pt m) :
    ∃ g : (ℕ → Bool) → ℝ, Measurable g ∧ (∀ θ, 0 ≤ g θ) ∧
      ∀ᵐ ω ∂X.P, g (Φ ω) = maxDeviation (sl.density b (X.ρ ω)) sl.set I I' p q := by
  obtain ⟨a, b', ha, hab⟩ := X.bounds
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure X.P
  have hab' : a ≤ b := (hab ω₀ 0).1.trans (hb ω₀ 0)
  have hb0 : 0 ≤ b := ha.le.trans hab'
  -- the clamped factored density and its slab density, on parameters
  let τ : (ℕ → Bool) → Pt m → ℝ := fun θ y => max a (min (h (θ, y)) b)
  have hτm : Measurable (Function.uncurry τ) := by
    change Measurable fun q : (ℕ → Bool) × Pt m => max a (min (h q) b)
    exact measurable_const.max (hh.min measurable_const)
  have hτb : ∀ θ y, τ θ y ≤ b := fun θ y => max_le hab' (min_le_right _ _)
  let σ : (ℕ → Bool) → Pt m → ℝ := fun θ => sl.density b (τ θ)
  have hσm : Measurable (Function.uncurry σ) := by
    change Measurable fun q : (ℕ → Bool) × Pt m =>
      if infDist q.2 sl.faces ≤ 1 then b else τ q.1 q.2
    exact Measurable.ite (measurableSet_le ((continuous_infDist_pt _).measurable.comp
      measurable_snd) measurable_const) measurable_const hτm
  have hσa : ∀ θ y, a ≤ σ θ y := by
    intro θ y
    change a ≤ sl.density b (τ θ) y
    unfold Slab.density
    split_ifs
    · exact hab'
    · exact le_max_left _ _
  have hσb : ∀ θ y, σ θ y ≤ b := fun θ y => (Slab.density_le sl b (hτb θ) y).trans (max_le
    le_rfl le_rfl)
  -- a jointly measurable version of the restricted passage times on parameters
  set μ := X.P.map Φ
  have hρm : Measurable fun q : (ℕ → Bool) × Pt m =>
      ENNReal.ofReal (extDensity sl b (τ q.1) q.2) :=
    (measurable_extDensity_uncurry sl b hτm).ennreal_ofReal
  obtain ⟨T, hTm, -, hTae⟩ := Infra.Measurability.exists_jointlyMeasurable_passageTime_version μ
    hρm (b := b.toNNReal) fun θ y => ENNReal.ofReal_le_ofReal (extDensity_le sl (hτb θ) y)
  have hDae : ∀ᵐ θ ∂μ, ∀ u ∈ sl.set, ∀ v ∈ sl.set,
      T θ (u, v) = restrictedPassageTime (σ θ) sl.set u v := by
    filter_upwards [hTae] with θ hθ u hu v hv
    rw [hθ (u, v)]
    exact ((passTime_eq_passageTime_extDensity sl b (τ θ) hu hv).trans
      (passageTime_eq_infra _ u v)).symm
  -- a deterministic bound of the distances
  have hT : ∀ θ, ∀ u ∈ sl.set, ∀ v ∈ sl.set,
      restrictedPassageTime (σ θ) sl.set u v ≤ b * dist u v := by
    intro θ u hu v hv
    have h1 := restrictedInf_le (hσb θ) (convex_slab_set sl) hu hv
    have hne : ENNReal.ofReal b * edist u v ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top u v)
    rw [restrictedPassageTime_eq_toReal]
    refine (ENNReal.toReal_mono hne h1).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb0, edist_dist,
      ENNReal.toReal_ofReal dist_nonneg]
  obtain ⟨R, hR⟩ := Localization.exists_dist_le_of_isOneOptimal (σ := σ) (S := sl.set) hI.isBounded
    hI'.isBounded ha hσa (B := b) hT
  obtain ⟨r₀, hr₀⟩ := hI.isBounded.subset_closedBall p
  have hae : AEMeasurable (fun θ => maxDeviation (σ θ) sl.set I I' p q) μ :=
    Localization.aemeasurable_iSup_oneOptimal μ hσm (isClosed_slab_set sl) hI.measurableSet
      hI'.measurableSet hTm hDae (V := fun x => infDist x.2.2 (segment ℝ p q)) (R := R + r₀)
      ((continuous_infDist_pt _).comp (continuous_snd.comp continuous_snd))
      (fun _ => infDist_nonneg)
      (fun θ u hu v hv γ hγ t ht => (infDist_le_dist_of_mem (left_mem_segment ℝ p q)).trans <|
        (dist_triangle _ u p).trans (add_le_add (hR θ u hu v hv γ hγ t ht)
          (mem_closedBall.1 (hr₀ hu))))
  refine ⟨fun θ => max (hae.mk _ θ) 0, hae.measurable_mk.max measurable_const,
    fun θ => le_max_right _ _, ?_⟩
  have h1 : ∀ᵐ θ ∂μ, max (hae.mk _ θ) 0 = maxDeviation (σ θ) sl.set I I' p q := by
    filter_upwards [hae.ae_eq_mk] with θ hθ
    rw [← hθ, max_eq_left (Gain.maxDeviation_nonneg _ _ _ _ _ _)]
  filter_upwards [ae_of_ae_map hΦ.aemeasurable h1] with ω hω
  rw [hω]
  refine maxDeviation_congr (fun y hy => ?_) I I' p q
  -- on the slab, the factored slab density is the slab density of the outcome
  have hτω : τ (Φ ω) = extDensity sl b (X.ρ ω) := by
    funext z
    change max a (min (h (Φ ω, z)) b) = _
    rw [← hfac ω z, min_eq_left (extDensity_le sl (hb ω) z)]
    refine max_eq_right ?_
    unfold extDensity
    split_ifs
    · exact Localization.le_slabDensity X hb (fun ω x => (hab ω x).1) sl ω z
    · exact hab'
  change sl.density b (τ (Φ ω)) y = _
  rw [hτω]
  exact density_extDensity_of_mem sl b _ hy

/-- **Independent versions of the radii** (the proof of Lemma `lem:blocks`): for `n > 0`, `W > 0`,
there are arrays `R̂_i(j, k)`, measurable in the outcome, nonnegative, independent over the slabs
`i`, with `R̂_i(j, k) = R_i(j, k)` for all `i, j, k` almost surely. -/
theorem exists_radius_versions (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {n W : ℝ}
    (hn : 0 < n) (hW : 0 < W) (K : ℕ) :
    ∃ Rv : Fin K → X.Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ,
      (∀ i j k, Measurable fun ω => Rv i ω j k) ∧ (∀ i ω j k, 0 ≤ Rv i ω j k) ∧
      iIndepFun Rv X.P ∧ ∀ᵐ ω ∂X.P, ∀ i j k, Rv i ω j k = X.R b n W ω i j k := by
  classical
  have hfac : ∀ i : Fin K, ∃ Φ : X.Ω → ℕ → Bool, Measurable[X.info (chainSlab n 0 i).set] Φ ∧
      ∃ h : (ℕ → Bool) × Pt m → ℝ, Measurable h ∧
        ∀ ω y, extDensity (chainSlab n 0 i) b (X.ρ ω) y = h (Φ ω, y) :=
    fun i => exists_factor_of_measurable_prod (measurable_extDensity_info X b (chainSlab n 0 i))
  choose Φ hΦ h hh hfh using hfac
  have hΦm : ∀ i, Measurable (Φ i) := fun i => (hΦ i).mono (X.info_le _) le_rfl
  have hg : ∀ (i : Fin K) (j k : Fin m → ℤ), ∃ g : (ℕ → Bool) → ℝ, Measurable g ∧
      (∀ θ, 0 ≤ g θ) ∧ ∀ᵐ ω ∂X.P, g (Φ i ω) =
        maxDeviation ((chainSlab n 0 i).density b (X.ρ ω)) (chainSlab n 0 i).set
          (gridCube n W 0 i j) (gridCube n W 0 (i + 1) k) (gridCubeCenter n W 0 i j)
          (gridCubeCenter n W 0 (i + 1) k) :=
    fun i j k => exists_measurable_maxDeviation_factor X hb _ (hΦm i) (hh i) (hfh i)
      (SmallMean.isCompact_gridCube _ _ _ _) (SmallMean.isCompact_gridCube _ _ _ _) _ _
  choose g hgm hg0 hgae using hg
  -- the arrays on parameters
  let F : Fin K → (ℕ → Bool) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ := fun i θ j k =>
    if W * zNorm (k - j) ≤ n / 2 then radiusConst m + W⁻¹ * g i j k θ else 0
  have hF : ∀ i, Measurable (F i) := by
    intro i
    refine Measurable.of_eval fun j => Measurable.of_eval fun k => ?_
    change Measurable fun θ =>
      if W * zNorm (k - j) ≤ n / 2 then radiusConst m + W⁻¹ * g i j k θ else 0
    split_ifs
    · exact measurable_const.add (measurable_const.mul (hgm i j k))
    · exact measurable_const
  have hRc : 0 ≤ radiusConst m := by unfold radiusConst; positivity
  refine ⟨fun i ω => F i (Φ i ω), fun i j k => ?_, fun i ω j k => ?_, ?_, ?_⟩
  · exact (((hF i).comp (hΦm i)).eval (a := j)).eval (a := k)
  · change 0 ≤ (if W * zNorm (k - j) ≤ n / 2 then radiusConst m + W⁻¹ * g i j k (Φ i ω)
      else 0)
    split_ifs
    · have := hg0 i j k (Φ i ω)
      have hWi : 0 ≤ W⁻¹ := inv_nonneg.mpr hW.le
      positivity
    · exact le_rfl
  · rw [iIndepFun_iff_iIndep]
    refine iIndep_of_iIndep_of_le (X.iIndep_info (Fin K) (fun i => (chainSlab n 0 i).set)
      (fun i => measurableSet_slab_set _) (fun i => volume_frontier_slab_set _)
      (pairwise_disjoint_interior_chainSlab hn 0 K)) fun i => ?_
    exact ((hF i).comp (hΦ i)).comap_le
  · have hall : ∀ᵐ ω ∂X.P, ∀ i j k, g i j k (Φ i ω) =
        maxDeviation ((chainSlab n 0 i).density b (X.ρ ω)) (chainSlab n 0 i).set
          (gridCube n W 0 i j) (gridCube n W 0 (i + 1) k) (gridCubeCenter n W 0 i j)
          (gridCubeCenter n W 0 (i + 1) k) :=
      ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hgae i j k
    filter_upwards [hall] with ω hω i j k
    change (if W * zNorm (k - j) ≤ n / 2 then radiusConst m + W⁻¹ * g i j k (Φ i ω)
      else 0) = X.R b n W ω i j k
    unfold Setting.R
    rw [hω i j k]

end IsotropicVariance.Paper.Proofs.Modulus
