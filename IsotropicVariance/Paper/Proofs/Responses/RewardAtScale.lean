/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Responses.TubeLocality
public import IsotropicVariance.Paper.Proofs.Responses.Deviation
public import IsotropicVariance.Paper.Proofs.Responses.ProfileMoments
public import IsotropicVariance.Paper.Proofs.Responses.GaussianTail
public import IsotropicVariance.Paper.Proofs.Responses.CellMoments
import Mathlib.Tactic.Linarith

/-!
# The reward moment at a fixed scale

The first bound of equation `eq:rewardmoment` in Lemma `lem:blocks`: only cells of the old tube
can contribute, their responses have uniform fixed moments, and Hölder with the Gaussian tube
tail makes the cell contributions summable with cost proportional to one plus the segment length.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Responses

open Contracts

variable {m : ℕ}

/-- The localization radius of a grid-cube pair, before replacing its noise. -/
noncomputable def pairLocalizationRadius (X : Setting m) (b s W : ℝ) (i : ℕ)
    (j k : Fin m → ℤ) (ω : X.Ω) : ℝ :=
  1 + W⁻¹ * maxSegmentDeviation ((Profiles.gridPair s W i j k).slab.density b (X.ρ ω))
    (Profiles.gridPair s W i j k).slab.set (Profiles.gridPair s W i j k).first
      (Profiles.gridPair s W i j k).second

/-- The constant in the `n`-th reward norm; it depends on dimension and the two input constants. -/
noncomputable def rewardMomentConst (m n : ℕ) (Cr Cp : ℝ) : ℝ :=
  (2 * osMomentConst (4 * (n : ℝ)) * Cp) ^ 2 *
    (2 * Real.exp (((2 * Real.sqrt m + 2) / Cr) ^ 2)) ^ (1 / (2 * (n : ℝ))) *
    gaussianSegmentConst m ((1 / (4 * Cr ^ 2)) / (2 * (n : ℝ)))

lemma rewardMomentConst_pos (m : ℕ) {n : ℕ} (hn : 1 ≤ n) {Cr Cp : ℝ}
    (hr : 0 < Cr) (hp : 0 < Cp) : 0 < rewardMomentConst m n Cr Cp := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM := osMomentConst_pos (4 * (n : ℝ))
  have hg := gaussianSegmentConst_pos m (by positivity : 0 < (1 / (4 * Cr ^ 2)) / (2 * (n : ℝ)))
  unfold rewardMomentConst
  positivity

/-- The reward bound uses only the profile estimate and the localization estimate at this scale,
for one old noise and the new noises of the blocks of a slab on any probability space. -/
theorem lintegral_reward_pow_le_of_isBlockCoupling {X : Setting m} {b : ℝ}
    (hb : X.IsUpperBound b) {s W Qn Cr Cp : ℝ} (hs : 0 ≤ s) (hW : 1 ≤ W) (hQ : 0 < Qn)
    (hr : 0 < Cr) (hp : 0 < Cp) {n : ℕ} (hn : 1 ≤ n)
    {L : ℕ} (hL : 1 ≤ L) (o : Fin m → Fin L) (i : ℕ) (j k : Fin m → ℤ)
    (hret : W * zNorm (k - j) ≤ s / 2)
    (hprof : Cited.IsOs X.P 1 (Cp * Qn) (slabProfile X b (Profiles.gridPair s W i j k)))
    (hloc : Cited.IsOs X.P 2 Cr (pairLocalizationRadius X b s W i j k))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {old : Ω' → X.Ω} {new : (Fin m → ℤ) → Ω' → X.Ω}
    (hcpl : ∀ g ∈ {g | IsBlockIndex L o g}, X.IsBlockCoupling (block s W L i g) P' old (new g)) :
    ∫⁻ ω, X.Y b s W Qn i j k {g | IsBlockIndex L o g} old new ω ^ n ∂P' ≤
      ENNReal.ofReal ((rewardMomentConst m n Cr Cp * (1 + zNorm (j - k))) ^ n) := by
  classical
  let p : ℝ := n
  have hp1 : 1 ≤ p := by change (1 : ℝ) ≤ (n : ℝ); exact_mod_cast hn
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  let I := {g : Fin m → ℤ | IsBlockIndex L o g}
  let a : ℝ := 2 * Real.sqrt m + 2
  let B : ℝ := 2 * Real.exp ((a / Cr) ^ 2)
  let c : ℝ := 1 / (4 * Cr ^ 2)
  let D : ℝ := 2 * osMomentConst (4 * p) * Cp
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := mul_pos (mul_pos (by norm_num) (osMomentConst_pos _)) hp
  let g₀ : I := ⟨cellBlockIndex L o 0, isBlockIndex_cellBlockIndex L o 0⟩
  have hold := (hcpl g₀ g₀.2).measurePreserving_old
  let U : I → Ω' → ℝ≥0∞ := fun g ω =>
    ENNReal.ofReal (X.blockGain b s W i j k (old ω) (new g ω) / Qn)
  have hUm (g : I) : AEMeasurable (U g) P' :=
    ((aemeasurable_blockGain hb hs hW0.le i j k hold
      (hcpl g g.2).measurePreserving_new).div_const Qn).ennreal_ofReal
  have hUnorm (g : I) : eLpNorm (U g) (ENNReal.ofReal (4 * p)) P' ≤ ENNReal.ofReal D :=
    eLpNorm_blockGain_div_le hb hs hW0.le hQ hp (by linarith) i j k hprof hold
      (hcpl g g.2).measurePreserving_new
  let r : X.Ω → ℝ := hloc.1.mk (pairLocalizationRadius X b s W i j k)
  have hrm : Measurable r := hloc.1.measurable_mk
  have hrae : pairLocalizationRadius X b s W i j k =ᵐ[X.P] r := hloc.1.ae_eq_mk
  have hrOs : Cited.IsOs X.P 2 Cr r := Cited.IsOs.congr hloc hrae
  have hrOldOs := Infra.Os.isOs_comp_measurePreserving hold hrOs
  let d : (Fin m → ℤ) → ℝ := fun z => infDist (transverseIntegerPoint z)
    (segment ℝ (transverseIntegerPoint j) (transverseIntegerPoint k))
  let A : (Fin m → ℤ) → Set Ω' := fun z => {ω | d z ≤ a + r (old ω)}
  have hAm (z : Fin m → ℤ) : MeasurableSet (A z) :=
    measurableSet_le measurable_const (measurable_const.add (hrm.comp hold.measurable))
  let f : (Fin m → ℤ) → Ω' → ℝ≥0∞ := fun z =>
    (A z).indicator fun ω => U ⟨cellBlockIndex L o z, isBlockIndex_cellBlockIndex L o z⟩ ω ^ 2
  have hfm (z : Fin m → ℤ) : AEMeasurable (f z) P' :=
    ((hUm _).pow_const 2).indicator (hAm z)
  have hprob (z : Fin m → ℤ) : P' (A z) ≤ ENNReal.ofReal (B * Real.exp (-c * d z ^ 2)) :=
    measure_le_shift_radius_le hr ha infDist_nonneg hrOldOs
  have hcell (z : Fin m → ℤ) : eLpNorm (f z) (ENNReal.ofReal p) P' ≤
      ENNReal.ofReal (D ^ 2 * B ^ (1 / (2 * p)) * Real.exp (-(c / (2 * p)) * d z ^ 2)) :=
    eLpNorm_indicator_sq_le_gaussian hp0 hD.le hB.le (hUm _) (hAm z) (hUnorm _) (hprob z)
  have hYeq (ω : Ω') : X.Y b s W Qn i j k I old new ω = ∑' g : I, U g ω ^ 2 := by
    simp only [Setting.Y, hret, ↓reduceIte]
    apply tsum_congr
    intro g
    exact ENNReal.ofReal_pow (div_nonneg (blockGain_nonneg X b s W i j k _ _) hQ.le) 2
  have hYm : AEMeasurable (fun ω => X.Y b s W Qn i j k I old new ω) P' := by
    simp_rw [hYeq]
    exact AEMeasurable.tsum fun g => (hUm g).pow_const 2
  have hnear : ∀ᵐ ω ∂P', ∀ g : I, ∀ D' : ℝ,
      (∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 (i + 1) k,
        ∀ γ : RectifiableCurve (Pt m),
          IsOneOptimal ((chainSlab s 0 i).density b (X.ρ (old ω)))
            (chainSlab s 0 i).set u v γ → ∀ t ∈ Icc (0 : ℝ) 1,
              infDist (γ.toFun t) (segment ℝ u v) ≤ D') →
      X.blockGain b s W i j k (old ω) (new g ω) ≠ 0 →
      ∃ z : Fin m → ℤ, cellBlockIndex L o z = g ∧ d z ≤ a + W⁻¹ * D' :=
    ae_all_iff.mpr fun g => IsBlockCoupling.ae_exists_cell_of_blockGain_ne_zero
      hb hs hW hL o i j k g g.2 (hcpl g g.2)
  have hpt : (fun ω => X.Y b s W Qn i j k I old new ω) ≤ᵐ[P']
      fun ω => ∑' z, f z ω := by
    filter_upwards [hnear, hold.quasiMeasurePreserving.ae hrae] with ω hω hrω
    rw [hYeq]
    apply tsum_blocks_le_tsum_cells (o := o) {z | d z ≤ a + r (old ω)} (fun g => U g ω ^ 2)
    intro g hg
    have hgain : X.blockGain b s W i j k (old ω) (new g ω) ≠ 0 := by
      intro hzero
      apply hg
      simp only [U, hzero, zero_div, ENNReal.ofReal_zero, zero_pow (by norm_num : 2 ≠ 0)]
    let δ := maxSegmentDeviation ((Profiles.gridPair s W i j k).slab.density b (X.ρ (old ω)))
      (Profiles.gridPair s W i j k).slab.set (Profiles.gridPair s W i j k).first
        (Profiles.gridPair s W i j k).second
    obtain ⟨z, hzg, hz⟩ := hω g δ (fun u hu v hv γ hγ t ht =>
      le_maxSegmentDeviation_slab X hb _
        (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_first _ hW0.le)).isBounded
        (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_second _ hW0.le)).isBounded
        (old ω) (Profiles.gridCube_subset_first s W hW0.le i j k hu)
        (Profiles.gridCube_subset_second s W hW0.le i j k hv)
        (by simpa only [Profiles.gridPair_slab_density, Profiles.gridPair_slab_set] using hγ) ht)
      hgain
    refine ⟨z, ?_, hzg⟩
    change d z ≤ a + r (old ω)
    change 1 + W⁻¹ * δ = r (old ω) at hrω
    linarith only [hz, hrω]
  apply lintegral_pow_le_of_eLpNorm_le hYm hn
    (mul_nonneg (rewardMomentConst_pos m hn hr hp).le (by linarith only [Profiles.zNorm_nonneg (j - k)] : 0 ≤ 1 + zNorm (j - k)))
  refine (eLpNorm_mono_enorm_ae (g := fun ω => ∑' z, f z ω) hYm.aestronglyMeasurable
    (hpt.mono fun ω hω => by simpa only [enorm_eq_self] using hω)).trans ?_
  exact eLpNorm_cell_sum_le hp1 (by positivity) (div_pos hc (by positivity)) j k hfm hcell

end IsotropicVariance.Paper.Proofs.Responses
