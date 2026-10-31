/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.Gain.RRReward
import CurvatureVariance.Paper.Proofs.Gain.TubeGeodesics
import CurvatureVariance.Paper.Proofs.Responses.LocalizationMoment
import CurvatureVariance.Paper.Proofs.Responses.RowCubes
import CurvatureVariance.Paper.Proofs.Responses.RowGeometry
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.SlabArrays
import CurvatureVariance.Infra.Os.Moments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The first bound of equation `eq:rewardmoment` from the contracts of Section `sec:cubes`

The first bound of equation `eq:rewardmoment`: for `N` large, every target, every exchangeable
replacement, every slab `i` and every retained pair `(j, k)`, `‖Y_i(j,k)‖_{16d} ≤ C(1 + |j − k|)`
with `C` independent of `K`, `L` and the offsets (`rewardSum_moment`). The hypotheses of
`lintegral_rewardSum_pow_le` come from:

* Proposition `prop:profiles`, its second case (`ProfilesStatement`, `b = 1`, `κ = 1/(9K)`, at
  length `n`): the row cubes `I_{i−1}(j)`, `I_i(k)` form a cube pair (`Responses.isCubePair_rows`)
  with slope at most `n^{δ/100−1/4}` on retained pairs (`Responses.rowPairSlope_norm_le`); the
  supremum of `|D_i − μ(v − u)|` is at most `X ≤ O₁(C Q_n)`, and `X/Q_n` has bounded `64d`-th moment
  (`eLpNorm_ofReal_le_of_isOs`);
* Lemma `lem:localization` (`LocalizationStatement`, same `b`, `κ`, through
  `Contracts.exists_radius_moments_of`): the `128d²` moment of the radius `R` of `D_i` on the row
  cubes, measurable by `Responses.measurable_locRadiusSlab`;
* the tube property (`TubeStatement`, the text before Lemma `lem:blocks`) and the a.s. existence of
  slab geodesics (`ae_exists_isSlabGeodesic_of_mem`);
* equation `eq:scales` (`ScalesStatement`), the width margin for the rounding of the row cubes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- **Moments of an `O₁(θ)` variable in `L^p`**: `‖X_+‖_p ≤ (2(1 + ⌈p⌉!))^{1/p} θ` for `p ≥ 1`. -/
theorem eLpNorm_ofReal_le_of_isOs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θ : ℝ}
    {X : Ω → ℝ} (hX : CurvatureVariance.IsOs P 1 θ X) (hθ : 0 < θ) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun ω => ENNReal.ofReal (X ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((2 * (1 + ((Nat.ceil p).factorial : ℝ))) ^ (1 / p) * θ) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (X ω)) P := hX.1.ennreal_ofReal
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    hmeas.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  have hpt : ∀ ω, ‖ENNReal.ofReal (X ω)‖ₑ ^ p = ENNReal.ofReal (max (X ω) 0 ^ p) := by
    intro ω
    rw [enorm_eq_self, ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hp0.le]
    congr 1
    rcases le_total (X ω) 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  simp_rw [hpt]
  have hm := hX.lintegral_pos_rpow_le one_pos hθ hp0.le
  rw [div_one] at hm
  have hB : 0 ≤ 2 * (1 + ((Nat.ceil p).factorial : ℝ)) := by positivity
  calc (∫⁻ ω, ENNReal.ofReal (max (X ω) 0 ^ p) ∂P) ^ (1 / p)
      ≤ ENNReal.ofReal (2 * (1 + ((Nat.ceil p).factorial : ℝ)) * θ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hm (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
        Real.mul_rpow hB (by positivity), ← Real.rpow_mul hθ.le, mul_one_div_cancel hp0.ne',
        Real.rpow_one]

/-- The constant `(2(1 + ⌈64d⌉!))^{1/(64d)}` of the `64d`-th moment of an `O₁(1)` variable. -/
noncomputable def osMomentConst (m : ℕ) : ℝ :=
  (2 * (1 + ((Nat.ceil (64 * ((m : ℝ) + 1))).factorial : ℝ))) ^ (1 / (64 * ((m : ℝ) + 1)))

theorem osMomentConst_nonneg (m : ℕ) : 0 ≤ osMomentConst m := by
  unfold osMomentConst; positivity

/-- **The first bound of equation `eq:rewardmoment` for the block sums, from the contracts**: there
is `C`, independent of `K`, `L` and the offsets, such that for `N` large under equation
`eq:premise`, every target, every exchangeable replacement, every slab `1 ≤ i ≤ K` and every
retained pair `(j, k)`, `E Y_i(j,k)^{16d} ≤ (C(1 + |j − k|))^{16d}`. Its constants and thresholds
come before the model and depend only on the bounds `bd`. The proof is from Proposition
`prop:profiles`, Lemma `lem:localization` and equation `eq:scales`. -/
theorem rewardSum_moment (hprof : ProfilesStatement m) (hrad : LocalizationStatement m)
    (hscales : ScalesStatement m) (htube : TubeStatement m) :
    ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
    ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
    Premise M K A N → RangeA M K A N Cstar →
    ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
    ∀ (L : ℕ), 1 ≤ L → ∀ o : ℕ → Fin m → ℤ,
    ∀ (Ω : Type*) [MeasurableSpace Ω] (Pr : Measure Ω) (old : Ω → Config m)
      (new : ℕ → (Fin m → ℤ) → Ω → Config m),
      IsSlabReplacement M Pr n K (wInt M K A n) L (targetSlope ℓ y) o old new →
      ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ j k : Fin m → ℤ, IsRetainedPair M n (wInt M K A n) j k →
        ∫⁻ ω, rewardSum M K A n (targetSlope ℓ y) old new i j k ω ^ (16 * (m + 1)) ∂Pr ≤
          ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (16 * (m + 1))) := by
  intro bd hbd Cstar
  obtain ⟨Cb, hCb, hS⟩ := hprof bd hbd Cstar 1 le_rfl
  obtain ⟨Cr, hCr, hRd⟩ := exists_radius_moments_of hrad bd hbd Cstar
  obtain ⟨Cd, hCd, hT⟩ := htube (bd.T + 1) (by linarith [hbd.T_nonneg])
  obtain ⟨Clat, hClat, hlat⟩ := Responses.tsum_rpow_infDist_segment_le (m := m)
    (s := 4 * ((m : ℝ) + 1)) (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  set CX : ℝ := osMomentConst m * Cb with hCXdef
  have hCX : 0 ≤ CX := mul_nonneg (osMomentConst_nonneg m) hCb.le
  refine ⟨max 1 (rewardConst m Cd Cr CX Clat), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro K hK
  have hKpos : (0 : ℝ) < K := by
    have hK1 : 1 ≤ K := by omega
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)
  obtain ⟨NS, hNS⟩ := hS (1 / (9 * K)) (by positivity) K hK
  obtain ⟨NR, hNR⟩ := hRd (1 / (9 * K)) (by positivity) K hK
  obtain ⟨Nw, hNw⟩ := Responses.eventually_row_width_small hscales bd hbd Cstar K hK
  refine ⟨max ((9 * K) ^ 2) (max NS (max NR Nw)), ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar L hL o Ω _ Pr old new hR i hi1 hiK j k hjk
  have hNS' : NS ≤ N := le_trans (le_max_left _ _) ((le_max_right _ _).trans hN)
  have hNR' : NR ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    ((le_max_right _ _).trans hN)
  have hNw' : Nw ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    ((le_max_right _ _).trans hN)
  obtain ⟨hn, hsqrt, -, -⟩ := Responses.target_size_bounds (by omega : 1 ≤ K)
    ((le_max_left _ _).trans hN) htar
  set t := targetSlope ℓ y with ht
  set w := wInt M K A n with hw
  have hwidth := hNw M hM hfit N hNw' A hA hrange n hsqrt
  have hround : 16 * Real.sqrt m ≤ (n : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := by
    rw [show 1 + (M.δ / 100 - 1 / 4) = (3 : ℝ) / 4 + M.δ / 100 by ring]
    nlinarith only [hwidth, Real.sqrt_nonneg (m : ℝ), Nat.cast_nonneg (α := ℝ) w]
  have hjk' : (w : ℝ) * ‖transversePoint (k - j)‖ ≤ (n : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) / 8 := by
    rw [show 1 + (M.δ / 100 - 1 / 4) = (3 : ℝ) / 4 + M.δ / 100 by ring]
    have h := hjk
    unfold IsRetainedPair at h
    linarith only [h]
  have htn := Responses.targetSlope_norm_le_half hM hK (by omega) htar.1 htar.2.2.2
  have hslope := Responses.rowPairSlope_norm_le (by omega : 1 ≤ n) t ((i : ℤ) - 1) j k
    htn hjk' hround
  have hwpos : 1 ≤ w := Responses.one_le_wInt (M := M) (K := K) hA (by omega : 1 ≤ n)
  have hpair := Responses.isCubePair_rows (M := M) (K := K) (A := A) (b := 1) (by omega : 1 ≤ n)
    hwpos (by simpa only [one_mul] using Responses.wInt_sub_one_le_W M K A n) t ((i : ℤ) - 1) j k
  simp only [sub_add_cancel] at hpair
  have hnlo : 1 / (9 * (K : ℝ)) * N ≤ n := by
    have h := htar.2.1
    rw [htar.1, Nat.cast_mul] at h
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 9 * K by positivity)).mp
    field_simp
    nlinarith only [h]
  have hnN : n ≤ N := by
    have hnℓ : n ≤ ℓ := by rw [htar.1]; exact Nat.le_mul_of_pos_left n (by omega)
    exact hnℓ.trans htar.2.2.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hQ : 0 < Q M K A n := mul_pos (lt_of_lt_of_le zero_lt_one hA) (Real.rpow_pos_of_pos hnpos _)
  -- the slope of the target is within one of `t₀`
  have hepow : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ n by omega))
    linarith [hM.delta_le_one]
  have ht1 : ‖t‖ ≤ bd.T + 1 := by
    have h1 : ‖t‖ ≤ ‖t - M.t₀‖ + ‖M.t₀‖ := by
      calc ‖t‖ = ‖(t - M.t₀) + M.t₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖t - M.t₀‖ + ‖M.t₀‖ := norm_add_le _ _
    linarith only [htn, hepow, h1, hfit.t₀_le]
  -- Proposition `prop:profiles`, its second case
  obtain ⟨X, hXos, hXae⟩ := hNS M hM hfit N hNS' A hA hprem hrange n _ _ _ hpair
    (Or.inr ⟨hnlo,
      by have : (n : ℝ) ≤ N := by exact_mod_cast hnN
         linarith only [this, Nat.cast_nonneg (α := ℝ) N],
      by linarith only [hslope, Real.rpow_nonneg hnpos.le (M.δ / 100 - 1 / 4)]⟩)
  set Xm : Config m → ℝ := hXos.1.mk X with hXmdef
  have hXm : Measurable Xm := hXos.1.measurable_mk
  have hXmos : CurvatureVariance.IsOs M.P 1 (Cb * Q M K A n) Xm := hXos.congr hXos.1.ae_eq_mk
  set Xn : Config m → ℝ := fun ω => (Q M K A n)⁻¹ * Xm ω with hXndef
  have hXnos : CurvatureVariance.IsOs M.P 1 Cb Xn := by
    have h := (Infra.Os.isOs_mul_iff (P := M.P) (s := 1) (θ := Cb * Q M K A n) (X := Xm)
      (inv_pos.2 hQ)).2 hXmos
    have e1 : (Q M K A n)⁻¹ * (Cb * Q M K A n) = Cb := by field_simp
    rwa [e1] at h
  have hXnm : Measurable Xn := hXm.const_mul _
  have hXmom : eLpNorm (fun ω => ENNReal.ofReal (Xn ω)) (ENNReal.ofReal (64 * ((m : ℝ) + 1)))
      M.P ≤ ENNReal.ofReal CX := by
    refine (eLpNorm_ofReal_le_of_isOs hXnos hCb
      (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])).trans (le_of_eq ?_)
    rw [hCXdef, osMomentConst]
  have hXb : ∀ᵐ ω ∂M.P, ∀ u ∈ rowCube n w t ((i : ℤ) - 1) j, ∀ v ∈ rowCube n w t i k,
      |slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - M.μ.1 (point v - point u)| ≤
        Q M K A n * Xn ω := by
    filter_upwards [hXae, hXos.1.ae_eq_mk] with ω hω hωeq u hu v hv
    have h := hω.2 u hu v hv
    rw [hu.1, hv.1] at h
    rw [hXndef]
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul, hXmdef, ← hωeq]
    exact h
  -- Lemma `lem:localization`
  have hRmom := (hNR M hM hfit N hNR' A hA hprem hrange n hnlo hnN _ _ _ hpair hslope).2
    (((i : ℤ) - 1) * n) (fun u hu => hu.1)
  have hface : ((i : ℤ) - 1) * n + n = (i : ℤ) * n := by ring
  rw [hface] at hRmom
  -- the tube and the geodesics
  have hgeo : ∀ᵐ ω ∂M.P, ∀ u ∈ rowCube n w t ((i : ℤ) - 1) j, ∀ v ∈ rowCube n w t i k,
      (∃ γ : (latticeGraph m).Walk u v,
        IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ) ∧
      ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
        ∀ e ∈ γ.edges, fineIndex w t (edgeMid e) ∈
          tubeIndices j k (ENNReal.ofReal Cd * (1 + locRadiusSlab ω (((i : ℤ) - 1) * n)
            ((i : ℤ) * n) (rowCube n w t ((i : ℤ) - 1) j) (rowCube n w t i k) (W M K A n))) := by
    filter_upwards [ae_exists_isSlabGeodesic_of_mem hM] with ω hω u hu v hv
    refine ⟨hω _ _ (by nlinarith only [hn]) u v ?_ ?_, fun γ hγ e he => ?_⟩
    · rw [hu.1]; constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n]
    · rw [hv.1]; constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n]
    · have h := hT M K A hA ω n (by omega) t ht1 i hi1 j k u hu v hv γ hγ e he
        (fineIndex w t (edgeMid e)) (by
          rw [sub_self, show transversePoint (0 : Fin m → ℤ) = 0 by ext; simp [transversePoint],
            norm_zero]
          norm_num)
      exact h
  have hmain := lintegral_rewardSum_pow_le hL hR hQ i j k hCd hCX hClat.le
    (Responses.measurable_locRadiusSlab (((i : ℤ) - 1) * n) ((i : ℤ) * n)
      (rowCube n w t ((i : ℤ) - 1) j) (rowCube n w t i k) (W M K A n)) hRmom hgeo hXnm
    (fun u v => M.μ.1 (point v - point u)) hXmom hXb (hlat j k)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 := rewardConst_nonneg m (C₃ := Cr) (CX := CX) hCd hClat.le
  gcongr
  exact le_max_right _ _

end CurvatureVariance.Paper.Gain
