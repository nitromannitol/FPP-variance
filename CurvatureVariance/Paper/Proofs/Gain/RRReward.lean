/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.RRReplacement
public import CurvatureVariance.Paper.Proofs.Gain.RRAnalysis
public import CurvatureVariance.Paper.Proofs.Responses.LoadAnalysis
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The first bound of equation `eq:rewardmoment` for the block sums

The first bound of equation `eq:rewardmoment`, `‖Y_i(j,k)‖_{16d} ≤ C(1 + |j − k|)`, here for the
unrestricted block sum `rewardSum` (the reward array is its restriction to the retained pairs), from
three hypotheses about the old weights, which the contracts of Sections `sec:cubes`,
`sec:localization` and `sec:gain` supply:

* a random variable `X ≥ |D_i − c|/Q_n` on the two row cubes, with `‖X‖_{64d} ≤ C_X` (Proposition
  `prop:profiles`: all moments of each supremum divided by `Q_n`);
* a measurable random radius `G` with `E G^{128d²} ≤ C₃^{128d²}` (Lemma `lem:localization`) such
  that the old geodesics between the row cubes exist and have their edges in fine cubes within
  `C_d(1 + G)` of `[j, k]` (the tube property, stated before Lemma `lem:blocks`);
* the lattice sum `∑_ℓ (1 + dist(ℓ, [j,k]))^{-4d} ≤ C_lat(1 + |j − k|)`.

The proof (`lintegral_rewardSum_pow_le`): the block sum is at most the sum over fine cubes `ℓ` of
`1_{ℓ ∈ tube} (X^{G(ℓ)} + X)²` (`tsum_sq_le_tsum_indicator_blockOf`); Minkowski's inequality for
the countable sum, Hölder's inequality with the indicator, `‖X^G + X‖_{64d} ≤ 2C_X` (the new weights
have the original law), Markov's inequality for the radius, and the lattice sum with exponent
`128d²/(32d) = 4d > d`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- The constant `(2C_X)² max((2C_d+3)^q, (2(C_d+1))^q C₃^q)^{1/(32d)} C_lat` of the first bound
of equation `eq:rewardmoment`, `q = 128d²`. -/
noncomputable def rewardConst (m : ℕ) (Cd C₃ CX Clat : ℝ) : ℝ :=
  (2 * CX) ^ 2 * max ((2 * Cd + 3) ^ (128 * (m + 1) ^ 2))
    ((2 * (Cd + 1)) ^ (128 * (m + 1) ^ 2) * C₃ ^ (128 * (m + 1) ^ 2)) ^
      (1 / (32 * ((m : ℝ) + 1))) * Clat

theorem rewardConst_nonneg (m : ℕ) {Cd C₃ CX Clat : ℝ} (hCd : 0 ≤ Cd) (hClat : 0 ≤ Clat) :
    0 ≤ rewardConst m Cd C₃ CX Clat := by
  unfold rewardConst
  have : 0 ≤ max ((2 * Cd + 3) ^ (128 * (m + 1) ^ 2))
      ((2 * (Cd + 1)) ^ (128 * (m + 1) ^ 2) * C₃ ^ (128 * (m + 1) ^ 2)) :=
    le_trans (by positivity) (le_max_left _ _)
  positivity

/-- **The first bound of equation `eq:rewardmoment` for the block sum**: under the three hypotheses
described in the module docstring, `E Y_i(j,k)^{16d} ≤ (C (1 + |j − k|))^{16d}` with
`C = rewardConst`. -/
theorem lintegral_rewardSum_pow_le {M : Model m} {K : ℕ} {A : ℝ} {n L : ℕ} (hL : 1 ≤ L)
    {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ} {Ω : Type*} [MeasurableSpace Ω]
    {Pr : Measure Ω} {old : Ω → Config m} {new : ℕ → (Fin m → ℤ) → Ω → Config m}
    (hR : IsSlabReplacement M Pr n K (wInt M K A n) L t o old new) (hQ : 0 < Q M K A n)
    (i : ℕ) (j k : Fin m → ℤ) {Cd C₃ CX Clat : ℝ} (hCd : 0 ≤ Cd) (hCX : 0 ≤ CX)
    (hClat : 0 ≤ Clat) {G : Config m → ℝ≥0∞} (hG : Measurable G)
    (hGmom : ∫⁻ ω, G ω ^ (128 * (m + 1) ^ 2) ∂M.P ≤ ENNReal.ofReal (C₃ ^ (128 * (m + 1) ^ 2)))
    (hgeo : ∀ᵐ ω ∂M.P, ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j,
      ∀ v ∈ rowCube n (wInt M K A n) t i k,
      (∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ) ∧
      ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
        ∀ e ∈ γ.edges, fineIndex (wInt M K A n) t (edgeMid e) ∈
          tubeIndices j k (ENNReal.ofReal Cd * (1 + G ω)))
    {X : Config m → ℝ} (hX : Measurable X) (c : Vertex m → Vertex m → ℝ)
    (hXmom : eLpNorm (fun ω => ENNReal.ofReal (X ω)) (ENNReal.ofReal (64 * ((m : ℝ) + 1))) M.P ≤
      ENNReal.ofReal CX)
    (hXb : ∀ᵐ ω ∂M.P, ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j,
      ∀ v ∈ rowCube n (wInt M K A n) t i k,
      |slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - c u v| ≤ Q M K A n * X ω)
    (hlat : ∑' ℓ : Fin m → ℤ, ENNReal.ofReal ((1 + Metric.infDist (transversePoint ℓ)
        (segment ℝ (transversePoint j) (transversePoint k))) ^ (-(4 * ((m : ℝ) + 1)))) ≤
      ENNReal.ofReal (Clat * (1 + ‖transversePoint (j - k)‖))) :
    ∫⁻ ω, rewardSum M K A n t old new i j k ω ^ (16 * (m + 1)) ∂Pr ≤
      ENNReal.ofReal ((rewardConst m Cd C₃ CX Clat * (1 + ‖transversePoint (j - k)‖)) ^
        (16 * (m + 1))) := by
  have hPr : IsProbabilityMeasure Pr := hR.prob
  set d : ℝ := (m : ℝ) + 1 with hd
  have hd1 : 1 ≤ d := by rw [hd]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set q : ℕ := 128 * (m + 1) ^ 2 with hq
  set Mt : ℝ := max ((2 * Cd + 3) ^ q) ((2 * (Cd + 1)) ^ q * C₃ ^ q) with hMt
  have hMt0 : 0 ≤ Mt := le_trans (by positivity) (le_max_left _ _)
  set V : (Fin m → ℤ) → Ω → ℝ≥0∞ := fun g ω =>
    ENNReal.ofReal (X (new i g ω)) + ENNReal.ofReal (X (old ω)) with hV
  set B : (Fin m → ℤ) → Set Ω := fun ℓ =>
    {ω | ℓ ∈ tubeIndices j k (ENNReal.ofReal Cd * (1 + G (old ω)))} with hB
  set f : (Fin m → ℤ) → Ω → ℝ≥0∞ := fun ℓ =>
    (B ℓ).indicator (fun ω => V (blockOf L (o i) ℓ) ω ^ 2) with hf
  have hVm : ∀ g, Measurable (V g) := fun g =>
    (hX.comp (hR.measurable_new i g)).ennreal_ofReal.add (hX.comp hR.measurable_old).ennreal_ofReal
  have hBm : ∀ ℓ, MeasurableSet (B ℓ) := fun ℓ =>
    measurableSet_le measurable_const (((hG.comp hR.measurable_old).const_add 1).const_mul _)
  -- the pointwise cell bound
  have hpt : ∀ᵐ ω ∂Pr, rewardSum M K A n t old new i j k ω ≤ ∑' ℓ, f ℓ ω := by
    filter_upwards [IsSlabReplacement.ae_old hR hgeo, IsSlabReplacement.ae_old hR hXb,
      IsSlabReplacement.ae_new hR hXb] with ω h1 h2 h3
    rw [rewardSum_eq]
    have hQ2 : (ENNReal.ofReal (Q M K A n ^ 2))⁻¹ = (ENNReal.ofReal (Q M K A n))⁻¹ ^ 2 := by
      rw [ENNReal.ofReal_pow hQ.le, ENNReal.inv_pow]
    rw [hQ2, ← ENNReal.tsum_mul_left]
    simp_rw [← mul_pow]
    refine (tsum_sq_le_tsum_indicator_blockOf hL (o i)
      (tubeIndices j k (ENNReal.ofReal Cd * (1 + G (old ω))))
      (fun g => (ENNReal.ofReal (Q M K A n))⁻¹ * blockSup n i
        (rowCube n (wInt M K A n) t ((i : ℤ) - 1) j) (rowCube n (wInt M K A n) t i k)
        (old ω) (new i g ω)) (fun g => V g ω) (fun g => ?_) (fun g hg => ?_)).trans
      (le_of_eq (tsum_congr fun ℓ => ?_))
    · exact blockSup_le_of_abs_sub_le hQ h2 (h3 i g)
    · rw [blockSup_eq_zero_of_disjoint (fun u hu v hv => (h1 u hu v hv).1)
        (fun u hu v hv => (h1 u hu v hv).2) hg (fun e he => hR.agree i g ω e he), mul_zero]
    · by_cases hℓ : ℓ ∈ tubeIndices j k (ENNReal.ofReal Cd * (1 + G (old ω)))
      · rw [Set.indicator_of_mem hℓ]
        exact (Set.indicator_of_mem (show ω ∈ B ℓ from hℓ)
          (fun ω => V (blockOf L (o i) ℓ) ω ^ 2)).symm
      · rw [Set.indicator_of_notMem hℓ]
        exact (Set.indicator_of_notMem (show ω ∉ B ℓ from hℓ)
          (fun ω => V (blockOf L (o i) ℓ) ω ^ 2)).symm
  -- the new and old deviations in `L^{64d}`
  have hVp : ∀ g, eLpNorm (V g) (ENNReal.ofReal (64 * d)) Pr ≤ ENNReal.ofReal (2 * CX) := by
    intro g
    have h64 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (64 * d) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
    have hXo : Measurable fun ω : Config m => ENNReal.ofReal (X ω) := hX.ennreal_ofReal
    calc eLpNorm (V g) (ENNReal.ofReal (64 * d)) Pr
        = eLpNorm ((fun ω => ENNReal.ofReal (X (new i g ω))) +
            fun ω => ENNReal.ofReal (X (old ω))) (ENNReal.ofReal (64 * d)) Pr := rfl
      _ ≤ eLpNorm (fun ω => ENNReal.ofReal (X (new i g ω))) (ENNReal.ofReal (64 * d)) Pr +
            eLpNorm (fun ω => ENNReal.ofReal (X (old ω))) (ENNReal.ofReal (64 * d)) Pr :=
          eLpNorm_add_le h64
      _ = eLpNorm (fun ω => ENNReal.ofReal (X ω)) (ENNReal.ofReal (64 * d)) M.P +
            eLpNorm (fun ω => ENNReal.ofReal (X ω)) (ENNReal.ofReal (64 * d)) M.P := by
          rw [IsSlabReplacement.eLpNorm_comp_new hR hXo, IsSlabReplacement.eLpNorm_comp_old hR hXo]
      _ ≤ ENNReal.ofReal CX + ENNReal.ofReal CX := add_le_add hXmom hXmom
      _ = ENNReal.ofReal (2 * CX) := by
          rw [← ENNReal.ofReal_add hCX hCX]; congr 1; ring
  -- each fine cube in `L^{16d}`
  have hcell : ∀ ℓ, eLpNorm (f ℓ) (ENNReal.ofReal (16 * d)) Pr ≤
      ENNReal.ofReal ((2 * CX) ^ 2 * Mt ^ (1 / (32 * d)) *
        (1 + Metric.infDist (transversePoint ℓ)
          (segment ℝ (transversePoint j) (transversePoint k))) ^ (-(4 * d))) := by
    intro ℓ
    set δ := Metric.infDist (transversePoint ℓ)
      (segment ℝ (transversePoint j) (transversePoint k))
    have hδ : 0 ≤ δ := Metric.infDist_nonneg
    have hsq : (fun ω => V (blockOf L (o i) ℓ) ω ^ 2) =
        fun ω => ‖V (blockOf L (o i) ℓ) ω‖ₑ ^ (2 : ℝ) := by
      funext ω; simp
    have h1 := Responses.eLpNorm_indicator_le_double_ennreal (μ := Pr) (by positivity : (0 : ℝ) < 16 * d)
      ((hVm (blockOf L (o i) ℓ)).pow_const 2).aemeasurable (hBm ℓ)
    have h2 : eLpNorm (fun ω => V (blockOf L (o i) ℓ) ω ^ 2)
        (ENNReal.ofReal (2 * (16 * d))) Pr ≤ ENNReal.ofReal (2 * CX) ^ 2 := by
      rw [hsq, eLpNorm_enorm_rpow _ (hVm _).aestronglyMeasurable (by norm_num : (0 : ℝ) < 2),
        ← ENNReal.ofReal_mul (by positivity)]
      have : 2 * (16 * d) * 2 = 64 * d := by ring
      rw [this, ENNReal.rpow_two]
      exact pow_le_pow_left₀ bot_le (hVp _) 2
    have hmomo : ∫⁻ ω, G (old ω) ^ q ∂Pr ≤ ENNReal.ofReal (C₃ ^ q) := by
      rw [IsSlabReplacement.lintegral_comp_old hR (hG.pow_const q)]
      exact hGmom
    have h3 : Pr (B ℓ) ≤ ENNReal.ofReal (Mt * (1 + δ) ^ (-(q : ℝ))) :=
      measure_mem_tubeIndices_le hCd (hG.comp hR.measurable_old) hmomo j k ℓ
    have h4 : Pr (B ℓ) ^ (1 / (2 * (16 * d))) ≤
        ENNReal.ofReal (Mt ^ (1 / (32 * d)) * (1 + δ) ^ (-(4 * d))) := by
      have h8 : (1 / (2 * (16 * d))) = 1 / (32 * d) := by ring
      rw [h8]
      refine (ENNReal.rpow_le_rpow h3 (by positivity)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
        Real.mul_rpow hMt0 (by positivity), ← Real.rpow_mul (by positivity)]
      congr 2
      have hq' : (q : ℝ) = 128 * d ^ 2 := by rw [hq, hd]; push_cast; ring
      rw [hq']
      field_simp
      ring_nf
    refine h1.trans ((mul_le_mul' h2 h4).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  -- Minkowski and the lattice sum
  have hfm : ∀ ℓ, AEMeasurable (f ℓ) Pr := fun ℓ =>
    (((hVm _).pow_const 2).indicator (hBm ℓ)).aemeasurable
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (16 * d) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsum : eLpNorm (fun ω => ∑' ℓ, f ℓ ω) (ENNReal.ofReal (16 * d)) Pr ≤
      ENNReal.ofReal (rewardConst m Cd C₃ CX Clat * (1 + ‖transversePoint (j - k)‖)) := by
    calc eLpNorm (fun ω => ∑' ℓ, f ℓ ω) (ENNReal.ofReal (16 * d)) Pr
        ≤ ∑' ℓ, eLpNorm (f ℓ) (ENNReal.ofReal (16 * d)) Pr := Responses.eLpNorm_tsum_le hp1 hfm
      _ ≤ ∑' ℓ : Fin m → ℤ, ENNReal.ofReal ((2 * CX) ^ 2 * Mt ^ (1 / (32 * d))) *
          ENNReal.ofReal ((1 + Metric.infDist (transversePoint ℓ)
            (segment ℝ (transversePoint j) (transversePoint k))) ^ (-(4 * d))) := by
        refine ENNReal.tsum_le_tsum fun ℓ => (hcell ℓ).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((2 * CX) ^ 2 * Mt ^ (1 / (32 * d))) *
          ∑' ℓ : Fin m → ℤ, ENNReal.ofReal ((1 + Metric.infDist (transversePoint ℓ)
            (segment ℝ (transversePoint j) (transversePoint k))) ^ (-(4 * d))) :=
        ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal ((2 * CX) ^ 2 * Mt ^ (1 / (32 * d))) *
          ENNReal.ofReal (Clat * (1 + ‖transversePoint (j - k)‖)) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [rewardConst, hMt, hq, hd]
        ring
  have hN : ((16 * (m + 1) : ℕ) : ℝ) = 16 * d := by rw [hd]; push_cast; ring
  have hmom := lintegral_pow_le_of_eLpNorm_le (μ := Pr)
    (AEMeasurable.tsum hfm) (n := 16 * (m + 1)) (by omega)
    (c := rewardConst m Cd C₃ CX Clat * (1 + ‖transversePoint (j - k)‖))
    (mul_nonneg (rewardConst_nonneg m hCd hClat) (by positivity)) (by rw [hN]; exact hsum)
  refine le_trans (lintegral_mono_ae ?_) hmom
  filter_upwards [hpt] with ω hω
  exact pow_le_pow_left₀ bot_le hω _

end CurvatureVariance.Paper.Gain
