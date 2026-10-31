/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.LabelResidual.Good
public import CurvatureVariance.Paper.Proofs.LabelResidual.SmallTail
import CurvatureVariance.Paper.Proofs.ReplacementResponses.Arrays
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Paper.Proofs.Responses.RadiusArrays
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.Positivity

/-!
# The rewards of label resampling are small for bounded pairs

The second paragraph of [AB26, proof of Lemma 6.3], with the event `E` of the proof of Lemma
`lem:residual`: for bounded `|j − k|`, the event `E` that the fine cubes within distance
`R_i(j,k)` of the segment from `j` to `k` are not in the subcube of one block has probability
tending to zero; off `E` only that block contributes to `Y_i(j,k)`, and its label takes the same
value at the old and the new weights; on `E`, Hölder's inequality and equation `eq:rewardmoment`
apply. Together, `‖Y_i(j,k)‖_{4d} → 0` as `L → ∞`.

Let `d = m + 1`. For an exchangeable replacement of the blocks (`IsSlabReplacement`) whose new
weights of each block `g` of slab `i` preserve a label `λ_g` of the block at error `ε`
(`IsBlockLabel`), a radius `r₀ ≥ √m` and `Y = Y_i(j,k)` (`reward`):

* on the event `R_i(j,k) ≤ r₀`, if the fine cubes within `r₀` of `[j, k]` lie in the subcube of one
  block `g₀` (a good offset), `Y ≤ (X(new) + X(old))²` (`rewardSum_le_of_subset_subIndices`), `X`
  the error of the label of `g₀`; with Hölder's inequality on the event `R_i(j,k) > r₀`, this gives
  the bounds off and on `E` (`Proofs.Residual.lintegral_reward_pow_le_add_of_ball_subset`,
  `Proofs.Residual.offsetAvg_reward_pow_le`), for which this file has the moment lemmas
  (`lintegral_indicator_pow_le`, `add_pow_le_two_pow_mul`) and the tube lemmas
  (`mem_tubeIndices_of_near_left`, `fineIndex_mem_tubeIndices_left`, `tubeIndices_mono`);
* `lintegral_reward_pow_le_of_moment`: `E Y^{4d} ≤ (C(1 + |j − k|))^{4d}` in any case, given
  `E Y^{16d} ≤ (C(1 + |j − k|))^{16d}` (equation `eq:rewardmoment`);
* `ae_slabGeodesic_tube_of`: the slab geodesics between the row cubes exist almost surely and lie
  in the tube of radius `R_i(j,k)` (`TubeStatement`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.Contracts

universe u

variable {m : ℕ}

/-! ### Analytic lemmas -/

/-- An `L^N` bound `‖X‖_N ≤ ε`, `N ≥ 1` an integer, bounds the `N`-th moment of `‖X‖` by `ε^N`. -/
theorem lintegral_enorm_pow_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X : α → ℝ} {N : ℕ} (hN : N ≠ 0) {ε : ℝ} (h : eLpNorm X N μ ≤ ENNReal.ofReal ε) :
    ∫⁻ x, ‖X x‖ₑ ^ N ∂μ ≤ ENNReal.ofReal ε ^ N := by
  have hX : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hN) (ENNReal.natCast_ne_top N) hX,
    ENNReal.toReal_natCast] at h
  have h2 := ENNReal.rpow_le_rpow h hN0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hN0.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast] at h2
  simpa only [ENNReal.rpow_natCast] using h2

/-- The `N`-th moment of `X ∘ φ`, for `φ` with law `P`, from the bound `‖X‖_N ≤ ε` under `P`. -/
theorem lintegral_ofReal_comp_pow_le {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {Pr : Measure Ω} {P : Measure α} {φ : Ω → α} (hφ : Measurable φ) (hmap : Pr.map φ = P)
    {X : α → ℝ} {N : ℕ} (hN : N ≠ 0) {ε : ℝ} (h : eLpNorm X N P ≤ ENNReal.ofReal ε) :
    ∫⁻ x, ENNReal.ofReal (X (φ x)) ^ N ∂Pr ≤ ENNReal.ofReal ε ^ N := by
  have hX : AEStronglyMeasurable X P :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  have hf : AEMeasurable (fun y => ‖X y‖ₑ ^ N) (Pr.map φ) := by
    rw [hmap]
    exact hX.enorm.pow_const N
  calc ∫⁻ x, ENNReal.ofReal (X (φ x)) ^ N ∂Pr ≤ ∫⁻ x, ‖X (φ x)‖ₑ ^ N ∂Pr := by
        refine lintegral_mono fun x => pow_le_pow_left₀ bot_le ?_ N
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ∫⁻ y, ‖X y‖ₑ ^ N ∂(Pr.map φ) := (lintegral_map' hf hφ.aemeasurable).symm
    _ = ∫⁻ y, ‖X y‖ₑ ^ N ∂P := by rw [hmap]
    _ ≤ _ := lintegral_enorm_pow_le_of_eLpNorm_le hN h

/-- **Hölder's inequality on an event**: if `E Y^{4p} ≤ b⁴`, `b ≥ 0`, then
`E[Y^p; B] ≤ b P(B)^{3/4}`. -/
theorem lintegral_indicator_pow_le {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {Y : Ω → ℝ≥0∞} (hY : AEMeasurable Y Pr) {B : Set Ω} (hB : MeasurableSet B) {p : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hmom : ∫⁻ x, Y x ^ (4 * p) ∂Pr ≤ ENNReal.ofReal (b ^ 4)) :
    ∫⁻ x, B.indicator (fun x => Y x ^ p) x ∂Pr ≤ ENNReal.ofReal b * Pr B ^ ((3 : ℝ) / 4) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) :=
    Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hind : B.indicator (fun x => Y x ^ p) =
      (fun x => Y x ^ p) * B.indicator (1 : Ω → ℝ≥0∞) := by
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [hind]
  have hg : AEMeasurable (B.indicator (1 : Ω → ℝ≥0∞)) Pr :=
    (measurable_one.indicator hB).aemeasurable
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq Pr hpq (hY.pow_const p) hg).trans ?_
  have h1 : (∫⁻ x, (Y x ^ p) ^ (4 : ℝ) ∂Pr) ^ (1 / (4 : ℝ)) ≤ ENNReal.ofReal b := by
    have he : ∀ x, (Y x ^ p) ^ (4 : ℝ) = Y x ^ (4 * p) := by
      intro x
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ← pow_mul, mul_comm]
    simp_rw [he]
    calc (∫⁻ x, Y x ^ (4 * p) ∂Pr) ^ (1 / (4 : ℝ)) ≤ ENNReal.ofReal (b ^ 4) ^ (1 / (4 : ℝ)) :=
          ENNReal.rpow_le_rpow hmom (by norm_num)
      _ = ENNReal.ofReal b := by
          rw [ENNReal.ofReal_pow hb, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
  have h2 : (∫⁻ x, (B.indicator (1 : Ω → ℝ≥0∞) x) ^ (4 / 3 : ℝ) ∂Pr) ^ (1 / (4 / 3 : ℝ)) =
      Pr B ^ ((3 : ℝ) / 4) := by
    have he : ∀ x, (B.indicator (1 : Ω → ℝ≥0∞) x) ^ (4 / 3 : ℝ) = B.indicator 1 x := by
      intro x
      by_cases hx : x ∈ B
      · simp [hx]
      · simp [hx, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 4 / 3)]
    simp_rw [he]
    rw [lintegral_indicator_one hB]
    norm_num
  rw [h2]
  gcongr

/-- `(a + b)^N ≤ 2^N (a^N + b^N)` in `[0, ∞]`. -/
theorem add_pow_le_two_pow_mul (a b : ℝ≥0∞) (N : ℕ) : (a + b) ^ N ≤ 2 ^ N * (a ^ N + b ^ N) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ N ≤ (2 * b) ^ N := pow_le_pow_left₀ bot_le (by rw [two_mul]; gcongr) N
      _ = 2 ^ N * b ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (a ^ N + b ^ N) := by gcongr; exact le_add_self
  · calc (a + b) ^ N ≤ (2 * a) ^ N := pow_le_pow_left₀ bot_le (by rw [two_mul]; gcongr) N
      _ = 2 ^ N * a ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (a ^ N + b ^ N) := by gcongr; exact le_self_add

/-- `ofReal ε ^ N ≤ ofReal (ε ^ N)` for `N ≠ 0`. -/
theorem ofReal_pow_le_ofReal_pow (ε : ℝ) {N : ℕ} (hN : N ≠ 0) :
    ENNReal.ofReal ε ^ N ≤ ENNReal.ofReal (ε ^ N) := by
  rcases le_or_gt 0 ε with h | h
  · rw [ENNReal.ofReal_pow h]
  · rw [ENNReal.ofReal_of_nonpos h.le, zero_pow hN]
    exact bot_le

/-! ### Row cubes and the tube -/

/-- An integer vector with coordinates in `[−1, 1]` has norm at most `√m`. -/
theorem norm_transversePoint_le_sqrt {v : Fin m → ℤ} (hv : ∀ c, |v c| ≤ 1) :
    ‖transversePoint v‖ ≤ Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ c, ‖transversePoint v c‖ ^ 2 ≤ ∑ _c : Fin m, (1 : ℝ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h : ‖transversePoint v c‖ ≤ 1 := by
          have : |((v c : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hv c
          simpa [transversePoint, Real.norm_eq_abs] using this
        nlinarith [norm_nonneg (transversePoint v c)]
    _ = m := by simp

/-- A fine cube within one of `j` in each coordinate lies in the tube of radius `r₀ ≥ √m` about
`[j, k]`. -/
theorem mem_tubeIndices_of_near_left {j k j' : Fin m → ℤ} (hj' : ∀ c, |j' c - j c| ≤ 1)
    {r₀ : ℝ} (hr₀ : Real.sqrt m ≤ r₀) : j' ∈ tubeIndices j k (ENNReal.ofReal r₀) := by
  refine ENNReal.ofReal_le_ofReal ?_
  calc Metric.infDist (transversePoint j') (segment ℝ (transversePoint j) (transversePoint k))
      ≤ dist (transversePoint j') (transversePoint j) :=
        Metric.infDist_le_dist_of_mem (left_mem_segment ℝ _ _)
    _ = ‖transversePoint (j' - j)‖ := by rw [dist_eq_norm, Infra.FPP.transversePoint_sub]
    _ ≤ r₀ := (norm_transversePoint_le_sqrt hj').trans hr₀

/-- A fine cube within one of `k` in each coordinate lies in the tube of radius `r₀ ≥ √m` about
`[j, k]`. -/
theorem mem_tubeIndices_of_near_right {j k j' : Fin m → ℤ} (hj' : ∀ c, |j' c - k c| ≤ 1)
    {r₀ : ℝ} (hr₀ : Real.sqrt m ≤ r₀) : j' ∈ tubeIndices j k (ENNReal.ofReal r₀) := by
  refine ENNReal.ofReal_le_ofReal ?_
  calc Metric.infDist (transversePoint j') (segment ℝ (transversePoint j) (transversePoint k))
      ≤ dist (transversePoint j') (transversePoint k) :=
        Metric.infDist_le_dist_of_mem (right_mem_segment ℝ _ _)
    _ = ‖transversePoint (j' - k)‖ := by rw [dist_eq_norm, Infra.FPP.transversePoint_sub]
    _ ≤ r₀ := (norm_transversePoint_le_sqrt hj').trans hr₀

/-- The fine cube of a point of the row cube `I_h(j)` lies in the tube of radius `r₀ ≥ √m` about
`[j, k]`. -/
theorem fineIndex_mem_tubeIndices_left {n w : ℕ} (hw : 0 < w) {t : EuclideanSpace ℝ (Fin m)}
    {h : ℤ} {j k : Fin m → ℤ} {r₀ : ℝ} (hr₀ : Real.sqrt m ≤ r₀) {x : Vertex m}
    (hx : x ∈ rowCube n w t h j) :
    fineIndex w t (point x) ∈ tubeIndices j k (ENNReal.ofReal r₀) := by
  refine mem_tubeIndices_of_near_left (fun c => ?_) hr₀
  have hc := fineIndex_point_mem_of_mem_rowCube hw hx c
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2]

/-- The fine cube of a point of the row cube `I_h(k)` lies in the tube of radius `r₀ ≥ √m` about
`[j, k]`. -/
theorem fineIndex_mem_tubeIndices_right {n w : ℕ} (hw : 0 < w) {t : EuclideanSpace ℝ (Fin m)}
    {h : ℤ} {j k : Fin m → ℤ} {r₀ : ℝ} (hr₀ : Real.sqrt m ≤ r₀) {x : Vertex m}
    (hx : x ∈ rowCube n w t h k) :
    fineIndex w t (point x) ∈ tubeIndices j k (ENNReal.ofReal r₀) := by
  refine mem_tubeIndices_of_near_right (fun c => ?_) hr₀
  have hc := fineIndex_point_mem_of_mem_rowCube hw hx c
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2]

/-- Tubes are monotone in the radius. -/
theorem tubeIndices_mono (j k : Fin m → ℤ) {r r' : ℝ≥0∞} (h : r ≤ r') :
    tubeIndices j k r ⊆ tubeIndices j k r' :=
  fun _ hj' => (show _ ≤ r from hj').trans h

/-- The reward array is at most the block sum. -/
theorem reward_le_rewardSum (M : Model m) (K : ℕ) (A : ℝ) {Ω : Type*} (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (old : Ω → Config m) (new : ℕ → (Fin m → ℤ) → Ω → Config m)
    (i : ℕ) (j k : Fin m → ℤ) (x : Ω) :
    reward M K A n t old new i j k x ≤ rewardSum M K A n t old new i j k x := by
  unfold reward
  split_ifs
  exacts [le_rfl, bot_le]

/-! ### The reward bound for one replacement -/

/-- **The trivial reward bound** from equation `eq:rewardmoment`:
`E Y^{4d} ≤ (C(1 + |j − k|))^{4d}` if `E Y^{16d} ≤ (C(1 + |j − k|))^{16d}`. -/
theorem lintegral_reward_pow_le_of_moment {M : Model m} {K : ℕ} {A : ℝ} {n L : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ} {Ω : Type*}
    [MeasurableSpace Ω] {Pr : Measure Ω} {old : Ω → Config m}
    {new : ℕ → (Fin m → ℤ) → Ω → Config m}
    (hR : IsSlabReplacement M Pr n K (wInt M K A n) L t o old new) {i : ℕ} {j k : Fin m → ℤ}
    {C : ℝ} (hmom : ∫⁻ x, reward M K A n t old new i j k x ^ (16 * (m + 1)) ∂Pr ≤
      ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (16 * (m + 1)))) :
    ∫⁻ x, reward M K A n t old new i j k x ^ (4 * (m + 1)) ∂Pr ≤
      ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (4 * (m + 1))) := by
  have hPr : IsProbabilityMeasure Pr := hR.prob
  have hYm := ReplacementResponses.measurable_reward M K A n t hR.measurable_old
    hR.measurable_new i j k
  set b : ℝ := (C * (1 + ‖transversePoint (j - k)‖)) ^ (4 * (m + 1)) with hb
  have hb0 : 0 ≤ b := Even.pow_nonneg ⟨2 * (m + 1), by ring⟩ _
  have hmom' : ∫⁻ x, reward M K A n t old new i j k x ^ (4 * (4 * (m + 1))) ∂Pr ≤
      ENNReal.ofReal (b ^ 4) := by
    have e1 : 4 * (4 * (m + 1)) = 16 * (m + 1) := by ring
    have e2 : b ^ 4 = (C * (1 + ‖transversePoint (j - k)‖)) ^ (16 * (m + 1)) := by
      rw [hb, ← pow_mul]
      congr 1
      ring
    rw [e1, e2]
    exact hmom
  have h := lintegral_indicator_pow_le hYm.aemeasurable MeasurableSet.univ hb0 hmom'
  simpa only [Set.indicator_univ, measure_univ, ENNReal.one_rpow, mul_one] using h

/-! ### The contract level -/

/-- **Slab geodesics and the tube, almost surely** (the tube property of Section `sec:gain`,
with `ae_exists_isSlabGeodesic`): for every bound `T ≥ 0` on the slopes there is the constant `C_d`
of the tube property, chosen before the model, such that, for every model, `A ≥ 1`, `n ≥ 2`, slopes
`|t| ≤ T` and `i ≥ 1`, almost surely the slab geodesics between the row cubes `I_{i−1}(j)` and
`I_i(k)` exist and have the fine cubes of their edges within `R_i(j,k)` of `[j, k]`. The uses take
`T = bd.T + 1`, which bounds the slopes within `1` of `t₀`. -/
theorem ae_slabGeodesic_tube_of (htube : TubeStatement m) :
    ∀ T : ℝ, 0 ≤ T → ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ M : Model m, M.Standing → ∀ (K : ℕ) (A : ℝ), 1 ≤ A →
    ∀ n : ℕ, 2 ≤ n → ∀ t : EuclideanSpace ℝ (Fin m), ‖t‖ ≤ T → ∀ i : ℕ, 1 ≤ i →
    ∀ j k : Fin m → ℤ,
    ∀ᵐ ω ∂M.P, ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j,
      ∀ v ∈ rowCube n (wInt M K A n) t i k,
      (∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ) ∧
      ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
        ∀ e ∈ γ.edges, fineIndex (wInt M K A n) t (edgeMid e) ∈
          tubeIndices j k (slabRadius M K A Cd ω n t i j k) := by
  intro T hT0
  obtain ⟨Cd, hCd, hT⟩ := htube T hT0
  refine ⟨Cd, hCd, ?_⟩
  intro M hM K A hA n hn t ht1 i hi1 j k
  filter_upwards [ae_exists_isSlabGeodesic_of_mem hM] with ω hω u hu v hv
  refine ⟨hω _ _ (by nlinarith only [hn]) u v ?_ ?_, fun γ hγ e he => ?_⟩
  · rw [hu.1]; constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n]
  · rw [hv.1]; constructor <;> nlinarith only [Nat.cast_nonneg (α := ℤ) n]
  · exact hT M K A hA ω n (by omega) t ht1 i hi1 j k u hu v hv γ hγ e he
      (fineIndex (wInt M K A n) t (edgeMid e)) (by
        rw [sub_self, show transversePoint (0 : Fin m → ℤ) = 0 by ext; simp [transversePoint],
          norm_zero]
        norm_num)

end CurvatureVariance.Paper.Gain.LabelResidual
