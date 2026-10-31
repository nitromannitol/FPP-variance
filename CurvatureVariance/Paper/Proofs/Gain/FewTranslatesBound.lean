/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.Gain.AVMoments
public import CurvatureVariance.Paper.Proofs.Gain.FewTranslatesJensen
public import CurvatureVariance.Paper.Proofs.Gain.L1Influence
public import CurvatureVariance.Paper.Proofs.Responses.IndependentReplacement
import CurvatureVariance.Infra.EfronStein.Countable
import CurvatureVariance.Paper.Proofs.Moments.Scales
import CurvatureVariance.Paper.Proofs.Responses.Energy
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge

/-!
# Lemma `lem:fewtranslates`

For `L ≥ 16` and `N` large depending on `K` and `L`, for every choice of the `a_i`,
`Σ_G E[(f − E_G[f])²] ≤ C K Q_n²` and `Σ_G E[|f − E_G[f]|]² ≤ C K^{−1/6} K Q_n²`, for
`f = E[F̄ | (X_G)_G]` and `τ^G` the resampling with `σ_G` constant. The paper's proof is that of
[AB26, Lemma 6.4] with the changes stated in the proof of Lemma `lem:fewtranslates`. The continuum
counterpart is `IsotropicVariance.Paper.Proofs.Gain.FewTranslatesBound`.

The steps of the paper's proof, in order.

* `f − E_G[f] = ⌈K^{2/3}⌉⁻¹ Σ_m E[F_m − F_m^G | (X_H)_H]`:
  `IsOffsetLabels.eLpNorm_labelMean_sub_le`.
* `F_m^G = F_m` unless `G` meets the tube of one of the two weights:
  `Gain.measure_targetMin_ne_le`. With the cube indices, as in the paper, the cells within
  `R_i(J_{i−1}, J_i)` of `[J_{i−1}, J_i]` lie in at most `3 + |ΔJ| + 2 R_i` of the blocks
  `G + m'Lwe₂` (`Gain.card_translates_meet_tube_le`).
* By equations `eq:rowenergy` and `eq:radiusenergy`, the squares of these numbers, summed over `i`,
  have mean at most `CK`, so each number has mean at most `C√K`: `Gain.sum_measure_allTubesMeet_le`.
* The two bounds of the last display of the proof of [AB26, Lemma 6.4], Jensen's inequality and the
  Cauchy–Schwarz inequality for the joint law of `m` and the weights:
  `sq_eLpNorm_two_labelMean_sub_le`, `sq_eLpNorm_one_labelMean_sub_le`, and
  `Gain.l1Term_average_sq_le`, with `sum_tsum_sq_l1Term_averagedMin_le` for the sum over the blocks.
* Equation `eq:rewardmoment` for `F_m` by stationarity, and the sum over `G`:
  `Gain.tsum_esTerm_translatedMin_eq`, `Gain.tsum_esTerm_averagedMin_le`.

The tube is that of `F`, and the block moves: the translation of `F_v` to `F` maps `G` to the block
`g − v e₂`. The bound for `F` is the instance of equation `eq:rewardmoment` for the resampling with
`σ_G` constant, the independent replacement `Responses.isSlabReplacement_pair`
(`lintegral_pairNew_eq`). The first bound of equation `eq:rewardmoment` is not used. Equation
`eq:scales` places the pairs of a chain among the retained pairs, since `R_i` vanishes on the others
(`row_width_small_of_scales`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper

variable {m : ℕ}

/-! ### The norms on the joint law -/

/-- The `L²` norm in `[0, ∞]`. As `IsotropicVariance.Paper.Proofs.Gain.Poincare.eLpNorm_two_sq`
in the continuum library. -/
theorem sq_eLpNorm_two_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    eLpNorm f 2 P ^ 2 = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num) hf
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  simpa only [Infra.EfronStein.enorm_sub_sq_eq_ofReal] using h

/-- The `L¹` norm in `[0, ∞]`. As `IsotropicVariance.Paper.Proofs.Gain.Poincare.eLpNorm_one_eq`
in the continuum library. -/
theorem eLpNorm_one_eq_ofReal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    eLpNorm f 1 P = ∫⁻ ω, ENNReal.ofReal |f ω| ∂P := by
  rw [eLpNorm_one_eq_lintegral_enorm hf]
  exact lintegral_congr fun ω => Real.enorm_eq_ofReal_abs _

/-- The change of a measurable `Z` under the resampling of `G` is measurable on the joint law. -/
theorem measurable_sub_resample {Z : Config m → ℝ} (hZ : Measurable Z)
    (G : Set (Sym2 (Vertex m))) :
    Measurable fun q : Config m × Config m => Z q.1 - Z (resample G q.1 q.2) :=
  (hZ.comp measurable_fst).sub (hZ.comp (Responses.measurable_resample G))

/-- `E[(Z − Z^G)²]` on the joint law is the Efron–Stein term. -/
theorem sq_eLpNorm_two_sub_resample {P : Measure (Config m)} [SFinite P] {Z : Config m → ℝ}
    (hZ : Measurable Z) (G : Set (Sym2 (Vertex m))) :
    eLpNorm (fun q : Config m × Config m => Z q.1 - Z (resample G q.1 q.2)) 2 (P.prod P) ^ 2 =
      esTerm P Z G := by
  rw [sq_eLpNorm_two_eq _ (measurable_sub_resample hZ G).aestronglyMeasurable, esTerm,
    lintegral_prod _ ((measurable_sub_resample hZ G).pow_const 2).ennreal_ofReal.aemeasurable]

/-- `E[|Z − Z^G|]` on the joint law is the `L¹` term. -/
theorem eLpNorm_one_sub_resample {P : Measure (Config m)} [SFinite P] {Z : Config m → ℝ}
    (hZ : Measurable Z) (G : Set (Sym2 (Vertex m))) :
    eLpNorm (fun q : Config m × Config m => Z q.1 - Z (resample G q.1 q.2)) 1 (P.prod P) =
      l1Term P Z G := by
  have hm : Measurable fun q : Config m × Config m =>
      ENNReal.ofReal |Z q.1 - Z (resample G q.1 q.2)| :=
    (continuous_abs.measurable.comp (measurable_sub_resample hZ G)).ennreal_ofReal
  rw [eLpNorm_one_eq_ofReal _ (measurable_sub_resample hZ G).aestronglyMeasurable, l1Term,
    lintegral_prod _ hm.aemeasurable]

/-! ### Jensen's inequality -/

variable {n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ} {β : Type*}
  {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β} {M : Model m}

/-- **The first bound of the last display of the proof of [AB26, Lemma 6.4]**:
`E[(f − E_G[f])²] ≤ E[(Z − Z^G)²]`, with `f = E[Z | (X_H)_H]`. For `Z = F̄`, the bound by the
average over `m` is `Gain.esTerm_averagedMin_le`. -/
theorem IsOffsetLabels.sq_eLpNorm_two_labelMean_sub_le (hM : M.Standing)
    (h : IsOffsetLabels n w L K t o lam) {i : ℕ} (hi : i < K) (g : Fin m → ℤ) {Z : Config m → ℝ}
    (hZm : Measurable Z) (hZ : Integrable Z M.P) :
    eLpNorm (labelMean M.P Z K o lam -
        integrateLabel M.P (labelMean M.P Z K o lam) K o lam i g) 2 M.P ^ 2 ≤
      esTerm M.P Z (block n w L t (i + 1) (o (i + 1)) g) := by
  have := hM.probP
  rw [← sq_eLpNorm_two_sub_resample hZm]
  exact pow_le_pow_left' (h.eLpNorm_labelMean_sub_le hM hi g hZ one_le_two) 2

/-- **The second bound of the last display of the proof of [AB26, Lemma 6.4], before the
Cauchy–Schwarz inequality**: `E[|f − E_G[f]|]² ≤ E[|Z − Z^G|]²`, with `f = E[Z | (X_H)_H]`. -/
theorem IsOffsetLabels.sq_eLpNorm_one_labelMean_sub_le (hM : M.Standing)
    (h : IsOffsetLabels n w L K t o lam) {i : ℕ} (hi : i < K) (g : Fin m → ℤ) {Z : Config m → ℝ}
    (hZm : Measurable Z) (hZ : Integrable Z M.P) :
    eLpNorm (labelMean M.P Z K o lam -
        integrateLabel M.P (labelMean M.P Z K o lam) K o lam i g) 1 M.P ^ 2 ≤
      l1Term M.P Z (block n w L t (i + 1) (o (i + 1)) g) ^ 2 := by
  have := hM.probP
  rw [← eLpNorm_one_sub_resample hZm]
  exact pow_le_pow_left' (h.eLpNorm_labelMean_sub_le hM hi g hZ le_rfl) 2

/-! ### Equation `eq:rewardmoment` for the resampling with `σ_G` constant -/

/-- The term of the block `(i, g)` of `IsSlabReplacement` for the independent resampling is the
Efron–Stein term. -/
theorem lintegral_pairNew_eq (hM : M.Standing) (X : Config m → ℝ) (hX : Measurable X) (n w L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (o : ℕ → Fin m → ℤ) (i : ℕ) (g : Fin m → ℤ) :
    ∫⁻ ω, ENNReal.ofReal ((X (Responses.pairNew n w L t o i g ω) - X (Responses.pairOld ω)) ^ 2)
        ∂Responses.pairLaw M.F = esTerm M.P X (block n w L t i (o i) g) := by
  have := hM.probF
  have := hM.probP
  set G := block n w L t i (o i) g
  have hpair := Responses.measurePreserving_pairFields hM.iid
  have hm : Measurable fun p : Config m × Config m =>
      ENNReal.ofReal ((X p.1 - X (resample G p.1 p.2)) ^ 2) :=
    ((measurable_sub_resample hX G).pow_const 2).ennreal_ofReal
  have hx := hpair.lintegral_comp hm
  rw [lintegral_prod _ hm.aemeasurable] at hx
  rw [esTerm, ← hx]
  refine lintegral_congr fun ω => ?_
  rw [sub_sq_comm]
  rfl

/-! ### The tubes -/

/-- **The pairs of a chain are retained**, for `N` large, from equation `eq:scales`: `R_i` vanishes
off the retained pairs, so the count of the translates needs this. The width margin is
`Moments.exists_width_margin`. -/
theorem row_width_small_of_scales (hS : Contracts.ScalesStatement m) (bd : Bounds m)
    (hbd : bd.Valid) (Cstar : ℝ) :
    ∃ N₀ : ℕ, ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N →
      ∀ A : ℝ, 1 ≤ A → RangeA M K A N Cstar → ∀ n : ℕ, Real.sqrt N ≤ n →
        32 * Real.sqrt m * ((wInt M K A n : ℝ) + 1) ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hbd.law.one_le_m)
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have ha : 0 < (3 : ℝ) / 4 + bd.law.δ / 100 := by have hδ := hbd.law.delta_pos; linarith only [hδ]
  obtain ⟨Nwidth, hwidth⟩ := Moments.exists_width_margin hS bd hbd Cstar
    (η := 1 / (128 * Real.sqrt m)) (by positivity)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      128 * Real.sqrt m ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + bd.law.δ / 100) :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (128 * Real.sqrt m))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max Nwidth (n₀ ^ 2), ?_⟩
  intro K hK M hM hfit N hN A hA hRange n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) ^ 2 := (Real.sqrt_le_iff.mp hn).2
  have hn0N : (n₀ : ℝ) ^ 2 ≤ N := by exact_mod_cast ((le_max_right _ _).trans hN)
  have hn0n : n₀ ≤ n := by
    have hnr : (n₀ : ℝ) ≤ n := by
      nlinarith only [hNn, hn0N, Nat.cast_nonneg (α := ℝ) n₀, Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast hnr
  have hp := hn₀ n hn0n
  rw [← hfit.δ_eq] at hp
  have hw := hwidth K hK M hM hfit N ((le_max_left _ _).trans hN) A hA hRange n
    ((div_le_self (Real.sqrt_nonneg _) (by norm_num : (1 : ℝ) ≤ 16)).trans hn)
  have hmul := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 32 * Real.sqrt m)
  have heq : 32 * Real.sqrt m * (1 / (128 * Real.sqrt m) *
      (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) =
      (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 4 := by field_simp; ring
  rw [heq] at hmul
  have hceil := (Nat.ceil_lt_add_one (Real.sqrt_nonneg ((n : ℝ) * Q M K A n))).le
  change (wInt M K A n : ℝ) ≤ W M K A n + 1 at hceil
  nlinarith only [hmul, hceil, hp, hsqrt.le]

/-- **The second bound over the blocks** (the second paragraph of the proof of [AB26, Lemma 6.4]):
the Cauchy–Schwarz inequality for the joint law of `m` and the weights
(`Gain.l1Term_average_sq_le`), the probability that `G` meets either tube of `F_m`
(`Gain.sum_measure_allTubesMeet_le`), and the sum over `G` by stationarity
(`Gain.tsum_average_esTerm_translatedMin_eq`), with the sums of `h1` and `h2` as hypotheses, and the
Efron–Stein sum of `F` kept on the right. -/
theorem sum_tsum_sq_l1Term_averagedMin_le (hM : M.Standing) {Cd T : ℝ} (hT : TubeBound M Cd T)
    {K : ℕ} (hK : 1 ≤ K) {A : ℝ} (hA : 1 ≤ A) {L n ℓ : ℕ} (hL : 1 ≤ L) (hn : 1 ≤ n)
    {y : Fin m → ℤ} (ht : ‖targetSlope ℓ y‖ ≤ T) {C : ℝ} (hC : 0 ≤ C)
    (hret : ∀ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y → ∀ i : Fin K,
      IsRetainedPair M n (wInt M K A n)
        (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
        (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ))
    (h1 : ∫⁻ ω, ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
        (_ : IsMinTuple M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y),
        ENNReal.ofReal (∑ i : Fin K, indexJumpSq n (wInt M K A n) (targetSlope ℓ y) Y i) ∂M.P ≤
      ENNReal.ofReal (C * K))
    (h2 : ∫⁻ ω, ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
        (_ : IsMinTuple M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y),
        ∑ i : Fin K, radiusArray M K A Cd ω n (targetSlope ℓ y) ((i : ℕ) + 1)
          (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
          (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ) ^ 2 ∂M.P ≤
      ENNReal.ofReal (C * K))
    (o : ℕ → Fin m → ℤ) :
    ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        l1Term M.P (fun ω => averagedMin M K A L ω n ℓ y)
          (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) ^ 2 ≤
      ENNReal.ofReal (6 * (1 + Real.sqrt C) * (K : ℝ) ^ (-(1 : ℝ) / 6)) *
        ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y)
          (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) := by
  have := hM.probP
  have hw : 1 ≤ wInt M K A n := Responses.one_le_wInt hA hn
  by_cases hadm : ∃ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y
  swap
  · push Not at hadm
    have hl : ∀ G, l1Term M.P (fun ω => averagedMin M K A L ω n ℓ y) G = 0 := by
      intro G
      simp [l1Term, averagedMin_eq_zero_of_forall_not hadm]
    simp [hl]
  have hV := numTranslates_pos hK
  set β : ℝ≥0∞ := ENNReal.ofReal (6 * (1 + Real.sqrt C) * (K : ℝ) ^ (-(1 : ℝ) / 6)) with hβ
  -- each block
  have key : ∀ i ∈ Finset.range K, ∀ g : Fin m → ℤ,
      l1Term M.P (fun ω => averagedMin M K A L ω n ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) ^ 2 ≤
      ((numTranslates K : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range (numTranslates K),
        esTerm M.P (fun ω => translatedMin M ω n K ℓ y
          (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
          (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g)) * β := by
    intro i hi g
    set i' : Fin K := ⟨i, Finset.mem_range.1 hi⟩
    have hCS := l1Term_average_sq_le (P := M.P) (fun v ω => translatedMin M ω n K ℓ y
        (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
      (fun v => measurable_translatedMin M n K ℓ y _) hV
      (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g)
    refine hCS.trans ?_
    gcongr
    have hpv : ∀ v ∈ Finset.range (numTranslates K),
        (M.P.prod M.P) {p : Config m × Config m |
          translatedMin M p.1 n K ℓ y (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m) ≠
            translatedMin M (resample (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1)
              (o (i + 1)) g) p.1 p.2) n K ℓ y
              (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m)} ≤
          2 * M.P {z : Config m | AllTubesMeet M K A Cd n ℓ y L i' (o (i + 1))
            (g - (v : ℤ) • transverseUnit m) z} := by
      intro v _
      rw [measure_translatedMin_ne_eq hM hw ℓ y (i + 1) v (o (i + 1)) g]
      exact measure_targetMin_ne_le hM hT hA hn ht i' (o (i + 1))
        (g - (v : ℤ) • transverseUnit m)
    have hcount := sum_measure_allTubesMeet_le hM hL hC hadm hret h1 h2 i' (o (i + 1)) g
      (numTranslates K)
    calc (numTranslates K : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range (numTranslates K),
          (M.P.prod M.P) {p : Config m × Config m |
            translatedMin M p.1 n K ℓ y (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m) ≠
              translatedMin M (resample (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1)
                (o (i + 1)) g) p.1 p.2) n K ℓ y
                (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m)}
        ≤ (numTranslates K : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range (numTranslates K),
          2 * M.P {z : Config m | AllTubesMeet M K A Cd n ℓ y L i' (o (i + 1))
            (g - (v : ℤ) • transverseUnit m) z} := by
          gcongr with v hv
          exact hpv v hv
      _ = (numTranslates K : ℝ≥0∞)⁻¹ * (2 * ∑ v ∈ Finset.range (numTranslates K),
          M.P {z : Config m | AllTubesMeet M K A Cd n ℓ y L i' (o (i + 1))
            (g - (v : ℤ) • transverseUnit m) z}) := by rw [← Finset.mul_sum]
      _ ≤ (numTranslates K : ℝ≥0∞)⁻¹ * (2 * ENNReal.ofReal (3 + 3 * Real.sqrt (C * K))) := by
          gcongr
      _ ≤ β := inv_numTranslates_mul_le hK hC
  calc ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        l1Term M.P (fun ω => averagedMin M K A L ω n ℓ y)
          (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) ^ 2
      ≤ ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        ((numTranslates K : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range (numTranslates K),
          esTerm M.P (fun ω => translatedMin M ω n K ℓ y
            (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
            (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g)) * β :=
        Finset.sum_le_sum fun i hi => ENNReal.tsum_le_tsum fun g => key i hi g
    _ = β * ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ, esTerm M.P
          (fun ω => targetMin M ω n K ℓ y)
          (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.tsum_mul_right, tsum_average_esTerm_translatedMin_eq hM hK
          (lt_of_lt_of_le Nat.zero_lt_one hw) ℓ y (i + 1) (o (i + 1)), mul_comm]

/-! ### Lemma `lem:fewtranslates` -/

/-- **The two bounds of Lemma `lem:fewtranslates` at one target**: from equation `eq:rewardmoment`
for `F` and the bound of the `L¹` terms of `F̄`, for every family of labels. -/
theorem IsOffsetLabels.fewTranslates_bounds (hM : M.Standing) {K : ℕ} (hK : 1 ≤ K) {A : ℝ}
    {L n ℓ : ℕ} (hn : 2 ≤ n) (hw : 0 < wInt M K A n) {y : Fin m → ℤ} {o : ℕ → Fin m → ℤ}
    {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β}
    (h : IsOffsetLabels n (wInt M K A n) L K (targetSlope ℓ y) o lam) {a b : ℝ≥0∞}
    (hS : ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y)
      (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) ≤ a)
    (h1 : ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
      l1Term M.P (fun ω => averagedMin M K A L ω n ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) ^ 2 ≤ b) :
    (∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        eLpNorm (labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam -
          integrateLabel M.P
            (labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam) K o lam i g)
          2 M.P ^ 2 ≤ a) ∧
    ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        eLpNorm (labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam -
          integrateLabel M.P
            (labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam) K o lam i g)
          1 M.P ^ 2 ≤ b := by
  have := hM.probP
  have hZm := measurable_averagedMin M K A L n ℓ y
  have hZ : Integrable (fun ω => averagedMin M K A L ω n ℓ y) M.P :=
    (memLp_averagedMin hM hn K A L ℓ y).integrable one_le_two
  refine ⟨le_trans (Finset.sum_le_sum fun i hi => ENNReal.tsum_le_tsum fun g => ?_)
    ((sum_tsum_esTerm_averagedMin_le hM hK hw ℓ y o).trans hS),
    le_trans (Finset.sum_le_sum fun i hi => ENNReal.tsum_le_tsum fun g => ?_) h1⟩
  · exact h.sq_eLpNorm_two_labelMean_sub_le hM (Finset.mem_range.1 hi) g hZm hZ
  · exact h.sq_eLpNorm_one_labelMean_sub_le hM (Finset.mem_range.1 hi) g hZm hZ

/-- **Lemma `lem:fewtranslates`**, the proof of [AB26, Lemma 6.4] with the changes of the paper,
from the second bound of equation `eq:rewardmoment` for [AB26, (6.2)], equations `eq:rowenergy` and
`eq:radiusenergy`, the tube property, and equation `eq:scales`. The first bound of equation
`eq:rewardmoment`, a premise of the edge, is not used: [AB26, Lemma 6.4] uses only the second. The
constant is `C = C_B (1 + 6 (1 + √(C_E + C_R)))`. -/
theorem fewTranslatesStatement_of (_hRM : Contracts.RewardMomentStatement.{0} m)
    (hB : Contracts.BlockReplacementStatement.{0} m) (hE : Contracts.ExpArrayStatement m)
    (hRad : Contracts.RadiusEnergyStatement m) (hS : Contracts.ScalesStatement m)
    (hT : Contracts.TubeStatement m) : Contracts.FewTranslatesStatement m := by
  intro bd hbd Cstar
  obtain ⟨Cd, hCd, hTube⟩ := exists_tubeBound hT (T := bd.T + 1) (by linarith [hbd.T_nonneg])
  obtain ⟨CB, hCB, HB⟩ := hB bd hbd Cstar
  obtain ⟨CE, hCE, HE⟩ := Contracts.response_energy_of hE bd hbd Cstar
  obtain ⟨CR, hCR, HR⟩ := hRad bd hbd Cstar Cd hCd
  obtain ⟨Nw, hNw⟩ := row_width_small_of_scales hS bd hbd Cstar
  set C₁ : ℝ := CE + CR with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨CB * (1 + 6 * (1 + Real.sqrt C₁)), by positivity, fun K hK L hL => ?_⟩
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
  have hL1 : 1 ≤ L := by omega
  obtain ⟨N₁, hN₁⟩ := HB K hK
  obtain ⟨N₂, hN₂⟩ := HE K hK
  obtain ⟨N₃, hN₃⟩ := HR K hK
  refine ⟨max (max N₁ N₂) (max (max N₃ Nw) ((9 * K) ^ 2)),
    fun M hM hfit N hN A hA hP hRA n ℓ y ht o ho lam hlam => ?_⟩
  have := hM.probP
  have := hM.probF
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N₃ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN4 : Nw ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hN
  have hN5 : (9 * K) ^ 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hn2, hsqrt, -, hℓ1⟩ := Responses.target_size_bounds hK1 hN5 ht
  have hn1 : 1 ≤ n := by omega
  have hnorm : ‖targetSlope ℓ y‖ ≤ bd.T + 1 := by
    have h := Responses.targetSlope_norm_le_base_add_one hM hℓ1 ht.2.2.2
    linarith only [h, hfit.t₀_le]
  have hw : 1 ≤ wInt M K A n := Responses.one_le_wInt hA hn1
  have hsmall := hNw K hK M hM hfit N hN4 A hA hRA n hsqrt
  have hret : ∀ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y → ∀ i : Fin K,
      IsRetainedPair M n (wInt M K A n)
        (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
        (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ) :=
    fun Y hY i => isRetainedPair_tupleIndex hY hw hsmall i
  -- the second bound of equation `eq:rewardmoment` for `σ_G` constant
  have hFm := Responses.measurable_targetMin M n K ℓ y
  have hES : ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y)
      (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) ≤
      ENNReal.ofReal (CB * K * Q M K A n ^ 2) := by
    have h := hN₁ M hM hfit N hN1 A hA hP hRA n ℓ y ht L hL1 o ho (Responses.PairWeights m)
      (Responses.pairLaw M.F) Responses.pairOld
      (Responses.pairNew n (wInt M K A n) L (targetSlope ℓ y) o)
      (Responses.isSlabReplacement_pair hM n K (wInt M K A n) L (targetSlope ℓ y) o)
    have e : ∀ (i : ℕ) (g : Fin m → ℤ), ∫⁻ ω, ENNReal.ofReal ((targetMin M
        (Responses.pairNew n (wInt M K A n) L (targetSlope ℓ y) o (i + 1) g ω) n K ℓ y -
          targetMin M (Responses.pairOld ω) n K ℓ y) ^ 2) ∂Responses.pairLaw M.F =
        esTerm M.P (fun ω => targetMin M ω n K ℓ y)
          (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) := fun i g =>
      lintegral_pairNew_eq hM (fun ω => targetMin M ω n K ℓ y) hFm n (wInt M K A n) L
        (targetSlope ℓ y) o (i + 1) g
    simpa only [e] using h
  -- equations `eq:rowenergy` and `eq:radiusenergy`
  have hle : ∀ x : ℝ, x ≤ C₁ → x * K ≤ C₁ * K := fun x hx =>
    mul_le_mul_of_nonneg_right hx hKr.le
  have h1 := (hN₂ M hM hfit N hN2 A hA hP hRA n ℓ y ht).trans
    (ENNReal.ofReal_le_ofReal (hle CE (by linarith only [hCR, hC₁])))
  have h2 := (hN₃ M hM hfit N hN3 A hA hP hRA n ℓ y ht).trans
    (ENNReal.ofReal_le_ofReal (hle CR (by linarith only [hCE, hC₁])))
  have hL₁ := sum_tsum_sq_l1Term_averagedMin_le (L := L) hM (hTube M) hK1 hA hL1 hn1 hnorm
    hC₁0.le hret h1 h2 o
  -- the arithmetic of the constants
  have hQ2 : 0 ≤ (K : ℝ) * Q M K A n ^ 2 := by positivity
  have hpow : 0 ≤ (K : ℝ) ^ (-(1 : ℝ) / 6) := Real.rpow_nonneg hKr.le _
  have hs0 := Real.sqrt_nonneg C₁
  have hb : ENNReal.ofReal (6 * (1 + Real.sqrt C₁) * (K : ℝ) ^ (-(1 : ℝ) / 6)) *
      ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) ≤
      ENNReal.ofReal (CB * (1 + 6 * (1 + Real.sqrt C₁)) * (K : ℝ) ^ (-(1 : ℝ) / 6) *
        (K * Q M K A n ^ 2)) := by
    refine (mul_le_mul' le_rfl hES).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx : 0 ≤ CB * (K : ℝ) ^ (-(1 : ℝ) / 6) * ((K : ℝ) * Q M K A n ^ 2) := by positivity
    nlinarith only [hx]
  refine IsOffsetLabels.fewTranslates_bounds hM hK1 hn2 (lt_of_lt_of_le Nat.zero_lt_one hw) hlam
    (hES.trans (ENNReal.ofReal_le_ofReal ?_)) (hL₁.trans hb)
  have hx : 0 ≤ CB * ((K : ℝ) * Q M K A n ^ 2) := by positivity
  have hy' : 0 ≤ CB * ((K : ℝ) * Q M K A n ^ 2) * (6 * (1 + Real.sqrt C₁)) := by positivity
  nlinarith only [hx, hy']

end CurvatureVariance.Paper.Gain
