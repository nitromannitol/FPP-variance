/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.InfluenceDefs
public import CurvatureVariance.Paper.Proofs.Gain.AVAlgebra
public import CurvatureVariance.Paper.Proofs.Gain.RRTuples
public import CurvatureVariance.Paper.Proofs.Responses.Basic
public import CurvatureVariance.Paper.Proofs.Responses.RadiusArrays
import CurvatureVariance.Infra.Os.Power
import CurvatureVariance.Paper.Proofs.ReplacementResponses.EnergyTransfer

/-!
# The expected number of translates met by the tubes

The proof of Lemma `lem:fewtranslates`: "the cells with indices `z` such that
`dist(z, [J_{i−1}, J_i]) ≤ R_i(J_{i−1}, J_i)` lie in at most
`C(1 + (|J_i − J_{i−1}| + R_i(J_{i−1}, J_i))/L)` of the blocks `G + m'Lwe₂` with `m' ∈ ℤ`, and
equations `eq:rowenergy` and `eq:radiusenergy` bound the squares of these numbers, summed over `i`,
by `CK` in mean". By the Cauchy–Schwarz inequality, each number has mean at most `C√K`, as in the
proof of [AB26, Lemma 6.4].

* `measurableSet_allTubesMeet`: the set where every minimizing tube meets a block is measurable
  (the tuples are countable; `slabRadius` is measurable).
* `sum_measure_allTubesMeet_le`: summed over the translates `g − v e₂`, `0 ≤ v < V`, of a block, the
  probabilities that every minimizing tube meets the translate are at most `3 + 3√(CK)`, for `C`
  bounding the sums of equations `eq:rowenergy` and `eq:radiusenergy`. Pointwise the number of
  translates is at most `3 + |J_{i+1} − J_i| + 2R` (`Gain.card_translates_meet_tube_le`) for any
  minimizing tuple, and each term has `L¹` norm at most `√(CK)` by Jensen.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper

variable {m : ℕ}

/-- Meeting a block is a measurable condition on the weights, for a fixed tuple. -/
theorem measurableSet_tubeMeets (M : Model m) (K : ℕ) (A Cd : ℝ) (n ℓ : ℕ) (y : Fin m → ℤ)
    (L : ℕ) (i : Fin K) (o g : Fin m → ℤ) (Y : Fin (K + 1) → Fin m → ℤ) :
    MeasurableSet {z : Config m | TubeMeets M K A Cd n ℓ y L i o g z Y} := by
  unfold TubeMeets
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun j' => ?_
  rw [Set.ofPred_and]
  exact (MeasurableSet.const _).inter (measurableSet_le measurable_const
    (Responses.measurable_slabRadius M K A Cd n (targetSlope ℓ y) ((i : ℕ) + 1) _ _))

theorem measurableSet_allTubesMeet (M : Model m) (K : ℕ) (A Cd : ℝ) (n ℓ : ℕ) (y : Fin m → ℤ)
    (L : ℕ) (i : Fin K) (o g : Fin m → ℤ) :
    MeasurableSet {z : Config m | AllTubesMeet M K A Cd n ℓ y L i o g z} := by
  unfold AllTubesMeet
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun Y => ?_
  have h : {z : Config m | IsMinTuple M z n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y →
      TubeMeets M K A Cd n ℓ y L i o g z Y} =
      {z | IsMinTuple M z n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y}ᶜ ∪
        {z | TubeMeets M K A Cd n ℓ y L i o g z Y} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  rw [h]
  exact (ReplacementResponses.measurableSet_isMinTuple M n K _ 0 _ Y).compl.union
    (measurableSet_tubeMeets M K A Cd n ℓ y L i o g Y)

/-- A supremum over the minimizing tuples, as a countable supremum of indicators. -/
theorem iSup_isMinTuple_eq_iSup_indicator (M : Model m) (n K : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (u v : Vertex m) (f : Config m → (Fin (K + 1) → Fin m → ℤ) → ℝ≥0∞) (z : Config m) :
    (⨆ (Y : Fin (K + 1) → Fin m → ℤ) (_ : IsMinTuple M z n K t u v Y), f z Y) =
      ⨆ Y : Fin (K + 1) → Fin m → ℤ,
        {z' : Config m | IsMinTuple M z' n K t u v Y}.indicator (fun z' => f z' Y) z := by
  refine iSup_congr fun Y => ?_
  by_cases h : IsMinTuple M z n K t u v Y
  · rw [iSup_pos h, Set.indicator_of_mem (show z ∈ {z' | IsMinTuple M z' n K t u v Y} from h)]
  · rw [iSup_neg h, Set.indicator_of_notMem (show z ∉ {z' | IsMinTuple M z' n K t u v Y} from h),
      bot_eq_zero]

/-- A supremum over the minimizing tuples of measurable functions is measurable. -/
theorem measurable_iSup_isMinTuple (M : Model m) (n K : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (u v : Vertex m) {f : Config m → (Fin (K + 1) → Fin m → ℤ) → ℝ≥0∞}
    (hf : ∀ Y, Measurable fun z => f z Y) :
    Measurable fun z =>
      ⨆ (Y : Fin (K + 1) → Fin m → ℤ) (_ : IsMinTuple M z n K t u v Y), f z Y := by
  simp_rw [iSup_isMinTuple_eq_iSup_indicator M n K t u v f]
  exact Measurable.iSup fun Y => (hf Y).indicator (ReplacementResponses.measurableSet_isMinTuple M n K t u v Y)

/-- `(x²)^{1/2} = x` in `[0, ∞]`. -/
theorem ennreal_sq_rpow_half (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **The expected number of translates met by every minimizing tube** (the proof of Lemma
`lem:fewtranslates`): at most `3 + 3√(CK)`, from equations `eq:rowenergy` and `eq:radiusenergy`. -/
theorem sum_measure_allTubesMeet_le {M : Model m} (hM : M.Standing) {K : ℕ} {A Cd : ℝ}
    {n ℓ : ℕ} {y : Fin m → ℤ} {L : ℕ} (hL : 1 ≤ L) {C : ℝ} (hC : 0 ≤ C)
    (hadm : ∃ Y, IsAdmissibleTuple M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y)
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
    (i : Fin K) (o g : Fin m → ℤ) (V : ℕ) :
    ∑ v ∈ Finset.range V, M.P {z : Config m |
        AllTubesMeet M K A Cd n ℓ y L i o (g - (v : ℤ) • transverseUnit m) z} ≤
      ENNReal.ofReal (3 + 3 * Real.sqrt (C * K)) := by
  classical
  have := hM.probP
  set w := wInt M K A n with hwdef
  set t := targetSlope ℓ y with htdef
  set J : (Fin (K + 1) → Fin m → ℤ) → Fin (K + 1) → Fin m → ℤ := fun Y => tupleIndex n w t Y
    with hJdef
  set S : ℕ → Set (Config m) := fun v =>
    {z | AllTubesMeet M K A Cd n ℓ y L i o (g - (v : ℤ) • transverseUnit m) z} with hSdef
  have hS : ∀ v, MeasurableSet (S v) := fun v =>
    measurableSet_allTubesMeet M K A Cd n ℓ y L i o _
  -- the two suprema of equations `eq:rowenergy` and `eq:radiusenergy`
  set S1 : Config m → ℝ≥0∞ := fun z => ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
    (_ : IsMinTuple M z n K t 0 ((ℓ : ℤ), y) Y),
    ENNReal.ofReal (∑ i : Fin K, indexJumpSq n w t Y i) with hS1def
  set S2 : Config m → ℝ≥0∞ := fun z => ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
    (_ : IsMinTuple M z n K t 0 ((ℓ : ℤ), y) Y),
    ∑ i : Fin K, radiusArray M K A Cd z n t ((i : ℕ) + 1) (J Y i.castSucc) (J Y i.succ) ^ 2
    with hS2def
  have hS1m : Measurable S1 :=
    measurable_iSup_isMinTuple M n K t 0 _ (f := fun _ Y =>
      ENNReal.ofReal (∑ i : Fin K, indexJumpSq n w t Y i)) fun _ => measurable_const
  have hS2m : Measurable S2 :=
    measurable_iSup_isMinTuple M n K t 0 _ (f := fun z Y => ∑ i : Fin K,
      radiusArray M K A Cd z n t ((i : ℕ) + 1) (J Y i.castSucc) (J Y i.succ) ^ 2) fun Y =>
      Finset.measurable_sum _ fun i _ =>
        (Responses.measurable_radiusArray M K A Cd n t _ _ _).pow_const 2
  -- the pointwise count
  have hpt : ∀ z, ∑ v ∈ Finset.range V, (S v).indicator 1 z ≤
      3 + S1 z ^ (1 / 2 : ℝ) + 2 * S2 z ^ (1 / 2 : ℝ) := by
    intro z
    obtain ⟨Y, hY⟩ := Gain.exists_isMinTuple hadm z
    set r := slabRadius M K A Cd z n t ((i : ℕ) + 1) (J Y i.castSucc) (J Y i.succ) with hrdef
    have hcount : ∑ v ∈ Finset.range V, (S v).indicator 1 z ≤
        3 + ENNReal.ofReal ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ + 2 * r := by
      have hsum : ∑ v ∈ Finset.range V, (S v).indicator (1 : Config m → ℝ≥0∞) z =
          (({v ∈ Finset.range V | z ∈ S v}).card : ℝ≥0∞) := by
        simp only [Set.indicator_apply, Pi.one_apply]
        exact Finset.sum_boole _ _
      rw [hsum]
      refine le_trans ?_ (Gain.card_translates_meet_tube_le hM.one_le_m hL o g
        (J Y i.castSucc) (J Y i.succ) r V)
      exact_mod_cast Finset.card_le_card fun v hv => by
        rw [Finset.mem_filter] at hv ⊢
        refine ⟨hv.1, ?_⟩
        obtain ⟨j', hj'b, hj't⟩ := hv.2 Y hY
        exact ⟨j', hj't, fun c => hj'b c⟩
    have hJ : ENNReal.ofReal ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ ≤
        S1 z ^ (1 / 2 : ℝ) := by
      have hx0 : 0 ≤ ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ := norm_nonneg _
      have heq : ENNReal.ofReal ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ =
          ENNReal.ofReal (indexJumpSq n w t Y i) ^ (1 / 2 : ℝ) := by
        rw [indexJumpSq, ENNReal.ofReal_pow hx0, ennreal_sq_rpow_half]
      rw [heq]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_iSup₂ (f := fun Y _ =>
        ENNReal.ofReal (∑ i : Fin K, indexJumpSq n w t Y i)) Y hY)
      exact Finset.single_le_sum (f := fun i => indexJumpSq n w t Y i)
        (fun i' _ => by unfold indexJumpSq; positivity) (Finset.mem_univ i)
    have hR : r ≤ S2 z ^ (1 / 2 : ℝ) := by
      have hra : radiusArray M K A Cd z n t ((i : ℕ) + 1) (J Y i.castSucc) (J Y i.succ) = r := by
        rw [radiusArray]
        exact ite_eq_left_iff.2 fun h => absurd (hret Y hY.1 i) h
      rw [← ennreal_sq_rpow_half r]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      refine le_trans ?_ (le_iSup₂ (f := fun Y _ => ∑ i : Fin K,
        radiusArray M K A Cd z n t ((i : ℕ) + 1) (J Y i.castSucc) (J Y i.succ) ^ 2) Y hY)
      rw [← hra]
      exact Finset.single_le_sum (f := fun i : Fin K =>
        radiusArray M K A Cd z n t ((i : ℕ) + 1) (J Y i.castSucc) (J Y i.succ) ^ 2)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    refine hcount.trans ?_
    gcongr
  -- integrate
  have hsqrt : ∀ {f : Config m → ℝ≥0∞}, Measurable f → ∫⁻ z, f z ∂M.P ≤ ENNReal.ofReal (C * K) →
      ∫⁻ z, f z ^ (1 / 2 : ℝ) ∂M.P ≤ ENNReal.ofReal (Real.sqrt (C * K)) := by
    intro f hf hint
    refine (Infra.Os.lintegral_rpow_le hf.aemeasurable (by norm_num) (by norm_num)).trans ?_
    refine (ENNReal.rpow_le_rpow hint (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]
  have hI1 : ∫⁻ z, S1 z ^ (1 / 2 : ℝ) ∂M.P ≤ ENNReal.ofReal (Real.sqrt (C * K)) := hsqrt hS1m h1
  have hI2 : ∫⁻ z, S2 z ^ (1 / 2 : ℝ) ∂M.P ≤ ENNReal.ofReal (Real.sqrt (C * K)) := hsqrt hS2m h2
  have hmeas1 : Measurable fun z => S1 z ^ (1 / 2 : ℝ) := hS1m.pow_const _
  have hmeas2 : Measurable fun z => S2 z ^ (1 / 2 : ℝ) := hS2m.pow_const _
  calc ∑ v ∈ Finset.range V, M.P (S v)
      = ∫⁻ z, ∑ v ∈ Finset.range V, (S v).indicator 1 z ∂M.P := by
        rw [lintegral_finsetSum _ fun v _ => measurable_one.indicator (hS v)]
        exact Finset.sum_congr rfl fun v _ => (lintegral_indicator_one (hS v)).symm
    _ ≤ ∫⁻ z, 3 + S1 z ^ (1 / 2 : ℝ) + 2 * S2 z ^ (1 / 2 : ℝ) ∂M.P := lintegral_mono hpt
    _ = 3 + ∫⁻ z, S1 z ^ (1 / 2 : ℝ) ∂M.P + 2 * ∫⁻ z, S2 z ^ (1 / 2 : ℝ) ∂M.P := by
        rw [lintegral_add_left (f := fun z => (3 : ℝ≥0∞) + S1 z ^ (1 / 2 : ℝ))
            (measurable_const.add hmeas1),
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hmeas2]
    _ ≤ 3 + ENNReal.ofReal (Real.sqrt (C * K)) + 2 * ENNReal.ofReal (Real.sqrt (C * K)) := by
        gcongr
    _ = ENNReal.ofReal (3 + 3 * Real.sqrt (C * K)) := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]
        ring

end CurvatureVariance.Paper.Gain
