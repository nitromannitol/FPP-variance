/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Arrays
public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Infra.Os.Moments
import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Equation `eq:chainsum`

`chainSumStatement`: `ChainSumStatement` (equation `eq:chainsum`) from `ExpArrayStatement`
(equation `eq:rowenergy`) and `ArraysStatement` ([AB26, Lemma 2.4]), as [AB26, (4.7)]. The proof
is that of the continuum library, in the namespace `IsotropicVariance.Paper.Proofs.Profiles`
(`lintegral_sum_selected_le`, `chainSumStatement_of`, and the module `RowEnergyIndex`), adapted:

* the arrays `(Z_i − |j − k|²)₊` are the arrays of [AB26, Lemma 2.4], with their supremum over `k`
  with `k 0 = 0`;
* the rows are the indices `J = tupleIndex …` of a minimizing tuple, and the bound is the supremum
  over all minimizing tuples; the indices satisfy `J 0 = 0` since the tuple starts at `0`;
* the energy of the indices is bounded by equation `eq:rowenergy` directly:
  `c Q_s Σ_i |J_i − J_{i−1}|² ≤ C M Q_s + X`, so it is at most `C M / c + max(X,0)/(c Q_s)`, a
  bound that does not depend on the tuple, so no measurability of the minimizing tuple is needed;
* `E[max(X,0)] ≤ 4 C Q_s` for `X ≤ O₁(C Q_s)`, and the integral is transported along `π`, a
  measure preserving map.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

/-- The squared distance of two transverse points is symmetric. -/
theorem norm_transversePoint_sub_comm (j k : Fin m → ℤ) :
    ‖transversePoint (j - k)‖ = ‖transversePoint (k - j)‖ := by
  rw [Infra.FPP.transversePoint_sub, Infra.FPP.transversePoint_sub, norm_sub_rev]

/-- `∫⁻ (a + b g) ≤ a + b ∫⁻ g` on a probability space. -/
theorem lintegral_ofReal_affine_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {a b : ℝ} (hb : 0 ≤ b) {g : Ω → ℝ} (hg : AEMeasurable g P) :
    ∫⁻ ω, ENNReal.ofReal (a + b * g ω) ∂P ≤
      ENNReal.ofReal a + ENNReal.ofReal b * ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
  calc ∫⁻ ω, ENNReal.ofReal (a + b * g ω) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal a + ENNReal.ofReal b * ENNReal.ofReal (g ω)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul hb]
        exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal a + ENNReal.ofReal b * ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul'' _ hg.ennreal_ofReal,
          lintegral_const, measure_univ, mul_one]

/-- The index of the first cube of a tuple that starts at `0` is `0`. -/
theorem tupleIndex_zero (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) {K : ℕ}
    (y : Fin (K + 1) → Fin m → ℤ) (hy : y 0 = 0) : tupleIndex n w t y 0 = 0 := by
  funext k
  simp [tupleIndex, rowIndex, hy]

/-- **Equation `eq:chainsum`**, from equation `eq:rowenergy` and [AB26, Lemma 2.4]. -/
theorem chainSumStatement (hE : Contracts.ExpArrayStatement m)
    (hA : Contracts.ArraysStatement.{u} m) : Contracts.ChainSumStatement.{u} m := by
  intro bd hbd Cstar
  obtain ⟨c, C, hc, hC, H⟩ := hE bd hbd Cstar
  obtain ⟨C₄, hC₄, H₄⟩ := hA
  refine ⟨C₄ + 10 * C / c, by positivity, fun K hK => ?_⟩
  obtain ⟨N₀, HN⟩ := H K hK
  refine ⟨max N₀ 1, fun Mo hMo hfit N hN A hA' hPrem hRange Ms s hMs hs hMsN z hz
    Ω _ Pr _ π hπ Z hZm hind hmom => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨X, hX, hae⟩ := HN Mo hMo hfit N hN0 A hA' hPrem hRange Ms s hMs hs hMsN z hz
  have hs1 : (1 : ℝ) ≤ s := by
    have : (1 : ℝ) ≤ Real.sqrt N := by
      rw [Real.one_le_sqrt]; exact_mod_cast hN1
    linarith
  have hQ := Proofs.ShortLengths.one_le_Q hMo hK hA' hs1
  have hQ0 : 0 < Q Mo K A s := by linarith
  set p := 4 * (m + 1) with hp
  have hp0 : p ≠ 0 := by omega
  set Q₀ := Q Mo K A s with hQ₀
  set w := wInt Mo K A s
  set t := targetSlope (Ms * s) z
  -- the arrays `(Z_i − |j − k|²)₊` of [AB26, Lemma 2.4]
  set c' : Fin Ms → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ := fun i ω j k =>
    Z i ω j k - ENNReal.ofReal (‖transversePoint (j - k)‖ ^ 2) with hc'
  have hc'm : ∀ i j k, Measurable fun ω => c' i ω j k := fun i j k => (hZm i j k).sub_const _
  set z' : Fin Ms → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ := fun i ω j k => (c' i ω j k).toReal
    with hz'
  have hz'm : ∀ i j k, Measurable fun ω => z' i ω j k :=
    fun i j k => (hc'm i j k).ennreal_toReal
  have hz'0 : ∀ i ω j k, 0 ≤ z' i ω j k := fun _ _ _ _ => ENNReal.toReal_nonneg
  have hz'ind : iIndepFun z' Pr := by
    let g : Fin Ms → ((Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ :=
      fun _ f j k => (f j k - ENNReal.ofReal (‖transversePoint (j - k)‖ ^ 2)).toReal
    have hg : ∀ i, Measurable (g i) := fun _ =>
      Measurable.of_eval fun j => Measurable.of_eval fun k =>
        (((measurable_pi_apply j).eval (a := k)).sub_const _).ennreal_toReal
    exact hind.comp g hg
  have hlint : ∀ i j k, ∫⁻ ω, ENNReal.ofReal (z' i ω j k ^ p) ∂Pr ≤ 1 := fun i j k =>
    (lintegral_mono fun ω => by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
      exact pow_le_pow_left₀ bot_le ENNReal.ofReal_toReal_le p).trans (hmom i j k)
  have hfin : ∀ᵐ ω ∂Pr, ∀ (i : Fin Ms) (j k : Fin m → ℤ), c' i ω j k ≠ ⊤ := by
    refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ?_
    filter_upwards [ae_lt_top ((hc'm i j k).pow_const p)
      ((hmom i j k).trans_lt ENNReal.one_lt_top).ne] with ω hω htop
    rw [htop, ENNReal.top_pow hp0] at hω
    exact lt_irrefl _ hω
  have H4 := H₄ Ms (by omega) Ω Pr z' hz'm hz'0 hz'ind hlint
  set Sup : Ω → ℝ≥0∞ := fun ω => ⨆ (k : Fin (Ms + 1) → Fin m → ℤ) (_ : k 0 = 0),
    ENNReal.ofReal ((∑ i : Fin Ms, z' i ω (k i.castSucc) (k i.succ)) -
      ∑ i : Fin Ms, ‖transversePoint (k i.succ - k i.castSucc)‖ ^ 2) with hSup
  -- the bound for the energy of the indices
  have hXm : AEMeasurable (fun ω => max (X (π ω)) 0) Pr :=
    (hX.1.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving).max aemeasurable_const
  set Pbd : Ω → ℝ := fun ω => C * Ms / c + (c * Q₀)⁻¹ * max (X (π ω)) 0 with hPbd
  have hae' : ∀ᵐ ω ∂Pr, ∀ Y : Fin (Ms + 1) → Fin m → ℤ,
      IsMinTuple Mo (π ω) s Ms t 0 (((Ms * s : ℕ) : ℤ), z) Y →
        ∑ i : Fin Ms, indexJumpSq s w t Y i ≤ Pbd ω := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hae] with ω hω Y hY
    have h1 := hω Y hY
    have h2 := abs_nonneg ((slabMin Mo (π ω) s Ms t 0 (((Ms * s : ℕ) : ℤ), z)).toReal -
      Mo.μ.1 (point (((Ms * s : ℕ) : ℤ), z)))
    have h3 : c * Q₀ * ∑ i : Fin Ms, indexJumpSq s w t Y i ≤
        C * Ms * Q₀ + max (X (π ω)) 0 := by
      have := le_max_left (X (π ω)) 0
      linarith
    simp only [hPbd]
    have hcQ : 0 < c * Q₀ := mul_pos hc hQ0
    have h4 : ∑ i : Fin Ms, indexJumpSq s w t Y i ≤
        (C * Ms * Q₀ + max (X (π ω)) 0) / (c * Q₀) := by
      rw [le_div_iff₀ hcQ]; linarith
    refine h4.trans (le_of_eq ?_)
    field_simp
  have hpt : ∀ᵐ ω ∂Pr,
      (⨆ (Y : Fin (Ms + 1) → Fin m → ℤ)
        (_ : IsMinTuple Mo (π ω) s Ms t 0 (((Ms * s : ℕ) : ℤ), z) Y),
        ∑ i : Fin Ms, Z i ω (tupleIndex s w t Y i.castSucc) (tupleIndex s w t Y i.succ)) ≤
      Sup ω + 2 * ENNReal.ofReal (Pbd ω) := by
    filter_upwards [hfin, hae'] with ω hω hbound
    refine iSup_le fun Y => iSup_le fun hY => ?_
    set J := tupleIndex s w t Y with hJ
    have hJ0 : J 0 = 0 := tupleIndex_zero s w t Y hY.1.1
    set Pen : ℝ := ∑ i : Fin Ms, ‖transversePoint (J i.succ - J i.castSucc)‖ ^ 2 with hPen
    have hPenle : Pen ≤ Pbd ω := hbound Y hY
    have hSup1 : ENNReal.ofReal (∑ i : Fin Ms, (c' i ω (J i.castSucc) (J i.succ)).toReal) ≤
        Sup ω + ENNReal.ofReal Pen := by
      have hle : ENNReal.ofReal ((∑ i : Fin Ms, z' i ω (J i.castSucc) (J i.succ)) - Pen) ≤
          Sup ω := le_iSup₂_of_le J hJ0 le_rfl
      calc ENNReal.ofReal (∑ i : Fin Ms, z' i ω (J i.castSucc) (J i.succ))
          = ENNReal.ofReal ((∑ i : Fin Ms, z' i ω (J i.castSucc) (J i.succ) - Pen) + Pen) := by
            rw [sub_add_cancel]
        _ ≤ ENNReal.ofReal (∑ i : Fin Ms, z' i ω (J i.castSucc) (J i.succ) - Pen) +
              ENNReal.ofReal Pen := ENNReal.ofReal_add_le
        _ ≤ Sup ω + ENNReal.ofReal Pen := by gcongr
    have hterm : ∀ i : Fin Ms, Z i ω (J i.castSucc) (J i.succ) ≤
        c' i ω (J i.castSucc) (J i.succ) +
          ENNReal.ofReal (‖transversePoint (J i.succ - J i.castSucc)‖ ^ 2) := fun i => by
      simp only [hc']
      rw [norm_transversePoint_sub_comm (J i.castSucc)]
      exact le_tsub_add
    calc ∑ i : Fin Ms, Z i ω (J i.castSucc) (J i.succ)
        ≤ ∑ i : Fin Ms, (c' i ω (J i.castSucc) (J i.succ) +
            ENNReal.ofReal (‖transversePoint (J i.succ - J i.castSucc)‖ ^ 2)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ENNReal.ofReal (∑ i : Fin Ms, (c' i ω (J i.castSucc) (J i.succ)).toReal) +
            ENNReal.ofReal Pen := by
          have e₁ : ENNReal.ofReal (∑ i : Fin Ms, (c' i ω (J i.castSucc) (J i.succ)).toReal) =
              ∑ i : Fin Ms, c' i ω (J i.castSucc) (J i.succ) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
            exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_toReal (hω i _ _)
          have e₂ : ENNReal.ofReal Pen =
              ∑ i : Fin Ms, ENNReal.ofReal (‖transversePoint (J i.succ - J i.castSucc)‖ ^ 2) :=
            ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _
          rw [e₁, e₂, Finset.sum_add_distrib]
      _ ≤ (Sup ω + ENNReal.ofReal Pen) + ENNReal.ofReal Pen := by gcongr
      _ ≤ (Sup ω + ENNReal.ofReal (Pbd ω)) + ENNReal.ofReal (Pbd ω) := by
          gcongr
      _ = Sup ω + 2 * ENNReal.ofReal (Pbd ω) := by ring
  -- the integral
  have hPm : AEMeasurable (fun ω => ENNReal.ofReal (Pbd ω)) Pr :=
    (((hXm.const_mul _).const_add _)).ennreal_ofReal
  have hmaxX : ∫⁻ ω, ENNReal.ofReal (max (X (π ω)) 0) ∂Pr ≤ ENNReal.ofReal (4 * (C * Q₀)) := by
    have hg : AEMeasurable (fun ω : Config m => ENNReal.ofReal (max (X ω) 0)) (Measure.map π Pr) := by
      rw [hπ.map_eq]
      exact (hX.1.max aemeasurable_const).ennreal_ofReal
    have h' := lintegral_map' hg hπ.aemeasurable
    rw [hπ.map_eq] at h'
    have hU := hX.lintegral_pos_rpow_le one_pos (by positivity : 0 < C * Q₀) zero_le_one
    simp only [Real.rpow_one] at hU
    have e4 : 2 * (1 + ((Nat.ceil ((1 : ℝ) / 1)).factorial : ℝ)) * (C * Q₀) = 4 * (C * Q₀) := by
      norm_num
    rw [e4] at hU
    exact h'.symm.trans_le hU
  calc ∫⁻ ω, (⨆ (Y : Fin (Ms + 1) → Fin m → ℤ)
        (_ : IsMinTuple Mo (π ω) s Ms t 0 (((Ms * s : ℕ) : ℤ), z) Y),
        ∑ i : Fin Ms, Z i ω (tupleIndex s w t Y i.castSucc) (tupleIndex s w t Y i.succ)) ∂Pr
      ≤ ∫⁻ ω, (Sup ω + 2 * ENNReal.ofReal (Pbd ω)) ∂Pr := lintegral_mono_ae hpt
    _ = ∫⁻ ω, Sup ω ∂Pr + 2 * ∫⁻ ω, ENNReal.ofReal (Pbd ω) ∂Pr := by
        rw [lintegral_add_right' _ (hPm.const_mul _), lintegral_const_mul'' _ hPm]
    _ ≤ ENNReal.ofReal (C₄ * Ms) + 2 * (ENNReal.ofReal (C * Ms / c) +
          ENNReal.ofReal (c * Q₀)⁻¹ * ENNReal.ofReal (4 * (C * Q₀))) := by
        gcongr
        refine (lintegral_ofReal_affine_le (inv_nonneg.mpr (mul_pos hc hQ0).le) hXm).trans ?_
        gcongr
    _ = ENNReal.ofReal (C₄ * Ms + 2 * (C * Ms / c + (c * Q₀)⁻¹ * (4 * (C * Q₀)))) := by
        have e0 : (0 : ℝ) ≤ C * Ms / c := by positivity
        have e1 : (0 : ℝ) ≤ (c * Q₀)⁻¹ * (4 * (C * Q₀)) := by positivity
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos hc hQ0).le), ← ENNReal.ofReal_add e0 e1,
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((C₄ + 10 * C / c) * Ms) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hMs1 : (1 : ℝ) ≤ Ms := by exact_mod_cast (by omega : 1 ≤ Ms)
        have e : (c * Q₀)⁻¹ * (4 * (C * Q₀)) = 4 * C / c := by field_simp
        rw [e]
        have : 8 * C / c ≤ 8 * C / c * Ms := le_mul_of_one_le_right (by positivity) hMs1
        have e2 : C * Ms / c = C / c * Ms := by ring
        have e3 : 4 * C / c = 4 * (C / c) := by ring
        have e4 : 8 * C / c = 8 * (C / c) := by ring
        have e5 : 10 * C / c = 10 * (C / c) := by ring
        rw [e2, e3]; rw [e4] at this; rw [e5]
        nlinarith [this]

end CurvatureVariance.Paper.Moments
