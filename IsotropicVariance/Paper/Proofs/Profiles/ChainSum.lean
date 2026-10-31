/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Arrays.Square
public import IsotropicVariance.Paper.Contracts.Profiles
public import IsotropicVariance.Paper.Contracts.Slab
import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
import IsotropicVariance.Paper.Proofs.BlockReplacement.Inputs
import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry
import IsotropicVariance.Paper.Proofs.Profiles.RowEnergy
import IsotropicVariance.Paper.Proofs.Profiles.RowEnergyIndex
import IsotropicVariance.Paper.Proofs.Responses.SelectedMoments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Equation `eq:chainsum`

Equation `eq:rowenergy` gives `E[Σ_i |k_i − k_{i−1}|²] ≤ CM`, so Lemma
`lem:polynomialarray`, applied to the arrays `(Z_i(j, k) − |j − k|²)₊`, gives
`E[Σ_i Z_i(x_{i−1}, x_i)] ≤ CM`.

* `lintegral_sum_selected_le`: the argument, on a probability space, for rows `J` with `J_0 = 0`
  and a bound of their energy.
* `lintegral_energy_comp`: the energy of the rows of `π ω` is that of the noise, for `π` measure
  preserving.
* `chainSumStatement_of`: equation `eq:chainsum`.
* `ChainSumBound`: equation `eq:chainsum` at given `M`, `s` and `W`, the part of the statement
  that follows them.
* `lintegral_sum_le_of_chainSum`: the use of the proofs of Lemmas `lem:blocks`, `lem:residual` and
  `lem:smallmean`: the bound for the arrays `T_i/λ`, from `E[(T_i − λ|j − k|²)₊^{4d}] ≤ λ^{4d}` on
  a set of pairs containing the pairs of the chain.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Contracts

variable {m : ℕ}

/-- The distance of two indices is symmetric. -/
theorem zNorm_sub_comm (j k : Fin m → ℤ) : zNorm (j - k) = zNorm (k - j) := by
  unfold zNorm
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- The conclusion of Lemma `lem:polynomialarray` with the constant `C`, for `M` arrays on the
probability space `(Ω, P)`. -/
def PenalizedBound (m M : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : ℝ) : Prop :=
  ∀ Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ,
    (∀ i j k, Measurable (fun ω => Z i ω j k)) →
    (∀ i ω j k, 0 ≤ Z i ω j k) →
    iIndepFun Z P →
    (∀ i j k, Integrable (fun ω => Z i ω j k ^ (4 * (m + 1))) P) →
    (∀ i j k, ∫ ω, Z i ω j k ^ (4 * (m + 1)) ∂P ≤ 1) →
    (∫⁻ ω, ⨆ k : Fin M → Fin m → ℤ,
      ENNReal.ofReal ((∑ i : Fin M, Z i ω (Infra.Arrays.pathPt 0 k i) (k i)) -
        ∑ i : Fin M, ∑ j : Fin m,
          ((k i j : ℝ) - (Infra.Arrays.pathPt 0 k i j : ℝ)) ^ 2) ∂P) ≤
      ENNReal.ofReal (C * M)

/-- **`E[Σ_i Z_i(J_{i−1}, J_i)] ≤ C₄M + 2B`**: for arrays `Z_i` in
`[0, ∞]`, independent over `i`, with `E[(Z_i(j, k) − |j − k|²)₊^{4d}] ≤ 1`, and rows `J` with
`J_0 = 0` and `E Σ_i |J_i − J_{i−1}|² ≤ B`, and `C₄` the constant of Lemma `lem:polynomialarray`:
`Σ_i Z_i(J_{i−1}, J_i)` is at most the supremum of the penalized sums of the arrays
`(Z_i − |j − k|²)₊` plus twice the energy of the rows. -/
theorem lintegral_sum_selected_le {M : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C₄ B : ℝ} (hC₄ : 0 ≤ C₄) (hB : 0 ≤ B)
    (hA : PenalizedBound m M P C₄) (Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞)
    (hZm : ∀ i j k, Measurable fun ω => Z i ω j k) (hind : iIndepFun Z P)
    (hmom : ∀ i j k, ∫⁻ ω, (Z i ω j k - ENNReal.ofReal (zNorm (j - k) ^ 2)) ^ (4 * (m + 1)) ∂P ≤ 1)
    (J : Ω → Fin (M + 1) → Fin m → ℤ) (hJ0 : ∀ ω, J ω 0 = 0)
    (hE : ∫⁻ ω, ENNReal.ofReal (∑ i : Fin M, zNorm (J ω i.succ - J ω i.castSucc) ^ 2) ∂P ≤
      ENNReal.ofReal B) :
    ∫⁻ ω, ∑ i : Fin M, Z i ω (J ω i.castSucc) (J ω i.succ) ∂P ≤
      ENNReal.ofReal (C₄ * M + 2 * B) := by
  set p := 4 * (m + 1) with hp
  have hp0 : p ≠ 0 := by omega
  -- the arrays of Lemma `lem:polynomialarray`: `(Z_i − |j − k|²)₊`
  set c : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ := fun i ω j k =>
    Z i ω j k - ENNReal.ofReal (zNorm (j - k) ^ 2) with hc
  have hcm : ∀ i j k, Measurable fun ω => c i ω j k := fun i j k => (hZm i j k).sub_const _
  set z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ := fun i ω j k => (c i ω j k).toReal with hz
  have hzm : ∀ i j k, Measurable fun ω => z i ω j k := fun i j k => (hcm i j k).ennreal_toReal
  have hz0 : ∀ i ω j k, 0 ≤ z i ω j k := fun _ _ _ _ => ENNReal.toReal_nonneg
  have hzind : iIndepFun z P := by
    let g : Fin M → ((Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ :=
      fun _ f j k => (f j k - ENNReal.ofReal (zNorm (j - k) ^ 2)).toReal
    have hg : ∀ i, Measurable (g i) := fun _ =>
      Measurable.of_eval fun j => Measurable.of_eval fun k =>
        (((measurable_pi_apply j).eval (a := k)).sub_const _).ennreal_toReal
    exact hind.comp g hg
  have hlint : ∀ i j k, ∫⁻ ω, ENNReal.ofReal (z i ω j k ^ p) ∂P ≤ 1 := fun i j k =>
    (lintegral_mono fun ω => by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
      exact pow_le_pow_left₀ bot_le ENNReal.ofReal_toReal_le p).trans (hmom i j k)
  have hzint : ∀ i j k, Integrable (fun ω => z i ω j k ^ p) P := fun i j k =>
    ⟨((hzm i j k).pow_const _).aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω =>
        pow_nonneg (hz0 i ω j k) _)]
      exact (hlint i j k).trans_lt ENNReal.one_lt_top⟩
  have hzle : ∀ i j k, ∫ ω, z i ω j k ^ p ∂P ≤ 1 := fun i j k => by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
      pow_nonneg (hz0 i ω j k) _) ((hzm i j k).pow_const _).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      ((hlint i j k).trans_eq ENNReal.ofReal_one.symm)
  have H := hA z hzm hz0 hzind hzint hzle
  set Sup : Ω → ℝ≥0∞ := fun ω => ⨆ k : Fin M → Fin m → ℤ,
    ENNReal.ofReal ((∑ i : Fin M, z i ω (Infra.Arrays.pathPt 0 k i) (k i)) -
      ∑ i : Fin M, ∑ j : Fin m, ((k i j : ℝ) - (Infra.Arrays.pathPt 0 k i j : ℝ)) ^ 2) with hSupdef
  have hSupm : Measurable Sup := Measurable.iSup fun k =>
    ((Finset.measurable_sum _ fun i _ => hzm i _ _).sub measurable_const).ennreal_ofReal
  -- the entries are finite
  have hfin : ∀ᵐ ω ∂P, ∀ (i : Fin M) (j k : Fin m → ℤ), c i ω j k ≠ ⊤ := by
    refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ?_
    filter_upwards [ae_lt_top ((hcm i j k).pow_const p)
      ((hmom i j k).trans_lt ENNReal.one_lt_top).ne] with ω hω htop
    rw [htop, ENNReal.top_pow hp0] at hω
    exact lt_irrefl _ hω
  -- the pointwise bound along the rows
  set Pen : Ω → ℝ := fun ω => ∑ i : Fin M, zNorm (J ω i.succ - J ω i.castSucc) ^ 2 with hPendef
  have hpt : ∀ᵐ ω ∂P, ∑ i : Fin M, Z i ω (J ω i.castSucc) (J ω i.succ) ≤
      Sup ω + 2 * ENNReal.ofReal (Pen ω) := by
    filter_upwards [hfin] with ω hω
    set k : Fin M → Fin m → ℤ := fun i => J ω i.succ with hk
    have hpath : ∀ i : Fin M, Infra.Arrays.pathPt 0 k (i : ℕ) = J ω i.castSucc :=
      fun i => Responses.pathPt_rows (J ω) (hJ0 ω) (Nat.le_of_lt i.2)
    have hsum : ∑ i : Fin M, z i ω (Infra.Arrays.pathPt 0 k i) (k i) =
        ∑ i : Fin M, (c i ω (J ω i.castSucc) (J ω i.succ)).toReal :=
      Finset.sum_congr rfl fun i _ => by rw [hpath i]
    have hpen : ∑ i : Fin M, ∑ j : Fin m,
        ((k i j : ℝ) - (Infra.Arrays.pathPt 0 k i j : ℝ)) ^ 2 = Pen ω := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zNorm_sub_sq, hpath i]
    have hSup : ENNReal.ofReal (∑ i : Fin M, (c i ω (J ω i.castSucc) (J ω i.succ)).toReal) ≤
        Sup ω + ENNReal.ofReal (Pen ω) := by
      rw [← hsum]
      have hle : ENNReal.ofReal ((∑ i : Fin M, z i ω (Infra.Arrays.pathPt 0 k i) (k i)) - Pen ω) ≤
          Sup ω := by
        rw [← hpen]
        exact le_iSup (fun k : Fin M → Fin m → ℤ => ENNReal.ofReal
          ((∑ i : Fin M, z i ω (Infra.Arrays.pathPt 0 k i) (k i)) - ∑ i : Fin M, ∑ j : Fin m,
            ((k i j : ℝ) - (Infra.Arrays.pathPt 0 k i j : ℝ)) ^ 2)) k
      calc ENNReal.ofReal (∑ i : Fin M, z i ω (Infra.Arrays.pathPt 0 k i) (k i))
          = ENNReal.ofReal ((∑ i : Fin M, z i ω (Infra.Arrays.pathPt 0 k i) (k i) - Pen ω) +
              Pen ω) := by rw [sub_add_cancel]
        _ ≤ ENNReal.ofReal (∑ i : Fin M, z i ω (Infra.Arrays.pathPt 0 k i) (k i) - Pen ω) +
              ENNReal.ofReal (Pen ω) := ENNReal.ofReal_add_le
        _ ≤ Sup ω + ENNReal.ofReal (Pen ω) := by gcongr
    have hterm : ∀ i : Fin M, Z i ω (J ω i.castSucc) (J ω i.succ) ≤
        c i ω (J ω i.castSucc) (J ω i.succ) +
          ENNReal.ofReal (zNorm (J ω i.succ - J ω i.castSucc) ^ 2) := fun i => by
      rw [zNorm_sub_comm (J ω i.succ)]
      exact le_tsub_add
    calc ∑ i : Fin M, Z i ω (J ω i.castSucc) (J ω i.succ)
        ≤ ∑ i : Fin M, (c i ω (J ω i.castSucc) (J ω i.succ) +
            ENNReal.ofReal (zNorm (J ω i.succ - J ω i.castSucc) ^ 2)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ENNReal.ofReal (∑ i : Fin M, (c i ω (J ω i.castSucc) (J ω i.succ)).toReal) +
            ENNReal.ofReal (Pen ω) := by
          have e₁ : ENNReal.ofReal (∑ i : Fin M, (c i ω (J ω i.castSucc) (J ω i.succ)).toReal) =
              ∑ i : Fin M, c i ω (J ω i.castSucc) (J ω i.succ) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
            exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_toReal (hω i _ _)
          have e₂ : ENNReal.ofReal (Pen ω) =
              ∑ i : Fin M, ENNReal.ofReal (zNorm (J ω i.succ - J ω i.castSucc) ^ 2) :=
            ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _
          rw [e₁, e₂, Finset.sum_add_distrib]
      _ ≤ (Sup ω + ENNReal.ofReal (Pen ω)) + ENNReal.ofReal (Pen ω) := by gcongr
      _ = Sup ω + 2 * ENNReal.ofReal (Pen ω) := by ring
  calc ∫⁻ ω, ∑ i : Fin M, Z i ω (J ω i.castSucc) (J ω i.succ) ∂P
      ≤ ∫⁻ ω, (Sup ω + 2 * ENNReal.ofReal (Pen ω)) ∂P := lintegral_mono_ae hpt
    _ = ∫⁻ ω, Sup ω ∂P + 2 * ∫⁻ ω, ENNReal.ofReal (Pen ω) ∂P := by
        rw [lintegral_add_left hSupm, lintegral_const_mul' _ _ (by simp)]
    _ ≤ ENNReal.ofReal (C₄ * M) + 2 * ENNReal.ofReal B := by gcongr
    _ = ENNReal.ofReal (C₄ * M + 2 * B) := by
        have e : ENNReal.ofReal (2 * B) = 2 * ENNReal.ofReal B := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        rw [ENNReal.ofReal_add (by positivity) (by positivity), e]

/-- The energy of the indices is almost everywhere measurable. -/
theorem aemeasurable_energy (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {s : ℝ}
    (hs : 0 < s) (M : ℕ) (W : ℝ) :
    AEMeasurable (fun ω => ENNReal.ofReal (∑ i : Fin M,
      zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2)) X.P :=
  (Finset.aemeasurable_fun_sum _ fun i _ =>
    aemeasurable_zNorm_sub_sq (Infra.Slab.aemeasurable_J X hb hs 0 M W i.succ)
      (Infra.Slab.aemeasurable_J X hb hs 0 M W i.castSucc)).ennreal_ofReal

/-- The energy of the indices of `π ω` is that of the noise, for `π` measure preserving. -/
theorem lintegral_energy_comp (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {s : ℝ}
    (hs : 0 < s) (M : ℕ) (W : ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {π : Ω' → X.Ω} (hπ : MeasurePreserving π P' X.P) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin M, zNorm (X.J b M s W 0 (π ω) i.succ -
      X.J b M s W 0 (π ω) i.castSucc) ^ 2) ∂P' =
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin M,
        zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2) ∂X.P := by
  have hg := aemeasurable_energy X hb hs M W
  have h' := lintegral_map' (μ := P') (g := π) (hπ.map_eq.symm ▸ hg) hπ.aemeasurable
  rw [hπ.map_eq] at h'
  exact h'.symm

/-- **Equation `eq:chainsum`**, from equation `eq:rowenergy` and Lemma `lem:polynomialarray`. -/
theorem chainSumStatement_of (hR : RowEnergyStatement.{u}) (hA : PenalizedArraysStatement.{u}) :
    ChainSumStatement.{u} := by
  intro m hm X hX b hb Cstar hC
  obtain ⟨CR, hCR, HR⟩ := rowEnergyIndexStatement_of_rowEnergy hR m hm X hX b hb Cstar hC
  obtain ⟨C₄, hC₄, H₄⟩ := hA m
  refine ⟨C₄ + 10 * CR, by positivity, fun c₁ hc₁ K => ?_⟩
  obtain ⟨N₀, HN⟩ := HR c₁ hc₁ K
  refine ⟨N₀, fun A N hN hS M s hM hs₁ hs₂ Ω' _ P' _ π hπ Z hZm hind hmom => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hs : 0 < s := lt_of_lt_of_le (mul_pos hc₁ (by linarith only [hS.2.2.1])) hs₁
  have hQ : 0 < Q K A s := Q_pos (by linarith only [hS.2.1]) hs
  have hE := BlockReplacement.lintegral_rowEnergy_le X hQ hCR (HN A N hN hS M s hM hs₁ hs₂)
  rw [← lintegral_energy_comp X hb hs M (W K A s) hπ] at hE
  refine (lintegral_sum_selected_le hC₄.le (by positivity) (fun z => H₄ M Ω' P' z) Z hZm hind hmom
    (fun ω => X.J b M s (W K A s) 0 (π ω)) (fun ω => J_zero X b M hs.le _ (π ω)) hE).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hCRM : CR ≤ CR * M := le_mul_of_one_le_right hCR.le hM1
  have e : (C₄ + 10 * CR) * M = C₄ * M + 10 * (CR * M) := by ring
  rw [e]
  linarith only [hCRM]

/-- **Equation `eq:chainsum` at given `M`, `s` and `W`**: the part of `ChainSumStatement` that
follows them, with `W = W K A s`. -/
def ChainSumBound (X : Setting.{u} m) (b : ℝ) (M : ℕ) (s W C : ℝ) : Prop :=
  ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (π : Ω' → X.Ω), MeasurePreserving π P' X.P →
    ∀ Z : Fin M → Ω' → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞,
      (∀ i j k, Measurable fun ω => Z i ω j k) →
      iIndepFun Z P' →
      (∀ i j k, ∫⁻ ω, (Z i ω j k - ENNReal.ofReal (zNorm (j - k) ^ 2)) ^ (4 * (m + 1)) ∂P' ≤ 1) →
      ∫⁻ ω, ∑ i : Fin M, Z i ω (X.J b M s W 0 (π ω) i.castSucc)
          (X.J b M s W 0 (π ω) i.succ) ∂P' ≤
        ENNReal.ofReal (C * M)

/-- **Equation `eq:chainsum`, applied to the arrays `T_i/λ`** (as in the proofs of Lemmas
`lem:blocks`, `lem:residual` and `lem:smallmean`): for arrays `T_i` in `[0, ∞]`, independent over
`i`, with `E[(T_i(j, k) − λ|j − k|²)₊^{4d}] ≤ λ^{4d}` on a set `D` of pairs containing the pairs of
the chain, `E[Σ_i T_i(x_{i−1}, x_i)] ≤ λCM`. The arrays of equation `eq:chainsum` are set to zero
off `D`. -/
theorem lintegral_sum_le_of_chainSum {X : Setting.{u} m} {b : ℝ} {M : ℕ} {s W C lam : ℝ}
    (hC : ChainSumBound X b M s W C) {Ω' : Type u} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {π : Ω' → X.Ω} (hπ : MeasurePreserving π P' X.P) (hlam : 0 < lam)
    (T : Fin M → Ω' → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞)
    (hTm : ∀ i j k, Measurable fun ω => T i ω j k) (hind : iIndepFun T P')
    (D : Set ((Fin m → ℤ) × (Fin m → ℤ)))
    (hmom : ∀ i j k, (j, k) ∈ D →
      ∫⁻ ω, (T i ω j k - ENNReal.ofReal (lam * zNorm (j - k) ^ 2)) ^ (4 * (m + 1)) ∂P' ≤
        ENNReal.ofReal (lam ^ (4 * (m + 1))))
    (hJD : ∀ ω (i : Fin M), (X.J b M s W 0 (π ω) i.castSucc, X.J b M s W 0 (π ω) i.succ) ∈ D) :
    ∫⁻ ω, ∑ i : Fin M, T i ω (X.J b M s W 0 (π ω) i.castSucc)
        (X.J b M s W 0 (π ω) i.succ) ∂P' ≤
      ENNReal.ofReal (lam * (C * M)) := by
  classical
  set p := 4 * (m + 1) with hp
  have hp0 : p ≠ 0 := by omega
  have hlam1 : ENNReal.ofReal lam⁻¹ * ENNReal.ofReal lam = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le), inv_mul_cancel₀ hlam.ne', ENNReal.ofReal_one]
  have hlam2 : ENNReal.ofReal lam * ENNReal.ofReal lam⁻¹ = 1 := by rw [mul_comm, hlam1]
  set Z : Fin M → Ω' → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ := fun i ω j k =>
    if (j, k) ∈ D then ENNReal.ofReal lam⁻¹ * T i ω j k else 0 with hZ
  have hZm : ∀ i j k, Measurable fun ω => Z i ω j k := fun i j k => by
    by_cases h : (j, k) ∈ D
    · simpa only [hZ, h, ite_true] using (hTm i j k).const_mul (ENNReal.ofReal lam⁻¹)
    · simp only [hZ, h, ite_false]
      exact measurable_const
  have hZind : iIndepFun Z P' := by
    let g : Fin M → ((Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ :=
      fun _ f j k => if (j, k) ∈ D then ENNReal.ofReal lam⁻¹ * f j k else 0
    have hg : ∀ i, Measurable (g i) := fun _ =>
      measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k => by
        by_cases h : (j, k) ∈ D
        · simp only [g, h, ite_true]
          have hev : Measurable fun f : (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ => f j k :=
            (measurable_pi_apply k).comp (measurable_pi_apply j)
          exact hev.const_mul _
        · simp only [g, h, ite_false]
          exact measurable_const
    exact hind.comp g hg
  have hZmom : ∀ i j k, ∫⁻ ω, (Z i ω j k - ENNReal.ofReal (zNorm (j - k) ^ 2)) ^ p ∂P' ≤ 1 := by
    intro i j k
    by_cases h : (j, k) ∈ D
    · have hpt : ∀ ω, (Z i ω j k - ENNReal.ofReal (zNorm (j - k) ^ 2)) ^ p =
          ENNReal.ofReal lam⁻¹ ^ p *
            (T i ω j k - ENNReal.ofReal (lam * zNorm (j - k) ^ 2)) ^ p := fun ω => by
        have e : ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (lam * zNorm (j - k) ^ 2) =
            ENNReal.ofReal (zNorm (j - k) ^ 2) := by
          rw [ENNReal.ofReal_mul hlam.le, ← mul_assoc, hlam1, one_mul]
        rw [← mul_pow, ENNReal.mul_sub fun _ _ => ENNReal.ofReal_ne_top, e]
        simp only [hZ, h, ite_true]
      simp only [hpt]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
      calc ENNReal.ofReal lam⁻¹ ^ p * ∫⁻ ω,
            (T i ω j k - ENNReal.ofReal (lam * zNorm (j - k) ^ 2)) ^ p ∂P'
          ≤ ENNReal.ofReal lam⁻¹ ^ p * ENNReal.ofReal (lam ^ p) := by gcongr; exact hmom i j k h
        _ = 1 := by rw [ENNReal.ofReal_pow hlam.le, ← mul_pow, hlam1, one_pow]
    · simp [hZ, h, hp0]
  have H := hC Ω' P' π hπ Z hZm hZind hZmom
  have hsum : ∀ ω, ∑ i : Fin M, T i ω (X.J b M s W 0 (π ω) i.castSucc)
      (X.J b M s W 0 (π ω) i.succ) = ENNReal.ofReal lam * ∑ i : Fin M,
        Z i ω (X.J b M s W 0 (π ω) i.castSucc) (X.J b M s W 0 (π ω) i.succ) := fun ω => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hZ, hJD ω i, ite_true]
    rw [← mul_assoc, hlam2, one_mul]
  simp only [hsum]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hlam.le]
  gcongr

end IsotropicVariance.Paper.Proofs.Profiles
