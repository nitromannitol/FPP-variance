/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.TubeCount
import IsotropicVariance.Paper.Proofs.Localization.Measurable
import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
import IsotropicVariance.Paper.Contracts.Cited
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Lemma `lem:fewtranslates`: the probability that a block meets the tube

The proof of Lemma `lem:fewtranslates`: "By `eq:rowenergy` and
`eq:radiusenergy`, the squares of these numbers, summed over `i`, have mean at most `CK`, so, by
the Cauchy–Schwarz inequality, each has mean at most `CK^{1/2}`". For a block `G = (i, z)` and its
translates `G_j = block(i, z − j L e₀)`, `j < M`,
`Σ_j P(G_j meets the tube of F in the slab i) ≤ E[2 R_i + 2 |J_{i+1} − J_i| + 2] ≤ C √K`,
with `2x ≤ x²/√K + √K`, the row energy `E Σ_i |J_{i+1} − J_i|² ≤ 5 C K` (equation `eq:rowenergy`)
and the radius energy `E Σ_i R_i(J_i, J_{i+1})² ≤ C K` (equation `eq:radiusenergy`).

* `aemeasurable_R`, `aemeasurable_R_J`: the radii, at fixed and at the random indices, are random
  variables (`Localization.aemeasurable_maxDeviation_slab`, `Infra.Slab.aemeasurable_J`).
* `nullMeasurableSet_hit`: the event that a set meets the tube is null measurable.
* `lintegral_sum_zNorm_sq_le`: the row energy from the `O_1` bound `eq:rowenergy` and the moment
  bound of `O_1`.
* `sum_measure_hit_le`: the bound on the sum of the probabilities.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper IsotropicVariance.Paper.Contracts

variable {m : ℕ}

/-! ### Measurability -/

/-- The radius `R_i(j, k)` is a random variable. -/
theorem aemeasurable_R (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) (n W : ℝ) (i : ℕ)
    (j k : Fin m → ℤ) :
    AEMeasurable (fun ω => X.R b n W ω i j k) X.P := by
  by_cases h : W * zNorm (k - j) ≤ n / 2
  · have e : (fun ω => X.R b n W ω i j k) = fun ω => radiusConst m + W⁻¹ *
        maxDeviation ((chainSlab n 0 i).density b (X.ρ ω)) (chainSlab n 0 i).set
          (gridCube n W 0 i j) (gridCube n W 0 (i + 1) k) (gridCubeCenter n W 0 i j)
          (gridCubeCenter n W 0 (i + 1) k) := by
      funext ω
      unfold Setting.R
      exact ite_eq_left h
    rw [e]
    exact ((Localization.aemeasurable_maxDeviation_slab X hb (chainSlab n 0 i)
      (SmallMean.isCompact_gridCube _ _ i j) (SmallMean.isCompact_gridCube _ _ (i + 1) k) _
      _).const_mul _).const_add _
  · have e : (fun ω => X.R b n W ω i j k) = fun _ => (0 : ℝ) := by
      funext ω
      unfold Setting.R
      exact ite_eq_right h
    rw [e]
    exact aemeasurable_const

/-- A family of random variables indexed by a countable discrete set, evaluated at a random index,
is a random variable. -/
theorem aemeasurable_apply_of_countable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] {f : Ω → ι → ℝ}
    (hf : ∀ j, AEMeasurable (fun ω => f ω j) P) {J : Ω → ι} (hJ : AEMeasurable J P) :
    AEMeasurable (fun ω => f ω (J ω)) P := by
  obtain ⟨g, hgm, hfg⟩ : ∃ g : ι → Ω → ℝ, (∀ j, Measurable (g j)) ∧
      ∀ j, (fun ω => f ω j) =ᵐ[P] g j :=
    ⟨fun j => (hf j).mk _, fun j => (hf j).measurable_mk, fun j => (hf j).ae_eq_mk⟩
  have hG : Measurable fun p : Ω × ι => g p.2 p.1 := measurable_from_prod_countable_left hgm
  have hm : Measurable fun ω => g (hJ.mk J ω) ω :=
    hG.comp (measurable_id.prodMk hJ.measurable_mk)
  refine ⟨fun ω => g (hJ.mk J ω) ω, hm, ?_⟩
  filter_upwards [ae_all_iff.2 hfg, hJ.ae_eq_mk] with ω hω hJω
  have h1 : f ω (J ω) = g (J ω) ω := hω (J ω)
  change f ω (J ω) = g (hJ.mk J ω) ω
  rw [h1, hJω]

/-- The radius `R_i(J_i, J_{i+1})` at the indices of the minimizing points is a random
variable. -/
theorem aemeasurable_R_J (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {K : ℕ} {n W : ℝ}
    (hn : 0 < n) (i : Fin K) :
    AEMeasurable (fun ω => X.R b n W ω i (X.J b K n W 0 ω i.castSucc)
      (X.J b K n W 0 ω i.succ)) X.P := by
  have hJ : AEMeasurable (fun ω => (X.J b K n W 0 ω i.castSucc, X.J b K n W 0 ω i.succ)) X.P :=
    (Infra.Slab.aemeasurable_J X hb hn 0 K W i.castSucc).prodMk
      (Infra.Slab.aemeasurable_J X hb hn 0 K W i.succ)
  have h := aemeasurable_apply_of_countable
    (f := fun ω (jk : (Fin m → ℤ) × (Fin m → ℤ)) => X.R b n W ω i jk.1 jk.2)
    (fun jk => aemeasurable_R X hb n W i jk.1 jk.2) hJ
  exact h

/-- **The event that a set meets the tube is null measurable.** -/
theorem nullMeasurableSet_hit (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {K : ℕ}
    {n W : ℝ} (hn : 0 < n) (hW : 0 ≤ W) (G : Set (Pt m)) (i : Fin K) :
    NullMeasurableSet {c | ¬ Disjoint G (tube X b K n W c i)} X.P := by
  set U : (Fin m → ℤ) × (Fin m → ℤ) → Set ℝ :=
    fun jk => {r | ¬ Disjoint G (segTube n W i jk.1 jk.2 r)} with hUdef
  have hU : ∀ jk, MeasurableSet (U jk) := fun jk =>
    (IsUpperSet.ordConnected (s := U jk) fun r r' hrr'
      (hr : ¬ Disjoint G (segTube n W i jk.1 jk.2 r)) hd =>
        hr (hd.mono_right (segTube_mono hW hrr'))).measurableSet
  set S : Set (((Fin m → ℤ) × (Fin m → ℤ)) × ℝ) := {p | p.2 ∈ U p.1} with hSdef
  have hS : MeasurableSet S := by
    have e : S = ⋃ jk : (Fin m → ℤ) × (Fin m → ℤ), ({jk} : Set _) ×ˢ U jk := by
      ext ⟨jk, r⟩
      simp [hSdef]
    rw [e]
    exact MeasurableSet.iUnion fun jk => (measurableSet_singleton jk).prod (hU jk)
  have hφ : AEMeasurable (fun c => ((X.J b K n W 0 c i.castSucc, X.J b K n W 0 c i.succ),
      X.R b n W c i (X.J b K n W 0 c i.castSucc) (X.J b K n W 0 c i.succ))) X.P :=
    ((Infra.Slab.aemeasurable_J X hb hn 0 K W i.castSucc).prodMk
      (Infra.Slab.aemeasurable_J X hb hn 0 K W i.succ)).prodMk (aemeasurable_R_J X hb hn i)
  exact hφ.nullMeasurable hS

/-! ### The row energy -/

/-- **The row energy** from the `O_1` bound `eq:rowenergy`: if
`|F − K n| + Q Σ_i |J_{i+1} − J_i|² − C K Q ≤ O_1(C Q)`, then `E Σ_i |J_{i+1} − J_i|² ≤ 5 C K`. -/
theorem lintegral_sum_zNorm_sq_le (X : Setting.{u} m) (b : ℝ) {K : ℕ} (hK : 1 ≤ K)
    {n W Q C : ℝ} (hQ : 0 < Q) (hC : 0 < C)
    (hos : Cited.IsOs X.P 1 (C * Q) (fun ω => |X.F b K n 0 ω - K * n| +
      Q * ∑ i : Fin K, zNorm (X.J b K n W 0 ω i.succ - X.J b K n W 0 ω i.castSucc) ^ 2 -
        C * K * Q)) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin K,
        zNorm (X.J b K n W 0 ω i.succ - X.J b K n W 0 ω i.castSucc) ^ 2) ∂X.P ≤
      ENNReal.ofReal (5 * C * K) := by
  set Z : X.Ω → ℝ := fun ω => ∑ i : Fin K,
    zNorm (X.J b K n W 0 ω i.succ - X.J b K n W 0 ω i.castSucc) ^ 2 with hZ
  set Y : X.Ω → ℝ := fun ω => |X.F b K n 0 ω - K * n| + Q * Z ω - C * K * Q with hY
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hmom := osMomentStatement_holds.{u} hos one_pos (by positivity) zero_le_one
  have e1 : (2 * (1 + ((Nat.ceil ((1 : ℝ) / 1)).factorial : ℝ)) * (C * Q) ^ (1 : ℝ)) =
      4 * (C * Q) := by
    rw [div_one, Nat.ceil_one, Nat.factorial_one, Real.rpow_one]
    norm_num
  rw [e1] at hmom
  simp only [Real.rpow_one] at hmom
  have hpt : ∀ ω, ENNReal.ofReal (Z ω) ≤
      ENNReal.ofReal Q⁻¹ * ENNReal.ofReal (max (Y ω) 0) + ENNReal.ofReal (C * K) := by
    intro ω
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hQ.le),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Y ω ≤ max (Y ω) 0 := le_max_left _ _
    have h2 : 0 ≤ |X.F b K n 0 ω - K * n| := abs_nonneg _
    have h3 : Q * Z ω ≤ max (Y ω) 0 + C * K * Q := by
      simp only [hY] at h1
      linarith only [h1, h2]
    have h4 : Z ω = Q⁻¹ * (Q * Z ω) := by field_simp
    rw [h4]
    calc Q⁻¹ * (Q * Z ω) ≤ Q⁻¹ * (max (Y ω) 0 + C * K * Q) :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hQ.le)
      _ = Q⁻¹ * max (Y ω) 0 + C * K := by field_simp
  calc ∫⁻ ω, ENNReal.ofReal (Z ω) ∂X.P
      ≤ ∫⁻ ω, (ENNReal.ofReal Q⁻¹ * ENNReal.ofReal (max (Y ω) 0) + ENNReal.ofReal (C * K)) ∂X.P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal Q⁻¹ * ∫⁻ ω, ENNReal.ofReal (max (Y ω) 0) ∂X.P +
          ENNReal.ofReal (C * K) := by
        rw [lintegral_add_right' _ aemeasurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal Q⁻¹ * ENNReal.ofReal (4 * (C * Q)) + ENNReal.ofReal (C * K) := by
        gcongr
    _ = ENNReal.ofReal (4 * C + C * K) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hQ.le),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (5 * C * K) := ENNReal.ofReal_le_ofReal
        (by linarith only [le_mul_of_one_le_right hC.le hK1])

/-! ### The probability that the translates of a block meet the tube -/

private lemma two_mul_le_inv_mul_sq_add {s x : ℝ} (hs : 0 < s) : 2 * x ≤ s⁻¹ * x ^ 2 + s := by
  have e : s⁻¹ * x ^ 2 + s - 2 * x = s⁻¹ * (x - s) ^ 2 := by field_simp; ring
  have h := mul_nonneg (inv_nonneg.2 hs.le) (sq_nonneg (x - s))
  rw [← e] at h
  linarith only [h]

/-- **The translates of a block meet the tube with total probability `O(√K)`** (the proof of Lemma
`lem:fewtranslates`): for the block `G = (i, z)` and its translates `G_j = block(i, z − j L e₀)`,
`j < M`, `Σ_j P(G_j meets the tube of F in the slab i) ≤ (C_row + C_rad + 4) √K`, given the row
energy `E Σ_i |J_{i+1} − J_i|² ≤ C_row K` and the radius energy `E Σ_i R_i(J_i, J_{i+1})² ≤ C_rad
K`. -/
theorem sum_measure_hit_le (X : Setting.{u} m) (hm : 1 ≤ m) {b : ℝ} (hb : X.IsUpperBound b)
    {K : ℕ} (hK : 1 ≤ K) {n W : ℝ} (hn : 0 < n) (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L) (M : ℕ)
    (i : Fin K) (z : Fin m → ℤ) {Crow Crad : ℝ} (hCrow : 0 ≤ Crow) (hCrad : 0 ≤ Crad)
    (hrow : ∫⁻ ω, ENNReal.ofReal (∑ i' : Fin K,
        zNorm (X.J b K n W 0 ω i'.succ - X.J b K n W 0 ω i'.castSucc) ^ 2) ∂X.P ≤
      ENNReal.ofReal (Crow * K))
    (hrad : ∫⁻ ω, ENNReal.ofReal (∑ i' : Fin K, X.R b n W ω i' (X.J b K n W 0 ω i'.castSucc)
        (X.J b K n W 0 ω i'.succ) ^ 2) ∂X.P ≤ ENNReal.ofReal (Crad * K)) :
    ∑ j ∈ Finset.range M,
        X.P {c | ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)} ≤
      ENNReal.ofReal ((Crow + Crad + 4) * Real.sqrt K) := by
  classical
  set A : ℕ → Set X.Ω :=
    fun j => {c | ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)} with hA
  have hAm : ∀ j, NullMeasurableSet (A j) X.P := fun j => nullMeasurableSet_hit X hb hn hW.le _ i
  set s := Real.sqrt K with hs_def
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : 0 < s := Real.sqrt_pos.2 hK0
  have hs1 : 1 ≤ s := by rw [hs_def, Real.one_le_sqrt]; exact_mod_cast hK
  have hss : s ^ 2 = K := Real.sq_sqrt hK0.le
  have hsi : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have h2s : (0 : ℝ) ≤ 2 * s + 2 := by linarith only [hs]
  set Zr : X.Ω → ℝ := fun ω => ∑ i' : Fin K,
    zNorm (X.J b K n W 0 ω i'.succ - X.J b K n W 0 ω i'.castSucc) ^ 2 with hZr
  set Zd : X.Ω → ℝ := fun ω => ∑ i' : Fin K,
    X.R b n W ω i' (X.J b K n W 0 ω i'.castSucc) (X.J b K n W 0 ω i'.succ) ^ 2 with hZd
  have hZd0 : ∀ ω, 0 ≤ Zd ω := fun ω => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZr0 : ∀ ω, 0 ≤ Zr ω := fun ω => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZdm : AEMeasurable (fun ω => ENNReal.ofReal (Zd ω)) X.P :=
    (Finset.aemeasurable_fun_sum _ fun i' _ =>
      (aemeasurable_R_J X hb hn i').pow_const 2).ennreal_ofReal
  have hpt : ∀ c, ∑ j ∈ Finset.range M, (A j).indicator 1 c ≤
      ENNReal.ofReal s⁻¹ * ENNReal.ofReal (Zr c) + ENNReal.ofReal s⁻¹ * ENNReal.ofReal (Zd c) +
        ENNReal.ofReal (2 * s + 2) := by
    intro c
    have e : ∑ j ∈ Finset.range M, (A j).indicator (1 : X.Ω → ℝ≥0∞) c =
        (((Finset.range M).filter fun j =>
          ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)).card :
            ℝ≥0∞) := by
      simp only [Set.indicator_apply, Pi.one_apply]
      rw [Finset.sum_boole]
      congr
    rw [e]
    have hcount := card_hit_le X hm b (n := n) hW hL c i z M
    set R := X.R b n W c i (X.J b K n W 0 c i.castSucc) (X.J b K n W 0 c i.succ) with hR
    set zN := zNorm (X.J b K n W 0 c i.succ - X.J b K n W 0 c i.castSucc) with hzN
    have hR0 : 0 ≤ R := R_nonneg X b n hW.le c i _ _
    have hzN0 : 0 ≤ zN := Real.sqrt_nonneg _
    have h2R : 2 * R ≤ s⁻¹ * R ^ 2 + s := two_mul_le_inv_mul_sq_add hs
    have h2z : 2 * zN ≤ s⁻¹ * zN ^ 2 + s := two_mul_le_inv_mul_sq_add hs
    have hRZ : R ^ 2 ≤ Zd c := Finset.single_le_sum (f := fun i' : Fin K =>
      X.R b n W c i' (X.J b K n W 0 c i'.castSucc) (X.J b K n W 0 c i'.succ) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hzZ : zN ^ 2 ≤ Zr c := Finset.single_le_sum (f := fun i' : Fin K =>
      zNorm (X.J b K n W 0 c i'.succ - X.J b K n W 0 c i'.castSucc) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hreal : (((Finset.range M).filter fun j =>
          ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)).card : ℝ) ≤
        s⁻¹ * Zr c + s⁻¹ * Zd c + (2 * s + 2) := by
      refine hcount.trans ?_
      linarith only [h2R, h2z, mul_le_mul_of_nonneg_left hRZ hsi,
        mul_le_mul_of_nonneg_left hzZ hsi]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hsi, ← ENNReal.ofReal_mul hsi,
      ← ENNReal.ofReal_add (mul_nonneg hsi (hZr0 c)) (mul_nonneg hsi (hZd0 c)),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hsi (hZr0 c)) (mul_nonneg hsi (hZd0 c)))
        h2s]
    exact ENNReal.ofReal_le_ofReal hreal
  calc ∑ j ∈ Finset.range M, X.P (A j)
      = ∑ j ∈ Finset.range M, ∫⁻ c, (A j).indicator 1 c ∂X.P :=
        Finset.sum_congr rfl fun j _ => (lintegral_indicator_one₀ (hAm j)).symm
    _ = ∫⁻ c, ∑ j ∈ Finset.range M, (A j).indicator 1 c ∂X.P :=
        (lintegral_finsetSum' _ fun j _ => aemeasurable_const.indicator₀ (hAm j)).symm
    _ ≤ ∫⁻ c, (ENNReal.ofReal s⁻¹ * ENNReal.ofReal (Zr c) +
          ENNReal.ofReal s⁻¹ * ENNReal.ofReal (Zd c) + ENNReal.ofReal (2 * s + 2)) ∂X.P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal s⁻¹ * ∫⁻ c, ENNReal.ofReal (Zr c) ∂X.P +
          ENNReal.ofReal s⁻¹ * ∫⁻ c, ENNReal.ofReal (Zd c) ∂X.P + ENNReal.ofReal (2 * s + 2) := by
        rw [lintegral_add_right' _ aemeasurable_const,
          lintegral_add_right' _ (hZdm.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal s⁻¹ * ENNReal.ofReal (Crow * K) +
          ENNReal.ofReal s⁻¹ * ENNReal.ofReal (Crad * K) + ENNReal.ofReal (2 * s + 2) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl hrow) (mul_le_mul' le_rfl hrad)) le_rfl
    _ = ENNReal.ofReal (s⁻¹ * (Crow * K) + s⁻¹ * (Crad * K) + (2 * s + 2)) := by
        have h1 : 0 ≤ s⁻¹ * (Crow * K) := mul_nonneg hsi (mul_nonneg hCrow hK0.le)
        have h2 : 0 ≤ s⁻¹ * (Crad * K) := mul_nonneg hsi (mul_nonneg hCrad hK0.le)
        rw [ENNReal.ofReal_add (add_nonneg h1 h2) h2s, ENNReal.ofReal_add h1 h2,
          ENNReal.ofReal_mul hsi, ENNReal.ofReal_mul hsi]
    _ ≤ ENNReal.ofReal ((Crow + Crad + 4) * s) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : s⁻¹ * (Crow * K) = Crow * s := by rw [← hss]; field_simp
        have e2 : s⁻¹ * (Crad * K) = Crad * s := by rw [← hss]; field_simp
        rw [e1, e2]
        linarith only [hs1]

end IsotropicVariance.Paper.Proofs.Gain
