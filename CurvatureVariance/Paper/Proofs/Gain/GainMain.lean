/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Gain.FromTargets
public import CurvatureVariance.Paper.Proofs.Gain.GainComparison
public import CurvatureVariance.Paper.Proofs.Gain.GainVariance
import CurvatureVariance.Paper.Proofs.Gain.AVMoments
import CurvatureVariance.Paper.Proofs.Gain.GainOnTargets
import CurvatureVariance.Paper.Proofs.Geometry.SupportAngular
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds

/-!
# Proposition `prop:gain`: the gain

The proof of Proposition `prop:gain` in the paper: the proof of [AB26, Proposition 6.5] with
Lemmas `lem:labels`, `lem:residual` and `lem:fewtranslates`, which gives `Var[F̄] ≤ ω_K K Q_n²`;
the comparison of `F̄` with the passage time by Lemma `lem:modulus` at the length `ℓ` and equation
`eq:fixedcomparison`; and `K Q_n² ≤ 2 Q_ℓ²`.
The reduction to the lengths `ℓ = Kn` (the beginning of Section `sec:gain`) is
`Gain.gainStatement_of`. The continuum counterpart is `IsotropicVariance.Paper.Proofs.Gain.Main`,
and the section on the block side follows it.

* `blockSide`: the block side `L(K)`, the largest integer in `[16, K^{1/24}]` with
  `α_L ≥ (log K)^{−1/2}`; it tends to infinity with `K` (`tendsto_blockSide`).
* `evariance_le_of_steps`: `Var[T] ≤ (2 e² + 4 v) Q_ℓ²` from `‖F̄ − T‖₂ ≤ e Q_ℓ`,
  `Var[F̄] ≤ v K Q_n²` and `K Q_n² ≤ 2 Q_ℓ²`.
* `gainOnTargetsStatement`: the proposition at the lengths `ℓ = Kn`.
* `gainStatement`: `GainStatement`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain.Printed

open CurvatureVariance.Paper

/-! ### The block side -/

open scoped Classical in
/-- **The block side `L(K)`** (the fourth paragraph of the proof of [AB26, Proposition 6.5]): the
largest integer in `[16, K^{1/24}]` with `α_L ≥ (log K)^{−1/2}`, the value of `findGreatest` being
the one the proof uses when such an integer exists (`blockSide_spec`). As
`IsotropicVariance.Paper.Proofs.Gain.blockSide` in the continuum library. -/
noncomputable def blockSide (α : ℕ → ℝ) (K : ℕ) : ℕ :=
  Nat.findGreatest (fun L => 16 ≤ L ∧ (Real.sqrt (Real.log K))⁻¹ ≤ α L)
    ⌊(K : ℝ) ^ ((1 : ℝ) / 24)⌋₊

/-- The defining properties of `L(K)`, when `L = 16` is admissible. -/
theorem blockSide_spec {α : ℕ → ℝ} {K : ℕ} (h16 : (16 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 24))
    (hα : (Real.sqrt (Real.log K))⁻¹ ≤ α 16) :
    16 ≤ blockSide α K ∧ (blockSide α K : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 24) ∧
      (Real.sqrt (Real.log K))⁻¹ ≤ α (blockSide α K) := by
  classical
  have hK0 : (0 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 24) := Real.rpow_nonneg (Nat.cast_nonneg K) _
  have h := Nat.findGreatest_spec (P := fun L => 16 ≤ L ∧ (Real.sqrt (Real.log K))⁻¹ ≤ α L)
    (m := 16) (Nat.le_floor (by exact_mod_cast h16)) ⟨le_rfl, hα⟩
  refine ⟨h.1, ?_, h.2⟩
  have hle := Nat.findGreatest_le (P := fun L => 16 ≤ L ∧ (Real.sqrt (Real.log K))⁻¹ ≤ α L)
    ⌊(K : ℝ) ^ ((1 : ℝ) / 24)⌋₊
  exact (Nat.cast_le.2 hle).trans (Nat.floor_le hK0)

/-- `(log K)^{−1/2} → 0`. -/
theorem tendsto_inv_sqrt_log :
    Tendsto (fun K : ℕ => (Real.sqrt (Real.log K))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

/-- `K^{1/24} → ∞`. -/
theorem tendsto_rpow_one_div_24 :
    Tendsto (fun K : ℕ => (K : ℝ) ^ ((1 : ℝ) / 24)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

/-- **`L(K)` tends to infinity with `K`** (the fourth paragraph of the proof of
[AB26, Proposition 6.5]): a fixed `L₀` is admissible for `K` large, since `α_{L₀} > 0`. -/
theorem tendsto_blockSide {α : ℕ → ℝ} (hα : ∀ L, 0 < α L) :
    Tendsto (blockSide α) atTop atTop := by
  classical
  refine tendsto_atTop.2 fun L₀ => ?_
  set L₁ := max L₀ 16
  filter_upwards [tendsto_rpow_one_div_24.eventually_ge_atTop (L₁ : ℝ),
    tendsto_inv_sqrt_log.eventually (ge_mem_nhds (hα L₁))] with K h1 h2
  exact (le_max_left L₀ 16).trans
    (Nat.le_findGreatest (P := fun L => 16 ≤ L ∧ (Real.sqrt (Real.log K))⁻¹ ≤ α L)
      (Nat.le_floor h1) ⟨le_max_right _ _, h2⟩)

/-- The index of the error in equation `eq:modulus`: for meshes `h k > 0` and `ρ K → 0`, the largest
`k ≤ K` with `ρ K < h k` tends to infinity, and it is an admissible index for `K` large. -/
theorem exists_index_tendsto {h ρ : ℕ → ℝ} (hh : ∀ k, 0 < h k) (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∃ (ks : ℕ → ℕ) (K₁ : ℕ), Tendsto ks atTop atTop ∧ ∀ K, K₁ ≤ K → ρ K < h (ks K) := by
  classical
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (hρ.eventually (gt_mem_nhds (hh 0)))
  refine ⟨fun K => Nat.findGreatest (fun k => ρ K < h k) K, K₁, ?_, fun K hK =>
    Nat.findGreatest_spec (P := fun k => ρ K < h k) (Nat.zero_le K) (hK₁ K hK)⟩
  refine tendsto_atTop.2 fun k₀ => ?_
  filter_upwards [eventually_ge_atTop k₀, hρ.eventually (gt_mem_nhds (hh k₀))] with K hK hρK
  exact Nat.le_findGreatest hK hρK

/-- With `α_L ≥ (log K)^{−1/2}`, the term `C/(α_L log K)` is at most `C (log K)^{−1/2}` (the
fourth paragraph of the proof of [AB26, Proposition 6.5]). -/
theorem div_mul_log_le {C α x : ℝ} (hC : 0 ≤ C) (hx : 0 < x) (hα : (Real.sqrt x)⁻¹ ≤ α) :
    C / (α * x) ≤ C * (Real.sqrt x)⁻¹ := by
  have hy : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hα0 : 0 < α := (inv_pos.2 hy).trans_le hα
  have hyy : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  rw [div_le_iff₀ (mul_pos hα0 hx)]
  have h1 : 1 ≤ (Real.sqrt x)⁻¹ * (α * x) := by
    calc (1 : ℝ) = (Real.sqrt x)⁻¹ * ((Real.sqrt x)⁻¹ * x) := by
          nth_rewrite 3 [← hyy]
          field_simp
      _ ≤ (Real.sqrt x)⁻¹ * (α * x) := by gcongr
  calc C = C * 1 := (mul_one C).symm
    _ ≤ C * ((Real.sqrt x)⁻¹ * (α * x)) := mul_le_mul_of_nonneg_left h1 hC
    _ = C * (Real.sqrt x)⁻¹ * (α * x) := by ring

/-! ### The last line of the proof -/

/-- **The conclusion** (the proof of Proposition `prop:gain`): `Var[T] ≤ 2 Var[Z] + 2 ‖T − Z‖₂²`,
with `‖Z − T‖₂ ≤ e Q`, `Var[Z] ≤ v A` and `A ≤ 2 Q²`. As
`IsotropicVariance.Paper.Proofs.Gain.evariance_le_of_steps`, through
`Gain.evariance_le_two_mul_add`. -/
theorem evariance_le_of_steps {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T Z : Ω → ℝ} (hZ : AEStronglyMeasurable Z P) {e v A Q : ℝ}
    (he : 0 ≤ e) (hv : 0 ≤ v) (hQ : 0 ≤ Q) (hA : A ≤ 2 * Q ^ 2)
    (h1 : eLpNorm (fun ω => Z ω - T ω) 2 P ≤ ENNReal.ofReal (e * Q))
    (h2 : evariance Z P ≤ ENNReal.ofReal (v * A)) :
    evariance T P ≤ ENNReal.ofReal ((2 * e ^ 2 + 4 * v) * Q ^ 2) := by
  have h20 : (0 : ℝ) ≤ 2 := by norm_num
  have hQ2 : 0 ≤ Q ^ 2 := sq_nonneg Q
  have heQ : 0 ≤ e * Q := mul_nonneg he hQ
  have hvA : v * A ≤ 2 * v * Q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hA hv
    linarith only [this]
  have hsub : eLpNorm (T - Z) 2 P = eLpNorm (fun ω => Z ω - T ω) 2 P := by
    rw [eLpNorm_sub_comm]
    rfl
  calc evariance T P
      ≤ 2 * evariance Z P + 2 * eLpNorm (T - Z) 2 P ^ 2 := evariance_le_two_mul_add hZ
    _ ≤ 2 * ENNReal.ofReal (2 * v * Q ^ 2) + 2 * ENNReal.ofReal (e * Q) ^ 2 := by
        rw [hsub]
        gcongr
        exact h2.trans (ENNReal.ofReal_le_ofReal hvA)
    _ = ENNReal.ofReal ((2 * e ^ 2 + 4 * v) * Q ^ 2) := by
        rw [← ENNReal.ofReal_pow heQ, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul h20,
          ← ENNReal.ofReal_mul h20, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The rate of `GainStatement` tends to zero. As
`IsotropicVariance.Paper.Proofs.Gain.tendsto_gainRate` in the continuum library. -/
theorem tendsto_gainRate {g : ℕ → ℝ} {ks : ℕ → ℕ} (hg : Tendsto g atTop (𝓝 0))
    (hks : Tendsto ks atTop atTop) (C : ℝ) :
    Tendsto (fun K : ℕ => 2 * (1 / (K : ℝ) + 1 / ((ks K : ℝ) + 1)) ^ 2 +
      4 * (g K + (K : ℝ) ^ (-(1 : ℝ) / 12) + 96 * C * (Real.sqrt (Real.log K))⁻¹))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun K : ℕ => 1 / (K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have h2 : Tendsto (fun K : ℕ => 1 / ((ks K : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hks
  have h3 : Tendsto (fun K : ℕ => (K : ℝ) ^ (-(1 : ℝ) / 12)) atTop (𝓝 0) := by
    have e : -(1 : ℝ) / 12 = -(1 / 12) := by ring
    rw [e]
    exact (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h4 := tendsto_inv_sqrt_log.const_mul (96 * C)
  have h := (((h1.add h2).pow 2).const_mul 2).add (((hg.add h3).add h4).const_mul 4)
  simpa using h

/-! ### Proposition `prop:gain` -/

variable {m : ℕ}

/-- **Proposition `prop:gain` at the lengths `ℓ = Kn`**, by the proof of Proposition `prop:gain` in
the paper, from the contracts that the proof of [AB26, Proposition 6.5] cites, with the changes of
the paper. As `IsotropicVariance.Paper.Proofs.Gain.gainStatement_of_contracts` in the continuum
library. Equation `eq:modulus` is taken at `b = 1`, `κ = 1/9`, and the error `1/(k + 1)` with
`k = ks K → ∞`; the error of equation `eq:fixedcomparison` is at most `Q_ℓ/K`. So
`‖F̄ − T‖₂ ≤ (1/K + 1/(ks K + 1)) Q_ℓ`. -/
theorem gainOnTargetsStatement (hL : Contracts.LabelsStatement m)
    (hR : Contracts.ResidualStatement m) (hF : Contracts.FewTranslatesStatement m)
    (hMP : Contracts.ModifiedPoincareStatement.{0, 0}) (hM : Contracts.ModulusStatement m)
    (hFC : Contracts.FixedComparisonStatement m) : GainOnTargetsStatement m := by
  intro bd hbd Cstar
  obtain ⟨α, ψ, hα, hψ, hLab⟩ := hL bd hbd Cstar
  obtain ⟨ψ', hψ', hRes⟩ := hR bd hbd Cstar α ψ hα hψ
  obtain ⟨C, hC, hFew⟩ := hF bd hbd Cstar
  obtain ⟨Cc, hCc, hCmp⟩ := hFC bd hbd
  set Lof : ℕ → ℕ := blockSide α with hLofdef
  have hLof : Tendsto Lof atTop atTop := tendsto_blockSide hα
  set g : ℕ → ℝ := fun K => max (ψ' (Lof K)) 0 with hgdef
  have hg0 : ∀ K, 0 ≤ g K := fun K => le_max_right _ _
  have hglim : Tendsto g atTop (𝓝 0) := by
    have h0 := (hψ'.comp hLof).max
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    rwa [max_self] at h0
  -- the meshes of `eq:modulus` at the errors `1/(k+1)`
  have hMod := fun k : ℕ => hM bd hbd Cstar 1 le_rfl (1 / ((k : ℝ) + 1)) (by positivity)
  choose h hh hMk using hMod
  set ρ : ℕ → ℝ := fun K => 2 * (K : ℝ) ^ (-(1 / 48 : ℝ)) with hρdef
  have hρlim : Tendsto ρ atTop (𝓝 0) := by
    have h0 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 48)).comp
      tendsto_natCast_atTop_atTop).const_mul 2
    rwa [mul_zero] at h0
  obtain ⟨ks, K₁, hks, hρK⟩ := exists_index_tendsto (h := fun k => min (h k) 1)
    (fun k => lt_min (hh k) one_pos) hρlim
  -- how large `K` must be
  have hev : ∀ᶠ K : ℕ in atTop, (16 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 24) ∧
      C ≤ (K : ℝ) ^ ((1 : ℝ) / 24) ∧ (Real.sqrt (Real.log K))⁻¹ ≤ α 16 ∧ 24 ≤ K := by
    filter_upwards [tendsto_rpow_one_div_24.eventually_ge_atTop 16,
      tendsto_rpow_one_div_24.eventually_ge_atTop C,
      tendsto_inv_sqrt_log.eventually (ge_mem_nhds (hα 16)), eventually_ge_atTop 24]
      with K h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.1 hev
  refine ⟨_, tendsto_gainRate hglim hks C, max K₁ K₂, fun K hK₀ hK => ?_⟩
  obtain ⟨h16K, hCK, hαK, hK24⟩ := hK₂ K ((le_max_right _ _).trans hK₀)
  have hρk := hρK K ((le_max_left _ _).trans hK₀)
  obtain ⟨hL16, hLK, hαL⟩ := blockSide_spec (α := α) h16K hαK
  set L := Lof K with hLdef
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hK1' : 1 < K := lt_of_lt_of_le (by norm_num) hK
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL16
  have hρle : ρ K ≤ h (ks K) := hρk.le.trans (min_le_left _ _)
  have hρ1 : ρ K ≤ 1 := hρk.le.trans (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hLab K hK L hL16
  obtain ⟨N₂, hN₂⟩ := hRes K hK L hL16
  obtain ⟨N₃, hN₃⟩ := hFew K hK L hL16
  obtain ⟨N₄, hN₄⟩ := hMk (ks K) K hK (1 / 9) (by norm_num) (by norm_num)
  obtain ⟨N₅, hN₅⟩ := hCmp K hK
  obtain ⟨N₆, hN₆⟩ := exists_log_sq_le (Cc * K * K)
  refine ⟨max N₁ (max N₂ (max N₃ (max N₄ (max N₅ (max N₆ ((9 * K) ^ 2)))))),
    fun M hMs hfit N hN A hA hP hRA n ℓ y ht => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2 : N₂ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : N₃ ≤ N :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hN4 : N₄ ≤ N := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))).trans hN
  have hN5 : N₅ ≤ N := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))).trans hN
  have hN6 : N₆ ≤ N := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hN
  have hN7 : (9 * K) ^ 2 ≤ N := ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))))).trans hN
  have := hMs.probP
  have hm := hMs.one_le_m
  obtain ⟨hn2, -, hnℓ, hℓ1⟩ := Responses.target_size_bounds hK1 hN7 ht
  have hn1 : 1 ≤ n := by omega
  have hNone : 1 ≤ N := le_trans (Nat.one_le_pow _ _ (by omega)) hN7
  obtain ⟨-, -, -, hslope⟩ := target_facts hK1 hNone ht
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  have hQn : 0 < Q M K A n := mul_pos hA0 (Real.rpow_pos_of_pos hnr _)
  have hQℓ : 0 < Q M K A ℓ := mul_pos hA0 (Real.rpow_pos_of_pos hℓr _)
  -- the instances of the contracts at this `K`, `L = L(K)` and the target
  obtain ⟨P, hPsub⟩ := Proofs.Geometry.exists_isSubgradient M.μ (slopeVec (targetSlope ℓ y))
  obtain ⟨lam, hfam⟩ := hN₁ M hMs hfit N hN1 A hA hP hRA n ℓ y ht P hPsub
  have hres := (hN₂ M hMs hfit N hN2 A hA hP hRA n ℓ y ht P hPsub lam hfam).2
  have hoff : ∀ (σ : Fin K → Fin m → Fin L) (i : ℕ) (k : Fin m),
      0 ≤ offsetOf σ i k ∧ offsetOf σ i k < L := fun σ i k => offsetOf_mem hL1 σ i k
  have hlabels : ∀ σ : Fin K → Fin m → Fin L,
      IsOffsetLabels n (wInt M K A n) L K (targetSlope ℓ y) (offsetOf σ) lam :=
    fun σ => hfam.isOffsetLabels (hoff σ)
  have hat : ∀ (σ : Fin K → Fin m → Fin L), ∀ i < K, ∀ (g : Fin m → ℤ) (ω : Config m),
      ENNReal.ofReal (α L) ≤ M.P (lam (i + 1) (offsetOf σ (i + 1)) g ⁻¹'
        {lam (i + 1) (offsetOf σ (i + 1)) g ω}) := fun σ i hi g ω =>
    hfam.le_measure (i + 1) (by omega) (by omega) _ g (hoff σ _) ω
  have hα1 : α L ≤ 1 := by
    have h0 := hfam.le_measure 1 le_rfl hK1 0 0
      (fun _ => ⟨le_rfl, show (0 : ℤ) < (L : ℤ) by exact_mod_cast hL1⟩) (fun _ => 0)
    exact ENNReal.ofReal_le_one.1 (h0.trans prob_le_one)
  have hF2 := memLp_averagedMin hMs hn2 K A L ℓ y
  -- `Var[f]`, for every choice of the vectors `a_i`
  have hf : ∀ σ : Fin K → Fin m → Fin L,
      evariance (labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K (offsetOf σ) lam) M.P ≤
        ENNReal.ofReal (((K : ℝ) ^ (-(1 : ℝ) / 12) + 96 * C / (α L * Real.log K)) *
          (K * Q M K A n ^ 2)) := fun σ =>
    evariance_labelMean_le hMP hMs hK1' (hlabels σ) hQn hC hCK (hα L) hα1 (hat σ) hF2
      (hN₃ M hMs hfit N hN3 A hA hP hRA n ℓ y ht (offsetOf σ) (hoff σ) lam (hlabels σ))
  -- `Var[F̄]`
  have hVF := evariance_le_of_offsets hMs hL1 hF2
    (fun σ => (hlabels σ).blockLabelSigma_le _) hres hf
  have hlogK : 0 < Real.log K := Real.log_pos (by exact_mod_cast hK1')
  have hKQ : 0 < (K : ℝ) * Q M K A n ^ 2 := by positivity
  have hκ : 0 < (K : ℝ) ^ (-(1 : ℝ) / 12) := Real.rpow_pos_of_pos hK0 _
  have hαlog := div_mul_log_le (C := 96 * C) (by positivity) hlogK hαL
  set v : ℝ := g K + (K : ℝ) ^ (-(1 : ℝ) / 12) + 96 * C * (Real.sqrt (Real.log K))⁻¹ with hv
  have hv0 : 0 ≤ v := by
    have := hg0 K
    have : 0 ≤ 96 * C * (Real.sqrt (Real.log K))⁻¹ := by positivity
    linarith only [this, hg0 K, hκ, hv]
  have hψg : ψ' L ≤ g K := le_max_left _ _
  have hVF' : evariance (fun ω => averagedMin M K A L ω n ℓ y) M.P ≤
      ENNReal.ofReal (v * (K * Q M K A n ^ 2)) := by
    refine hVF.trans ?_
    refine (add_le_add (ENNReal.ofReal_le_ofReal (q := g K * (K * Q M K A n ^ 2)) ?_)
      (ENNReal.ofReal_le_ofReal (q := ((K : ℝ) ^ (-(1 : ℝ) / 12) +
        96 * C * (Real.sqrt (Real.log K))⁻¹) * (K * Q M K A n ^ 2)) ?_)).trans (le_of_eq ?_)
    · rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hψg hKQ.le
    · exact mul_le_mul_of_nonneg_right (by linarith only [hαlog]) hKQ.le
    · rw [← ENNReal.ofReal_add (mul_nonneg (hg0 K) hKQ.le)
        (mul_nonneg (by positivity) hKQ.le)]
      congr 1
      rw [hv]
      ring
  -- the comparison with the passage time
  have hV : 0 < numTranslates K := numTranslates_pos hK1
  have hWℓ0 : 0 ≤ W M K A ℓ := Real.sqrt_nonneg _
  have hδ1 := hMs.delta_le_one
  have hsideρ : side M K A L n ≤ ρ K * W M K A ℓ := by
    refine (side_le_rpow hMs hK hA hn1 ht.1 hLK).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rpow_translation_le hK24 hδ1) zero_le_two) hWℓ0
  have hsideh : side M K A L n ≤ h (ks K) * W M K A ℓ :=
    hsideρ.trans (mul_le_mul_of_nonneg_right hρle hWℓ0)
  have hside1 : side M K A L n ≤ 1 * W M K A ℓ :=
    hsideρ.trans (mul_le_mul_of_nonneg_right hρ1 hWℓ0)
  have hpair := isCubePair_tau (M := M) K A L n ℓ y hℓ1 hside1
  obtain ⟨X, hX, hXae⟩ := hN₄ M hMs hfit N hN4 A hA hP hRA ℓ (by
    have := ht.2.1
    linarith only [this]) ht.2.2.1 _ _ _ hpair hslope P hPsub
  have hlog := hN₆ N hN6
  have hcmp : Cc * K * Real.log N ^ 2 ≤ 1 / (K : ℝ) * Q M K A ℓ := by
    have h1 := hlog.trans (rpow_le_Q hMs hK hA hℓ1 ht.2.1)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hK0]
    calc Cc * K * Real.log N ^ 2 * K = Cc * K * K * Real.log N ^ 2 := by ring
      _ ≤ Q M K A ℓ := h1
  have ha : eLpNorm (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P ≤
      ENNReal.ofReal (1 / (K : ℝ) * Q M K A ℓ) :=
    (hN₅ M hMs hfit N hN5 n ℓ y ht).trans (ENNReal.ofReal_le_ofReal hcmp)
  have hcomp := eLpNorm_averagedMin_sub_le_of_modulus hMs hm hV hsideh hX hXae ha
  have hk0 : (0 : ℝ) ≤ 1 / ((ks K : ℝ) + 1) := by positivity
  have hK0' : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
  have hcomp' : eLpNorm (fun ω => averagedMin M K A L ω n ℓ y -
      passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P ≤
      ENNReal.ofReal ((1 / (K : ℝ) + 1 / ((ks K : ℝ) + 1)) * Q M K A ℓ) := by
    refine hcomp.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (mul_nonneg hK0' hQℓ.le) (mul_nonneg hk0 hQℓ.le), add_mul]
  exact evariance_le_of_steps (measurable_averagedMin M K A L n ℓ y).aestronglyMeasurable
    (add_nonneg hK0' hk0) hv0 hQℓ.le (K_mul_Q_sq_le M hMs hK ht.1 A) hcomp' hVF'

/-- **Proposition `prop:gain`**, from Lemmas `lem:labels`, `lem:residual` and `lem:fewtranslates`,
[AB26, Proposition 1.3], equations `eq:modulus` and `eq:fixedcomparison`, and the reduction
`Gain.gainStatement_of` of the beginning of Section `sec:gain`. The premise `RoundingStatement` of
the edge is not used as a hypothesis: `Gain.gainStatement_of` calls `Chart.roundingStatement_holds`,
which proves it. -/
theorem gainStatement (hL : Contracts.LabelsStatement m) (hR : Contracts.ResidualStatement m)
    (hF : Contracts.FewTranslatesStatement m) (hMP : Contracts.ModifiedPoincareStatement.{0, 0})
    (hM : Contracts.ModulusStatement m) (hFC : Contracts.FixedComparisonStatement m)
    (_hRound : Contracts.RoundingStatement m) : Contracts.GainStatement m :=
  gainStatement_of (gainOnTargetsStatement hL hR hF hMP hM hFC)

end CurvatureVariance.Paper.Gain.Printed
