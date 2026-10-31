/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Gain
public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Paper.Proofs.Gain.AverageComparison
public import IsotropicVariance.Paper.Proofs.Gain.AverageVariance
import IsotropicVariance.Paper.Proofs.Gain.GainAssembly
import IsotropicVariance.Paper.Proofs.SmallMean.SmallMean

/-!
# Proposition `prop:gain`: the gain

The proof of Proposition `prop:gain` in the paper, from the labels
(`LabelsStatement`), the residual (`ResidualStatement`), Lemma `lem:fewtranslates`
(`FewTranslatesStatement`), Proposition `prop:BR` (`ModifiedPoincareStatement`), the modulus of
continuity (`ModulusStatement`) and Lemma `lem:slab` (`SlabStatement`).

* `blockSide`: the block side `L(K)`, the largest integer in `[16, K^{1/24}]` with
  `α_L ≥ (log K)^{−1/2}`; it tends to infinity with `K` (`tendsto_blockSide`).
* `evariance_le_of_steps`: `Var[T_{Kn}] ≤ (2 e + 6 v) Q_{Kn}²` from `E (F̄ − T_{Kn})² ≤ e Q_{Kn}²`,
  `Var[F̄] ≤ v K Q_n²` and `K Q_n² ≤ 3 Q_{Kn}²`.
* `evariance_TRV_le_of_instances`: the steps of the proof at fixed `K`, `L` and `ℓ`.
* `gainStatement_of_contracts`: `GainStatement`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper IsotropicVariance.Paper.Contracts

/-! ### The block side -/

open scoped Classical in
/-- **The block side `L(K)`** (proof of Proposition `prop:gain`): the largest integer in
`[16, K^{1/24}]` with `α_L ≥ (log K)^{−1/2}`, the value of `findGreatest` being the one the proof
uses when such an integer exists (`blockSide_spec`). -/
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

/-- **`L(K)` tends to infinity with `K`** (proof of Proposition `prop:gain`): a fixed `L₀` is
admissible for `K` large, since `α_{L₀} > 0`. -/
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

/-- With `α_L ≥ (log K)^{−1/2}`, the term `C/(α_L log K)` is at most `C (log K)^{−1/2}`
(proof of Proposition `prop:gain`). -/
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

/-- **The conclusion** (end of the proof of Proposition `prop:gain`):
`Var[T] ≤ 2 E (Z − T)² + 2 Var[Z]`, with `E (Z − T)² ≤ e Q²`, `Var[Z] ≤ v (K Q_n²)` and
`K Q_n² ≤ 3 Q²`. -/
theorem evariance_le_of_steps {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T Z : Ω → ℝ} (hT : MemLp T 2 P) (hZ : MemLp Z 2 P) {e v A Q : ℝ}
    (he : 0 ≤ e) (hv : 0 ≤ v) (hA : A ≤ 3 * Q ^ 2)
    (h1 : ∫⁻ ω, ENNReal.ofReal ((Z ω - T ω) ^ 2) ∂P ≤ ENNReal.ofReal (e * Q ^ 2))
    (h2 : evariance Z P ≤ ENNReal.ofReal (v * A)) :
    evariance T P ≤ ENNReal.ofReal ((2 * e + 6 * v) * Q ^ 2) := by
  have hQ : 0 ≤ Q ^ 2 := sq_nonneg Q
  have h20 : (0 : ℝ) ≤ 2 := by norm_num
  have hvA : v * A ≤ 3 * v * Q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hA hv
    linarith only [this]
  calc evariance T P
      ≤ 2 * ∫⁻ ω, ENNReal.ofReal ((Z ω - T ω) ^ 2) ∂P + 2 * evariance Z P :=
        evariance_le_two_mul hT hZ
    _ ≤ 2 * ENNReal.ofReal (e * Q ^ 2) + 2 * ENNReal.ofReal (3 * v * Q ^ 2) := by
        gcongr
        exact h2.trans (ENNReal.ofReal_le_ofReal hvA)
    _ = ENNReal.ofReal ((2 * e + 6 * v) * Q ^ 2) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul h20, ← ENNReal.ofReal_mul h20,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The error of Lemma `lem:slab` is negligible against `Q_ℓ`, for `ℓ` large depending on `K`:
`36 (C K log²(2 + ℓ))² ≤ (1/K)² Q_ℓ²`, given `36 C² K⁴ log⁴(2 + ℓ) ≤ ℓ^{4/5}`. -/
theorem sq_slabError_le {K : ℕ} (hK : 10 ≤ K) {A ℓ Cs : ℝ} (hA : 1 ≤ A) (hℓ : 1 ≤ ℓ)
    (h : 36 * Cs ^ 2 * (K : ℝ) ^ 4 * Real.log (2 + ℓ) ^ 4 ≤ ℓ ^ (4 / 5 : ℝ)) :
    36 * (Cs * K * Real.log (2 + ℓ) ^ 2) ^ 2 ≤ (1 / (K : ℝ)) ^ 2 * Q K A ℓ ^ 2 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hℓ0 : 0 < ℓ := by linarith only [hℓ]
  have hQ := SmallMean.rpow_le_Q hK hA hℓ
  have hrpow0 : 0 ≤ ℓ ^ (2 / 5 : ℝ) := Real.rpow_nonneg hℓ0.le _
  have hQ2 : ℓ ^ (4 / 5 : ℝ) ≤ Q K A ℓ ^ 2 := by
    have e : ℓ ^ (4 / 5 : ℝ) = ℓ ^ (2 / 5 : ℝ) * ℓ ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_add hℓ0]
      norm_num
    rw [e, sq]
    exact mul_le_mul hQ hQ hrpow0 (hrpow0.trans hQ)
  have e : 36 * (Cs * K * Real.log (2 + ℓ) ^ 2) ^ 2 =
      (1 / (K : ℝ)) ^ 2 * (36 * Cs ^ 2 * (K : ℝ) ^ 4 * Real.log (2 + ℓ) ^ 4) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (h.trans hQ2) (sq_nonneg _)

/-! ### Proposition `prop:gain` -/

section Fixed

variable {m : ℕ} {X : Setting.{u} m}

/-- **The bound at fixed `K`, `L`, `ℓ`**: the steps of the proof of Proposition `prop:gain` at one
choice of the parameters, from the instances of the contracts. Here `g K Q_n²` bounds the first term
of the decomposition (Lemma `lem:residual`), `C` is the constant of Lemma `lem:fewtranslates`, and
`η` is the error of equation `eq:modulus`. -/
theorem evariance_TRV_le_of_instances (hMP : ModifiedPoincareStatement.{0, 0}) {b : ℝ}
    (hb : X.IsUpperBound b) {K L : ℕ} (hK : 1 < K) (hL : 1 ≤ L) {A ℓ C α g η θ r ρ : ℝ}
    (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hC : 0 < C) (hCK : C ≤ (K : ℝ) ^ ((1 : ℝ) / 24)) (hg : 0 ≤ g)
    (hη : 0 ≤ η) (hθ : 0 < θ) (hrρ : r ≤ ρ) (Λ : X.LabelFamily)
    (hdet : Λ.IsDetermined (ℓ / K) (W K A (ℓ / K)) L) (hα : 0 < α) (hat : Λ.AtomsGe α)
    (hres : ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o : Fin K → Fin m → Fin L,
        ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K (ℓ / K) (W K A (ℓ / K)) L ω -
          X.P[averagedMin X b K (ℓ / K) (W K A (ℓ / K)) L | Λ.allSigma K o] ω) ^ 2) ∂X.P ≤
        ENNReal.ofReal (g * K * Q K A (ℓ / K) ^ 2))
    (hfew : ∀ o : Fin K → Fin m → Fin L,
      ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
          eLpNorm (X.labelMean b K (ℓ / K) (W K A (ℓ / K)) Λ o -
            X.P[X.labelMean b K (ℓ / K) (W K A (ℓ / K)) Λ o | Λ.otherSigma K o i z]) 2 X.P ^ 2 ≤
            ENNReal.ofReal (C * K * Q K A (ℓ / K) ^ 2) ∧
        ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
          eLpNorm (X.labelMean b K (ℓ / K) (W K A (ℓ / K)) Λ o -
            X.P[X.labelMean b K (ℓ / K) (W K A (ℓ / K)) Λ o | Λ.otherSigma K o i z]) 1 X.P ^ 2 ≤
            ENNReal.ofReal (C * (K : ℝ) ^ (-(1 : ℝ) / 6) * K * Q K A (ℓ / K) ^ 2))
    (htrans : ∀ j < colCount K, 0 ≤ (j : ℝ) * L * W K A (ℓ / K) ∧
      (j : ℝ) * L * W K A (ℓ / K) ≤ r)
    (hY : ∀ τ : Pt m, (∀ ω, 0 ≤ X.F b K (ℓ / K) τ ω - X.passTime ω τ (τ + ℓ • e₁)) ∧
      Cited.IsOs X.P 1 θ fun ω => X.F b K (ℓ / K) τ ω - X.passTime ω τ (τ + ℓ • e₁))
    (hmod : eLpNorm (fun ω => modulusSup (X.slabTime b (centeredPair ℓ r).slab ω)
      (centeredPair ℓ r).first (centeredPair ℓ r).second ρ) (8 * (m + 1) : ℝ≥0∞) X.P ≤
        ENNReal.ofReal (η * Q K A ℓ))
    (hθK : 36 * θ ^ 2 ≤ (1 / (K : ℝ)) ^ 2 * Q K A ℓ ^ 2) :
    evariance (X.TRV ℓ) X.P ≤ ENNReal.ofReal
      ((2 * ((1 / (K : ℝ)) ^ 2 + 3 * η ^ 2) +
        6 * (g + (K : ℝ) ^ (-(1 : ℝ) / 12) + 96 * C / (α * Real.log K))) * Q K A ℓ ^ 2) := by
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hK2 : (1 : ℝ) < K := by exact_mod_cast hK
  have hlogK : 0 < Real.log K := Real.log_pos hK2
  have hn : 0 < ℓ / K := div_pos hℓ hK0
  have hQn : 0 < Q K A (ℓ / K) := mul_pos (by linarith only [hA]) (Real.rpow_pos_of_pos hn _)
  have hWn : 0 < W K A (ℓ / K) := Real.sqrt_pos.2 (mul_pos hn hQn)
  have hQℓ : 0 < Q K A ℓ := mul_pos (by linarith only [hA]) (Real.rpow_pos_of_pos hℓ _)
  have hKℓ : (K : ℝ) * (ℓ / K) = ℓ := mul_div_cancel₀ ℓ hK0.ne'
  have hF := (averagedMin_regular X hb K hn.le (W K A (ℓ / K)) L).1
  -- `Var[F̄]`
  have hκ : 0 < (K : ℝ) ^ (-(1 : ℝ) / 12) := Real.rpow_pos_of_pos hK0 _
  have hVF := evariance_averagedMin_le_of_offsets hL Λ hdet hF hres fun o =>
    evariance_labelMean_le hMP hK hn hWn hQn hC hCK Λ hdet hα hat o hF (hfew o)
  have hVF' : evariance (averagedMin X b K (ℓ / K) (W K A (ℓ / K)) L) X.P ≤
      ENNReal.ofReal ((g + (K : ℝ) ^ (-(1 : ℝ) / 12) + 96 * C / (α * Real.log K)) *
        (K * Q K A (ℓ / K) ^ 2)) := by
    refine hVF.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  -- the comparison with `T_ℓ`
  have hE := lintegral_sq_averagedMin_sub_le hb hK1 hn hKℓ hrρ hθ (by positivity) htrans hY hmod
  have hE' : ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K (ℓ / K) (W K A (ℓ / K)) L ω -
      X.TRV ℓ ω) ^ 2) ∂X.P ≤
        ENNReal.ofReal (((1 / (K : ℝ)) ^ 2 + 3 * η ^ 2) * Q K A ℓ ^ 2) := by
    refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
    have e : (η * Q K A ℓ) ^ 2 = η ^ 2 * Q K A ℓ ^ 2 := mul_pow _ _ _
    rw [e, add_mul]
    linarith only [hθK]
  exact evariance_le_of_steps (Infra.TimeConstant.memLp_TRV X ℓ) hF (by positivity) (by positivity)
    (mul_Q_sq_le hK1 A hℓ.le) hE' hVF'

end Fixed

/-- The rate of `GainStatement` tends to zero. -/
theorem tendsto_gainRate {g : ℕ → ℝ} {ks : ℕ → ℕ} (hg : Tendsto g atTop (𝓝 0))
    (hks : Tendsto ks atTop atTop) (C : ℝ) :
    Tendsto (fun K : ℕ => 2 * ((1 / (K : ℝ)) ^ 2 + 3 * (1 / ((ks K : ℝ) + 1)) ^ 2) +
      6 * (g K + (K : ℝ) ^ (-(1 : ℝ) / 12) + 96 * C * (Real.sqrt (Real.log K))⁻¹))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun K : ℕ => (1 / (K : ℝ)) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).pow 2
  have h2 : Tendsto (fun K : ℕ => (1 / ((ks K : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hks).pow 2
  have h3 : Tendsto (fun K : ℕ => (K : ℝ) ^ (-(1 : ℝ) / 12)) atTop (𝓝 0) := by
    have e : -(1 : ℝ) / 12 = -(1 / 12) := by ring
    rw [e]
    exact (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h4 := tendsto_inv_sqrt_log.const_mul (96 * C)
  have h := ((h1.add (h2.const_mul 3)).const_mul 2).add
    (((hg.add h3).add h4).const_mul 6)
  simpa using h

/-- **Proposition `prop:gain`, by the paper's proof**: `Var[T_{Kn}] ≤ δ_K Q_{Kn}²` for every `n`
with `Kn ∈ [N/8, N]`, from the contracts the proof cites. -/
theorem gainStatement_of_contracts (hL : LabelsStatement.{u}) (hR : ResidualStatement.{u})
    (hF : FewTranslatesStatement.{u}) (hMP : ModifiedPoincareStatement.{0, 0})
    (hM : ModulusStatement.{u}) (hS : SlabStatement.{u}) : GainStatement.{u} := by
  intro m hm X hX Cstar hCstar
  obtain ⟨a₀, b, ha₀, hbd⟩ := X.bounds
  have hb : X.IsUpperBound b := fun ω x => (hbd ω x).2
  obtain ⟨α, δ, hα, hδ, hLab⟩ := hL m hm X hX b hb Cstar hCstar
  obtain ⟨G, hG, hRes⟩ := hR m hm X hX b hb Cstar hCstar
  obtain ⟨C, hC, hFew⟩ := hF m hm X hX b hb Cstar hCstar
  obtain ⟨Cs, hCs, -, hSlab⟩ := hS m hm X hX b hb
  -- the errors of `eq:labelprofile`, made positive, and the rate of the residual
  set ε : ℕ → ℝ := fun L => max (δ L) (1 / ((L : ℝ) + 1)) with hεdef
  have hεpos : ∀ L, 0 < ε L := fun L => lt_max_of_lt_right (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h0 := hδ.max (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [max_self] at h0
  set Lof : ℕ → ℕ := blockSide α with hLofdef
  have hLof : Tendsto Lof atTop atTop := tendsto_blockSide hα
  set g : ℕ → ℝ := fun K => max (G (ε (Lof K)) (Lof K)) 0 with hgdef
  have hg0 : ∀ K, 0 ≤ g K := fun K => le_max_right _ _
  have hglim : Tendsto g atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun η hη => ?_
    obtain ⟨ε₀, hε₀, L₀, hG₀⟩ := hG (η / 2) (half_pos hη)
    obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 (hεlim.eventually (gt_mem_nhds hε₀))
    obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (hLof.eventually_ge_atTop (max L₀ L₁))
    refine ⟨K₁, fun K hK => ?_⟩
    have h1 := hG₀ (ε (Lof K)) (hεpos _) (hL₁ _ ((le_max_right _ _).trans (hK₁ K hK))).le (Lof K)
      ((le_max_left _ _).trans (hK₁ K hK))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
    exact (max_le h1 (half_pos hη).le).trans_lt (half_lt_self hη)
  -- the meshes of `eq:modulus` at the errors `1/(k+1)`
  have hMod := fun k : ℕ => hM m hm X hX b hb Cstar hCstar (1 / ((k : ℝ) + 1)) (by positivity)
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
  obtain ⟨N₁, hN₁⟩ := hLab K hK L hL16
  obtain ⟨N₂, hN₂⟩ := hRes K hK L hL16 (ε L) (hεpos L)
  obtain ⟨N₃, hN₃⟩ := hFew K hK L hL16
  obtain ⟨N₄, hN₄⟩ := hMk (ks K) (1 / 8) (by norm_num) (by norm_num) K
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_log_bound (36 * Cs ^ 2 * (K : ℝ) ^ 4)
  refine ⟨max N₁ (max N₂ (max N₃ (max N₄ (max (8 * ℓ₀) (16 * K + 8))))),
    fun A N hN hSt ℓ hℓ₁ hℓ₂ => ?_⟩
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂' : N₂ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₃' : N₃ ≤ N :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hN₄' : N₄ ≤ N := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))).trans hN
  have hN₅ : max (8 * ℓ₀) (16 * (K : ℝ) + 8) ≤ N := ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hN
  have hN₆ : 8 * ℓ₀ ≤ N := (le_max_left _ _).trans hN₅
  have hN₇ : 16 * (K : ℝ) + 8 ≤ N := (le_max_right _ _).trans hN₅
  have hA : 1 ≤ A := hSt.2.1
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hℓ1 : 1 ≤ ℓ := by linarith only [hN₇, hℓ₁, hK0]
  have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
  have hKℓ : (K : ℝ) * (ℓ / K) = ℓ := mul_div_cancel₀ ℓ hK0.ne'
  have hn2 : 2 < ℓ / K := by
    rw [lt_div_iff₀ hK0]
    linarith only [hN₇, hℓ₁]
  -- the instances of the contracts at this `K`, `L = L(K)` and `ℓ`
  obtain ⟨Λ, hdet, -, hat, hcov, hprof⟩ := hN₁ A N hN₁' hSt ℓ hℓ₁ hℓ₂
  have hprof' : Proofs.Gain.LabelProfileBound X b K A ℓ L Λ (ε L) := fun i hi z =>
    (hprof i hi z).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hres := (hN₂ A N hN₂' hSt ℓ hℓ₁ hℓ₂ Λ hdet hcov hprof').2
  have hfew := hN₃ A N hN₃' hSt ℓ hℓ₁ hℓ₂ Λ hdet
  have hQn2 : 0 ≤ (K : ℝ) * Q K A (ℓ / K) ^ 2 := by positivity
  have hgle : G (ε L) L * K * Q K A (ℓ / K) ^ 2 ≤ g K * K * Q K A (ℓ / K) ^ 2 := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hQn2
  have hres' := hres.trans (ENNReal.ofReal_le_ofReal hgle)
  -- the translates
  have hWℓ0 : 0 ≤ W K A ℓ := Real.sqrt_nonneg _
  have hρle : ρ K ≤ h (ks K) := hρk.le.trans (min_le_left _ _)
  have hρ1 : ρ K ≤ 1 := hρk.le.trans (min_le_right _ _)
  have hρ0 : 0 ≤ ρ K := mul_nonneg zero_le_two (Real.rpow_nonneg hK0.le _)
  set r : ℝ := ρ K * W K A ℓ with hrdef
  have hr0 : 0 ≤ r := mul_nonneg hρ0 hWℓ0
  have hrW : 2 * r ≤ 4 * W K A ℓ := by
    have := mul_le_of_le_one_left hWℓ0 hρ1
    linarith only [this, hWℓ0]
  have htrans : ∀ j < colCount K, 0 ≤ (j : ℝ) * L * W K A (ℓ / K) ∧
      (j : ℝ) * L * W K A (ℓ / K) ≤ r := by
    intro j hj
    refine ⟨mul_nonneg (by positivity) (Real.sqrt_nonneg _), ?_⟩
    refine (translate_le hK1 A hℓ0.le hLK hj).trans ?_
    have := rpow_translation_le hK24
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this zero_le_two) hWℓ0
  -- equation `eq:modulus` at the length `ℓ` and Lemma `lem:slab`
  have hp : (centeredPair (m := m) ℓ r).IsAdmissible ℓ (W K A ℓ) (1 / 2) :=
    centeredPair_isAdmissible hr0 hrW (by norm_num)
  have hmod := hN₄ A N hN₄' hSt ℓ (by linarith only [hℓ₁]) hℓ₂ _ hp
  have hrρ : r ≤ h (ks K) * W K A ℓ := mul_le_mul_of_nonneg_right hρle hWℓ0
  have hY : ∀ τ : Pt m, (∀ ω, 0 ≤ X.F b K (ℓ / K) τ ω - X.passTime ω τ (τ + ℓ • e₁)) ∧
      Cited.IsOs X.P 1 (Cs * K * Real.log (2 + ℓ) ^ 2) fun ω =>
        X.F b K (ℓ / K) τ ω - X.passTime ω τ (τ + ℓ • e₁) := fun τ => by
    have h' := hSlab K (ℓ / K) τ hK1 hn2
    rwa [hKℓ] at h'
  have hlogpos : 0 < Real.log (2 + ℓ) := Real.log_pos (by linarith only [hℓ0])
  have hθ : 0 < Cs * K * Real.log (2 + ℓ) ^ 2 := by positivity
  have hθK := sq_slabError_le hK hA hℓ1 (hℓ₀ ℓ (by linarith only [hN₆, hℓ₁]))
  have hK1' : 1 < K := by omega
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL16
  have hmain := evariance_TRV_le_of_instances hMP hb hK1' hL1 hA hℓ0 hC hCK (hg0 K)
    (by positivity : (0 : ℝ) ≤ 1 / ((ks K : ℝ) + 1)) hθ hrρ Λ hdet (hα L) hat hres' hfew htrans hY
    hmod hθK
  refine hmain.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
  have hx : 0 < Real.log K := Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have h96 := div_mul_log_le (C := 96 * C) (by positivity) hx hαL
  linarith only [h96]

end IsotropicVariance.Paper.Proofs.Gain
