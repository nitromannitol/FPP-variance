/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.InfluenceProb
public import IsotropicVariance.Paper.Proofs.Gain.GainVariance
public import IsotropicVariance.Paper.Contracts.Blocks
public import IsotropicVariance.Paper.Contracts.Profiles
import IsotropicVariance.Paper.Proofs.Profiles.Asymptotics
import IsotropicVariance.Paper.Proofs.Gain.GainAssembly

/-!
# Proposition `prop:gain`: the Cauchy–Schwarz inequality of the few translates

The inequality behind Lemma `lem:fewtranslates`, for the averaged minimum
`F̄ = M⁻¹ Σ_{j<M} F_j`, `M = ⌈K^{2/3}⌉`. Fix a block `G = (i, z)` and a coupling of it. With
`Δ_j = F_j^G − F_j`, `Δ_j = 0` unless the tube of the moved noise meets the moved block. Hence
`|Δ_j| ≤ t Δ_j² + (4t)⁻¹ (1_{E₁} + 1_{E₂})` for every `t > 0`, and averaging over `j` and optimizing
over `t` gives `(E|F̄^G − F̄|)² ≤ (M⁻¹ Σ_j E Δ_j²) (M⁻¹ Σ_j 2 P(G_j meets the tube))`.

* `sq_le_mul_of_forall_le`: `x ≤ t a + (4t)⁻¹ q` for all `t > 0` gives `x² ≤ a q`.
* `sq_lintegral_abs_average_le`: the abstract form of the bound for one block.
* `sq_lintegral_abs_averagedMin_sub_le_of_isBlockCoupling`: the bound for one block of `F̄`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper IsotropicVariance.Paper.Contracts

variable {m : ℕ}

/-! ### Two elementary inequalities -/

/-- `|x| ≤ t x² + (4t)⁻¹` for `t > 0`. -/
theorem abs_le_mul_sq_add {t : ℝ} (ht : 0 < t) (x : ℝ) : |x| ≤ t * x ^ 2 + (4 * t)⁻¹ := by
  have h : t * x ^ 2 + (4 * t)⁻¹ - |x| = (2 * t * |x| - 1) ^ 2 / (4 * t) := by
    rw [← sq_abs x]
    field_simp
    ring
  have : 0 ≤ (2 * t * |x| - 1) ^ 2 / (4 * t) := by positivity
  linarith

/-- **Optimizing the parameter**: if `x ≤ t a + (4t)⁻¹ q` for every `t > 0`, with `a`, `q`
finite, then `x² ≤ a q`. -/
theorem sq_le_mul_of_forall_le {x a q : ℝ≥0∞} (ha : a ≠ ⊤) (hq : q ≠ ⊤)
    (h : ∀ t : ℝ, 0 < t → x ≤ ENNReal.ofReal t * a + ENNReal.ofReal (4 * t)⁻¹ * q) :
    x ^ 2 ≤ a * q := by
  have hfin : ∀ t : ℝ, ENNReal.ofReal t * a + ENNReal.ofReal (4 * t)⁻¹ * q ≠ ⊤ := fun t =>
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq⟩
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top (hfin 1) (h 1 one_pos)
  have hreal : ∀ t : ℝ, 0 < t → x.toReal ≤ t * a.toReal + (4 * t)⁻¹ * q.toReal := by
    intro t ht
    have h1 := ENNReal.toReal_mono (hfin t) (h t ht)
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ht.le, ENNReal.toReal_ofReal (by positivity)] at h1
  set ξ := x.toReal
  set α := a.toReal
  set π := q.toReal
  have hξ0 : 0 ≤ ξ := ENNReal.toReal_nonneg
  have hα0 : 0 ≤ α := ENNReal.toReal_nonneg
  have hπ0 : 0 ≤ π := ENNReal.toReal_nonneg
  have key : ξ ^ 2 ≤ α * π := by
    by_contra hcon
    push Not at hcon
    have hξ : 0 < ξ := by
      rcases hξ0.eq_or_lt with h0 | h0
      · rw [← h0] at hcon
        linarith only [hcon, mul_nonneg hα0 hπ0]
      · exact h0
    rcases hα0.eq_or_lt with hα | hα
    · have h1 := hreal ((π + 1) / ξ) (by positivity)
      rw [← hα, mul_zero, zero_add] at h1
      have h2 : (4 * ((π + 1) / ξ))⁻¹ * π < ξ := by
        have e : (4 * ((π + 1) / ξ))⁻¹ * π = ξ * (π / (4 * (π + 1))) := by
          field_simp
        have h3 : π / (4 * (π + 1)) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        rw [e]
        exact mul_lt_of_lt_one_right hξ h3
      linarith
    · have h1 := hreal (ξ / (2 * α)) (by positivity)
      have e1 : ξ / (2 * α) * α = ξ / 2 := by field_simp
      have e2 : (4 * (ξ / (2 * α)))⁻¹ * π = α * π / (2 * ξ) := by
        field_simp
        ring
      have h2 : α * π / (2 * ξ) < ξ / 2 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        linarith only [hcon]
      rw [e1, e2] at h1
      linarith
  calc x ^ 2 = ENNReal.ofReal (ξ ^ 2) := by rw [ENNReal.ofReal_pow hξ0, ENNReal.ofReal_toReal hx]
    _ ≤ ENNReal.ofReal (α * π) := ENNReal.ofReal_le_ofReal key
    _ = a * q := by rw [ENNReal.ofReal_mul hα0, ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hq]

/-! ### The bound for one block -/

/-- **The `L¹` bound for one block, abstractly**: on a probability space, if `|Δ_j| ≤ B` and
`Δ_j = 0` almost surely off `E₁ j ∪ E₂ j`, then
`(E |M⁻¹ Σ_{j<M} Δ_j|)² ≤ (M⁻¹ Σ_j E Δ_j²) (M⁻¹ Σ_j (P(E₁ j) + P(E₂ j)))`. -/
theorem sq_lintegral_abs_average_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {M : ℕ} (hM : 1 ≤ M) (Δ : ℕ → Ω' → ℝ)
    (hΔ : ∀ j, AEMeasurable (Δ j) P') {B : ℝ} (hB : ∀ j ω, |Δ j ω| ≤ B) (E₁ E₂ : ℕ → Set Ω')
    (hE₁ : ∀ j, NullMeasurableSet (E₁ j) P') (hE₂ : ∀ j, NullMeasurableSet (E₂ j) P')
    (h0 : ∀ j ∈ Finset.range M, ∀ᵐ ω ∂P', ω ∉ E₁ j → ω ∉ E₂ j → Δ j ω = 0) :
    (∫⁻ ω, ENNReal.ofReal |(M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω| ∂P') ^ 2 ≤
      ((M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, ∫⁻ ω, ENNReal.ofReal (Δ j ω ^ 2) ∂P') *
        ((M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, (P' (E₁ j) + P' (E₂ j))) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hMinv : (M : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by exact_mod_cast hM0.ne')
  set a := (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, ∫⁻ ω, ENNReal.ofReal (Δ j ω ^ 2) ∂P' with ha_def
  set q := (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, (P' (E₁ j) + P' (E₂ j)) with hq_def
  have ha : a ≠ ⊤ := by
    refine ENNReal.mul_ne_top hMinv (ENNReal.sum_ne_top.2 fun j _ => ?_)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B ^ 2)) ?_
    calc ∫⁻ ω, ENNReal.ofReal (Δ j ω ^ 2) ∂P' ≤ ∫⁻ _, ENNReal.ofReal (B ^ 2) ∂P' :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hB j ω) 2)
      _ = ENNReal.ofReal (B ^ 2) := by rw [lintegral_const, measure_univ, mul_one]
  have hq : q ≠ ⊤ := ENNReal.mul_ne_top hMinv (ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
  refine sq_le_mul_of_forall_le ha hq fun t ht => ?_
  set r : ℕ → Ω' → ℝ≥0∞ := fun j ω => ENNReal.ofReal t * ENNReal.ofReal (Δ j ω ^ 2) +
    ENNReal.ofReal (4 * t)⁻¹ * ((E₁ j).indicator 1 ω + (E₂ j).indicator 1 ω) with hr_def
  -- the pointwise bound
  have hpt : ∀ j ∈ Finset.range M, ∀ᵐ ω ∂P', ENNReal.ofReal |Δ j ω| ≤ r j ω := by
    intro j hj
    filter_upwards [h0 j hj] with ω hω
    have hamgm : ENNReal.ofReal |Δ j ω| ≤
        ENNReal.ofReal t * ENNReal.ofReal (Δ j ω ^ 2) + ENNReal.ofReal (4 * t)⁻¹ := by
      rw [← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (abs_le_mul_sq_add ht _)
    by_cases h1 : ω ∈ E₁ j
    · refine hamgm.trans (add_le_add le_rfl ?_)
      calc ENNReal.ofReal (4 * t)⁻¹ = ENNReal.ofReal (4 * t)⁻¹ * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul' le_rfl (by simp [Set.indicator_of_mem h1])
    · by_cases h2 : ω ∈ E₂ j
      · refine hamgm.trans (add_le_add le_rfl ?_)
        calc ENNReal.ofReal (4 * t)⁻¹ = ENNReal.ofReal (4 * t)⁻¹ * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul' le_rfl (by simp [Set.indicator_of_mem h2])
      · rw [hω h1 h2, abs_zero, ENNReal.ofReal_zero]
        exact bot_le
  -- the average
  have hpt' : ∀ᵐ ω ∂P', ENNReal.ofReal |(M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω| ≤
      (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, r j ω := by
    have hall := (Filter.eventually_all_finset (Finset.range M)).2 hpt
    filter_upwards [hall] with ω hω
    calc ENNReal.ofReal |(M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω|
        ≤ ENNReal.ofReal ((M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, |Δ j ω|) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [abs_mul, abs_of_pos (inv_pos.2 hM0)]
          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hM0.le)
      _ = (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, ENNReal.ofReal |Δ j ω| := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 hM0.le), ENNReal.ofReal_inv_of_pos hM0,
            ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
      _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum hω)
  have hΔ2 : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal t * ENNReal.ofReal (Δ j ω ^ 2)) P' :=
    fun j => (((hΔ j).pow_const 2).ennreal_ofReal).const_mul _
  have hi₁ : ∀ j, AEMeasurable ((E₁ j).indicator (1 : Ω' → ℝ≥0∞)) P' := fun j =>
    aemeasurable_one.indicator₀ (hE₁ j)
  have hi₂ : ∀ j, AEMeasurable ((E₂ j).indicator (1 : Ω' → ℝ≥0∞)) P' := fun j =>
    aemeasurable_one.indicator₀ (hE₂ j)
  have hrm : ∀ j ∈ Finset.range M, AEMeasurable (r j) P' := fun j _ =>
    (hΔ2 j).add (((hi₁ j).add (hi₂ j)).const_mul _)
  have hint : ∀ j, ∫⁻ ω, r j ω ∂P' = ENNReal.ofReal t * ∫⁻ ω, ENNReal.ofReal (Δ j ω ^ 2) ∂P' +
      ENNReal.ofReal (4 * t)⁻¹ * (P' (E₁ j) + P' (E₂ j)) := by
    intro j
    rw [hr_def, lintegral_add_left' (hΔ2 j), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left' (hi₁ j), lintegral_indicator_one₀ (hE₁ j),
      lintegral_indicator_one₀ (hE₂ j)]
  calc ∫⁻ ω, ENNReal.ofReal |(M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω| ∂P'
      ≤ ∫⁻ ω, (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, r j ω ∂P' := lintegral_mono_ae hpt'
    _ = (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, (ENNReal.ofReal t *
          ∫⁻ ω, ENNReal.ofReal (Δ j ω ^ 2) ∂P' +
          ENNReal.ofReal (4 * t)⁻¹ * (P' (E₁ j) + P' (E₂ j))) := by
        rw [lintegral_const_mul' _ _ hMinv, lintegral_finsetSum' _ hrm]
        simp_rw [hint]
    _ = ENNReal.ofReal t * a + ENNReal.ofReal (4 * t)⁻¹ * q := by
        rw [ha_def, hq_def, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-! ### The averaged minimum -/

/-- The change of a function of the noise under a block coupling is almost everywhere
measurable when the function is. -/
theorem aemeasurable_sub_of_isBlockCoupling {X : Setting.{u} m} {G : Set (Pt m)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (hc : X.IsBlockCoupling G P' old new) {Z : X.Ω → ℝ} (hZ : AEMeasurable Z X.P) :
    AEMeasurable (fun ω => Z (new ω) - Z (old ω)) P' := by
  have hnew : AEMeasurable Z (P'.map new) := by rw [hc.measurePreserving_new.map_eq]; exact hZ
  have hold : AEMeasurable Z (P'.map old) := by rw [hc.measurePreserving_old.map_eq]; exact hZ
  exact (hnew.comp_measurable hc.measurePreserving_new.measurable).sub
    (hold.comp_measurable hc.measurePreserving_old.measurable)

/-- The change of `F̄` is the average of the changes of the `F_j`. -/
theorem averagedMin_sub (X : Setting.{u} m) (b : ℝ) (K : ℕ) (n W : ℝ) (L : ℕ) (c c' : X.Ω) :
    averagedMin X b K n W L c' - averagedMin X b K n W L c =
      ((colCount K : ℝ))⁻¹ * ∑ j ∈ Finset.range (colCount K),
        (X.F b K n (((j : ℝ) * L * W) • e₂ m) c' - X.F b K n (((j : ℝ) * L * W) • e₂ m) c) := by
  simp only [averagedMin, ← mul_sub, ← Finset.sum_sub_distrib]

/-- **The `L¹` bound for one block of `F̄`** (Lemma `lem:fewtranslates`), for a coupling of the
block `G = (i, z)` on any probability space: `(E|F̄^G − F̄|)² ≤ (M⁻¹ Σ_j E (F_j^G − F_j)²) (M⁻¹ Σ_j
2 P(G_j meets the tube))`, with `G_j = block(i, z − j L e₀)`, for `W ≥ 1` and `W √m ≤ n/4`. -/
theorem sq_lintegral_abs_averagedMin_sub_le_of_isBlockCoupling (X : Setting.{u} m) (hm : 1 ≤ m)
    {b : ℝ} (hb : X.IsUpperBound b) {K : ℕ} (hM : 1 ≤ colCount K) {n W : ℝ} (hn : 0 < n)
    (hW : 1 ≤ W) (hWn : W * Real.sqrt m ≤ n / 4) {L : ℕ} (i : Fin K) (z : Fin m → ℤ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {old new : Ω' → X.Ω} (hc : X.IsBlockCoupling (block n W L i z) P' old new) :
    (∫⁻ ω, ENNReal.ofReal |averagedMin X b K n W L (new ω) -
        averagedMin X b K n W L (old ω)| ∂P') ^ 2 ≤
      ((colCount K : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range (colCount K),
          ∫⁻ ω, ENNReal.ofReal ((X.F b K n (((j : ℝ) * L * W) • e₂ m) (new ω) -
            X.F b K n (((j : ℝ) * L * W) • e₂ m) (old ω)) ^ 2) ∂P') *
        ((colCount K : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range (colCount K),
          2 * X.P {c | ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)}) := by
  set M := colCount K with hMdef
  set g : ℕ → Pt m ≃ᵃⁱ[ℝ] Pt m := fun j => shiftBy (((j : ℝ) * L * W) • e₂ m) with hg
  set Δ : ℕ → Ω' → ℝ := fun j ω => X.F b K n (((j : ℝ) * L * W) • e₂ m) (new ω) -
    X.F b K n (((j : ℝ) * L * W) • e₂ m) (old ω) with hΔ_def
  set A : ℕ → Set X.Ω := fun j =>
    {c | ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)} with hA_def
  set E₁ : ℕ → Set Ω' := fun j => (fun ω => X.act (g j) (old ω)) ⁻¹' A j with hE₁_def
  set E₂ : ℕ → Set Ω' := fun j => (fun ω => X.act (g j) (new ω)) ⁻¹' A j with hE₂_def
  have hW0 : 0 < W := by linarith
  have hact : ∀ j, MeasurePreserving (X.act (g j)) X.P X.P := fun j =>
    X.measurePreserving_act _ (isProperRigidMotion_shiftBy _)
  have hold : ∀ j, MeasurePreserving (fun ω => X.act (g j) (old ω)) P' X.P := fun j =>
    (hact j).comp hc.measurePreserving_old
  have hnew : ∀ j, MeasurePreserving (fun ω => X.act (g j) (new ω)) P' X.P := fun j =>
    (hact j).comp hc.measurePreserving_new
  have hA : ∀ j, NullMeasurableSet (A j) X.P := fun j =>
    nullMeasurableSet_hit X hb hn hW0.le _ i
  have hE₁ : ∀ j, NullMeasurableSet (E₁ j) P' := fun j =>
    (hA j).preimage (hold j).quasiMeasurePreserving
  have hE₂ : ∀ j, NullMeasurableSet (E₂ j) P' := fun j =>
    (hA j).preimage (hnew j).quasiMeasurePreserving
  have hPE₁ : ∀ j, P' (E₁ j) = X.P (A j) := fun j => (hold j).measure_preimage (hA j)
  have hPE₂ : ∀ j, P' (E₂ j) = X.P (A j) := fun j => (hnew j).measure_preimage (hA j)
  have hB : ∀ j ω, |Δ j ω| ≤ K * b * n := by
    intro j ω
    have h1 := F_nonneg X b K n (((j : ℝ) * L * W) • e₂ m) (new ω)
    have h2 := F_le X hb K hn.le (((j : ℝ) * L * W) • e₂ m) (new ω)
    have h3 := F_nonneg X b K n (((j : ℝ) * L * W) • e₂ m) (old ω)
    have h4 := F_le X hb K hn.le (((j : ℝ) * L * W) • e₂ m) (old ω)
    rw [abs_le]
    constructor <;> simp only [hΔ_def] <;> linarith
  have hΔm : ∀ j, AEMeasurable (Δ j) P' := fun j =>
    aemeasurable_sub_of_isBlockCoupling hc (aemeasurable_F X hb K hn.le (lon_smul_e₂ _))
  have h0 : ∀ j ∈ Finset.range M, ∀ᵐ ω ∂P', ω ∉ E₁ j → ω ∉ E₂ j → Δ j ω = 0 := by
    intro j _
    have hloc := IsBlockCoupling.ae_rho_eq_closure (isBlockCoupling_act hc
      (isProperRigidMotion_shiftBy _) (image_shiftBy_block hm n W L i j z))
    filter_upwards [hloc] with ω hω h1 h2
    have hF : ∀ ω' : X.Ω, X.F b K n (((j : ℝ) * L * W) • e₂ m) ω' =
        X.F b K n 0 (X.act (g j) ω') := fun ω' => F_eq_F_zero_act X b K n (lon_smul_e₂ _) ω'
    have hd1 : Disjoint (block n W L i (z - blockShift hm j L))
        (tube X b K n W (X.act (g j) (old ω)) i) := by
      by_contra hcon
      exact h1 hcon
    have hd2 : Disjoint (block n W L i (z - blockShift hm j L))
        (tube X b K n W (X.act (g j) (new ω)) i) := by
      by_contra hcon
      exact h2 hcon
    have le1 := F_le_of_disjoint_tube X hb hn hW hWn L i (z - blockShift hm j L)
      (c := X.act (g j) (old ω)) (c' := X.act (g j) (new ω)) hω hd1
    have le2 := F_le_of_disjoint_tube X hb hn hW hWn L i (z - blockShift hm j L)
      (c := X.act (g j) (new ω)) (c' := X.act (g j) (old ω)) (fun x hx => (hω x hx).symm) hd2
    simp only [hΔ_def]
    rw [hF, hF]
    linarith
  have key := sq_lintegral_abs_average_le hM Δ hΔm hB E₁ E₂ hE₁ hE₂ h0
  have e1 : ∀ ω, averagedMin X b K n W L (new ω) - averagedMin X b K n W L (old ω) =
      (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω := fun ω => averagedMin_sub X b K n W L _ _
  have e2 : ∑ j ∈ Finset.range M, (P' (E₁ j) + P' (E₂ j)) =
      ∑ j ∈ Finset.range M, 2 * X.P (A j) :=
    Finset.sum_congr rfl fun j _ => by rw [hPE₁, hPE₂, two_mul]
  simp_rw [e1]
  rw [e2] at key
  exact key

/-! ### The scales -/

/-- `√K / ⌈K^{2/3}⌉ ≤ K^{-1/6}`. -/
theorem sqrt_div_colCount_le {K : ℕ} (hK : 1 ≤ K) :
    Real.sqrt K / colCount K ≤ (K : ℝ) ^ (-(1 : ℝ) / 6) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM : (K : ℝ) ^ ((2 : ℝ) / 3) ≤ colCount K := Nat.le_ceil _
  have hpos : 0 < (K : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hK0 _
  rw [div_le_iff₀ (hpos.trans_le hM)]
  calc Real.sqrt K = (K : ℝ) ^ (-(1 : ℝ) / 6) * (K : ℝ) ^ ((2 : ℝ) / 3) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hK0]
        norm_num
    _ ≤ (K : ℝ) ^ (-(1 : ℝ) / 6) * colCount K :=
        mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg hK0.le _)

end IsotropicVariance.Paper.Proofs.Gain
