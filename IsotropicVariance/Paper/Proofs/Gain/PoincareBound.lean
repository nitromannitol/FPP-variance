/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Cited
public import IsotropicVariance.Paper.Proofs.Gain.FewTranslates
import IsotropicVariance.Infra.EfronStein.Countable
import IsotropicVariance.Infra.Entropy.Martingale
import IsotropicVariance.Paper.Proofs.Gain.PoincareJensen
import Mathlib.Probability.Independence.InfinitePi

/-!
# Proposition `prop:BR` for `f`, with the `X_G` as the variables

The first step of the proof of Proposition `prop:gain` applies Proposition `prop:BR` to
`f = E[F̄ | (X_G)_G]`, "with the `X_G` as the variables and `E_G[f]` the expectation of `f` with
respect to `X_G` alone" (text before Lemma `lem:residual`). Proposition `prop:BR` is a statement on
a product measure, and `f` lives on the noise. This file makes the transfer.

* `modifiedPoincare_of_labels`: the transfer for independent finite-valued variables on a
  probability space, written with the variables `f − E_c`, where `E_c` is the sum over the values
  of the variable `c`. It also gives the case left open by the Lean form of Proposition `prop:BR`:
  when `Σ_c E[|f − E_c|]² = 0` the logarithm is `0`, and Efron–Stein gives `Var[f] = 0`.
* `modifiedPoincare_labelMean`: the inequality of the first display of the proof of Proposition
  `prop:gain`, for `f` measurable for the labels of the blocks with offsets `o`, with the two sums
  of `Contracts.FewTranslatesStatement`. The conditional expectations given the other labels are
  identified with the expectations over `X_G` alone by
  `Proofs.Gain.condExp_otherSigma_eq_sum_label`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain.Printed

open IsotropicVariance.Paper

/-! ### Independent finite-valued variables -/

section Generic

variable {ι V : Type} {Ω : Type*} [Countable ι] [DecidableEq ι] [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `E[|g|]² ≤ E[g²]` for `g ∈ L²`. -/
theorem sq_integral_abs_le_integral_sq {Ω' : Type*} {_ : MeasurableSpace Ω'} {ν : Measure Ω'}
    [IsProbabilityMeasure ν] {g : Ω' → ℝ} (hg : MemLp g 2 ν) :
    (∫ x, |g x| ∂ν) ^ 2 ≤ ∫ x, g x ^ 2 ∂ν := by
  have h := variance_nonneg (|g|) ν
  rw [variance_eq_sub hg.abs] at h
  simp only [Pi.pow_apply, Pi.abs_apply, sq_abs] at h
  linarith only [h]

/-- **Proposition `prop:BR` for a function of independent variables on a probability space**: for
independent finite-valued variables `lab c`, each value of probability `0` or at least `α`, and
`f = φ((lab c)_c)` almost surely, with `E_c` the expectation of `f` over the variable `c` alone
(`hE`), the inequality of `prop:BR` holds for `f`. If the sum of the `L¹` terms vanishes, then
`Var[f] = 0` by Efron–Stein: the Lean form of the logarithm of `V/0` is `0`, so this case is not
contained in the inequality. -/
theorem modifiedPoincare_of_labels (hMP : Contracts.ModifiedPoincareStatement.{0, 0})
    (lab : ι → Ω → V) (hlab : ∀ c, Measurable (lab c)) (hind : iIndepFun lab P) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hatom : ∀ c v, P (lab c ⁻¹' {v}) = 0 ∨ ENNReal.ofReal α ≤ P (lab c ⁻¹' {v}))
    {f : Ω → ℝ} {φ : (ι → V) → ℝ} (hφ : Measurable φ)
    (hfφ : f =ᵐ[P] φ ∘ fun ω c => lab c ω) (hf : MemLp f 2 P) (E : ι → Ω → ℝ)
    (hE : ∀ c, E c =ᵐ[P] fun ω =>
      ∑ v, P.real (lab c ⁻¹' {v}) * φ (Function.update (fun c' => lab c' ω) c v))
    (hsum : Summable fun c => ∫ ω, (f ω - E c ω) ^ 2 ∂P) :
    variance f P * Real.log (variance f P / ∑' c, (∫ ω, |f ω - E c ω| ∂P) ^ 2) ≤
        4 / α * ∑' c, ∫ ω, (f ω - E c ω) ^ 2 ∂P ∧
      (∑' c, (∫ ω, |f ω - E c ω| ∂P) ^ 2 = 0 → variance f P = 0) := by
  set Φ : Ω → ι → V := fun ω c => lab c ω with hΦdef
  have hΦ : Measurable Φ := measurable_pi_iff.2 hlab
  set μ : ι → Measure V := fun c => P.map (lab c) with hμdef
  have hμ : ∀ c, IsProbabilityMeasure (μ c) := fun c =>
    (Measure.isProbabilityMeasure_map_iff (hlab c).aemeasurable).2 inferInstance
  have hmap : P.map Φ = Measure.infinitePi μ :=
    (iIndepFun_iff_map_fun_eq_infinitePi_map hlab).1 hind
  have hμv : ∀ c (v : V), μ c {v} = P (lab c ⁻¹' {v}) := fun c v =>
    Measure.map_apply (hlab c) (measurableSet_singleton v)
  have hatom' : ∀ c (v : V), μ c {v} = 0 ∨ ENNReal.ofReal α ≤ μ c {v} := fun c v => by
    rw [hμv]
    exact hatom c v
  have hφL : MemLp φ 2 (Measure.infinitePi μ) := by
    rw [← hmap]
    exact (memLp_map_measure_iff hφ.aestronglyMeasurable hΦ.aemeasurable).2 (hf.ae_eq hfφ)
  -- the coordinate differences
  set D : ι → (ι → V) → ℝ := fun c => Cited.coordDiff μ c φ with hDdef
  have hDeq : ∀ c, D c = Cited.coordDiff μ c φ := fun _ => rfl
  have hDm : ∀ c, Measurable (D c) := fun c => by
    rw [hDeq]
    exact hφ.sub (Infra.Entropy.measurable_coordAvg c hφ)
  have hDL : ∀ c, MemLp (D c) 2 (Measure.infinitePi μ) := fun c => by
    rw [hDeq]
    exact Infra.Entropy.memLp_coordDiff c hφL
  have hD : ∀ c, D c ∘ Φ =ᵐ[P] fun ω => f ω - E c ω := by
    intro c
    filter_upwards [hE c, hfφ] with ω h1 h2
    have e : ∫ y, φ (Function.update (Φ ω) c y) ∂μ c =
        ∑ v, P.real (lab c ⁻¹' {v}) * φ (Function.update (Φ ω) c v) := by
      rw [integral_fintype Integrable.of_finite]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_eq_mul, measureReal_def, measureReal_def, hμv]
    change φ (Φ ω) - ∫ y, φ (Function.update (Φ ω) c y) ∂μ c = f ω - E c ω
    rw [e, h1, h2]
    rfl
  have e2 : ∀ c, ∫ x, D c x ^ 2 ∂Measure.infinitePi μ = ∫ ω, (f ω - E c ω) ^ 2 ∂P := by
    intro c
    rw [← hmap, integral_map hΦ.aemeasurable ((hDm c).pow_const 2).aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hD c] with ω h
    rw [← h]
    rfl
  have e1 : ∀ c, ∫ x, |D c x| ∂Measure.infinitePi μ = ∫ ω, |f ω - E c ω| ∂P := by
    intro c
    have hm : AEStronglyMeasurable (fun x => |D c x|) (P.map Φ) :=
      (continuous_abs.measurable.comp (hDm c)).aestronglyMeasurable
    rw [← hmap, integral_map hΦ.aemeasurable hm]
    refine integral_congr_ae ?_
    filter_upwards [hD c] with ω h
    rw [← h]
    rfl
  have hV : variance φ (Measure.infinitePi μ) = variance f P := by
    rw [← hmap, variance_map (hmap ▸ hφ.aemeasurable) hΦ.aemeasurable]
    exact variance_congr hfφ.symm
  have hsum' : Summable fun c => ∫ x, D c x ^ 2 ∂Measure.infinitePi μ := by
    simpa only [e2] using hsum
  have hmain := hMP μ hα hα1 hatom' hφ hφL hsum'
  have e2' : ∀ c, ∫ x, Cited.coordDiff μ c φ x ^ 2 ∂Measure.infinitePi μ =
      ∫ ω, (f ω - E c ω) ^ 2 ∂P := e2
  have e1' : ∀ c, ∫ x, |Cited.coordDiff μ c φ x| ∂Measure.infinitePi μ =
      ∫ ω, |f ω - E c ω| ∂P := e1
  simp only [hV, e2', e1'] at hmain
  refine ⟨hmain, fun h0 => ?_⟩
  -- Efron–Stein, when the `L¹` sum vanishes
  have hle : ∀ c, (∫ ω, |f ω - E c ω| ∂P) ^ 2 ≤ ∫ ω, (f ω - E c ω) ^ 2 ∂P := fun c => by
    rw [← e2, ← e1]
    exact sq_integral_abs_le_integral_sq (hDL c)
  have hsum1 : Summable fun c => (∫ ω, |f ω - E c ω| ∂P) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle hsum
  have hzero := (hasSum_zero_iff_of_nonneg fun _ => sq_nonneg _).1 (h0 ▸ hsum1.hasSum)
  have hD0 : ∀ c, ∫ x, D c x ^ 2 ∂Measure.infinitePi μ = 0 := by
    intro c
    have h1 : ∫ x, |D c x| ∂Measure.infinitePi μ = 0 := by
      rw [e1]
      exact pow_eq_zero_iff two_ne_zero |>.1 (congrFun hzero c)
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _)
      ((hDL c).integrable one_le_two).abs).1 h1
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply, abs_eq_zero] at hx ⊢
    simp [hx]
  have hE0 : ∀ c, Infra.EfronStein.resampleEnergy μ φ c = 0 := fun c => by
    have h := ofReal_integral_eq_lintegral_ofReal (hDL c).integrable_sq
      (ae_of_all _ fun x => sq_nonneg (D c x))
    rw [hD0 c, ENNReal.ofReal_zero] at h
    rw [Infra.EfronStein.resampleEnergy_eq_two_mul_lintegral_sub_coordAverage μ hφ hφL c]
    exact mul_eq_zero_of_right _ h.symm
  have hES := Infra.EfronStein.evariance_le_half_tsum_resampleEnergy μ hφL
  simp only [hE0, tsum_zero, ENNReal.zero_div, nonpos_iff_eq_zero] at hES
  rw [← hV, variance, hES, ENNReal.toReal_zero]

omit [Countable ι] [DecidableEq ι] in
/-- A sum of real terms bounded in `[0, ∞]` is a convergent real sum. -/
theorem summable_tsum_le_of_tsum_ofReal_le {a : ι → ℝ} (ha : ∀ c, 0 ≤ a c) {A : ℝ} (hA : 0 ≤ A)
    (h : ∑' c, ENNReal.ofReal (a c) ≤ ENNReal.ofReal A) : Summable a ∧ ∑' c, a c ≤ A := by
  have htop : ∑' c, ENNReal.ofReal (a c) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hs := ENNReal.summable_toReal htop
  simp only [ENNReal.toReal_ofReal (ha _)] at hs
  refine ⟨hs, ?_⟩
  have e := ENNReal.tsum_toReal_eq (f := fun c => ENNReal.ofReal (a c))
    fun _ => ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal (ha _)] at e
  rw [← e]
  exact ENNReal.toReal_le_of_le_ofReal hA h

end Generic

/-! ### The labels of the blocks with given offsets -/

section Labels

variable {m L K : ℕ} {X : Setting.{u} m}

/-- **Proposition `prop:BR` for `f`** (proof of Proposition `prop:gain`): for `f ∈ L²` measurable
for the labels of the blocks with offsets `o`, each value of a label of probability `0` or at least
`α`, and `Σ_G ‖f − E_G[f]‖₂² ≤ a` and `Σ_G ‖f − E_G[f]‖₁² ≤ b`, the two sums `S ≤ a` and `B ≤ b`
satisfy the inequality of the paper, `Var[f] log(Var[f]/B) ≤ (4/α) S`. Moreover `B = 0` forces
`Var[f] = 0`. -/
theorem modifiedPoincare_labelMean (hMP : Contracts.ModifiedPoincareStatement.{0, 0})
    (Λ : X.LabelFamily) {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (hdet : Λ.IsDetermined n W L)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hat : Λ.AtomsGe α) (o : Fin K → Fin m → Fin L)
    {f : X.Ω → ℝ} (hf : MemLp f 2 X.P) (hfm : StronglyMeasurable[Λ.allSigma K o] f) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h2 : ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
      eLpNorm (f - X.P[f | Λ.otherSigma K o i z]) 2 X.P ^ 2 ≤ ENNReal.ofReal a)
    (h1 : ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
      eLpNorm (f - X.P[f | Λ.otherSigma K o i z]) 1 X.P ^ 2 ≤ ENNReal.ofReal b) :
    ∃ S B : ℝ, 0 ≤ B ∧ S ≤ a ∧ B ≤ b ∧
      variance f X.P * Real.log (variance f X.P / B) ≤ 4 / α * S ∧
      (B = 0 → variance f X.P = 0) := by
  let _ : MeasurableSpace Λ.V := ⊤
  have _ : MeasurableSingletonClass Λ.V := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  set lab : Bridge.BlockIdx L K o → X.Ω → Λ.V := fun c => Λ.label c.1 c.2 with hlabdef
  have hlab : ∀ c, Measurable (lab c) := fun c =>
    Measurable.of_comap_le ((Λ.sigma_le hdet _ _).trans (X.info_le _))
  have hind : iIndepFun lab X.P := by
    rw [iIndepFun_iff_iIndep]
    have h := X.iIndep_info (Bridge.BlockIdx L K o)
      (fun c => block n W L (c.1 : ℕ) (c.2 : Fin m → ℤ))
      (fun c => Bridge.measurableSet_block n W L _ _)
      (fun c => Bridge.volume_frontier_block n W L _ _)
      (Bridge.disjoint_interior_blockOf hn.le hW)
    exact iIndep_of_iIndep_of_le h fun c => Λ.sigma_le hdet (c.1 : ℕ) (c.2 : Fin m → ℤ)
  have hatom : ∀ c v, X.P (lab c ⁻¹' {v}) = 0 ∨ ENNReal.ofReal α ≤ X.P (lab c ⁻¹' {v}) :=
    fun c v => hat _ _ v
  -- `f` is a measurable function of the labels
  have hle : Λ.allSigma K o ≤ MeasurableSpace.comap (labelsOf Λ o) MeasurableSpace.pi := by
    refine iSup₂_le fun i z => iSup_le fun hz => ?_
    change MeasurableSpace.comap ((fun x => x (⟨i, z, hz⟩ : Bridge.BlockIdx L K o)) ∘
      labelsOf Λ o) ⊤ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  obtain ⟨φ, hφ, hfφ⟩ := (hfm.measurable.mono hle le_rfl).exists_eq_measurable_comp
  set E : Bridge.BlockIdx L K o → X.Ω → ℝ := fun c => X.P[f | Λ.otherSigma K o c.1 c.2] with hEdef
  have hE : ∀ c, E c =ᵐ[X.P] fun ω => ∑ v, X.P.real (lab c ⁻¹' {v}) *
      φ (Function.update (fun c' => lab c' ω) c v) := by
    rintro ⟨i, z, hz⟩
    exact Proofs.Gain.condExp_otherSigma_eq_sum_label Λ hn hW hdet o hz hφ
      (EventuallyEq.of_eq hfφ) (hf.integrable one_le_two)
  have hL2 : ∀ c, MemLp (f - E c) 2 X.P := fun c => hf.sub (hf.condExp one_le_two)
  -- the two sums, as real sums
  have e2 : ∀ c, ENNReal.ofReal (∫ ω, (f ω - E c ω) ^ 2 ∂X.P) = eLpNorm (f - E c) 2 X.P ^ 2 := by
    intro c
    change ENNReal.ofReal (∫ ω, (f - E c) ω ^ 2 ∂X.P) = _
    rw [ofReal_integral_eq_lintegral_ofReal (hL2 c).integrable_sq
      (ae_of_all _ fun _ => sq_nonneg _), Poincare.eLpNorm_two_sq X.P (hL2 c).aestronglyMeasurable]
  have e1 : ∀ c, ENNReal.ofReal ((∫ ω, |f ω - E c ω| ∂X.P) ^ 2) =
      eLpNorm (f - E c) 1 X.P ^ 2 := by
    intro c
    change ENNReal.ofReal ((∫ ω, |(f - E c) ω| ∂X.P) ^ 2) = _
    rw [ENNReal.ofReal_pow (integral_nonneg fun _ => abs_nonneg _),
      ofReal_integral_eq_lintegral_ofReal ((hL2 c).integrable one_le_two).abs
        (ae_of_all _ fun _ => abs_nonneg _),
      Poincare.eLpNorm_one_eq X.P (hL2 c).aestronglyMeasurable]
  have hs2 : ∑' c, ENNReal.ofReal (∫ ω, (f ω - E c ω) ^ 2 ∂X.P) ≤ ENNReal.ofReal a := by
    simp only [e2]
    rw [Bridge.tsum_blockIdx]
    exact h2
  have hs1 : ∑' c, ENNReal.ofReal ((∫ ω, |f ω - E c ω| ∂X.P) ^ 2) ≤ ENNReal.ofReal b := by
    simp only [e1]
    rw [Bridge.tsum_blockIdx]
    exact h1
  obtain ⟨hsum2, hle2⟩ := summable_tsum_le_of_tsum_ofReal_le
    (fun _ => integral_nonneg fun _ => sq_nonneg _) ha hs2
  obtain ⟨hsum1, hle1⟩ := summable_tsum_le_of_tsum_ofReal_le (fun _ => sq_nonneg _) hb hs1
  obtain ⟨hmain, hzero⟩ := modifiedPoincare_of_labels hMP lab hlab hind hα hα1 hatom hφ
    (EventuallyEq.of_eq hfφ) hf E hE hsum2
  exact ⟨_, _, tsum_nonneg fun _ => sq_nonneg _, hle2, hle1, hmain, hzero⟩

end Labels

end IsotropicVariance.Paper.Proofs.Gain.Printed
