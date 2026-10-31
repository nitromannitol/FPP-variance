/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.EfronStein.Conditional
import CurvatureVariance.Infra.EfronStein.CountableProduct

/-!
# Efron–Stein given the labels of countably many coordinates

As in the continuum library, `IsotropicVariance.Infra.EfronStein.AllLabels`. This is the
conditional form of [BLM03, Proposition 1], extended to countably many variables by martingale
convergence, that the third paragraph of [AB26, proof of Lemma 6.3] uses, and so the second bound
of Lemma `lem:residual`. The cited `CurvatureVariance.blm_proposition1` enters through
`evariance_le_half_tsum_resampleEnergy`. The changes:

* `evariance_le_half_tsum_resampleEnergy` is `evariance_le_half_tsum_resampleEnergy` of
  `CurvatureVariance.Infra.EfronStein.CountableProduct`, since the lattice's theorem of that name does
  not use `CurvatureVariance.blm_proposition1`;
* `enorm_sq_eq_ofReal_sq` is the lattice's `enorm_sub_sq_eq_ofReal`.

On the lattice, the coordinates are the weights of the blocks of the `K` slabs (the fibers of
`Paper.Gain.LabelResidual.cellOf`), with the weights of the other edges as one more coordinate, and
the label of a block, read on its weights, takes its values in the finite set of the values of
`X_G`. Lemma `lem:labels`, in the form `Paper.Gain.IsLabelFamily`, gives what the theorem assumes:
the fields `dep`, `finite` and `measurableSet` of `IsBlockLabel`. Every value having probability at
least `α_L` is not needed here. It is used by [AB26, Proposition 1.3].

Let `P = Measure.infinitePi μ` be a countable product, and let each coordinate carry a label with
countably many values. `lintegral_sub_condExp_allLabelSigma_le` is the conditional Efron–Stein
inequality given the labels of all the coordinates:
`E Var(F | all labels) ≤ ½ ∑ᵢ E ∫ (F x - F (x[i ↦ y]))² d(μᵢ[·|ℓᵢ = ℓᵢ(xᵢ)])(y)`,
for every square-integrable `F`, with no assumption on the sum.

The fibers of infinitely many labels are null, so the argument on the fibers
(`lintegral_sub_condExp_labelSigma_le_of_fibers`) covers finitely many labels. The passage is the
extension of the inequality to countably many variables by martingale convergence. Average `F` over
the coordinates outside a finite set `J`, to get
`Φ = partialIntegral μ J F`. On a fiber of the labels of `J`, the law is a product law with the
laws `μ i` off `J`, and Efron–Stein applied to `Φ` has energies bounded by those of `F` at the
coordinates of `J`, and zero off `J`. Since `E[Φ | labels of J]` is measurable for the labels of
all the coordinates, the best-approximation property of the conditional expectation
(`lintegral_sub_condExp_le`) and `‖Φ - F‖₂ → 0` (`tendsto_lintegral_sub_partialIntegral`,
Lévy's upward theorem and the Pythagorean identity) give the inequality for `F`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CurvatureVariance.Infra.EfronStein

/-! ### The conditional expectation as a projection -/

section Projection

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

/-- **The Pythagorean identity**: `E (f - E[f | m])² + E E[f | m]² = E f²`. -/
theorem lintegral_sub_condExp_add (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ ω, ENNReal.ofReal ((f ω - P[f | m] ω) ^ 2) ∂P + ∫⁻ ω, ENNReal.ofReal (P[f | m] ω ^ 2) ∂P =
      ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P := by
  have hc := hf.condExp (m := m) one_le_two
  have hvar : ∫ ω, Var[f; P | m] ω ∂P = ∫ ω, f ω ^ 2 ∂P - ∫ ω, P[f | m] ω ^ 2 ∂P := by
    have hsub : ∫ ω, (P[f ^ 2 | m] - P[f | m] ^ 2 : Ω → ℝ) ω ∂P =
        ∫ ω, P[f ^ 2 | m] ω ∂P - ∫ ω, P[f | m] ω ^ 2 ∂P :=
      integral_sub integrable_condExp hc.integrable_sq
    rw [integral_congr_ae (condVar_ae_eq_condExp_sq_sub_sq_condExp hm hf), hsub,
      integral_condExp hm]
    rfl
  have hnn : 0 ≤ ∫ ω, Var[f; P | m] ω ∂P := by
    rw [condVar, integral_condExp hm]
    exact integral_nonneg fun ω => sq_nonneg _
  have hc0 : 0 ≤ ∫ ω, P[f | m] ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  rw [← ofReal_integral_condVar hm hf, ← ofReal_integral_eq_lintegral_ofReal hc.integrable_sq
    (ae_of_all _ fun ω => sq_nonneg _), ← ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (ae_of_all _ fun ω => sq_nonneg _), ← ENNReal.ofReal_add hnn hc0, hvar, sub_add_cancel]

/-- **Best approximation**: `E[f | m]` is at least as close to `f` as every `m`-measurable `g`. -/
theorem lintegral_sub_condExp_le (hm : m ≤ mΩ) {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (hgm : StronglyMeasurable[m] g) :
    ∫⁻ ω, ENNReal.ofReal ((f ω - P[f | m] ω) ^ 2) ∂P ≤ ∫⁻ ω, ENNReal.ofReal ((f ω - g ω) ^ 2) ∂P := by
  have hfi := hf.integrable one_le_two
  have hgi := hg.integrable one_le_two
  have hc : P[f - g | m] =ᵐ[P] P[f | m] - g :=
    (condExp_sub hfi hgi m).trans
      (EventuallyEq.sub EventuallyEq.rfl (EventuallyEq.of_eq (condExp_of_stronglyMeasurable hm hgm hgi)))
  have h := lintegral_sub_condExp_add hm (hf.sub hg)
  calc ∫⁻ ω, ENNReal.ofReal ((f ω - P[f | m] ω) ^ 2) ∂P
      = ∫⁻ ω, ENNReal.ofReal (((f - g) ω - P[f - g | m] ω) ^ 2) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hc] with ω hω
        rw [hω, Pi.sub_apply, Pi.sub_apply]
        congr 1
        ring
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((f - g) ω ^ 2) ∂P := le_of_le_of_eq le_self_add h
    _ = _ := rfl

omit [IsProbabilityMeasure P] in
/-- The `L²` norm, as an integral in `ℝ≥0∞`. -/
theorem eLpNorm_two_eq_rpow {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    eLpNorm f 2 P = (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_sub_sq_eq_ofReal]

end Projection

variable {I : Type*} [DecidableEq I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-! ### Martingale convergence in `L²` -/

omit [DecidableEq I] in
/-- **The partial integrals converge to the functional in `L²`**, along an increasing exhaustion of
the index set. -/
theorem tendsto_lintegral_sub_partialIntegral {S : ℕ → Set I} (hmono : Monotone S)
    (hcov : ∀ i : I, ∃ n, i ∈ S n) {F : ((i : I) → X i) → ℝ} (hFm : Measurable F)
    (hF : MemLp F 2 (Measure.infinitePi μ)) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal ((F ω - partialIntegral μ (S n) F ω) ^ 2)
      ∂Measure.infinitePi μ) atTop (𝓝 0) := by
  set P := Measure.infinitePi μ with hP
  have hFi : Integrable F P := hF.integrable one_le_two
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal ((F ω - partialIntegral μ (S n) F ω) ^ 2) ∂P
    with ha
  set b : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal (partialIntegral μ (S n) F ω ^ 2) ∂P with hb
  set c : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (F ω ^ 2) ∂P with hc
  have hctop : c ≠ ⊤ := by
    rw [hc, ← ofReal_integral_eq_lintegral_ofReal hF.integrable_sq
      (ae_of_all _ fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hsum : ∀ n, a n + b n = c := fun n => by
    have hae := partialIntegral_ae_eq_condExp μ (S n) hFm hFi
    refine Eq.trans ?_ (lintegral_sub_condExp_add (coordinateSigma_le X (S n)) hF)
    congr 1
    · exact lintegral_congr_ae (by filter_upwards [hae] with ω hω; rw [hω])
    · exact lintegral_congr_ae (by filter_upwards [hae] with ω hω; rw [hω])
  have hconv := tendsto_partialIntegral μ hmono hcov hFm hFi
  have hlim : ∀ᵐ ω ∂P, ENNReal.ofReal (F ω ^ 2) =
      liminf (fun n => ENNReal.ofReal (partialIntegral μ (S n) F ω ^ 2)) atTop := by
    filter_upwards [hconv] with ω hω
    have : Tendsto (fun n => ENNReal.ofReal (partialIntegral μ (S n) F ω ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (F ω ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)
    exact this.liminf_eq.symm
  have hfatou : c ≤ liminf b atTop := by
    calc c = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (partialIntegral μ (S n) F ω ^ 2)) atTop ∂P :=
          lintegral_congr_ae hlim
      _ ≤ liminf b atTop := lintegral_liminf_le fun n =>
          ((measurable_partialIntegral μ (S n) hFm).pow_const 2).ennreal_ofReal
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hc0 : c = 0
  · exact Eventually.of_forall fun n => by
      rw [← hsum n] at hc0
      rw [(add_eq_zero.mp hc0).1]
      exact zero_le
  have hlt : c - ε < liminf b atTop :=
    (ENNReal.sub_lt_self hctop hc0 hε.ne').trans_le hfatou
  filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
  have h₁ : a n + (c - ε) ≤ c := (add_le_add le_rfl hn.le).trans_eq (hsum n)
  have h₂ := ENNReal.le_sub_of_add_le_right (ne_top_of_le_ne_top hctop tsub_le_self) h₁
  exact h₂.trans tsub_tsub_le

/-! ### The labels of all the coordinates -/

section Labels

variable {Λ : I → Type*} [∀ i, MeasurableSpace (Λ i)]

/-- The σ-algebra generated by the labels of all the coordinates. -/
@[instance_reducible]
def allLabelSigma (ℓ : (i : I) → X i → Λ i) : MeasurableSpace ((i : I) → X i) :=
  ⨆ i, MeasurableSpace.comap (fun x => ℓ i (x i)) inferInstance

omit [DecidableEq I] in
theorem allLabelSigma_le {ℓ : (i : I) → X i → Λ i} (hℓ : ∀ i, Measurable (ℓ i)) :
    allLabelSigma ℓ ≤ MeasurableSpace.pi :=
  iSup_le fun i => ((hℓ i).comp (measurable_pi_apply i)).comap_le

omit [DecidableEq I] [∀ i, MeasurableSpace (X i)] in
/-- The labels of a finite set are among the labels of all the coordinates. -/
theorem labelSigma_le_allLabelSigma (ℓ : (i : I) → X i → Λ i) (J : Finset I) :
    labelSigma ℓ J ≤ allLabelSigma ℓ := by
  rw [labelSigma, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup (fun i => MeasurableSpace.comap (fun x : (i : I) → X i => ℓ i (x i)) inferInstance)
    (j : I)

omit [DecidableEq I] in
/-- The partial integral over the coordinates outside `S` reads only the laws outside `S`. -/
theorem partialIntegral_congr_measure {ν : (i : I) → Measure (X i)}
    [∀ i, IsProbabilityMeasure (ν i)] {S : Set I} (hν : ∀ i, i ∉ S → ν i = μ i)
    {F : ((i : I) → X i) → ℝ} (hFm : Measurable F) :
    partialIntegral ν S F = partialIntegral μ S F := by
  classical
  funext ω
  let f : (i : I) → X i → X i := fun i a => if i ∈ S then ω i else a
  have hf : ∀ i, Measurable (f i) := fun i => by
    by_cases hi : i ∈ S
    · simp only [f, hi, ite_true]
      exact measurable_const
    · simp only [f, hi, ite_false]
      exact measurable_id'
  have hr : (resample S ω : ((i : I) → X i) → (i : I) → X i) = fun x i => f i (x i) := by
    funext x i
    simp only [resample, f]
  have hmap : (Measure.infinitePi ν).map (resample S ω) =
      (Measure.infinitePi μ).map (resample S ω) := by
    rw [hr, Measure.infinitePi_map_pi ν hf, Measure.infinitePi_map_pi μ hf]
    congr 1
    funext i
    by_cases hi : i ∈ S
    · have hc : f i = fun _ => ω i := funext fun a => by simp only [f, hi, ite_true]
      simp only [hc, Measure.map_const, measure_univ]
    · rw [hν i hi]
  have hrm : Measurable (resample S ω : ((i : I) → X i) → (i : I) → X i) := by
    rw [hr]
    exact measurable_pi_iff.mpr fun i => (hf i).comp (measurable_pi_apply i)
  have hFs := hFm.aestronglyMeasurable (μ := (Measure.infinitePi μ).map (resample S ω))
  calc ∫ η, F (resample S ω η) ∂Measure.infinitePi ν
      = ∫ x, F x ∂(Measure.infinitePi ν).map (resample S ω) :=
        (integral_map hrm.aemeasurable (by rw [hmap]; exact hFs)).symm
    _ = ∫ x, F x ∂(Measure.infinitePi μ).map (resample S ω) := by rw [hmap]
    _ = ∫ η, F (resample S ω η) ∂Measure.infinitePi μ := integral_map hrm.aemeasurable hFs

/-- **Efron–Stein on a fiber.** For a product law `ν` with the laws `μ i` off `J`, the variance of
the average of `F` over the coordinates off `J` is at most half the sum over `J` of the energies of
`F`. -/
theorem evariance_partialIntegral_le {ν : (i : I) → Measure (X i)}
    [∀ i, IsProbabilityMeasure (ν i)] [Countable I] (J : Finset I) (hν : ∀ i, i ∉ J → ν i = μ i)
    {F : ((i : I) → X i) → ℝ} (hFm : Measurable F) (hF : MemLp F 2 (Measure.infinitePi ν)) :
    evariance (partialIntegral μ J F) (Measure.infinitePi ν) ≤
      ∑' i, ∫⁻ x, ∫⁻ y, (if i ∈ J then
          2⁻¹ * ENNReal.ofReal ((F x - F (Function.update x i y)) ^ 2) else 0)
        ∂ν i ∂Measure.infinitePi ν := by
  rw [← partialIntegral_congr_measure μ (S := J) (fun i hi => hν i hi) hFm]
  set Φ := partialIntegral ν (J : Set I) F with hΦ
  have hFi := hF.integrable one_le_two
  have hΦm : Measurable Φ := measurable_partialIntegral ν _ hFm
  have hΦ2 : MemLp Φ 2 (Measure.infinitePi ν) :=
    (memLp_two_iff_integrable_sq hΦm.aestronglyMeasurable).mpr
      (integrable_sq_partialIntegral ν _ hFm hFi hF.integrable_sq)
  refine (evariance_le_half_tsum_resampleEnergy ν hΦ2).trans ?_
  rw [ENNReal.div_eq_inv_mul, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun i => ?_
  by_cases hi : i ∈ J
  · simp only [hi, ite_true]
    calc 2⁻¹ * resampleEnergy ν Φ i ≤ 2⁻¹ * resampleEnergy ν F i :=
          mul_le_mul' le_rfl (resampleEnergy_partialIntegral_le ν hi hFm hFi)
      _ = _ := by
          rw [resampleEnergy, ← lintegral_const_mul' _ _ (by simp)]
          exact lintegral_congr fun x => (lintegral_const_mul' _ _ (by simp)).symm
  · have h0 : resampleEnergy ν Φ i = 0 := by
      refine (lintegral_congr fun x => ?_).trans lintegral_zero
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      have : Φ (Function.update x i y) = Φ x := partialIntegral_congr ν _ F fun k hk => by
        have hki : k ≠ i := fun h => hi (h ▸ hk)
        rw [Function.update_of_ne hki]
      rw [this, sub_self]
      simp
    rw [h0, mul_zero]
    exact zero_le

variable [∀ i, MeasurableSingletonClass (Λ i)] [∀ i, Countable (Λ i)]

omit [DecidableEq I] [∀ i, IsProbabilityMeasure (μ i)] [∀ i, MeasurableSpace (Λ i)]
  [∀ i, MeasurableSingletonClass (Λ i)] in
/-- Almost every coordinate has a label of positive probability. -/
theorem ae_measure_label_ne_zero (ℓ : (i : I) → X i → Λ i) (i : I) :
    ∀ᵐ a ∂μ i, μ i (ℓ i ⁻¹' {ℓ i a}) ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have hsub : {a | μ i (ℓ i ⁻¹' {ℓ i a}) = 0} ⊆
      ⋃ c ∈ {c : Λ i | μ i (ℓ i ⁻¹' {c}) = 0}, ℓ i ⁻¹' {c} := fun a ha =>
    Set.mem_biUnion (show ℓ i a ∈ {c : Λ i | μ i (ℓ i ⁻¹' {c}) = 0} from ha) rfl
  exact measure_mono_null hsub
    ((measure_biUnion_null_iff (Set.to_countable _)).mpr fun c hc => hc)

/-- **Efron–Stein given the labels of all the coordinates.** For labels with countably many
values on countably many independent coordinates, and `F` square integrable, the mean conditional
variance of `F` given all the labels is at most half the sum over the coordinates of the mean square
change of `F` when the coordinate `i` is replaced by a sample of its conditional law given its
label. -/
theorem lintegral_sub_condExp_allLabelSigma_le [Countable I] {ℓ : (i : I) → X i → Λ i}
    (hℓ : ∀ i, Measurable (ℓ i)) {F : ((i : I) → X i) → ℝ} (hFm : Measurable F)
    (hF : MemLp F 2 (Measure.infinitePi μ)) :
    ∫⁻ x, ENNReal.ofReal ((F x - (Measure.infinitePi μ)[F | allLabelSigma ℓ] x) ^ 2)
        ∂Measure.infinitePi μ ≤
      (∑' i, ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((F x - F (Function.update x i y)) ^ 2)
        ∂(μ i)[|ℓ i ⁻¹' {ℓ i (x i)}] ∂Measure.infinitePi μ) / 2 := by
  classical
  set P := Measure.infinitePi μ with hP
  set R : ℝ≥0∞ := (∑' i, ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((F x - F (Function.update x i y)) ^ 2)
    ∂(μ i)[|ℓ i ⁻¹' {ℓ i (x i)}] ∂P) / 2 with hR
  set T := P[F | allLabelSigma ℓ] with hT
  have hFi : Integrable F P := hF.integrable one_le_two
  -- an exhaustion by finite sets
  obtain ⟨g, hg⟩ := exists_injective_nat I
  have hSfin : ∀ n, ({i | g i < n} : Set I).Finite := fun n =>
    (Set.Finite.preimage hg.injOn (Set.finite_Iio n)).subset fun i hi => hi
  set Sf : ℕ → Finset I := fun n => (hSfin n).toFinset with hSf
  have hmem : ∀ n i, i ∈ Sf n ↔ g i < n := fun n i => by simp [hSf]
  have hmono : Monotone fun n => (Sf n : Set I) := fun a b hab i hi =>
    (hmem b i).mpr (((hmem a i).mp hi).trans_le hab)
  have hcov : ∀ i : I, ∃ n, i ∈ (Sf n : Set I) := fun i =>
    ⟨g i + 1, (hmem _ i).mpr (Nat.lt_succ_self _)⟩
  set Φ : ℕ → ((i : I) → X i) → ℝ := fun n => partialIntegral μ (Sf n : Set I) F with hΦ
  have hΦm : ∀ n, Measurable (Φ n) := fun n => measurable_partialIntegral μ _ hFm
  have hΦ2 : ∀ n, MemLp (Φ n) 2 P := fun n =>
    (memLp_two_iff_integrable_sq (hΦm n).aestronglyMeasurable).mpr
      (integrable_sq_partialIntegral μ _ hFm hFi hF.integrable_sq)
  set G : ℕ → ((i : I) → X i) → ℝ := fun n => P[Φ n | labelSigma ℓ (Sf n)] with hG
  have hG2 : ∀ n, MemLp (G n) 2 P := fun n => (hΦ2 n).condExp one_le_two
  -- the step at a finite set
  have hkey : ∀ n, ∫⁻ x, ENNReal.ofReal ((Φ n x - G n x) ^ 2) ∂P ≤ R := by
    intro n
    have h := lintegral_sub_condExp_labelSigma_le_of_fibers μ hℓ (Sf n) (hΦ2 n)
      (fun i x y => if i ∈ Sf n then
        2⁻¹ * ENNReal.ofReal ((F x - F (Function.update x i y)) ^ 2) else 0)
      fun ν _ hν ⟨s, _, hs, hνs⟩ => evariance_partialIntegral_le μ (Sf n) hν hFm (by
        rw [hνs, ProbabilityTheory.cond]
        exact (hF.restrict _).smul_measure (ENNReal.inv_ne_top.mpr hs))
    refine h.trans ?_
    rw [hR, ENNReal.div_eq_inv_mul, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun i => ?_
    by_cases hi : i ∈ Sf n
    · have hae : ∀ᵐ x ∂P, labelLaw μ ℓ (Sf n) i (x i) = (μ i)[|ℓ i ⁻¹' {ℓ i (x i)}] := by
        filter_upwards [(measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae
          (ae_measure_label_ne_zero μ ℓ i)] with x hx
        simp only [labelLaw, hi, true_and, hx, ne_eq, not_false_eq_true, ite_true]
      rw [← lintegral_const_mul' _ _ (by simp)]
      refine (lintegral_congr_ae ?_).le
      filter_upwards [hae] with x hx
      simp only [hi, ite_true, hx]
      exact lintegral_const_mul' _ _ (by simp)
    · simp only [hi, ite_false, lintegral_zero]
      exact zero_le
  -- the limit
  have he := tendsto_lintegral_sub_partialIntegral μ hmono hcov hFm hF
  have he' : Tendsto (fun n => (∫⁻ ω, ENNReal.ofReal ((F ω - Φ n ω) ^ 2) ∂P) ^ (1 / 2 : ℝ) +
      R ^ (1 / 2 : ℝ)) atTop (𝓝 (R ^ (1 / 2 : ℝ))) := by
    have h0 : Tendsto (fun n => (∫⁻ ω, ENNReal.ofReal ((F ω - Φ n ω) ^ 2) ∂P) ^ (1 / 2 : ℝ)) atTop
        (𝓝 0) := by
      have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp he
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
      exact h
    simpa only [zero_add] using h0.add_const (R ^ (1 / 2 : ℝ))
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hle : ∀ n, (∫⁻ x, ENNReal.ofReal ((F x - T x) ^ 2) ∂P) ^ (1 / 2 : ℝ) ≤
      (∫⁻ ω, ENNReal.ofReal ((F ω - Φ n ω) ^ 2) ∂P) ^ (1 / 2 : ℝ) + R ^ (1 / 2 : ℝ) := by
    intro n
    have hbest := lintegral_sub_condExp_le (allLabelSigma_le hℓ) hF (hG2 n)
      (stronglyMeasurable_condExp.mono (labelSigma_le_allLabelSigma ℓ (Sf n)))
    have htri : eLpNorm (F - G n) 2 P ≤ eLpNorm (F - Φ n) 2 P + eLpNorm (Φ n - G n) 2 P := by
      have h := eLpNorm_add_le (f := F - Φ n) (g := Φ n - G n) (p := 2) (μ := P) (by norm_num)
      rwa [sub_add_sub_cancel] at h
    rw [eLpNorm_two_eq_rpow (hF.sub (hG2 n)).aestronglyMeasurable,
      eLpNorm_two_eq_rpow (hF.sub (hΦ2 n)).aestronglyMeasurable,
      eLpNorm_two_eq_rpow ((hΦ2 n).sub (hG2 n)).aestronglyMeasurable] at htri
    calc (∫⁻ x, ENNReal.ofReal ((F x - T x) ^ 2) ∂P) ^ (1 / 2 : ℝ)
        ≤ (∫⁻ x, ENNReal.ofReal ((F x - G n x) ^ 2) ∂P) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hbest hhalf.le
      _ ≤ _ := htri.trans (add_le_add le_rfl (ENNReal.rpow_le_rpow (hkey n) hhalf.le))
  exact (ENNReal.rpow_le_rpow_iff hhalf).mp (ge_of_tendsto' he' hle)

end Labels

end CurvatureVariance.Infra.EfronStein
