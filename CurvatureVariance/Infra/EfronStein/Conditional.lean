/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.EfronStein.Countable
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.CondVar

/-!
# The conditional Efron–Stein inequality given labels

The inequality on a countable product `P = Measure.infinitePi μ` of arbitrary probability spaces.
Each coordinate `i` of a finite set `J` carries a label `ℓ i (xᵢ)` with values in a countable set.
Given the labels, the coordinates are independent: on each fiber of the label vector the
conditional law of `P` is the product of the conditional laws of the coordinates given their labels
(`cond_labelVector_eq_infinitePi`). Hence, with `labelLaw μ ℓ J i (xᵢ)` the conditional law of the
coordinate `i` given its label (`μ i` for `i ∉ J`), an Efron–Stein bound on every such fiber gives
`E Var(F | labels) ≤ ∑ᵢ E ∫ g i x y d(labelLaw i xᵢ)(y)`
(`lintegral_sub_condExp_labelSigma_le_of_fibers`); with
`g i x y = ½ (F x - F (x[i ↦ y]))²` this is `E Var(F | Π) ≤ ½ ∑_G E (F - F^{(G)})²` when each group
is replaced by an independent sample of its conditional law given its label. `E Var(F | 𝒜)` is
written `∫⁻ ofReal ((F - E[F | 𝒜])²)`; `ofReal_integral_condVar` identifies it with Mathlib's
`∫ Var[F; P | 𝒜]`.

It rests on two facts: conditioning on a variable with countably many values splits
`E Var(F | L)` over the fibers (`lintegral_sub_condExp_comap_eq_tsum`), and conditioning a product
law on a product event gives a product law (`cond_infinitePi_pi`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

namespace CurvatureVariance.Infra.EfronStein

/-! ### Conditioning on a random variable with countably many values -/

section CountablePartition

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSingletonClass Λ]
  [Countable Λ] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSingletonClass Λ] [Countable Λ] in
/-- The fibers of a map are pairwise disjoint. -/
theorem pairwise_disjoint_preimage_singleton (L : Ω → Λ) :
    Pairwise (Function.onFun Disjoint fun c : Λ => L ⁻¹' {c}) := by
  intro i j hij
  exact (Set.disjoint_singleton.2 hij).preimage L

omit [MeasurableSpace Λ] [MeasurableSingletonClass Λ] [IsProbabilityMeasure P] in
/-- A lower integral is the sum of its restrictions to the fibers of a map with measurable fibers
and countably many values. -/
theorem lintegral_eq_tsum_setLIntegral_preimage {L : Ω → Λ}
    (hA : ∀ c, MeasurableSet (L ⁻¹' {c})) (φ : Ω → ℝ≥0∞) :
    ∫⁻ x, φ x ∂P = ∑' c, ∫⁻ x in L ⁻¹' {c}, φ x ∂P := by
  rw [← lintegral_iUnion hA (pairwise_disjoint_preimage_singleton L)]
  have : (⋃ c : Λ, L ⁻¹' {c}) = Set.univ := by ext x; simp
  rw [this, Measure.restrict_univ]

omit [MeasurableSpace Λ] [MeasurableSingletonClass Λ] [Countable Λ] in
/-- Conditioning on an event, integrated back. -/
theorem toReal_measure_mul_integral_cond (s : Set Ω) (F : Ω → ℝ) :
    (P s).toReal * ∫ x, F x ∂(P[|s]) = ∫ x in s, F x ∂P := by
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, smul_eq_mul]
  by_cases h0 : P s = 0
  · simp [h0, Measure.restrict_eq_zero.2 h0]
  · rw [← mul_assoc, ENNReal.toReal_inv, mul_inv_cancel₀, one_mul]
    exact (ENNReal.toReal_pos h0 (measure_ne_top _ _)).ne'

omit [MeasurableSpace Λ] [MeasurableSingletonClass Λ] [Countable Λ] in
/-- Conditioning on an event, integrated back, in `ℝ≥0∞`. -/
theorem mul_lintegral_cond (s : Set Ω) (φ : Ω → ℝ≥0∞) :
    P s * ∫⁻ x, φ x ∂(P[|s]) = ∫⁻ x in s, φ x ∂P := by
  unfold ProbabilityTheory.cond
  rw [lintegral_smul_measure, smul_eq_mul]
  by_cases h0 : P s = 0
  · simp [h0, Measure.restrict_eq_zero.2 h0]
  · rw [← mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

/-- Conditioning on a random variable with countably many values: on the fiber `L = c`, the
conditional expectation is the mean of `F` under the conditional probability given `L = c`. -/
theorem condExp_comap_ae_eq_integral_cond {L : Ω → Λ} (hL : Measurable L) {F : Ω → ℝ}
    (hF : Integrable F P) :
    P[F | MeasurableSpace.comap L inferInstance] =ᵐ[P]
      fun ω => ∫ x, F x ∂(P[|L ⁻¹' {L ω}]) := by
  classical
  set h : Λ → ℝ := fun c => ∫ x, F x ∂(P[|L ⁻¹' {c}]) with hh
  have hA : ∀ c, MeasurableSet (L ⁻¹' {c}) := fun c => hL (measurableSet_singleton c)
  have hg_on : ∀ c, ∀ x ∈ L ⁻¹' {c}, h (L x) = h c := by
    intro c x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rw [hx]
  have hset : ∀ c, ∫ x in L ⁻¹' {c}, h (L x) ∂P = ∫ x in L ⁻¹' {c}, F x ∂P := by
    intro c
    rw [setIntegral_congr_fun (hA c) (fun x hx => hg_on c x hx), setIntegral_const,
      ← toReal_measure_mul_integral_cond]
    rfl
  have hhm : Measurable h := measurable_of_countable h
  have hint : Integrable (fun x => h (L x)) P := by
    refine ⟨(hhm.comp hL).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_eq_tsum_setLIntegral_preimage (fun c => hL (measurableSet_singleton c))]
    calc ∑' c, ∫⁻ x in L ⁻¹' {c}, ‖h (L x)‖ₑ ∂P
        ≤ ∑' c, ∫⁻ x in L ⁻¹' {c}, ‖F x‖ₑ ∂P := by
          refine ENNReal.tsum_le_tsum fun c => ?_
          rw [setLIntegral_congr_fun (hA c) (fun x hx => by rw [hg_on c x hx]),
            setLIntegral_const]
          calc ‖h c‖ₑ * P (L ⁻¹' {c}) = ‖∫ x in L ⁻¹' {c}, F x ∂P‖ₑ := by
                rw [← toReal_measure_mul_integral_cond, enorm_mul,
                  Real.enorm_of_nonneg ENNReal.toReal_nonneg,
                  ENNReal.ofReal_toReal (measure_ne_top _ _), mul_comm]
            _ ≤ _ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ x, ‖F x‖ₑ ∂P := (lintegral_eq_tsum_setLIntegral_preimage (fun c => hL (measurableSet_singleton c)) _).symm
      _ < ∞ := hF.2
  have hm : MeasurableSpace.comap L inferInstance ≤ ‹MeasurableSpace Ω› := hL.comap_le
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hF (fun s _ _ => hint.integrableOn)
    ?_ ?_).symm
  · intro s hs _
    obtain ⟨B, hB, rfl⟩ := hs
    have hU : ∀ f : Ω → ℝ, Integrable f P →
        (∀ c, ∫ x in L ⁻¹' {c}, f x ∂P = ∫ x in L ⁻¹' {c}, F x ∂P) →
        ∫ x in L ⁻¹' B, f x ∂P = ∫ x in L ⁻¹' B, F x ∂P := by
      intro f hf hfc
      have key : ∀ (u : Ω → ℝ), Integrable u P →
          ∫ x in L ⁻¹' B, u x ∂P = ∑' c, ∫ x in L ⁻¹' B ∩ L ⁻¹' {c}, u x ∂P := by
        intro u hu
        have : L ⁻¹' B = ⋃ c : Λ, L ⁻¹' B ∩ L ⁻¹' {c} := by
          ext x; simp
        conv_lhs => rw [this]
        exact integral_iUnion (fun c => (hL hB).inter (hA c))
          (fun i j hij => (pairwise_disjoint_preimage_singleton L hij).mono Set.inter_subset_right Set.inter_subset_right)
          hu.integrableOn
      rw [key f hf, key F hF]
      refine tsum_congr fun c => ?_
      by_cases hc : c ∈ B
      · have : L ⁻¹' B ∩ L ⁻¹' {c} = L ⁻¹' {c} := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun h => h.2, fun h => ⟨h ▸ hc, h⟩⟩
        rw [this]; exact hfc c
      · have : L ⁻¹' B ∩ L ⁻¹' {c} = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro h1 h2; exact hc (h2 ▸ h1)
        rw [this]; simp
    exact hU _ hint hset
  · exact (hhm.comp (comap_measurable L)).stronglyMeasurable.aestronglyMeasurable

/-- The mean conditional variance given a random variable with countably many values, as a sum
over the fibers. -/
theorem lintegral_sub_condExp_comap_eq_tsum {L : Ω → Λ} (hL : Measurable L) {F : Ω → ℝ}
    (hF : MemLp F 2 P) :
    ∫⁻ ω, ENNReal.ofReal ((F ω - P[F | MeasurableSpace.comap L inferInstance] ω) ^ 2) ∂P =
      ∑' c, P (L ⁻¹' {c}) * evariance F (P[|L ⁻¹' {c}]) := by
  have h1 := condExp_comap_ae_eq_integral_cond hL (P := P) (hF.integrable one_le_two)
  have hA : ∀ c, MeasurableSet (L ⁻¹' {c}) := fun c => hL (measurableSet_singleton c)
  rw [lintegral_congr_ae (g := fun x => ENNReal.ofReal
      ((F x - ∫ y, F y ∂(P[|L ⁻¹' {L x}])) ^ 2)) (h1.mono fun x hx => by rw [hx]),
    lintegral_eq_tsum_setLIntegral_preimage (fun c => hL (measurableSet_singleton c))]
  refine tsum_congr fun c => ?_
  rw [evariance_eq_lintegral_ofReal, mul_lintegral_cond]
  refine setLIntegral_congr_fun (hA c) (fun x hx => ?_)
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp only [hx]

end CountablePartition

/-- The mean conditional variance `∫ Var[F; P | m]` in `ℝ≥0∞`: it is the mean square of
`F - E[F | m]`. -/
theorem ofReal_integral_condVar {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsProbabilityMeasure P] {F : Ω → ℝ} (hF : MemLp F 2 P) :
    ENNReal.ofReal (∫ ω, Var[F; P | m] ω ∂P) =
      ∫⁻ ω, ENNReal.ofReal ((F ω - P[F | m] ω) ^ 2) ∂P := by
  have hi : Integrable (fun ω => (F ω - P[F | m] ω) ^ 2) P :=
    (hF.sub (hF.condExp one_le_two)).integrable_sq
  rw [condVar, integral_condExp hm, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  rfl

/-! ### Conditioning a product law on a product event -/

section Product

variable {I : Type*} [DecidableEq I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Conditioning a product law on a product event `{x | ∀ i ∈ J, xᵢ ∈ Bᵢ}` (`J` finite) gives
the product of the conditioned coordinate laws. -/
theorem cond_infinitePi_pi (J : Finset I) {B : (i : I) → Set (X i)}
    (hB : ∀ i ∈ J, MeasurableSet (B i)) (hpos : ∀ i ∈ J, μ i (B i) ≠ 0)
    (ν : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i = if i ∈ J then (μ i)[|B i] else μ i) :
    (Measure.infinitePi μ)[|Set.pi (↑J) B] = Measure.infinitePi ν := by
  classical
  have hA : MeasurableSet (Set.pi (↑J : Set I) B) :=
    MeasurableSet.pi J.countable_toSet (fun i hi => hB i hi)
  have hPA : Measure.infinitePi μ (Set.pi (↑J : Set I) B) = ∏ i ∈ J, μ i (B i) :=
    Measure.infinitePi_pi μ (fun i hi => hB i hi)
  have hne : ∏ i ∈ J, μ i (B i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hpos
  have hnt : ∏ i ∈ J, μ i (B i) ≠ ⊤ :=
    ENNReal.prod_ne_top (fun i _ => measure_ne_top _ _)
  apply Measure.eq_infinitePi ν
  intro s t ht
  rw [cond_apply hA, hPA]
  let t' : (i : I) → Set (X i) := fun i =>
    (if i ∈ J then B i else Set.univ) ∩ (if i ∈ s then t i else Set.univ)
  have hset : Set.pi (↑J : Set I) B ∩ Set.pi (↑s : Set I) t = Set.pi (↑(s ∪ J) : Set I) t' := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe, Finset.mem_union, t']
    constructor
    · rintro ⟨h1, h2⟩ i hi
      refine ⟨?_, ?_⟩
      · split_ifs with h
        · exact h1 i h
        · trivial
      · split_ifs with h
        · exact h2 i h
        · trivial
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have := (h i (Or.inr hi)).1
        simpa [hi] using this
      · have := (h i (Or.inl hi)).2
        simpa [hi] using this
  have hmt' : ∀ i ∈ s ∪ J, MeasurableSet (t' i) := by
    intro i hi
    refine MeasurableSet.inter ?_ ?_
    · split_ifs with h
      · exact hB i h
      · exact MeasurableSet.univ
    · split_ifs with h
      · exact ht i
      · exact MeasurableSet.univ
  rw [hset, Measure.infinitePi_pi μ hmt']
  have hfac : ∀ i ∈ s ∪ J, μ i (t' i) =
      (if i ∈ J then μ i (B i) else 1) * (if i ∈ s then ν i (t i) else 1) := by
    intro i _
    by_cases hJ : i ∈ J <;> by_cases hs : i ∈ s
    · have := hν i
      simp only [t', hJ, hs, ite_true] at this ⊢
      rw [this, ← cond_mul_eq_inter (hB i hJ), mul_comm]
    · simp [t', hJ, hs]
    · simp [t', hJ, hs, hν i]
    · exfalso; simp_all
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  have h1 : ∏ i ∈ s ∪ J, (if i ∈ J then μ i (B i) else 1) = ∏ i ∈ J, μ i (B i) := by
    rw [← Finset.prod_subset (Finset.subset_union_right (s₁ := s) (s₂ := J))]
    · exact Finset.prod_congr rfl (fun i hi => by simp [hi])
    · intro i _ hi; simp [hi]
  have h2 : ∏ i ∈ s ∪ J, (if i ∈ s then ν i (t i) else 1) = ∏ i ∈ s, ν i (t i) := by
    rw [← Finset.prod_subset (Finset.subset_union_left (s₁ := s) (s₂ := J))]
    · exact Finset.prod_congr rfl (fun i hi => by simp [hi])
    · intro i _ hi; simp [hi]
  rw [h1, h2, ← mul_assoc, ENNReal.inv_mul_cancel hne hnt, one_mul]

end Product

/-! ### Efron–Stein given labels -/

section Labels

variable {I : Type*} [DecidableEq I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
  {Λ : I → Type*} [∀ i, MeasurableSpace (Λ i)]

/-- The labels `(ℓ j (x j))_{j ∈ J}` of the coordinates in `J`. -/
def labelVector (ℓ : (i : I) → X i → Λ i) (J : Finset I) (x : (i : I) → X i) :
    (j : J) → Λ j :=
  fun j => ℓ j (x j)

/-- The σ-algebra generated by the labels of the coordinates in `J`. -/
@[instance_reducible]
def labelSigma (ℓ : (i : I) → X i → Λ i) (J : Finset I) : MeasurableSpace ((i : I) → X i) :=
  MeasurableSpace.comap (labelVector ℓ J) inferInstance

omit [DecidableEq I] in
theorem measurable_labelVector {ℓ : (i : I) → X i → Λ i} (hℓ : ∀ i, Measurable (ℓ i))
    (J : Finset I) : Measurable (labelVector ℓ J) :=
  measurable_pi_iff.mpr fun j => (hℓ j).comp (measurable_pi_apply (j : I))

open Classical in
/-- The conditional law of the coordinate `i` given its label `ℓ i a`: for `i ∈ J`, `μ i`
conditioned on `{ℓ i = ℓ i a}` (when this event has positive probability); otherwise `μ i`. -/
def labelLaw (μ : (i : I) → Measure (X i)) (ℓ : (i : I) → X i → Λ i) (J : Finset I) (i : I)
    (a : X i) : Measure (X i) :=
  if i ∈ J ∧ μ i (ℓ i ⁻¹' {ℓ i a}) ≠ 0 then (μ i)[|ℓ i ⁻¹' {ℓ i a}] else μ i

variable (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

omit [∀ i, IsProbabilityMeasure (μ i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Λ i)] in
/-- A fiber of the label vector is a product event. -/
theorem labelVector_preimage_singleton (ℓ : (i : I) → X i → Λ i) (J : Finset I)
    (c : (j : J) → Λ j) :
    labelVector ℓ J ⁻¹' {c} =
      Set.pi ↑J (fun i => if h : i ∈ J then ℓ i ⁻¹' {c ⟨i, h⟩} else Set.univ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe]
  constructor
  · rintro rfl i hi
    simp [hi, labelVector]
  · intro h
    funext j
    have := h j j.2
    simpa [j.2, labelVector] using this

/-- **Given the labels, the coordinates are independent**: the law of `x` conditioned on the
labels `c` of the coordinates in `J` is the product of the laws of the coordinates conditioned on
their labels. -/
theorem cond_labelVector_eq_infinitePi {ℓ : (i : I) → X i → Λ i} (hℓ : ∀ i, Measurable (ℓ i))
    [∀ i, MeasurableSingletonClass (Λ i)] (J : Finset I) (c : (j : J) → Λ j)
    (hc : Measure.infinitePi μ (labelVector ℓ J ⁻¹' {c}) ≠ 0)
    (ν : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i = if h : i ∈ J then (μ i)[|ℓ i ⁻¹' {c ⟨i, h⟩}] else μ i) :
    (Measure.infinitePi μ)[|labelVector ℓ J ⁻¹' {c}] = Measure.infinitePi ν := by
  classical
  set B : (i : I) → Set (X i) := fun i => if h : i ∈ J then ℓ i ⁻¹' {c ⟨i, h⟩} else Set.univ
    with hBdef
  have hBm : ∀ i ∈ J, MeasurableSet (B i) := fun i hi => by
    simp only [hBdef, hi, dite_true]
    exact hℓ i (measurableSet_singleton _)
  rw [labelVector_preimage_singleton] at hc ⊢
  have hpos : ∀ i ∈ J, μ i (B i) ≠ 0 := by
    rw [Measure.infinitePi_pi μ hBm] at hc
    exact Finset.prod_ne_zero_iff.mp hc
  refine cond_infinitePi_pi μ J hBm hpos ν fun i => ?_
  by_cases hi : i ∈ J
  · simp [hν i, hi, hBdef]
  · simp [hν i, hi]

/-- The fibers of the label vector with positive probability: there, every coordinate of `J` has a
label of positive probability. -/
theorem measure_label_ne_zero_of_mem {ℓ : (i : I) → X i → Λ i} (hℓ : ∀ i, Measurable (ℓ i))
    [∀ i, MeasurableSingletonClass (Λ i)] (J : Finset I) (c : (j : J) → Λ j)
    (hc : Measure.infinitePi μ (labelVector ℓ J ⁻¹' {c}) ≠ 0) (i : I) (hi : i ∈ J) :
    μ i (ℓ i ⁻¹' {c ⟨i, hi⟩}) ≠ 0 := by
  classical
  have hBm : ∀ k ∈ J, MeasurableSet
      ((fun k => if h : k ∈ J then ℓ k ⁻¹' {c ⟨k, h⟩} else Set.univ) k) := fun k hk => by
    simp only [hk, dite_true]
    exact hℓ k (measurableSet_singleton _)
  rw [labelVector_preimage_singleton, Measure.infinitePi_pi μ hBm] at hc
  have := Finset.prod_ne_zero_iff.mp hc i hi
  simpa [hi] using this

/-- The general assembly: a fiberwise bound gives a bound for the mean conditional variance given
the labels. The fibers are the conditional laws of `Measure.infinitePi μ` on the events of positive
probability of the labels of `J`, which are product laws with the laws `μ i` off `J`. The bound is
asked only of those laws, which `lintegral_sub_condExp_allLabelSigma_le` needs, as in the continuum
library's `IsotropicVariance.Infra.EfronStein.Conditional`. -/
theorem lintegral_sub_condExp_labelSigma_le_of_fibers [Countable I]
    [∀ i, MeasurableSingletonClass (Λ i)] [∀ i, Countable (Λ i)]
    {ℓ : (i : I) → X i → Λ i} (hℓ : ∀ i, Measurable (ℓ i)) (J : Finset I)
    {F : ((i : I) → X i) → ℝ} (hF : MemLp F 2 (Measure.infinitePi μ))
    (g : (i : I) → ((j : I) → X j) → X i → ℝ≥0∞)
    (hfib : ∀ (ν : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)],
      (∀ i, i ∉ J → ν i = μ i) →
      (∃ s, MeasurableSet s ∧ Measure.infinitePi μ s ≠ 0 ∧
        Measure.infinitePi ν = (Measure.infinitePi μ)[|s]) →
        evariance F (Measure.infinitePi ν) ≤
          ∑' i, ∫⁻ x, ∫⁻ y, g i x y ∂ν i ∂Measure.infinitePi ν) :
    ∫⁻ x, ENNReal.ofReal ((F x - (Measure.infinitePi μ)[F | labelSigma ℓ J] x) ^ 2)
        ∂Measure.infinitePi μ ≤
      ∑' i, ∫⁻ x, ∫⁻ y, g i x y ∂labelLaw μ ℓ J i (x i) ∂Measure.infinitePi μ := by
  classical
  set P := Measure.infinitePi μ with hP
  set L := labelVector ℓ J with hLdef
  have hL : Measurable L := measurable_labelVector hℓ J
  -- the mean conditional variance, fiber by fiber
  rw [labelSigma, lintegral_sub_condExp_comap_eq_tsum hL hF]
  -- split the right side along the fibers
  have hdisj : Pairwise (Function.onFun Disjoint fun c : (j : J) → Λ j => L ⁻¹' {c}) :=
    fun c c' hcc' => Set.disjoint_left.mpr fun x hx hx' =>
      hcc' ((Set.mem_singleton_iff.mp hx).symm.trans (Set.mem_singleton_iff.mp hx'))
  have hunion : (⋃ c : (j : J) → Λ j, L ⁻¹' {c}) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨L x, rfl⟩
  have hsplit : ∀ φ : ((j : I) → X j) → ℝ≥0∞,
      ∫⁻ x, φ x ∂P = ∑' c : (j : J) → Λ j, ∫⁻ x in L ⁻¹' {c}, φ x ∂P := by
    intro φ
    rw [← lintegral_iUnion (fun c => hL (measurableSet_singleton c)) hdisj, hunion,
      Measure.restrict_univ]
  simp_rw [hsplit (fun x => ∫⁻ y, g _ x y ∂labelLaw μ ℓ J _ (x _))]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun c => ?_
  -- one fiber
  by_cases hc : P (L ⁻¹' {c}) = 0
  · rw [hc, zero_mul]
    exact zero_le
  let ν : (i : I) → Measure (X i) := fun i =>
    if h : i ∈ J then (μ i)[|ℓ i ⁻¹' {c ⟨i, h⟩}] else μ i
  have hpos := measure_label_ne_zero_of_mem μ hℓ J c hc
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i => by
    by_cases hi : i ∈ J
    · simp only [ν, hi, dite_true]
      exact cond_isProbabilityMeasure (hpos i hi)
    · simp only [ν, hi, dite_false]
      infer_instance
  have hcond : P[|L ⁻¹' {c}] = Measure.infinitePi ν :=
    cond_labelVector_eq_infinitePi μ hℓ J c hc ν fun i => rfl
  have hlaw : ∀ i, ∀ x ∈ L ⁻¹' {c}, labelLaw μ ℓ J i (x i) = ν i := by
    intro i x hx
    have hx' : ∀ (h : i ∈ J), ℓ i (x i) = c ⟨i, h⟩ := fun h =>
      congrFun (Set.mem_singleton_iff.mp hx) ⟨i, h⟩
    by_cases hi : i ∈ J
    · simp only [labelLaw, ν, hi, dite_true, hx' hi, true_and, hpos i hi, ne_eq,
        not_false_eq_true, ite_true]
    · simp only [labelLaw, ν, hi, dite_false, false_and, ite_false]
  calc P (L ⁻¹' {c}) * evariance F (P[|L ⁻¹' {c}])
      ≤ P (L ⁻¹' {c}) * ∑' i, ∫⁻ x, ∫⁻ y, g i x y ∂ν i ∂(P[|L ⁻¹' {c}]) := by
        rw [hcond]
        gcongr
        exact hfib ν (fun i hi => by simp only [ν, hi, dite_false])
          ⟨L ⁻¹' {c}, hL (measurableSet_singleton c), hc, hcond.symm⟩
    _ = ∑' i, ∫⁻ x in L ⁻¹' {c}, ∫⁻ y, g i x y ∂ν i ∂P := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun i => mul_lintegral_cond _ _
    _ = ∑' i, ∫⁻ x in L ⁻¹' {c}, ∫⁻ y, g i x y ∂labelLaw μ ℓ J i (x i) ∂P := by
        refine tsum_congr fun i => setLIntegral_congr_fun (hL (measurableSet_singleton c)) ?_
        intro x hx
        simp only [hlaw i x hx]

end Labels

end CurvatureVariance.Infra.EfronStein
