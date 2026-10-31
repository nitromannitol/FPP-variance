/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.BlockReplacement.CondIndep
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Condexp

/-!
# Conditional laws on a standard Borel space

Generic facts behind the characterization of the resampling of Section `sec:gain`, with no noise.
For a sub-σ-algebra `m` of a standard Borel space and the conditional law
`condExpKernel P m`:

* `lintegral_mul_condExpKernel`, `setLIntegral_condExpKernel`: the disintegration.
* `condExpKernel_ae_eq_of_setLIntegral`: a measurable function with the disintegration integrals is
  a version of the conditional law.
* `condExpKernel_sup_ae_eq`: for `s ≤ a` and `c` independent of `a`, an event of `a` has the same
  conditional law given `s ⊔ c` as given `s`.
* `condExpKernel_ae_eq_of_le_aeClosure`: σ-algebras equal up to null sets give the same conditional
  law.
* `setLIntegral_mul_measure_fiber`: conditional independence given a label.

The two draws: for a kernel `κ` equal to `condExpKernel P m`, the law `P ⊗ₘ κ` of the old noise and
the new noise.

* `compProd_prod_eq`: its value on a rectangle, `∫ κ(A) κ(B)`.
* `map_swap_compProd`: it is exchangeable.
* `map_snd_compProd`: the second draw has the law `P`.
* `ae_mem_iff_compProd`: the two draws agree on the events of `m`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Resampling

open Gain.Bridge BlockReplacement

variable {Ω : Type*} {m m₁ m₂ a s c : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The disintegration -/

/-- **The disintegration.** For `f` measurable for `m`, `∫ f(ω) κ(ω, B) dP = ∫_B f dP`. -/
theorem lintegral_mul_condExpKernel (hm : m ≤ mΩ) {f : Ω → ℝ≥0∞} (hf : Measurable[m] f)
    {B : Set Ω} (hB : MeasurableSet B) :
    ∫⁻ ω, f ω * condExpKernel P m ω B ∂P = ∫⁻ ω in B, f ω ∂P := by
  have hκ : Measurable[m] fun ω => f ω * condExpKernel P m ω B :=
    hf.mul (measurable_condExpKernel hB)
  have hF : Measurable[m.prod mΩ] fun p : Ω × Ω => f p.1 * B.indicator 1 p.2 :=
    (hf.comp measurable_fst).mul ((measurable_one.indicator hB).comp measurable_snd)
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have hinner : (fun ω => ∫⁻ b, f (ω, b).1 * B.indicator 1 (ω, b).2 ∂(condExpKernel P m ω)) =
      fun ω => f ω * condExpKernel P m ω B := by
    funext ω
    change ∫⁻ b, f ω * B.indicator 1 b ∂(condExpKernel P m ω) = _
    rw [lintegral_const_mul _ (measurable_one.indicator hB), lintegral_indicator_one hB]
  have h := congrArg (fun ν => ∫⁻ p, f p.1 * B.indicator 1 p.2 ∂ν)
    (compProd_trim_condExpKernel (μ := P) hm)
  rw [Measure.lintegral_compProd hF, @lintegral_map Ω (Ω × Ω) mΩ (m.prod mΩ) P _ _ hF hdiag,
    hinner, lintegral_trim hm hκ] at h
  refine h.trans ?_
  rw [← lintegral_indicator hB]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ B <;> simp [hω, Function.diag]

/-- **The disintegration on sets**: `∫_T κ(ω, B) dP = P(T ∩ B)` for `T` in `m`. -/
theorem setLIntegral_condExpKernel (hm : m ≤ mΩ) {T B : Set Ω} (hT : MeasurableSet[m] T)
    (hB : MeasurableSet B) : ∫⁻ ω in T, condExpKernel P m ω B ∂P = P (T ∩ B) := by
  have hT' := hm _ hT
  have h := lintegral_mul_condExpKernel (P := P) hm (f := T.indicator 1)
    (measurable_const.indicator hT) hB
  rw [lintegral_indicator_one hT', Measure.restrict_apply hT'] at h
  rw [← h, ← lintegral_indicator hT']
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ T <;> simp [hω]

/-- A function measurable for `m` with the integrals of the disintegration is a version of the
conditional law. -/
theorem condExpKernel_ae_eq_of_setLIntegral (hm : m ≤ mΩ) {B : Set Ω} (hB : MeasurableSet B)
    {g : Ω → ℝ≥0∞} (hg : Measurable[m] g)
    (H : ∀ T, MeasurableSet[m] T → ∫⁻ ω in T, g ω ∂P = P (T ∩ B)) :
    ∀ᵐ ω ∂P, condExpKernel P m ω B = g ω := by
  have hκ : Measurable[m] fun ω => condExpKernel P m ω B := measurable_condExpKernel hB
  refine ae_eq_of_ae_eq_trim (hm := hm) ?_
  refine @ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite _ m (P.trim hm) _ _ _ hκ hg
    fun T hT _ => ?_
  rw [setLIntegral_trim hm hκ hT, setLIntegral_trim hm hg hT,
    setLIntegral_condExpKernel hm hT hB, H T hT]

/-- **Conditioning on independent information.** If `s ≤ a` and `c` is independent of `a`, an event
of `a` has the same conditional law given `s ⊔ c` as given `s`. -/
theorem condExpKernel_sup_ae_eq (ha : a ≤ mΩ) (hc : c ≤ mΩ) (hs : s ≤ a) (hac : Indep a c P)
    {B : Set Ω} (hB : MeasurableSet[a] B) :
    ∀ᵐ ω ∂P, condExpKernel P (s ⊔ c) ω B = condExpKernel P s ω B := by
  have hB' := ha _ hB
  have hind : Indep a (c.comap id) P := by rwa [MeasurableSpace.comap_id]
  have hsid : s.comap id ≤ a := by rwa [MeasurableSpace.comap_id]
  obtain ⟨φ, hφ, hφA⟩ := exists_setLIntegral_eq_of_indep (MeasurePreserving.id P) (hs.trans ha) hc
    (indep_of_indep_of_le_left hac hs) ha hsid hind (g := B.indicator 1)
    (measurable_const.indicator hB) (by rw [lintegral_indicator_one hB']; exact measure_ne_top _ _)
  have hφ' : ∀ T, MeasurableSet[s ⊔ c] T → ∫⁻ ω in T, φ ω ∂P = P (T ∩ B) := by
    intro T hT
    have hT' : MeasurableSet T := sup_le (hs.trans ha) hc T hT
    rw [hφA T hT, preimage_id_eq, id_eq, lintegral_indicator_one hB', Measure.restrict_apply hB',
      inter_comm]
  have h₁ := condExpKernel_ae_eq_of_setLIntegral (P := P) (sup_le (hs.trans ha) hc) hB'
    (hφ.mono le_sup_left le_rfl) hφ'
  have h₂ := condExpKernel_ae_eq_of_setLIntegral (P := P) (hs.trans ha) hB' hφ
    fun T hT => hφ' T (le_sup_left (a := s) (b := c) T hT)
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  rw [hω₁, hω₂]

/-- **σ-algebras equal up to null sets** give the same conditional law. -/
theorem condExpKernel_ae_eq_of_le_aeClosure (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ mΩ)
    (h₂₁ : m₂ ≤ aeClosure m₁ P) {B : Set Ω} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P, condExpKernel P m₂ ω B = condExpKernel P m₁ ω B := by
  refine condExpKernel_ae_eq_of_setLIntegral h₂ hB
    ((measurable_condExpKernel hB).mono h₁₂ le_rfl) fun T hT => ?_
  obtain ⟨T', hT', hTT'⟩ := h₂₁ T hT
  rw [setLIntegral_congr hTT', setLIntegral_condExpKernel (h₁₂.trans h₂) hT' hB]
  exact measure_congr (hTT'.symm.inter EventuallyEq.rfl)

/-! ### Conditioning on a label -/

section Label

variable {V : Type*} {ℓ : Ω → V}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] mΩ in
/-- A function measurable for the σ-algebra of a label is constant on the fibers of the label. -/
theorem exists_eq_on_fiber {ψ : Ω → ℝ≥0∞} (hψ : Measurable[MeasurableSpace.comap ℓ ⊤] ψ) (v : V) :
    ∃ c, ∀ ω, ℓ ω = v → ψ ω = c := by
  by_cases hv : ∃ ω₀, ℓ ω₀ = v
  · obtain ⟨ω₀, hω₀⟩ := hv
    refine ⟨ψ ω₀, fun ω hω => ?_⟩
    obtain ⟨t, -, ht⟩ := hψ (measurableSet_singleton (ψ ω₀))
    have h₀ : ω₀ ∈ ℓ ⁻¹' t := by
      rw [ht]
      rfl
    have h₁ : ω ∈ ℓ ⁻¹' t := by
      change ℓ ω ∈ t
      rw [hω, ← hω₀]
      exact h₀
    rw [ht] at h₁
    exact h₁
  · exact ⟨0, fun ω hω => (hv ⟨ω, hω⟩).elim⟩

/-- **Conditional independence given a label.** If `κ(·, B)` is almost surely the conditional
probability of `B` given the label `ℓ`, then on a fiber `Y` of the label and for an event `A`,
`(∫_{A ∩ Y} κ(ω, B)) P(Y) = P(A ∩ Y) P(B ∩ Y)`. -/
theorem setLIntegral_mul_measure_fiber (hℓ : MeasurableSpace.comap ℓ ⊤ ≤ mΩ) {κ : Kernel Ω Ω}
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hκ : ∀ᵐ ω ∂P, κ ω B = condExpKernel P (MeasurableSpace.comap ℓ ⊤) ω B) (v : V) :
    (∫⁻ ω in A ∩ ℓ ⁻¹' {v}, κ ω B ∂P) * P (ℓ ⁻¹' {v}) =
      P (A ∩ ℓ ⁻¹' {v}) * P (B ∩ ℓ ⁻¹' {v}) := by
  have hYσ : MeasurableSet[MeasurableSpace.comap ℓ ⊤] (ℓ ⁻¹' {v}) :=
    ⟨{v}, MeasurableSpace.measurableSet_top, rfl⟩
  have hY : MeasurableSet (ℓ ⁻¹' {v}) := hℓ _ hYσ
  obtain ⟨c, hc⟩ := exists_eq_on_fiber (measurable_condExpKernel (μ := P) hB) v
  have h₁ : ∫⁻ ω in A ∩ ℓ ⁻¹' {v}, κ ω B ∂P = c * P (A ∩ ℓ ⁻¹' {v}) := by
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun_ae (hA.inter hY) ?_
    filter_upwards [hκ] with ω hω hmem
    rw [hω]
    exact hc ω hmem.2
  have h₂ : P (B ∩ ℓ ⁻¹' {v}) = c * P (ℓ ⁻¹' {v}) := by
    rw [inter_comm, ← setLIntegral_condExpKernel hℓ hYσ hB, ← setLIntegral_const]
    exact setLIntegral_congr_fun hY fun ω hω => hc ω hω
  rw [h₁, h₂]
  ring

end Label

/-! ### The two draws -/

section Pair

variable {κ : Kernel Ω Ω}

/-- The disintegration for the kernel `κ`. -/
theorem setLIntegral_kernel (hm : m ≤ mΩ) (hκ : ∀ ω, κ ω = condExpKernel P m ω) {T B : Set Ω}
    (hT : MeasurableSet[m] T) (hB : MeasurableSet B) : ∫⁻ ω in T, κ ω B ∂P = P (T ∩ B) := by
  simp_rw [hκ]
  exact setLIntegral_condExpKernel hm hT hB

variable [IsMarkovKernel κ]

/-- The law of the two draws on a rectangle: `P ⊗ κ (A × B) = ∫ κ(ω, A) κ(ω, B) dP`. -/
theorem compProd_prod_eq (hm : m ≤ mΩ) (hκ : ∀ ω, κ ω = condExpKernel P m ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (P ⊗ₘ κ) (A ×ˢ B) = ∫⁻ ω, κ ω A * κ ω B ∂P := by
  rw [Measure.compProd_apply_prod hA hB]
  simp_rw [hκ]
  rw [← lintegral_mul_condExpKernel (P := P) hm (measurable_condExpKernel hB) hA]
  exact lintegral_congr fun ω => mul_comm _ _

/-- **The two draws are exchangeable.** -/
theorem map_swap_compProd (hm : m ≤ mΩ) (hκ : ∀ ω, κ ω = condExpKernel P m ω) :
    (P ⊗ₘ κ).map Prod.swap = P ⊗ₘ κ := by
  refine Measure.ext_prod fun {A B} hA hB => ?_
  rw [Measure.map_apply measurable_swap (hA.prod hB), preimage_swap_prod,
    compProd_prod_eq hm hκ hB hA, compProd_prod_eq hm hκ hA hB]
  exact lintegral_congr fun ω => mul_comm _ _

/-- **The second draw has the law `P`.** -/
theorem map_snd_compProd (hm : m ≤ mΩ) (hκ : ∀ ω, κ ω = condExpKernel P m ω) :
    (P ⊗ₘ κ).map Prod.snd = P := by
  have h : (P ⊗ₘ κ).map Prod.fst = P := Measure.fst_compProd P κ
  conv_lhs => rw [← map_swap_compProd hm hκ]
  rw [Measure.map_map measurable_snd measurable_swap]
  exact h

/-- **The two draws agree on the events of `m`.** -/
theorem ae_mem_iff_compProd (hm : m ≤ mΩ) (hκ : ∀ ω, κ ω = condExpKernel P m ω) {C : Set Ω}
    (hC : MeasurableSet[m] C) : ∀ᵐ p ∂(P ⊗ₘ κ), (p.1 ∈ C ↔ p.2 ∈ C) := by
  have hC' := hm _ hC
  have h₁ : (P ⊗ₘ κ) (C ×ˢ Cᶜ) = 0 := by
    rw [Measure.compProd_apply_prod hC' hC'.compl, setLIntegral_kernel hm hκ hC hC'.compl]
    simp
  have h₂ : (P ⊗ₘ κ) (Cᶜ ×ˢ C) = 0 := by
    rw [Measure.compProd_apply_prod hC'.compl hC',
      setLIntegral_kernel hm hκ (@MeasurableSet.compl _ _ m hC) hC']
    simp
  have h := measure_union_null h₁ h₂
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) h
  by_cases h₁ : p.1 ∈ C <;> by_cases h₂ : p.2 ∈ C <;> simp_all

end Pair

end IsotropicVariance.Paper.Proofs.Resampling
