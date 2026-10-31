/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Labels
public import IsotropicVariance.Infra.Resampling.ConditionalPair
import IsotropicVariance.Paper.Proofs.Gain.BridgeInfo
import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry

/-!
# Section `sec:gain`: resampling a block given its label

For a set `G` of the noise and a finite label `ℓ` determined by the noise in `G`,
`pairLaw N G ℓ` draws two outcomes independently from the conditional law of the noise given the
noise off `G` and the label (`Infra.Resampling.labelPairLaw`, the retained information being
`Retained N G ℓ`).

* `retainedKernel_inter_ae`: if the information of `G` and of `Gᶜ` are independent, the
  conditional law of an event `A ∩ C`, `A` in `G`, `C` off `G`, is `1_C · P(A | ℓ)`.
* `pairLaw_prod`: hence `P'((A ∩ C) × (B ∩ D)) = Σ_v P(A | ℓ = v) P(B | ℓ = v) P(ℓ = v) P(C ∩ D)`.
* `isBlockCoupling_pairLaw`, `isLabelResampling_pairLaw`: the pair is a coupling of the block
  (`IsBlockCoupling`), and a resampling given the label (`IsLabelResampling`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Gain.Bridge

open IsotropicVariance.Paper IsotropicVariance.Infra.Resampling

universe u

/-! ### The conditional law of a standard Borel variable given a label -/

section Generic

variable {E Λ : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
  [MeasurableSpace Λ] (μ : Measure E) [IsProbabilityMeasure μ] (π : E → Λ)

/-- The pair law of a rectangle: `∫ κ(A) κ(B)` over the label law. -/
theorem labelPairLaw_prod {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    labelPairLaw μ π (A ×ˢ B) =
      ∫⁻ l, labelKernel μ π l A * labelKernel μ π l B ∂(μ.map π) := by
  rw [labelPairLaw, Measure.bind_apply (hA.prod hB) (Kernel.aemeasurable _)]
  refine lintegral_congr fun l => ?_
  rw [Kernel.prod_apply, Measure.prod_prod]

/-- The disintegration: `∫_T κ(S) d(π_* μ) = μ(π⁻¹ T ∩ S)`. -/
theorem setLIntegral_labelKernel (hπ : Measurable π) {T : Set Λ} (hT : MeasurableSet T)
    {S : Set E} (hS : MeasurableSet S) :
    ∫⁻ l in T, labelKernel μ π l S ∂(μ.map π) = μ (π ⁻¹' T ∩ S) := by
  have h := compProd_map_condDistrib (μ := μ) (Y := id) hπ.aemeasurable aemeasurable_id
  have h2 : (μ.map π ⊗ₘ condDistrib id π μ) (T ×ˢ S) =
      (μ.map fun a => (π a, id a)) (T ×ˢ S) := by rw [h]
  rw [Measure.compProd_apply_prod hT hS,
    Measure.map_apply (hπ.prodMk measurable_id) (hT.prod hS)] at h2
  exact h2

/-- The conditional law of `S` is a measurable `h` of the label as soon as `h` has the
disintegration integrals of `S`. -/
theorem labelKernel_ae_eq_of_setLIntegral (hπ : Measurable π) {S : Set E} (hS : MeasurableSet S)
    {h : Λ → ℝ≥0∞} (hh : Measurable h)
    (H : ∀ T, MeasurableSet T → ∫⁻ l in T, h l ∂(μ.map π) = μ (π ⁻¹' T ∩ S)) :
    ∀ᵐ l ∂(μ.map π), labelKernel μ π l S = h l :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (Kernel.measurable_coe _ hS) hh
    fun T hT _ => (setLIntegral_labelKernel μ π hπ hT hS).trans (H T hT).symm

end Generic

/-! ### Finite labels -/

section Fibers

variable {Ω : Type*} [MeasurableSpace Ω] {V : Type*} [Fintype V] {ℓ : Ω → V}

/-- A function to a countable type with measurable fibers is measurable for the discrete
σ-algebra. -/
theorem measurable_top_of_fibers {α : Type*} {mα : MeasurableSpace α} {W : Type*} [Countable W]
    {f : α → W} (h : ∀ w, MeasurableSet (f ⁻¹' {w})) : @Measurable α W mα ⊤ f :=
  fun s _ => by
    rw [← biUnion_preimage_singleton]
    exact MeasurableSet.biUnion (to_countable s) fun w _ => h w

/-- Splitting a set integral along the fibers of a finite label. -/
theorem setLIntegral_eq_sum_fibers (hℓ : ∀ v, MeasurableSet (ℓ ⁻¹' {v})) (P : Measure Ω)
    {Y : Set Ω} (hY : MeasurableSet Y) (F : Ω → ℝ≥0∞) :
    ∫⁻ ω in Y, F ω ∂P = ∑ v, ∫⁻ ω in Y ∩ ℓ ⁻¹' {v}, F ω ∂P := by
  have hU : Y = ⋃ v, Y ∩ ℓ ⁻¹' {v} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => ⟨ℓ ω, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  conv_lhs => rw [hU]
  rw [lintegral_iUnion (fun v => hY.inter (hℓ v)), tsum_fintype]
  intro v w hvw
  exact (Disjoint.preimage ℓ (disjoint_singleton.2 hvw)).mono inter_subset_right
    inter_subset_right

/-- Splitting a measure along the fibers of a finite label. -/
theorem measure_eq_sum_fibers (hℓ : ∀ v, MeasurableSet (ℓ ⁻¹' {v})) (P : Measure Ω)
    {Y : Set Ω} (hY : MeasurableSet Y) : P Y = ∑ v, P (Y ∩ ℓ ⁻¹' {v}) := by
  rw [← setLIntegral_one, setLIntegral_eq_sum_fibers hℓ P hY]
  simp only [setLIntegral_one]

end Fibers

/-! ### The retained information -/

section Retained

variable {m : ℕ} (N : NoiseModel.{u} m) (G : Set (Pt m)) {V : Type} (ℓ : N.Ω → V)

/-- The noise, remembered only through its information off `G` and the label `ℓ`. -/
def Retained (N : NoiseModel.{u} m) (_G : Set (Pt m)) {V : Type} (_ℓ : N.Ω → V) : Type u :=
  N.Ω

/-- The retained information: the noise off `G` and the label. -/
instance : MeasurableSpace (Retained N G ℓ) := N.info Gᶜ ⊔ MeasurableSpace.comap ℓ ⊤

/-- The quotient map to the retained information. -/
def toRetained (N : NoiseModel.{u} m) (G : Set (Pt m)) {V : Type} (ℓ : N.Ω → V) :
    N.Ω → Retained N G ℓ := id

local instance : Nonempty N.Ω := nonempty_of_isProbabilityMeasure N.P

/-- Resampling the noise in `G` given the noise off `G` and the label `ℓ`: two outcomes drawn
independently from the conditional law of the noise given the retained information. -/
noncomputable def pairLaw : Measure (N.Ω × N.Ω) := labelPairLaw N.P (toRetained N G ℓ)

/-- The conditional law of the noise given the retained information. -/
noncomputable def retainedKernel : ProbabilityTheory.Kernel (Retained N G ℓ) N.Ω :=
  labelKernel N.P (toRetained N G ℓ)

/-- The pair law is a probability. -/
instance : IsProbabilityMeasure (pairLaw N G ℓ) := by
  unfold pairLaw
  infer_instance

variable {N G ℓ}

/-- An event of the noise off `G` is retained. -/
theorem measurableSet_retained_of_compl {C : Set N.Ω} (hC : MeasurableSet[N.info Gᶜ] C) :
    @MeasurableSet (Retained N G ℓ) _ C :=
  le_sup_left (a := N.info Gᶜ) C hC

/-- The label is retained. -/
theorem measurable_label_retained : @Measurable (Retained N G ℓ) V _ ⊤ ℓ :=
  Measurable.of_comap_le le_sup_right

/-- The fibers of the label are events. -/
theorem measurableSet_fiber (hℓ : ∀ v, MeasurableSet[N.info G] (ℓ ⁻¹' {v})) (v : V) :
    MeasurableSet (ℓ ⁻¹' {v}) :=
  N.info_le G _ (hℓ v)

variable [Fintype V] (hℓ : ∀ v, MeasurableSet[N.info G] (ℓ ⁻¹' {v}))
include hℓ

/-- The quotient map is measurable. -/
theorem measurable_toRetained : Measurable (toRetained N G ℓ) := fun s hs =>
  (sup_le (N.info_le Gᶜ) (measurable_top_of_fibers fun v => measurableSet_fiber hℓ v).comap_le) s hs

/-- The old draw has the law of the noise. -/
theorem pairLaw_map_fst : MeasurePreserving Prod.fst (pairLaw N G ℓ) N.P :=
  ⟨measurable_fst, labelPairLaw_map_fst _ _ (measurable_toRetained hℓ)⟩

/-- The new draw has the law of the noise. -/
theorem pairLaw_map_snd : MeasurePreserving Prod.snd (pairLaw N G ℓ) N.P :=
  ⟨measurable_snd, labelPairLaw_map_snd _ _ (measurable_toRetained hℓ)⟩

omit [Fintype V] hℓ in
/-- **The retained events.** An event of the retained information is, on each fiber of the
label, an event of the noise off `G`. -/
theorem exists_of_measurableSet_retained {T : Set (Retained N G ℓ)} (hT : MeasurableSet T) :
    ∃ D : V → Set N.Ω, (∀ v, MeasurableSet[N.info Gᶜ] (D v)) ∧ ∀ ω, ω ∈ T ↔ ω ∈ D (ℓ ω) := by
  classical
  let 𝒮 : MeasurableSpace N.Ω :=
    { MeasurableSet' := fun T => ∃ D : V → Set N.Ω, (∀ v, MeasurableSet[N.info Gᶜ] (D v)) ∧
        ∀ ω, ω ∈ T ↔ ω ∈ D (ℓ ω)
      measurableSet_empty := ⟨fun _ => ∅, fun _ => @MeasurableSet.empty _ (N.info Gᶜ),
        fun _ => Iff.rfl⟩
      measurableSet_compl := fun T ⟨D, hD, hTD⟩ =>
        ⟨fun v => (D v)ᶜ, fun v => (hD v).compl, fun ω => by simp [hTD ω]⟩
      measurableSet_iUnion := fun f hf => by
        choose D hD hfD using hf
        exact ⟨fun v => ⋃ n, D n v, fun v => MeasurableSet.iUnion fun n => hD n v,
          fun ω => by simp [hfD _ ω]⟩ }
  have hle : (inferInstance : MeasurableSpace (Retained N G ℓ)) ≤ 𝒮 := by
    refine sup_le (fun C hC => ⟨fun _ => C, fun _ => hC, fun _ => Iff.rfl⟩) ?_
    rintro _ ⟨U, -, rfl⟩
    refine ⟨fun v => if v ∈ U then univ else ∅, fun v => ?_, fun ω => ?_⟩
    · show MeasurableSet[N.info Gᶜ] (if v ∈ U then univ else ∅)
      split_ifs
      · exact @MeasurableSet.univ _ (N.info Gᶜ)
      · exact @MeasurableSet.empty _ (N.info Gᶜ)
    · by_cases h : ℓ ω ∈ U <;>
        simp only [h, ite_true, ite_false, mem_univ, iff_true, mem_empty_iff_false, iff_false] <;>
        exact h
  exact hle T hT

omit [Fintype V] in
/-- `P(ℓ = v, A, C) = P(ℓ = v, A) P(C)` for `A` in `G` and `C` off `G`. -/
theorem measure_fiber_inter (hind : Indep (N.info G) (N.info Gᶜ) N.P) (v : V) {A C : Set N.Ω}
    (hA : MeasurableSet[N.info G] A) (hC : MeasurableSet[N.info Gᶜ] C) :
    N.P (ℓ ⁻¹' {v} ∩ A ∩ C) = N.P (ℓ ⁻¹' {v} ∩ A) * N.P C :=
  (Indep_iff _ _ _).1 hind _ _ ((hℓ v).inter hA) hC

/-- **The conditional law given the retained information.** For `A` in `G` and `C` off `G`, the
conditional probability of `A ∩ C` is `1_C P(A | ℓ)`. -/
theorem retainedKernel_inter_ae (hind : Indep (N.info G) (N.info Gᶜ) N.P) {A C : Set N.Ω}
    (hA : MeasurableSet[N.info G] A) (hC : MeasurableSet[N.info Gᶜ] C) :
    ∀ᵐ ω ∂N.P, retainedKernel N G ℓ (toRetained N G ℓ ω) (A ∩ C) =
      C.indicator 1 ω * N.P[A | ℓ ⁻¹' {ℓ ω}] := by
  have hπ := measurable_toRetained hℓ
  have hA' := N.info_le G A hA
  have hC' := N.info_le Gᶜ C hC
  set h : Retained N G ℓ → ℝ≥0∞ := fun ω => C.indicator 1 ω * N.P[A | ℓ ⁻¹' {ℓ ω}] with hdef
  have hg : Measurable fun ω : Retained N G ℓ => N.P[A | ℓ ⁻¹' {ℓ ω}] :=
    (measurable_from_top (f := fun v : V => N.P[A | ℓ ⁻¹' {v}])).comp measurable_label_retained
  have hh : Measurable h :=
    (measurable_one.indicator (measurableSet_retained_of_compl hC)).mul hg
  have hmeas : Measurable fun ω : N.Ω => h (toRetained N G ℓ ω) := hh.comp hπ
  refine ae_of_ae_map hπ.aemeasurable (labelKernel_ae_eq_of_setLIntegral N.P _ hπ
    (hA'.inter hC') hh fun T hT => ?_)
  obtain ⟨D, hD, hTD⟩ := exists_of_measurableSet_retained hT
  have hT' : MeasurableSet (toRetained N G ℓ ⁻¹' T) := hπ hT
  rw [setLIntegral_map hT hh hπ, setLIntegral_eq_sum_fibers (measurableSet_fiber hℓ) N.P hT',
    measure_eq_sum_fibers (measurableSet_fiber hℓ) N.P (hT'.inter (hA'.inter hC'))]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib : toRetained N G ℓ ⁻¹' T ∩ ℓ ⁻¹' {v} = D v ∩ ℓ ⁻¹' {v} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨(hTD ω).1 h1, rfl⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨(hTD ω).2 h1, rfl⟩
  have hDv := N.info_le _ _ (hD v)
  have hset : toRetained N G ℓ ⁻¹' T ∩ (A ∩ C) ∩ ℓ ⁻¹' {v} = ℓ ⁻¹' {v} ∩ A ∩ (D v ∩ C) := by
    rw [inter_right_comm, hfib]
    ext ω
    simp only [mem_inter_iff]
    tauto
  rw [hfib, hset, measure_fiber_inter hℓ hind v hA ((hD v).inter hC)]
  calc ∫⁻ ω in D v ∩ ℓ ⁻¹' {v}, h (toRetained N G ℓ ω) ∂N.P
      = ∫⁻ ω in D v ∩ ℓ ⁻¹' {v}, C.indicator (fun _ => N.P[A | ℓ ⁻¹' {v}]) ω ∂N.P := by
        refine setLIntegral_congr_fun (hDv.inter (measurableSet_fiber hℓ v)) fun ω hω => ?_
        have hv : ℓ ω = v := hω.2
        simp only [hdef, toRetained, id, hv]
        by_cases hωC : ω ∈ C <;> simp [hωC]
    _ = N.P[A | ℓ ⁻¹' {v}] * N.P (C ∩ (D v ∩ ℓ ⁻¹' {v})) := by
        rw [lintegral_indicator_const hC', Measure.restrict_apply hC']
    _ = N.P[A | ℓ ⁻¹' {v}] * (N.P (ℓ ⁻¹' {v}) * N.P (D v ∩ C)) := by
        have := measure_fiber_inter hℓ hind v (A := univ) MeasurableSet.univ ((hD v).inter hC)
        rw [inter_univ] at this
        rw [← this]
        congr 2
        ext ω
        simp only [mem_inter_iff]
        tauto
    _ = N.P (ℓ ⁻¹' {v} ∩ A) * N.P (D v ∩ C) := by
        rw [← mul_assoc, cond_mul_eq_inter (measurableSet_fiber hℓ v)]

/-- **The pair law of rectangles.** For `A, B` in `G` and `C, D` off `G`,
`P'((A ∩ C) × (B ∩ D)) = Σ_v P(A | ℓ = v) P(B | ℓ = v) P(ℓ = v) P(C ∩ D)`. -/
theorem pairLaw_prod (hind : Indep (N.info G) (N.info Gᶜ) N.P) {A B C D : Set N.Ω}
    (hA : MeasurableSet[N.info G] A) (hB : MeasurableSet[N.info G] B)
    (hC : MeasurableSet[N.info Gᶜ] C) (hD : MeasurableSet[N.info Gᶜ] D) :
    pairLaw N G ℓ ((A ∩ C) ×ˢ (B ∩ D)) =
      ∑ v, N.P[A | ℓ ⁻¹' {v}] * N.P[B | ℓ ⁻¹' {v}] * N.P (ℓ ⁻¹' {v}) * N.P (C ∩ D) := by
  have hπ := measurable_toRetained hℓ
  have hA' := N.info_le G A hA
  have hB' := N.info_le G B hB
  have hC' := N.info_le Gᶜ C hC
  have hD' := N.info_le Gᶜ D hD
  have hκ : ∀ {S : Set N.Ω}, MeasurableSet S →
      Measurable fun l : Retained N G ℓ => labelKernel N.P (toRetained N G ℓ) l S :=
    fun hS => Kernel.measurable_coe _ hS
  rw [pairLaw, labelPairLaw_prod _ _ (hA'.inter hC') (hB'.inter hD'),
    lintegral_map (f := fun l => labelKernel N.P (toRetained N G ℓ) l (A ∩ C) *
      labelKernel N.P (toRetained N G ℓ) l (B ∩ D))
      ((hκ (hA'.inter hC')).mul (hκ (hB'.inter hD'))) hπ]
  have hae := (retainedKernel_inter_ae hℓ hind hA hC).and (retainedKernel_inter_ae hℓ hind hB hD)
  rw [lintegral_congr_ae (hae.mono fun ω hω => by
      change retainedKernel N G ℓ (toRetained N G ℓ ω) (A ∩ C) *
        retainedKernel N G ℓ (toRetained N G ℓ ω) (B ∩ D) = _
      rw [hω.1, hω.2])]
  have hpt : ∀ ω, C.indicator 1 ω * N.P[A | ℓ ⁻¹' {ℓ ω}] *
      (D.indicator 1 ω * N.P[B | ℓ ⁻¹' {ℓ ω}]) =
      (C ∩ D).indicator (fun ω => N.P[A | ℓ ⁻¹' {ℓ ω}] * N.P[B | ℓ ⁻¹' {ℓ ω}]) ω := by
    intro ω
    by_cases hωC : ω ∈ C <;> by_cases hωD : ω ∈ D <;> simp [hωC, hωD, mul_comm]
  simp_rw [hpt]
  rw [lintegral_indicator (hC'.inter hD'),
    setLIntegral_eq_sum_fibers (measurableSet_fiber hℓ) N.P (hC'.inter hD')]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib := measurableSet_fiber hℓ v
  rw [setLIntegral_congr_fun ((hC'.inter hD').inter hfib)
      (g := fun _ => N.P[A | ℓ ⁻¹' {v}] * N.P[B | ℓ ⁻¹' {v}])
      (fun ω hω => by rw [show ℓ ω = v from hω.2]),
    setLIntegral_const]
  have := measure_fiber_inter hℓ hind v (A := univ) MeasurableSet.univ (hC.inter hD)
  rw [inter_univ] at this
  rw [show C ∩ D ∩ ℓ ⁻¹' {v} = ℓ ⁻¹' {v} ∩ (C ∩ D) from inter_comm _ _, this]
  ring

end Retained

/-! ### The couplings on the product of two copies of the noise -/

section Couplings

variable {m : ℕ} (X : Setting.{u} m) {G : Set (Pt m)} {V : Type} [Fintype V] {ℓ : X.Ω → V}

local instance : Nonempty X.Ω := nonempty_of_isProbabilityMeasure X.P

/-- An event of the noise off `G` happens for both draws or for neither, almost surely. -/
theorem pairLaw_ae_mem_iff (hℓ : ∀ v, MeasurableSet[X.info G] (ℓ ⁻¹' {v})) {C : Set X.Ω}
    (hC : MeasurableSet[X.info Gᶜ] C) :
    ∀ᵐ p ∂pairLaw X.toNoiseModel G ℓ, (p.1 ∈ C ↔ p.2 ∈ C) := by
  have h := labelPairLaw_ae_real_eq X.P (toRetained X.toNoiseModel G ℓ)
    (measurable_toRetained hℓ) (f := C.indicator (1 : Retained X.toNoiseModel G ℓ → ℝ))
    (measurable_one.indicator (measurableSet_retained_of_compl hC))
  refine h.mono fun p hp => ?_
  by_cases h1 : p.1 ∈ C <;> by_cases h2 : p.2 ∈ C <;>
    simp_all [toRetained, Set.indicator]

/-- The label is the same for both draws, almost surely. -/
theorem pairLaw_ae_label_eq (hℓ : ∀ v, MeasurableSet[X.info G] (ℓ ⁻¹' {v})) :
    ∀ᵐ p ∂pairLaw X.toNoiseModel G ℓ, ℓ p.2 = ℓ p.1 := by
  have h : ∀ v, ∀ᵐ p ∂pairLaw X.toNoiseModel G ℓ,
      (ℓ ⁻¹' {v}).indicator (1 : X.Ω → ℝ) p.1 = (ℓ ⁻¹' {v}).indicator 1 p.2 := fun v =>
    labelPairLaw_ae_real_eq X.P (toRetained X.toNoiseModel G ℓ) (measurable_toRetained hℓ)
      (f := (ℓ ⁻¹' {v}).indicator (1 : Retained X.toNoiseModel G ℓ → ℝ))
      (measurable_one.indicator (measurable_label_retained (measurableSet_singleton v)))
  filter_upwards [ae_all_iff.2 h] with p hp
  by_contra hne
  have := hp (ℓ p.1)
  rw [Set.indicator_of_mem (show p.1 ∈ ℓ ⁻¹' {ℓ p.1} from rfl),
    Set.indicator_of_notMem (show p.2 ∉ ℓ ⁻¹' {ℓ p.1} from hne)] at this
  exact one_ne_zero this

/-- The pair law is a coupling of `G`: exchangeable draws with the law of the noise, agreeing
off `G`, the pair in `G` independent of the old noise off `G`. -/
theorem isBlockCoupling_pairLaw (hG : MeasurableSet G) (hGfr : volume (frontier G) = 0)
    (hℓ : ∀ v, MeasurableSet[X.info G] (ℓ ⁻¹' {v})) :
    X.IsBlockCoupling G (pairLaw X.toNoiseModel G ℓ) Prod.fst Prod.snd := by
  have hind := indep_info_compl X.toNoiseModel hG hGfr
  refine ⟨pairLaw_map_fst hℓ, pairLaw_map_snd hℓ, ?_, fun C hC => pairLaw_ae_mem_iff X hℓ hC,
    ?_⟩
  · change (pairLaw X.toNoiseModel G ℓ).map id = _
    rw [Measure.map_id]
    exact (labelPairLaw_map_swap _ _).symm
  · -- independence through the rectangles
    set p₁ : Set (Set (X.Ω × X.Ω)) := {s | ∃ A B, MeasurableSet[X.info G] A ∧
      MeasurableSet[X.info G] B ∧ s = Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B} with hp₁
    have hπ₁ : IsPiSystem p₁ := by
      rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ -
      refine ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', ?_⟩
      ext p
      simp only [mem_inter_iff, mem_preimage]
      tauto
    have hgen₁ : (X.info G).comap Prod.fst ⊔ (X.info G).comap Prod.snd =
        MeasurableSpace.generateFrom p₁ := by
      apply le_antisymm
      · refine sup_le ?_ ?_
        · rintro _ ⟨A, hA, rfl⟩
          refine MeasurableSpace.measurableSet_generateFrom ⟨A, univ, hA,
            @MeasurableSet.univ _ (X.info G), ?_⟩
          simp
        · rintro _ ⟨B, hB, rfl⟩
          refine MeasurableSpace.measurableSet_generateFrom ⟨univ, B,
            @MeasurableSet.univ _ (X.info G), hB, ?_⟩
          simp
      · refine MeasurableSpace.generateFrom_le ?_
        rintro _ ⟨A, B, hA, hB, rfl⟩
        exact (le_sup_left (b := (X.info G).comap Prod.snd) _
          (MeasurableSpace.measurableSet_comap.2 ⟨A, hA, rfl⟩)).inter
          (le_sup_right (a := (X.info G).comap Prod.fst) _
            (MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩))
    have hle₁ : (X.info G).comap Prod.fst ⊔ (X.info G).comap Prod.snd ≤
        (inferInstance : MeasurableSpace (X.Ω × X.Ω)) :=
      sup_le ((MeasurableSpace.comap_mono (X.info_le G)).trans measurable_fst.comap_le)
        ((MeasurableSpace.comap_mono (X.info_le G)).trans measurable_snd.comap_le)
    have hle₂ : (X.info Gᶜ).comap Prod.fst ≤ (inferInstance : MeasurableSpace (X.Ω × X.Ω)) :=
      (MeasurableSpace.comap_mono (X.info_le Gᶜ)).trans measurable_fst.comap_le
    refine IndepSets.indep hle₁ hle₂ hπ₁ (@MeasurableSpace.isPiSystem_measurableSet _
      ((X.info Gᶜ).comap Prod.fst)) hgen₁ (@MeasurableSpace.generateFrom_measurableSet _
      ((X.info Gᶜ).comap Prod.fst)).symm ?_
    rw [IndepSets_iff]
    intro t₁ t₂ ht₁ ht₂
    obtain ⟨A, B, hA, hB, rfl⟩ := ht₁
    obtain ⟨C, hC, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht₂
    have h1 : Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B ∩ Prod.fst ⁻¹' C = (A ∩ C) ×ˢ (B ∩ univ) := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
      tauto
    have h2 : Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B = (A ∩ univ) ×ˢ (B ∩ univ) := by
      ext p
      simp
    have h3 : (pairLaw X.toNoiseModel G ℓ) (Prod.fst ⁻¹' C) = X.P C :=
      (pairLaw_map_fst hℓ).measure_preimage (X.info_le Gᶜ C hC).nullMeasurableSet
    rw [h1, h2, h3, pairLaw_prod hℓ hind hA hB hC (@MeasurableSet.univ _ (X.info Gᶜ)),
      pairLaw_prod hℓ hind hA hB (@MeasurableSet.univ _ (X.info Gᶜ))
        (@MeasurableSet.univ _ (X.info Gᶜ)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp

/-- The pair law for the label of a block is a resampling of the block given its label. -/
theorem isLabelResampling_pairLaw (Λ : X.LabelFamily) {n W : ℝ} {L : ℕ}
    (hdet : Λ.IsDetermined n W L) (i : ℕ) (z : Fin m → ℤ) :
    X.IsLabelResampling Λ n W L i z
      (pairLaw X.toNoiseModel (block n W L i z) (Λ.label i z)) Prod.fst Prod.snd := by
  have hℓ : ∀ v, MeasurableSet[X.info (block n W L i z)] (Λ.label i z ⁻¹' {v}) := hdet i z
  have hind := indep_info_compl X.toNoiseModel (measurableSet_block n W L i z)
    (volume_frontier_block n W L i z)
  refine ⟨isBlockCoupling_pairLaw X (measurableSet_block n W L i z)
    (volume_frontier_block n W L i z) hℓ, pairLaw_ae_label_eq X hℓ, ?_⟩
  intro A B hA hB v
  have hfib := hℓ v
  have hset₁ : {ω : X.Ω × X.Ω | ω.1 ∈ A ∧ ω.2 ∈ B ∧ Λ.label i z ω.1 = v} =
      ((A ∩ Λ.label i z ⁻¹' {v}) ∩ univ) ×ˢ (B ∩ univ) := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_inter_iff, mem_preimage, mem_singleton_iff,
      mem_univ, and_true]
    tauto
  have hfst : ∀ S : Set X.Ω, MeasurableSet S →
      (pairLaw X.toNoiseModel (block n W L i z) (Λ.label i z)) {ω | ω.1 ∈ S} = X.P S :=
    fun S hS => (pairLaw_map_fst hℓ).measure_preimage hS.nullMeasurableSet
  have hset₂ : ∀ S : Set X.Ω, {ω : X.Ω × X.Ω | ω.1 ∈ S ∧ Λ.label i z ω.1 = v} =
      {ω | ω.1 ∈ S ∩ Λ.label i z ⁻¹' {v}} := fun S => by
    ext p
    simp
  have hlab : {ω : X.Ω × X.Ω | Λ.label i z ω.1 = v} = {ω | ω.1 ∈ Λ.label i z ⁻¹' {v}} := by
    ext p
    simp
  have hfib' := X.info_le _ _ hfib
  rw [hset₁, hset₂, hset₂, hlab, hfst _ hfib', hfst _ ((X.info_le _ _ hA).inter hfib'),
    hfst _ ((X.info_le _ _ hB).inter hfib'),
    pairLaw_prod hℓ hind (hA.inter hfib) hB (@MeasurableSet.univ _ (X.info _))
      (@MeasurableSet.univ _ (X.info _)), univ_inter, measure_univ, Finset.sum_mul]
  rw [Finset.sum_eq_single v]
  · -- the term of the value `v`
    have hc : ∀ S, X.P[S | Λ.label i z ⁻¹' {v}] * X.P (Λ.label i z ⁻¹' {v}) =
        X.P (Λ.label i z ⁻¹' {v} ∩ S) := fun S => cond_mul_eq_inter hfib' S X.P
    have hAv : X.P[A ∩ Λ.label i z ⁻¹' {v} | Λ.label i z ⁻¹' {v}] =
        X.P[A | Λ.label i z ⁻¹' {v}] := by
      rw [cond_apply hfib', cond_apply hfib', inter_comm A, ← inter_assoc, inter_self]
    rw [hAv, mul_one]
    calc X.P[A | Λ.label i z ⁻¹' {v}] * X.P[B | Λ.label i z ⁻¹' {v}] *
          X.P (Λ.label i z ⁻¹' {v}) * X.P (Λ.label i z ⁻¹' {v})
        = (X.P[A | Λ.label i z ⁻¹' {v}] * X.P (Λ.label i z ⁻¹' {v})) *
          (X.P[B | Λ.label i z ⁻¹' {v}] * X.P (Λ.label i z ⁻¹' {v})) := by ring
      _ = X.P (A ∩ Λ.label i z ⁻¹' {v}) * X.P (B ∩ Λ.label i z ⁻¹' {v}) := by
        rw [hc, hc, inter_comm _ A, inter_comm _ B]
  · -- the other values do not contribute
    intro w _ hw
    have h0 : X.P[A ∩ Λ.label i z ⁻¹' {v} | Λ.label i z ⁻¹' {w}] = 0 := by
      rw [cond_apply (X.info_le _ _ (hℓ w))]
      have : Λ.label i z ⁻¹' {w} ∩ (A ∩ Λ.label i z ⁻¹' {v}) = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        intro h1 _ h2
        exact hw (h1.symm.trans h2)
      rw [this, measure_empty, mul_zero]
    rw [h0]
    simp
  · intro h
    exact absurd (Finset.mem_univ v) h

end Couplings

end IsotropicVariance.Paper.Proofs.Gain.Bridge
