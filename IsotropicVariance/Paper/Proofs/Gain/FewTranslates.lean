/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Averaged
public import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry
public import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration

/-!
# Lemma `lem:fewtranslates`: the expectation `E_G` on the noise

The text before Lemma `lem:residual` defines `E_G` as the expectation over the variable `X_G`
alone, the other labels being fixed. Lemma `lem:fewtranslates` is stated on the noise, with
`E_G[f] = X.P[f | Λ.otherSigma K o i z]` (module `IsotropicVariance.Paper.Defs.Averaged`). The
labels of distinct blocks are independent, so the two agree:

* `Setting.LabelFamily.indep_sigma_otherSigma`: the label of a block is independent of the others.
* `Setting.LabelFamily.allSigma_eq_otherSigma_sup`: the information of all labels is that of the
  others and that of the block.
* `condExp_eq_sum_of_indep`: `E[φ(λ, rest) | rest] = Σ_v P(λ = v) φ(v, rest)` for `λ` finite-valued
  and independent of `rest`.
* `condExp_otherSigma_eq_sum_label`: **the identity.** If `f = φ ∘ (X_H)_H` almost surely, then
  almost surely `X.P[f | Λ.otherSigma K o i z] = Σ_v P(X_G = v) φ((X_H)_H with X_G replaced by v)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper

namespace Setting.LabelFamily

variable {m L K : ℕ} {X : Setting.{u} m} (Λ : X.LabelFamily)

/-- The information of all labels is that of the others and that of the block. -/
theorem allSigma_eq_otherSigma_sup (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ}
    (hz : IsBlockIndex L (o i) z) :
    Λ.allSigma K o = Λ.otherSigma K o i z ⊔ Λ.sigma i z := by
  refine le_antisymm (iSup₂_le fun i' z' => iSup_le fun hz' => ?_) (sup_le
    (Λ.otherSigma_le_allSigma K o i z) (le_iSup₂_of_le i z (le_iSup_of_le hz le_rfl)))
  by_cases h : (i', z') = (i, z)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact le_sup_right
  · have hle : Λ.sigma i' z' ≤ Λ.otherSigma K o i z :=
      le_iSup₂_of_le i' z' (le_iSup_of_le hz' (le_iSup_of_le h le_rfl))
    exact hle.trans le_sup_left

/-- The label of a block of the offsets `o` is independent of the labels of the others. -/
theorem indep_sigma_otherSigma {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (hdet : Λ.IsDetermined n W L)
    (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ} (hz : IsBlockIndex L (o i) z) :
    Indep (Λ.sigma i z) (Λ.otherSigma K o i z) X.P := by
  let ι := Proofs.Gain.Bridge.BlockIdx L K o
  let s : ι → MeasurableSpace X.Ω := fun c => Λ.sigma (c.1 : ℕ) (c.2 : Fin m → ℤ)
  have hs : ∀ c, s c ≤ X.measurableSpace := fun c =>
    (Λ.sigma_le hdet (c.1 : ℕ) (c.2 : Fin m → ℤ)).trans (X.info_le _)
  have hI : iIndep s X.P := by
    have h := X.iIndep_info ι (fun c => block n W L (c.1 : ℕ) (c.2 : Fin m → ℤ))
      (fun c => Proofs.Gain.Bridge.measurableSet_block n W L _ _)
      (fun c => Proofs.Gain.Bridge.volume_frontier_block n W L _ _)
      (Proofs.Gain.Bridge.disjoint_interior_blockOf hn.le hW)
    exact iIndep_of_iIndep_of_le h fun c => Λ.sigma_le hdet (c.1 : ℕ) (c.2 : Fin m → ℤ)
  let c₀ : ι := ⟨i, z, hz⟩
  have h := indep_iSup_of_disjoint hs hI (S := {c₀}) (T := {c | c ≠ c₀}) (by simp)
  rw [iSup_singleton] at h
  refine indep_of_indep_of_le_right h ?_
  refine iSup₂_le fun i' z' => iSup_le fun hz' => iSup_le fun hne => ?_
  have hne' : (⟨i', z', hz'⟩ : ι) ≠ c₀ := fun h => hne (by
    have h1 := congrArg Sigma.fst h
    subst h1
    have h2 := Subtype.ext_iff.1 (eq_of_heq (Sigma.mk.inj_iff.1 h).2)
    simp only [Prod.mk.injEq, true_and]
    exact h2)
  exact le_iSup₂_of_le (f := fun c (_ : c ∈ {c | c ≠ c₀}) => s c) ⟨i', z', hz'⟩ hne' le_rfl

end Setting.LabelFamily

namespace Proofs.Gain

/-! ### Integrating out an independent finite-valued variable -/

section Generic

variable {Ω V : Type*} {m₂ mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `E[φ(λ, rest) | rest] = Σ_v P(λ = v) φ(v, rest)` for `λ` finite-valued and independent of
`rest`, written with `h v = φ(v, rest)` measurable for the information `m₂` of `rest`. -/
theorem condExp_eq_sum_of_indep [Fintype V] [IsProbabilityMeasure P] (hm₂ : m₂ ≤ mΩ) (ℓ : Ω → V)
    (hℓ : MeasurableSpace.comap ℓ ⊤ ≤ mΩ) (hind : Indep (MeasurableSpace.comap ℓ ⊤) m₂ P)
    (h : V → Ω → ℝ) (hm : ∀ v, StronglyMeasurable[m₂] (h v)) (hi : ∀ v, Integrable (h v) P) :
    P[fun ω => h (ℓ ω) ω | m₂] =ᵐ[P] fun ω => ∑ v, P.real (ℓ ⁻¹' {v}) * h v ω := by
  classical
  have hset : ∀ v, MeasurableSet[MeasurableSpace.comap ℓ ⊤] (ℓ ⁻¹' {v}) := fun v =>
    ⟨{v}, MeasurableSpace.measurableSet_top, rfl⟩
  let ind : V → Ω → ℝ := fun v => (ℓ ⁻¹' {v}).indicator 1
  have hindm : ∀ v, StronglyMeasurable[MeasurableSpace.comap ℓ ⊤] (ind v) := fun v =>
    stronglyMeasurable_const.indicator (hset v)
  have hindi : ∀ v, Integrable (ind v) P := fun v =>
    (integrable_const (1 : ℝ)).indicator (hℓ _ (hset v))
  have hsplit : (fun ω => h (ℓ ω) ω) = ∑ v, ind v * h v := by
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, ind]
    rw [Finset.sum_eq_single (ℓ ω)]
    · simp
    · intro v _ hv
      have : ω ∉ ℓ ⁻¹' {v} := fun hω => hv hω.symm
      simp [indicator_of_notMem this]
    · simp
  have hprod : ∀ v, Integrable (ind v * h v) P := fun v => by
    refine (hi v).bdd_mul (c := 1) (hindm v |>.mono hℓ).aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases hω : ω ∈ ℓ ⁻¹' {v} <;> simp [ind, hω]
  have hone : ∀ v, P[ind v * h v | m₂] =ᵐ[P] fun ω => P.real (ℓ ⁻¹' {v}) * h v ω := fun v => by
    have h1 := condExp_mul_of_stronglyMeasurable_right (hm v) (hprod v) (hindi v)
    have h2 := condExp_indep_eq hℓ hm₂ (hindm v) hind
    have h3 : ∫ ω, ind v ω ∂P = P.real (ℓ ⁻¹' {v}) := by
      rw [integral_indicator_one (hℓ _ (hset v))]
    filter_upwards [h1, h2] with ω h1 h2
    rw [h1, Pi.mul_apply, h2, h3]
  rw [hsplit]
  refine (condExp_finsetSum (fun v _ => hprod v) m₂).trans ?_
  have hall := ae_all_iff.2 hone
  filter_upwards [hall] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ => hω v

/-- A function of an independent pair: if `h v` is measurable for `m₂`, the integrability of
`h (ℓ ω) ω` gives that of `h v` at every value `v` of positive probability. -/
theorem integrable_of_measure_ne_zero [IsProbabilityMeasure P] (hm₂ : m₂ ≤ mΩ) (ℓ : Ω → V)
    (hℓ : MeasurableSpace.comap ℓ ⊤ ≤ mΩ) (hind : Indep (MeasurableSpace.comap ℓ ⊤) m₂ P)
    (h : V → Ω → ℝ) (hm : ∀ v, StronglyMeasurable[m₂] (h v))
    (hi : Integrable (fun ω => h (ℓ ω) ω) P) {v : V} (hv : P (ℓ ⁻¹' {v}) ≠ 0) :
    Integrable (h v) P := by
  classical
  have hset : MeasurableSet[MeasurableSpace.comap ℓ ⊤] (ℓ ⁻¹' {v}) :=
    ⟨{v}, MeasurableSpace.measurableSet_top, rfl⟩
  have hsm : StronglyMeasurable (h v) := (hm v).mono hm₂
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace hℓ hm₂ hind
    (f := (ℓ ⁻¹' {v}).indicator 1) (g := fun ω => ‖h v ω‖ₑ)
    (measurable_const.indicator hset) (hm v).enorm
  have hle : ∫⁻ ω, (ℓ ⁻¹' {v}).indicator 1 ω * ‖h v ω‖ₑ ∂P ≤ ∫⁻ ω, ‖h (ℓ ω) ω‖ₑ ∂P := by
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ ℓ ⁻¹' {v}
    · have hω' : ℓ ω = v := hω
      simp [hω, hω']
    · simp [hω]
  rw [hprod, lintegral_indicator_one (hℓ _ hset)] at hle
  have hfin := hle.trans_lt hi.2
  exact lt_top_iff_ne_top.2 fun htop => by
    rw [htop, ENNReal.mul_top hv] at hfin
    exact lt_irrefl _ hfin

end Generic

/-! ### The expectation `E_G` -/

section Label

variable {m L K : ℕ} {X : Setting.{u} m}

/-- The labels `(X_H)_H` of the blocks with offsets `o`. -/
def labelsOf (Λ : X.LabelFamily) (o : Fin K → Fin m → Fin L) (ω : X.Ω) :
    Bridge.BlockIdx L K o → Λ.V :=
  fun c => Λ.label (c.1 : ℕ) (c.2 : Fin m → ℤ) ω

/-- With a block's label fixed at a value, the labels are determined by the others. -/
theorem measurable_update_labelsOf (Λ : X.LabelFamily) [MeasurableSpace Λ.V]
    [MeasurableSingletonClass Λ.V] (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ}
    (hz : IsBlockIndex L (o i) z) [DecidableEq (Bridge.BlockIdx L K o)] (v : Λ.V) :
    Measurable[Λ.otherSigma K o i z] fun ω =>
      Function.update (labelsOf Λ o ω) (⟨i, z, hz⟩ : Bridge.BlockIdx L K o) v := by
  refine @Measurable.of_eval _ _ _ (Λ.otherSigma K o i z) _ _ fun c => ?_
  by_cases hc : c = ⟨i, z, hz⟩
  · subst hc
    simp only [Function.update_self]
    exact @measurable_const _ _ _ (Λ.otherSigma K o i z) _
  · simp only [Function.update_of_ne hc]
    obtain ⟨i', z', hz'⟩ := c
    have hne : ((i' : Fin K), (z' : Fin m → ℤ)) ≠ (i, z) := fun h => hc (by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl)
    have hle : Λ.sigma i' z' ≤ Λ.otherSigma K o i z :=
      le_iSup₂_of_le i' z' (le_iSup_of_le hz' (le_iSup_of_le hne le_rfl))
    refine Measurable.mono (ma := Λ.sigma i' z') ?_ hle le_rfl
    exact fun t _ => ⟨t, MeasurableSpace.measurableSet_top, rfl⟩

/-- **`E_G` is the expectation over `X_G` alone** (text before Lemma `lem:residual`): if
`f = φ ∘ (X_H)_H` almost surely, with `φ` measurable, then almost surely
`X.P[f | Λ.otherSigma K o i z] = Σ_v P(X_G = v) φ((X_H)_H with X_G replaced by v)`.

Each `φ((X_H)_H with X_G replaced by v)` is integrable when `v` has positive probability
(`integrable_of_measure_ne_zero`). The terms of the other values vanish, so `φ` need not be
bounded. -/
theorem condExp_otherSigma_eq_sum_label (Λ : X.LabelFamily) [MeasurableSpace Λ.V]
    [MeasurableSingletonClass Λ.V] {n W : ℝ} (hn : 0 < n) (hW : 0 < W)
    (hdet : Λ.IsDetermined n W L) (o : Fin K → Fin m → Fin L) {i : Fin K} {z : Fin m → ℤ}
    (hz : IsBlockIndex L (o i) z) [DecidableEq (Bridge.BlockIdx L K o)]
    {φ : (Bridge.BlockIdx L K o → Λ.V) → ℝ} (hφ : Measurable φ) {f : X.Ω → ℝ}
    (hf : f =ᵐ[X.P] fun ω => φ (labelsOf Λ o ω)) (hfi : Integrable f X.P) :
    X.P[f | Λ.otherSigma K o i z] =ᵐ[X.P] fun ω =>
      ∑ v, X.P.real (Λ.label i z ⁻¹' {v}) *
        φ (Function.update (labelsOf Λ o ω) (⟨i, z, hz⟩ : Bridge.BlockIdx L K o) v) := by
  classical
  set ℓ := Λ.label i z with hℓ_def
  set O := Λ.otherSigma K o i z with hO_def
  have hσle : Λ.sigma i z ≤ X.measurableSpace :=
    (Λ.sigma_le hdet i z).trans (X.info_le _)
  have hOle : O ≤ X.measurableSpace :=
    (Λ.otherSigma_le_allSigma K o i z).trans (Λ.allSigma_le hdet K o)
  have hind : Indep (MeasurableSpace.comap ℓ ⊤) O X.P := Λ.indep_sigma_otherSigma hn hW hdet o hz
  set c₀ : Bridge.BlockIdx L K o := ⟨i, z, hz⟩ with hc₀
  set h : Λ.V → X.Ω → ℝ := fun v ω => φ (Function.update (labelsOf Λ o ω) c₀ v) with hh
  have hm : ∀ v, StronglyMeasurable[O] (h v) := fun v =>
    (hφ.comp (measurable_update_labelsOf Λ o hz v)).stronglyMeasurable
  have hself : ∀ ω, h (ℓ ω) ω = φ (labelsOf Λ o ω) := fun ω => by
    simp only [hh]
    congr 1
    exact Function.update_eq_self c₀ (labelsOf Λ o ω)
  have hif : Integrable (fun ω => h (ℓ ω) ω) X.P :=
    hfi.congr (hf.mono fun ω hω => by rw [hω]; exact (hself ω).symm)
  set h' : Λ.V → X.Ω → ℝ := fun v => if X.P (ℓ ⁻¹' {v}) ≠ 0 then h v else 0 with hh'
  have hm' : ∀ v, StronglyMeasurable[O] (h' v) := fun v => by
    simp only [hh']
    split_ifs
    · exact hm v
    · exact stronglyMeasurable_zero
  have hi' : ∀ v, Integrable (h' v) X.P := fun v => by
    simp only [hh']
    split_ifs with hv
    · exact integrable_of_measure_ne_zero hOle ℓ hσle hind h hm hif hv
    · exact integrable_zero _ _ _
  have hae : f =ᵐ[X.P] fun ω => h' (ℓ ω) ω := by
    have hnull : ∀ᵐ ω ∂X.P, X.P (ℓ ⁻¹' {ℓ ω}) ≠ 0 := by
      have e : {ω | ¬ X.P (ℓ ⁻¹' {ℓ ω}) ≠ 0} =
          ⋃ v ∈ {v : Λ.V | X.P (ℓ ⁻¹' {v}) = 0}, ℓ ⁻¹' {v} := by
        ext ω
        simp
      rw [ae_iff, e]
      exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun v hv => hv
    filter_upwards [hf, hnull] with ω hω hne
    simp only [hh', ite_eq_left hne]
    rw [hω, hself]
  refine (condExp_congr_ae hae).trans ?_
  refine (condExp_eq_sum_of_indep hOle ℓ hσle hind h' hm' hi').trans ?_
  refine Eventually.of_forall fun ω => Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : X.P (ℓ ⁻¹' {v}) = 0
  · simp [measureReal_def, hv]
  · simp [hh', hv, hh]

end Label

end Proofs.Gain

end IsotropicVariance.Paper
