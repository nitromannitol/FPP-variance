/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonSetting
public import IsotropicVariance.Infra.TimeConstant.SettingBounds
public import IsotropicVariance.Paper.Contracts.Classical

/-! # The Poisson realization-to-setting bridge

The source sample space is never given a lifted rigid-motion action. Instead its configuration
law is transferred to the canonical carrier. A measurable lift exists up to null sets solely
for comparing passage laws with that fixed canonical setting.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace IsotropicVariance.Infra.Instances
universe u
variable {m : ℕ} {lam : ℝ≥0}

/-- Every source Poisson realization maps measure-preservingly to the canonical carrier, with
its decoded configuration unchanged almost surely. -/
theorem exists_poissonCarrier_lift {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)}
    (hη : IsotropicVariance.IsPoissonProcess lam η P) :
    ∃ f : Ω → PoissonCarrier m, Measurable f ∧
      MeasurePreserving f P (poissonCanonicalLaw m lam) ∧
      (fun ω => poissonCarrierDecode (f ω)) =ᵐ[P] η := by
  have he := measurableEmbedding_poissonCarrierDecode (m := m)
  obtain ⟨r, hr, hrd⟩ := he.exists_measurable_extend (g := id) measurable_id
    (fun _ => ⟨(0 : PoissonCarrier m)⟩)
  have hlaw : P.map η = (poissonCanonicalLaw m lam).map poissonCarrierDecode :=
    isPoissonProcess_law_eq hη (isPoissonProcess_poissonCarrierDecode m lam)
  have hae : ∀ᵐ ω ∂P, η ω ∈ range (poissonCarrierDecode (m := m)) := by
    rw [ae_iff]
    change P (η ⁻¹' (range (poissonCarrierDecode (m := m)))ᶜ) = 0
    rw [← Measure.map_apply hη.1 he.measurableSet_range.compl, hlaw,
      Measure.map_apply he.measurable he.measurableSet_range.compl]
    have hempty : poissonCarrierDecode ⁻¹' (range (poissonCarrierDecode (m := m)))ᶜ = ∅ := by
      ext c
      simp only [mem_preimage, mem_compl_iff, mem_range, mem_empty_iff_false, iff_false, not_not]
      exact ⟨c, rfl⟩
    rw [hempty, measure_empty]
  let f := r ∘ η
  have hf : Measurable f := hr.comp hη.1
  have hdecode : (fun ω => poissonCarrierDecode (f ω)) =ᵐ[P] η := by
    filter_upwards [hae] with ω hω
    obtain ⟨c, hc⟩ := hω
    change poissonCarrierDecode (r (η ω)) = η ω
    rw [← hc]
    exact congrArg poissonCarrierDecode (congrFun hrd c)
  refine ⟨f, hf, ⟨hf, ?_⟩, hdecode⟩
  apply he.map_injective
  rw [Measure.map_map he.measurable hf]
  exact (Measure.map_congr hdecode).trans hlaw

/-- The Poisson part of the setting-of-realization bridge, in the exact variables of the main
theorem `IsotropicVariance.variance_passageTime_le_of_isPoissonProcess`. The constructed setting
lives in universe zero. -/
theorem exists_poissonSetting_of_realization {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)}
    (hη : IsotropicVariance.IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ S : Paper.Setting.{0} m, ∀ u v : Pt m,
      AEMeasurable (fun ω => passageTime (ρ (η ω)) u v) P ∧
      AEMeasurable (fun ω => S.passTime ω u v) S.P ∧
      P.map (fun ω => passageTime (ρ (η ω)) u v) = S.P.map (fun ω => S.passTime ω u v) := by
  let S := poissonSetting lam ρ hρ
  obtain ⟨f, hf, hmp, hdecode⟩ := exists_poissonCarrier_lift hη
  refine ⟨S, fun u v => ?_⟩
  have hS : AEMeasurable (fun ω => S.passTime ω u v) S.P :=
    (TimeConstant.aestronglyMeasurable_passTime S u v).aemeasurable
  have hSlaw : HasLaw (fun ω => S.passTime ω u v) (S.P.map (fun ω => S.passTime ω u v)) S.P :=
    ⟨hS, rfl⟩
  have hcomp := hSlaw.comp hmp.hasLaw
  have heq : (fun ω => passageTime (ρ (η ω)) u v) =ᵐ[P] ((fun ω => S.passTime ω u v) ∘ f) := by
    filter_upwards [hdecode] with ω hω
    change passageTime (ρ (η ω)) u v = passageTime (ρ (poissonCarrierDecode (f ω))) u v
    rw [hω]
  have hresult := hcomp.congr heq
  exact ⟨hresult.aemeasurable, hS, hresult.map_eq⟩

/-- The Poisson branch of `SettingOfRealizationStatement`, without any new premise. -/
theorem settingOfRealizationStatement_poisson (X : Paper.Realization.{u} m)
    (hnoise : X.noise = Paper.Noise.poisson lam) :
    ∃ S : Paper.Setting.{0} m, ∀ u v : Pt m,
      AEMeasurable (fun ω => passageTime (X.ρ (X.config ω)) u v) X.P ∧
      AEMeasurable (fun ω => S.passTime ω u v) S.P ∧
      X.P.map (fun ω => passageTime (X.ρ (X.config ω)) u v) =
        S.P.map (fun ω => S.passTime ω u v) := by
  rcases X with @⟨noise, Ω, mΩ, sbΩ, P, ip, η, hη, ρ, hρ⟩
  cases hnoise
  let := mΩ
  let := sbΩ
  let := ip
  exact exists_poissonSetting_of_realization hη.2 hρ

end IsotropicVariance.Infra.Instances
