/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
Ported from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability) at
99cfc20, LatticeProb/Prob/EfronSteinCountable.lean (the finite inequality read on the field, and
the countable inequality); modified: heterogeneous coordinate spaces and laws, and the finite step
from `blm_proposition1`.
-/
module

public import CurvatureVariance.Infra.EfronStein.Countable
import CurvatureVariance.Statements.Inputs.BlmProposition1

/-!
# The Efron–Stein inequality on a countable product, from [BLM03, Proposition 1]

As in the continuum library, `IsotropicVariance.Infra.EfronStein.Countable`: its theorems
`evariance_le_half_sum_resampleEnergy_of_dependsOn`,
`evariance_le_half_tsum_resampleEnergy_of_measurable` and `evariance_le_half_tsum_resampleEnergy`.
This is the extension of [BLM03, Proposition 1] to countably many independent variables by
martingale convergence, in the third paragraph of [AB26, proof of Lemma 6.3], which the proof of
Lemma `lem:residual` applies.

The finite step is `CurvatureVariance.blm_proposition1` itself, which has no moment
hypothesis. The one adaptation of the continuum's proofs: its `enorm_sq_eq_ofReal_sq` is the
lattice's `enorm_sub_sq_eq_ofReal`.

* `evariance_le_half_sum_resampleEnergy_of_dependsOn`: the finite inequality for a function of
  the coordinates in a finite set, read on the countable product.
* `evariance_le_half_tsum_resampleEnergy_of_measurable`, for a measurable `F`.
* `evariance_le_half_tsum_resampleEnergy`, for every `F ∈ L²`.

As in `CurvatureVariance.Infra.EfronStein.Countable`: average out the coordinates outside a finite
set (`partialIntegral`), apply the finite inequality, bound the energies of the average by those of
`F` (Jensen), converge along an exhaustion (Lévy), and transfer the variance by Fatou.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CurvatureVariance.Infra.EfronStein

variable {I : Type*} [DecidableEq I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- **The Efron–Stein inequality for a function of finitely many coordinates of a countable
product.** The finite inequality is [BLM03, Proposition 1], `blm_proposition1`, which has no moment
hypothesis. -/
theorem evariance_le_half_sum_resampleEnergy_of_dependsOn (S : Finset I)
    {Φ : ((i : I) → X i) → ℝ} (hΦm : Measurable Φ) (hloc : DependsOn Φ S) :
    evariance Φ (Measure.infinitePi μ) ≤ (∑ i ∈ S, resampleEnergy μ Φ i) / 2 := by
  set P := Measure.infinitePi μ with hP
  set k := S.card with hk
  set e : Fin k → I := fun j => (S.equivFin.symm j : I) with he
  have heinj : Function.Injective e := fun a b hab =>
    S.equivFin.symm.injective (Subtype.ext hab)
  set ν : (j : Fin k) → Measure (X (e j)) := fun j => μ (e j) with hν
  set Q := Measure.pi ν with hQ
  set T : ((i : I) → X i) → ((j : Fin k) → X (e j)) := fun x j => x (e j) with hT
  have hTmp : MeasurePreserving T P Q := measurePreserving_restrict_fin μ S
  -- a base point, to extend configurations of `S` to the whole index set
  obtain ⟨ω₀, -⟩ : (Set.univ : Set ((i : I) → X i)).Nonempty :=
    nonempty_of_measure_ne_zero (μ := P) (by simp [hP])
  let ext : ((i : S) → X i) → ((i : I) → X i) := fun z i =>
    if h : i ∈ S then z ⟨i, h⟩ else ω₀ i
  have hext : Measurable ext := by
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases h : i ∈ S
    · simp only [ext, h, dite_true]
      exact measurable_pi_apply _
    · simp only [ext, h, dite_false]
      exact measurable_const
  let back := MeasurableEquiv.piCongrLeft (fun i : S => X i) S.equivFin.symm
  set G : ((j : Fin k) → X (e j)) → ℝ := fun y => Φ (ext (back y)) with hG
  have hGm : Measurable G := hΦm.comp (hext.comp back.measurable)
  have hGT : ∀ x, G (T x) = Φ x := by
    intro x
    have hb : back (T x) = S.restrict x := back.apply_symm_apply (S.restrict x)
    change Φ (ext (back (T x))) = Φ x
    refine hloc fun i hi => ?_
    rw [hb]
    change (if h : i ∈ S then (S.restrict x) ⟨i, h⟩ else ω₀ i) = x i
    simp only [Finset.mem_coe.mp hi, dite_true, Finset.restrict]
  have hTupd : ∀ (x : (i : I) → X i) (j : Fin k) (t : X (e j)),
      T (Function.update x (e j) t) = Function.update (T x) j t :=
    fun x j t => Function.update_comp_eq_of_injective' x heinj j t
  have hGmap : AEStronglyMeasurable G (Measure.map T P) := by
    rw [hTmp.map_eq]; exact hGm.aestronglyMeasurable
  -- `blm_proposition1` is the whole finite input
  have hmain : evariance G Q ≤ (1 / 2 : ℝ≥0∞) * ∑ j : Fin k, ∫⁻ y, ∫⁻ t : X (e j),
      ‖G y - G (Function.update y j t)‖ₑ ^ 2 ∂ν j ∂Q :=
    CurvatureVariance.blm_proposition1 k ν G hGm
  have hmean : ∫ y, G y ∂Q = ∫ x, Φ x ∂P := by
    rw [← hTmp.map_eq, integral_map hTmp.measurable.aemeasurable hGmap]
    simp only [hGT]
  have hlhs : evariance G Q = evariance Φ P := by
    have hm : Measurable (fun y => ‖G y - ∫ x, Φ x ∂P‖ₑ ^ 2) :=
      ((hGm.sub measurable_const).enorm).pow_const 2
    simp only [evariance, hmean]
    rw [← hTmp.lintegral_comp hm]
    simp only [hGT]
  have hEj : ∀ j : Fin k, (∫⁻ y, ∫⁻ t : X (e j), ‖G y - G (Function.update y j t)‖ₑ ^ 2 ∂ν j ∂Q) =
      resampleEnergy μ Φ (e j) := by
    intro j
    have hT' : MeasurePreserving (fun q : ((i : I) → X i) × X (e j) => (T q.1, q.2))
        (P.prod (μ (e j))) (Q.prod (ν j)) := hTmp.prod (MeasurePreserving.id _)
    have hmr : Measurable (fun r : ((j : Fin k) → X (e j)) × X (e j) =>
        ‖G r.1 - G (Function.update r.1 j r.2)‖ₑ ^ 2) :=
      (((hGm.comp measurable_fst).sub (hGm.comp measurable_update')).enorm).pow_const 2
    rw [← lintegral_prod _ hmr.aemeasurable, ← hT'.lintegral_comp hmr,
      resampleEnergy_eq_lintegral_prod μ hΦm (e j)]
    refine lintegral_congr fun q => ?_
    simp only [← hTupd, hGT]
    exact enorm_sub_sq_eq_ofReal _
  have hsum : ∑ j : Fin k, resampleEnergy μ Φ (e j) = ∑ i ∈ S, resampleEnergy μ Φ i := by
    rw [← Finset.sum_coe_sort S (fun i => resampleEnergy μ Φ i)]
    exact Fintype.sum_equiv S.equivFin.symm _ _ (fun j => rfl)
  rw [← hlhs, ← hsum]
  refine hmain.trans_eq ?_
  simp only [hEj]
  rw [one_div, ENNReal.div_eq_inv_mul]

/-- The countable Efron–Stein inequality for a measurable `F`, from [BLM03, Proposition 1]; see
`evariance_le_half_tsum_resampleEnergy` for a general square-integrable `F`. -/
theorem evariance_le_half_tsum_resampleEnergy_of_measurable [Countable I]
    {F : ((i : I) → X i) → ℝ} (hFm : Measurable F) (hF : MemLp F 2 (Measure.infinitePi μ)) :
    evariance F (Measure.infinitePi μ) ≤ (∑' i, resampleEnergy μ F i) / 2 := by
  classical
  set P := Measure.infinitePi μ with hP
  have hFint : Integrable F P := hF.integrable (by norm_num)
  set m : ℝ := ∫ ω, F ω ∂P with hm
  obtain ⟨g, hg⟩ := exists_injective_nat I
  set Sset : ℕ → Set I := fun n => {i | g i < n} with hSset
  have hSfinite : ∀ n, (Sset n).Finite := by
    intro n
    have hsub : Sset n ⊆ g ⁻¹' (Set.Iio n) := fun i hi => hi
    exact Set.Finite.subset (Set.Finite.preimage hg.injOn (Set.finite_Iio n)) hsub
  set Sf : ℕ → Finset I := fun n => (hSfinite n).toFinset with hSf
  have hmemSf : ∀ (n : ℕ) (i : I), i ∈ Sf n ↔ i ∈ Sset n := fun n i =>
    Set.Finite.mem_toFinset _
  have hmono : Monotone Sset := fun a b hab i hi => lt_of_lt_of_le hi hab
  have hcov : ∀ i : I, ∃ n, i ∈ Sset n := fun i => ⟨g i + 1, Nat.lt_succ_self _⟩
  set Φ : ℕ → ((i : I) → X i) → ℝ := fun n => partialIntegral μ (Sset n) F with hΦ
  have hΦm : ∀ n, Measurable (Φ n) := fun n => measurable_partialIntegral μ _ hFm
  have hΦmean : ∀ n, ∫ ω, Φ n ω ∂P = m := fun n => integral_partialIntegral μ _ hFint
  have hΦloc : ∀ n, DependsOn (Φ n) (Sf n : Set I) :=
    fun n ω ω' h => partialIntegral_congr μ _ F fun i hi => h i ((hmemSf n i).mpr hi)
  have hΦE : ∀ (n : ℕ), ∀ i ∈ Sf n, resampleEnergy μ (Φ n) i ≤ resampleEnergy μ F i :=
    fun n i hi => resampleEnergy_partialIntegral_le μ ((hmemSf n i).mp hi) hFm hFint
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal ((Φ n ω - m) ^ 2) ∂P
      ≤ (∑' i, resampleEnergy μ F i) / 2 := by
    intro n
    have h1 : ∫⁻ ω, ENNReal.ofReal ((Φ n ω - m) ^ 2) ∂P = evariance (Φ n) P := by
      rw [evariance_eq_lintegral_ofReal, hΦmean n]
    rw [h1]
    refine (evariance_le_half_sum_resampleEnergy_of_dependsOn μ (Sf n) (hΦm n)
      (hΦloc n)).trans ?_
    refine ENNReal.div_le_div_right ?_ 2
    calc ∑ i ∈ Sf n, resampleEnergy μ (Φ n) i
        ≤ ∑ i ∈ Sf n, resampleEnergy μ F i := Finset.sum_le_sum (hΦE n)
      _ ≤ ∑' i, resampleEnergy μ F i := ENNReal.sum_le_tsum _
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Φ n ω) atTop (𝓝 (F ω)) :=
    tendsto_partialIntegral μ hmono hcov hFm hFint
  have hlim : ∀ᵐ ω ∂P, ENNReal.ofReal ((F ω - m) ^ 2)
      = liminf (fun n => ENNReal.ofReal ((Φ n ω - m) ^ 2)) atTop := by
    filter_upwards [hconv] with ω hω
    have : Tendsto (fun n => ENNReal.ofReal ((Φ n ω - m) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((F ω - m) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((hω.sub_const m).pow 2)
    exact this.liminf_eq.symm
  calc evariance F P
      = ∫⁻ ω, ENNReal.ofReal ((F ω - m) ^ 2) ∂P := evariance_eq_lintegral_ofReal F P
    _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal ((Φ n ω - m) ^ 2)) atTop ∂P :=
        lintegral_congr_ae hlim
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((Φ n ω - m) ^ 2) ∂P) atTop :=
        lintegral_liminf_le fun n => (((hΦm n).sub measurable_const).pow_const 2).ennreal_ofReal
    _ ≤ liminf (fun _ : ℕ => (∑' i, resampleEnergy μ F i) / 2) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hbound)
    _ = (∑' i, resampleEnergy μ F i) / 2 := liminf_const _

/-- **The Efron–Stein inequality over a countable product of arbitrary probability spaces**, from
[BLM03, Proposition 1] by martingale convergence (the third paragraph of
[AB26, proof of Lemma 6.3]). The variance of a square-integrable function is at most half the sum of
its resampling energies. -/
theorem evariance_le_half_tsum_resampleEnergy [Countable I] {F : ((i : I) → X i) → ℝ}
    (hF : MemLp F 2 (Measure.infinitePi μ)) :
    evariance F (Measure.infinitePi μ) ≤ (∑' i, resampleEnergy μ F i) / 2 := by
  have hFG := hF.aestronglyMeasurable.ae_eq_mk
  rw [evariance_congr hFG]
  simp_rw [resampleEnergy_congr_ae μ hFG]
  exact evariance_le_half_tsum_resampleEnergy_of_measurable μ
    hF.aestronglyMeasurable.stronglyMeasurable_mk.measurable (MemLp.ae_eq hFG hF)

end CurvatureVariance.Infra.EfronStein
