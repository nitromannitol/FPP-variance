/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.AVLabels
import CurvatureVariance.Infra.FPP.Model
public import CurvatureVariance.Paper.Proofs.LabelResidual.Blocks

/-!
# Labels of blocks and the fiber product of the weights

The proof of Proposition `prop:gain` (that of [AB26, Proposition 6.5]) bounds the variance of a
function `Z` of the weights by the conditional Efron–Stein inequality given the labels of the blocks
(the second bound of equation `eq:residual`) and the modified Poincaré inequality on the product of
the label laws ([AB26, Proposition 1.3]). This file carries facts on the product of the weights of
the fibers of a map `b : Edge m → ι` (`fiberEquiv`) to the configurations:

* `cond_map_eq`, `map_eval_fiberEquiv`: the pushforward of a conditioned measure, and the law
  `fiberLaw` of the weights of one fiber;
* `lintegral_lintegral_update_fiber_cond`: integrals over a coordinate of the fiber product replaced
  conditionally on a label are integrals over configurations resampled conditionally on the label;
* `tsum_option_blocks`, `eq_of_resample_blockCell_none`: sums over the blocks of the `K` slabs and
  the rest, and a function of the weights of the blocks is unchanged by resampling the rest.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open LabelResidual (blockCell cellOf cellOf_eq_iff fiberEquiv fiberEquiv_symm_update map_fiberEquiv)

open CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- The pushforward of a conditioned measure. -/
theorem cond_map_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (P : Measure α)
    {g : α → β} (hg : Measurable g) {s : Set β} (hs : MeasurableSet s) :
    (P.map g)[|s] = (P[|g ⁻¹' s]).map g := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.restrict_map hg hs,
    Measure.map_apply hg hs, Measure.map_smul]
  exact hg.aemeasurable

section Fibers

variable {ι : Type} [DecidableEq ι] (b : Edge m → ι) (F : Measure ℝ≥0) [IsProbabilityMeasure F]

/-- The law `F^{⊗ b⁻¹{c}}` of the weights of the fiber `c`. -/
noncomputable abbrev fiberLaw (c : ι) : Measure ({e : Edge m // b e = c} → ℝ≥0) :=
  Measure.infinitePi fun _ : {e : Edge m // b e = c} => F

omit [DecidableEq ι] in
/-- The weights of one fiber have the law `fiberLaw`. -/
theorem map_eval_fiberEquiv (c : ι) :
    (Measure.infinitePi fun _ : Edge m => F).map (fun ω => fiberEquiv b ω c) = fiberLaw b F c := by
  have h : (fun ω => fiberEquiv b ω c) = (fun x => x c) ∘ fiberEquiv b := rfl
  rw [h, ← Measure.map_map (measurable_pi_apply c) (MeasurableEquiv.measurable _),
    map_fiberEquiv, Measure.infinitePi_map_eval]

variable {b} in
/-- **Replacing a coordinate of the fiber product conditionally on a label is resampling the
fiber conditionally on the label**, for a label `ℓ` of the fiber coordinate whose level sets are
those of a label `lab` of the configuration. -/
theorem lintegral_lintegral_update_fiber_cond (c : ι) {G : Set (Sym2 (Vertex m))}
    (hG : ∀ e : Edge m, e.1 ∈ G ↔ b e = c) {β Λ : Type*} [MeasurableSpace Λ]
    [MeasurableSingletonClass Λ] (lab : Config m → β)
    (ℓ : ({e : Edge m // b e = c} → ℝ≥0) → Λ) (hℓ : Measurable ℓ)
    (hℓlab : ∀ ω ω', ℓ (fiberEquiv b ω' c) = ℓ (fiberEquiv b ω c) ↔ lab ω' = lab ω)
    {f : (∀ c, ({e : Edge m // b e = c} → ℝ≥0)) → (∀ c, ({e : Edge m // b e = c} → ℝ≥0)) → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    ∫⁻ x, ∫⁻ y, f x (Function.update x c y) ∂(fiberLaw b F c)[|ℓ ⁻¹' {ℓ (x c)}]
        ∂Measure.infinitePi (fiberLaw b F) =
      ∫⁻ ω, ∫⁻ ω', f (fiberEquiv b ω) (fiberEquiv b (resample G ω ω'))
        ∂(Measure.infinitePi (fun _ : Edge m => F))[|lab ⁻¹' {lab ω}]
        ∂Measure.infinitePi (fun _ : Edge m => F) := by
  have hmeas : ∀ x, Measurable (fun y => f x (Function.update x c y)) := fun x =>
    hf.comp (measurable_const.prodMk (measurable_update x))
  rw [← map_fiberEquiv b F, lintegral_map_equiv]
  refine lintegral_congr fun ω => ?_
  have hπ : Measurable (fun ω : Config m => fiberEquiv b ω c) :=
    (measurable_pi_apply c).comp (MeasurableEquiv.measurable _)
  have hpre : (fun ω : Config m => fiberEquiv b ω c) ⁻¹' (ℓ ⁻¹' {ℓ (fiberEquiv b ω c)}) =
      lab ⁻¹' {lab ω} := by
    ext ω'
    simp only [mem_preimage, mem_singleton_iff]
    exact hℓlab ω ω'
  rw [← map_eval_fiberEquiv b F c, cond_map_eq _ hπ (hℓ (measurableSet_singleton _)), hpre,
    lintegral_map (hmeas _) hπ]
  refine lintegral_congr fun ω' => ?_
  rw [← fiberEquiv_symm_update b c ω ω' hG, MeasurableEquiv.apply_symm_apply]

end Fibers

/-! ### The blocks of the `K` slabs -/

section Blocks

/-- A sum over the block indices of the `K` slabs and the rest, whose term at the rest vanishes,
is the sum over the blocks. -/
theorem tsum_option_blocks {K : ℕ} {f : Option (Fin K × (Fin m → ℤ)) → ℝ≥0∞} (h0 : f none = 0) :
    ∑' c, f c = ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
      f (if h : i < K then some (⟨i, h⟩, g) else none) := by
  have hsupp : Function.support f ⊆ Set.range some := by
    intro c hc
    rcases c with _ | c
    · exact absurd h0 hc
    · exact ⟨c, rfl⟩
  rw [← Option.some_injective _ |>.tsum_eq hsupp, ENNReal.tsum_prod', tsum_fintype,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => tsum_congr fun g => ?_
  simp only [i.isLt, ↓reduceDIte]

variable {n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)} (o : ℕ → Fin m → ℤ)

/-- A function of the weights of the blocks is unchanged by resampling the rest. -/
theorem eq_of_resample_blockCell_none {Z : Config m → ℝ}
    (hZdep : ∀ ω ω' : Config m, (∀ e : Edge m, (∃ i < K, ∃ g,
      e.1 ∈ block n w L t (i + 1) (o (i + 1)) g) → ω e = ω' e) → Z ω = Z ω')
    (ω ω' : Config m) : Z (resample (blockCell n w L K t o none) ω ω') = Z ω := by
  refine hZdep _ _ fun e ⟨i, hi, g, he⟩ => ?_
  have hn : e.1 ∉ blockCell n w L K t o none := fun h => h (⟨i, hi⟩, g) he
  simp [resample, hn]

end Blocks

end CurvatureVariance.Paper.Gain
