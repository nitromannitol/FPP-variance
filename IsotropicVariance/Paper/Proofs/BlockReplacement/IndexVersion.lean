/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
import IsotropicVariance.Infra.Selection.Subtype
import Mathlib.MeasureTheory.Function.Floor

/-!
# The indices `J` as functions of the information of the slabs

The indices `J_i` of the minimizing points (the proof of Lemma `lem:rowenergy`)
are almost surely equal to a function measurable for the information of the slabs of the chain
(`exists_chainInfo_measurable_J`). This is `Infra.Slab.exists_measurable_lexMinimizer_ae`, whose
selection is run here for the information of the slabs instead of all events: the continuous
versions of the slab passage times are measurable for the information of their slabs
(`Infra.Slab.exists_slabTime_version`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.BlockReplacement

open Infra.Slab

variable {m : ℕ}

/-- The information of the `M` slabs of width `s` of the chain from `0`. -/
@[instance_reducible]
def chainInfo (X : Setting m) (s : ℝ) (M : ℕ) : MeasurableSpace X.Ω :=
  ⨆ r : Fin M, X.info (chainSlab s 0 r).set

/-- **The indices are functions of the information of the slabs**, almost surely. -/
theorem exists_chainInfo_measurable_J (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {s : ℝ}
    (hs : 0 < s) (M : ℕ) (W : ℝ) :
    ∃ J' : X.Ω → Fin (M + 1) → Fin m → ℤ, Measurable[chainInfo X s M] J' ∧
      ∀ᵐ ω ∂X.P, X.J b M s W 0 ω = J' ω := by
  choose V _ hVc hVi hVae using fun i : Fin M => exists_slabTime_version X hb (chainSlab s 0 i)
  let SV : X.Ω → (Fin (M + 1) → Pt m) → ℝ := fun ω x =>
    ∑ i : Fin M, V i ω (x i.castSucc, x i.succ)
  have hSVc (ω : X.Ω) : Continuous (SV ω) :=
    continuous_finsetSum _ fun i _ =>
      (hVc i ω).comp ((continuous_apply i.castSucc).prodMk (continuous_apply i.succ))
  let G : X.Ω → flatSet M s (0 : Pt m) → ℝ := fun ω y => SV ω (unflatten y.1)
  have hGc (ω : X.Ω) : Continuous (G ω) :=
    (hSVc ω).comp (continuous_unflatten.comp continuous_subtype_val)
  have hGm (y : flatSet M s (0 : Pt m)) : Measurable[chainInfo X s M] fun ω => G ω y := by
    let _ : MeasurableSpace X.Ω := chainInfo X s M
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((measurable_pi_apply _).comp (hVi i)).mono
      (le_iSup (fun r : Fin M => X.info (chainSlab s 0 r).set) i) le_rfl
  obtain ⟨sel, hselm, hsel⟩ := (let _ : MeasurableSpace X.Ω := chainInfo X s M
    Infra.Selection.exists_measurable_lexMinimizer (flatSet M s (0 : Pt m))
      (isCompact_flatSet hs.le) (nonempty_flatSet hs.le) G hGc hGm)
  let g : X.Ω → Fin (M + 1) → Pt m := fun ω => unflatten (sel ω).1
  have hg : Measurable[chainInfo X s M] g := by
    let _ : MeasurableSpace X.Ω := chainInfo X s M
    exact continuous_unflatten.measurable.comp (measurable_subtype_coe.comp hselm)
  refine ⟨fun ω i k => if 0 < W then ⌊Pt.tr (g ω i - 0) k / W⌋ else 0, ?_, ?_⟩
  · let _ : MeasurableSpace X.Ω := chainInfo X s M
    refine Measurable.of_eval fun i => Measurable.of_eval fun k => ?_
    by_cases hW : 0 < W
    · simp only [hW, ↓reduceIte]
      refine Measurable.floor ?_
      have hc : Continuous fun x : Pt m => Pt.tr (x - 0) k / W :=
        ((Infra.Slab.continuous_tr_apply k).comp (continuous_id.sub continuous_const)).div_const W
      exact hc.measurable.comp ((measurable_pi_apply i).comp hg)
    · simp only [hW, ↓reduceIte]
      exact measurable_const
  · filter_upwards [ae_all_iff.mpr hVae] with ω hω
    have hf : ∀ x, IsAdmissible M s 0 x → SV ω x = slabSum b (X.ρ ω) M s 0 x := by
      intro x hx
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := admissible_mem_chainSlab hs.le hx i
      exact hω i _ h.1 _ h.2
    have hsel' := isLexLeastMinimizer_of_select (SV ω) hf (sel ω) (hsel ω).1 (hsel ω).2
    have hlex : lexMinimizer b (X.ρ ω) M s 0 = g ω :=
      (lexMinimizer_eq_iff b (X.isValidChain ω hs.le) M 0).mpr hsel'
    funext i k
    change (if 0 < W then ⌊Pt.tr (lexMinimizer b (X.ρ ω) M s 0 i - 0) k / W⌋ else 0) = _
    rw [hlex]

end IsotropicVariance.Paper.Proofs.BlockReplacement
