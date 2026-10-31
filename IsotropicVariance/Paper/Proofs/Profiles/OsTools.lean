/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.SumRule
public import IsotropicVariance.Infra.Os.Maximum
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Small tools for `O_1` bounds and suprema of continuous random fields

The rules of the `O_s` calculus (Section `ssec:notation`) in the forms needed in Section
`sec:exponential`: positive parts, the sum of two bounds and of a deterministic constant (the sum
rule [AKM, Lemma A.4] for `s = 1`), squares of `O_2` bounds, and the bound obtained from an
exponential moment at most one. The supremum of a random field that is continuous in its
parameter, over a separable parameter space, is almost everywhere measurable when each value is.
-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## `O_1` bounds -/

lemma isOs_pos {s θ : ℝ} {X : Ω → ℝ} (h : IsOs P s θ X) :
    IsOs P s θ fun ω => max (X ω) 0 := by
  refine ⟨h.1.max aemeasurable_const, le_of_eq_of_le ?_ h.2⟩
  congr 1
  funext ω
  rw [max_eq_left (le_max_right _ _)]

/-- A deterministic `c ≥ 0` is `O_1(θ)` once `c ≤ θ log 2`. -/
lemma isOs_const [IsProbabilityMeasure P] {θ c : ℝ} (hθ : 0 < θ) (hc : c ≤ θ * Real.log 2) :
    IsOs P 1 θ fun _ => c := by
  refine ⟨aemeasurable_const, ?_⟩
  have h : Real.exp ((max c 0 / θ) ^ (1 : ℝ)) ≤ 2 := by
    rw [Real.rpow_one]
    calc Real.exp (max c 0 / θ) ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          rw [div_le_iff₀ hθ]
          rcases le_total c 0 with h0 | h0
          · rw [max_eq_right h0]
            have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
            positivity
          · rw [max_eq_left h0]
            linarith
      _ = 2 := Real.exp_log (by norm_num)
  simp only [lintegral_const, measure_univ, mul_one]
  calc ENNReal.ofReal (Real.exp ((max c 0 / θ) ^ (1 : ℝ))) ≤ ENNReal.ofReal 2 :=
        ENNReal.ofReal_le_ofReal h
    _ = 2 := by norm_num

/-- The sum rule for two `O_s` bounds, `s ≥ 1`, with no independence hypothesis. -/
lemma isOs_add_of_one_le [IsProbabilityMeasure P] {s θ₁ θ₂ : ℝ} (hs₁ : 1 ≤ s) {X Y : Ω → ℝ}
    (hX : IsOs P s θ₁ X) (hY : IsOs P s θ₂ Y) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    IsOs P s (θ₁ + θ₂) fun ω => X ω + Y ω := by
  let Z : Fin 2 → Ω → ℝ := ![fun ω => max (X ω) 0, fun ω => max (Y ω) 0]
  let θ : Fin 2 → ℝ := ![θ₁, θ₂]
  have hs := isOs_sum_of_one_le (P := P) hs₁ Finset.univ θ
    (fun i _ => by fin_cases i <;> simp [θ, hθ₁, hθ₂]) Z
    (fun i _ => by fin_cases i <;> simp [Z, θ, isOs_pos hX, isOs_pos hY])
    (fun i _ => by fin_cases i <;> exact ae_of_all _ fun ω => by simp [Z])
  simp only [Fin.sum_univ_two, θ, Z, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
  refine hs.mono (by linarith only [hs₁]) (by positivity) (hX.1.add hY.1)
    (ae_of_all _ fun ω => ?_)
  exact add_le_add (le_max_left _ _) (le_max_left _ _)

/-- The sum rule for two `O_1` bounds. -/
lemma isOs_add [IsProbabilityMeasure P] {θ₁ θ₂ : ℝ} {X Y : Ω → ℝ} (hX : IsOs P 1 θ₁ X)
    (hY : IsOs P 1 θ₂ Y) (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    IsOs P 1 (θ₁ + θ₂) fun ω => X ω + Y ω :=
  isOs_add_of_one_le le_rfl hX hY hθ₁ hθ₂

/-- Adding a deterministic constant `c ≥ 0` to an `O_1(θ)` bound. -/
lemma isOs_add_const [IsProbabilityMeasure P] {θ c : ℝ} {X : Ω → ℝ} (hX : IsOs P 1 θ X)
    (hθ : 0 < θ) (hc : 0 ≤ c) :
    IsOs P 1 (θ + (c + 1) / Real.log 2) fun ω => X ω + c := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  refine isOs_add hX (isOs_const (by positivity) ?_) hθ (by positivity)
  rw [div_mul_cancel₀ _ hl.ne']
  linarith

/-- The square of a nonnegative `O_2(θ)` bound is `O_1(θ²)`. -/
lemma isOs_sq {θ : ℝ} {S : Ω → ℝ} (h : IsOs P 2 θ S) (hS : ∀ ω, 0 ≤ S ω) :
    IsOs P 1 (θ ^ 2) fun ω => S ω ^ 2 := by
  refine ⟨h.1.pow_const 2, le_of_eq_of_le ?_ h.2⟩
  congr 1
  funext ω
  rw [max_eq_left (hS ω), max_eq_left (sq_nonneg _), Real.rpow_one, Real.rpow_two, div_pow]

/-- An exponential moment at most one gives an `O_1` bound. -/
lemma isOs_of_lintegral_exp_le_one [IsProbabilityMeasure P] {θ : ℝ} {U : Ω → ℝ}
    (hU : AEMeasurable U P)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (U ω / θ)) ∂P ≤ 1) : IsOs P 1 θ U := by
  refine ⟨hU, ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (U ω) 0 / θ) ^ (1 : ℝ))) ∂P
      ≤ ∫⁻ ω, (1 + ENNReal.ofReal (Real.exp (U ω / θ))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [Real.rpow_one]
        rcases le_total (U ω) 0 with h0 | h0
        · rw [max_eq_right h0, zero_div, Real.exp_zero, ENNReal.ofReal_one]
          exact le_self_add
        · rw [max_eq_left h0]
          exact le_add_self
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (Real.exp (U ω / θ)) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + 1 := add_le_add le_rfl h
    _ = 2 := one_add_one_eq_two

/-! ## Suprema of continuous random fields -/

/-- Over a separable space, the supremum of a bounded continuous function is the supremum over
a countable dense set. -/
lemma iSup_eq_iSup_dense {ι : Type*} [TopologicalSpace ι] [Nonempty ι] {D : Set ι}
    (hD : Dense D) {f : ι → ℝ} (hf : Continuous f) (hb : BddAbove (range f)) :
    ⨆ i, f i = ⨆ d : D, f d := by
  have : Nonempty D := hD.nonempty.to_subtype
  have hbD : BddAbove (range fun d : D => f d) :=
    hb.mono (range_subset_iff.mpr fun d => mem_range_self _)
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    have hcl : IsClosed {j | f j ≤ ⨆ d : D, f d} := isClosed_le hf continuous_const
    have hsub : D ⊆ {j | f j ≤ ⨆ d : D, f d} := fun d hd =>
      le_ciSup hbD (⟨d, hd⟩ : D)
    exact hcl.closure_subset_iff.mpr hsub (hD i)
  · exact ciSup_le fun d => le_ciSup hb (d : ι)

/-- The supremum of a random field, continuous and bounded in a separable parameter, is almost
everywhere measurable when each of its values is. -/
lemma aemeasurable_iSup_of_continuous {ι : Type*} [TopologicalSpace ι] [SeparableSpace ι]
    {F : Ω → ι → ℝ} (hc : ∀ ω, Continuous (F ω)) (hb : ∀ ω, BddAbove (range (F ω)))
    (hm : ∀ i, AEMeasurable (fun ω => F ω i) P) :
    AEMeasurable (fun ω => ⨆ i, F ω i) P := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty]
    exact aemeasurable_const
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense ι
  have : Countable D := hDc.to_subtype
  have heq : (fun ω => ⨆ i, F ω i) = fun ω => ⨆ d : D, F ω d :=
    funext fun ω => iSup_eq_iSup_dense hD (hc ω) (hb ω)
  rw [heq]
  exact AEMeasurable.iSup fun d => hm d

/-- A double supremum of a bounded family is the supremum over pairs. -/
lemma iSup_iSup_eq_iSup_prod {ι κ : Type*} {f : ι → κ → ℝ}
    (hb : BddAbove (range fun p : ι × κ => f p.1 p.2)) :
    ⨆ (i : ι) (k : κ), f i k = ⨆ p : ι × κ, f p.1 p.2 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hbi (i : ι) : BddAbove (range (f i)) :=
    hb.mono (range_subset_iff.mpr fun k => mem_range.mpr ⟨(i, k), rfl⟩)
  apply le_antisymm
  · exact ciSup_le fun i => ciSup_le fun k => le_ciSup hb (i, k)
  · refine ciSup_le fun p => (le_ciSup (hbi p.1) p.2).trans ?_
    obtain ⟨c, hc⟩ := hb
    refine le_ciSup (f := fun i => ⨆ k, f i k) ⟨c, ?_⟩ p.1
    rintro _ ⟨i, rfl⟩
    exact ciSup_le fun k => hc ⟨(i, k), rfl⟩

/-- The double supremum version of `aemeasurable_iSup_of_continuous`. -/
lemma aemeasurable_iSup₂_of_continuous {ι κ : Type*} [TopologicalSpace ι] [TopologicalSpace κ]
    [SeparableSpace ι] [SeparableSpace κ] {F : Ω → ι → κ → ℝ}
    (hc : ∀ ω, Continuous fun p : ι × κ => F ω p.1 p.2)
    (hb : ∀ ω, BddAbove (range fun p : ι × κ => F ω p.1 p.2))
    (hm : ∀ i k, AEMeasurable (fun ω => F ω i k) P) :
    AEMeasurable (fun ω => ⨆ (i : ι) (k : κ), F ω i k) P := by
  have heq : (fun ω => ⨆ (i : ι) (k : κ), F ω i k) = fun ω => ⨆ p : ι × κ, F ω p.1 p.2 :=
    funext fun ω => iSup_iSup_eq_iSup_prod (hb ω)
  rw [heq]
  exact aemeasurable_iSup_of_continuous hc hb fun p => hm p.1 p.2

end IsotropicVariance.Paper.Proofs.Profiles
