/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Finite-valued approximations: quantization and merging of rare values

Steps 2 and 3 of the proof of Lemma `lem:labels`: a bounded random quantity is
replaced by one of finitely many values (a clamp to `[−M, M]` followed by rounding down to the mesh
`δ`), and every value of probability below a threshold `θ` is merged into a value of largest
probability. After merging, each value has probability `0` or at least `θ` (for `θ` at most the
inverse of the number of values), and the merged label differs from the original one only on an
event of probability at most `θ` times the number of values.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Labels

/-! ### Clamping and rounding -/

/-- The clamp of `x` to `[−M, M]`. -/
noncomputable def clampM (M x : ℝ) : ℝ := max (-M) (min M x)

/-- The number of levels of the mesh `δ` in `[−M, M]`. -/
noncomputable def levelCount (M δ : ℝ) : ℕ := ⌈2 * M / δ⌉₊ + 1

/-- The level of `x`: its clamp to `[−M, M]` rounded down to the mesh `δ`. -/
noncomputable def quantize (M δ x : ℝ) : Fin (levelCount M δ) :=
  ⟨min ⌊(clampM M x + M) / δ⌋₊ (levelCount M δ - 1), by
    have : 0 < levelCount M δ := Nat.succ_pos _
    omega⟩

/-- The value of a level. -/
noncomputable def dequantize (M δ : ℝ) (r : Fin (levelCount M δ)) : ℝ := -M + (r : ℝ) * δ

theorem clampM_mem {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : clampM M x ∈ Set.Icc (-M) M :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem abs_clampM_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clampM M x| ≤ M :=
  abs_le.2 (clampM_mem hM x)

theorem clampM_of_mem {M x : ℝ} (hx : x ∈ Set.Icc (-M) M) : clampM M x = x := by
  rw [clampM, min_eq_right hx.2, max_eq_right hx.1]

/-- Clamping moves a point by at most its excess over `M`. -/
theorem abs_sub_clampM_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |x - clampM M x| ≤ max (|x| - M) 0 := by
  rcases le_total M x with h | h
  · have : clampM M x = M := by rw [clampM, min_eq_left h, max_eq_right (by linarith)]
    rw [this, abs_of_nonneg (show 0 ≤ x - M by linarith), abs_of_nonneg (show 0 ≤ x by linarith)]
    exact le_max_left _ _
  rcases le_total x (-M) with h' | h'
  · have : clampM M x = -M := by rw [clampM, min_eq_right h, max_eq_left h']
    rw [this, abs_of_nonpos (show x - -M ≤ 0 by linarith), abs_of_nonpos (show x ≤ 0 by linarith)]
    exact le_max_of_le_left (by linarith)
  · rw [clampM_of_mem ⟨h', h⟩, sub_self, abs_zero]
    exact le_max_right _ _

/-- Rounding moves the clamp by at most the mesh. -/
theorem abs_clampM_sub_dequantize_le {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (x : ℝ) :
    |clampM M x - dequantize M δ (quantize M δ x)| ≤ δ := by
  set y := clampM M x + M with hy
  have hy0 : 0 ≤ y := by have := (clampM_mem hM x).1; linarith
  have hy2 : y ≤ 2 * M := by have := (clampM_mem hM x).2; linarith
  have hk : ⌊y / δ⌋₊ ≤ levelCount M δ - 1 := by
    rw [levelCount, Nat.add_sub_cancel]
    exact Nat.floor_le_ceil _ |>.trans (Nat.ceil_mono (div_le_div_of_nonneg_right hy2 hδ.le))
  have hq : ((quantize M δ x : ℕ) : ℝ) = ⌊y / δ⌋₊ := by
    simp only [quantize, Nat.cast_inj]
    exact min_eq_left hk
  have h1 : (⌊y / δ⌋₊ : ℝ) * δ ≤ y := by
    have := Nat.floor_le (div_nonneg hy0 hδ.le)
    rwa [le_div_iff₀ hδ] at this
  have h2 : y < ((⌊y / δ⌋₊ : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one (y / δ)
    rwa [div_lt_iff₀ hδ] at this
  rw [dequantize, hq, abs_le]
  constructor <;> nlinarith

/-- The values of the levels lie in `[−M, M + δ]`. -/
theorem abs_dequantize_le {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (r : Fin (levelCount M δ)) :
    |dequantize M δ r| ≤ M + δ := by
  have hr : (r : ℝ) ≤ ⌈2 * M / δ⌉₊ := by
    have := r.isLt
    simp only [levelCount] at this
    exact_mod_cast Nat.lt_succ_iff.1 this
  have hc : (⌈2 * M / δ⌉₊ : ℝ) < 2 * M / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrδ : (r : ℝ) * δ < 2 * M + δ := by
    calc (r : ℝ) * δ ≤ ⌈2 * M / δ⌉₊ * δ := mul_le_mul_of_nonneg_right hr hδ.le
      _ < (2 * M / δ + 1) * δ := mul_lt_mul_of_pos_right hc hδ
      _ = 2 * M + δ := by field_simp
  have hr0 : 0 ≤ (r : ℝ) * δ := by positivity
  rw [dequantize, abs_le]
  constructor <;> linarith

theorem measurable_clampM (M : ℝ) : Measurable (clampM M) :=
  measurable_const.max (measurable_const.min measurable_id)

theorem measurable_quantize (M δ : ℝ) : Measurable (quantize M δ) := by
  have hf : Measurable fun x => ⌊(clampM M x + M) / δ⌋₊ :=
    (((measurable_clampM M).add_const M).div_const δ).nat_floor
  exact (measurable_from_nat (f := fun k : ℕ => (⟨min k (levelCount M δ - 1), by
    have : 0 < levelCount M δ := Nat.succ_pos _
    omega⟩ : Fin (levelCount M δ)))).comp hf

/-! ### Merging rare values -/

/-- Composing with a map of the values keeps each fiber a finite union of fibers. -/
theorem measurableSet_comp_preimage {Ω V : Type*} [Finite V] {m : MeasurableSpace Ω}
    {c : Ω → V} (hc : ∀ v, MeasurableSet[m] (c ⁻¹' {v})) (g : V → V) (w : V) :
    MeasurableSet[m] ((fun ω => g (c ω)) ⁻¹' {w}) := by
  have : (fun ω => g (c ω)) ⁻¹' {w} = ⋃ v ∈ {v : V | g v = w}, c ⁻¹' {v} := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun v _ => hc v

section Merge

variable {Ω V : Type*} [MeasurableSpace Ω] [Fintype V] [Nonempty V]

/-- A value of largest probability. -/
noncomputable def mostLikely (P : Measure Ω) (c : Ω → V) : V :=
  (Finset.univ.exists_max_image (fun v => P (c ⁻¹' {v})) Finset.univ_nonempty).choose

theorem measure_le_mostLikely (P : Measure Ω) (c : Ω → V) (v : V) :
    P (c ⁻¹' {v}) ≤ P (c ⁻¹' {mostLikely P c}) :=
  (Finset.univ.exists_max_image (fun v => P (c ⁻¹' {v})) Finset.univ_nonempty).choose_spec.2 v
    (Finset.mem_univ _)

/-- Merge the values of probability below `θ` into a value of largest probability. -/
noncomputable def mergeRare (P : Measure Ω) (c : Ω → V) (θ : ℝ) (v : V) : V :=
  if P (c ⁻¹' {v}) < ENNReal.ofReal θ then mostLikely P c else v

/-- The fibers of a finite-valued random variable have total probability one, so a value of
largest probability has probability at least the inverse of the number of values. -/
theorem inv_card_le_measure_mostLikely (P : Measure Ω) [IsProbabilityMeasure P] {c : Ω → V}
    (hc : ∀ v, MeasurableSet (c ⁻¹' {v})) :
    ENNReal.ofReal (1 / Fintype.card V) ≤ P (c ⁻¹' {mostLikely P c}) := by
  have hsum : ∑ v, P (c ⁻¹' {v}) = 1 := by
    rw [← measure_biUnion_finset (fun v _ w _ hvw => ?_) (fun v _ => hc v)]
    · have : (⋃ v ∈ (Finset.univ : Finset V), c ⁻¹' {v}) = Set.univ := by
        ext ω; simp
      rw [this, measure_univ]
    · exact Set.disjoint_left.2 fun ω h1 h2 => hvw (h1.symm.trans h2)
  have hle : (1 : ℝ≥0∞) ≤ Fintype.card V * P (c ⁻¹' {mostLikely P c}) := by
    calc (1 : ℝ≥0∞) = ∑ v, P (c ⁻¹' {v}) := hsum.symm
      _ ≤ ∑ _v : V, P (c ⁻¹' {mostLikely P c}) :=
        Finset.sum_le_sum fun v _ => measure_le_mostLikely P c v
      _ = Fintype.card V * P (c ⁻¹' {mostLikely P c}) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_div_of_pos hcard, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rw [ENNReal.div_le_iff (by exact_mod_cast hcard.ne') (by simp), mul_comm]
  exact hle

/-- **After merging, each value has probability `0` or at least `θ`**, for `θ` at most the
inverse of the number of values. -/
theorem atoms_mergeRare (P : Measure Ω) [IsProbabilityMeasure P] {c : Ω → V}
    (hc : ∀ v, MeasurableSet (c ⁻¹' {v})) {θ : ℝ} (hθ : θ ≤ 1 / Fintype.card V) (w : V) :
    P ((fun ω => mergeRare P c θ (c ω)) ⁻¹' {w}) = 0 ∨
      ENNReal.ofReal θ ≤ P ((fun ω => mergeRare P c θ (c ω)) ⁻¹' {w}) := by
  have hstar : ¬ P (c ⁻¹' {mostLikely P c}) < ENNReal.ofReal θ := fun h =>
    absurd ((ENNReal.ofReal_le_ofReal hθ).trans (inv_card_le_measure_mostLikely P hc)) (not_le.2 h)
  by_cases hw : w = mostLikely P c
  · right
    refine (not_lt.1 hstar).trans (measure_mono fun ω hω => ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    simp only [mergeRare, hω, hw, ite_self]
  by_cases hrare : P (c ⁻¹' {w}) < ENNReal.ofReal θ
  · left
    refine measure_mono_null (fun ω hω => ?_) (measure_empty (μ := P))
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mergeRare] at hω
    split_ifs at hω with h
    · exact hw hω.symm
    · rw [hω] at h
      exact h hrare
  · right
    refine (not_lt.1 hrare).trans (measure_mono fun ω hω => ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    simp only [mergeRare, hω, hrare, ite_false]

/-- **Merging changes the label only on a rare event**: of probability at most `θ` times the
number of values. -/
theorem measure_mergeRare_ne_le (P : Measure Ω) {c : Ω → V} (θ : ℝ) :
    P {ω | mergeRare P c θ (c ω) ≠ c ω} ≤ ENNReal.ofReal (Fintype.card V * θ) := by
  have hsub : {ω | mergeRare P c θ (c ω) ≠ c ω} ⊆
      ⋃ v ∈ Finset.univ.filter (fun v => P (c ⁻¹' {v}) < ENNReal.ofReal θ), c ⁻¹' {v} := by
    intro ω hω
    change mergeRare P c θ (c ω) ≠ c ω at hω
    simp only [mergeRare] at hω
    split_ifs at hω with h
    · exact Set.mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩) rfl
    · exact absurd rfl hω
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ v ∈ Finset.univ.filter (fun v => P (c ⁻¹' {v}) < ENNReal.ofReal θ), P (c ⁻¹' {v})
      ≤ ∑ _v ∈ Finset.univ.filter (fun v => P (c ⁻¹' {v}) < ENNReal.ofReal θ),
          ENNReal.ofReal θ := Finset.sum_le_sum fun v hv => (Finset.mem_filter.1 hv).2.le
    _ ≤ ∑ _v : V, ENNReal.ofReal θ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ENNReal.ofReal (Fintype.card V * θ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rcases le_total θ 0 with h | h
        · rw [ENNReal.ofReal_of_nonpos h, mul_zero,
            ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) h)]
        · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end Merge

end IsotropicVariance.Paper.Proofs.Labels
