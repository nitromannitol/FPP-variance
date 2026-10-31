/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith

/-!
# Finite labels: clipping, quantization and merging of rare values

The clipping, rounding and merging of the proof of Lemma `lem:labels` (Steps 2 and 3 of the proof of
[AB26, Lemma 6.2]): a measurable finite vector `V : Ω → S → ℝ` is clipped to `[-B, B]`, quantized to
the grid `ξ ℤ`, and every value of probability below `p₀` is merged into one of largest probability.
The result is a label `Φ ∘ V` with values in a finite alphabet depending only on `S`, `B` and `ξ`,
every value of which has probability at least `p₀`, and which is within `ξ` of the clipped vector
except on an event of probability at most `(card alphabet) p₀`, where it is within `2B + 2ξ`
(`exists_finiteLabel`).

A rare value is merged into an arbitrary value of largest probability, and masses are kept in
`ℝ≥0∞`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CurvatureVariance.Paper.Gain

/-! ### Clipping -/

/-- Clipping a real number to `[-B, B]`. -/
def clipAt (B x : ℝ) : ℝ :=
  max (-B) (min B x)

/-- A clipped value lies in `[-B, B]`. -/
theorem abs_clipAt_le {B : ℝ} (hB : 0 ≤ B) (x : ℝ) : |clipAt B x| ≤ B := by
  unfold clipAt
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clipping changes a value by its excess over `B`. -/
theorem abs_sub_clipAt_le {B : ℝ} (hB : 0 ≤ B) (x : ℝ) : |x - clipAt B x| ≤ max (|x| - B) 0 := by
  unfold clipAt
  rcases le_or_gt x B with h1 | h1
  · rcases le_or_gt (-B) x with h2 | h2
    · rw [min_eq_right h1, max_eq_right h2, sub_self, abs_zero]
      exact le_max_right _ _
    · rw [min_eq_right h1, max_eq_left h2.le, abs_of_neg (by linarith : x - -B < 0),
        abs_of_neg (by linarith : x < 0)]
      exact le_max_of_le_left (by linarith)
  · rw [min_eq_left h1.le, max_eq_right (by linarith : -B ≤ B),
      abs_of_pos (by linarith : 0 < x - B), abs_of_pos (by linarith : 0 < x)]
    exact le_max_left _ _

/-- Clipping is measurable. -/
theorem measurable_clipAt (B : ℝ) : Measurable (clipAt B) := by
  unfold clipAt
  exact measurable_const.max (measurable_const.min measurable_id)

/-! ### Quantization -/

/-- The finite alphabet of quantized clipped vectors: `⌊[-B, B]/ξ⌋^S`. -/
noncomputable def labelAlphabet (S : Type*) [Fintype S] [DecidableEq S] (B ξ : ℝ) :
    Finset (S → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc ⌊-B / ξ⌋ ⌊B / ξ⌋

/-- The quantized clipped vector `⌊clip_B(v)/ξ⌋`. -/
noncomputable def quantClip {S : Type*} (B ξ : ℝ) (v : S → ℝ) : S → ℤ :=
  fun s => ⌊clipAt B (v s) / ξ⌋

/-- A quantized clipped vector lies in the alphabet. -/
theorem quantClip_mem_labelAlphabet {S : Type*} [Fintype S] [DecidableEq S] {B ξ : ℝ}
    (hB : 0 ≤ B) (hξ : 0 < ξ) (v : S → ℝ) : quantClip B ξ v ∈ labelAlphabet S B ξ := by
  refine Fintype.mem_piFinset.mpr fun s => Finset.mem_Icc.mpr ⟨?_, ?_⟩ <;>
    refine Int.floor_mono (div_le_div_of_nonneg_right ?_ hξ.le)
  · exact (abs_le.mp (abs_clipAt_le hB (v s))).1
  · exact (abs_le.mp (abs_clipAt_le hB (v s))).2

/-- Rounding down to the grid `ξ ℤ` loses less than `ξ`. -/
theorem quantClip_error {S : Type*} {B ξ : ℝ} (hξ : 0 < ξ) (v : S → ℝ) (s : S) :
    0 ≤ clipAt B (v s) - ξ * quantClip B ξ v s ∧ clipAt B (v s) - ξ * quantClip B ξ v s < ξ := by
  have hlo := (le_div_iff₀ hξ).mp (Int.floor_le (clipAt B (v s) / ξ))
  have hhi := (div_lt_iff₀ hξ).mp (Int.lt_floor_add_one (clipAt B (v s) / ξ))
  unfold quantClip
  constructor <;> nlinarith only [hlo, hhi]

/-- A value of the alphabet, rescaled by `ξ`, lies in `[-B - ξ, B]`. -/
theorem mem_labelAlphabet_bounds {S : Type*} [Fintype S] [DecidableEq S] {B ξ : ℝ} (hξ : 0 < ξ)
    {a : S → ℤ} (ha : a ∈ labelAlphabet S B ξ) (s : S) :
    -B - ξ ≤ ξ * a s ∧ ξ * a s ≤ B := by
  have h := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp ha s)
  have h1 : ((⌊-B / ξ⌋ : ℤ) : ℝ) ≤ a s := by exact_mod_cast h.1
  have h2 : (a s : ℝ) ≤ ⌊B / ξ⌋ := by exact_mod_cast h.2
  have h3 := Int.lt_floor_add_one (-B / ξ)
  have h4 := Int.floor_le (B / ξ)
  have e1 : ξ * (-B / ξ) = -B := by field_simp
  have e2 : ξ * (B / ξ) = B := by field_simp
  constructor
  · nlinarith only [h1, h3, hξ, e1]
  · nlinarith only [h2, h4, hξ, e2]

/-! ### Merging rare values -/

/-- **Merging rare values**: for a measurable label `lab` with values in a finite set `Λ` and a
threshold `p₀` with `p₀ |Λ| ≤ 1`, there is a map `Φ : Λ → Λ` such that every value of `Φ ∘ lab`
has probability at least `p₀` and `Φ ∘ lab ≠ lab` has probability at most `|Λ| p₀` (merge every
value of probability below `p₀` into one of largest probability). -/
theorem exists_merge {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : Finset ι) (hΛ : Λ.Nonempty) {lab : Ω → ι} (hlab : ∀ a, MeasurableSet (lab ⁻¹' {a}))
    (hmem : ∀ ω, lab ω ∈ Λ) {p₀ : ℝ≥0∞} (hp₀ : p₀ * Λ.card ≤ 1) :
    ∃ Φ : ι → ι, (∀ a ∈ Λ, Φ a ∈ Λ) ∧ (∀ ω, p₀ ≤ P {ω' | Φ (lab ω') = Φ (lab ω)}) ∧
      P {ω | Φ (lab ω) ≠ lab ω} ≤ Λ.card * p₀ := by
  classical
  let mass : ι → ℝ≥0∞ := fun a => P (lab ⁻¹' {a})
  obtain ⟨a₀, ha₀, hmax⟩ := Λ.exists_max_image mass hΛ
  have hpre : lab ⁻¹' (Λ : Set ι) = univ := eq_univ_of_forall hmem
  have hsum : ∑ a ∈ Λ, mass a = 1 := by
    rw [sum_measure_preimage_singleton Λ fun a _ => hlab a, hpre, measure_univ]
  have hcard0 : (Λ.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hΛ).ne'
  have hkey : p₀ ≤ mass a₀ := by
    have h1 : (1 : ℝ≥0∞) ≤ Λ.card * mass a₀ := by
      rw [← hsum, ← nsmul_eq_mul]
      exact Finset.sum_le_card_nsmul Λ mass (mass a₀) hmax
    rw [← ENNReal.mul_le_mul_iff_right hcard0 (ENNReal.natCast_ne_top _), mul_comm]
    exact hp₀.trans h1
  let Φ : ι → ι := fun a => if mass a < p₀ then a₀ else a
  refine ⟨Φ, fun a ha => ?_, fun ω => ?_, ?_⟩
  · by_cases h : mass a < p₀
    · simp only [Φ, h, ite_true, ha₀]
    · simp only [Φ, h, ite_false, ha]
  · by_cases h : mass (lab ω) < p₀
    · have hΦ : Φ (lab ω) = a₀ := by simp only [Φ, h, ite_true]
      rw [hΦ]
      refine hkey.trans (measure_mono fun ω' hω' => ?_)
      have hω'' : lab ω' = a₀ := hω'
      change Φ (lab ω') = a₀
      rw [hω'']
      by_cases h' : mass a₀ < p₀
      · simp only [Φ, h', ite_true]
      · simp only [Φ, h', ite_false]
    · have hΦ : Φ (lab ω) = lab ω := by simp only [Φ, h, ite_false]
      rw [hΦ]
      refine (not_lt.mp h).trans (measure_mono fun ω' hω' => ?_)
      have hω'' : lab ω' = lab ω := hω'
      change Φ (lab ω') = lab ω
      rw [hω'']
      simp only [Φ, h, ite_false]
  · let A : Finset ι := Λ.filter (fun a : ι => mass a < p₀)
    have hsub : {ω | Φ (lab ω) ≠ lab ω} ⊆ lab ⁻¹' (A : Set ι) := by
      intro ω hω
      refine Finset.mem_filter.mpr ⟨hmem ω, ?_⟩
      by_contra h
      exact hω (by simp only [Φ, h, ite_false])
    calc P {ω | Φ (lab ω) ≠ lab ω} ≤ P (lab ⁻¹' (A : Set ι)) := measure_mono hsub
      _ = ∑ a ∈ A, mass a := (sum_measure_preimage_singleton A fun a _ => hlab a).symm
      _ ≤ ∑ _a ∈ A, p₀ := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2.le
      _ = A.card * p₀ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Λ.card * p₀ := by
        gcongr
        exact Finset.filter_subset _ _

/-! ### The finite label -/

/-- **A finite label of a bounded-error vector** (the proof of Lemma `lem:labels`):
for a measurable `V : Ω → S → ℝ` (`S` finite), `B ≥ 0`, `ξ > 0` and `p₀` with `p₀ |Λ| ≤ 1`, `Λ` the
alphabet of quantized clipped vectors, there is `Φ` such that the label `Φ ∘ V` takes values in `Λ`,
each of probability at least `p₀`, its level sets are measurable, and
`|clip_B(V ω s) − ξ Φ(V ω) s| ≤ ξ + (2B + ξ) 1_Bad(ω)` with `P(Bad) ≤ |Λ| p₀`. -/
theorem exists_finiteLabel {Ω S : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [Fintype S] [DecidableEq S] {V : Ω → S → ℝ} (hV : Measurable V)
    {B ξ : ℝ} (hB : 0 ≤ B) (hξ : 0 < ξ) {p₀ : ℝ≥0∞}
    (hp₀ : p₀ * (labelAlphabet S B ξ).card ≤ 1) :
    ∃ Φ : (S → ℝ) → (S → ℤ),
      (∀ ω, Φ (V ω) ∈ labelAlphabet S B ξ) ∧
      (∀ ω, p₀ ≤ P {ω' | Φ (V ω') = Φ (V ω)}) ∧
      (∀ T : Set (S → ℤ), MeasurableSet {ω | Φ (V ω) ∈ T}) ∧
      ∃ Bad : Set Ω, MeasurableSet Bad ∧ P Bad ≤ (labelAlphabet S B ξ).card * p₀ ∧
        ∀ ω s, |clipAt B (V ω s) - ξ * Φ (V ω) s| ≤ ξ + (2 * B + ξ) * Bad.indicator 1 ω := by
  classical
  let lab : Ω → S → ℤ := fun ω => quantClip B ξ (V ω)
  have hlabm : Measurable lab := by
    refine measurable_pi_iff.mpr fun s => ?_
    exact (((measurable_clipAt B).comp ((measurable_pi_apply s).comp hV)).div_const ξ).floor
  have hpre : ∀ T : Set (S → ℤ), MeasurableSet (lab ⁻¹' T) :=
    fun T => hlabm (Set.to_countable T).measurableSet
  obtain ⟨Φm, hΦΛ, hΦmass, hΦbad⟩ := exists_merge P (labelAlphabet S B ξ)
    ⟨_, quantClip_mem_labelAlphabet hB hξ (0 : S → ℝ)⟩ (fun a => hpre {a})
    (fun ω => quantClip_mem_labelAlphabet hB hξ (V ω)) hp₀
  refine ⟨fun v => Φm (quantClip B ξ v),
    fun ω => hΦΛ _ (quantClip_mem_labelAlphabet hB hξ (V ω)), hΦmass,
    fun T => hpre (Φm ⁻¹' T), {ω | Φm (lab ω) ≠ lab ω}, hpre {a | Φm a ≠ a}, hΦbad,
    fun ω s => ?_⟩
  by_cases hω : Φm (lab ω) ≠ lab ω
  · have hind : ({ω | Φm (lab ω) ≠ lab ω} : Set Ω).indicator (1 : Ω → ℝ) ω = 1 :=
      Set.indicator_of_mem hω _
    rw [hind, mul_one]
    have h1 := abs_le.mp (abs_clipAt_le hB (V ω s))
    have h2 := mem_labelAlphabet_bounds hξ
      (hΦΛ _ (quantClip_mem_labelAlphabet hB hξ (V ω))) s
    rw [abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, hξ]
  · have hind : ({ω | Φm (lab ω) ≠ lab ω} : Set Ω).indicator (1 : Ω → ℝ) ω = 0 :=
      Set.indicator_of_notMem hω _
    rw [hind, mul_zero, add_zero]
    have heq : Φm (lab ω) = lab ω := not_not.mp hω
    change |clipAt B (V ω s) - ξ * (Φm (lab ω) s : ℝ)| ≤ ξ
    rw [heq]
    have h := quantClip_error (B := B) hξ (V ω) s
    rw [abs_le]
    constructor <;> linarith only [h.1, h.2]

end CurvatureVariance.Paper.Gain
