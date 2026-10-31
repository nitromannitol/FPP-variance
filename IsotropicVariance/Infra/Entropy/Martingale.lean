/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Entropy.Splice
public import Mathlib.Probability.Moments.Variance

/-!
# The martingale decomposition along an enumeration of the coordinates

Let `P = Measure.infinitePi μ` over a countable index set, enumerated by an injection
`e : ι → ℕ`, and let `f ∈ L²(P)` be measurable. Integrating out the coordinates outside the first
`n` gives `f_n = E_{W_n} f` with `W_n = tailSet e n`; then `f_0 = E f`, and the increments
`f_{n+1} - f_n` are orthogonal, so `Var f = ∑ₙ ‖f_{n+1} - f_n‖₂²` (`hasSum_integral_sq_increment`).
When `e i = n`, the increment is `E_{W_{n+1}} (D_i f)` with `D_i f = f - E_i f`, so its `L¹` norm is
at most that of `D_i f` (`integral_abs_increment_le`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace IsotropicVariance.Infra.Entropy

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)] {T W W' : Set ι}
  {f h : (∀ i, X i) → ℝ}

/-! ### Linearity and orthogonality of `integrateOut` -/

theorem integrateOut_sub_ae (hf : Integrable f (Measure.infinitePi μ))
    (hh : Integrable h (Measure.infinitePi μ)) :
    integrateOut μ T (fun x => f x - h x) =ᵐ[Measure.infinitePi μ]
      fun x => integrateOut μ T f x - integrateOut μ T h x := by
  filter_upwards [ae_integrable_splice (T := T) hf, ae_integrable_splice (T := T) hh]
    with x hx hhx
  exact integral_sub hx hhx

omit [∀ i, IsProbabilityMeasure (μ i)] in
theorem integrable_mul_of_memLp_two {u v : (∀ i, X i) → ℝ} (hu : MemLp u 2 (Measure.infinitePi μ))
    (hv : MemLp v 2 (Measure.infinitePi μ)) :
    Integrable (fun x => u x * v x) (Measure.infinitePi μ) :=
  hu.integrable_mul hv

/-- For `W' ⊆ W`, `E[E_W f · E_{W'} f] = E[(E_W f)²]`. -/
theorem integral_mul_integrateOut_of_subset (hWW : W' ⊆ W) (hf : MemLp f 2 (Measure.infinitePi μ)) :
    ∫ x, integrateOut μ W f x * integrateOut μ W' f x ∂Measure.infinitePi μ =
      ∫ x, integrateOut μ W f x ^ 2 ∂Measure.infinitePi μ := by
  have hfi : Integrable f (Measure.infinitePi μ) := hf.integrable one_le_two
  have hu : ∀ x y, integrateOut μ W f (splice W x y) = integrateOut μ W f x :=
    fun x y => integrateOut_splice x y
  have hint := integrable_mul_of_memLp_two (memLp_integrateOut (T := W) hf)
    (memLp_integrateOut (T := W') hf)
  rw [← integral_mul_integrateOut hu hint]
  have htower := integrateOut_integrateOut (S := W) (T := W') hfi
  rw [Set.union_eq_right.2 hWW] at htower
  refine integral_congr_ae (htower.mono fun x hx => ?_)
  simp only [hx, sq]

/-- Pythagoras for nested integrations: `‖E_{W'} f - E_W f‖² = ‖E_{W'} f‖² - ‖E_W f‖²`. -/
theorem integral_sq_sub_integrateOut (hWW : W' ⊆ W) (hf : MemLp f 2 (Measure.infinitePi μ)) :
    ∫ x, (integrateOut μ W' f x - integrateOut μ W f x) ^ 2 ∂Measure.infinitePi μ =
      ∫ x, integrateOut μ W' f x ^ 2 ∂Measure.infinitePi μ -
        ∫ x, integrateOut μ W f x ^ 2 ∂Measure.infinitePi μ := by
  have h1 := memLp_integrateOut (T := W') hf
  have h2 := memLp_integrateOut (T := W) hf
  have i11 : Integrable (fun x => integrateOut μ W' f x ^ 2) (Measure.infinitePi μ) :=
    h1.integrable_sq
  have i22 : Integrable (fun x => integrateOut μ W f x ^ 2) (Measure.infinitePi μ) :=
    h2.integrable_sq
  have i12 : Integrable (fun x => 2 * (integrateOut μ W f x * integrateOut μ W' f x))
      (Measure.infinitePi μ) := (integrable_mul_of_memLp_two h2 h1).const_mul 2
  have e : (fun x => (integrateOut μ W' f x - integrateOut μ W f x) ^ 2) = fun x =>
      integrateOut μ W' f x ^ 2 - 2 * (integrateOut μ W f x * integrateOut μ W' f x) +
        integrateOut μ W f x ^ 2 := by
    funext x; ring
  have i3 : Integrable (fun x => integrateOut μ W' f x ^ 2 -
      2 * (integrateOut μ W f x * integrateOut μ W' f x)) (Measure.infinitePi μ) := i11.sub i12
  rw [e, integral_add i3 i22, integral_sub i11 i12, integral_const_mul,
    integral_mul_integrateOut_of_subset hWW hf]
  ring

/-! ### The martingale along an enumeration -/

theorem tailSet_succ_subset (e : ι → ℕ) (n : ℕ) : tailSet e (n + 1) ⊆ tailSet e n :=
  tailSet_antitone e (Nat.le_succ n)

theorem tailSet_succ_union {e : ι → ℕ} (he : Function.Injective e) {n : ℕ} {i : ι}
    (hi : e i = n) : tailSet e (n + 1) ∪ {i} = tailSet e n := by
  ext j
  simp only [tailSet, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (h | rfl) <;> omega
  · intro h
    rcases h.lt_or_eq with h | h
    · left; omega
    · right; exact he (h.symm.trans hi.symm)

theorem tailSet_succ_eq {e : ι → ℕ} {n : ℕ} (hn : ∀ i, e i ≠ n) :
    tailSet e (n + 1) = tailSet e n := by
  ext j; simp only [tailSet, Set.mem_ofPred_eq]; have := hn j; omega

omit [∀ i, IsProbabilityMeasure (μ i)] in
theorem integrateOut_tailSet_zero (e : ι → ℕ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    integrateOut μ (tailSet e 0) f x = ∫ y, f y ∂Measure.infinitePi μ := by
  have : tailSet e 0 = Set.univ := by ext j; simp [tailSet]
  simp [integrateOut, this]

/-- `∫ (E_{W_n} f)² → ∫ f²`. -/
theorem tendsto_integral_sq_integrateOut [Countable ι] (e : ι → ℕ) (hfm : Measurable f)
    (hf : MemLp f 2 (Measure.infinitePi μ)) :
    Tendsto (fun n => ∫ x, integrateOut μ (tailSet e n) f x ^ 2 ∂Measure.infinitePi μ) atTop
      (𝓝 (∫ x, f x ^ 2 ∂Measure.infinitePi μ)) := by
  set s : ℕ → ℝ := fun n => ∫ x, integrateOut μ (tailSet e n) f x ^ 2 ∂Measure.infinitePi μ
  have hmono : Monotone s := by
    refine monotone_nat_of_le_succ fun n => ?_
    have h := integral_sq_sub_integrateOut (tailSet_succ_subset e n) hf
    have h0 : 0 ≤ ∫ x, (integrateOut μ (tailSet e (n + 1)) f x -
        integrateOut μ (tailSet e n) f x) ^ 2 ∂Measure.infinitePi μ :=
      integral_nonneg fun x => sq_nonneg _
    simp only [s]; linarith
  have hbdd : ∀ n, s n ≤ ∫ x, f x ^ 2 ∂Measure.infinitePi μ := fun n =>
    integral_sq_integrateOut_le hf
  have htend := tendsto_atTop_ciSup hmono ⟨_, Set.forall_mem_range.2 hbdd⟩
  suffices hle : ∫ x, f x ^ 2 ∂Measure.infinitePi μ ≤ ⨆ n, s n by
    have : ⨆ n, s n = ∫ x, f x ^ 2 ∂Measure.infinitePi μ :=
      le_antisymm (ciSup_le hbdd) hle
    rwa [this] at htend
  -- Fatou along Lévy's upward theorem
  have hfi : Integrable f (Measure.infinitePi μ) := hf.integrable one_le_two
  have hlim : ∀ᵐ x ∂Measure.infinitePi μ, Tendsto
      (fun n => ENNReal.ofReal (integrateOut μ (tailSet e n) f x ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (f x ^ 2))) := by
    filter_upwards [tendsto_integrateOut_ae μ e hfm hfi] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_pow 2).tendsto _ |>.comp hx)
  have hfatou : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂Measure.infinitePi μ ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (integrateOut μ (tailSet e n) f x ^ 2)
        ∂Measure.infinitePi μ) atTop := by
    calc ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂Measure.infinitePi μ
        = ∫⁻ x, liminf (fun n => ENNReal.ofReal (integrateOut μ (tailSet e n) f x ^ 2)) atTop
            ∂Measure.infinitePi μ :=
          lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp
          ((measurable_integrateOut hfm).pow_const 2)
  have hconv : ∀ n, ∫⁻ x, ENNReal.ofReal (integrateOut μ (tailSet e n) f x ^ 2)
      ∂Measure.infinitePi μ = ENNReal.ofReal (s n) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (memLp_integrateOut hf).integrable_sq
      (ae_of_all _ fun x => sq_nonneg _)).symm
  simp_rw [hconv] at hfatou
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (ae_of_all _ fun x => sq_nonneg _)] at hfatou
  have hsup : liminf (fun n => ENNReal.ofReal (s n)) atTop ≤ ENNReal.ofReal (⨆ n, s n) :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun n =>
      ENNReal.ofReal_le_ofReal (le_ciSup ⟨_, Set.forall_mem_range.2 hbdd⟩ n))
  have := hfatou.trans hsup
  rwa [ENNReal.ofReal_le_ofReal_iff (le_trans (integral_nonneg fun x => sq_nonneg _)
    (le_ciSup ⟨_, Set.forall_mem_range.2 hbdd⟩ 0))] at this

/-- **Orthogonal decomposition of the variance** along the martingale `E_{W_n} f`. -/
theorem hasSum_integral_sq_increment [Countable ι] (e : ι → ℕ) (hfm : Measurable f)
    (hf : MemLp f 2 (Measure.infinitePi μ)) :
    HasSum (fun n => ∫ x, (integrateOut μ (tailSet e (n + 1)) f x -
      integrateOut μ (tailSet e n) f x) ^ 2 ∂Measure.infinitePi μ)
      (ProbabilityTheory.variance f (Measure.infinitePi μ)) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n => integral_nonneg fun x => sq_nonneg _) _).2 ?_
  have hpart : ∀ N, ∑ n ∈ Finset.range N, ∫ x, (integrateOut μ (tailSet e (n + 1)) f x -
      integrateOut μ (tailSet e n) f x) ^ 2 ∂Measure.infinitePi μ =
      ∫ x, integrateOut μ (tailSet e N) f x ^ 2 ∂Measure.infinitePi μ -
        (∫ x, f x ∂Measure.infinitePi μ) ^ 2 := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, integrateOut_tailSet_zero, integral_const,
        probReal_univ, one_smul]
      ring
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, integral_sq_sub_integrateOut (tailSet_succ_subset e N) hf]
      ring
  simp_rw [hpart]
  rw [ProbabilityTheory.variance_eq_sub hf]
  exact (tendsto_integral_sq_integrateOut e hfm hf).sub_const _

/-! ### The increments -/

variable [DecidableEq ι]

theorem memLp_coordDiff (i : ι) (hf : MemLp f 2 (Measure.infinitePi μ)) :
    MemLp (Cited.coordDiff μ i f) 2 (Measure.infinitePi μ) :=
  hf.sub (memLp_coordAvg i hf)

/-- When `e i = n`, the increment `E_{W_{n+1}} f - E_{W_n} f` is `E_{W_{n+1}} (D_i f)`. -/
theorem increment_ae_eq {e : ι → ℕ} (he : Function.Injective e) {n : ℕ} {i : ι} (hi : e i = n)
    (hfm : Measurable f) (hfi : Integrable f (Measure.infinitePi μ)) :
    (fun x => integrateOut μ (tailSet e (n + 1)) f x - integrateOut μ (tailSet e n) f x)
      =ᵐ[Measure.infinitePi μ] integrateOut μ (tailSet e (n + 1)) (Cited.coordDiff μ i f) := by
  have htower := integrateOut_integrateOut (S := tailSet e (n + 1)) (T := {i}) hfi
  rw [Set.union_comm, tailSet_succ_union he hi, ← coordAvg_eq_integrateOut i hfm] at htower
  filter_upwards [htower, integrateOut_sub_ae (T := tailSet e (n + 1)) hfi
    (integrable_coordAvg i hfi)] with x h1 h2
  have hcd : Cited.coordDiff μ i f = fun x => f x - coordAvg μ i f x := rfl
  rw [← h1, hcd]
  exact h2.symm

omit [∀ i, IsProbabilityMeasure (μ i)] [DecidableEq ι] in
theorem increment_eq_zero {e : ι → ℕ} {n : ℕ} (hn : ∀ i, e i ≠ n) (x : ∀ i, X i) :
    integrateOut μ (tailSet e (n + 1)) f x - integrateOut μ (tailSet e n) f x = 0 := by
  rw [tailSet_succ_eq hn, sub_self]

/-- The `L¹` norm of the increment at `e i` is at most `‖D_i f‖₁`. -/
theorem integral_abs_increment_le {e : ι → ℕ} (he : Function.Injective e) {n : ℕ} {i : ι}
    (hi : e i = n) (hfm : Measurable f) (hf : MemLp f 2 (Measure.infinitePi μ)) :
    ∫ x, |integrateOut μ (tailSet e (n + 1)) f x - integrateOut μ (tailSet e n) f x|
      ∂Measure.infinitePi μ ≤ ∫ x, |Cited.coordDiff μ i f x| ∂Measure.infinitePi μ := by
  have hfi : Integrable f (Measure.infinitePi μ) := hf.integrable one_le_two
  rw [integral_congr_ae ((increment_ae_eq he hi hfm hfi).mono fun x hx => by
    dsimp only at hx; rw [hx])]
  exact integral_abs_integrateOut_le ((memLp_coordDiff i hf).integrable one_le_two)

omit [DecidableEq ι] in
/-- Reindexing a nonnegative family along an injection `e : ι → ℕ`. -/
theorem tsum_le_tsum_of_injective {e : ι → ℕ} (he : Function.Injective e) {a : ℕ → ℝ}
    {b : ι → ℝ} (ha : ∀ n, 0 ≤ a n) (hab : ∀ i, a (e i) ≤ b i)
    (hout : ∀ n, (∀ i, e i ≠ n) → a n = 0) (hb : Summable b) :
    Summable a ∧ ∑' n, a n ≤ ∑' i, b i := by
  set B : ℕ → ℝ := Function.extend e b 0
  have hB : HasSum B (∑' i, b i) := (hasSum_extend_zero he).2 hb.hasSum
  have haB : ∀ n, a n ≤ B n := by
    intro n
    by_cases h : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := h
      simp only [B, he.extend_apply]
      exact hab i
    · push Not at h
      rw [hout n h]
      simp only [B]
      rw [Function.extend_apply' _ _ _ (by simpa using h)]
      rfl
  have hsa : Summable a := hB.summable.of_nonneg_of_le ha haB
  exact ⟨hsa, (hsa.tsum_le_tsum haB hB.summable).trans_eq hB.tsum_eq⟩

end IsotropicVariance.Infra.Entropy
