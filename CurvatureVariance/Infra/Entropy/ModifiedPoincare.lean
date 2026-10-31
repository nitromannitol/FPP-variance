/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Entropy.Tensorization
public import CurvatureVariance.Infra.Entropy.Martingale
public import CurvatureVariance.Infra.Entropy.LogSum

/-!
# The modified Poincaré inequality of Benaïm and Rossignol

[BR, Proposition 2.1] (Benaïm and Rossignol, *Exponential concentration for first passage
percolation through modified Poincaré inequalities*, Ann. Inst. Henri Poincaré Probab. Stat. 44
(2008), 544–573):
let `(X_i, μ_i)`, `i ∈ I` countable, be probability spaces, `A_i` linear spaces of functions on
`X_i` containing the constants, and `R_i` linear operators vanishing on constants such that
`Ent_{μ_i}(g²) ≤ E_{μ_i} (R_i g)²` for `g ∈ A_i`. If the `R_i` commute with integration over the
other coordinates, then for every `f` in the product class `A^I`,
`Var f · log (Var f / ∑ᵢ ‖Δ_i f‖₁²) ≤ ∑ᵢ E (R_i f)²`, where `Δ_i f = f - ∫ f dμ_i`.

## Reading of the statement

* `R_i` acts on real functions on `X_i` (a linear map on all functions; only its values on `A_i`
  matter), and is extended to the product by `R_i f (x) = R_i (f_{x_{-i}}) (x_i)`
  (`extendCoord`), as in Benaïm–Rossignol.
* `A^I` (`productDomain`) consists of the measurable `f ∈ L²` whose slices `f_{x_{-j}}` lie in
  `A_j` for almost every `x`. The extended operators `R_i f` are assumed square integrable, and
  the right side finite (otherwise the inequality is empty).
* The commutation hypothesis is required for integration over any set `T ∌ i` of coordinates;
  Benaïm and Rossignol state it for `T = I ∖ {i}`, but their proof uses it for the partial
  integrations defining the martingale increments. This stronger hypothesis is not derived here
  from the premise on page 5; for the centered-difference operators it is proved directly
  (`extendCoord_scaledDiff_integrateOut`).
* The logarithmic Sobolev inequality is stated with the extended entropy `eentropy`, which is
  `∞` when `g² log g²` is not integrable.

## Proof

Following Benaïm and Rossignol: enumerate the coordinates, write `f - E f = ∑ₙ Vₙ` with
martingale increments `Vₙ` (`CurvatureVariance.Infra.Entropy.Martingale`), apply tensorization and
the coordinate inequalities to each `Vₙ²`, use that the energies of the increments add up to at
most the energy of `f`, bound each `Ent (Vₙ²)` below by Falik–Samorodnitsky, and conclude by the
log-sum inequality.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace CurvatureVariance.Infra.Entropy

/-! ### Two measure-theoretic facts -/

theorem ofReal_integral_le_lintegral_ofReal' {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (f : Y → ℝ) : ENNReal.ofReal (∫ y, f y ∂ν) ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂ν := by
  by_cases hf : Integrable f ν
  · exact ofReal_integral_le_lintegral_ofReal hf
  · rw [integral_undef hf, ENNReal.ofReal_zero]; exact bot_le

theorem lintegral_lintegral_glue_ae {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {P : Measure Ω} {ν : Measure B} [SFinite ν] {φ : Ω × B → Ω}
    (hφ : MeasurePreserving φ (P.prod ν) P) {F : Ω → ℝ≥0∞} (hF : AEMeasurable F P) :
    ∫⁻ x, ∫⁻ y, F (φ (x, y)) ∂ν ∂P = ∫⁻ x, F x ∂P := by
  rw [← lintegral_prod (fun p => F (φ p))
    (hF.comp_quasiMeasurePreserving hφ.quasiMeasurePreserving)]
  conv_rhs => rw [← hφ.map_eq]
  rw [lintegral_map' (by rw [hφ.map_eq]; exact hF) hφ.aemeasurable]

section BenaimRossignol

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)] [DecidableEq ι]

/-! ### Coordinate operators on the product -/

/-- The extension of an operator `R` on functions of the coordinate `j` to functions on the
product, acting only on the coordinate `j`: `R_j f (x) = R (f_{x_{-j}}) (x_j)` with
`f_{x_{-j}} = fun y => f (update x j y)`. -/
noncomputable def extendCoord (j : ι) (R : (X j → ℝ) →ₗ[ℝ] (X j → ℝ)) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) : ℝ :=
  R (fun y => f (Function.update x j y)) (x j)

variable (μ) in
/-- The class `A^I` of Benaïm–Rossignol: measurable square-integrable functions on the product
whose slices `f_{x_{-j}}` lie in `A j` for almost every `x`, for every `j`. -/
def productDomain (A : ∀ i, Submodule ℝ (X i → ℝ)) : Set ((∀ i, X i) → ℝ) :=
  {f | Measurable f ∧ MemLp f 2 (Measure.infinitePi μ) ∧
    ∀ j, ∀ᵐ x ∂Measure.infinitePi μ, (fun y => f (Function.update x j y)) ∈ A j}

variable (μ) in
/-- The martingale increment `E_{W_{n+1}} f - E_{W_n} f` along the enumeration `e`. -/
noncomputable def increment (e : ι → ℕ) (f : (∀ i, X i) → ℝ) (n : ℕ) (x : ∀ i, X i) : ℝ :=
  integrateOut μ (tailSet e (n + 1)) f x - integrateOut μ (tailSet e n) f x

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- `E_T f` does not depend on a coordinate in `T`. -/
theorem integrateOut_update_of_mem {T : Set ι} {i : ι} (hi : i ∈ T) (f : (∀ j, X j) → ℝ)
    (x : ∀ j, X j) (y : X i) :
    integrateOut μ T f (Function.update x i y) = integrateOut μ T f x := by
  have h : Function.update x i y = splice T x (Function.update x i y) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [splice, hi]
    · by_cases hjT : j ∈ T <;> simp [splice, hjT, hj]
  rw [h, integrateOut_splice]

omit [∀ i, MeasurableSpace (X i)] in
theorem extendCoord_sub (i : ι) (R : (X i → ℝ) →ₗ[ℝ] (X i → ℝ)) (g h : (∀ j, X j) → ℝ)
    (x : ∀ j, X j) :
    extendCoord i R (fun z => g z - h z) x = extendCoord i R g x - extendCoord i R h x := by
  have e : (fun y => g (Function.update x i y) - h (Function.update x i y)) =
      (fun y => g (Function.update x i y)) - fun y => h (Function.update x i y) := rfl
  simp only [extendCoord, e, map_sub, Pi.sub_apply]

/-- The extended operator vanishes almost everywhere on functions constant in its coordinate. -/
theorem extendCoord_ae_eq_zero {i : ι} {R : (X i → ℝ) →ₗ[ℝ] (X i → ℝ)}
    (hR : R (fun _ => 1) =ᵐ[μ i] 0) {g : (∀ j, X j) → ℝ}
    (hg : ∀ x y, g (Function.update x i y) = g x) :
    extendCoord i R g =ᵐ[Measure.infinitePi μ] 0 := by
  have hev : (R (fun _ => 1)) ∘ (fun x : ∀ j, X j => x i) =ᵐ[Measure.infinitePi μ]
      (0 : X i → ℝ) ∘ (fun x : ∀ j, X j => x i) :=
    (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae_eq_comp hR
  filter_upwards [hev] with x hx
  have hslice : (fun y => g (Function.update x i y)) = (g x) • (fun _ : X i => (1 : ℝ)) := by
    funext y; simp [hg]
  simp only [Function.comp_apply, Pi.zero_apply] at hx
  simp only [extendCoord, hslice, map_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hx,
    mul_zero]

/-! ### The energies of the increments -/

variable {A : ∀ i, Submodule ℝ (X i → ℝ)} {R : ∀ i, (X i → ℝ) →ₗ[ℝ] (X i → ℝ)}
  {f : (∀ i, X i) → ℝ}

variable (μ) in
/-- `E_{W_n} h` when the coordinate `i` is among the first `n`, and `0` otherwise. -/
noncomputable def energyMart (e : ι → ℕ) (i : ι) (h : (∀ j, X j) → ℝ) (n : ℕ)
    (x : ∀ j, X j) : ℝ :=
  if e i < n then integrateOut μ (tailSet e n) h x else 0

theorem extendCoord_integrateOut_ae_eq (hRconst : ∀ i (c : ℝ), R i (fun _ => c) =ᵐ[μ i] 0)
    (hcomm : ∀ (T : Set ι) (j : ι), j ∉ T → extendCoord j (R j) (integrateOut μ T f)
      =ᵐ[Measure.infinitePi μ] integrateOut μ T (extendCoord j (R j) f))
    (e : ι → ℕ) (i : ι) (n : ℕ) :
    extendCoord i (R i) (integrateOut μ (tailSet e n) f) =ᵐ[Measure.infinitePi μ]
      energyMart μ e i (extendCoord i (R i) f) n := by
  by_cases hn : e i < n
  · have hi : i ∉ tailSet e n := by simp [tailSet]; omega
    filter_upwards [hcomm _ i hi] with x hx
    simp [energyMart, hn, hx]
  · have hi : i ∈ tailSet e n := by simp [tailSet]; omega
    filter_upwards [extendCoord_ae_eq_zero (μ := μ) (hRconst i 1)
      (fun x y => integrateOut_update_of_mem (μ := μ) hi f x y)] with x hx
    simp [energyMart, hn, hx]

theorem extendCoord_increment_ae_eq (hRconst : ∀ i (c : ℝ), R i (fun _ => c) =ᵐ[μ i] 0)
    (hcomm : ∀ (T : Set ι) (j : ι), j ∉ T → extendCoord j (R j) (integrateOut μ T f)
      =ᵐ[Measure.infinitePi μ] integrateOut μ T (extendCoord j (R j) f))
    (e : ι → ℕ) (i : ι) (n : ℕ) :
    extendCoord i (R i) (increment μ e f n) =ᵐ[Measure.infinitePi μ]
      fun x => energyMart μ e i (extendCoord i (R i) f) (n + 1) x -
        energyMart μ e i (extendCoord i (R i) f) n x := by
  filter_upwards [extendCoord_integrateOut_ae_eq hRconst hcomm e i (n + 1),
    extendCoord_integrateOut_ae_eq hRconst hcomm e i n] with x h1 h2
  rw [← h1, ← h2]
  exact extendCoord_sub i (R i) _ _ x

omit [DecidableEq ι] in
theorem memLp_energyMart {h : (∀ j, X j) → ℝ} (hh : MemLp h 2 (Measure.infinitePi μ))
    (e : ι → ℕ) (i : ι) (n : ℕ) : MemLp (energyMart μ e i h n) 2 (Measure.infinitePi μ) := by
  by_cases hn : e i < n
  · have : energyMart μ e i h n = integrateOut μ (tailSet e n) h := by
      funext x; simp [energyMart, hn]
    rw [this]; exact memLp_integrateOut hh
  · have : energyMart μ e i h n = 0 := by funext x; simp [energyMart, hn]
    rw [this]; exact MemLp.zero

omit [DecidableEq ι] in
theorem integral_sq_sub_energyMart {h : (∀ j, X j) → ℝ} (hh : MemLp h 2 (Measure.infinitePi μ))
    (e : ι → ℕ) (i : ι) (n : ℕ) :
    ∫ x, (energyMart μ e i h (n + 1) x - energyMart μ e i h n x) ^ 2 ∂Measure.infinitePi μ =
      ∫ x, energyMart μ e i h (n + 1) x ^ 2 ∂Measure.infinitePi μ -
        ∫ x, energyMart μ e i h n x ^ 2 ∂Measure.infinitePi μ := by
  rcases lt_trichotomy (e i) n with hn | hn | hn
  · have h1 : e i < n + 1 := by omega
    simp only [energyMart, hn, h1, ite_true]
    exact integral_sq_sub_integrateOut (tailSet_succ_subset e n) hh
  · have h1 : e i < n + 1 := by omega
    have h2 : ¬ e i < n := by omega
    simp [energyMart, h1, h2]
  · have h1 : ¬ e i < n + 1 := by omega
    have h2 : ¬ e i < n := by omega
    simp [energyMart, h1, h2]

/-- The energies of the increments add up to at most the energy of `f`. -/
theorem sum_range_integral_sq_extendCoord_increment_le
    (hRconst : ∀ i (c : ℝ), R i (fun _ => c) =ᵐ[μ i] 0)
    (hcomm : ∀ (T : Set ι) (j : ι), j ∉ T → extendCoord j (R j) (integrateOut μ T f)
      =ᵐ[Measure.infinitePi μ] integrateOut μ T (extendCoord j (R j) f))
    {i : ι} (hR2 : MemLp (extendCoord i (R i) f) 2 (Measure.infinitePi μ)) (e : ι → ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∫ x, extendCoord i (R i) (increment μ e f n) x ^ 2
      ∂Measure.infinitePi μ ≤ ∫ x, extendCoord i (R i) f x ^ 2 ∂Measure.infinitePi μ := by
  set h := extendCoord i (R i) f
  have hterm : ∀ n, ∫ x, extendCoord i (R i) (increment μ e f n) x ^ 2 ∂Measure.infinitePi μ =
      ∫ x, energyMart μ e i h (n + 1) x ^ 2 ∂Measure.infinitePi μ -
        ∫ x, energyMart μ e i h n x ^ 2 ∂Measure.infinitePi μ := by
    intro n
    rw [← integral_sq_sub_energyMart hR2 e i n]
    exact integral_congr_ae ((extendCoord_increment_ae_eq hRconst hcomm e i n).mono
      fun x hx => by dsimp only; rw [hx])
  simp_rw [hterm]
  rw [Finset.sum_range_sub (fun n => ∫ x, energyMart μ e i h n x ^ 2 ∂Measure.infinitePi μ)]
  have h0 : ∫ x, energyMart μ e i h 0 x ^ 2 ∂Measure.infinitePi μ = 0 := by
    simp [energyMart]
  rw [h0, sub_zero]
  by_cases hN : e i < N
  · have : energyMart μ e i h N = integrateOut μ (tailSet e N) h := by
      funext x; simp [energyMart, hN]
    rw [this]; exact integral_sq_integrateOut_le hR2
  · have : energyMart μ e i h N = 0 := by funext x; simp [energyMart, hN]
    rw [this]
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
    exact integral_nonneg fun x => sq_nonneg _

/-! ### The coordinate inequalities applied to an increment -/

/-- Integrating the coordinate inequality in `i` for a function `V` with slices in `A i`. -/
theorem lintegral_coordEntropy_sq_le
    (hLSI : ∀ i, ∀ g ∈ A i, eentropy (μ i) (fun y => g y ^ 2) ≤
      ENNReal.ofReal (∫ y, R i g y ^ 2 ∂μ i))
    {i : ι} {V : (∀ j, X j) → ℝ}
    (hVslice : ∀ᵐ x ∂Measure.infinitePi μ, (fun y => V (Function.update x i y)) ∈ A i)
    (hRV : MemLp (extendCoord i (R i) V) 2 (Measure.infinitePi μ)) :
    ∫⁻ x, coordEntropy μ i (fun z => V z ^ 2) x ∂Measure.infinitePi μ ≤
      ENNReal.ofReal (∫ x, extendCoord i (R i) V x ^ 2 ∂Measure.infinitePi μ) := by
  calc ∫⁻ x, coordEntropy μ i (fun z => V z ^ 2) x ∂Measure.infinitePi μ
      ≤ ∫⁻ x, ENNReal.ofReal (∫ y, R i (fun y => V (Function.update x i y)) y ^ 2 ∂μ i)
          ∂Measure.infinitePi μ :=
        lintegral_mono_ae (hVslice.mono fun x hx => hLSI i _ hx)
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (extendCoord i (R i) V (Function.update x i y) ^ 2) ∂μ i
          ∂Measure.infinitePi μ := by
        refine lintegral_mono fun x => (ofReal_integral_le_lintegral_ofReal' _).trans_eq ?_
        congr 1
        funext y
        simp [extendCoord]
    _ = ∫⁻ x, ENNReal.ofReal (extendCoord i (R i) V x ^ 2) ∂Measure.infinitePi μ :=
        lintegral_lintegral_glue_ae (measurePreserving_update μ i)
          (ENNReal.measurable_ofReal.comp_aemeasurable
            (hRV.aestronglyMeasurable.aemeasurable.pow_const 2))
    _ = ENNReal.ofReal (∫ x, extendCoord i (R i) V x ^ 2 ∂Measure.infinitePi μ) :=
        (ofReal_integral_eq_lintegral_ofReal hRV.integrable_sq
          (ae_of_all _ fun x => sq_nonneg _)).symm

/-! ### The modified Poincaré inequality -/

/-- **Benaïm–Rossignol, Proposition 2.1**, for one function `f`: the hypotheses on `f` are those
that the proof uses (slices of the partial integrals of `f` in `A_j`, and commutation of `R_j`
with integration over sets of coordinates not containing `j`). -/
theorem variance_mul_log_le_of_logSobolev_of_commute [Countable ι]
    (hconst : ∀ i (c : ℝ), (fun _ => c) ∈ A i)
    (hRconst : ∀ i (c : ℝ), R i (fun _ => c) =ᵐ[μ i] 0)
    (hLSI : ∀ i, ∀ g ∈ A i, eentropy (μ i) (fun y => g y ^ 2) ≤
      ENNReal.ofReal (∫ y, R i g y ^ 2 ∂μ i))
    (hfm : Measurable f) (hf : MemLp f 2 (Measure.infinitePi μ))
    (hslice : ∀ (T : Set ι) (j : ι), j ∉ T → ∀ᵐ x ∂Measure.infinitePi μ,
      (fun y => integrateOut μ T f (Function.update x j y)) ∈ A j)
    (hcomm : ∀ (T : Set ι) (j : ι), j ∉ T → extendCoord j (R j) (integrateOut μ T f)
      =ᵐ[Measure.infinitePi μ] integrateOut μ T (extendCoord j (R j) f))
    (hR2 : ∀ i, MemLp (extendCoord i (R i) f) 2 (Measure.infinitePi μ))
    (hsum : Summable fun i => ∫ x, extendCoord i (R i) f x ^ 2 ∂Measure.infinitePi μ) :
    ProbabilityTheory.variance f (Measure.infinitePi μ) *
        log (ProbabilityTheory.variance f (Measure.infinitePi μ) /
          ∑' i, (∫ x, |coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
      ∑' i, ∫ x, extendCoord i (R i) f x ^ 2 ∂Measure.infinitePi μ := by
  set P := Measure.infinitePi μ
  set Var := ProbabilityTheory.variance f P
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  set V : ℕ → (∀ j, X j) → ℝ := increment μ e f
  set a : ℕ → ℝ := fun n => ∫ x, V n x ^ 2 ∂P
  set b : ℕ → ℝ := fun n => (∫ x, |V n x| ∂P) ^ 2
  set S := ∑' i, ∫ x, extendCoord i (R i) f x ^ 2 ∂P
  have hS0 : 0 ≤ S := tsum_nonneg fun i => integral_nonneg fun x => sq_nonneg _
  have hV2 : ∀ n, MemLp (V n) 2 P := fun n =>
    (memLp_integrateOut hf).sub (memLp_integrateOut hf)
  have hVm : ∀ n, Measurable (V n) := fun n =>
    (measurable_integrateOut hfm).sub (measurable_integrateOut hfm)
  have ha : HasSum a Var := hasSum_integral_sq_increment e hfm hf
  have ha0 : ∀ n, 0 ≤ a n := fun n => integral_nonneg fun x => sq_nonneg _
  have hb0 : ∀ n, 0 ≤ b n := fun n => sq_nonneg _
  have hba : ∀ n, b n ≤ a n := by
    intro n
    have habs : MemLp (fun x => |V n x|) 2 P := (hV2 n).abs
    have := ProbabilityTheory.variance_nonneg (fun x => |V n x|) P
    rw [ProbabilityTheory.variance_eq_sub habs] at this
    simp only [Pi.pow_apply, sq_abs] at this
    simp only [a, b]
    linarith
  have hab0 : ∀ n, b n = 0 → a n = 0 := by
    intro n hn
    have h1 : ∫ x, |V n x| ∂P = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hn
    have hz := integral_eq_zero_imp_ae_zero (ae_of_all _ fun x => abs_nonneg (V n x))
      ((hV2 n).integrable one_le_two).abs h1
    simp only [a]
    refine integral_eq_zero_of_ae (hz.mono fun x hx => ?_)
    simp only [Pi.zero_apply, abs_eq_zero] at hx
    simp [hx]
  -- the slices of the increments lie in `A i`
  have hgslice : ∀ m i, ∀ᵐ x ∂P,
      (fun y => integrateOut μ (tailSet e m) f (Function.update x i y)) ∈ A i := by
    intro m i
    by_cases hi : i ∈ tailSet e m
    · refine ae_of_all _ fun x => ?_
      have : (fun y => integrateOut μ (tailSet e m) f (Function.update x i y)) =
          fun _ => integrateOut μ (tailSet e m) f x :=
        funext fun y => integrateOut_update_of_mem hi f x y
      rw [this]; exact hconst i _
    · exact hslice _ i hi
  have hVslice : ∀ n i, ∀ᵐ x ∂P, (fun y => V n (Function.update x i y)) ∈ A i := by
    intro n i
    filter_upwards [hgslice (n + 1) i, hgslice n i] with x h1 h2
    exact (A i).sub_mem h1 h2
  have hRV2 : ∀ n i, MemLp (extendCoord i (R i) (V n)) 2 P := fun n i =>
    ((memLp_energyMart (hR2 i) e i (n + 1)).sub (memLp_energyMart (hR2 i) e i n)).ae_eq
      (extendCoord_increment_ae_eq hRconst hcomm e i n).symm
  -- each increment: Falik–Samorodnitsky, tensorization and the coordinate inequalities
  have hEnt : ∀ n, ENNReal.ofReal (a n * log (a n / b n)) ≤
      ∑' i, ENNReal.ofReal (∫ x, extendCoord i (R i) (V n) x ^ 2 ∂P) := by
    intro n
    refine (ofReal_mul_log_div_le_eentropy_sq (hV2 n)).trans ?_
    refine (eentropy_le_tsum_coordEntropy (fun x => sq_nonneg _) ((hVm n).pow_const 2)
      (hV2 n).integrable_sq).trans ?_
    exact ENNReal.tsum_le_tsum fun i => lintegral_coordEntropy_sq_le hLSI (hVslice n i) (hRV2 n i)
  -- the energies of the increments
  have hEsum : ∀ i, ∑' n, ENNReal.ofReal (∫ x, extendCoord i (R i) (V n) x ^ 2 ∂P) ≤
      ENNReal.ofReal (∫ x, extendCoord i (R i) f x ^ 2 ∂P) := by
    intro i
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => integral_nonneg fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (sum_range_integral_sq_extendCoord_increment_le hRconst hcomm (hR2 i) e N)
  have hcomb : ∑' n, ENNReal.ofReal (a n * log (a n / b n)) ≤ ENNReal.ofReal S := by
    calc ∑' n, ENNReal.ofReal (a n * log (a n / b n))
        ≤ ∑' n, ∑' i, ENNReal.ofReal (∫ x, extendCoord i (R i) (V n) x ^ 2 ∂P) :=
          ENNReal.tsum_le_tsum hEnt
      _ = ∑' i, ∑' n, ENNReal.ofReal (∫ x, extendCoord i (R i) (V n) x ^ 2 ∂P) :=
          ENNReal.tsum_comm
      _ ≤ ∑' i, ENNReal.ofReal (∫ x, extendCoord i (R i) f x ^ 2 ∂P) :=
          ENNReal.tsum_le_tsum hEsum
      _ = ENNReal.ofReal S :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun x => sq_nonneg _)
            hsum).symm
  -- back to real numbers
  have ht0 : ∀ n, 0 ≤ a n * log (a n / b n) := by
    intro n
    rcases (hb0 n).eq_or_lt with hb | hb
    · simp [← hb]
    · exact mul_nonneg (ha0 n) (log_nonneg ((one_le_div hb).2 (hba n)))
  have hfin : ∑' n, ENNReal.ofReal (a n * log (a n / b n)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcomb
  have hts : Summable fun n => a n * log (a n / b n) := by
    have := ENNReal.summable_toReal hfin
    simpa only [ENNReal.toReal_ofReal (ht0 _)] using this
  have htle : ∑' n, a n * log (a n / b n) ≤ S := by
    have h1 := ENNReal.tsum_toReal_eq (f := fun n => ENNReal.ofReal (a n * log (a n / b n)))
      (fun n => ENNReal.ofReal_ne_top)
    simp only [ENNReal.toReal_ofReal (ht0 _)] at h1
    rw [← h1, ← ENNReal.toReal_ofReal hS0]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hcomb
  -- the log-sum inequality
  have hbs : Summable b := ha.summable.of_nonneg_of_le hb0 hba
  have hlogsum := mul_log_div_le_tsum ha0 hb0 hab0 ha hbs.hasSum hts
  set B' := ∑' n, b n
  have hB'0 : 0 ≤ B' := tsum_nonneg hb0
  have hB'pos : 0 < Var → 0 < B' := by
    intro hV
    rcases hB'0.eq_or_lt with h | h
    · exfalso
      have h0 : HasSum b 0 := by convert hbs.hasSum using 1
      have hbz : b = 0 := (hasSum_zero_iff_of_nonneg hb0).1 h0
      have haz : a = 0 := funext fun n => hab0 n (congrFun hbz n)
      rw [haz] at ha
      exact hV.ne' (ha.unique hasSum_zero)
    · exact h
  have hVar0 : 0 ≤ Var := ProbabilityTheory.variance_nonneg f P
  by_cases hBs : Summable fun i => (∫ x, |coordDiff μ i f x| ∂P) ^ 2
  · have hBB : B' ≤ ∑' i, (∫ x, |coordDiff μ i f x| ∂P) ^ 2 := by
      refine (tsum_le_tsum_of_injective he hb0 (fun i => ?_) (fun n hn => ?_) hBs).2
      · exact pow_le_pow_left₀ (integral_nonneg fun x => abs_nonneg _)
          (integral_abs_increment_le he rfl hfm hf) 2
      · simp only [b, V, increment, increment_eq_zero hn, abs_zero, integral_zero]
        norm_num
    calc Var * log (Var / ∑' i, (∫ x, |coordDiff μ i f x| ∂P) ^ 2)
        ≤ Var * log (Var / B') := by
          rcases hVar0.eq_or_lt with hV | hV
          · simp [← hV]
          have hB' := hB'pos hV
          refine mul_le_mul_of_nonneg_left (log_le_log (div_pos hV (hB'.trans_le hBB)) ?_) hVar0
          exact div_le_div_of_nonneg_left hVar0 hB' hBB
      _ ≤ ∑' n, a n * log (a n / b n) := hlogsum
      _ ≤ S := htle
  · rw [tsum_eq_zero_of_not_summable hBs, div_zero, log_zero, mul_zero]
    exact hS0

/-- **Benaïm–Rossignol, Proposition 2.1** (the modified Poincaré inequality on a countable
product). Let `μ i` be probability measures on `X i`, `A i` linear spaces of square-integrable
functions containing the constants, and `R i` linear operators with square-integrable values on
`A i`, vanishing on constants, such that `Ent_{μ i} (g²) ≤ E_{μ i} (R i g)²` for `g ∈ A i`.
Suppose that integrating `f ∈ A^I` over a set of coordinates not containing `i` stays in `A^I` and
commutes with the extension of `R i`. Then every `f ∈ A^I` with square-integrable `R_i f` and
`∑ᵢ E (R_i f)² < ∞` satisfies
`Var f · log (Var f / ∑ᵢ ‖Δ_i f‖₁²) ≤ ∑ᵢ E (R_i f)²`, with `Δ_i f = f - ∫ f dμ_i`. -/
theorem variance_mul_log_le_of_logSobolev [Countable ι]
    (A : ∀ i, Submodule ℝ (X i → ℝ)) (R : ∀ i, (X i → ℝ) →ₗ[ℝ] (X i → ℝ))
    (_hA2 : ∀ i, ∀ g ∈ A i, MemLp g 2 (μ i))
    (hconst : ∀ i (c : ℝ), (fun _ => c) ∈ A i)
    (_hR2 : ∀ i, ∀ g ∈ A i, MemLp (R i g) 2 (μ i))
    (hRconst : ∀ i (c : ℝ), R i (fun _ => c) =ᵐ[μ i] 0)
    (hLSI : ∀ i, ∀ g ∈ A i, eentropy (μ i) (fun y => g y ^ 2) ≤
      ENNReal.ofReal (∫ y, R i g y ^ 2 ∂μ i))
    (hcomm : ∀ i, ∀ f ∈ productDomain μ A, ∀ T : Set ι, i ∉ T →
      integrateOut μ T f ∈ productDomain μ A ∧
        extendCoord i (R i) (integrateOut μ T f) =ᵐ[Measure.infinitePi μ]
          integrateOut μ T (extendCoord i (R i) f)) :
    ∀ f ∈ productDomain μ A, (∀ i, MemLp (extendCoord i (R i) f) 2 (Measure.infinitePi μ)) →
      Summable (fun i => ∫ x, extendCoord i (R i) f x ^ 2 ∂Measure.infinitePi μ) →
      ProbabilityTheory.variance f (Measure.infinitePi μ) *
          log (ProbabilityTheory.variance f (Measure.infinitePi μ) /
            ∑' i, (∫ x, |coordDiff μ i f x| ∂Measure.infinitePi μ) ^ 2) ≤
        ∑' i, ∫ x, extendCoord i (R i) f x ^ 2 ∂Measure.infinitePi μ := by
  intro f hf hR2 hsum
  exact variance_mul_log_le_of_logSobolev_of_commute hconst hRconst hLSI hf.1 hf.2.1
    (fun T j hj => ((hcomm j f hf T hj).1).2.2 j) (fun T j hj => (hcomm j f hf T hj).2) hR2 hsum

end BenaimRossignol

end CurvatureVariance.Infra.Entropy
