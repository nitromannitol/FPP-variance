/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Os.Basic
public import IsotropicVariance.Infra.Arrays.Basic
public import IsotropicVariance.Paper.Proofs.Profiles.OsTools
public import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The penalized supremum over lattice paths is `O_1`

The probabilistic core of the proof of Lemma `lem:rowenergy`: "The arrays `Z_i` are
independent over `i`, so ... The sum of these products over `k_1, …, k_M` is at most `C^M`. Hence a
union bound gives" the bound on the supremum.

For independent random variables `V_i` and functions `φ_i(k_{i−1}, k_i, ·)` with exponential
moments `E exp(φ_i / θ) ≤ 2`, the supremum over any finite set of lattice paths `k` (started at
`k_0 = 0`) of `Σ_i (φ_i(k_{i−1}, k_i, V_i) − cθ|k_i − k_{i−1}|²)`, minus `θ M log (2 G^m)` with
`G = Σ_{n ∈ ℤ} e^{−cn²}`, is `O_1(θ)` (`isOs_sup_penalized`). The exponential of the supremum is
at most the sum over the paths; by independence each term has expectation at most
`Π_i 2 e^{−c|Δ_i|²}`, and the increments `Δ_i = k_i − k_{i−1}` determine the path, so the sum over
the paths is at most `(2 G^m)^M`. The bound does not depend on the set of paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os

/-! ## The Gaussian sum -/

/-- `Σ_{n ∈ ℤ} e^{−c n²}`. -/
noncomputable def gaussSum1 (c : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-c * (n : ℝ) ^ 2)

/-- The constant of the union bound: `log (2 (Σ_n e^{−cn²})^m)`. -/
noncomputable def penaltyLog (c : ℝ) (m : ℕ) : ℝ := Real.log (2 * gaussSum1 c ^ m)

lemma summable_exp_neg_mul_sq_int {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2) := by
  have hnat : Summable fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2) := by
    refine Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith)
      (f := fun n : ℕ => (n : ℝ) ^ 2) fun i => ?_
    rcases Nat.eq_zero_or_pos i with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ i := by exact_mod_cast h
      nlinarith
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hnat
  · simpa using hnat

lemma one_le_gaussSum1 {c : ℝ} (hc : 0 < c) : 1 ≤ gaussSum1 c := by
  calc (1 : ℝ) = Real.exp (-c * ((0 : ℤ) : ℝ) ^ 2) := by simp
    _ ≤ gaussSum1 c :=
      (summable_exp_neg_mul_sq_int hc).le_tsum 0 fun j _ => (Real.exp_pos _).le

lemma gaussSum1_pos {c : ℝ} (hc : 0 < c) : 0 < gaussSum1 c :=
  one_pos.trans_le (one_le_gaussSum1 hc)

lemma penaltyLog_pos {c : ℝ} (hc : 0 < c) (m : ℕ) : 0 < penaltyLog c m := by
  apply Real.log_pos
  have := one_le_pow₀ (n := m) (one_le_gaussSum1 hc)
  linarith

lemma exp_penaltyLog {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Real.exp (penaltyLog c m) = 2 * gaussSum1 c ^ m := by
  have := gaussSum1_pos hc
  exact Real.exp_log (by positivity)

/-- A finite Gaussian sum over a box of `ℤ^m` is at most `G^m`. -/
lemma sum_piFinset_exp_le {c : ℝ} (hc : 0 < c) {m : ℕ} (T : Finset ℤ) :
    ∑ δ ∈ Fintype.piFinset (fun _ : Fin m => T), Real.exp (-c * ∑ l, ((δ l : ℤ) : ℝ) ^ 2) ≤
      gaussSum1 c ^ m := by
  have h1 (δ : Fin m → ℤ) : Real.exp (-c * ∑ l, ((δ l : ℤ) : ℝ) ^ 2) =
      ∏ l, Real.exp (-c * ((δ l : ℤ) : ℝ) ^ 2) := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Finset.prod_univ_sum (fun _ => T) (fun _ n => Real.exp (-c * (n : ℝ) ^ 2))]
  calc ∏ _l : Fin m, ∑ n ∈ T, Real.exp (-c * (n : ℝ) ^ 2) ≤ ∏ _l : Fin m, gaussSum1 c :=
        Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          fun _ _ => (summable_exp_neg_mul_sq_int hc).sum_le_tsum T
            fun _ _ => (Real.exp_pos _).le
    _ = gaussSum1 c ^ m := by simp

/-! ## Increments of lattice paths -/

/-- The increments `k_i − k_{i−1}` of the lattice path through `k_0 = 0` and `k`. -/
def increments {M m : ℕ} (k : Fin M → Fin m → ℤ) : Fin M → Fin m → ℤ :=
  fun i => k i - Infra.Arrays.pathPt 0 k i

/-- The increments determine the path. -/
lemma increments_injective {M m : ℕ} :
    Function.Injective (increments : (Fin M → Fin m → ℤ) → Fin M → Fin m → ℤ) := by
  intro k k' h
  have hp : ∀ j : ℕ, Infra.Arrays.pathPt 0 k j = Infra.Arrays.pathPt 0 k' j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      by_cases hj : j < M
      · have h1 := congrFun h ⟨j, hj⟩
        simp only [increments] at h1
        have e1 : Infra.Arrays.pathPt 0 k (j + 1) = k ⟨j, hj⟩ := by
          simp [Infra.Arrays.pathPt, hj]
        have e2 : Infra.Arrays.pathPt 0 k' (j + 1) = k' ⟨j, hj⟩ := by
          simp [Infra.Arrays.pathPt, hj]
        rw [e1, e2]
        rw [ih] at h1
        exact sub_left_injective h1
      · simp [Infra.Arrays.pathPt, hj]
  funext i
  have := hp ((i : ℕ) + 1)
  rwa [Infra.Arrays.pathPt_succ, Infra.Arrays.pathPt_succ] at this

/-- **The union bound over paths.** Summing the Gaussian weights of the increments over any set of
paths costs at most `(2 G^m)^M`. -/
lemma sum_prod_two_exp_le {c : ℝ} (hc : 0 < c) {M m : ℕ} (S : Finset (Fin M → Fin m → ℤ)) :
    ∑ k ∈ S, ∏ i : Fin M, (2 * Real.exp (-(c * ∑ l : Fin m,
      ((k i l : ℝ) - (Infra.Arrays.pathPt 0 k i l : ℝ)) ^ 2))) ≤ (2 * gaussSum1 c ^ m) ^ M := by
  classical
  let g : (Fin M → Fin m → ℤ) → ℝ := fun d =>
    ∏ i : Fin M, (2 * Real.exp (-c * ∑ l : Fin m, ((d i l : ℤ) : ℝ) ^ 2))
  have hg0 (d : Fin M → Fin m → ℤ) : 0 ≤ g d :=
    Finset.prod_nonneg fun _ _ => by positivity
  have hterm (k : Fin M → Fin m → ℤ) : ∏ i : Fin M, (2 * Real.exp (-(c * ∑ l : Fin m,
      ((k i l : ℝ) - (Infra.Arrays.pathPt 0 k i l : ℝ)) ^ 2))) = g (increments k) := by
    simp only [g, increments, Pi.sub_apply, Int.cast_sub, neg_mul]
  simp_rw [hterm]
  rw [← Finset.sum_image fun x _ y _ hxy => increments_injective hxy]
  -- All increments of paths of `S` take values in a finite set `T`.
  let T : Finset ℤ := (S.image increments).biUnion fun d =>
    Finset.univ.biUnion fun i => Finset.univ.image (d i)
  let B := Fintype.piFinset fun _ : Fin M => Fintype.piFinset fun _ : Fin m => T
  have hsub : S.image increments ⊆ B := by
    intro d hd
    rw [Fintype.mem_piFinset]
    intro i
    rw [Fintype.mem_piFinset]
    intro l
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => hg0 d).trans ?_
  have hB : ∑ d ∈ B, g d = ∏ _i : Fin M, ∑ δ ∈ Fintype.piFinset (fun _ : Fin m => T),
      2 * Real.exp (-c * ∑ l : Fin m, ((δ l : ℤ) : ℝ) ^ 2) :=
    (Finset.prod_univ_sum (fun _ => Fintype.piFinset fun _ : Fin m => T)
      (fun _ δ => 2 * Real.exp (-c * ∑ l : Fin m, ((δ l : ℤ) : ℝ) ^ 2))).symm
  rw [hB]
  calc ∏ _i : Fin M, ∑ δ ∈ Fintype.piFinset (fun _ : Fin m => T),
        2 * Real.exp (-c * ∑ l : Fin m, ((δ l : ℤ) : ℝ) ^ 2)
      ≤ ∏ _i : Fin M, (2 * gaussSum1 c ^ m) := by
        refine Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
          fun _ _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_piFinset_exp_le hc T) zero_le_two
    _ = (2 * gaussSum1 c ^ m) ^ M := by simp

/-! ## The exponential bound -/

/-- **The penalized supremum over lattice paths is `O_1(θ)`** (the proof of Lemma `lem:rowenergy`).
For independent `V_i` and exponential moments `E exp(φ_i(j, k, V_i)/θ) ≤ 2`, the supremum over any
nonempty finite set of paths `k` (with `k_0 = 0`) of `Σ_i (φ_i(k_{i−1}, k_i, V_i) − cθ|k_i −
k_{i−1}|²)`, minus `θ M log (2 G^m)`, is `O_1(θ)`. -/
theorem isOs_sup_penalized {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {M m : ℕ} (V : Fin M → Ω → β)
    (hV : ∀ i, Measurable (V i)) (hind : iIndepFun V P)
    (φ : Fin M → (Fin m → ℤ) → (Fin m → ℤ) → β → ℝ) (hφ : ∀ i j k, Measurable (φ i j k))
    {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c)
    (hmom : ∀ i j k, ∫⁻ ω, ENNReal.ofReal (Real.exp (φ i j k (V i ω) / θ)) ∂P ≤ 2)
    (S : Finset (Fin M → Fin m → ℤ)) (hS : S.Nonempty) :
    IsOs P 1 θ fun ω => S.sup' hS (fun k => ∑ i : Fin M,
      (φ i (Infra.Arrays.pathPt 0 k i) (k i) (V i ω) -
        c * θ * ∑ l : Fin m, ((k i l : ℝ) - (Infra.Arrays.pathPt 0 k i l : ℝ)) ^ 2)) -
      θ * M * penaltyLog c m := by
  -- The summands, their exponential weights and the penalties.
  let A : (Fin M → Fin m → ℤ) → Ω → ℝ := fun k ω => ∑ i : Fin M,
    (φ i (Infra.Arrays.pathPt 0 k i) (k i) (V i ω) -
      c * θ * ∑ l : Fin m, ((k i l : ℝ) - (Infra.Arrays.pathPt 0 k i l : ℝ)) ^ 2)
  let pen : (Fin M → Fin m → ℤ) → Fin M → ℝ := fun k i =>
    c * ∑ l : Fin m, ((k i l : ℝ) - (Infra.Arrays.pathPt 0 k i l : ℝ)) ^ 2
  let X : (Fin M → Fin m → ℤ) → Fin M → Ω → ℝ≥0∞ := fun k i ω =>
    ENNReal.ofReal (Real.exp (φ i (Infra.Arrays.pathPt 0 k i) (k i) (V i ω) / θ)) *
      ENNReal.ofReal (Real.exp (-pen k i))
  have hAm (k : Fin M → Fin m → ℤ) : Measurable (A k) :=
    Finset.measurable_sum _ fun i _ =>
      ((hφ i _ _).comp (hV i)).sub measurable_const
  have hsup : Measurable fun ω => S.sup' hS (fun k => A k ω) := by
    have h := Finset.measurable_sup' hS fun k _ => hAm k
    have heq : (fun ω => S.sup' hS (fun k => A k ω)) = S.sup' hS A := by
      funext ω
      exact (Finset.sup'_apply hS A ω).symm
    rwa [heq]
  have hUm : Measurable fun ω => S.sup' hS (fun k => A k ω) - θ * M * penaltyLog c m :=
    hsup.sub measurable_const
  change IsOs P 1 θ fun ω => S.sup' hS (fun k => A k ω) - θ * M * penaltyLog c m
  refine isOs_of_lintegral_exp_le_one hUm.aemeasurable ?_
  -- Pointwise: the exponential of the supremum is at most the sum over the paths.
  have hpt (ω : Ω) : ENNReal.ofReal (Real.exp ((S.sup' hS (fun k => A k ω) -
      θ * M * penaltyLog c m) / θ)) ≤
      ENNReal.ofReal (Real.exp (-(M * penaltyLog c m))) * ∑ k ∈ S, ∏ i : Fin M, X k i ω := by
    have hexpA (k : Fin M → Fin m → ℤ) : Real.exp (A k ω / θ) = ∏ i : Fin M,
        (Real.exp (φ i (Infra.Arrays.pathPt 0 k i) (k i) (V i ω) / θ) * Real.exp (-pen k i)) := by
      simp_rw [← Real.exp_add]
      rw [← Real.exp_sum]
      congr 1
      simp only [A, pen, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
      ring
    obtain ⟨k₀, hk₀, heq⟩ := S.exists_mem_eq_sup' hS fun k => A k ω
    have hsplit : (S.sup' hS (fun k => A k ω) - θ * M * penaltyLog c m) / θ =
        A k₀ ω / θ + -(M * penaltyLog c m) := by
      rw [heq]
      field_simp
      ring
    rw [hsplit, Real.exp_add, mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
    have hle : Real.exp (A k₀ ω / θ) ≤ ∑ k ∈ S, Real.exp (A k ω / θ) :=
      Finset.single_le_sum (f := fun k => Real.exp (A k ω / θ))
        (fun _ _ => (Real.exp_pos _).le) hk₀
    refine (ENNReal.ofReal_le_ofReal hle).trans_eq ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => (Real.exp_pos _).le]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hexpA, ENNReal.ofReal_prod_of_nonneg fun _ _ => by positivity]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  -- In expectation: independence along each path, then the union bound.
  have hpath (k : Fin M → Fin m → ℤ) : ∫⁻ ω, ∏ i : Fin M, X k i ω ∂P ≤
      ENNReal.ofReal (∏ i : Fin M, (2 * Real.exp (-pen k i))) := by
    have hXind : iIndepFun (X k) P := by
      have := hind.comp (fun i b => ENNReal.ofReal
          (Real.exp (φ i (Infra.Arrays.pathPt 0 k i) (k i) b / θ)) *
          ENNReal.ofReal (Real.exp (-pen k i)))
        fun i => (((hφ i _ _).div_const θ).exp.ennreal_ofReal).mul_const _
      exact this
    have hXm (i : Fin M) : Measurable (X k i) :=
      ((((hφ i _ _).comp (hV i)).div_const θ).exp.ennreal_ofReal).mul_const _
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hXind hXm,
      ENNReal.ofReal_prod_of_nonneg fun _ _ => by positivity]
    refine Finset.prod_le_prod fun i _ => ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul zero_le_two,
      ENNReal.ofReal_ofNat]
    exact mul_le_mul_left (hmom i _ _) _
  have hsum : ∑ k ∈ S, ∏ i : Fin M, (2 * Real.exp (-pen k i)) ≤ (2 * gaussSum1 c ^ m) ^ M :=
    sum_prod_two_exp_le hc S
  have hconst : Real.exp (-(M * penaltyLog c m)) * (2 * gaussSum1 c ^ m) ^ M = 1 := by
    rw [← exp_penaltyLog hc m, ← Real.exp_nat_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((S.sup' hS (fun k => A k ω) -
        θ * M * penaltyLog c m) / θ)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-(M * penaltyLog c m))) *
          ∑ k ∈ S, ∏ i : Fin M, X k i ω ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (-(M * penaltyLog c m))) *
          ∑ k ∈ S, ∫⁻ ω, ∏ i : Fin M, X k i ω ∂P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_finsetSum' _ fun k _ =>
          (Finset.measurable_prod _ fun i _ =>
            ((((hφ i _ _).comp (hV i)).div_const θ).exp.ennreal_ofReal).mul_const _).aemeasurable
    _ ≤ ENNReal.ofReal (Real.exp (-(M * penaltyLog c m))) *
          ENNReal.ofReal (∑ k ∈ S, ∏ i : Fin M, (2 * Real.exp (-pen k i))) := by
        gcongr
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
        exact Finset.sum_le_sum fun k _ => hpath k
    _ ≤ ENNReal.ofReal (Real.exp (-(M * penaltyLog c m))) *
          ENNReal.ofReal ((2 * gaussSum1 c ^ m) ^ M) := by
        gcongr
    _ = 1 := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hconst, ENNReal.ofReal_one]

end IsotropicVariance.Paper.Proofs.Profiles
