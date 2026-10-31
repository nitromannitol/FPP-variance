/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.Basic
public import CurvatureVariance.Paper.Proofs.Responses.Basic
import CurvatureVariance.Paper.Proofs.Responses.Slabs
import CurvatureVariance.Infra.EfronStein.Coordinates
import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exponential moments over the slabs of equation `eq:rowenergy`

The probabilistic part of the proof of equation `eq:rowenergy` (the proof of Lemma
`lem:rowenergy`, as in the proof of [AB26, Lemma 4.3]): for fixed indices the errors are
independent over the slabs, so half the quadratic term is kept and the exponential Markov
inequality applies; summing over index sequences starting at `0`, with free final index, costs
`(2 ∑_z e^{−c|z|²})^M`.

* `lintegral_prod_local`: under i.i.d. weights, functions of pairwise disjoint sets of edges have
  the product of their integrals as the integral of their product.
* `exists_isOs_of_lintegral_le`: the exponential Markov inequality in `O₁` form: if
  `E Z ≤ B`, one `G ≤ O₁(θ)` has `Φ ≤ θ log(2B) + G` whenever `e^{Φ/θ} ≤ Z`.
* `slabSet`, `pairwise_disjoint_slabSet`, `slabTimeReal_congr`: the slabs of width `s` own disjoint
  edges, and slab passage times read only their own weights.
* `exists_isOs_sum_local`: a sum of `n` independent `O₁(θ)` variables is at most
  `θ log(2·2ⁿ) + O₁(θ)`.
* `pathOf`, `exists_isOs_pathSum`: the sum over index paths `J` with `J₀ = 0` and jumps in a finite
  set `B` of the products `∏ᵢ Eᵢ(J_{i−1}, J_i) g(J_i − J_{i−1})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Moments.ExpArray

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

/-! ## Independence of functions of disjoint edge sets -/

/-- Under i.i.d. weights, functions of pairwise disjoint sets of edges are independent, so the
integral of their product is the product of their integrals. -/
theorem lintegral_prod_local {F : Measure ℝ≥0} [IsProbabilityMeasure F] {P : Measure (Config m)}
    (hP : IsIIDWeights P F) {ι : Type*} (S : ι → Set (Edge m))
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) (Φ : ι → Config m → ℝ≥0∞)
    (hΦ : ∀ i, Measurable (Φ i))
    (hloc : ∀ i (ω ω' : Config m), (∀ e ∈ S i, ω e = ω' e) → Φ i ω = Φ i ω') (s : Finset ι) :
    ∫⁻ ω, ∏ i ∈ s, Φ i ω ∂P = ∏ i ∈ s, ∫⁻ ω, Φ i ω ∂P := by
  classical
  rw [Infra.FPP.IsIIDWeights.eq_infinitePi hP]
  let ext : (i : ι) → ((S i) → ℝ≥0) → Config m :=
    fun i x e => if h : e ∈ S i then x ⟨e, h⟩ else 0
  have hext : ∀ i, Measurable (ext i) := by
    intro i
    refine measurable_pi_iff.mpr fun e => ?_
    by_cases h : e ∈ S i
    · simp only [ext, h, dite_true]; exact measurable_pi_apply _
    · simp only [ext, h, dite_false]; exact measurable_const
  have hind := Infra.EfronStein.iIndepFun_comp_restrict_infinitePi
    (X := fun _ : Edge m => ℝ≥0) (fun _ => F) S hS (fun i => Φ i ∘ ext i)
    (fun i => (hΦ i).comp (hext i))
  have hfun : (fun i (ω : Config m) => (Φ i ∘ ext i) (fun j : S i => ω j)) = Φ := by
    funext i ω
    exact hloc i _ _ (fun e he => by simp [ext, he])
  rw [hfun] at hind
  exact lintegral_prod_eq_prod_lintegral_of_indepFun s Φ hind hΦ

/-! ## The exponential Markov inequality in `O₁` form -/

/-- The integrand of `O₁(θ)` dominates `e^{X/θ}`. -/
theorem lintegral_exp_le_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {θ : ℝ}
    {X : Ω → ℝ} (hX : IsOs P 1 θ X) (hθ : 0 < θ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω / θ)) ∂P ≤ 2 := by
  refine (lintegral_mono fun ω => ?_).trans hX.2
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_one]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (le_max_left _ _) hθ.le)

/-- **Exponential Markov in `O₁` form.** If `E Z ≤ B` with `B ≥ 1`, there is `G ≤ O₁(θ)` such
that almost surely every `Φ` with `e^{Φ/θ} ≤ Z` satisfies `Φ ≤ θ log(2B) + G`. -/
theorem exists_isOs_of_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞} (hZ : Measurable Z) {B θ : ℝ} (hB : 1 ≤ B)
    (hθ : 0 < θ) (hint : ∫⁻ ω, Z ω ∂P ≤ ENNReal.ofReal B) :
    ∃ G : Ω → ℝ, IsOs P 1 θ G ∧ ∀ᵐ ω ∂P, ∀ Φ : ℝ,
      ENNReal.ofReal (Real.exp (Φ / θ)) ≤ Z ω → Φ ≤ θ * Real.log (2 * B) + G ω := by
  have hB0 : 0 < B := by linarith
  set G : Ω → ℝ := fun ω => θ * Real.log (max (Z ω).toReal 1) - θ * Real.log (2 * B) with hG
  have hGm : Measurable G :=
    ((hZ.ennreal_toReal.max measurable_const).log.const_mul θ).sub_const _
  refine ⟨G, ⟨hGm.aemeasurable, ?_⟩, ?_⟩
  · have hpt : ∀ ω, ENNReal.ofReal (Real.exp ((max (G ω) 0 / θ) ^ (1 : ℝ))) ≤
        1 + ENNReal.ofReal (1 / (2 * B)) * (Z ω + 1) := by
      intro ω
      rcases eq_or_ne (Z ω) ⊤ with h | h
      · have hne : ENNReal.ofReal (1 / (2 * B)) ≠ 0 := by
          rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
        rw [h, top_add, ENNReal.mul_top hne, add_top]
        exact le_top
      · set x := (Z ω).toReal with hx
        have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
        have hZx : Z ω = ENNReal.ofReal x := (ENNReal.ofReal_toReal h).symm
        have hexpG : Real.exp (G ω / θ) = max x 1 / (2 * B) := by
          simp only [hG]
          rw [← mul_sub, mul_div_cancel_left₀ _ hθ.ne', Real.exp_sub,
            Real.exp_log (lt_max_of_lt_right one_pos), Real.exp_log (by positivity)]
        have h1 : Real.exp ((max (G ω) 0 / θ) ^ (1 : ℝ)) ≤ 1 + 1 / (2 * B) * (x + 1) := by
          rw [Real.rpow_one]
          have hnn : 0 ≤ 1 / (2 * B) * (x + 1) := by positivity
          rcases le_total (G ω) 0 with hg | hg
          · rw [max_eq_right hg, zero_div, Real.exp_zero]; linarith
          · rw [max_eq_left hg, hexpG]
            have hm : max x 1 ≤ x + 1 := max_le (by linarith) (by linarith)
            have : max x 1 / (2 * B) ≤ 1 / (2 * B) * (x + 1) := by
              rw [div_eq_mul_one_div, mul_comm]
              exact mul_le_mul_of_nonneg_left hm (by positivity)
            linarith
        calc ENNReal.ofReal (Real.exp ((max (G ω) 0 / θ) ^ (1 : ℝ)))
            ≤ ENNReal.ofReal (1 + 1 / (2 * B) * (x + 1)) := ENNReal.ofReal_le_ofReal h1
          _ = 1 + ENNReal.ofReal (1 / (2 * B)) * (Z ω + 1) := by
            rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hx0 zero_le_one,
              ENNReal.ofReal_one, hZx]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (G ω) 0 / θ) ^ (1 : ℝ))) ∂P
        ≤ ∫⁻ ω, (1 + ENNReal.ofReal (1 / (2 * B)) * (Z ω + 1)) ∂P := lintegral_mono hpt
      _ = 1 + ENNReal.ofReal (1 / (2 * B)) * (∫⁻ ω, Z ω ∂P + 1) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul (ENNReal.ofReal (1 / (2 * B))) (f := fun ω => Z ω + 1)
              (hZ.add_const 1),
            lintegral_add_left hZ, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + ENNReal.ofReal (1 / (2 * B)) * (ENNReal.ofReal B + 1) := by gcongr
      _ ≤ 2 := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hB0.le zero_le_one,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add zero_le_one (by positivity)]
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
          apply ENNReal.ofReal_le_ofReal
          have : 1 / (2 * B) * (B + 1) ≤ 1 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
            linarith
          linarith
  · have hfin : ∀ᵐ ω ∂P, Z ω < ⊤ :=
      ae_lt_top hZ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hint)
    filter_upwards [hfin] with ω hω Φ hΦ
    have hx : Real.exp (Φ / θ) ≤ (Z ω).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hω.ne).mp hΦ
    have h1 : Φ / θ ≤ Real.log (max (Z ω).toReal 1) := by
      rw [Real.le_log_iff_exp_le (lt_max_of_lt_right one_pos)]
      exact hx.trans (le_max_left _ _)
    have h2 : Φ ≤ θ * Real.log (max (Z ω).toReal 1) := by
      rw [div_le_iff₀ hθ] at h1; linarith
    simp only [hG]
    linarith

/-! ## Slabs -/

/-- The edges of the slab `[is, (i+1)s]`, as a set of edges of the lattice. -/
def slabSet (s i : ℕ) : Set (Edge m) :=
  {e | e.1 ∈ slabEdges ((i : ℤ) * s) (((i : ℤ) + 1) * s)}

/-- Distinct slabs of a row own disjoint edges. -/
theorem pairwise_disjoint_slabSet (s : ℕ) :
    Pairwise fun i j : ℕ => Disjoint (slabSet (m := m) s i) (slabSet s j) := by
  intro i j hij
  have h := Responses.pairwise_disjoint_slabEdges (m := m) 0 s hij
  simp only [zero_add] at h
  exact Disjoint.preimage _ h

/-- The slabs indexed by `Fin n` own disjoint edges. -/
theorem pairwise_disjoint_slabSet_fin (s n : ℕ) :
    Pairwise fun i j : Fin n => Disjoint (slabSet (m := m) s i) (slabSet s j) :=
  fun _ _ hij => pairwise_disjoint_slabSet s (fun h => hij (Fin.ext h))

/-- A slab passage time reads only the weights of its slab. -/
theorem slabTimeReal_congr {p q : ℤ} (u v : Vertex m) {ω ω' : Config m}
    (h : ∀ e : Edge m, e.1 ∈ slabEdges p q → ω e = ω' e) :
    slabTimeReal ω p q u v = slabTimeReal ω' p q u v := by
  unfold slabTimeReal slabTime
  rw [Responses.restrictedTime_congr _ u v h]

/-- Slab passage times are measurable. -/
theorem measurable_slabTimeReal (p q : ℤ) (u v : Vertex m) :
    Measurable fun ω : Config m => slabTimeReal ω p q u v :=
  (Responses.measurable_restrictedTime _ u v).ennreal_toReal

/-! ## Sums of independent `O₁` variables -/

/-- A sum of `n` independent `O₁(θ)` variables, each a function of its own set of edges, is at
most `θ log(2·2ⁿ) + O₁(θ)`. -/
theorem exists_isOs_sum_local {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} [IsProbabilityMeasure P] (hP : IsIIDWeights P F) {n : ℕ}
    (S : Fin n → Set (Edge m)) (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (V : Fin n → Config m → ℝ) (hV : ∀ i, Measurable (V i))
    (hloc : ∀ i (ω ω' : Config m), (∀ e ∈ S i, ω e = ω' e) → V i ω = V i ω') {θ : ℝ}
    (hθ : 0 < θ) (hOs : ∀ i, IsOs P 1 θ (V i)) :
    ∃ G : Config m → ℝ, IsOs P 1 θ G ∧
      ∀ᵐ ω ∂P, ∑ i, V i ω ≤ θ * Real.log (2 * 2 ^ n) + G ω := by
  set Z : Config m → ℝ≥0∞ := fun ω => ∏ i, ENNReal.ofReal (Real.exp (V i ω / θ)) with hZ
  have hZm : Measurable Z :=
    Finset.measurable_prod _ fun i _ => ((hV i).div_const θ).exp.ennreal_ofReal
  have hint : ∫⁻ ω, Z ω ∂P ≤ ENNReal.ofReal (2 ^ n) := by
    rw [hZ, lintegral_prod_local hP S hS (fun i ω => ENNReal.ofReal (Real.exp (V i ω / θ)))
      (fun i => ((hV i).div_const θ).exp.ennreal_ofReal)
      (fun i ω ω' h => by rw [hloc i ω ω' h])]
    calc ∏ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (V i ω / θ)) ∂P ≤ ∏ _i : Fin n, (2 : ℝ≥0∞) :=
          Finset.prod_le_prod fun i _ => lintegral_exp_le_two (hOs i) hθ
      _ = ENNReal.ofReal (2 ^ n) := by simp
  obtain ⟨G, hG, hae⟩ := exists_isOs_of_lintegral_le hZm (one_le_pow₀ (by norm_num)) hθ hint
  refine ⟨G, hG, ?_⟩
  filter_upwards [hae] with ω hω
  apply hω
  refine le_of_eq ?_
  simp only [hZ]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), Finset.sum_div,
    Real.exp_sum]

/-! ## Index paths -/

/-- The jumps `Δ` extended by zero to all of `ℕ`. -/
def jumpExt {n : ℕ} (Δ : Fin n → Fin m → ℤ) (l : ℕ) : Fin m → ℤ :=
  if h : l < n then Δ ⟨l, h⟩ else 0

/-- The index path starting at `0` with jumps `Δ`: `J_i = Δ_0 + ⋯ + Δ_{i−1}`. -/
def pathOf {n : ℕ} (Δ : Fin n → Fin m → ℤ) (i : ℕ) : Fin m → ℤ :=
  ∑ l ∈ Finset.range i, jumpExt Δ l

theorem pathOf_succ_sub {n : ℕ} (Δ : Fin n → Fin m → ℤ) (i : Fin n) :
    pathOf Δ ((i : ℕ) + 1) - pathOf Δ i = Δ i := by
  simp [pathOf, Finset.sum_range_succ, jumpExt, i.isLt]

/-- An index path starting at `0` is the path of its jumps. -/
theorem pathOf_jumps {n : ℕ} (J : Fin (n + 1) → Fin m → ℤ) (h0 : J 0 = 0) :
    ∀ (i : ℕ) (hi : i < n + 1),
      pathOf (fun l : Fin n => J l.succ - J l.castSucc) i = J ⟨i, hi⟩ := by
  intro i
  induction i with
  | zero => intro hi; simp [pathOf, ← h0]
  | succ i ih =>
    intro hi
    have hi' : i < n := by omega
    rw [pathOf, Finset.sum_range_succ, ← pathOf, ih (by omega)]
    simp only [jumpExt, hi', dite_true]
    have h1 : (⟨i, hi'⟩ : Fin n).castSucc = ⟨i, by omega⟩ := rfl
    have h2 : (⟨i, hi'⟩ : Fin n).succ = ⟨i + 1, hi⟩ := rfl
    rw [h1, h2]
    abel

/-- **Penalized sums over index paths.** Let `Eᵢ(j, k)` be measurable, a function of the edges of
`Sᵢ` (pairwise disjoint), with `E Eᵢ(j,k) ≤ 2` whenever `k − j ∈ B`. If `∑_{z∈B} 2 g(z) ≤ B_c`, then
one `G ≤ O₁(θ)` has, almost surely, `Φ ≤ θ log(2 B_cⁿ) + G` for every index path `J` with `J₀ = 0`
and jumps in `B` and every `Φ` with `e^{Φ/θ} ≤ ∏ᵢ Eᵢ(J_i, J_{i+1}) g(J_{i+1} − J_i)`. -/
theorem exists_isOs_pathSum {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} [IsProbabilityMeasure P] (hP : IsIIDWeights P F) {n : ℕ}
    (S : Fin n → Set (Edge m)) (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (E : Fin n → (Fin m → ℤ) → (Fin m → ℤ) → Config m → ℝ≥0∞)
    (hEm : ∀ i j k, Measurable (E i j k))
    (hloc : ∀ i j k (ω ω' : Config m), (∀ e ∈ S i, ω e = ω' e) → E i j k ω = E i j k ω')
    (B : Finset (Fin m → ℤ)) (hE : ∀ i j k, k - j ∈ B → ∫⁻ ω, E i j k ω ∂P ≤ 2)
    (g : (Fin m → ℤ) → ℝ≥0∞) {Bc : ℝ} (hBc : 1 ≤ Bc)
    (hg : ∑ z ∈ B, 2 * g z ≤ ENNReal.ofReal Bc) {θ : ℝ} (hθ : 0 < θ) :
    ∃ G : Config m → ℝ, IsOs P 1 θ G ∧ ∀ᵐ ω ∂P, ∀ J : Fin (n + 1) → Fin m → ℤ, J 0 = 0 →
      (∀ i : Fin n, J i.succ - J i.castSucc ∈ B) → ∀ Φ : ℝ,
        ENNReal.ofReal (Real.exp (Φ / θ)) ≤
          ∏ i : Fin n, E i (J i.castSucc) (J i.succ) ω * g (J i.succ - J i.castSucc) →
        Φ ≤ θ * Real.log (2 * Bc ^ n) + G ω := by
  set Z : Config m → ℝ≥0∞ := fun ω => ∑ Δ ∈ Fintype.piFinset (fun _ : Fin n => B),
    ∏ i : Fin n, E i (pathOf Δ i) (pathOf Δ ((i : ℕ) + 1)) ω * g (Δ i) with hZ
  have hZm : Measurable Z :=
    Finset.measurable_sum _ fun Δ _ => Finset.measurable_prod _ fun i _ =>
      (hEm _ _ _).mul_const _
  have hint : ∫⁻ ω, Z ω ∂P ≤ ENNReal.ofReal (Bc ^ n) := by
    rw [hZ, lintegral_finsetSum _ fun Δ _ => Finset.measurable_prod _ fun i _ =>
      (hEm _ _ _).mul_const _]
    calc ∑ Δ ∈ Fintype.piFinset (fun _ : Fin n => B),
          ∫⁻ ω, ∏ i : Fin n, E i (pathOf Δ i) (pathOf Δ ((i : ℕ) + 1)) ω * g (Δ i) ∂P
        ≤ ∑ Δ ∈ Fintype.piFinset (fun _ : Fin n => B), ∏ i : Fin n, 2 * g (Δ i) := by
          refine Finset.sum_le_sum fun Δ hΔ => ?_
          rw [lintegral_prod_local hP S hS
            (fun i ω => E i (pathOf Δ i) (pathOf Δ ((i : ℕ) + 1)) ω * g (Δ i))
            (fun i => (hEm _ _ _).mul_const _)
            (fun i ω ω' h => by rw [hloc i _ _ ω ω' h])]
          refine Finset.prod_le_prod fun i _ => ?_
          rw [lintegral_mul_const _ (hEm _ _ _)]
          gcongr
          apply hE
          rw [pathOf_succ_sub]
          exact Fintype.mem_piFinset.mp hΔ i
      _ = (∑ z ∈ B, 2 * g z) ^ n := by
          rw [Finset.sum_prod_piFinset B (fun _ z => 2 * g z)]
          simp
      _ ≤ ENNReal.ofReal Bc ^ n := by gcongr
      _ = ENNReal.ofReal (Bc ^ n) := (ENNReal.ofReal_pow (by linarith) n).symm
  obtain ⟨G, hG, hae⟩ := exists_isOs_of_lintegral_le hZm (one_le_pow₀ hBc) hθ hint
  refine ⟨G, hG, ?_⟩
  filter_upwards [hae] with ω hω J hJ0 hJB Φ hΦ
  apply hω
  refine hΦ.trans ?_
  set Δ : Fin n → Fin m → ℤ := fun l => J l.succ - J l.castSucc with hΔ
  have hmem : Δ ∈ Fintype.piFinset (fun _ : Fin n => B) := Fintype.mem_piFinset.mpr hJB
  have hterm : ∏ i : Fin n, E i (J i.castSucc) (J i.succ) ω * g (J i.succ - J i.castSucc) =
      ∏ i : Fin n, E i (pathOf Δ i) (pathOf Δ ((i : ℕ) + 1)) ω * g (Δ i) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pathOf_jumps J hJ0 i (by omega), pathOf_jumps J hJ0 ((i : ℕ) + 1) (by omega)]
    rfl
  rw [hterm, hZ]
  exact Finset.single_le_sum (f := fun Δ => ∏ i : Fin n,
    E i (pathOf Δ i) (pathOf Δ ((i : ℕ) + 1)) ω * g (Δ i)) (fun _ _ => zero_le) hmem

end CurvatureVariance.Paper.Moments.ExpArray
