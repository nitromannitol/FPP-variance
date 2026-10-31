/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Infra.Os.Sum
public import CurvatureVariance.Infra.Os.Maximum
public import CurvatureVariance.Infra.FPP.Translation
public import CurvatureVariance.Infra.FPP.Model
import CurvatureVariance.Paper.Proofs.OsSum
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith

/-!
# Helpers for Section `sec:cubes`: constants in `O₁`, stationarity, the translated premise

Elementary tools for the proofs of the contracts of Section `sec:cubes`:

* `isOs_one_const`, `isOs_add`, `isOs_add_const`, `isOs_one_finset_sum`: a positive constant `c`
  is `O₁(2c)` and finite sums of `O₁` bounds add their scales ([AKM, Lemma A.4] with constant
  one).
* `isOs_comp_measurePreserving`, `isAbsOs_comp_measurePreserving`: an `O_s` bound is a statement
  about the law, so it transfers along measure-preserving maps (here translations of the lattice);
  `isAbsOs_upper`: the upper half of `|X| ≤ O_s(θ)`.
* `passageTimeReal_triangle`, `passageTimeReal_symm`, `passageTimeReal_nonneg`.
* `premise_isAbsOs_shift`, `premise_isAbsOs_pair`: the induction hypothesis, equation
  `eq:premise`, stated at the origin, holds from every lattice point, by the translation
  invariance of the i.i.d. law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

/-! ## Constants and sums in `O_s` -/

section Os

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `e^{1/2} ≤ 2`. -/
theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- A positive constant `c` is `O₁(2c)`: `E exp(c / 2c) = e^{1/2} ≤ 2`. -/
theorem isOs_one_const [IsProbabilityMeasure P] {c : ℝ} (hc : 0 < c) :
    IsOs P 1 (2 * c) (fun _ => c) := by
  refine ⟨aemeasurable_const, ?_⟩
  rw [lintegral_const, measure_univ, mul_one]
  have h : max c 0 / (2 * c) = 1 / 2 := by
    rw [max_eq_left hc.le]; field_simp
  rw [h, Real.rpow_one]
  calc ENNReal.ofReal (Real.exp (1 / 2)) ≤ ENNReal.ofReal 2 :=
        ENNReal.ofReal_le_ofReal exp_half_le_two
    _ = 2 := ENNReal.ofReal_ofNat 2

/-- [AKM, Lemma A.4] for two summands with exponent one: the scales add. -/
theorem isOs_add [IsProbabilityMeasure P] {θ η : ℝ} {X Y : Ω → ℝ} (hX : IsOs P 1 θ X)
    (hY : IsOs P 1 η Y) (hθ : 0 < θ) (hη : 0 < η) :
    IsOs P 1 (θ + η) (fun ω => X ω + Y ω) := by
  have h := CurvatureVariance.Paper.isOs_sum_of_one_le (P := P) (s := 1) le_rfl Finset.univ Finset.univ_nonempty
    ![θ, η] (fun i _ => by fin_cases i <;> simp [hθ, hη]) ![X, Y]
    (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

/-- Adding a nonnegative constant `c` to an `O₁(θ)` variable costs `2c` in the scale. -/
theorem isOs_add_const [IsProbabilityMeasure P] {θ c : ℝ} {X : Ω → ℝ} (hX : IsOs P 1 θ X)
    (hθ : 0 < θ) (hc : 0 ≤ c) : IsOs P 1 (θ + 2 * c) (fun ω => X ω + c) := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using hX
  · exact isOs_add hX (isOs_one_const hc) hθ (by linarith only [hc])

/-- An `O₁` bound for a sum over a finite family, with the sum of the scales. -/
theorem isOs_one_finset_sum [IsProbabilityMeasure P] {ι : Type*} (T : Finset ι) (hT : T.Nonempty)
    (θ : ι → ℝ) (hθ : ∀ i ∈ T, 0 < θ i) (X : ι → Ω → ℝ) (hX : ∀ i ∈ T, IsOs P 1 (θ i) (X i)) :
    IsOs P 1 (∑ i ∈ T, θ i) (fun ω => ∑ i ∈ T, X i ω) := by
  exact CurvatureVariance.Paper.isOs_sum_of_one_le (P := P) le_rfl T hT θ hθ X hX

/-- An `O_s` bound is a property of the law: it transfers along measure-preserving maps. -/
theorem isOs_comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {f : Ω' → Ω} (hf : MeasurePreserving f P' P) {s θ : ℝ} {X : Ω → ℝ} (hX : IsOs P s θ X) :
    IsOs P' s θ (fun ω => X (f ω)) := by
  refine ⟨hX.1.comp_quasiMeasurePreserving hf.quasiMeasurePreserving, ?_⟩
  have hg := aemeasurable_exp_pos_rpow hX.1 s θ
  rw [← hf.map_eq] at hg
  have h := lintegral_map' hg hf.measurable.aemeasurable
  rw [hf.map_eq] at h
  exact h.symm.le.trans hX.2

/-- Bounds `|X| ≤ O_s(θ)` transfer along measure-preserving maps. -/
theorem isAbsOs_comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {f : Ω' → Ω} (hf : MeasurePreserving f P' P) {s θ : ℝ} {X : Ω → ℝ} (hX : IsAbsOs P s θ X) :
    IsAbsOs P' s θ (fun ω => X (f ω)) :=
  ⟨hX.1.comp_quasiMeasurePreserving hf.quasiMeasurePreserving,
    isOs_comp_measurePreserving hf hX.2⟩

/-- The upper half of `|X| ≤ O_s(θ)`: `X ≤ O_s(θ)`. -/
theorem isAbsOs_upper {s θ : ℝ} {X : Ω → ℝ} (hX : IsAbsOs P s θ X) (hs : 0 ≤ s) (hθ : 0 < θ) :
    IsOs P s θ X :=
  hX.2.mono hs hθ hX.1 (Eventually.of_forall fun ω => le_abs_self (X ω))

end Os

/-! ## Real passage times -/

variable {m : ℕ}

theorem passageTimeReal_nonneg (ω : Config m) (u v : Vertex m) : 0 ≤ passageTimeReal ω u v :=
  NNReal.coe_nonneg _

theorem passageTimeReal_symm (ω : Config m) (u v : Vertex m) :
    passageTimeReal ω u v = passageTimeReal ω v u := by
  unfold passageTimeReal; rw [Infra.FPP.passageTime_symm]

theorem passageTimeReal_triangle (ω : Config m) (u v w : Vertex m) :
    passageTimeReal ω u w ≤ passageTimeReal ω u v + passageTimeReal ω v w := by
  unfold passageTimeReal
  exact_mod_cast Infra.FPP.passageTime_triangle ω u v w

theorem measurable_passageTimeReal (u v : Vertex m) :
    Measurable fun ω : Config m => passageTimeReal ω u v :=
  (Infra.FPP.measurable_passageTime u v).coe_nnreal_real

/-- The real passage time of the translated configuration. -/
theorem passageTimeReal_translate (a : Vertex m) (ω : Config m) (u v : Vertex m) :
    passageTimeReal (Infra.FPP.translate a ω) u v = passageTimeReal ω (u + a) (v + a) := by
  unfold passageTimeReal; rw [Infra.FPP.passageTime_translate]

/-- Under the standing hypotheses, every translation preserves the law of the weights. -/
theorem standing_measurePreserving_translate {M : Model m} (hM : M.Standing)
    (a : Vertex m) : MeasurePreserving (Infra.FPP.translate a) M.P M.P := by
  have := hM.probF
  exact Infra.FPP.IsIIDWeights.measurePreserving_translate hM.iid a

/-! ## The translated premise -/

/-- **The premise from every lattice point.** If equation `eq:premise` holds, then for every
vertex `x`, `1 ≤ s ≤ 2N/3` and `y ∈ 𝒟(s)`: `|T(x, x + (s, y)) − μ(s, y)| ≤ O₁(Q_s)`. -/
theorem premise_isAbsOs_shift {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {N : ℕ}
    (hPrem : Premise M K A N) (x : Vertex m) {s : ℕ} (hs1 : 1 ≤ s)
    (hsN : (s : ℝ) ≤ 2 * (N : ℝ) / 3) {y : Fin m → ℤ} (hy : y ∈ premiseDomain M s) :
    IsAbsOs M.P 1 (Q M K A s) (fun ω =>
      passageTimeReal ω x (x + ((s : ℤ), y)) - M.μ.1 (point ((s : ℤ), y))) := by
  have h := isAbsOs_comp_measurePreserving (standing_measurePreserving_translate hM x)
    (hPrem s hs1 hsN y hy)
  simpa only [passageTimeReal_translate, zero_add, add_comm x] using h

/-- The premise between two lattice points `x, x'` with `x'₁ − x₁ = s ∈ [1, 2N/3]` and
`x'₂ − x₂ ∈ 𝒟(s)`: `|T(x, x') − μ(x' − x)| ≤ O₁(Q_s)`. -/
theorem premise_isAbsOs_pair {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {N : ℕ}
    (hPrem : Premise M K A N) {x x' : Vertex m} {s : ℕ} (hs : x'.1 - x.1 = s) (hs1 : 1 ≤ s)
    (hsN : (s : ℝ) ≤ 2 * (N : ℝ) / 3) (hy : x'.2 - x.2 ∈ premiseDomain M s) :
    IsAbsOs M.P 1 (Q M K A s) (fun ω =>
      passageTimeReal ω x x' - M.μ.1 (point x' - point x)) := by
  have hx' : x' = x + ((s : ℤ), x'.2 - x.2) := by
    ext
    · simp only [Prod.fst_add]; omega
    · simp
  have h := premise_isAbsOs_shift hM hPrem x hs1 hsN hy
  rw [← hx'] at h
  have hpt : point ((s : ℤ), x'.2 - x.2) = point x' - point x := by
    rw [← Infra.FPP.point_sub]; congr 1; ext
    · simp only [Prod.fst_sub]; omega
    · simp
  simpa only [hpt] using h

end CurvatureVariance.Paper.Moments
