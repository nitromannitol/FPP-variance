/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ParentTuples
public import CurvatureVariance.Statements.Inputs.MeasureAbsPassageTimeSubIntegralLe
public import CurvatureVariance.Infra.Os.Tail
import CurvatureVariance.Statements.Inputs.IsOsOfMeasureGeLe
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Estimates for Lemma `lem:parent`

Ingredients of the proof of Lemma `lem:parent`:

* `isOs_lowerDev`: by the lower Gaussian bound at all scales of [ADH, Theorem 3.13]
  (`measure_abs_passageTime_sub_integral_le`), `(E T(0,x) − T(0,x))₊ ≤ O₂(2 √((|x|₁ + 1)/C₁))`.
* `Q_le_of_mul_le`, `rpow_third_le_Q`, `sqrt_mul_rpow_le_Q`: `Q_s ≤ M^{−1/3} Q_ℓ` for `Ms ≤ ℓ`,
  `Q_ℓ ≥ ℓ^{1/3}` and `Q_ℓ ≥ √ℓ ℓ^{−δ/K}`.
* `eventually_le_rpow`: `C ≤ N^p` for `N` large.
* `abs_le_of_parts`: the deterministic combination of the bounds in the proof of Lemma
  `lem:parent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments.Parent

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

/-! ## The lower deviations -/

/-- The positive part of an `O_s(θ)` variable is `O_s(θ)`. -/
theorem isOs_max_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {s θ : ℝ} {X : Ω → ℝ}
    (hX : IsOs P s θ X) : IsOs P s θ (fun ω => max (X ω) 0) := by
  refine ⟨hX.1.max aemeasurable_const, ?_⟩
  simpa only [max_eq_left (le_max_right _ (0 : ℝ))] using hX.2

/-- **Lower deviations** ([ADH, Theorem 3.13], lower tail at all scales): there is `C₁ > 0` with
`(E T(0,x) − T(0,x))₊ ≤ O₂(2 √((|x|₁ + 1)/C₁))` for every `x ≠ 0`. -/
theorem isOs_lowerDev {M : Law m} (hM : M.Valid) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ x : Vertex m, x ≠ 0 →
      IsOs M.P 2 (2 * Real.sqrt ((l1Norm x + 1) / C₁)) (fun ω =>
        max ((∫ ω', passageTimeReal ω' 0 x ∂M.P) - passageTimeReal ω 0 x) 0) := by
  have := hM.probF
  have := hM.probP
  obtain ⟨C₁, C₂, hC₁, -, h⟩ :=
    measure_abs_passageTime_sub_integral_le hM.one_le_m M.F hM.assumptionW
  refine ⟨C₁, hC₁, fun x hx => ?_⟩
  obtain ⟨-, -, hlow⟩ := h M.P hM.iid x hx
  set θ := Real.sqrt ((l1Norm x + 1) / C₁) with hθ
  have hθ0 : 0 < θ := Real.sqrt_pos.mpr (by positivity)
  set X : Config m → ℝ := fun ω => (∫ ω', passageTimeReal ω' 0 x ∂M.P) - passageTimeReal ω 0 x
    with hX
  have hXm : AEMeasurable X M.P :=
    (measurable_const.sub (measurable_passageTimeReal 0 x)).aemeasurable
  have hsC : 0 < Real.sqrt C₁ := Real.sqrt_pos.mpr hC₁
  have htail : ∀ u : ℝ, 0 ≤ u → M.P {ω | θ * u ≤ X ω} ≤
      ENNReal.ofReal (Real.exp (-(u ^ (2 : ℝ)))) := by
    intro u hu
    set τ := u / Real.sqrt C₁ with hτ
    have hτ0 : 0 ≤ τ := div_nonneg hu hsC.le
    have hθτ : τ * Real.sqrt (l1Norm x : ℝ) ≤ θ * u := by
      have h1 : Real.sqrt (l1Norm x : ℝ) / Real.sqrt C₁ ≤ θ := by
        rw [hθ, Real.sqrt_div' _ hC₁.le]
        exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hsC.le
      calc τ * Real.sqrt (l1Norm x : ℝ) = Real.sqrt (l1Norm x : ℝ) / Real.sqrt C₁ * u := by
            rw [hτ]; ring
        _ ≤ θ * u := mul_le_mul_of_nonneg_right h1 hu
    have hsub : {ω | θ * u ≤ X ω} ⊆ {ω | (passageTime ω 0 x : ℝ) -
        ∫ ω', (passageTime ω' 0 x : ℝ) ∂M.P ≤ -(τ * Real.sqrt (l1Norm x : ℝ))} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, hX, passageTimeReal] at hω ⊢
      linarith
    refine (measure_mono hsub).trans ((hlow τ hτ0).trans (ENNReal.ofReal_le_ofReal ?_))
    apply Real.exp_le_exp.mpr
    rw [Real.rpow_two, hτ, div_pow, Real.sq_sqrt hC₁.le]
    field_simp
    exact le_rfl
  have h1 := CurvatureVariance.isOs_of_measure_ge_le two_pos hθ0 hXm htail
  have h2 : (2 : ℝ) ^ (1 / (2 : ℝ)) * θ ≤ 2 * θ := by
    have : (2 : ℝ) ^ (1 / (2 : ℝ)) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / (2 : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    nlinarith
  exact isOs_max_zero (h1.mono_scale (by norm_num) (by positivity) h2)

/-! ## The scales -/

section Scales

variable {M : Model m} {K : ℕ} {A : ℝ}

theorem Q_exponent_bounds (hM : M.Standing) (hK : 10 ^ 4 ≤ K) :
    (1 : ℝ) / 3 ≤ 1 / 2 - M.δ / K ∧ M.δ / K ≤ M.δ / 10000 := by
  have hK' : (10000 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : M.δ / K ≤ M.δ / 10000 := div_le_div_of_nonneg_left hM.delta_pos.le (by norm_num) hK'
  refine ⟨?_, h1⟩
  have := hM.delta_le_one
  have : M.δ / 10000 ≤ 1 / 10000 := by linarith
  linarith

/-- `Q_s ≤ (1/Ms)^{1/3} Q_ℓ` for `1 ≤ s`, `Ms s ≤ ℓ`. -/
theorem Q_le_of_mul_le (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 0 ≤ A) {s ℓ Ms : ℝ}
    (hs : 0 < s) (hMs : 1 ≤ Ms) (hℓ : Ms * s ≤ ℓ) :
    Q M K A s ≤ (1 / Ms) ^ ((1 : ℝ) / 3) * Q M K A ℓ := by
  obtain ⟨hp, -⟩ := Q_exponent_bounds hM hK
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ
  have hsl : s / ℓ ≤ 1 / Ms := by
    rw [div_le_div_iff₀ hℓ0 (by linarith)]; linarith
  have h1 : (s / ℓ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ (1 / Ms) ^ ((1 : ℝ) / 2 - M.δ / K) :=
    Real.rpow_le_rpow (by positivity) hsl (by linarith)
  have h2 : (1 / Ms) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ (1 / Ms) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one (by linarith)]; exact hMs)
      hp
  have h3 : s ^ ((1 : ℝ) / 2 - M.δ / K) =
      (s / ℓ) ^ ((1 : ℝ) / 2 - M.δ / K) * ℓ ^ ((1 : ℝ) / 2 - M.δ / K) := by
    rw [Real.div_rpow hs.le hℓ0.le, div_mul_cancel₀ _ (by positivity)]
  unfold Q
  rw [h3]
  have h4 : 0 ≤ ℓ ^ ((1 : ℝ) / 2 - M.δ / K) := by positivity
  calc A * ((s / ℓ) ^ ((1 : ℝ) / 2 - M.δ / K) * ℓ ^ ((1 : ℝ) / 2 - M.δ / K))
      ≤ A * ((1 / Ms) ^ ((1 : ℝ) / 3) * ℓ ^ ((1 : ℝ) / 2 - M.δ / K)) := by gcongr; linarith
    _ = (1 / Ms) ^ ((1 : ℝ) / 3) * (A * ℓ ^ ((1 : ℝ) / 2 - M.δ / K)) := by ring

/-- `Q_ℓ ≥ ℓ^{1/3}` for `ℓ ≥ 1`, `A ≥ 1`. -/
theorem rpow_third_le_Q (hM : M.Standing) (hK : 10 ^ 4 ≤ K) (hA : 1 ≤ A) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    ℓ ^ ((1 : ℝ) / 3) ≤ Q M K A ℓ := by
  obtain ⟨hp, -⟩ := Q_exponent_bounds hM hK
  unfold Q
  calc ℓ ^ ((1 : ℝ) / 3) ≤ ℓ ^ ((1 : ℝ) / 2 - M.δ / K) := Real.rpow_le_rpow_of_exponent_le hℓ hp
    _ ≤ A * ℓ ^ ((1 : ℝ) / 2 - M.δ / K) := le_mul_of_one_le_left (by positivity) hA

/-- `Q_ℓ ≥ √ℓ · ℓ^{−δ/K}` for `A ≥ 1`. -/
theorem sqrt_mul_rpow_le_Q (hA : 1 ≤ A) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Real.sqrt ℓ * ℓ ^ (-(M.δ / K)) ≤ Q M K A ℓ := by
  unfold Q
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hℓ]
  have : (1 : ℝ) / 2 + -(M.δ / K) = 1 / 2 - M.δ / K := by ring
  rw [this]
  exact le_mul_of_one_le_left (by positivity) hA

end Scales

/-! ## Eventual bounds -/

/-- For `p > 0`, eventually `C ≤ N^p`. -/
theorem eventually_le_rpow (C : ℝ) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ p :=
  tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hp).eventually_ge_atTop C)

/-! ## The deterministic combination -/

/-- The combination in the proof of Lemma `lem:parent`: with `T ≤ T₀ + T_c`, `T₀ ≤ T + T_c`,
`|μ − μ₀| ≤ d`, `T₀ ≤ F`, `|F − μ₀| ≤ B`, `μ₀ ≤ E T₀`, and `F ≤ T₀ + B_S` on `𝒢` (indicator `ι` of
`𝒢ᶜ`), `|T − μ| ≤ B + T_c + d + B_S + ι (E T₀ − T₀)₊`. -/
theorem abs_le_of_parts {T μ T₀ μ₀ F Tc d B BS E₀ ι : ℝ} (hT : T ≤ T₀ + Tc) (hT₀ : T₀ ≤ T + Tc)
    (hμ : |μ - μ₀| ≤ d) (hF : T₀ ≤ F) (hB : |F - μ₀| ≤ B) (hE : μ₀ ≤ E₀)
    (hBS : 0 ≤ BS) (hι : (ι = 0 ∧ F ≤ T₀ + BS) ∨ ι = 1) :
    |T - μ| ≤ B + Tc + d + BS + ι * max (E₀ - T₀) 0 := by
  have h1 := abs_le.mp hμ
  have h2 := abs_le.mp hB
  have hm := le_max_left (E₀ - T₀) 0
  have hm0 := le_max_right (E₀ - T₀) 0
  have hι0 : 0 ≤ ι * max (E₀ - T₀) 0 := by
    rcases hι with ⟨h, -⟩ | h <;> rw [h] <;> linarith
  rw [abs_le]
  constructor
  · rcases hι with ⟨h, hG⟩ | h
    · rw [h]; linarith
    · rw [h]; linarith
  · linarith

end CurvatureVariance.Paper.Moments.Parent
