/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
import CurvatureVariance.Infra.FPP.Model
import CurvatureVariance.Infra.FPP.Walks

/-!
# The closing: the base case

`baseCaseStatement_holds` proves `Contracts.BaseCaseStatement`: for every `x ∈ ℤ^d`,
`|T(0,x) − μ(x)| ≤ O₁(θ)` for some `θ` depending only on `x` and the law (the proof of Theorem
`thm:main`, for the finitely many small lengths and points: "the passage time along a path of
`|x|_1` edges, which has an exponential moment by (W)"). The passage time
is at most the cost of a coordinate path from `0` to `x`, which has the exponential moment of (W)
(`Infra.FPP.IsIIDWeights.integrable_exp_mul_walkCost`); `exists_isOs_one_of_lintegral_exp` turns a
finite exponential moment into an `O₁` bound, by dominated convergence as the scale tends to
infinity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Closing

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- A nonnegative random variable with a finite exponential moment is `O₁(θ)` for some `θ`. -/
theorem exists_isOs_one_of_lintegral_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Ω → ℝ} (hSm : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω) {β : ℝ}
    (hβ : 0 < β) (hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (β * S ω)) ∂P < ⊤) :
    ∃ θ : ℝ, 0 < θ ∧ CurvatureVariance.IsOs P 1 θ S := by
  set G : ℕ → Ω → ℝ≥0∞ :=
    fun k ω => ENNReal.ofReal (Real.exp ((max (S ω) 0 / (((k : ℝ) + 1) / β)) ^ (1 : ℝ)))
    with hGdef
  have hG : ∀ k ω, G k ω = ENNReal.ofReal (Real.exp (β * S ω * (1 / ((k : ℝ) + 1)))) := by
    intro k ω
    simp only [hGdef, max_eq_left (hS0 ω), Real.rpow_one]
    congr 2
    field_simp
  have hmeas : ∀ k, Measurable (G k) := by
    intro k
    have : G k = fun ω => ENNReal.ofReal (Real.exp (β * S ω * (1 / ((k : ℝ) + 1)))) :=
      funext (hG k)
    rw [this]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hSm.const_mul β).mul_const _))
  have hbound : ∀ k, G k ≤ᵐ[P] fun ω => ENNReal.ofReal (Real.exp (β * S ω)) := by
    intro k
    refine ae_of_all _ fun ω => ?_
    rw [hG]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h0 : 0 ≤ β * S ω := mul_nonneg hβ.le (hS0 ω)
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc β * S ω * (1 / ((k : ℝ) + 1)) ≤ β * S ω * 1 :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = β * S ω := mul_one _
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 1) := by
    refine ae_of_all _ fun ω => ?_
    have h1 : Tendsto (fun k : ℕ => β * S ω * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (β * S ω)
    have h2 := (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto 0).comp h1)
    simp only [Real.exp_zero, ENNReal.ofReal_one] at h2
    refine h2.congr (fun k => ?_)
    simp [hG]
  have hT := tendsto_lintegral_of_dominated_convergence _ hmeas hbound hfin.ne hlim
  rw [lintegral_const, measure_univ, one_mul] at hT
  obtain ⟨k, hk⟩ :=
    (hT.eventually (gt_mem_nhds (show (1 : ℝ≥0∞) < 2 by norm_num))).exists
  exact ⟨((k : ℝ) + 1) / β, by positivity, hSm.aemeasurable, hk.le⟩

/-- **The base case** (in the proof of Theorem `thm:main`): `θ` is built from the law of the bounds
and `x` alone, before the model; a model that fits the bounds has this law. -/
theorem baseCaseStatement_holds (m : ℕ) : BaseCaseStatement m := by
  intro bd hbd x
  have := hbd.law.probP
  have := hbd.law.probF
  obtain ⟨α, hα, hαi⟩ := hbd.law.assumptionW.1
  obtain ⟨γ, hγ, -⟩ := Infra.FPP.exists_isPath_length_eq_l1Dist (0 : Vertex m) x
  set c := bd.law.μ.1 (point x) with hcdef
  have hc : 0 ≤ c := apply_nonneg _ _
  set S : Config m → ℝ := fun ω => (walkCost ω γ : ℝ) + c with hSdef
  have hSm : Measurable S := (Infra.FPP.measurable_walkCost_real γ).add_const c
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => add_nonneg (NNReal.coe_nonneg _) hc
  have hint : Integrable (fun ω => Real.exp (α * (walkCost ω γ : ℝ))) bd.law.P :=
    Infra.FPP.IsIIDWeights.integrable_exp_mul_walkCost hbd.law.iid γ hγ.edges_nodup hαi
  have hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (α * S ω)) ∂bd.law.P < ⊤ := by
    have h := (hint.const_mul (Real.exp (α * c))).lintegral_lt_top
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun ω => ?_)) h
    congr 1
    rw [hSdef, mul_add, Real.exp_add, mul_comm]
  obtain ⟨θ, hθ, hOs⟩ := exists_isOs_one_of_lintegral_exp hSm hS0 hα hfin
  have hTm : Measurable fun ω : Config m => passageTimeReal ω 0 x - c :=
    (Infra.FPP.measurable_passageTime_real 0 x).sub_const c
  refine ⟨θ, hθ, fun M _ hfit => ?_⟩
  rw [hfit.P_eq, hfit.μ_eq]
  refine ⟨hTm.aemeasurable, hOs.mono zero_le_one hθ
    ((continuous_abs.measurable.comp hTm).aemeasurable) (ae_of_all _ fun ω => ?_)⟩
  have hT0 : 0 ≤ passageTimeReal ω 0 x := NNReal.coe_nonneg _
  have hTle : passageTimeReal ω 0 x ≤ (walkCost ω γ : ℝ) := by
    exact_mod_cast Infra.FPP.passageTime_le_walkCost ω γ
  show |passageTimeReal ω 0 x - c| ≤ (walkCost ω γ : ℝ) + c
  rw [abs_le]
  constructor <;> linarith

end CurvatureVariance.Paper.Closing
