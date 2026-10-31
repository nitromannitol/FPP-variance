/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
import CurvatureVariance.Statements.Inputs.IsOsMeasureGeLe
import CurvatureVariance.Infra.FPP.MeanDefs
import CurvatureVariance.Paper.Proofs.Mean.Domain
import CurvatureVariance.Infra.FPP.Model
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The upper estimate for the long minimum in Lemma `lem:smallmean`

The final paragraph of the proof of Lemma `lem:smallmean` compares the minimum with the unrestricted
passage time on a good event. These lemmas quantify its exceptional-set contribution and the decay
of the logarithmic comparison error relative to `Q_s`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

/-- The `O₂(C/S)` bound on a bad-event indicator gives its Gaussian tail at one. -/
theorem measure_compl_le_of_isOs_indicator {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set Ω} {C S : ℝ}
    (hC : 0 < C) (hS : 0 < S)
    (hbad : CurvatureVariance.IsOs P 2 (C / S) (Gᶜ.indicator fun _ => (1 : ℝ))) :
    P Gᶜ ≤ ENNReal.ofReal (2 * Real.exp (-((S / C) ^ 2))) := by
  have ht := hbad.measure_ge_le (by norm_num : (0 : ℝ) < 2)
    (div_pos hC hS) (div_nonneg hS.le hC.le)
  have hmul : C / S * (S / C) = 1 := by field_simp
  have heq : {ω | C / S * (S / C) ≤ (Gᶜ.indicator fun _ => (1 : ℝ)) ω} = Gᶜ := by
    ext ω
    rw [hmul]
    by_cases hω : ω ∈ Gᶜ
    · simp only [indicator_of_mem hω, le_refl, mem_ofPred_eq, hω]
    · simp only [indicator_of_notMem hω, mem_ofPred_eq, hω]
      norm_num
  simpa only [heq, Real.rpow_two] using ht

/-- The expectation of a bad-event indicator is bounded by the same tail probability. -/
theorem integral_indicator_le_of_isOs {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set Ω} {C S : ℝ}
    (hC : 0 < C) (hS : 0 < S)
    (hbad : CurvatureVariance.IsOs P 2 (C / S) (Gᶜ.indicator fun _ => (1 : ℝ))) :
    (∫ ω, (Gᶜ.indicator fun _ => (1 : ℝ)) ω ∂P) ≤
      2 * Real.exp (-((S / C) ^ 2)) := by
  have htail := measure_compl_le_of_isOs_indicator hC hS hbad
  have hI : Integrable (Gᶜ.indicator fun _ => (1 : ℝ)) P := by
    apply (integrable_const (1 : ℝ)).mono' hbad.1.aestronglyMeasurable
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ Gᶜ
    · rw [indicator_of_mem hω]
      norm_num
    · rw [indicator_of_notMem hω]
      norm_num
  have hnonneg : ∀ ω, 0 ≤ (Gᶜ.indicator fun _ => (1 : ℝ)) ω := fun ω =>
    indicator_nonneg (fun _ _ => zero_le_one) ω
  have hli : (∫⁻ ω, ENNReal.ofReal ((Gᶜ.indicator fun _ => (1 : ℝ)) ω) ∂P) ≤ P Gᶜ := by
    have heq : (fun ω => ENNReal.ofReal ((Gᶜ.indicator fun _ => (1 : ℝ)) ω)) =
        Gᶜ.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      by_cases hω : ω ∈ Gᶜ
      · simp only [indicator_of_mem hω, ENNReal.ofReal_one]
      · simp only [indicator_of_notMem hω, ENNReal.ofReal_zero]
    rw [heq]
    exact lintegral_indicator_one_le Gᶜ
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hnonneg)] at hli
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hli.trans htail)

/-- A good-event comparison can be integrated with a tunable second-moment error.
The parameter `R` is chosen polynomially large when the exceptional probability has a
Gaussian tail in `log s`. -/
theorem integral_le_of_good_event {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {G : Set Ω} {F T H : Ω → ℝ}
    {b C S R : ℝ} (hb : 0 ≤ b) (hC : 0 < C) (hS : 0 < S) (hR : 0 < R)
    (hF : Integrable F P) (hT : Integrable T P)
    (hH : Integrable (fun ω => H ω ^ 2) P) (hT0 : ∀ ω, 0 ≤ T ω)
    (hdom : ∀ ω, F ω ≤ H ω) (hgood : ∀ ω ∈ G, F ω ≤ T ω + b)
    (hbad : CurvatureVariance.IsOs P 2 (C / S) (Gᶜ.indicator fun _ => (1 : ℝ))) :
    (∫ ω, F ω ∂P) - (∫ ω, T ω ∂P) ≤
      b + (∫ ω, H ω ^ 2 ∂P) / (2 * R) + R * Real.exp (-((S / C) ^ 2)) := by
  let X : Ω → ℝ := Gᶜ.indicator fun _ => (1 : ℝ)
  have hXI : Integrable X P := by
    apply (integrable_const (1 : ℝ)).mono' hbad.1.aestronglyMeasurable
    apply Eventually.of_forall
    intro ω
    change ‖(Gᶜ.indicator fun _ => (1 : ℝ)) ω‖ ≤ 1
    by_cases hω : ω ∈ Gᶜ
    · rw [indicator_of_mem hω]
      norm_num
    · rw [indicator_of_notMem hω]
      norm_num
  have hpoint : ∀ ω, F ω ≤ T ω + b + H ω ^ 2 / (2 * R) + (R / 2) * X ω := by
    intro ω
    by_cases hω : ω ∈ G
    · have hx : X ω = 0 := indicator_of_notMem (by simpa using hω) _
      rw [hx, mul_zero, add_zero]
      exact (hgood ω hω).trans (le_add_of_nonneg_right (by positivity))
    · have hx : X ω = 1 := indicator_of_mem (by simpa using hω) _
      rw [hx, mul_one]
      have hY : H ω ≤ H ω ^ 2 / (2 * R) + R / 2 := by
        rw [show H ω ^ 2 / (2 * R) + R / 2 = (H ω ^ 2 + R ^ 2) / (2 * R) by
          field_simp]
        exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * R)).mpr
          (by nlinarith only [sq_nonneg (H ω - R)])
      linarith only [hdom ω, hY, hT0 ω, hb]
  have hbound := integral_mono hF (((hT.add (integrable_const b)).add
    (hH.div_const (2 * R))).add (hXI.const_mul (R / 2))) hpoint
  change (∫ ω, F ω ∂P) ≤ ∫ ω, T ω + b + H ω ^ 2 / (2 * R) + (R / 2) * X ω ∂P at hbound
  rw [integral_add (f := fun ω => T ω + b + H ω ^ 2 / (2 * R))
      (g := fun ω => R / 2 * X ω)
      ((hT.add (integrable_const b)).add (hH.div_const (2 * R))) (hXI.const_mul (R / 2)),
    integral_add (f := fun ω => T ω + b) (g := fun ω => H ω ^ 2 / (2 * R))
      (hT.add (integrable_const b)) (hH.div_const (2 * R)),
    integral_add (f := T) (g := fun _ => b) hT (integrable_const b), integral_const, integral_div,
    integral_const_mul, probReal_univ, one_smul] at hbound
  have htail := integral_indicator_le_of_isOs hC hS hbad
  have herror : R / 2 * (∫ ω, X ω ∂P) ≤ R * Real.exp (-((S / C) ^ 2)) := by
    calc R / 2 * (∫ ω, X ω ∂P) ≤ R / 2 * (2 * Real.exp (-((S / C) ^ 2))) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = R * Real.exp (-((S / C) ^ 2)) := by ring
  linarith only [hbound, herror]

/-- Every squared logarithmic comparison error is negligible relative to a positive power. -/
theorem tendsto_log_sq_div_rpow {q : ℝ} (hq : 0 < q) :
    Tendsto (fun s : ℝ => Real.log s ^ 2 / s ^ q) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hq).tendsto_div_nhds_zero
  simpa only [Real.rpow_two] using hh

/-- The logarithmic slab comparison error is uniformly negligible relative to `Q_s`,
even when `K` varies; only the lower bound `K ≥ 10⁴` and `A ≥ 1` is used. -/
theorem log_sq_le_mul_Q {m : ℕ} (bd : Bounds m) (hbd : bd.Valid)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 1 ≤ s₀ ∧ ∀ M : Model m, M.Standing → M.Fits bd → ∀ s : ℝ, s₀ ≤ s →
      ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ A : ℝ, 1 ≤ A →
        C * Real.log s ^ 2 ≤ ε * Q M K A s := by
  have hf : Tendsto (fun s : ℝ => C * (Real.log s ^ 2 / s ^ ((1 : ℝ) / 4)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := C)).mul (tendsto_log_sq_div_rpow (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 (hf.eventually (eventually_lt_nhds hε))
  refine ⟨max s₀ 1, le_max_right _ _, ?_⟩
  intro M hM hfit s hs K hK A hA
  have hs1 : 1 ≤ s := (le_max_right _ _).trans hs
  have hspos : 0 < s := zero_lt_one.trans_le hs1
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hK4 : (4 : ℝ) ≤ K := by exact_mod_cast (show 4 ≤ K by omega)
  have hq : (1 : ℝ) / 4 ≤ 1 / 2 - M.δ / K := by
    have hh : M.δ / K ≤ (1 : ℝ) / 4 := (div_le_iff₀ hKpos).2 (by
      have hδ : M.δ ≤ 1 := by rw [hfit.δ_eq]; exact hbd.law.delta_le_one
      linarith only [hδ, hK4])
    linarith only [hh]
  have hQ : s ^ ((1 : ℝ) / 4) ≤ Q M K A s := by
    calc s ^ ((1 : ℝ) / 4) ≤ s ^ ((1 : ℝ) / 2 - M.δ / K) :=
          Real.rpow_le_rpow_of_exponent_le hs1 hq
      _ ≤ A * s ^ ((1 : ℝ) / 2 - M.δ / K) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hA
            (Real.rpow_nonneg hspos.le _)
  have hsmall : C * Real.log s ^ 2 / s ^ ((1 : ℝ) / 4) ≤ ε := by
    simpa only [mul_div_assoc] using (hs₀ s ((le_max_left _ _).trans hs)).le
  exact ((div_le_iff₀ (Real.rpow_pos_of_pos hspos _)).1 hsmall).trans
    (mul_le_mul_of_nonneg_left hQ hε.le)

/-- The lattice one-norm scales exactly along natural multiples. -/
theorem oneNorm_nsmul {m : ℕ} (s : ℕ) (v : Vertex m) :
    oneNorm (s • v) = s * oneNorm v := by
  simp [oneNorm, nsmul_eq_mul, Int.natAbs_mul, Finset.mul_sum, mul_add]

/-- Classical mean excess at the long endpoint of the mean-lemma contradiction is
negligible relative to `s Q_s`, uniformly in the induction parameters. -/
theorem classical_long_mean_le_mul_Q {m : ℕ} (hclassical : ClassicalStatement m)
    (bd : Bounds m) (hbd : bd.Valid) (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℝ, 1 ≤ s₀ ∧ ∀ M : Model m, M.Standing → M.Fits bd → ∀ s : ℕ, s₀ ≤ s → ∀ y₀ : Fin m → ℤ,
      ‖transversePoint y₀‖ ≤ (bd.T + 1) * s → ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ A : ℝ, 1 ≤ A →
        (∫ ω, passageTimeReal ω 0 (s • ((s : ℤ), y₀)) ∂M.P) -
            s * M.μ.1 (point ((s : ℤ), y₀)) ≤ ε * s * Q M K A s := by
  obtain ⟨C, hC, hclassical⟩ := hclassical bd hbd
  let d : ℝ := ((m : ℝ) + 1) * (bd.T + 1)
  let D : ℝ := Real.log (d + 2) + 2
  have hd : 0 < d := by dsimp [d]; have := hbd.T_nonneg; positivity
  have hD : 0 < D := by
    have hlog : 0 ≤ Real.log (d + 2) := Real.log_nonneg (by linarith only [hd])
    dsimp [D]
    linarith only [hlog]
  obtain ⟨s₀, hs₀1, hs₀⟩ := log_sq_le_mul_Q bd hbd (C * Real.sqrt (d * D)) ε hε
  refine ⟨max s₀ (Real.exp 1), hs₀1.trans (le_max_left _ _), ?_⟩
  intro M hM hfit s hs y₀ hy₀ K hK A hA
  have hs1 : (1 : ℝ) ≤ s := hs₀1.trans ((le_max_left _ _).trans hs)
  have hspos : (0 : ℝ) < s := zero_lt_one.trans_le hs1
  have hlogs : 1 ≤ Real.log (s : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hs)
    simpa only [Real.log_exp] using hh
  let v : Vertex m := ((s : ℤ), y₀)
  let x : Vertex m := s • v
  have hv : oneNorm v ≤ d * s :=
    oneNorm_le_of_transverse_bound (by linarith only [hbd.T_nonneg]) hy₀
  have hx0 : x ≠ 0 := by
    intro hx
    have hh := congrArg Prod.fst hx
    have hsNat : 0 < s := by exact_mod_cast hspos
    simp [x, v, nsmul_eq_mul, Nat.ne_of_gt hsNat] at hh
  obtain ⟨_, _, _, hmean⟩ := hclassical M hM hfit x hx0
  have hr : oneNorm x ≤ d * (s : ℝ) ^ 2 := by
    change oneNorm (s • v) ≤ _
    rw [oneNorm_nsmul]
    have hh := mul_le_mul_of_nonneg_left hv hspos.le
    nlinarith only [hh]
  have hs2 : 1 ≤ (s : ℝ) ^ 2 := one_le_pow₀ hs1
  have hlogr : Real.log (2 + oneNorm x) ≤ D * Real.log s := by
    have hlogd : 0 ≤ Real.log (d + 2) := Real.log_nonneg (by linarith only [hd])
    calc Real.log (2 + oneNorm x) ≤ Real.log ((d + 2) * (s : ℝ) ^ 2) := by
          apply Real.log_le_log (by
            have hxnonneg : 0 ≤ oneNorm x := by dsimp [oneNorm]; positivity
            linarith only [hxnonneg])
          nlinarith only [hr, hs2]
      _ = Real.log (d + 2) + 2 * Real.log s := by
          rw [Real.log_mul (by linarith only [hd]) (by positivity), Real.log_pow]
          norm_num
      _ ≤ D * Real.log s := by
          have hh := mul_le_mul_of_nonneg_left hlogs hlogd
          dsimp [D]
          nlinarith only [hh]
  have hroot : Real.sqrt (oneNorm x * Real.log (2 + oneNorm x)) ≤
      Real.sqrt (d * D) * s * Real.log s ^ 2 := by
    have hxnonneg : 0 ≤ oneNorm x := by dsimp [oneNorm]; positivity
    have hlognonneg : 0 ≤ Real.log (2 + oneNorm x) := Real.log_nonneg (by linarith only [hxnonneg])
    have hprod := mul_le_mul hr hlogr hlognonneg (by positivity : 0 ≤ d * (s : ℝ) ^ 2)
    have hlogsq : Real.log (s : ℝ) ≤ Real.log s ^ 4 := by
      have hh : 1 ≤ Real.log (s : ℝ) ^ 3 := one_le_pow₀ hlogs
      have hhh := mul_le_mul_of_nonneg_left hh (zero_le_one.trans hlogs)
      nlinarith only [hhh]
    have hb : oneNorm x * Real.log (2 + oneNorm x) ≤
        (Real.sqrt (d * D) * s * Real.log s ^ 2) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hlogsq (by positivity : 0 ≤ d * D * (s : ℝ) ^ 2)
      have hsqrt := Real.sq_sqrt (mul_nonneg hd.le hD.le)
      calc
        oneNorm x * Real.log (2 + oneNorm x) ≤ d * (s : ℝ) ^ 2 * (D * Real.log s) := hprod
        _ ≤ d * D * (s : ℝ) ^ 2 * Real.log s ^ 4 := by
          convert hh using 1; ring
        _ = (Real.sqrt (d * D) * s * Real.log s ^ 2) ^ 2 := by
          simp only [mul_pow, hsqrt]
          ring
    exact Real.sqrt_le_iff.2 ⟨by positivity, hb⟩
  have hmu : M.μ.1 (point x) = s * M.μ.1 (point v) := by
    change M.μ.1 (point (s • v)) = _
    rw [CurvatureVariance.Infra.FPP.point_nsmul, map_smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg s)]
  rw [hmu] at hmean
  have hscalar := hs₀ M hM hfit s ((le_max_left _ _).trans hs) K hK A hA
  have hh := mul_le_mul_of_nonneg_left hroot hC.le
  have hh₂ := mul_le_mul_of_nonneg_left hscalar hspos.le
  change _ ≤ ε * s * Q M K A s
  change _ ≤ _ at hmean
  nlinarith only [hmean, hh, hh₂]

/-- The exponential moment in (W) supplies the square moment of a weight. -/
theorem integrable_weight_sq {m : ℕ} (M : Model m) (hM : M.Standing) :
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) M.F := by
  obtain ⟨α, hα, hexp⟩ := hM.assumptionW.1
  apply (hexp.const_mul ((2 / α) ^ 2)).mono'
    (measurable_coe_nnreal_real.pow_const 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hh := rpow_abs_le_mul_exp_abs (x : ℝ) (p := 2) (by norm_num) hα.ne'
  simpa only [Real.rpow_two, abs_of_pos hα, abs_of_nonneg (NNReal.coe_nonneg x)] using hh

/-- A finite sum has square moment at most the number of terms times the sum of square
moments; independence is unnecessary. -/
theorem integral_sq_sum_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {X : ι → Ω → ℝ}
    (hXm : ∀ i, AEStronglyMeasurable (X i) P)
    (hXsq : ∀ i, Integrable (fun ω => X i ω ^ 2) P) :
    Integrable (fun ω => (∑ i, X i ω) ^ 2) P ∧
      (∫ ω, (∑ i, X i ω) ^ 2 ∂P) ≤
        Fintype.card ι * ∑ i, ∫ ω, X i ω ^ 2 ∂P := by
  let B : Ω → ℝ := fun ω => (Fintype.card ι : ℝ) * ∑ i, X i ω ^ 2
  have hBI : Integrable B P :=
    (integrable_finsetSum Finset.univ (fun i _ => hXsq i)).const_mul (Fintype.card ι : ℝ)
  have hpoint : ∀ ω, (∑ i, X i ω) ^ 2 ≤ B ω := fun ω => by
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => X i ω))
  have hFI : Integrable (fun ω => (∑ i, X i ω) ^ 2) P := by
    refine hBI.mono' ((Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun i _ => hXm i)).pow 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∑ i, X i ω))]
    exact hpoint ω
  refine ⟨hFI, (integral_mono hFI hBI hpoint).trans_eq ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hXsq i)]

/-- A fixed walk has square moment at most its squared length times the square moment
of a weight, including walks with repeated edges. -/
theorem integral_walkCost_sq_le {m : ℕ} {F : Measure ℝ≥0} {P : Measure (Config m)}
    (hIID : IsIIDWeights P F) (hF2 : Integrable (fun x : ℝ≥0 => (x : ℝ) ^ 2) F)
    {u v : Vertex m} (γ : (latticeGraph m).Walk u v) :
    Integrable (fun ω => (walkCost ω γ : ℝ) ^ 2) P ∧
      (∫ ω, (walkCost ω γ : ℝ) ^ 2 ∂P) ≤
        (γ.length : ℝ) ^ 2 * ∫ x, (x : ℝ) ^ 2 ∂F := by
  let X : Fin γ.darts.length → Config m → ℝ := fun i ω => ω (Infra.FPP.dartEdge γ i)
  have hXs : ∀ i, Integrable (fun ω => X i ω ^ 2) P := fun i =>
    ((Infra.FPP.IsIIDWeights.identDistrib hIID (Infra.FPP.dartEdge γ i)).comp
      (measurable_id.pow_const 2)).integrable_iff.2 hF2
  have hsum := integral_sq_sum_le (X := X)
    (fun i => ((measurable_pi_apply (Infra.FPP.dartEdge γ i)).coe_nnreal_real).aestronglyMeasurable) hXs
  have heq : (fun ω => (walkCost ω γ : ℝ) ^ 2) = fun ω => (∑ i, X i ω) ^ 2 := by
    funext ω
    rw [Infra.FPP.coe_walkCost_eq_sum]
  rw [← heq] at hsum
  refine ⟨hsum.1, hsum.2.trans_eq ?_⟩
  have hident (i : Fin γ.darts.length) : (∫ ω, X i ω ^ 2 ∂P) = ∫ x, (x : ℝ) ^ 2 ∂F :=
    ((Infra.FPP.IsIIDWeights.identDistrib hIID (Infra.FPP.dartEdge γ i)).comp
      (measurable_id.pow_const 2)).integral_eq
  simp only [hident, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    SimpleGraph.Walk.length_darts]
  ring

/-- A coordinate walk between opposite slab faces uses owned edges and has the expected
Manhattan length. This strengthens the finiteness construction of the module
`CurvatureVariance.Paper.Proofs.Responses.Finiteness`. -/
theorem exists_coordinate_slab_walk {m : ℕ} {p q : ℤ} (hpq : p + 2 ≤ q)
    (y z : Fin m → ℤ) :
    ∃ γ : (latticeGraph m).Walk (p, y) (q, z),
      (∀ e ∈ γ.edges, e ∈ slabEdges p q) ∧
      (γ.length : ℤ) = q - p + ∑ j, |y j - z j| := by
  obtain ⟨a, hal, ha⟩ := exists_longitudinal_walk ((p, y) : Vertex m) (p + 1)
  obtain ⟨b, hbl, hb⟩ := CurvatureVariance.Infra.FPP.exists_longitudinal_walk
    ((q, z) : Vertex m) (p + 1)
  have hnn : 0 ≤ ∑ j, |y j - z j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c, hcl, hc⟩ := CurvatureVariance.Infra.FPP.exists_transverse_walk z
    (∑ j, |y j - z j|).toNat ((p + 1, y) : Vertex m)
    (by simpa using (Int.toNat_of_nonneg hnn).symm)
  refine ⟨a.append (c.append b.reverse), ?_, ?_⟩
  · intro e he
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_append, List.mem_reverse] at he
    rcases he with he | he | he
    · exact CurvatureVariance.Paper.Responses.walk_mem_slabEdges_of_snd_eq a
        (fun x hx => by have h := ha x hx; exact ⟨by constructor <;> omega, h.1⟩) e he
    · exact CurvatureVariance.Paper.Responses.walk_mem_slabEdges_of_fst_eq
        (by omega : p < p + 1) (by omega : p + 1 < q) c hc e he
    · exact CurvatureVariance.Paper.Responses.walk_mem_slabEdges_of_snd_eq b
        (fun x hx => by have h := hb x hx; exact ⟨by constructor <;> omega, h.1⟩) e he
  · simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, Nat.cast_add]
    rw [hal, hbl, hcl, Int.toNat_of_nonneg hnn]
    rw [abs_of_nonpos (by omega : p - (p + 1) ≤ 0), abs_of_nonneg (by omega : 0 ≤ q - (p + 1))]
    ring

/-- The straight tuple has exactly the desired displacement in every slab. -/
theorem straight_tuple_admissible {m : ℕ} (M : Model m) {s : ℕ} (hs : 0 < s)
    (y₀ : Fin m → ℤ) :
    IsAdmissibleTuple M s s ((s : ℝ)⁻¹ • transversePoint y₀) 0
      (s • ((s : ℤ), y₀)) (fun i : Fin (s + 1) => (i : ℕ) • y₀) := by
  refine ⟨by simp only [Fin.val_zero, zero_nsmul, Prod.snd_zero], ?_, ?_⟩
  · simp only [Fin.val_last, nsmul_eq_mul]
    rfl
  · intro i
    have hinc : (i.succ : ℕ) • y₀ - (i.castSucc : ℕ) • y₀ = y₀ := by
      simp only [Fin.val_succ, Fin.val_castSucc, succ_nsmul, add_sub_cancel_left]
    rw [hinc, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hs.ne' : (s : ℝ) ≠ 0),
      one_smul, sub_self, norm_zero]
    positivity

/-- The long slab minimum admits a fixed-path dominating variable with square moment
`O(s⁴)`. This estimate uses only the second moment of the weights. -/
theorem exists_long_slabMin_domination {m : ℕ} (bd : Bounds m) (hbd : bd.Valid) :
    ∃ B : ℝ, 0 < B ∧ ∀ M : Model m, M.Standing → M.Fits bd → ∀ s : ℕ, 2 ≤ s → ∀ y₀ : Fin m → ℤ,
      ‖transversePoint y₀‖ ≤ (bd.T + 1) * s → ∃ H : Config m → ℝ,
        Integrable H M.P ∧ Integrable (fun ω => H ω ^ 2) M.P ∧
        (∀ ω, (slabMin M ω s s ((s : ℝ)⁻¹ • transversePoint y₀) 0
          (s • ((s : ℤ), y₀))).toReal ≤ H ω) ∧
        (∫ ω, H ω ^ 2 ∂M.P) ≤ B * (s : ℝ) ^ 4 ∧
        Integrable (fun ω => (slabMin M ω s s ((s : ℝ)⁻¹ • transversePoint y₀) 0
          (s • ((s : ℤ), y₀))).toReal) M.P := by
  classical
  let d : ℝ := ((m : ℝ) + 1) * (bd.T + 1)
  let J : ℝ := ∫ x, (x : ℝ) ^ 2 ∂bd.law.F
  have hJ : 0 ≤ J := integral_nonneg fun _ => sq_nonneg _
  have hd : 0 ≤ d := by dsimp [d]; have := hbd.T_nonneg; positivity
  refine ⟨d ^ 2 * J + 1, by positivity, ?_⟩
  intro M hM hfit s hs y₀ hy₀
  have : IsProbabilityMeasure M.F := hM.probF
  have hF2 := integrable_weight_sq M hM
  obtain ⟨α, hα, hexp⟩ := hM.assumptionW.1
  have hF1 := integrable_coe_of_exp hα hexp
  let Y : Fin (s + 1) → Fin m → ℤ := fun i => (i : ℕ) • y₀
  have hY := straight_tuple_admissible M (by omega : 0 < s) y₀
  have hexists (i : Fin s) :
      ∃ γ : (latticeGraph m).Walk (tuplePoint 0 s Y i.castSucc) (tuplePoint 0 s Y i.succ),
        (∀ e ∈ γ.edges, e ∈ slabEdges ((i : ℤ) * s) (((i : ℤ) + 1) * s)) ∧
        (γ.length : ℝ) ≤ d * s := by
    have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
    obtain ⟨γ, hγ, hlen⟩ := exists_coordinate_slab_walk
      (p := (i : ℤ) * s) (q := ((i : ℤ) + 1) * s) (by nlinarith only [hsZ])
      (Y i.castSucc) (Y i.succ)
    have hu : (((i : ℤ) * s, Y i.castSucc) : Vertex m) = tuplePoint 0 s Y i.castSucc := by
      apply Prod.ext
      · simp only [tuplePoint, Prod.fst_zero, Fin.val_castSucc]
        omega
      · rfl
    have hv : (((((i : ℤ) + 1) * s), Y i.succ) : Vertex m) = tuplePoint 0 s Y i.succ := by
      apply Prod.ext
      · simp only [tuplePoint, Prod.fst_zero, Fin.val_succ]
        push_cast
        ring
      · rfl
    refine ⟨γ.copy hu hv, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.edges_copy] using hγ
    simp only [SimpleGraph.Walk.length_copy]
    have hinc (j : Fin m) : Y i.castSucc j - Y i.succ j = -y₀ j := by
      simp only [Y, Fin.val_castSucc, Fin.val_succ, succ_nsmul, Pi.add_apply]
      omega
    have hlen' : (γ.length : ℤ) = s + ∑ j, |y₀ j| := by
      simpa only [hinc, abs_neg, add_mul, one_mul, add_sub_cancel_left] using hlen
    have hlenR : (γ.length : ℝ) = oneNorm ((s : ℤ), y₀) := by
      have hh := congrArg ((↑) : ℤ → ℝ) hlen'
      push_cast at hh
      simpa only [oneNorm, Int.natAbs_natCast, Nat.cast_natAbs, Int.cast_abs,
        Nat.cast_add, Nat.cast_sum] using hh
    rw [hlenR]
    exact oneNorm_le_of_transverse_bound (by linarith only [hbd.T_nonneg]) hy₀
  choose γ hγ hlen using hexists
  let H : Config m → ℝ := fun ω => ∑ i : Fin s, (walkCost ω (γ i) : ℝ)
  have hHI : Integrable H M.P := integrable_finsetSum Finset.univ
    (fun i _ => Infra.FPP.IsIIDWeights.integrable_walkCost hM.iid (γ i) hF1)
  have hmoment (i : Fin s) := integral_walkCost_sq_le hM.iid hF2 (γ i)
  simp only [hfit.F_eq] at hmoment
  have hHsq := integral_sq_sum_le
    (fun i : Fin s => (Infra.FPP.measurable_walkCost_real (γ i)).aestronglyMeasurable)
    (fun i => (hmoment i).1)
  have hHbound : (∫ ω, H ω ^ 2 ∂M.P) ≤ (d ^ 2 * J + 1) * (s : ℝ) ^ 4 := by
    have heach (i : Fin s) : (∫ ω, (walkCost ω (γ i) : ℝ) ^ 2 ∂M.P) ≤
        (d * s) ^ 2 * J := by
      exact (hmoment i).2.trans (mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg hd (Nat.cast_nonneg s))).2 (hlen i)) hJ)
    calc (∫ ω, H ω ^ 2 ∂M.P) ≤ s * ∑ i : Fin s, ∫ ω, (walkCost ω (γ i) : ℝ) ^ 2 ∂M.P := by
          simpa only [Fintype.card_fin] using hHsq.2
      _ ≤ s * ∑ _i : Fin s, (d * s) ^ 2 * J :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => heach i) (Nat.cast_nonneg s)
      _ = (d ^ 2 * J) * (s : ℝ) ^ 4 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ (d ^ 2 * J + 1) * (s : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
  have hdom : ∀ ω, (slabMin M ω s s ((s : ℝ)⁻¹ • transversePoint y₀) 0
      (s • ((s : ℤ), y₀))).toReal ≤ H ω := by
    intro ω
    have hfinite (i : Fin s) := CurvatureVariance.Paper.Responses.tuple_slabTime_ne_top ω
      (0 : Vertex m) hs Y i
    have htuplefinite : tupleCost ω 0 s Y ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun i _ => hfinite i
    calc (slabMin M ω s s ((s : ℝ)⁻¹ • transversePoint y₀) 0
        (s • ((s : ℤ), y₀))).toReal ≤ (tupleCost ω 0 s Y).toReal :=
          ENNReal.toReal_mono htuplefinite
            (CurvatureVariance.Paper.Responses.slabMin_le_tupleCost hY ω)
      _ = ∑ i : Fin s, (slabTime ω ((i : ℤ) * s) (((i : ℤ) + 1) * s)
          (tuplePoint 0 s Y i.castSucc) (tuplePoint 0 s Y i.succ)).toReal := by
          rw [tupleCost, ENNReal.toReal_sum (fun i _ => hfinite i)]
          simp only [Prod.fst_zero, zero_add]
      _ ≤ ∑ i : Fin s, (walkCost ω (γ i) : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hh : slabTime ω ((i : ℤ) * s) (((i : ℤ) + 1) * s)
              (tuplePoint 0 s Y i.castSucc) (tuplePoint 0 s Y i.succ) ≤
              (walkCost ω (γ i) : ℝ≥0∞) := iInf₂_le (γ i) (hγ i)
          simpa only [ENNReal.coe_toReal] using ENNReal.toReal_mono ENNReal.coe_ne_top hh
  refine ⟨H, hHI, hHsq.1, hdom, hHbound, ?_⟩
  apply hHI.mono' ((CurvatureVariance.Paper.Responses.measurable_slabMin M s s
    ((s : ℝ)⁻¹ • transversePoint y₀) 0 (s • ((s : ℤ), y₀))).ennreal_toReal.aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hdom ω

/-- A Gaussian tail in the logarithm absorbs the polynomial moment bound used for
the exceptional event at the long target. -/
theorem tendsto_pow_six_mul_exp_neg_log_sq {C : ℝ} (hC : 0 < C) :
    Tendsto (fun s : ℝ => s ^ 6 * Real.exp (-((Real.log s / C) ^ 2)))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun s => by positivity)
    (g := fun s : ℝ => s⁻¹) ?_ tendsto_inv_atTop_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (7 * C ^ 2)] with s hs hlog
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hlog0 : 0 ≤ Real.log s := Real.log_nonneg hs
  have hquad : 7 * Real.log s ≤ (Real.log s / C) ^ 2 := by
    rw [div_pow, le_div_iff₀ (sq_pos_of_pos hC)]
    have hh := mul_le_mul_of_nonneg_right hlog hlog0
    nlinarith only [hh]
  have hpow : s ^ 6 = Real.exp (6 * Real.log s) := by
    rw [show (6 : ℝ) * Real.log s = Real.log (s ^ 6) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hspos 6)]
  rw [hpow, ← Real.exp_add]
  calc Real.exp (6 * Real.log s + -((Real.log s / C) ^ 2)) ≤ Real.exp (-Real.log s) :=
        Real.exp_le_exp.mpr (by linarith only [hquad])
    _ = s⁻¹ := by rw [Real.exp_neg, Real.exp_log hspos]

end CurvatureVariance.Paper.Mean
