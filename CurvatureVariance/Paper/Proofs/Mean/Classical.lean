/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Mean
public import CurvatureVariance.Paper.Contracts.Geometry
import CurvatureVariance.Paper.Proofs.OsSum
import CurvatureVariance.Infra.Os.Sum
import CurvatureVariance.Paper.Proofs.Mean.Domain
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The classical range in Section `sec:mean`

The classical estimates of Section `sec:prelim` imply the induction improvement when the
amplitude is above the classical scale. Constants depend only on the common law and
`Bounds` record, uniformly in fitting models, `K` and `A`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- Adding a deterministic positive upper bound to an exponential stochastic bound. -/
theorem isOs_add_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {θ b : ℝ}
    (hθ : 0 < θ) (hb : 0 < b) (hX : CurvatureVariance.IsOs P 1 θ X) :
    CurvatureVariance.IsOs P 1 (θ + b / Real.log 2) (fun ω => X ω + b) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hc : CurvatureVariance.IsOs P 1 (b / Real.log 2) (fun _ : Ω => b) := by
    refine ⟨aemeasurable_const, ?_⟩
    have heq : b / (b / Real.log 2) = Real.log 2 := by field_simp
    simp only [max_eq_left hb.le, heq, Real.rpow_one, Real.exp_log two_pos,
      ENNReal.ofReal_ofNat, lintegral_const, measure_univ, mul_one]
    exact le_rfl
  let scales : Fin 2 → ℝ := ![θ, b / Real.log 2]
  let vars : Fin 2 → Ω → ℝ := ![X, fun _ => b]
  have hh := CurvatureVariance.Paper.isOs_sum_of_one_le (P := P) (s := 1) le_rfl Finset.univ Finset.univ_nonempty
    scales (fun i _ => by fin_cases i <;> dsimp [scales] <;> positivity) vars
    (fun i _ => by fin_cases i; exact hX; exact hc)
  simpa only [Fin.sum_univ_two, scales, vars, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

/-- The induction domain has a linear physical size depending on the reference slope. -/
theorem oneNorm_target_le {m : ℕ} {M : Model m} (hM : M.Standing) {bd : Bounds m} (hfit : M.Fits bd)
    {N : ℕ} (hN : 1 ≤ N) {y : Fin m → ℤ} (hy : y ∈ premiseDomain M N) :
    oneNorm ((N : ℤ), y) ≤ (m + 1 : ℝ) * (bd.T + 1) * N :=
  oneNorm_le_of_transverse_bound (by linarith only [norm_nonneg M.t₀, hfit.t₀_le])
    (norm_transverse_le_of_mem_fit hM hfit (by exact_mod_cast hN) hy)

/-- The classical estimates cover amplitudes above the range used in the induction. -/
theorem ClassicalRangeStatement_of {m : ℕ} (hclassical : ClassicalStatement m) :
    ClassicalRangeStatement m := by
  intro bd hbd
  obtain ⟨C, hC, hc⟩ := hclassical bd hbd
  let d : ℝ := (m + 1) * (bd.T + 1)
  let D₁ : ℝ := Real.sqrt (d / Real.log 2)
  let D₂ : ℝ := Real.sqrt (2 * d)
  have hd : 0 < d := by dsimp [d]; have := hbd.T_nonneg; positivity
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hD₁ : 0 < D₁ := Real.sqrt_pos.2 (div_pos hd hlog)
  have hD₂ : 0 < D₂ := Real.sqrt_pos.2 (mul_pos two_pos hd)
  refine ⟨2 * C * (D₁ + D₂ / Real.log 2), by positivity, ?_⟩
  intro K _hK
  refine ⟨max (m + 1) ⌈d⌉₊, ?_⟩
  intro M hM hfit N hN A _hA hrange y hy
  let : IsProbabilityMeasure M.P := hM.probP
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans_le hN1)
  have hNd : d ≤ N := (Nat.le_ceil d).trans (by
    exact_mod_cast ((le_max_right _ _).trans hN))
  have hx : ((N : ℤ), y) ≠ (0 : Vertex m) := by
    intro hh
    have hh₁ := congrArg Prod.fst hh
    simp only [Prod.fst_zero] at hh₁
    omega
  obtain ⟨_hI, hconc, hmean0, hmean⟩ := hc M hM hfit ((N : ℤ), y) hx
  let r : ℝ := oneNorm ((N : ℤ), y)
  let R : ℝ := Real.sqrt ((N : ℝ) * Real.log (2 + N))
  have hrN : (N : ℝ) ≤ r := by
    dsimp only [r, oneNorm]
    push_cast
    simp only [Int.natAbs_natCast]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hrpos : 0 < r := hNpos.trans_le hrN
  have hrbound : r ≤ d * N := oneNorm_target_le hM hfit hN1 hy
  have hlogN : Real.log 2 ≤ Real.log (2 + (N : ℝ)) :=
    Real.log_le_log two_pos (by linarith)
  have hlogr : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
  have hlogNpos : 0 < Real.log (2 + (N : ℝ)) := hlog.trans_le hlogN
  have hR : 0 < R := Real.sqrt_pos.2 (mul_pos hNpos hlogNpos)
  have hlogbound : Real.log (2 + r) ≤ 2 * Real.log (2 + (N : ℝ)) := by
    calc
      Real.log (2 + r) ≤ Real.log ((2 + (N : ℝ)) ^ 2) := by
        apply Real.log_le_log (by linarith)
        have hh := mul_le_mul_of_nonneg_right hNd hNpos.le
        nlinarith only [hrbound, hh, sq_nonneg (N : ℝ), hNpos]
      _ = _ := by rw [Real.log_pow]; norm_num
  have hθbound : Real.sqrt r ≤ D₁ * R := by
    calc
      Real.sqrt r ≤ Real.sqrt ((d / Real.log 2) * ((N : ℝ) * Real.log (2 + N))) := by
        apply Real.sqrt_le_sqrt
        apply hrbound.trans
        have hh := mul_le_mul_of_nonneg_left hlogN (mul_nonneg hd.le hNpos.le)
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hlog).2
        convert hh using 1
        ring
      _ = D₁ * R := by rw [Real.sqrt_mul (div_nonneg hd.le hlog.le)]
  have hbnd : Real.sqrt (r * Real.log (2 + r)) ≤ D₂ * R := by
    calc
      Real.sqrt (r * Real.log (2 + r)) ≤
          Real.sqrt ((2 * d) * ((N : ℝ) * Real.log (2 + N))) := by
        apply Real.sqrt_le_sqrt
        calc
          r * Real.log (2 + r) ≤ (d * N) * (2 * Real.log (2 + (N : ℝ))) :=
            mul_le_mul hrbound hlogbound hlogr.le (mul_nonneg hd.le hNpos.le)
          _ = _ := by ring
      _ = D₂ * R := by rw [Real.sqrt_mul (mul_nonneg (by norm_num) hd.le)]
  let θ : ℝ := C * Real.sqrt r
  let b : ℝ := C * Real.sqrt (r * Real.log (2 + r))
  have hθ : 0 < θ := mul_pos hC (Real.sqrt_pos.2 hrpos)
  have hb : 0 < b := mul_pos hC (Real.sqrt_pos.2 (mul_pos hrpos hlogr))
  have hscale : θ + b / Real.log 2 ≤ Q M K A N / 2 := by
    have hlarge : 2 * C * (D₁ + D₂ / Real.log 2) * R < Q M K A N :=
      lt_of_not_ge hrange
    have hθ' := mul_le_mul_of_nonneg_left hθbound hC.le
    have hb' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbnd hC.le) hlog.le
    calc
      θ + b / Real.log 2 ≤ C * (D₁ * R) + C * (D₂ * R) / Real.log 2 :=
        add_le_add hθ' hb'
      _ = C * (D₁ + D₂ / Real.log 2) * R := by ring
      _ ≤ Q M K A N / 2 := by linarith only [hlarge]
  have hmeas : AEMeasurable
      (fun ω => passageTimeReal ω 0 ((N : ℤ), y) - M.μ.1 (point ((N : ℤ), y))) M.P := by
    have heq : (fun ω => passageTimeReal ω 0 ((N : ℤ), y) - M.μ.1 (point ((N : ℤ), y))) =
        fun ω => (passageTimeReal ω 0 ((N : ℤ), y) -
          ∫ ω', passageTimeReal ω' 0 ((N : ℤ), y) ∂M.P) +
          ((∫ ω', passageTimeReal ω' 0 ((N : ℤ), y) ∂M.P) - M.μ.1 (point ((N : ℤ), y))) := by
      funext ω
      ring
    rw [heq]
    exact hconc.1.add_const _
  refine ⟨hmeas, ?_⟩
  have hh := isOs_add_const hθ hb hconc.2
  refine (hh.mono zero_le_one (by positivity)
    (by simpa only [Real.norm_eq_abs] using hmeas.norm)
    (Filter.Eventually.of_forall fun ω => ?_)).mono_scale
    zero_le_one (by positivity) hscale
  have htriangle := abs_sub_le (passageTimeReal ω 0 ((N : ℤ), y))
    (∫ ω', passageTimeReal ω' 0 ((N : ℤ), y) ∂M.P)
    (M.μ.1 (point ((N : ℤ), y)))
  rw [abs_of_nonneg hmean0] at htriangle
  exact htriangle.trans (add_le_add le_rfl hmean)

end CurvatureVariance.Paper.Mean
