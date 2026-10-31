/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Arrays
public import CurvatureVariance.Paper.Proofs.Mean.MeanRows
public import CurvatureVariance.Paper.Proofs.Mean.MeanSup
import CurvatureVariance.Infra.FPP.Lattice
import CurvatureVariance.Infra.FPP.Model
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.FieldSimp

/-!
# The arrays in the proof of Lemma `lem:smallmean`

The paper (the proof of Lemma `lem:smallmean`): with
`Z_i(j,k) = sup_{u,v} |T^{(i)}(u,v) − E[T(u,v)]|/(θQ_s)` for `8w|k − j| ≤ s^{3/4+δ/100}` and
`Z_i(j,k) = 0` for the others, `E[Z_i(j,k)^{4d}] ≤ 1`, `c₁(x − d^{1/2})₊² ≥ θ(x² − 2d)` for `x ≥ 0`
if `θ ≤ c₁/2`, and summing along the minimizing chain gives
`F − sμ(s,y₀) ≥ (c₁ − 2dθ)sQ_s − θQ_s sup_{k₁,…,k_s} {∑ᵢ Z_i(k_{i−1},k_i) − ∑ᵢ |k_i − k_{i−1}|²}`,
and [AB26, Lemma 2.4] gives `E[F] − sμ(s,y₀) ≥ (c₁ − Cθ)sQ_s`.

* `meanSlabArray_arrays`: the arrays `Paper.Mean.meanSlabArray` satisfy the hypotheses of
  `ArraysStatement`.
* `meanpenalty_le`: the inequality `c₁(x − d^{1/2})₊² ≥ θ(x² − 2d)`.
* `mean_row_lower`: the bound on `E[T(u,v)] − ζ_t·(v − u)` after equation `eq:meanbelow`.
* `smallMean_row_entry_lower`: the bound on a slab time, in terms of the entry of the array.
* `integral_slabMin_ge_of_arraysStatement`, `exists_smallMean_lower`: the summation and
  `ArraysStatement`.

The sum holds for every admissible tuple, so for the infimum `F`, with no choice of a minimizing
chain. The supremum in `ArraysStatement` is over all sequences with `k₀ = 0`, and the sequence of
cube indices of a tuple is one of them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Paper.Responses
  CurvatureVariance.Infra.FPP

/-- The arrays `Z_i` of the proof of Lemma `lem:smallmean`, with `B = θ Q_s`, satisfy the hypotheses
of `ArraysStatement`: they are measurable, nonnegative, independent over `i`, as they are read off
disjoint slabs, and `E[Z_i(j,k)^{4d}] ≤ 1`. -/
theorem meanSlabArray_arrays {m K : ℕ} {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} (hIID : IsIIDWeights P F) (s w : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) {B : ℝ} (hB : 0 < B)
    (adm : (Fin m → ℤ) → (Fin m → ℤ) → Prop)
    (hprofiles : ∀ (i : Fin K) (j k : Fin m → ℤ), adm j k →
      ∃ X : Config m → ℝ, eLpNorm X (4 * (m + 1) : ℕ) P ≤ ENNReal.ofReal B ∧
        ∀ᵐ ω ∂P, ∀ u ∈ rowCube s w t i j, ∀ v ∈ rowCube s w t ((i : ℤ) + 1) k,
          |slabTimeReal ω ((i : ℤ) * s) (((i : ℤ) + 1) * s) u v -
            ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂P| ≤ X ω) :
    (∀ i j k, Measurable fun ω => meanSlabArray (K := K) P s w t B adm i j k ω) ∧
      (∀ i ω j k, 0 ≤ meanSlabArray (K := K) P s w t B adm i j k ω) ∧
      iIndepFun (fun (i : Fin K) (ω : Config m) (j k : Fin m → ℤ) =>
        meanSlabArray P s w t B adm i j k ω) P ∧
      ∀ i j k, ∫⁻ ω, ENNReal.ofReal
        (meanSlabArray (K := K) P s w t B adm i j k ω ^ (4 * (m + 1))) ∂P ≤ 1 := by
  classical
  let : IsProbabilityMeasure P := Infra.FPP.IsIIDWeights.isProbabilityMeasure hIID
  have hmeas : ∀ (i : Fin K) (j k : Fin m → ℤ),
      Measurable (meanSlabArray P s w t B adm i j k) := by
    intro i j k
    by_cases hjk : adm j k
    · simpa only [meanSlabArray, hjk, ite_true] using
        (measurable_meanSlabSup P s w t i j k).ennreal_toReal.div_const B
    · simpa only [meanSlabArray, hjk, ite_false] using
        (measurable_const : Measurable fun _ : Config m => (0 : ℝ))
  have hpos : ∀ (i : Fin K) (j k : Fin m → ℤ) ω, 0 ≤ meanSlabArray P s w t B adm i j k ω := by
    intro i j k ω
    unfold meanSlabArray
    split_ifs
    · exact div_nonneg ENNReal.toReal_nonneg hB.le
    · exact le_rfl
  have hLp : ∀ (i : Fin K) (j k : Fin m → ℤ),
      eLpNorm (meanSlabArray P s w t B adm i j k) (4 * (m + 1) : ℕ) P ≤ 1 := by
    intro i j k
    by_cases hjk : adm j k
    · obtain ⟨X, hXp, hX⟩ := hprofiles i j k hjk
      have hbound := (eLpNorm_meanSlabSup_le_of_majorant P s w t i j k hX _).trans hXp
      simpa only [meanSlabArray, hjk, ite_true] using eLpNorm_div_le_one _ _ hB hbound
    · simp only [meanSlabArray, hjk, ite_false]
      change eLpNorm (0 : Config m → ℝ) (4 * (m + 1) : ℕ) P ≤ 1
      rw [eLpNorm_zero]
      exact zero_le
  have hind : iIndepFun (fun (i : Fin K) (ω : Config m) (j k : Fin m → ℤ) =>
      meanSlabArray P s w t B adm i j k ω) P := by
    apply iIndepFun_of_slab_local hIID 0 s
    · intro i
      apply Measurable.of_eval
      intro j
      apply Measurable.of_eval
      intro k
      exact hmeas i j k
    · intro i ω ω' hω
      funext j k
      unfold meanSlabArray
      split_ifs with hjk
      · dsimp only
        rw [meanSlabSup_congr P s w t i j k (by simpa only [zero_add] using hω)]
      · rfl
  refine ⟨hmeas, fun i ω j k => hpos i j k ω, hind, ?_⟩
  intro i j k
  obtain ⟨hint, hmom⟩ := integral_pow_le_one_of_eLpNorm_le_one
    (by omega : 0 < 4 * (m + 1)) (hpos i j k) (hLp i j k)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun ω => pow_nonneg (hpos i j k ω) _)]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hmom

/-- **The penalty** (the proof of Lemma `lem:smallmean`):
`c₁(x − d^{1/2})₊² ≥ θ(x² − 2d)` for `x ≥ 0`, if `θ ≤ c₁/2`. -/
theorem meanpenalty_le {x d c₁ θ : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) (hθ : 0 ≤ θ)
    (hθc : θ ≤ c₁ / 2) :
    θ * (x ^ 2 - 2 * d) ≤ c₁ * (max (x - Real.sqrt d) 0) ^ 2 := by
  set r := max (x - Real.sqrt d) 0 with hr
  have hsq := sq_ge_half_sq_sub hx (le_max_left (x - Real.sqrt d) 0)
  rw [← hr, Real.sq_sqrt hd] at hsq
  have h1 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * θ)
  have h2 := mul_le_mul_of_nonneg_right hθc (sq_nonneg r)
  nlinarith only [h1, h2]

/-- **The bound on the mean at an entry** (the display after equation `eq:meanbelow`): for
`u ∈ I_i(j)`, `v ∈ I_{i+1}(k)`, equation `eq:meanbelow` at `z = v − u − (s, y₀)`, with
`|z − w(k − j)| ≤ wd^{1/2}` and `w² ≥ sQ_s`, gives
`E[T(u,v)] − ζ_t·(v − u) ≥ c₁Q_s + c₁Q_s(|k − j| − d^{1/2})₊²`. The transverse dimension is
`d − 1 = m`, so `row_jump_norm_bounds` has `|z − w(k − j)| ≤ w(d−1)^{1/2}`, which is stronger. -/
theorem mean_row_lower {m n w : ℕ} (hw : 0 < w) (hn : 0 < n)
    {y₀ : Fin m → ℤ} {t : EuclideanSpace ℝ (Fin m)}
    (hnt : (n : ℝ) • t = transversePoint y₀) {i : ℤ} {j k : Fin m → ℤ}
    {u v : Vertex m} (hu : u ∈ rowCube n w t i j) (hv : v ∈ rowCube n w t (i + 1) k)
    (p : Pt m) (g : (Fin m → ℤ) → ℝ) {Q c₁ R : ℝ}
    (hc₁ : 0 < c₁) (hwQ : (n : ℝ) * Q ≤ (w : ℝ) ^ 2)
    (hprofile : ∀ z : Fin m → ℤ, ‖transversePoint z‖ ≤ R →
      c₁ * Q + c₁ * ‖transversePoint z‖ ^ 2 / n ≤
        g (y₀ + z) - inner ℝ p (point ((n : ℤ), y₀ + z)))
    (hR : (w : ℝ) * ‖transversePoint (k - j)‖ + Real.sqrt m * w ≤ R) :
    c₁ * Q + c₁ * Q *
        (max (‖transversePoint (k - j)‖ - Real.sqrt ((m : ℝ) + 1)) 0) ^ 2 ≤
      g (v.2 - u.2) - inner ℝ p (point v - point u) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hwpos : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  let z := v.2 - u.2 - y₀
  let x := ‖transversePoint (k - j)‖
  let r := max (x - Real.sqrt ((m : ℝ) + 1)) 0
  have hb := row_jump_norm_bounds hw hnt hu hv
  have hzR : ‖transversePoint z‖ ≤ R := hb.2.trans hR
  have hsqrt : Real.sqrt m ≤ Real.sqrt ((m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith only [])
  have hnorm : (w : ℝ) * r ≤ ‖transversePoint z‖ := by
    rw [mul_max_of_nonneg _ _ hwpos, mul_zero]
    refine max_le ?_ (norm_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hsqrt hwpos
    have h2 := hb.1
    dsimp only [x]
    nlinarith only [h1, h2]
  have hnormsq := pow_le_pow_left₀ (mul_nonneg hwpos (le_max_right _ _)) hnorm 2
  rw [mul_pow] at hnormsq
  have hwQr := mul_le_mul_of_nonneg_right hwQ (sq_nonneg r)
  have hquadratic : c₁ * Q * r ^ 2 ≤ c₁ * ‖transversePoint z‖ ^ 2 / n := by
    rw [le_div_iff₀ hnpos]
    have hh := mul_le_mul_of_nonneg_left (hwQr.trans hnormsq) hc₁.le
    nlinarith only [hh]
  have hprof := hprofile z hzR
  have hyz : y₀ + z = v.2 - u.2 := by dsimp only [z]; abel
  rw [hyz] at hprof
  have hpt : point v - point u = point ((n : ℤ), v.2 - u.2) := by
    rw [← point_sub]
    congr 1
    apply Prod.ext
    · simp only [Prod.fst_sub, hu.1, hv.1]
      ring
    · rfl
  rw [hpt]
  change c₁ * Q + c₁ * Q * r ^ 2 ≤ _
  linarith only [hquadratic, hprof]

/-- **The bound on an entry** (the display after equation `eq:meanbelow`, and the proof of Lemma
`lem:smallmean`): `mean_row_lower` and `meanpenalty_le` give
`E[T(u,v)] − ζ_t·(v − u) ≥ (c₁ − 2dθ)Q_s + θQ_s|k − j|²`, and a slab time within `Y` of `E[T(u,v)]`
is then bounded below. -/
theorem smallMean_row_entry_lower {m n w : ℕ} (hw : 0 < w) (hn : 0 < n)
    {y₀ : Fin m → ℤ} {t : EuclideanSpace ℝ (Fin m)}
    (hnt : (n : ℝ) • t = transversePoint y₀) {i : ℤ} {j k : Fin m → ℤ}
    {u v : Vertex m} (hu : u ∈ rowCube n w t i j) (hv : v ∈ rowCube n w t (i + 1) k)
    (p : Pt m) (g : (Fin m → ℤ) → ℝ) {Q c₁ θ R : ℝ}
    (hQ : 0 < Q) (hc₁ : 0 < c₁) (hθ : 0 ≤ θ) (hθc : θ ≤ c₁ / 2)
    (hwQ : (n : ℝ) * Q ≤ (w : ℝ) ^ 2)
    (hprofile : ∀ z : Fin m → ℤ, ‖transversePoint z‖ ≤ R →
      c₁ * Q + c₁ * ‖transversePoint z‖ ^ 2 / n ≤
        g (y₀ + z) - inner ℝ p (point ((n : ℤ), y₀ + z)))
    (hR : (w : ℝ) * ‖transversePoint (k - j)‖ + Real.sqrt m * w ≤ R)
    {dVal Y : ℝ} (hcenter : |dVal - g (v.2 - u.2)| ≤ Y) :
    (c₁ - 2 * ((m : ℝ) + 1) * θ) * Q + θ * Q * ‖transversePoint (k - j)‖ ^ 2 - Y ≤
      dVal - inner ℝ p (point v - point u) := by
  have hrow := mean_row_lower hw hn hnt hu hv p g hc₁ hwQ hprofile hR
  have hpen := meanpenalty_le (x := ‖transversePoint (k - j)‖) (d := (m : ℝ) + 1)
    (norm_nonneg _) (by positivity) hθ hθc
  have hpenQ := mul_le_mul_of_nonneg_right hpen hQ.le
  have hcent := (abs_le.mp hcenter).1
  nlinarith only [hrow, hpenQ, hcent]

/-- **The sum along the chains and `ArraysStatement`** (the proof of Lemma `lem:smallmean`): if
every slab of every admissible tuple is bounded below by
`b + ζ·(increment) + a|ΔJ|² − a Z_i(J_{i−1}, J_i)`, for indices `J` of a tuple that start at `0`,
then `E[F] ≥ ζ·(v − u) + Kb − a C K`, where `C K` bounds the mean of the penalized supremum. Every
premise concerns the slab costs or the arrays: no estimate for the expected minimum is assumed. -/
theorem integral_slabMin_ge_of_arraysStatement {m n K : ℕ} {M : Model m}
    {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m} (hlong : v.1 = u.1 + (K : ℤ) * n)
    {P : Measure (Config m)} [IsProbabilityMeasure P] {Carr b a : ℝ} (ha : 0 ≤ a)
    (hCarr : 0 ≤ Carr)
    (Z : Fin K → Config m → (Fin m → ℤ) → (Fin m → ℤ) → ℝ)
    (hZm : ∀ i j k, Measurable fun ω => Z i ω j k)
    (hsum : ∫⁻ ω, ⨆ (k : Fin (K + 1) → Fin m → ℤ) (_ : k 0 = 0),
        ENNReal.ofReal ((∑ i : Fin K, Z i ω (k i.castSucc) (k i.succ)) -
          ∑ i : Fin K, ‖transversePoint (k i.succ - k i.castSucc)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (Carr * K))
    (J : (Fin (K + 1) → Fin m → ℤ) → Fin (K + 1) → Fin m → ℤ)
    (hJ₀ : ∀ Y, IsAdmissibleTuple M n K t u v Y → J Y 0 = 0)
    (hnonempty : ∃ Y, IsAdmissibleTuple M n K t u v Y)
    (hfinite : ∀ ω Y, IsAdmissibleTuple M n K t u v Y → ∀ i : Fin K,
      slabTime ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
        (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ) ≠ ⊤)
    (hF : Integrable (fun ω => (slabMin M ω n K t u v).toReal) P)
    (p : Pt m)
    (hlower : ∀ᵐ ω ∂P, ∀ Y, IsAdmissibleTuple M n K t u v Y → ∀ i : Fin K,
      b + inner ℝ p (point (tuplePoint u n Y i.succ) - point (tuplePoint u n Y i.castSucc)) +
          a * ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ ^ 2 -
          a * Z i ω (J Y i.castSucc) (J Y i.succ) ≤
        slabTimeReal ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
          (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ)) :
    inner ℝ p (point v - point u) + K * b - a * (Carr * K) ≤
      ∫ ω, (slabMin M ω n K t u v).toReal ∂P := by
  set S : Config m → ℝ≥0∞ := fun ω => ⨆ (k : Fin (K + 1) → Fin m → ℤ) (_ : k 0 = 0),
    ENNReal.ofReal ((∑ i : Fin K, Z i ω (k i.castSucc) (k i.succ)) -
      ∑ i : Fin K, ‖transversePoint (k i.succ - k i.castSucc)‖ ^ 2) with hS
  have hSm : Measurable S := Measurable.iSup fun k => Measurable.iSup fun _ =>
    ((Finset.measurable_sum _ fun i _ => hZm i _ _).sub_const _).ennreal_ofReal
  have hSfin : ∫⁻ ω, S ω ∂P ≠ ⊤ := (hsum.trans_lt ENNReal.ofReal_lt_top).ne
  have hSae : ∀ᵐ ω ∂P, S ω < ⊤ := ae_lt_top hSm hSfin
  have hSint : Integrable (fun ω => (S ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hSfin
  have hSmean : ∫ ω, (S ω).toReal ∂P ≤ Carr * K := by
    rw [integral_toReal hSm.aemeasurable hSae]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCarr (Nat.cast_nonneg K)) hsum
  have hFfinite : ∀ ω, slabMin M ω n K t u v ≠ ⊤ := by
    intro ω
    obtain ⟨Y, hY⟩ := hnonempty
    apply ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ => hfinite ω Y hY i)
    exact iInf₂_le Y hY
  have hpoint : ∀ᵐ ω ∂P, inner ℝ p (point v - point u) + K * b - a * (S ω).toReal ≤
      (slabMin M ω n K t u v).toReal := by
    filter_upwards [hlower, hSae] with ω hω hSfinite
    apply (ENNReal.ofReal_le_iff_le_toReal (hFfinite ω)).mp
    apply le_iInf₂
    intro Y hY
    have hscore : (∑ i : Fin K, Z i ω (J Y i.castSucc) (J Y i.succ)) -
        ∑ i : Fin K, ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ ^ 2 ≤ (S ω).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hSfinite.ne).mp
        (le_iSup₂_of_le (J Y) (hJ₀ Y hY) le_rfl)
    have hsum' := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin K))) => hω Y hY i
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      sum_inner_tuplePoint_sub hY hlong] at hsum'
    have hcostfinite : tupleCost ω u n Y ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun i _ => hfinite ω Y hY i
    rw [← ENNReal.ofReal_toReal hcostfinite]
    apply ENNReal.ofReal_le_ofReal
    rw [tupleCost, ENNReal.toReal_sum fun i _ => hfinite ω Y hY i]
    have hmul := mul_le_mul_of_nonneg_left hscore ha
    change _ ≤ ∑ i : Fin K, slabTimeReal ω (u.1 + (i : ℤ) * n)
      (u.1 + ((i : ℤ) + 1) * n) (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ)
    linarith only [hsum', hmul]
  have hbound := integral_mono_ae
    ((integrable_const (inner ℝ p (point v - point u) + K * b)).sub (hSint.const_mul a))
    hF hpoint
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub (integrable_const _) (hSint.const_mul a), integral_const,
    probReal_univ, one_smul, integral_const_mul] at hbound
  have hmul := mul_le_mul_of_nonneg_left hSmean ha
  linarith only [hbound, hmul]

/-- **The lower bound on `E[F]`** (the proof of Lemma `lem:smallmean`): from
equation `eq:meanbelow`, the bound `E[Z_i(j,k)^{4d}] ≤ 1` and [AB26, Lemma 2.4] (`ArraysStatement`),
`E[F] ≥ s μ(s,y₀) + s(c₁ − 2dθ)Q_s − θQ_s C s`. The constant `C` comes before the model, and `μ` is
written through the subgradient `p`. -/
theorem exists_smallMean_lower {m : ℕ} (harrays : ArraysStatement.{0} m) :
    ∃ Carr : ℝ, 0 < Carr ∧ ∀ (M : Model m), M.Standing → ∀ {s w : ℕ}, 2 ≤ s → 0 < w →
      ∀ (y₀ : Fin m → ℤ) (t : EuclideanSpace ℝ (Fin m)), (s : ℝ) • t = transversePoint y₀ →
      ∀ (p : Pt m) {Q c₁ θ : ℝ}, 0 < Q → 0 < c₁ → 0 < θ → θ ≤ c₁ / 2 →
      (s : ℝ) * Q ≤ (w : ℝ) ^ 2 →
      Real.sqrt m * w ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 →
      (∀ z : Fin m → ℤ, ‖transversePoint z‖ ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 4 →
        c₁ * Q + c₁ * ‖transversePoint z‖ ^ 2 / s ≤
          (∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀ + z) ∂M.P) -
            inner ℝ p (point ((s : ℤ), y₀ + z))) →
      (∃ Y, IsAdmissibleTuple M s s t 0 (s • ((s : ℤ), y₀)) Y) →
      Integrable (fun ω => (slabMin M ω s s t 0 (s • ((s : ℤ), y₀))).toReal) M.P →
      (∀ (i : Fin s) (j k : Fin m → ℤ),
        (w : ℝ) * ‖transversePoint (k - j)‖ ≤
          (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 8 →
        ∃ X : Config m → ℝ, eLpNorm X (4 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal (θ * Q) ∧
          ∀ᵐ ω ∂M.P, ∀ u ∈ rowCube s w t i j, ∀ v ∈ rowCube s w t ((i : ℤ) + 1) k,
            |slabTimeReal ω ((i : ℤ) * s) (((i : ℤ) + 1) * s) u v -
              ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂M.P| ≤ X ω) →
      inner ℝ p (point (s • ((s : ℤ), y₀))) + (s : ℝ) * ((c₁ - 2 * ((m : ℝ) + 1) * θ) * Q) -
          (θ * Q) * (Carr * s) ≤
        ∫ ω, (slabMin M ω s s t 0 (s • ((s : ℤ), y₀))).toReal ∂M.P := by
  obtain ⟨Carr, hCarr, harr⟩ := harrays
  refine ⟨Carr, hCarr, ?_⟩
  intro M hM s w hs hw y₀ t hst p Q c₁ θ hQ hc₁ hθ hθc hwQ hwidth hmean hnonempty hF hprofiles
  classical
  let : IsProbabilityMeasure M.P := hM.probP
  let : IsProbabilityMeasure M.F := hM.probF
  let adm : (Fin m → ℤ) → (Fin m → ℤ) → Prop := fun j k =>
    (w : ℝ) * ‖transversePoint (k - j)‖ ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 8
  have hB : 0 < θ * Q := mul_pos hθ hQ
  obtain ⟨hZm, hZ0, hZind, hZmom⟩ := meanSlabArray_arrays (K := s) hM.iid s w t hB adm hprofiles
  let Z : Fin s → Config m → (Fin m → ℤ) → (Fin m → ℤ) → ℝ := fun i ω j k =>
    meanSlabArray M.P s w t (θ * Q) adm i j k ω
  have hsum := harr s (by omega) (Config m) M.P Z hZm hZ0 hZind hZmom
  let J : (Fin (s + 1) → Fin m → ℤ) → Fin (s + 1) → Fin m → ℤ :=
    fun Y i => rowIndex s w t i (Y i)
  have hcenter : ∀ᵐ ω ∂M.P, ∀ (i : Fin s) (j k : Fin m → ℤ), adm j k →
      ∀ u ∈ rowCube s w t i j, ∀ v ∈ rowCube s w t ((i : ℤ) + 1) k,
      |slabTimeReal ω ((i : ℤ) * s) (((i : ℤ) + 1) * s) u v -
        ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂M.P| ≤
        (θ * Q) * Z i ω j k := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    by_cases hjk : adm j k
    · obtain ⟨X, _hXp, hX⟩ := hprofiles i j k hjk
      filter_upwards [ae_le_meanSlabSup_of_majorant M.P s w t i j k hX] with ω hω
      intro _hadm u hu v hv
      have heq : (θ * Q) * Z i ω j k = (meanSlabSup M.P s w t i j k ω).toReal := by
        dsimp only [Z, meanSlabArray]
        rw [ite_eq_left hjk]
        field_simp
      rw [heq]
      exact hω u hu v hv
    · exact Filter.Eventually.of_forall fun _ h => False.elim (hjk h)
  have hJ₀ : ∀ Y, IsAdmissibleTuple M s s t 0 (s • ((s : ℤ), y₀)) Y → J Y 0 = 0 := by
    intro Y hY
    ext j
    simp only [J, rowIndex, hY.1, Fin.val_zero, Nat.cast_zero, Int.cast_zero,
      zero_mul, Int.floor_zero, Prod.snd_zero, Pi.zero_apply, sub_zero, zero_div]
  have hlong : (s • ((s : ℤ), y₀) : Vertex m).1 = (0 : Vertex m).1 + (s : ℤ) * s := by
    change s • (s : ℤ) = 0 + (s : ℤ) * s
    simp only [nsmul_eq_mul, zero_add]
  have hlower : ∀ᵐ ω ∂M.P, ∀ Y, IsAdmissibleTuple M s s t 0 (s • ((s : ℤ), y₀)) Y →
      ∀ i : Fin s,
        (c₁ - 2 * ((m : ℝ) + 1) * θ) * Q +
            inner ℝ p (point (tuplePoint 0 s Y i.succ) - point (tuplePoint 0 s Y i.castSucc)) +
            (θ * Q) * ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ ^ 2 -
            (θ * Q) * Z i ω (J Y i.castSucc) (J Y i.succ) ≤
          slabTimeReal ω ((i : ℤ) * s) (((i : ℤ) + 1) * s)
            (tuplePoint 0 s Y i.castSucc) (tuplePoint 0 s Y i.succ) := by
    filter_upwards [hcenter] with ω hω
    intro Y hY i
    have hu : tuplePoint 0 s Y i.castSucc ∈ rowCube s w t i (J Y i.castSucc) := by
      refine ⟨?_, rfl⟩
      simp only [tuplePoint, Prod.fst_zero, zero_add, Fin.val_castSucc]
    have hv : tuplePoint 0 s Y i.succ ∈ rowCube s w t ((i : ℤ) + 1) (J Y i.succ) := by
      refine ⟨?_, rfl⟩
      simp only [tuplePoint, Prod.fst_zero, zero_add, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have hb := row_jump_norm_bounds hw hst hu hv
    have hdis : ‖transversePoint ((Y i.succ) - Y i.castSucc - y₀)‖ ≤
        (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 := by
      rw [transversePoint_sub, ← hst]
      exact hY.2.2 i
    have hadm : adm (J Y i.castSucc) (J Y i.succ) := by
      dsimp only [adm]
      have hb1 := hb.1
      change (w : ℝ) * ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ - Real.sqrt m * w ≤
        ‖transversePoint (Y i.succ - Y i.castSucc - y₀)‖ at hb1
      linarith only [hb1, hdis, hwidth]
    have hR : (w : ℝ) * ‖transversePoint (J Y i.succ - J Y i.castSucc)‖ + Real.sqrt m * w ≤
        (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 4 := by
      dsimp only [adm] at hadm
      have hp := Real.rpow_nonneg (Nat.cast_nonneg s) ((3 : ℝ) / 4 + M.δ / 100)
      linarith only [hadm, hwidth, hp]
    have he := smallMean_row_entry_lower hw (by omega : 0 < s) hst hu hv p
      (fun y => ∫ η, passageTimeReal η 0 ((s : ℤ), y) ∂M.P) hQ hc₁ hθ.le hθc hwQ hmean hR
      (hω i _ _ hadm _ hu _ hv)
    linarith only [he]
  have hh := integral_slabMin_ge_of_arraysStatement hlong hB.le hCarr.le Z hZm hsum J hJ₀
    hnonempty (fun ω Y _hY i => tuple_slabTime_ne_top ω 0 hs Y i) hF p
    (by simpa only [Prod.fst_zero, zero_add] using hlower)
  simpa only [Infra.FPP.point_zero, sub_zero] using hh

end CurvatureVariance.Paper.Mean
