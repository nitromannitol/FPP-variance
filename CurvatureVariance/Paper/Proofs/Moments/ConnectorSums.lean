/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ConnectorLinks
public import CurvatureVariance.Paper.Proofs.Moments.Weights
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry

/-!
# Sums and small estimates for the chaining of equation `eq:tree`

* `sum_range_two_pow_le`, `sum_range_succ_mul_pow_le`: `∑_{j<J} 2^j ≤ 2^J` and
  `∑_{j<J} (j + 1) y^j ≤ (1 − y)^{−2}` for `0 ≤ y < 1` (the sum of the random errors in the proof
  of Lemma `lem:tree`, `∑ⱼ (1 + j) Q_{2^{-j} r} ≤ C Q_r`).
* `Q_div_two_pow_le`: `Q_{r/2^j} ≤ Q_r 2^{−j/4}` when the exponent of `Q` is at least `1/4`.
* `log_two_mul_linkCard`: `log₂ (2 · 2^{j(m+1)} 2^{(j+1)(m+1)}) = 1 + (2j + 1)(m + 1)`.
* `l1Dist_le_norm`: `|x − y|₁ ≤ (m + 1) |x − y|`.
* `norm_le_of_isSubgradient`: a subgradient of `μ` has norm at most the constant of `μ ≤ C|·|`.
* `isOs_final_step`: the last step of a chain, a coordinate path of bounded length.
* `thicken_subset_shearBox`: the thickened cube lies in the sheared box of the chaining.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem sum_range_two_pow_le (J : ℕ) : ∑ j ∈ Finset.range J, (2 : ℝ) ^ j ≤ 2 ^ J := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, pow_succ]; linarith only [ih]

theorem sum_range_succ_mul_pow_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, ((j : ℝ) + 1) * y ^ j ≤ 1 / (1 - y) ^ 2 := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := y)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hy0]; exact hy1)
  have h2 := hasSum_geometric_of_lt_one hy0 hy1
  have h := h1.add h2
  have heq : y / (1 - y) ^ 2 + (1 - y)⁻¹ = 1 / (1 - y) ^ 2 := by
    have : 1 - y ≠ 0 := by linarith only [hy1]
    field_simp; ring
  rw [heq] at h
  calc ∑ j ∈ Finset.range J, ((j : ℝ) + 1) * y ^ j =
      ∑ j ∈ Finset.range J, ((j : ℝ) * y ^ j + y ^ j) :=
        Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 1 / (1 - y) ^ 2 := sum_le_hasSum _ (fun i _ => by positivity) h

/-- `Q_{r/2^j} ≤ Q_r 2^{−j/4}` when the exponent `1/2 − δ/K` of `Q` is at least `1/4`. -/
theorem Q_div_two_pow_le (M : Model m) (K : ℕ) {A r : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r)
    (he : (1 : ℝ) / 4 ≤ 1 / 2 - M.δ / K) (j : ℕ) :
    Q M K A (r / 2 ^ j) ≤ Q M K A r * ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ ^ j := by
  unfold Q
  set e := (1 : ℝ) / 2 - M.δ / K with hedef
  have hpow1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h1 : ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) ≤ ((2 : ℝ) ^ j) ^ e :=
    Real.rpow_le_rpow_of_exponent_le hpow1 he
  have h2 : ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 4) = ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ j :=
    (Real.rpow_pow_comm (by norm_num) _ j).symm
  rw [Real.div_rpow hr (by positivity), mul_assoc, inv_pow, ← div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hA
  rw [← h2]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1

theorem log_two_mul_linkCard (m j : ℕ) :
    Real.log (2 * ((2 ^ (j * (m + 1)) * 2 ^ ((j + 1) * (m + 1)) : ℕ) : ℝ)) / Real.log 2 =
      1 + (2 * j + 1) * (m + 1) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h : (2 : ℝ) * ((2 ^ (j * (m + 1)) * 2 ^ ((j + 1) * (m + 1)) : ℕ) : ℝ) =
      2 ^ (1 + (j * (m + 1) + (j + 1) * (m + 1))) := by
    push_cast; ring
  rw [h, Real.log_pow, mul_div_assoc, div_self hlog2, mul_one]
  push_cast; ring

/-- `|x − y|₁ ≤ (m + 1) |x − y|`. -/
theorem l1Dist_le_norm (x y : Vertex m) :
    (Infra.FPP.l1Dist x y : ℝ) ≤ ((m : ℝ) + 1) * ‖point x - point y‖ := by
  have h := Infra.FPP.l1Dist_eq x y
  have hR : (Infra.FPP.l1Dist x y : ℝ) = |(x.1 : ℝ) - y.1| + ∑ j, |(x.2 j : ℝ) - y.2 j| := by
    have := congrArg (Int.cast (R := ℝ)) h
    push_cast at this
    exact this
  rw [hR]
  have h1 : |(x.1 : ℝ) - y.1| ≤ ‖point x - point y‖ := by
    have := Proofs.Geometry.abs_fst_le_norm (point x - point y)
    rwa [WithLp.sub_fst, Infra.FPP.point_fst, Infra.FPP.point_fst] at this
  have h2 : ∀ j, |(x.2 j : ℝ) - y.2 j| ≤ ‖point x - point y‖ := by
    intro j
    have h3 := ExpArray.abs_apply_le_norm (point x - point y).snd j
    have h4 := Proofs.Geometry.norm_snd_le_norm (point x - point y)
    rw [WithLp.sub_snd, Infra.FPP.point_snd, Infra.FPP.point_snd, PiLp.sub_apply,
      Infra.FPP.transversePoint_apply, Infra.FPP.transversePoint_apply] at h3
    exact h3.trans h4
  calc |(x.1 : ℝ) - y.1| + ∑ j, |(x.2 j : ℝ) - y.2 j| ≤
      ‖point x - point y‖ + ∑ _j : Fin m, ‖point x - point y‖ :=
        add_le_add h1 (Finset.sum_le_sum fun j _ => h2 j)
    _ = _ := by simp; ring

/-- A subgradient `P` of `μ ≤ C|·|` has `|P| ≤ C`. -/
theorem norm_le_of_isSubgradient {M : Model m} {hi : ℝ} (hhi0 : 0 ≤ hi)
    (hhi : ∀ z : Pt m, M.μ.1 z ≤ hi * ‖z‖) {x P : Pt m} (hP : IsSubgradient M.μ x P) :
    ‖P‖ ≤ hi := by
  have h := hP.2 P
  rw [real_inner_self_eq_norm_sq] at h
  have h' := h.trans (hhi P)
  rcases (norm_nonneg P).eq_or_lt with h0 | h0
  · rw [← h0]; exact hhi0
  · nlinarith only [h', h0]

/-- **The last step of a chain**: if `|u − x| ≤ L` and `|P| ≤ C`, then
`T(x, u) − P·(u − x) ≤ O₁(θ₀((m + 1) L + 1) + 2 C L)`. -/
theorem isOs_final_step {M : Model m} (hM : M.Standing) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hw : ∀ e : Edge m, IsOs M.P 1 θ₀ (fun ω => (ω e : ℝ))) {hi : ℝ} (hhi0 : 0 ≤ hi) {P : Pt m}
    (hP : ‖P‖ ≤ hi) {x u : Vertex m} {L : ℝ} (hL : ‖point u - point x‖ ≤ L) :
    IsOs M.P 1 (θ₀ * (((m : ℝ) + 1) * L + 1) + 2 * (hi * L))
      (fun ω => passageTimeReal ω x u - inner ℝ P (point u - point x)) := by
  have := hM.probP
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  have h1 := isOs_passageTimeReal_l1Dist hM hθ₀ hw x u
  have hl1 : (Infra.FPP.l1Dist x u : ℝ) ≤ ((m : ℝ) + 1) * L := by
    rw [Infra.FPP.l1Dist_comm]
    exact (l1Dist_le_norm u x).trans (mul_le_mul_of_nonneg_left hL (by positivity))
  have h2 := h1.mono_scale (η := θ₀ * (((m : ℝ) + 1) * L + 1)) zero_le_one (by positivity)
    (mul_le_mul_of_nonneg_left (by linarith only [hl1]) hθ₀.le)
  have h3 := isOs_add_const h2 (by positivity) (mul_nonneg hhi0 hL0)
  refine h3.mono zero_le_one (by positivity)
    ((measurable_passageTimeReal x u).sub_const _).aemeasurable
    (Eventually.of_forall fun ω => ?_)
  have h4 : -inner ℝ P (point u - point x) ≤ hi * L := by
    have := abs_real_inner_le_norm P (point u - point x)
    have h5 : ‖P‖ * ‖point u - point x‖ ≤ hi * L :=
      mul_le_mul hP hL (norm_nonneg _) hhi0
    linarith only [(abs_le.mp this).1, h5]
  change passageTimeReal ω x u - inner ℝ P (point u - point x) ≤ passageTimeReal ω x u + hi * L
  linarith only [h4]

/-- The cube `I` thickened by `λ` along `(1, t)` lies in the sheared box with `R₁ > λ + √d` and
`R₂ > a₀/2 + √d (1 + |t|)`. -/
theorem thicken_subset_shearBox {p : ℤ} {c t : E} {a₀ lam R₁ R₂ : ℝ}
    (hR₁ : lam + Real.sqrt ((m : ℝ) + 1) < R₁)
    (hR₂ : a₀ / 2 + Real.sqrt ((m : ℝ) + 1) * (1 + ‖t‖) < R₂) :
    thicken (transverseCube p c a₀) t lam ⊆ (shearBox p c t R₁ R₂ : Set (Vertex m)) := by
  intro u hu
  obtain ⟨x, hx, τ, hτ, hux⟩ := hu
  obtain ⟨hx1, hx2⟩ := hx
  rw [Finset.mem_coe, mem_shearBox]
  set v := point u - (point x + τ • slopeVec t) with hv
  have hvf : v.fst = (u.1 : ℝ) - p - τ := by
    rw [hv, WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst, Infra.FPP.point_fst,
      Infra.FPP.point_fst, hx1]
    change (u.1 : ℝ) - (p + τ * 1) = _
    ring
  have hvs : ∀ k, v.snd k = (u.2 k : ℝ) - x.2 k - τ * t k := by
    intro k
    rw [hv, WithLp.sub_snd, WithLp.add_snd, WithLp.smul_snd, Infra.FPP.point_snd,
      Infra.FPP.point_snd]
    change (u.2 k : ℝ) - ((x.2 k : ℝ) + τ * t k) = _
    ring
  have h1 : |v.fst| ≤ Real.sqrt ((m : ℝ) + 1) := (Proofs.Geometry.abs_fst_le_norm v).trans hux
  constructor
  · unfold shearTau
    rw [abs_le] at h1 hτ
    rw [abs_lt]
    rw [hvf] at h1
    constructor <;> linarith only [h1.1, h1.2, hτ.1, hτ.2, hR₁]
  · intro k
    have h2 : |v.snd k| ≤ Real.sqrt ((m : ℝ) + 1) :=
      (ExpArray.abs_apply_le_norm v.snd k).trans ((Proofs.Geometry.norm_snd_le_norm v).trans hux)
    have h3 : |t k| ≤ ‖t‖ := ExpArray.abs_apply_le_norm t k
    have hw : shearW p c t u k = ((x.2 k : ℝ) - c k) + v.snd k - v.fst * t k := by
      rw [hvs k, hvf]
      simp only [shearW, shearTau, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        Infra.FPP.transversePoint_apply]
      ring
    rw [hw]
    have h4 : |v.fst * t k| ≤ Real.sqrt ((m : ℝ) + 1) * ‖t‖ := by
      rw [abs_mul]; exact mul_le_mul h1 h3 (abs_nonneg _) (Real.sqrt_nonneg _)
    have h5 := hx2 k
    calc |((x.2 k : ℝ) - c k) + v.snd k - v.fst * t k| ≤
        |(x.2 k : ℝ) - c k| + |v.snd k| + |v.fst * t k| := by
          refine (abs_sub _ _).trans ?_
          exact add_le_add (abs_add_le _ _) le_rfl
      _ < R₂ := by nlinarith only [h2, h4, h5, hR₂]

end CurvatureVariance.Paper.Moments
