/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ConnectorSums
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chaining of equation `eq:tree` under the premise

The proof of Lemma `lem:tree`. The chain points of `CurvatureVariance.Paper.Proofs.Moments.Shear`,
with links bounded by the premise, equation `eq:premise` (`chain_link_bounds`), and the last step
by a coordinate path (`isOs_final_step`), give one
variable bounding `T(a, u) − P'·(u − a)` over the sheared box (`exists_chain_premise`, an
application of `exists_isOs_chain`). Its scale is the sum of three terms, bounded here:

* `sum_link_scales_le`: the random errors,
  `∑_{j<J} log₂(2Bⱼ) Q_{r/2^j} ≤ 2(m+1)(1 − 2^{−1/4})^{−2} Q_r`
  (the sum over the generations in the proof of Lemma `lem:tree`);
* `log_two_mul_card_le`: the maximum over the final steps, `log₂(2|U|)` for `|U| ≤ (C₁ r)^{m+1}`;
* `sum_linkCostBound_le`: the deterministic costs,
  `∑ⱼ (…) ≤ C(72 m R₂²/r + 64 ε₁² 2^J/r + 2r|t − t₀|^{2+δ})`, `ε₁ = (2 + T)√d`
  for a bound `T ≥ |t₀|` (`roundSlack`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- The bound on the cost of the links of generation `j` (`chain_link_bounds`). -/
noncomputable def linkCostBound (M : Model m) (T CS R₂ r : ℝ) (t : E) (j : ℕ) : ℝ :=
  CS * (2 * (Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j))) ^ 2 + 8 * roundSlack m T ^ 2) *
      (2 ^ (j + 3) / r) + CS * (r / 2 ^ j) * ‖t - M.t₀‖ ^ (2 + M.δ)

/-- The number of links of generation `j`. -/
def linkCard (m j : ℕ) : ℕ := 2 ^ (j * (m + 1)) * 2 ^ ((j + 1) * (m + 1))

/-- **The chain under the premise.** -/
theorem exists_chain_premise {M : Model m} (hM : M.Standing) {T : ℝ} (hT : ‖M.t₀‖ ≤ T)
    {cS CS r₁ : ℝ}
    (h24 : ∀ t h : E, ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hCS : 0 < CS) (hr₁ : 0 < r₁) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hw : ∀ e : Edge m, IsOs M.P 1 θ₀ (fun ω => (ω e : ℝ))) {hi : ℝ} (hhi0 : 0 ≤ hi)
    (hhi : ∀ z : Pt m, M.μ.1 z ≤ hi * ‖z‖)
    {K : ℕ} (hK : 2 ≤ K) {A : ℝ} (hA : 1 ≤ A) {N : ℕ} (hPrem : Premise M K A N)
    {p : ℤ} {c t : E} {R₁ R₂ r sg θ L₁ Lf : ℝ} (hsg : sg = 1 ∨ sg = -1) {a : Vertex m}
    (ha : ‖point a - (WithLp.toLp 2 ((p : ℝ), c) + (sg * r) • slopeVec t)‖ ≤
      Real.sqrt ((m : ℝ) + 1))
    {P : Pt m} (hP : IsSubgradient M.μ (slopeVec t) P) (ht1 : ‖t - M.t₀‖ ≤ 1)
    (htr : ‖t - M.t₀‖ ≤ r₁ / 2) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hslope : ∀ lam : ℝ, 0 < lam → lam ≤ r →
      lam * ‖t - M.t₀‖ ≤ θ * lam ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hr : 0 < r) (hR₁r : R₁ ≤ r / 32) (hrN : r ≤ N / 2)
    (hmarg : 12 * Real.sqrt m * R₂ ≤ (1 - θ) * r ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hL₁ : 2 * roundSlack m T + 1 ≤ 29 / 32 * L₁ ∧
      (4 * roundSlack m T / (1 - θ)) ^ 2 ≤ 29 / 32 * L₁ ∧ (4 / r₁) ^ 5 ≤ 29 / 32 * L₁)
    {J : ℕ} (hJ : ∀ j < J, L₁ ≤ r / 2 ^ (j + 1))
    (hfinal : ∀ u ∈ shearBox p c t R₁ R₂,
      ‖point u - point (chainPoint p c t R₁ R₂ r sg a J u)‖ ≤ Lf)
    (hU : (shearBox p c t R₁ R₂).Nonempty) :
    ∃ X : Config m → ℝ, IsOs M.P 1
        (∑ j ∈ Finset.range J, Real.log (2 * (linkCard m j : ℝ)) / Real.log 2 *
            Q M K A (r / 2 ^ j) +
          Real.log (2 * (shearBox p c t R₁ R₂).card) / Real.log 2 *
            (θ₀ * (((m : ℝ) + 1) * Lf + 1) + 2 * (hi * Lf)) +
          2 * ∑ j ∈ Finset.range J, linkCostBound M T CS R₂ r t j) X ∧
      ∀ ω, ∀ u ∈ shearBox p c t R₁ R₂,
        passageTimeReal ω a u - inner ℝ ((-sg) • P) (point u - point a) ≤ X ω := by
  have hA0 : (0 : ℝ) < A := by linarith only [hA]
  have hP' : ‖(-sg) • P‖ ≤ hi := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg,
      show |sg| = 1 by rcases hsg with rfl | rfl <;> norm_num, one_mul]
    exact norm_le_of_isSubgradient hhi0 hhi hP
  have hLf0 : 0 ≤ Lf := by
    obtain ⟨u, hu⟩ := hU
    exact (norm_nonneg _).trans (hfinal u hu)
  have hcostnn : 0 ≤ ∑ j ∈ Finset.range J, linkCostBound M T CS R₂ r t j :=
    Finset.sum_nonneg fun j _ => by unfold linkCostBound; positivity
  exact exists_isOs_chain hM ((-sg) • P) a (shearBox p c t R₁ R₂) hU J
    (chainPoint p c t R₁ R₂ r sg a) (fun u _ => chainPoint_zero _ _ _ _ _ _ _ _ _)
    (fun j => Q M K A (r / 2 ^ j)) (fun j => Q_pos M K hA0 (by positivity))
    (fun j => (linkCard m j : ℝ))
    (fun j hj u hu => (chain_link_bounds hM hT h24 hCS hr₁ hK hA hPrem hsg ha hP ht1 htr hθ0 hθ1
      hslope hR₁ hR₂ hr hR₁r hrN hmarg hL₁ (hJ j hj) hu).1)
    (fun j _ => by exact_mod_cast card_image_chainPoint_le p c t hR₁ hR₂ r sg a j)
    _ hcostnn
    (fun u hu => Finset.sum_le_sum fun j hj => (chain_link_bounds hM hT h24 hCS hr₁ hK hA hPrem
      hsg ha hP ht1 htr hθ0 hθ1 hslope hR₁ hR₂ hr hR₁r hrN hmarg hL₁
      (hJ j (Finset.mem_range.mp hj)) hu).2)
    _ (by positivity)
    (fun u hu => isOs_final_step hM hθ₀ hw hhi0 hP' (hfinal u hu))

/-- The random errors of the links: `∑_{j<J} log₂(2Bⱼ) Q_{r/2^j} ≤ 2(m+1)(1 − y)^{−2} Q_r`,
`y = 2^{−1/4}` (the sum over the generations in the proof of Lemma `lem:tree`). -/
theorem sum_link_scales_le (M : Model m) (K : ℕ) {A r : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r)
    (he : (1 : ℝ) / 4 ≤ 1 / 2 - M.δ / K) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.log (2 * (linkCard m j : ℝ)) / Real.log 2 * Q M K A (r / 2 ^ j) ≤
      2 * ((m : ℝ) + 1) * (1 / (1 - ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹) ^ 2) * Q M K A r := by
  set y := ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by
    rw [hy]
    apply inv_lt_one_of_one_lt₀
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hQ : 0 ≤ Q M K A r := by unfold Q; positivity
  calc ∑ j ∈ Finset.range J, Real.log (2 * (linkCard m j : ℝ)) / Real.log 2 * Q M K A (r / 2 ^ j)
      ≤ ∑ j ∈ Finset.range J, 2 * ((m : ℝ) + 1) * Q M K A r * (((j : ℝ) + 1) * y ^ j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [linkCard, log_two_mul_linkCard]
        have h1 := Q_div_two_pow_le M K hA hr he j
        have hQj : 0 ≤ Q M K A (r / 2 ^ j) := by unfold Q; positivity
        calc (1 + (2 * (j : ℝ) + 1) * ((m : ℝ) + 1)) * Q M K A (r / 2 ^ j)
            ≤ (2 * ((m : ℝ) + 1) * ((j : ℝ) + 1)) * (Q M K A r * y ^ j) := by
              apply mul_le_mul _ h1 hQj (by positivity)
              nlinarith only [Nat.cast_nonneg (α := ℝ) j, Nat.cast_nonneg (α := ℝ) m]
          _ = _ := by ring
    _ = 2 * ((m : ℝ) + 1) * Q M K A r * ∑ j ∈ Finset.range J, ((j : ℝ) + 1) * y ^ j := by
        rw [Finset.mul_sum]
    _ ≤ 2 * ((m : ℝ) + 1) * Q M K A r * (1 / (1 - y) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_range_succ_mul_pow_le hy0 hy1 J) (by positivity)
    _ = _ := by ring

/-- `log₂(2|U|) ≤ 1 + (m + 1)(|log C₁| + 4 r^{1/4})/log 2` when `|U| ≤ (C₁ r)^{m+1}`. -/
theorem log_two_mul_card_le {n : ℕ} {C₁ r : ℝ} (hn : 1 ≤ n) (hC₁ : 0 < C₁) (hr : 1 ≤ r)
    (hcard : (n : ℝ) ≤ (C₁ * r) ^ (m + 1)) :
    Real.log (2 * n) / Real.log 2 ≤
      1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4 * r ^ ((1 : ℝ) / 4)) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : Real.log (2 * n) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) (by positivity)
  have h2 : Real.log n ≤ ((m : ℝ) + 1) * (Real.log C₁ + Real.log r) := by
    calc Real.log n ≤ Real.log ((C₁ * r) ^ (m + 1)) := Real.log_le_log (by positivity) hcard
      _ = ((m : ℝ) + 1) * (Real.log C₁ + Real.log r) := by
        rw [Real.log_pow, Real.log_mul hC₁.ne' (by positivity)]; push_cast; ring
  have h3 : Real.log r ≤ 4 * r ^ ((1 : ℝ) / 4) := by
    have := Real.log_le_rpow_div (x := r) (by positivity) (by norm_num : (0 : ℝ) < 1 / 4)
    linarith only [this]
  have h4 : Real.log C₁ ≤ |Real.log C₁| := le_abs_self _
  rw [h1, add_div, div_self hlog2.ne', add_le_add_iff_left]
  apply div_le_div_of_nonneg_right _ hlog2.le
  calc Real.log n ≤ ((m : ℝ) + 1) * (Real.log C₁ + Real.log r) := h2
    _ ≤ ((m : ℝ) + 1) * (|Real.log C₁| + 4 * r ^ ((1 : ℝ) / 4)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [h3, h4]

/-- The deterministic costs of the links. -/
theorem sum_linkCostBound_le (M : Model m) (T : ℝ) {CS R₂ r : ℝ} (hCS : 0 ≤ CS) (hr : 0 < r) (t : E)
    (J : ℕ) :
    ∑ j ∈ Finset.range J, linkCostBound M T CS R₂ r t j ≤
      CS * (72 * m * R₂ ^ 2 / r + 64 * roundSlack m T ^ 2 * 2 ^ J / r +
        2 * r * ‖t - M.t₀‖ ^ (2 + M.δ)) := by
  have hterm : ∀ j : ℕ, linkCostBound M T CS R₂ r t j =
      CS * (36 * m * R₂ ^ 2 / r) * (1 / 2 : ℝ) ^ j +
        CS * (64 * roundSlack m T ^ 2 / r) * 2 ^ j +
        CS * (r * ‖t - M.t₀‖ ^ (2 + M.δ)) * (1 / 2 : ℝ) ^ j := by
    intro j
    unfold linkCostBound
    have hm : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
    have hpow : (0 : ℝ) < 2 ^ j := by positivity
    rw [one_div_pow, pow_add]
    field_simp
    rw [hm]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have h1 := sum_geometric_two_le J
  have h2 := sum_range_two_pow_le J
  have hc1 : 0 ≤ CS * (36 * m * R₂ ^ 2 / r) := by positivity
  have hc2 : 0 ≤ CS * (64 * roundSlack m T ^ 2 / r) := by positivity
  have hc3 : 0 ≤ CS * (r * ‖t - M.t₀‖ ^ (2 + M.δ)) := by positivity
  have e1 := mul_le_mul_of_nonneg_left h1 hc1
  have e2 := mul_le_mul_of_nonneg_left h2 hc2
  have e3 := mul_le_mul_of_nonneg_left h1 hc3
  have heq : CS * (72 * m * R₂ ^ 2 / r + 64 * roundSlack m T ^ 2 * 2 ^ J / r +
      2 * r * ‖t - M.t₀‖ ^ (2 + M.δ)) = CS * (36 * m * R₂ ^ 2 / r) * 2 +
        CS * (64 * roundSlack m T ^ 2 / r) * 2 ^ J +
        CS * (r * ‖t - M.t₀‖ ^ (2 + M.δ)) * 2 := by
    field_simp; ring
  rw [heq]
  linarith only [e1, e2, e3]

end CurvatureVariance.Paper.Moments
