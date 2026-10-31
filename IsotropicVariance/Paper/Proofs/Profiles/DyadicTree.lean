/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.DyadicBoxes
public import IsotropicVariance.Paper.Proofs.Profiles.Profiles
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chain over the dyadic subboxes (proof of Lemma `lem:tree`)

The end of the proof of Lemma `lem:tree`, from the definition of `j₀` on. For
`z = g y` in the box, `y_j` is the point attached to the subbox of generation `j` containing `z`,
these subboxes being nested, so that consecutive points form a pair of `𝒜_j`.

* `dyadicTree_chain`: the triangle inequality along `y_0 = x, y_1, …, y_{j₀}, z`, with
  `|z − y_{j₀}| ≤ 9` and equation `eq:treestep`.
* `dyadicTree_bound`: the union bound `eq:union` at each generation, then the sum rule `eq:sum`.

The paper takes `x = 0` and `e = e₁`. Here `x`, `e` are general: the hypothesis on the steps is for
every pair of points, so isotropy is used once per pair, where the steps are bounded.
-/

@[expose] public section

open MeasureTheory Set Metric Finset
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os

variable {m : ℕ}

/-- The constant of Lemma `lem:tree`. -/
noncomputable def dyadicTreeConst (m : ℕ) (Bd Cs Λ : ℝ) : ℝ :=
  4 * (m + 1) * Cs * treeSeries + (8 / 15 * Λ + 9 * (Bd + 1) + 1) / Real.log 2

open scoped Classical in
/-- **The chain**: for a point `z = g y` of the box,
`T(x, z) − (z − x)·e` is at most the sum over `j < j₀` of the largest excess `X_j` of the pairs of
`𝒜_j` (any upper bounds `Y j`), plus `C 2^{−j} Q_t` for the step along `e`, plus the last segment,
of length at most `9`. -/
lemma dyadicTree_chain (X : Setting m) {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd)
    {g : Pt m ≃ᵃⁱ[ℝ] Pt m} {r₀ : ℝ} {r : Fin m → ℝ} {x e : Pt m} {t w Λ κ : ℝ}
    (he : ‖e‖ = 1) (hg0 : g 0 = x + t • e)
    (hdiam : ∀ z ∈ g '' stdBox r₀ r, ∀ z' ∈ g '' stdBox r₀ r, dist z z' ≤ t / 8)
    (hline : ∀ z ∈ g '' stdBox r₀ r, ‖perp e (z - x)‖ ≤ w) (ht : 16 ≤ t)
    (hwΛ : w ^ 2 ≤ Λ * t * κ) (Y : ℕ → X.Ω → ℝ)
    (hY : ∀ j ω, ∀ pq ∈ treePairs g r₀ r e t j,
      X.passTime ω pq.1 pq.2 - dist pq.1 pq.2 ≤ Y j ω)
    (ω : X.Ω) {y : Pt m} (hy : y ∈ stdBox r₀ r) :
    X.passTime ω x (g y) - ⟪g y - x, e⟫ ≤
      ∑ j ∈ range (dyadicDepth t), max (Y j ω) 0 + (8 / 15 * (Λ * κ) + 9 * (Bd + 1)) := by
  have htpos : 0 < t := by linarith only [ht]
  have hΛκ : w ^ 2 / t ≤ Λ * κ := by
    rw [div_le_iff₀ htpos]
    linarith only [hwΛ]
  have hΛκ0 : 0 ≤ Λ * κ := (div_nonneg (sq_nonneg w) htpos.le).trans hΛκ
  have hr₀ : 0 ≤ r₀ := (abs_nonneg _).trans hy.1
  have hr : ∀ k, 0 ≤ r k := fun k => (abs_nonneg _).trans (hy.2 k)
  set J := dyadicDepth t with hJ
  set p : ℕ → Pt m := fun j => attachedPt g r₀ r e t j (chainIndex r₀ r y j) with hp
  have hp0 : p 0 = x := by
    have h0 : subboxCenter r₀ r 0 (chainIndex r₀ r y 0) = 0 := by
      apply pt_ext
      · simp [subboxCenter, chainIndex_zero, cellCenter]
      · ext k
        simp [subboxCenter, chainIndex_zero, cellCenter]
    simp [p, attachedPt, h0, hg0, genScale]
  -- each step lies in `𝒜_j` and satisfies `eq:treestep`
  have hstep : ∀ j, (p j, p (j + 1)) ∈ treePairs g r₀ r e t j ∧
      dist (p j) (p (j + 1)) - ⟪p (j + 1) - p j, e⟫ ≤
        ((2 : ℝ) ^ j)⁻¹ * (4 / 15 * w ^ 2 / t) := by
    intro j
    obtain ⟨σ, hσ, hchild⟩ := exists_chainIndex_succ r₀ r y j
    have hpj : p (j + 1) = attachedPt g r₀ r e t (j + 1)
        (fun κ => 2 * chainIndex r₀ r y j κ + σ κ) := by
      simp only [p, hchild]
    refine ⟨?_, ?_⟩
    · rw [treePairs, Finset.mem_image]
      refine ⟨(fun κ => ⟨_, chainIndex_lt hy j κ⟩, fun κ => ⟨_, hσ κ⟩), Finset.mem_univ _, ?_⟩
      rw [hpj]
    · rw [hpj]
      exact (attached_step he hg0 hdiam hline htpos hr₀ hr j _ hσ).2.2
  -- each step, in terms of the excess
  have hT : ∀ j, X.passTime ω (p j) (p (j + 1)) ≤
      max (Y j ω) 0 + ⟪p (j + 1) - p j, e⟫ + 4 / 15 * (Λ * κ) * ((2 : ℝ) ^ j)⁻¹ := by
    intro j
    obtain ⟨h1, h2⟩ := hstep j
    have h4 := hY j ω _ h1
    have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹ := by positivity
    have h6 : ((2 : ℝ) ^ j)⁻¹ * (4 / 15 * w ^ 2 / t) ≤ 4 / 15 * (Λ * κ) * ((2 : ℝ) ^ j)⁻¹ := by
      have e1 : ((2 : ℝ) ^ j)⁻¹ * (4 / 15 * w ^ 2 / t) =
          ((2 : ℝ) ^ j)⁻¹ * (4 / 15 * (w ^ 2 / t)) := by ring
      have e2 := mul_le_mul_of_nonneg_left hΛκ (by positivity : 0 ≤ ((2 : ℝ) ^ j)⁻¹ * (4 / 15))
      rw [e1]
      linarith only [e2]
    simp only at h4
    linarith only [le_max_left (Y j ω) 0, h2, h4, h6]
  have hsum : ∑ j ∈ range J, X.passTime ω (p j) (p (j + 1)) ≤
      ∑ j ∈ range J, max (Y j ω) 0 + ⟪p J - p 0, e⟫ + 8 / 15 * (Λ * κ) := by
    refine (sum_le_sum fun j _ => hT j).trans ?_
    rw [sum_add_distrib, sum_add_distrib]
    have htel : ∑ j ∈ range J, ⟪p (j + 1) - p j, e⟫ = ⟪p J - p 0, e⟫ := by
      simp only [inner_sub_left]
      exact sum_range_sub (fun j => ⟪p j, e⟫) J
    rw [htel, ← mul_sum]
    have h2 := mul_le_mul_of_nonneg_left (sum_inv_two_pow_le J)
      (by positivity : 0 ≤ 4 / 15 * (Λ * κ))
    linarith only [h2]
  -- the last segment
  have hlast : dist (g y) (p J) ≤ 9 := by
    obtain ⟨h1, h2⟩ := chainIndex_close hy J
    have H := dist_attached_le he hdiam htpos h1 h2
    have h16 := genScale_depth_lt (by linarith only [ht] : 4 ≤ t)
    simp only [p]
    linarith only [H, h16]
  have hchain := passTime_le_sum_chain hBd hBd0 ω p J
  rw [hp0] at hchain
  have htri := passTime_triangle hBd ω x (p J) (g y)
  have hend := passTime_le_mul_dist hBd hBd0 ω (p J) (g y)
  rw [dist_comm] at hend
  have hinner : ⟪g y - x, e⟫ = ⟪g y - p J, e⟫ + ⟪p J - x, e⟫ := by
    rw [← inner_add_left]
    congr 1
    abel
  have hlow : -dist (g y) (p J) ≤ ⟪g y - p J, e⟫ := by
    have h := abs_real_inner_le_norm (g y - p J) e
    rw [he, mul_one, ← dist_eq_norm] at h
    linarith only [h, neg_abs_le ⟪g y - p J, e⟫]
  rw [hp0] at hsum
  have hB9 := mul_le_mul_of_nonneg_left hlast hBd0
  linarith only [hsum, hchain, htri, hend, hinner, hlow, hB9, hlast]

open scoped Classical in
/-- `X_j ≤ O_1(C (1 + j) 2^{−2j/5} κ)`: the union bound `eq:union` over
the pairs of `𝒜_j`, each of which has excess `O_1(C_s 2^{−2j/5} κ)`. -/
lemma isOs_generation {X : Setting m} {g : Pt m ≃ᵃⁱ[ℝ] Pt m} {r₀ : ℝ} {r : Fin m → ℝ} {e : Pt m}
    {t κ Cs : ℝ} (hκ : 0 < κ) (hCs : 0 < Cs) {j : ℕ} (hF : ∀ pq ∈ treePairs g r₀ r e t j,
      IsOs X.P 1 (Cs * treeRatio ^ j * κ) fun ω => X.passTime ω pq.1 pq.2 - dist pq.1 pq.2) :
    IsOs X.P 1 (4 * (m + 1) * (j + 1) * (Cs * treeRatio ^ j * κ))
      ((treePairs g r₀ r e t j).sup' (treePairs_nonempty g r₀ r e t j)
        fun pq ω => X.passTime ω pq.1 pq.2 - dist pq.1 pq.2) := by
  have hsθ : 0 < Cs * treeRatio ^ j * κ := by
    have := treeRatio_pos
    positivity
  have hn := treePairs_nonempty g r₀ r e t j
  have H := isOs_finset_sup'_log one_pos hsθ _ hn _ hF
  have hcard : 0 < Real.log (2 + ((treePairs g r₀ r e t j).card : ℝ)) := by
    refine Real.log_pos ?_
    have : (0 : ℝ) ≤ (treePairs g r₀ r e t j).card := Nat.cast_nonneg _
    linarith only [this]
  refine IsOs.mono_scale H zero_le_one (by
    simp only [div_one, Real.rpow_one]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity) ?_
  simp only [div_one, Real.rpow_one]
  have hu := union_factor_le m j ((card_treePairs_le g r₀ r e t j).trans
    (Nat.pow_le_pow_right (by norm_num) (by nlinarith only [])))
  calc 2 / Real.log 2 * (Cs * treeRatio ^ j * κ) *
        Real.log (2 + ((treePairs g r₀ r e t j).card : ℝ))
      = 2 / Real.log 2 * Real.log (2 + ((treePairs g r₀ r e t j).card : ℝ)) *
        (Cs * treeRatio ^ j * κ) := by ring
    _ ≤ 4 * (m + 1) * (j + 1) * (Cs * treeRatio ^ j * κ) :=
      mul_le_mul_of_nonneg_right hu hsθ.le

open scoped Classical in
/-- **The bound of Lemma `lem:tree` from the steps**: if every pair of
points at distance between `(15/32) 2^{−j} t` and `2^{−j} t`, with `2^{−j} t ≥ 8`, has excess
`O_1(C_s 2^{−2j/5} κ)`, then for every rectangular box `B` centered at `x + te`, `t ≥ 16`, of
diameter at most `t/8`, within `w` of the line `x + ℝe`, with `w² ≤ Λ t κ` and `κ ≥ 1`,
`sup_{z ∈ B} (T(x, z) − (z − x)·e) ≤ O_1(C κ)`. -/
theorem dyadicTree_bound (X : Setting m) {Bd : ℝ} (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd)
    {t κ w Cs Λ : ℝ} (ht : 16 ≤ t) (hκ : 1 ≤ κ) (hCs : 0 < Cs) (hwΛ : w ^ 2 ≤ Λ * t * κ)
    (hstep : ∀ j : ℕ, 8 ≤ genScale t j → ∀ p q : Pt m, 15 / 32 * genScale t j ≤ dist p q →
      dist p q ≤ genScale t j →
        IsOs X.P 1 (Cs * treeRatio ^ j * κ) fun ω => X.passTime ω p q - dist p q)
    {x e : Pt m} (he : ‖e‖ = 1) {B : Set (Pt m)} (hB : IsRectBox B (x + t • e))
    (hdiam : ∀ z ∈ B, ∀ z' ∈ B, dist z z' ≤ t / 8)
    (hline : ∀ z ∈ B, infDist z (range fun r : ℝ => x + r • e) ≤ w) :
    IsOs X.P 1 (dyadicTreeConst m Bd Cs Λ * κ)
      fun ω => ⨆ z : B, (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫) := by
  have htpos : 0 < t := by linarith only [ht]
  have hκ0 : 0 < κ := by linarith only [hκ]
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hΛκ0 : 0 ≤ Λ * κ := by
    have h : w ^ 2 / t ≤ Λ * κ := by
      rw [div_le_iff₀ htpos]
      linarith only [hwΛ]
    exact (div_nonneg (sq_nonneg w) htpos.le).trans h
  have hΛ0 : 0 ≤ Λ := nonneg_of_mul_nonneg_left hΛκ0 hκ0
  obtain ⟨g, r₀, r, hr₀, hr, hg0, rfl⟩ := hB
  change IsOs X.P 1 _ fun ω => ⨆ z : (g '' stdBox r₀ r), (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫)
  change ∀ z ∈ g '' stdBox r₀ r, ∀ z' ∈ g '' stdBox r₀ r, dist z z' ≤ t / 8 at hdiam
  change ∀ z ∈ g '' stdBox r₀ r, infDist z (range fun r : ℝ => x + r • e) ≤ w at hline
  have h0mem : (0 : Pt m) ∈ stdBox r₀ r := ⟨by simpa using hr₀, fun k => by simpa using hr k⟩
  have hcmem : x + t • e ∈ g '' stdBox r₀ r := hg0 ▸ mem_image_of_mem g h0mem
  have hline' : ∀ z ∈ g '' stdBox r₀ r, ‖perp e (z - x)‖ ≤ w :=
    fun z hz => (norm_perp_le_infDist he x z).trans (hline z hz)
  -- the largest excess of the pairs of each generation
  set J := dyadicDepth t with hJ
  let F : Pt m × Pt m → X.Ω → ℝ := fun pq ω => X.passTime ω pq.1 pq.2 - dist pq.1 pq.2
  let Y : ℕ → X.Ω → ℝ := fun j => (treePairs g r₀ r e t j).sup' (treePairs_nonempty g r₀ r e t j) F
  have hY : ∀ j ω, ∀ pq ∈ treePairs g r₀ r e t j,
      X.passTime ω pq.1 pq.2 - dist pq.1 pq.2 ≤ Y j ω := fun j ω pq hpq =>
    Finset.le_sup' F hpq ω
  let θ : ℕ → ℝ := fun j => 4 * (m + 1) * (j + 1) * (Cs * treeRatio ^ j * κ)
  have hθ : ∀ j, 0 < θ j := fun j => by
    have := treeRatio_pos
    positivity
  have hYos : ∀ j ∈ range J, IsOs X.P 1 (θ j) (Y j) := by
    intro j hj
    refine isOs_generation hκ0 hCs fun pq hpq => ?_
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hpq
    obtain ⟨h1, h2, -⟩ := attached_step (σ := fun κ => q.2 κ) he hg0 hdiam hline' htpos hr₀ hr j
      (fun κ => q.1 κ) fun κ => (q.2 κ).2
    exact hstep j (eight_le_genScale (by linarith only [ht]) (mem_range.mp hj)) _ _ h1 h2
  -- the sum over the generations
  let Z : X.Ω → ℝ := fun ω => ∑ j ∈ range J, max (Y j ω) 0
  have hJ0 : 0 < J := by
    obtain ⟨-, h1⟩ := dyadicDepth_spec (t := t) (by linarith only [ht])
    rcases Nat.eq_zero_or_pos J with h0 | h0
    · rw [← hJ, h0] at h1
      norm_num at h1
      linarith only [ht, h1]
    · exact h0
  have hrange : (range J).Nonempty := ⟨0, mem_range.mpr hJ0⟩
  have hZ : IsOs X.P 1 (∑ j ∈ range J, θ j) Z :=
    isOs_sum_of_one_le le_rfl _ θ (fun j _ => hθ j) (fun j ω => max (Y j ω) 0)
      (fun j hj => isOs_pos (hYos j hj)) (fun j _ => ae_of_all _ fun ω => le_max_right _ _)
  have hΘ : ∑ j ∈ range J, θ j ≤ 4 * (m + 1) * Cs * treeSeries * κ := by
    have h := sum_le_treeSeries J
    calc ∑ j ∈ range J, θ j
        = 4 * (m + 1) * Cs * κ * ∑ j ∈ range J, ((j : ℝ) + 1) * treeRatio ^ j := by
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring
      _ ≤ 4 * (m + 1) * Cs * κ * treeSeries :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 4 * (m + 1) * Cs * treeSeries * κ := by ring
  set D : ℝ := 8 / 15 * (Λ * κ) + 9 * (Bd + 1) with hD
  have hD0 : 0 ≤ D := by positivity
  have hΘpos : 0 < ∑ j ∈ range J, θ j := sum_pos (fun j _ => hθ j) hrange
  have hZD := isOs_add_const hZ hΘpos hD0
  have hscale : 0 < ∑ j ∈ range J, θ j + (D + 1) / Real.log 2 := by positivity
  -- the supremum
  have hdistx : ∀ z ∈ g '' stdBox r₀ r, dist x z ≤ 9 / 8 * t := fun z hz => by
    have h1 := dist_triangle x (x + t • e) z
    have h3 : dist x (x + t • e) = t := by
      rw [dist_eq_norm, show x - (x + t • e) = -(t • e) by abel, norm_neg, norm_smul, he,
        mul_one, Real.norm_eq_abs, abs_of_pos htpos]
    have h4 := hdiam _ hcmem z hz
    linarith only [h1, h3, h4]
  have hbdd := fun ω => bddAbove_passTime_sub hBd hBd0 ω he hdistx
  have hmeas : AEMeasurable (fun ω => ⨆ z : (g '' stdBox r₀ r),
      (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫)) X.P := by
    refine aemeasurable_iSup_of_continuous (fun ω => ?_) hbdd fun z => ?_
    · exact ((continuous_passTime hBd ω).comp (continuous_const.prodMk continuous_subtype_val)).sub
        ((continuous_subtype_val.sub continuous_const).inner continuous_const)
    · exact (aemeasurable_passTime x z).sub_const _
  have hle : ∀ ω, ⨆ z : (g '' stdBox r₀ r), (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫) ≤
      Z ω + D := by
    intro ω
    have : Nonempty (g '' stdBox r₀ r) := ⟨⟨_, hcmem⟩⟩
    refine ciSup_le fun ⟨z, hz⟩ => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    exact dyadicTree_chain X hBd hBd0 he hg0 hdiam hline' ht hwΛ Y hY ω hy
  refine (IsOs.mono hZD zero_le_one hscale hmeas (ae_of_all _ hle)).mono_scale
    zero_le_one hscale ?_
  unfold dyadicTreeConst
  have hκD : D + 1 ≤ (8 / 15 * Λ + 9 * (Bd + 1) + 1) * κ := by
    have h1 : 8 / 15 * Λ * 1 ≤ 8 / 15 * Λ * κ := mul_le_mul_of_nonneg_left hκ (by positivity)
    have h2 : 0 ≤ (9 * (Bd + 1) + 1) * (κ - 1) := mul_nonneg (by positivity) (by linarith only [hκ])
    rw [hD]
    linarith only [h2]
  have h3 : (D + 1) / Real.log 2 ≤ (8 / 15 * Λ + 9 * (Bd + 1) + 1) / Real.log 2 * κ := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hκD hl.le
  have e1 : (4 * (m + 1) * Cs * treeSeries + (8 / 15 * Λ + 9 * (Bd + 1) + 1) / Real.log 2) * κ =
      4 * (m + 1) * Cs * treeSeries * κ + (8 / 15 * Λ + 9 * (Bd + 1) + 1) / Real.log 2 * κ := by
    ring
  rw [e1]
  linarith only [hΘ, h3]

end IsotropicVariance.Paper.Proofs.Profiles
