/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.ChainCurve
public import IsotropicVariance.Paper.Proofs.SlabComparison.SlabPair
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! # Equation `eq:columns` on one outcome

The third paragraph of the proof of Lemma `lem:slab`, on one outcome, for a threshold `R` of
Lemma `lem:straight`.

* `admissible_of_straight`: if `s ≥ R`, ordered points of a near-geodesic from `τ` to `τ + ℓe₁` on
  the faces `{x · e₁ = τ₁ + is}` are admissible in equation `eq:F`, by Lemma `lem:straight` for the
  subarcs ending at `τ + ℓe₁` and for the reversed curve.
* `chain_comparison_straight`: the bound `T_P ≤ T + 6bR + 1` in each slab gives
  `F ≤ T_ℓ + 1 + M(6bR + 1)`.
* `chain_bound`: with the case `s < R`, by the points `ise₁`.

The paper takes the first points on the faces, and uses only their order; Lean takes the ordered
hits of `exists_ordered_hyperplane_hits`.
-/

@[expose] public section
open Set InnerProductGeometry
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper Infra.Slab
variable {m : ℕ}

@[simp] lemma lip_toRectifiable_apply {u v : Pt m} (γ : Infra.Curves.LipCurve (Pt m) u v)
    (t : ℝ) : γ.toRectifiable.toFun t = γ.toFun t := rfl

/-- The passage times along ordered points of a near-geodesic sum to at most the passage time
between the first and the last point plus one: `∑ T(x_{i−1}, x_i) ≤ T + 1`
(proof of equation `eq:columns`). -/
theorem ordered_passTime_sum_le_add_one (X : Setting m) (ω : X.Ω)
    (γ : IsotropicVariance.RectifiableCurve (Pt m)) {u v : Pt m}
    (hγ : IsOneOptimal (X.ρ ω) univ u v γ) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Icc (0 : ℝ) 1) (hmono : Monotone t) (M : ℕ) :
    (∑ i : Fin M, X.passTime ω (γ.toFun (t i)) (γ.toFun (t (i + 1)))) ≤
      X.passTime ω (γ.toFun (t 0)) (γ.toFun (t M)) + 1 := by
  have hsum : ∀ n : ℕ, (∑ i : Fin n, X.passTime ω (γ.toFun (t i)) (γ.toFun (t (i + 1)))) ≤
      pieceCost X ω γ (t 0) (t n) (ht 0).1 (hmono (Nat.zero_le n)) (ht n).2 := by
    intro n
    induction n with
    | zero => simp only [Fin.sum_univ_zero]; exact ENNReal.toReal_nonneg
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have hstep := passTime_le_pieceCost X ω γ (ht n).1 (hmono (Nat.le_succ n)) (ht (n + 1)).2
      have hadd := pieceCost_add X ω γ (ht 0).1 (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))
        (ht (n + 1)).2
      change (∑ i : Fin n, X.passTime ω (γ.toFun (t i)) (γ.toFun (t (i + 1)))) +
        X.passTime ω (γ.toFun (t n)) (γ.toFun (t (n + 1))) ≤ _
      linarith only [ih, hstep, hadd]
  exact (hsum M).trans (pieceCost_le_passTime_add_one X ω γ hγ (ht 0).1 (hmono (Nat.zero_le M))
    (ht M).2)

/-- **The ordered points of a near-geodesic are admissible** (proof of `eq:columns`): if `s ≥ R`,
Lemma `lem:straight` for the subarc from `x_i` to `τ + ℓe₁` bounds `∠(x_{i+1} − x_i, τ + ℓe₁ − x_i)`
by `1/10`, Lemma `lem:straight` for the reversed curve bounds `∠(τ + ℓe₁ − x_i, e₁)` by `1/10`, and
a vector at angle at most `1/5` from `e₁` has slope at most `1/4`. -/
theorem admissible_of_straight (X : Setting m) (ω : X.Ω) (M : ℕ) (hM : 1 ≤ M)
    {s : ℝ} (hs : 0 < s) (τ : Pt m)
    (γ : Infra.Curves.LipCurve (Pt m) τ (τ + ((M : ℝ) * s) • e₁))
    (hγ : IsOneOptimal (X.ρ ω) univ τ (τ + ((M : ℝ) * s) • e₁) γ.toRectifiable)
    (hγrev : IsOneOptimal (X.ρ ω) univ (τ + ((M : ℝ) * s) • e₁) τ γ.reverse.toRectifiable)
    {B : Set (Pt m)} {R : ℝ} (hstraight : StraightOn X ω B R) (hRs : R ≤ s)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ B)
    (t : ℕ → ℝ) (ht0 : t 0 = 0) (htM : t M = 1) (hmono : Monotone t)
    (ht : ∀ n, t n ∈ Icc (0 : ℝ) 1)
    (hlevel : ∀ n ≤ M, Pt.lon (γ.toFun (t n)) = Pt.lon τ + (n : ℝ) * s) :
    IsAdmissible M s τ (fun i => γ.toFun (t i)) := by
  have hτB : τ ∈ B := by simpa only [γ.map_zero] using hB 0 ⟨le_rfl, zero_le_one⟩
  have heB : τ + ((M : ℝ) * s) • e₁ ∈ B := by
    simpa only [γ.map_one] using hB 1 ⟨zero_le_one, le_rfl⟩
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hℓ : 0 < (M : ℝ) * s := mul_pos hM0 hs
  have hτe : τ + ((M : ℝ) * s) • e₁ ≠ τ := by
    intro h
    have hh := congrArg Pt.lon h
    rw [Pt.lon_add, Pt.lon_smul, Pt.lon_e₁, mul_one] at hh
    linarith only [hh, hℓ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Fin.val_zero, ht0] using γ.map_zero
  · simpa only [Fin.val_last, htM] using γ.map_one
  · intro i
    rw [Pt.lon_sub, hlevel i (Nat.le_of_lt_succ i.isLt)]
    ring
  · intro i
    have hi : (i : ℕ) + 1 ≤ M := Nat.succ_le_of_lt i.isLt
    have hi0 : (i : ℕ) ≤ M := (Nat.le_succ _).trans hi
    have hiR : (i : ℝ) + 1 ≤ M := by exact_mod_cast hi
    have hwidth : Pt.lon (γ.toFun (t (i + 1)) - γ.toFun (t i)) = s := by
      rw [Pt.lon_sub, hlevel _ hi, hlevel _ hi0, Nat.cast_add, Nat.cast_one]
      ring
    have hstep : s ≤ ‖γ.toFun (t (i + 1)) - γ.toFun (t i)‖ := by
      have hh := Profiles.abs_lon_le_norm (γ.toFun (t (i + 1)) - γ.toFun (t i))
      rwa [hwidth, abs_of_pos hs] at hh
    have hend : s ≤ ‖γ.toFun (t i) - (τ + ((M : ℝ) * s) • e₁)‖ := by
      have hh := Profiles.abs_lon_le_norm (γ.toFun (t i) - (τ + ((M : ℝ) * s) • e₁))
      rw [Pt.lon_sub, Pt.lon_add, Pt.lon_smul, Pt.lon_e₁, mul_one, hlevel _ hi0] at hh
      have hneg := neg_le_abs (Pt.lon τ + (i : ℝ) * s - (Pt.lon τ + M * s))
      have hmul := mul_le_mul_of_nonneg_right hiR hs.le
      linarith only [hh, hneg, hmul]
    have hne : γ.toFun (t i) ≠ τ + ((M : ℝ) * s) • e₁ := by
      intro h
      rw [h, sub_self, norm_zero] at hend
      linarith only [hend, hs]
    have hforward := hstraight.angle_subarc γ.toRectifiable hγ (ht i).1 (hmono (Nat.le_succ i))
      (ht (i + 1)).2 (hB _ (ht i)) heB hne (hRs.trans hstep)
    have hrev : γ.reverse.toRectifiable.toFun (1 - t i) = γ.toFun (t i) := by
      change γ.toFun (1 - (1 - t i)) = γ.toFun (t i)
      rw [sub_sub_cancel]
    have hbackward := hstraight _ heB τ hτB hτe γ.reverse.toRectifiable hγrev (1 - t i)
      ⟨by linarith only [(ht i).2], by linarith only [(ht i).1]⟩
      (by rw [hrev]; exact hRs.trans hend)
    rw [hrev] at hbackward
    have hw : γ.toFun (t i) - (τ + ((M : ℝ) * s) • e₁) =
        -(τ + ((M : ℝ) * s) • e₁ - γ.toFun (t i)) := (neg_sub _ _).symm
    have hax : τ - (τ + ((M : ℝ) * s) • e₁) = -(((M : ℝ) * s) • (e₁ : Pt m)) := by abel
    rw [hw, hax, angle_neg_neg, angle_smul_right_of_pos _ _ hℓ] at hbackward
    have hangle := (angle_le_angle_add_angle (γ.toFun (t (i + 1)) - γ.toFun (t i))
      (τ + ((M : ℝ) * s) • e₁ - γ.toFun (t i)) (e₁ : Pt m)).trans
        (add_le_add hforward hbackward)
    have hv : γ.toFun (t (i + 1)) - γ.toFun (t i) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hstep
      linarith only [hstep, hs]
    have hcone := tr_le_lon_of_angle_le hv (hangle.trans_eq (by norm_num))
    rw [hwidth] at hcone
    change ‖(γ.toFun (t (i + 1)) - γ.toFun (t i)) - s • e₁‖ ≤ s / 4
    rw [norm_sub_smul_e₁_of_lon hwidth]
    exact hcone

/-- **Equation `eq:columns`, the case of a large width**, on one outcome:
if `R ≤ s`, for `R ≥ 9` a threshold of Lemma `lem:straight` on a set containing the near-geodesics
from `τ` to `τ + ℓe₁`, then `F ≤ T_ℓ + 1 + M(6bR + 1)`. -/
theorem chain_comparison_straight (X : Setting m) (ω : X.Ω) {b : ℝ} (hb : X.IsUpperBound b)
    (M : ℕ) (hM : 1 ≤ M) {s : ℝ} (hs : 0 < s) (τ : Pt m)
    {B : Set (Pt m)} {R : ℝ} (hstraight : StraightOn X ω B R)
    (hB : ∀ γ : IsotropicVariance.RectifiableCurve (Pt m),
      IsOneOptimal (X.ρ ω) univ τ (τ + ((M : ℝ) * s) • e₁) γ →
        ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ B)
    (hR : 9 ≤ R) (hRs : R ≤ s) :
    X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁) ≤ 1 + M * (6 * b * R + 1) := by
  obtain ⟨γ, hγ, hγrev⟩ := exists_oneOptimal_lipschitz X ω τ (τ + ((M : ℝ) * s) • e₁)
  obtain ⟨t, ht0, htM, hmono, ht⟩ := exists_ordered_hyperplane_hits M hM hs τ γ
  have hlevel (n : ℕ) (hn : n ≤ M) :
      Pt.lon (γ.toFun (t n)) = Pt.lon τ + (n : ℝ) * s := by
    simpa only [min_eq_left hn] using (ht n).2
  have hγB := hB γ.toRectifiable hγ
  have hx : IsAdmissible M s τ (fun i => γ.toFun (t i)) :=
    admissible_of_straight X ω M hM hs τ γ hγ hγrev hstraight hRs hγB t ht0 htM hmono
      (fun n => (ht n).1) hlevel
  have hlocal (i : Fin M) :
      (chainSlab s τ i).passTime b (X.ρ ω) (γ.toFun (t i)) (γ.toFun (t (i + 1))) ≤
        X.passTime ω (γ.toFun (t i)) (γ.toFun (t (i + 1))) + (6 * b * R + 1) := by
    have hh := slabTime_sub_passTime_le X ω hb (chainSlab s τ i) hs (admissible_face₀ hx i)
      (admissible_face₁ hx i) (admissible_slope_le_two hs hx i) hstraight (hγB _ (ht _).1)
      (hγB _ (ht _).1) hR
    change (chainSlab s τ i).passTime b (X.ρ ω) (γ.toFun (t i)) (γ.toFun (t (i + 1))) -
      X.passTime ω (γ.toFun (t i)) (γ.toFun (t (i + 1))) ≤ _ at hh
    linarith only [hh]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpass := ordered_passTime_sum_le_add_one X ω γ.toRectifiable hγ t (fun n => (ht n).1)
    hmono M
  simp only [lip_toRectifiable_apply, ht0, htM, γ.map_zero, γ.map_one] at hpass
  have hF := slabMinimum_le_slabSum X ω b M s τ (fun i => γ.toFun (t i)) hx
  change X.F b M s τ ω ≤
    ∑ i : Fin M, (chainSlab s τ i).passTime b (X.ρ ω) (γ.toFun (t i)) (γ.toFun (t (i + 1))) at hF
  linarith only [hsum, hpass, hF]

/-- **Equation `eq:columns`, both cases**, on one outcome. If `s < R`, the points `ise₁` give
`F ≤ bMs`. -/
theorem chain_bound (X : Setting m) (ω : X.Ω) {b : ℝ} (hb : X.IsUpperBound b)
    (M : ℕ) (hM : 1 ≤ M) {s : ℝ} (hs : 0 < s) (τ : Pt m)
    {B : Set (Pt m)} {R : ℝ} (hstraight : StraightOn X ω B R)
    (hB : ∀ γ : IsotropicVariance.RectifiableCurve (Pt m),
      IsOneOptimal (X.ρ ω) univ τ (τ + ((M : ℝ) * s) • e₁) γ →
        ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ B)
    (hR : 9 ≤ R) :
    X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁) ≤ M * (6 * b * R + 2) := by
  have hb0 := upperBound_nonneg X hb ω
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbR : 0 ≤ b * R := mul_nonneg hb0 (by linarith only [hR])
  have hMbR : 0 ≤ M * (b * R) := mul_nonneg (by linarith only [hM1]) hbR
  by_cases hRs : R ≤ s
  · have hh := chain_comparison_straight X ω hb M hM hs τ hstraight hB hR hRs
    have hexp : (M : ℝ) * (6 * b * R + 2) = M * (6 * b * R + 1) + M := by ring
    linarith only [hh, hexp, hM1]
  · have hh := (chain_comparison_small_width X ω M hs.le τ hb hb0).2
    have hmul : b * M * s ≤ b * M * R :=
      mul_le_mul_of_nonneg_left (not_le.mp hRs).le (mul_nonneg hb0 (by linarith only [hM1]))
    have hexp : (M : ℝ) * (6 * b * R + 2) = 6 * (M * (b * R)) + 2 * M := by ring
    have hexp' : b * M * R = M * (b * R) := by ring
    linarith only [hh, hmul, hexp, hexp', hMbR, hM1]

end IsotropicVariance.Paper.Proofs.SlabComparison
