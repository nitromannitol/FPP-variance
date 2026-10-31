/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Tube
import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
public import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# Lemma `lem:fewtranslates`: the translates of a block meeting a tube

The proof of Lemma `lem:fewtranslates`: "The tube `U_i(x_{i−1}, x_i)`
meets at most `C(1 + |x_i − x_{i−1} − ne_1|/(nQ_n)^{1/2} + R_i(x_{i−1}, x_i))` translates of `G` by
multiples of `L(nQ_n)^{1/2}e_2`."

The translates `block(i, z − j L e₀)`, `j ∈ ℕ`, of a block have the first transverse coordinate in
the disjoint intervals `W [z₀ − jL, z₀ − jL + L)`, and the first transverse coordinate of a point of
the tube is within `R W + W |J_{i+1} − J_i|` of that of the center of `I_i(J_i)`. Hence at most
`2 R + 2 |J_{i+1} − J_i| + 2` translates meet the tube (`card_hit_le`).

* `card_filter_le`: at most `w + 1` integers lie in an interval `[x, x + w)`.
* `abs_tr_sub_le_infDist_segment`: a transverse coordinate moves along a segment by at most its
  change between the endpoints.
* `card_not_disjoint_le`: the count for any set whose first transverse coordinates lie in an
  interval.
* `card_hit_le`: the count for the tube of the slab minimum.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

variable {m : ℕ}

/-- **Counting integers in an interval**: at most `w + 1` natural numbers `j < M` lie in
`[x, x + w)`. -/
theorem card_filter_le (M : ℕ) (x w : ℝ) (hw : 0 ≤ w) :
    (((Finset.range M).filter fun j : ℕ => x ≤ j ∧ (j : ℝ) < x + w).card : ℝ) ≤ w + 1 := by
  have hsub : (Finset.range M).filter (fun j : ℕ => x ≤ j ∧ (j : ℝ) < x + w) ⊆
      Finset.Ico ⌈x⌉₊ (⌈x⌉₊ + ⌈w⌉₊) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_Ico]
    refine ⟨Nat.ceil_le.2 hj.2.1, ?_⟩
    have h1 : x ≤ ⌈x⌉₊ := Nat.le_ceil x
    have h2 : w ≤ ⌈w⌉₊ := Nat.le_ceil w
    have h3 : (j : ℝ) < ((⌈x⌉₊ + ⌈w⌉₊ : ℕ) : ℝ) := by
      push_cast
      linarith [hj.2.2]
    exact_mod_cast h3
  calc (((Finset.range M).filter fun j : ℕ => x ≤ j ∧ (j : ℝ) < x + w).card : ℝ)
      ≤ ((Finset.Ico ⌈x⌉₊ (⌈x⌉₊ + ⌈w⌉₊)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (⌈w⌉₊ : ℝ) := by rw [Nat.card_Ico, Nat.add_sub_cancel_left]
    _ ≤ w + 1 := (Nat.ceil_lt_add_one hw).le

/-- A transverse coordinate moves along the segment `[p, q]` by at most its change between the
endpoints: `|y_k − p_k| ≤ dist(y, [p, q]) + |q_k − p_k|`. -/
theorem abs_tr_sub_le_infDist_segment (y p q : Pt m) (k : Fin m) :
    |Pt.tr y k - Pt.tr p k| ≤ infDist y (segment ℝ p q) + |Pt.tr q k - Pt.tr p k| := by
  have hne : (segment ℝ p q).Nonempty := ⟨p, left_mem_segment ℝ p q⟩
  suffices h : |Pt.tr y k - Pt.tr p k| - |Pt.tr q k - Pt.tr p k| ≤ infDist y (segment ℝ p q) by
    linarith
  refine (le_infDist hne).2 fun s hs => ?_
  obtain ⟨a, c, ha, hc, hac, rfl⟩ := hs
  have e1 : Pt.tr (a • p + c • q) k = a * Pt.tr p k + c * Pt.tr q k := rfl
  have e2 : Pt.tr y k - Pt.tr (a • p + c • q) k = Pt.tr (y - (a • p + c • q)) k := rfl
  have h1 : |Pt.tr y k - Pt.tr (a • p + c • q) k| ≤ dist y (a • p + c • q) := by
    rw [e2, dist_eq_norm]
    exact Profiles.abs_tr_apply_le_norm _ k
  have h2 : |Pt.tr (a • p + c • q) k - Pt.tr p k| ≤ |Pt.tr q k - Pt.tr p k| := by
    rw [e1]
    have : a * Pt.tr p k + c * Pt.tr q k - Pt.tr p k = c * (Pt.tr q k - Pt.tr p k) := by
      rw [show a = 1 - c by linarith]
      ring
    rw [this, abs_mul, abs_of_nonneg hc]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
  have h3 := abs_sub_le (Pt.tr y k) (Pt.tr (a • p + c • q) k) (Pt.tr p k)
  linarith

open Classical in
/-- **The translates meeting a set**: if the first transverse coordinates of the points of `S` are
within `r` of `P`, then at most `2 r / W + 2` of the translates `block(i, z − j L e₀)`, `j < M`,
meet `S`. -/
theorem card_not_disjoint_le (hm : 1 ≤ m) {n W : ℝ} (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L)
    (i : ℕ) (z : Fin m → ℤ) (M : ℕ) {S : Set (Pt m)} {P r : ℝ} (hr : 0 ≤ r)
    (hS : ∀ y ∈ S, |Pt.tr y ⟨0, hm⟩ - P| ≤ r) :
    (((Finset.range M).filter fun j =>
        ¬ Disjoint (block n W L i (z - blockShift hm j L)) S).card : ℝ) ≤ 2 * r / W + 2 := by
  set k₀ : Fin m := ⟨0, hm⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLW : 0 < (L : ℝ) * W := by positivity
  set x : ℝ := (W * z k₀ - P - r) / ((L : ℝ) * W)
  set w : ℝ := 2 * r / ((L : ℝ) * W) + 1
  have hw : 0 ≤ w := by positivity
  have hsub : (Finset.range M).filter (fun j =>
      ¬ Disjoint (block n W L i (z - blockShift hm j L)) S) ⊆
        (Finset.range M).filter fun j : ℕ => x ≤ j ∧ (j : ℝ) < x + w := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    obtain ⟨y, hyG, hyS⟩ := Set.not_disjoint_iff.1 hj.2
    have hy := hyG.2.2 k₀
    have hz : (((z - blockShift hm j L) k₀ : ℤ) : ℝ) = z k₀ - j * L := by
      rw [Pi.sub_apply, Int.cast_sub, blockShift_apply_real]
      simp [k₀]
    rw [hz] at hy
    have hP := abs_le.1 (hS y hyS)
    constructor
    · rw [div_le_iff₀ hLW]
      nlinarith [hy.1, hP.2]
    · have e : x + w = (W * z k₀ - P + r + L * W) / ((L : ℝ) * W) := by
        simp only [x, w]
        field_simp
        ring
      rw [e, lt_div_iff₀ hLW]
      nlinarith [hy.2, hP.1]
  calc (((Finset.range M).filter fun j =>
        ¬ Disjoint (block n W L i (z - blockShift hm j L)) S).card : ℝ)
      ≤ (((Finset.range M).filter fun j : ℕ => x ≤ j ∧ (j : ℝ) < x + w).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ w + 1 := card_filter_le M x w hw
    _ ≤ 2 * r / W + 2 := by
        have : 2 * r / ((L : ℝ) * W) ≤ 2 * r / W := by
          apply div_le_div_of_nonneg_left (by positivity) hW
          nlinarith
        simp only [w]
        linarith

open Classical in
/-- **The translates of a block meeting the tube** (the proof of Lemma `lem:fewtranslates`):
at most `2 R_i(J_i, J_{i+1}) + 2 |J_{i+1} − J_i| + 2` of the translates `block(i, z − j L e₀)`,
`j < M`, meet the tube of `F` in the slab `i`. -/
theorem card_hit_le (X : Setting.{u} m) (hm : 1 ≤ m) (b : ℝ) {K : ℕ} {n W : ℝ} (hW : 0 < W)
    {L : ℕ} (hL : 1 ≤ L) (c : X.Ω) (i : Fin K) (z : Fin m → ℤ) (M : ℕ) :
    (((Finset.range M).filter fun j =>
        ¬ Disjoint (block n W L i (z - blockShift hm j L)) (tube X b K n W c i)).card : ℝ) ≤
      2 * X.R b n W c i (X.J b K n W 0 c i.castSucc) (X.J b K n W 0 c i.succ) +
        2 * zNorm (X.J b K n W 0 c i.succ - X.J b K n W 0 c i.castSucc) + 2 := by
  set J₁ := X.J b K n W 0 c i.castSucc
  set J₂ := X.J b K n W 0 c i.succ
  set R := X.R b n W c i J₁ J₂
  set p := gridCubeCenter n W 0 (i : ℕ) J₁
  set q := gridCubeCenter n W 0 ((i : ℕ) + 1) J₂
  set k₀ : Fin m := ⟨0, hm⟩
  have hR0 : 0 ≤ R := R_nonneg X b n hW.le c i J₁ J₂
  have hz0 : 0 ≤ zNorm (J₂ - J₁) := Real.sqrt_nonneg _
  have hpq : |Pt.tr q k₀ - Pt.tr p k₀| ≤ W * zNorm (J₂ - J₁) := by
    have e : Pt.tr q k₀ - Pt.tr p k₀ = W * (((J₂ - J₁) k₀ : ℤ) : ℝ) := by
      simp only [p, q, gridCubeCenter, zero_add, Pt.tr_mk, PiLp.toLp_apply, Pi.sub_apply,
        Int.cast_sub]
      ring
    rw [e, abs_mul, abs_of_pos hW]
    exact mul_le_mul_of_nonneg_left (SmallMean.abs_le_zNorm _ _) hW.le
  have hS : ∀ y ∈ tube X b K n W c i, |Pt.tr y k₀ - Pt.tr p k₀| ≤ R * W + W * zNorm (J₂ - J₁) :=
    fun y hy => (abs_tr_sub_le_infDist_segment y p q k₀).trans (add_le_add hy hpq)
  refine (card_not_disjoint_le hm hW hL i z M (by positivity) hS).trans (le_of_eq ?_)
  field_simp

end IsotropicVariance.Paper.Proofs.Gain
