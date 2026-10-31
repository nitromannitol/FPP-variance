/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.Localization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import IsotropicVariance.Paper.Proofs.Profiles.Scales

/-!
# The upper bound of the proof of Lemma `lem:localization`: the exterior pieces

In the frame `g` of a pair of cubes, with `a = −2C₀n e₁` and `b = (r + 2C₀n) e₁`, the triangle
inequality through `−(n/16) e₁` and `(r + n/16) e₁`, Lemma `lem:tree` at the length `n/16` and
equation `eq:parent` at the length `(2C₀ − 1/16)n` give `T(a, u) ≤ e₁ · (u − a) + O_1(CQ_n)` and
`T(v, b) ≤ e₁ · (b − v) + O_1(CQ_n)`, uniformly in `u` and `v`.

* `end_first_le`, `end_second_le`: the triangle inequality, for one outcome.
* `endTreeFirst`, `endTreeSecond`, `endParentFirst`, `endParentSecond`: the four random variables,
  and their `O_1` bounds.
* `isOs_treePlus_sixteenth`, `isOs_treeMinus_sixteenth`: Lemma `lem:tree` at the length `n/16` over
  the boxes of the proof of equation `eq:boxpenalty`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

universe u

open IsotropicVariance.Paper.Proofs.Profiles (Q_pos)
open IsotropicVariance.Paper.Proofs.Responses (transverseIntegerPoint)
namespace IsotropicVariance.Paper.Proofs.Localization

open Contracts Cited Infra.Os

variable {m : ℕ}

/-! ## The points `−(n/16) e₁` and `(r + n/16) e₁` -/

section Frame

variable (g : Pt m ≃ᵃⁱ[ℝ] Pt m)

/-- The point `−(n/16) e₁` of the upper bound in the proof of Lemma `lem:localization`, in the
frame. -/
noncomputable def nearA (n : ℝ) : Pt m := g ((-(n / 16)) • e₁)

/-- The point `(r + n/16) e₁` of the upper bound in the proof of Lemma `lem:localization`, in the
frame. -/
noncomputable def nearB (n r : ℝ) : Pt m := g ((r + n / 16) • e₁)

lemma nearA_add (n : ℝ) : nearA g n + (n / 16) • frameDir g = g 0 := by
  rw [nearA, frameDir, ← map_smul, ← frame_add, ← add_smul]; simp

lemma nearB_add (n r : ℝ) : nearB g n r + (n / 16) • -frameDir g = g (r • e₁) := by
  rw [nearB, frameDir, smul_neg, ← map_smul, ← map_neg, ← frame_add, ← sub_eq_add_neg,
    ← sub_smul]; ring_nf

lemma dist_anchorA_nearA {n C₀ : ℝ} (hn : 0 ≤ n) (hC₀ : 1 ≤ C₀) :
    dist (anchorA g n C₀) (nearA g n) = (2 * C₀ - 1 / 16) * n := by
  rw [anchorA, nearA, dist_frame, ← sub_smul, norm_smul, norm_e₁, mul_one, Real.norm_eq_abs,
    abs_of_nonpos]
  · ring
  · have := mul_nonneg (by linarith only [hC₀] : 0 ≤ 2 * C₀ - 1 / 16) hn
    linarith only [this]

lemma dist_nearB_anchorB {n r C₀ : ℝ} (hn : 0 ≤ n) (hC₀ : 1 ≤ C₀) :
    dist (nearB g n r) (anchorB g n r C₀) = (2 * C₀ - 1 / 16) * n := by
  rw [nearB, anchorB, dist_frame, ← sub_smul, norm_smul, norm_e₁, mul_one, Real.norm_eq_abs,
    abs_of_nonpos]
  · ring
  · have := mul_nonneg (by linarith only [hC₀] : 0 ≤ 2 * C₀ - 1 / 16) hn
    linarith only [this]

/-- **The bound for `T(a, u)` for one outcome**: the triangle inequality
through `−(n/16) e₁`, with the tree error `Z` at that point and the parent error `P` at the length
`(2C₀ − 1/16)n`. -/
theorem end_first_le (T : Pt m → Pt m → ℝ) (htri : ∀ x y z, T x z ≤ T x y + T y z)
    {n C₀ Cp Qd Z P : ℝ} (hn : 0 ≤ n) (hC₀ : 1 ≤ C₀) {u : Pt m}
    (hZ : T (nearA g n) u - ⟪u - nearA g n, frameDir g⟫ ≤ Z)
    (hP : |T (anchorA g n C₀) (nearA g n) - dist (anchorA g n C₀) (nearA g n)| - Cp * Qd ≤ P) :
    T (anchorA g n C₀) u ≤ Pt.lon (g.symm u) + 2 * C₀ * n + (Z + P + Cp * Qd) := by
  have hin : ⟪u - nearA g n, frameDir g⟫ = Pt.lon (g.symm u) + n / 16 := by
    calc ⟪u - nearA g n, frameDir g⟫ =
          ⟪g (g.symm u) - g ((-(n / 16)) • e₁), frameDir g⟫ := by simp [nearA]
      _ = Pt.lon (g.symm u - (-(n / 16)) • e₁) := inner_frameDir g _ _
      _ = Pt.lon (g.symm u) + n / 16 := by simp
  have hd := dist_anchorA_nearA g hn hC₀
  have h1 := htri (anchorA g n C₀) (nearA g n) u
  have h2 := le_abs_self (T (anchorA g n C₀) (nearA g n) - dist (anchorA g n C₀) (nearA g n))
  rw [hd] at h2 hP
  rw [hin] at hZ
  have e : (2 * C₀ - 1 / 16) * n + n / 16 = 2 * C₀ * n := by ring
  linarith only [h1, h2, hZ, hP, e]

/-- **The bound for `T(v, b)` for one outcome**: the triangle inequality
through `(r + n/16) e₁`. -/
theorem end_second_le (T : Pt m → Pt m → ℝ) (htri : ∀ x y z, T x z ≤ T x y + T y z)
    (hsym : ∀ x y, T x y = T y x) {n r C₀ Cp Qd Z P : ℝ} (hn : 0 ≤ n) (hC₀ : 1 ≤ C₀) {v : Pt m}
    (hZ : T (nearB g n r) v - ⟪v - nearB g n r, -frameDir g⟫ ≤ Z)
    (hP : |T (nearB g n r) (anchorB g n r C₀) - dist (nearB g n r) (anchorB g n r C₀)| -
      Cp * Qd ≤ P) :
    T v (anchorB g n r C₀) ≤ r + 2 * C₀ * n - Pt.lon (g.symm v) + (Z + P + Cp * Qd) := by
  have hin : ⟪v - nearB g n r, -frameDir g⟫ = r + n / 16 - Pt.lon (g.symm v) := by
    calc ⟪v - nearB g n r, -frameDir g⟫ =
          -⟪g (g.symm v) - g ((r + n / 16) • e₁), frameDir g⟫ := by
            simp [nearB, inner_neg_right]
      _ = -Pt.lon (g.symm v - (r + n / 16) • e₁) := by rw [inner_frameDir]
      _ = r + n / 16 - Pt.lon (g.symm v) := by simp
  have hd := dist_nearB_anchorB (r := r) g hn hC₀
  have h1 := htri v (nearB g n r) (anchorB g n r C₀)
  have h2 := le_abs_self (T (nearB g n r) (anchorB g n r C₀) -
    dist (nearB g n r) (anchorB g n r C₀))
  rw [hd] at h2 hP
  rw [hin] at hZ
  rw [hsym v (nearB g n r)] at h1
  have e : (2 * C₀ - 1 / 16) * n + n / 16 = 2 * C₀ * n := by ring
  linarith only [h1, h2, hZ, hP, e]

end Frame

/-! ## The random variables -/

section Variables

variable (X : Setting m) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (n r C₀ : ℝ)

/-- The tree error at `−(n/16) e₁` over `I`. -/
noncomputable def endTreeFirst (I : Set (Pt m)) (ω : X.Ω) : ℝ :=
  ⨆ z : I, (X.passTime ω (nearA g n) z - ⟪(z : Pt m) - nearA g n, frameDir g⟫)

/-- The tree error at `(r + n/16) e₁` over `I'`. -/
noncomputable def endTreeSecond (I' : Set (Pt m)) (ω : X.Ω) : ℝ :=
  ⨆ z : I', (X.passTime ω (nearB g n r) z - ⟪(z : Pt m) - nearB g n r, -frameDir g⟫)

/-- The parent error for `T(a, −(n/16) e₁)`: `|T − ℓ| − C Q_ℓ`, `ℓ = (2C₀ − 1/16)n`. -/
noncomputable def endParentFirst (Cp : ℝ) (K : ℕ) (A : ℝ) (ω : X.Ω) : ℝ :=
  |X.passTime ω (anchorA g n C₀) (nearA g n) - dist (anchorA g n C₀) (nearA g n)| -
    Cp * Q K A (dist (anchorA g n C₀) (nearA g n))

/-- The parent error for `T((r + n/16) e₁, b)`. -/
noncomputable def endParentSecond (Cp : ℝ) (K : ℕ) (A : ℝ) (ω : X.Ω) : ℝ :=
  |X.passTime ω (nearB g n r) (anchorB g n r C₀) - dist (nearB g n r) (anchorB g n r C₀)| -
    Cp * Q K A (dist (nearB g n r) (anchorB g n r C₀))

end Variables

/-! ## Lemma `lem:tree` at the length `n/16` -/

lemma isOs_tree_sixteenth (X : Setting m) {CT : ℝ} {K : ℕ} {A N n : ℝ}
    (hTK : TreeAt X (1 / 2) CT K A N) (hK : 10 ≤ K) (hA : 0 < A) (hn : 256 ≤ n) (hnN : n ≤ N)
    (hCT : 0 < CT) (x e : Pt m) (he : ‖e‖ = 1) {B : Set (Pt m)}
    (hB : IsRectBox B (x + (n / 16) • e)) (hdiam : ∀ z ∈ B, ∀ z' ∈ B, dist z z' ≤ n / 16 / 8)
    (hline : ∀ z ∈ B, infDist z (range fun s : ℝ => x + s • e) ≤ 2 * Real.sqrt m * W K A n) :
    IsOs X.P 1 (CT * Q K A n) (fun ω => ⨆ z : B, (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫)) := by
  have hn0 : 0 ≤ n := by linarith only [hn]
  have h : IsOs X.P 1 (CT * Q K A (n / 16)) _ := hTK (n / 16) (by linarith only [hn])
    (by linarith only [hnN, hn]) x e he B hB hdiam (fun z hz => (hline z hz).trans ?_)
  · exact h.mono_scale zero_le_one (mul_pos hCT (Q_pos hA (by positivity)))
      (mul_le_mul_of_nonneg_left
        (Profiles.Q_mono hK hA.le (by positivity) (by linarith only [hn])) hCT.le)
  · have h8 := W_div_sixteen (K := K) hA.le hn0
    have hW0 := Profiles.W_nonneg K A n
    have hW1 := Profiles.W_nonneg K A (n / 16)
    have hs : Real.sqrt m ≤ Real.sqrt (m + 1) := Real.sqrt_le_sqrt (by linarith only)
    have e1 := mul_le_mul_of_nonneg_right hs hW0
    have e2 := mul_le_mul_of_nonneg_left (by linarith only [h8] : W K A n ≤ 8 * W K A (n / 16))
      (Real.sqrt_nonneg ((m : ℝ) + 1))
    linarith only [e1, e2]

/-- The tree bound at `−(n/16) e₁` over the first cube. -/
lemma isOs_endTreeFirst (X : Setting m) {CT κ : ℝ} {K : ℕ} {A N n : ℝ}
    (hTK : TreeAt X (1 / 2) CT K A N) (hK : 10 ≤ K) (hA : 0 < A) (hn : 256 ≤ n) (hnN : n ≤ N)
    (hCT : 0 < CT) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {p : CubePair m}
    (hp : p.IsAdmissible n (W K A n) κ) (hg0 : g 0 = p.center₁)
    (hε : 2 * Real.sqrt m * W K A n ≤ n / 500) :
    IsOs X.P 1 (CT * Q K A n) (endTreeFirst X g n p.first) := by
  have hfirst := fun z (hz : z ∈ p.first) => CubePairFacts.dist_first_le hp hz
  refine isOs_tree_sixteenth X hTK hK hA hn hnN hCT (nearA g n) (frameDir g) (norm_frameDir g)
    (by rw [nearA_add, hg0]; exact CubePairFacts.isRectBox_first hp) (fun z hz z' hz' => ?_)
    (fun z hz => ?_)
  · have := dist_triangle z p.center₁ z'
    rw [dist_comm p.center₁ z'] at this
    linarith only [this, hfirst z hz, hfirst z' hz', hε, hn]
  · refine (infDist_le_dist_of_mem (mem_range_self (f := fun s : ℝ =>
      nearA g n + s • frameDir g) (n / 16))).trans ?_
    rw [nearA_add, hg0]
    exact hfirst z hz

/-- The tree bound at `(r + n/16) e₁` over the second cube. -/
lemma isOs_endTreeSecond (X : Setting m) {CT κ : ℝ} {K : ℕ} {A N n r : ℝ}
    (hTK : TreeAt X (1 / 2) CT K A N) (hK : 10 ≤ K) (hA : 0 < A) (hn : 256 ≤ n) (hnN : n ≤ N)
    (hCT : 0 < CT) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {p : CubePair m}
    (hp : p.IsAdmissible n (W K A n) κ) (hgr : g (r • e₁) = p.center₂)
    (hε : 2 * Real.sqrt m * W K A n ≤ n / 500) :
    IsOs X.P 1 (CT * Q K A n) (endTreeSecond X g n r p.second) := by
  have hsecond := fun z (hz : z ∈ p.second) => CubePairFacts.dist_second_le hp hz
  refine isOs_tree_sixteenth X hTK hK hA hn hnN hCT (nearB g n r) (-frameDir g)
    (by rw [norm_neg, norm_frameDir])
    (by rw [nearB_add, hgr]; exact CubePairFacts.isRectBox_second hp) (fun z hz z' hz' => ?_)
    (fun z hz => ?_)
  · have := dist_triangle z p.center₂ z'
    rw [dist_comm p.center₂ z'] at this
    linarith only [this, hsecond z hz, hsecond z' hz', hε, hn]
  · refine (infDist_le_dist_of_mem (mem_range_self (f := fun s : ℝ =>
      nearB g n r + s • -frameDir g) (n / 16))).trans ?_
    rw [nearB_add, hgr]
    exact hsecond z hz

/-- Lemma `lem:tree` at the length `n/16` at `x₊`, over a box of the proof of equation
`eq:boxpenalty`. -/
lemma isOs_treePlus_sixteenth (X : Setting m) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {C₀ CT : ℝ} {K : ℕ}
    {A N n : ℝ} (hTK : TreeAt X (1 / 2) CT K A N) (hK : 10 ≤ K) (hA : 0 < A) (hn : 256 ≤ n)
    (hnN : n ≤ N) (hCT : 0 < CT) (hε : 2 * Real.sqrt m * W K A n ≤ n / 500)
    (jk : ℕ × (Fin m → ℤ)) :
    IsOs X.P 1 (CT * Q K A n) (treePlus X g n (W K A n) C₀ jk) := by
  have hn0 : 0 ≤ n := by linarith only [hn]
  have hW0 := Profiles.W_nonneg K A n
  refine isOs_tree_sixteenth X hTK hK hA hn hnN hCT _ (-frameDir g)
    (by rw [norm_neg, norm_frameDir]) (by rw [plusPt_add]; exact isRectBox_box g hn0 hW0 jk)
    (box_diam g hW0 hε jk) (fun z hz => (infDist_line_plus_le g hW0 jk hz).trans ?_)
  have := mul_nonneg (Real.sqrt_nonneg (m : ℝ)) hW0
  linarith only [this]

/-- Lemma `lem:tree` at the length `n/16` at `x₋`, over a box of the proof of equation
`eq:boxpenalty`. -/
lemma isOs_treeMinus_sixteenth (X : Setting m) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {C₀ CT : ℝ} {K : ℕ}
    {A N n : ℝ} (hTK : TreeAt X (1 / 2) CT K A N) (hK : 10 ≤ K) (hA : 0 < A) (hn : 256 ≤ n)
    (hnN : n ≤ N) (hCT : 0 < CT) (hε : 2 * Real.sqrt m * W K A n ≤ n / 500)
    (jk : ℕ × (Fin m → ℤ)) :
    IsOs X.P 1 (CT * Q K A n) (treeMinus X g n (W K A n) C₀ jk) := by
  have hn0 : 0 ≤ n := by linarith only [hn]
  have hW0 := Profiles.W_nonneg K A n
  refine isOs_tree_sixteenth X hTK hK hA hn hnN hCT _ (frameDir g) (norm_frameDir g)
    (by rw [minusPt_add]; exact isRectBox_box g hn0 hW0 jk)
    (box_diam g hW0 hε jk) (fun z hz => (infDist_line_minus_le g hW0 jk hz).trans ?_)
  have := mul_nonneg (Real.sqrt_nonneg (m : ℝ)) hW0
  linarith only [this]

/-! ## Equation `eq:parent` at the length `(2C₀ − 1/16)n` -/

/-- `n ≤ (2C₀ − 1/16)n ≤ L₀ n`. -/
lemma end_length_bounds {n C₀ : ℝ} (hn : 0 ≤ n) (hC₀ : 1 ≤ C₀) :
    n ≤ (2 * C₀ - 1 / 16) * n ∧ (2 * C₀ - 1 / 16) * n ≤ boxL m C₀ * n := by
  have h0 : 0 ≤ Real.sqrt m * (C₀ + 2) := by positivity
  constructor
  · exact le_mul_of_one_le_left hn (by linarith only [hC₀])
  · refine mul_le_mul_of_nonneg_right ?_ hn
    unfold boxL
    linarith only [h0, hC₀]

/-- `Q_d ≤ √L₀ Q_n` for `d ≤ L₀ n`. -/
lemma Q_le_of_le_boxL {K : ℕ} {A n d C₀ : ℝ} (hK : 10 ≤ K) (hA : 0 ≤ A) (hn : 0 ≤ n)
    (hC₀ : 1 ≤ C₀) (hd0 : 0 ≤ d) (hd : d ≤ boxL m C₀ * n) :
    Q K A d ≤ Real.sqrt (boxL m C₀) * Q K A n :=
  (Profiles.Q_mono hK hA hd0 hd).trans (Q_mul_le hA (one_le_boxL (by linarith only [hC₀])) hn)

variable (X : Setting m) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) in
/-- The parent error at the first exterior piece is `O_1(√L₀ Q_n/100)`. -/
lemma isOs_endParentFirst (hm : 1 ≤ m) {C₀ CPar c₁ : ℝ} {K : ℕ} {A N n : ℝ}
    (hPK : ParentAt X c₁ (boxL m C₀) CPar K A N) (hK : 10 ≤ K) (hA : 0 < A) (hC₀ : 1 ≤ C₀)
    (hn : 0 < n) (hc₁n : c₁ * N ≤ n) (hnN : n ≤ N) :
    IsOs X.P 1 (Real.sqrt (boxL m C₀) * Q K A n / 100) (endParentFirst X g n C₀ CPar K A) := by
  obtain ⟨hd1, hd2⟩ := end_length_bounds (m := m) hn.le hC₀
  rw [← dist_anchorA_nearA g hn.le hC₀] at hd1 hd2
  have hL := one_le_boxL (m := m) (by linarith only [hC₀] : (0 : ℝ) ≤ C₀)
  set d := dist (anchorA g n C₀) (nearA g n)
  have hdN := mul_le_mul_of_nonneg_left hnN (by linarith only [hL] : (0 : ℝ) ≤ boxL m C₀)
  have h := hPK d (by linarith only [hc₁n, hd1]) (by linarith only [hd2, hdN])
  have h2 := Profiles.isOs_passTime_of_TRV (X := X) hm (measurable_parentFun d (CPar * Q K A d))
    (anchorA g n C₀) (nearA g n) h
  refine IsOs.mono_scale h2 zero_le_one ?_ ?_
  · have := Q_pos (K := K) hA (by linarith only [hd1, hn] : 0 < d)
    positivity
  · have := Q_le_of_le_boxL hK hA.le hn.le hC₀ (by linarith only [hd1, hn]) hd2
    linarith only [this]

variable (X : Setting m) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) in
/-- The parent error at the second exterior piece is `O_1(√L₀ Q_n/100)`. -/
lemma isOs_endParentSecond (hm : 1 ≤ m) {C₀ CPar c₁ : ℝ} {K : ℕ} {A N n r : ℝ}
    (hPK : ParentAt X c₁ (boxL m C₀) CPar K A N) (hK : 10 ≤ K) (hA : 0 < A) (hC₀ : 1 ≤ C₀)
    (hn : 0 < n) (hc₁n : c₁ * N ≤ n) (hnN : n ≤ N) :
    IsOs X.P 1 (Real.sqrt (boxL m C₀) * Q K A n / 100)
      (endParentSecond X g n r C₀ CPar K A) := by
  obtain ⟨hd1, hd2⟩ := end_length_bounds (m := m) hn.le hC₀
  rw [← dist_nearB_anchorB (r := r) g hn.le hC₀] at hd1 hd2
  have hL := one_le_boxL (m := m) (by linarith only [hC₀] : (0 : ℝ) ≤ C₀)
  set d := dist (nearB g n r) (anchorB g n r C₀)
  have hdN := mul_le_mul_of_nonneg_left hnN (by linarith only [hL] : (0 : ℝ) ≤ boxL m C₀)
  have h := hPK d (by linarith only [hc₁n, hd1]) (by linarith only [hd2, hdN])
  have h2 := Profiles.isOs_passTime_of_TRV (X := X) hm (measurable_parentFun d (CPar * Q K A d))
    (nearB g n r) (anchorB g n r C₀) h
  refine IsOs.mono_scale h2 zero_le_one ?_ ?_
  · have := Q_pos (K := K) hA (by linarith only [hd1, hn] : 0 < d)
    positivity
  · have := Q_le_of_le_boxL hK hA.le hn.le hC₀ (by linarith only [hd1, hn]) hd2
    linarith only [this]

/-! ## The sum rule -/

/-- **The sum rule** for the six `O_1` terms of the proof of Lemma `lem:localization` and their
deterministic parts (equation `eq:sum`). -/
lemma isOs_endSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z₁ P₁ Z₂ P₂ Y G : Ω → ℝ} {θT θP θ₃ θ₄ c : ℝ} (hθT : 0 < θT) (hθP : 0 < θP) (hθ₃ : 0 < θ₃)
    (hθ₄ : 0 < θ₄) (hc : 0 ≤ c) (hZ₁ : IsOs P 1 θT Z₁) (hP₁ : IsOs P 1 θP P₁)
    (hZ₂ : IsOs P 1 θT Z₂) (hP₂ : IsOs P 1 θP P₂) (hY : IsOs P 1 θ₃ Y) (hG : IsOs P 1 θ₄ G) :
    IsOs P 1 (θT + θP + (θT + θP) + θ₃ + θ₄ + (c + 1) / Real.log 2)
      (fun ω => Z₁ ω + P₁ ω + (Z₂ ω + P₂ ω) + Y ω + G ω + c) :=
  Profiles.isOs_add_const (Profiles.isOs_add (Profiles.isOs_add (Profiles.isOs_add
    (Profiles.isOs_add hZ₁ hP₁ hθT hθP) (Profiles.isOs_add hZ₂ hP₂ hθT hθP) (by positivity)
    (by positivity)) hY (by positivity) hθ₃) hG (by positivity) hθ₄) (by positivity) hc

end IsotropicVariance.Paper.Proofs.Localization
