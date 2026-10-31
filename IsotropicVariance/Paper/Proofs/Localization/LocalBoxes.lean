/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.LocalCore
public import IsotropicVariance.Paper.Proofs.Localization.Os
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
import IsotropicVariance.Paper.Proofs.Profiles.Scales

/-!
# The proof of Lemma `lem:localization`: the boxes and the penalty for one outcome

The boxes `[t_j ± n/1000] × W(k + [−1, 1]^{d−1})`, finitely many `t_j` and the `k` with
`|k_i| ≤ C₀n/W + 2`, cover the region `|t| ≤ C₀n`, `|y| ≤ C₀n`. For each box the tree bounds at
`x_±` and the parent bounds for `T(a, x₊)`, `T(x₋, b)` are random variables; the penalty
`G = max_{boxes} (U_{jk} − Q_n|k|²/(2L₀))` gives equation `eq:boxpenalty` for every point of the
region and every outcome.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

open IsotropicVariance.Paper.Proofs.Profiles (Q_nonneg abs_lon_le_norm)
open IsotropicVariance.Paper.Proofs.Responses (transverseIntegerPoint)
namespace IsotropicVariance.Paper.Proofs.Localization

variable {m : ℕ}

lemma abs_apply_le_norm (y : EuclideanSpace ℝ (Fin m)) (i : Fin m) : |y i| ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, show |y i| = Real.sqrt (‖y i‖ ^ 2) by
    rw [Real.norm_eq_abs, Real.sqrt_sq (abs_nonneg _)]]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- The number of longitudinal positions of the boxes, less one. -/
noncomputable def boxCountLon (C₀ : ℝ) : ℕ := ⌈1000 * C₀⌉₊ + 1

/-- The range of the transverse indices of the boxes. -/
noncomputable def boxRange (n W C₀ : ℝ) : ℕ := ⌈C₀ * n / W⌉₊ + 1

/-- The indices `(j, k)` of the boxes. -/
noncomputable def boxIndex (m : ℕ) (n W C₀ : ℝ) : Finset (ℕ × (Fin m → ℤ)) :=
  Finset.range (boxCountLon C₀ + 1) ×ˢ
    Fintype.piFinset fun _ => Finset.Icc (-(boxRange n W C₀ : ℤ)) (boxRange n W C₀)

lemma boxIndex_nonempty (n W C₀ : ℝ) : (boxIndex m n W C₀).Nonempty :=
  ⟨(0, 0), Finset.mem_product.2 ⟨by simp, Fintype.mem_piFinset.2 fun _ => by simp⟩⟩

lemma boxLon_ge {n C₀ : ℝ} (hn : 0 < n) (j : ℕ) : -(C₀ * n) ≤ boxLon n C₀ j := by
  unfold boxLon; have : (0 : ℝ) ≤ j * (n / 500) := by positivity
  linarith only [this]

lemma boxLon_le {n C₀ : ℝ} (hn : 0 < n) (hC₀ : 0 ≤ C₀) {j : ℕ} (hj : j < boxCountLon C₀ + 1) :
    boxLon n C₀ j ≤ C₀ * n + n / 250 := by
  unfold boxLon boxCountLon at *
  have h1 : (j : ℝ) ≤ ⌈1000 * C₀⌉₊ + 1 := by exact_mod_cast Nat.lt_succ_iff.1 hj
  have h2 : (⌈1000 * C₀⌉₊ : ℝ) < 1000 * C₀ + 1 := Nat.ceil_lt_add_one (by positivity)
  have : (j : ℝ) * (n / 500) ≤ (1000 * C₀ + 2) * (n / 500) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith only [this]

lemma norm_kvec_le {n W C₀ : ℝ} {k : Fin m → ℤ}
    (hk : k ∈ Fintype.piFinset fun _ => Finset.Icc (-(boxRange n W C₀ : ℤ)) (boxRange n W C₀)) :
    ‖transverseIntegerPoint k‖ ≤ Real.sqrt m * boxRange n W C₀ := by
  refine Profiles.norm_le_of_abs_le (by positivity) fun i => ?_
  have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hk i)
  simp only [transverseIntegerPoint]
  rw [abs_le]
  constructor
  · have : (-(boxRange n W C₀ : ℤ) : ℝ) ≤ (k i : ℝ) := by exact_mod_cast this.1
    simpa using this
  · exact_mod_cast this.2

/-- **The boxes cover the region** `|t| ≤ C₀n`, `|y| ≤ C₀n`. -/
lemma exists_mem_boxSet {n W C₀ : ℝ} (hn : 0 < n) (hW : 0 < W) {ζ : Pt m}
    (hlon : |Pt.lon ζ| ≤ C₀ * n) (htr : ‖Pt.tr ζ‖ ≤ C₀ * n) :
    ∃ jk ∈ boxIndex m n W C₀, ζ ∈ boxSet n W C₀ jk.1 jk.2 := by
  set s := (Pt.lon ζ + C₀ * n) / (n / 500)
  have hs0 : 0 ≤ s := div_nonneg (by linarith only [(abs_le.1 hlon).1]) (by positivity)
  have hs1 : s ≤ 1000 * C₀ := by
    rw [div_le_iff₀ (by positivity)]; linarith only [(abs_le.1 hlon).2]
  set j := ⌊s + 1 / 2⌋₊
  have hj1 : (j : ℝ) ≤ s + 1 / 2 := Nat.floor_le (by linarith only [hs0])
  have hj2 : s + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  set k : Fin m → ℤ := fun i => ⌊Pt.tr ζ i / W + 1 / 2⌋
  have hk1 : ∀ i, (k i : ℝ) ≤ Pt.tr ζ i / W + 1 / 2 := fun i => Int.floor_le _
  have hk2 : ∀ i, Pt.tr ζ i / W + 1 / 2 < k i + 1 := fun i => Int.lt_floor_add_one _
  have htri : ∀ i, |Pt.tr ζ i| ≤ C₀ * n := fun i => (abs_apply_le_norm _ i).trans htr
  refine ⟨(j, k), Finset.mem_product.2 ⟨?_, Fintype.mem_piFinset.2 fun i => ?_⟩, ?_, fun i => ?_⟩
  · rw [Finset.mem_range]
    have : (j : ℝ) < ⌈1000 * C₀⌉₊ + 2 := by
      have := Nat.le_ceil (1000 * C₀); linarith only [this, hj1, hs1]
    unfold boxCountLon; exact_mod_cast this
  · rw [Finset.mem_Icc]
    have hb : C₀ * n / W ≤ ⌈C₀ * n / W⌉₊ := Nat.le_ceil _
    have h1 := (abs_le.1 (htri i))
    have hd1 : Pt.tr ζ i / W ≤ C₀ * n / W := div_le_div_of_nonneg_right h1.2 hW.le
    have hd2 : -(C₀ * n / W) ≤ Pt.tr ζ i / W := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right h1.1 hW.le
    unfold boxRange
    constructor
    · have : -((⌈C₀ * n / W⌉₊ : ℝ) + 1) ≤ k i := by linarith only [hk2 i, hd2, hb]
      exact_mod_cast this
    · have : (k i : ℝ) ≤ ⌈C₀ * n / W⌉₊ + 1 := by linarith only [hk1 i, hd1, hb]
      exact_mod_cast this
  · -- the longitudinal coordinate
    unfold boxLon
    have hlon' : Pt.lon ζ = -(C₀ * n) + s * (n / 500) := by
      simp only [s]; field_simp; ring
    have hn5 : 0 ≤ n / 500 := by positivity
    have e1 := mul_le_mul_of_nonneg_right (show (j : ℝ) - s ≤ 1 / 2 by linarith only [hj1]) hn5
    have e2 := mul_le_mul_of_nonneg_right (show s - j ≤ 1 / 2 by linarith only [hj2]) hn5
    rw [hlon', abs_le]
    constructor <;> linarith only [e1, e2]
  · -- the transverse coordinates
    have h1 := hk1 i
    have h2 := hk2 i
    have e : Pt.tr ζ i = W * (Pt.tr ζ i / W) := by field_simp
    have e1 := mul_le_mul_of_nonneg_left
      (show (k i : ℝ) - Pt.tr ζ i / W ≤ 1 / 2 by linarith only [h1]) hW.le
    have e2 := mul_le_mul_of_nonneg_left
      (show Pt.tr ζ i / W - k i ≤ 1 / 2 by linarith only [h2]) hW.le
    rw [abs_le]
    constructor <;> linarith only [e, e1, e2, hW]

/-! ## The random variables of a box -/

section Variables

variable (X : Setting m) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (n r W C₀ : ℝ)

/-- The tree error at `x₊` over the box: `sup_z (T(x₊, z) − (z − x₊)·(−e))`. -/
noncomputable def treePlus (jk : ℕ × (Fin m → ℤ)) (ω : X.Ω) : ℝ :=
  ⨆ z : g '' boxSet n W C₀ jk.1 jk.2, (X.passTime ω (plusPt g n W C₀ jk.1 jk.2) z -
    ⟪(z : Pt m) - plusPt g n W C₀ jk.1 jk.2, -frameDir g⟫)

/-- The tree error at `x₋` over the box: `sup_z (T(x₋, z) − (z − x₋)·e)`. -/
noncomputable def treeMinus (jk : ℕ × (Fin m → ℤ)) (ω : X.Ω) : ℝ :=
  ⨆ z : g '' boxSet n W C₀ jk.1 jk.2, (X.passTime ω (minusPt g n W C₀ jk.1 jk.2) z -
    ⟪(z : Pt m) - minusPt g n W C₀ jk.1 jk.2, frameDir g⟫)

/-- The parent error for `T(a, x₊)`: `|T(a, x₊) − ℓ| − C Q_ℓ`, `ℓ = |x₊ − a|`. -/
noncomputable def parentPlus (Cp : ℝ) (K : ℕ) (A : ℝ) (jk : ℕ × (Fin m → ℤ)) (ω : X.Ω) : ℝ :=
  |X.passTime ω (anchorA g n C₀) (plusPt g n W C₀ jk.1 jk.2) -
      dist (anchorA g n C₀) (plusPt g n W C₀ jk.1 jk.2)| -
    Cp * Q K A (dist (anchorA g n C₀) (plusPt g n W C₀ jk.1 jk.2))

/-- The parent error for `T(x₋, b)`. -/
noncomputable def parentMinus (Cp : ℝ) (K : ℕ) (A : ℝ) (jk : ℕ × (Fin m → ℤ)) (ω : X.Ω) : ℝ :=
  |X.passTime ω (minusPt g n W C₀ jk.1 jk.2) (anchorB g n r C₀) -
      dist (minusPt g n W C₀ jk.1 jk.2) (anchorB g n r C₀)| -
    Cp * Q K A (dist (minusPt g n W C₀ jk.1 jk.2) (anchorB g n r C₀))

/-- The total error `U_{jk}` of a box. -/
noncomputable def boxError (Cp : ℝ) (K : ℕ) (A : ℝ) (jk : ℕ × (Fin m → ℤ)) (ω : X.Ω) : ℝ :=
  treePlus X g n W C₀ jk ω + treeMinus X g n W C₀ jk ω + parentPlus X g n W C₀ Cp K A jk ω +
    parentMinus X g n r W C₀ Cp K A jk ω

/-- The penalty `G = max_{jk} (U_{jk} − Q_n|k|²/(2L₀))` of equation `eq:boxpenalty`. -/
noncomputable def boxPenalty (Cp : ℝ) (K : ℕ) (A L₀ : ℝ) : X.Ω → ℝ :=
  (boxIndex m n W C₀).sup' (boxIndex_nonempty n W C₀) fun jk ω =>
    boxError X g n r W C₀ Cp K A jk ω - Q K A n * ‖transverseIntegerPoint jk.2‖ ^ 2 / (2 * L₀)

end Variables

/-- Suprema of `T(x, z) − (z − x)·e` over a bounded set are bounded. -/
lemma bddAbove_tree (X : Setting m) {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (hB0 : 0 ≤ B) (ω : X.Ω)
    (x e : Pt m) (he : ‖e‖ = 1) {Z : Set (Pt m)} {c : Pt m} {R : ℝ}
    (hZ : ∀ z ∈ Z, dist z c ≤ R) :
    BddAbove (range fun z : Z => X.passTime ω x z - ⟪(z : Pt m) - x, e⟫) := by
  refine ⟨(B + 1) * (dist x c + R), ?_⟩
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  have h1 := Profiles.passTime_le_mul_dist hB hB0 ω x z
  have h2 : -⟪z - x, e⟫ ≤ ‖z - x‖ := by
    have := abs_real_inner_le_norm (z - x) e
    rw [he, mul_one] at this
    linarith [neg_abs_le ⟪z - x, e⟫]
  have h3 : dist x z ≤ dist x c + R := by
    have := dist_triangle x c z; rw [dist_comm c z] at this; linarith [hZ z hz]
  rw [← dist_eq_norm, dist_comm] at h2
  simp only
  have h4 := mul_le_mul_of_nonneg_left h3 hB0
  linarith only [h1, h2, h3, h4]

/-- The bound `L₀` with `n ≤ |x₊ − a|, |b − x₋| ≤ L₀ n`. -/
noncomputable def boxL (m : ℕ) (C₀ : ℝ) : ℝ := 3 * C₀ + 4 + Real.sqrt m * (C₀ + 2)

lemma one_le_boxL {C₀ : ℝ} (hC₀ : 0 ≤ C₀) : 1 ≤ boxL m C₀ := by
  unfold boxL; have : 0 ≤ Real.sqrt m * (C₀ + 2) := by positivity
  linarith

lemma boxCtr_mem {n : ℝ} (hn : 0 ≤ n) (W C₀ : ℝ) (hW : 0 ≤ W) (jk : ℕ × (Fin m → ℤ)) :
    boxCtr n W C₀ jk.1 jk.2 ∈ boxSet n W C₀ jk.1 jk.2 := by
  refine ⟨by simp [boxCtr]; positivity, fun i => ?_⟩
  simp [boxCtr, transverseIntegerPoint, hW]

/-- The distances `|x₊ − a|`, `|b − x₋|` of the boxes are between `n` and `L₀ n`. -/
lemma dist_box_bounds (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n r W C₀ : ℝ} (hn : 0 < n) (hW : 0 < W)
    (hWn : W ≤ n) (hC₀ : 1 ≤ C₀) (hr0 : 0 ≤ r) (hr2 : r ≤ 2 * n) {jk : ℕ × (Fin m → ℤ)}
    (hjk : jk ∈ boxIndex m n W C₀) :
    (n ≤ dist (anchorA g n C₀) (plusPt g n W C₀ jk.1 jk.2) ∧
      dist (anchorA g n C₀) (plusPt g n W C₀ jk.1 jk.2) ≤ boxL m C₀ * n) ∧
    (n ≤ dist (minusPt g n W C₀ jk.1 jk.2) (anchorB g n r C₀) ∧
      dist (minusPt g n W C₀ jk.1 jk.2) (anchorB g n r C₀) ≤ boxL m C₀ * n) := by
  obtain ⟨hj, hk⟩ := Finset.mem_product.1 hjk
  have hj' : jk.1 < boxCountLon C₀ + 1 := Finset.mem_range.1 hj
  have hl1 := boxLon_ge (C₀ := C₀) hn jk.1
  have hl2 := boxLon_le hn (by linarith) hj'
  have hkn := norm_kvec_le hk
  have hrange : W * boxRange n W C₀ ≤ (C₀ + 2) * n := by
    unfold boxRange
    have h1 : (⌈C₀ * n / W⌉₊ : ℝ) < C₀ * n / W + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : W * (C₀ * n / W) = C₀ * n := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1.le hW.le
    push_cast
    linarith only [h2, h3, hWn]
  have hWk : W * ‖transverseIntegerPoint jk.2‖ ≤ Real.sqrt m * (C₀ + 2) * n := by
    have := mul_le_mul_of_nonneg_left hkn hW.le
    have h2 := mul_le_mul_of_nonneg_left hrange (Real.sqrt_nonneg m)
    linarith only [this, h2]
  have hC₀n : n ≤ C₀ * n := le_mul_of_one_le_left hn.le hC₀
  set c := boxCtr n W C₀ jk.1 jk.2
  have hlonc : Pt.lon c = boxLon n C₀ jk.1 := rfl
  have htrc : Pt.tr c = W • transverseIntegerPoint jk.2 := rfl
  constructor
  · have hd : dist (anchorA g n C₀) (plusPt g n W C₀ jk.1 jk.2) =
        ‖(c + (n / 16) • e₁) - (-(2 * C₀ * n)) • e₁‖ := by
      rw [anchorA, plusPt, dist_frame, norm_sub_rev]
    have hlon : Pt.lon ((c + (n / 16) • e₁) - (-(2 * C₀ * n)) • e₁) =
        boxLon n C₀ jk.1 + n / 16 + 2 * C₀ * n := by simp [hlonc]
    have htr : ‖Pt.tr ((c + (n / 16) • e₁) - (-(2 * C₀ * n)) • e₁)‖ =
        W * ‖transverseIntegerPoint jk.2‖ := by
      simp [htrc, norm_smul, hW.le]
    rw [hd]
    constructor
    · have := (le_abs_self _).trans (abs_lon_le_norm ((c + (n / 16) • e₁) -
        (-(2 * C₀ * n)) • e₁))
      rw [hlon] at this; linarith only [this, hl1, hC₀n, hn]
    · have := Pt.lon_tr_norm_le ((c + (n / 16) • e₁) - (-(2 * C₀ * n)) • e₁)
      rw [hlon, htr, abs_of_pos (by linarith only [hl1, hC₀n, hn])] at this
      unfold boxL; linarith only [this, hl2, hWk, hn]
  · have hd : dist (minusPt g n W C₀ jk.1 jk.2) (anchorB g n r C₀) =
        ‖(r + 2 * C₀ * n) • e₁ - (c - (n / 16) • e₁)‖ := by
      rw [anchorB, minusPt, dist_frame, norm_sub_rev]
    have hlon : Pt.lon ((r + 2 * C₀ * n) • e₁ - (c - (n / 16) • e₁)) =
        r + 2 * C₀ * n - boxLon n C₀ jk.1 + n / 16 := by simp [hlonc]; ring
    have htr : ‖Pt.tr ((r + 2 * C₀ * n) • e₁ - (c - (n / 16) • e₁))‖ =
        W * ‖transverseIntegerPoint jk.2‖ := by
      simp [htrc, norm_smul, hW.le]
    rw [hd]
    constructor
    · have := (le_abs_self _).trans (abs_lon_le_norm ((r + 2 * C₀ * n) • e₁ -
        (c - (n / 16) • e₁)))
      rw [hlon] at this; linarith only [this, hl2, hC₀n, hr0, hn]
    · have := Pt.lon_tr_norm_le ((r + 2 * C₀ * n) • e₁ - (c - (n / 16) • e₁))
      rw [hlon, htr, abs_of_pos (by linarith only [hl2, hC₀n, hr0, hn])] at this
      unfold boxL; linarith only [this, hl1, hr2, hWk, hn]

/-- **Equation `eq:boxpenalty` for one outcome** (the proof of Lemma `lem:localization`): every
point `g ζ` of the region has `c'|y|²/n ≤ T(a, z) + T(z, b) − |b − a| + G + C Q_n`, with `c' =
1/(4L₀)`. -/
theorem penalty_bound (X : Setting m) {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (hB0 : 0 ≤ B)
    (ω : X.Ω) (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n r W C₀ Cp : ℝ} {K : ℕ} {A : ℝ} (hn : 0 < n)
    (hW : 0 < W) (hWn : W ≤ n) (hC₀ : 1 ≤ C₀) (hr0 : 0 ≤ r) (hr2 : r ≤ 2 * n) (hK : 10 ≤ K)
    (hA : 0 ≤ A) (hWQ : W ^ 2 = n * Q K A n) (hCp : 0 ≤ Cp) {ζ : Pt m}
    (hlon : |Pt.lon ζ| ≤ C₀ * n) (htr : ‖Pt.tr ζ‖ ≤ C₀ * n) :
    1 / (4 * boxL m C₀) * ‖Pt.tr ζ‖ ^ 2 / n ≤
      X.passTime ω (anchorA g n C₀) (g ζ) + X.passTime ω (g ζ) (anchorB g n r C₀) -
        (r + 4 * C₀ * n) + (boxPenalty X g n r W C₀ Cp K A (boxL m C₀) ω +
          2 * Cp * Real.sqrt (boxL m C₀) * Q K A n + m * Q K A n / (2 * boxL m C₀)) := by
  set L₀ := boxL m C₀
  have hL₀ : 1 ≤ L₀ := one_le_boxL (by linarith)
  obtain ⟨jk, hjk, hζ⟩ := exists_mem_boxSet hn hW hlon htr
  obtain ⟨⟨hdp1, hdp2⟩, ⟨hdm1, hdm2⟩⟩ := dist_box_bounds g hn hW hWn hC₀ hr0 hr2 hjk
  have hj' : jk.1 < boxCountLon C₀ + 1 := Finset.mem_range.1 (Finset.mem_product.1 hjk).1
  have hl1 := boxLon_ge (C₀ := C₀) hn jk.1
  have hl2 := boxLon_le hn (by linarith) hj'
  set dp := dist (anchorA g n C₀) (plusPt g n W C₀ jk.1 jk.2)
  set dm := dist (minusPt g n W C₀ jk.1 jk.2) (anchorB g n r C₀)
  set Qn := Q K A n
  set k2 := ‖transverseIntegerPoint jk.2‖ ^ 2
  have hC₀n : 0 < C₀ * n := mul_pos (by linarith) hn
  -- the box variables bound the box
  have hR : ∀ z ∈ g '' boxSet n W C₀ jk.1 jk.2,
      dist z (g (boxCtr n W C₀ jk.1 jk.2)) ≤ n / 500 + 2 * Real.sqrt m * W := by
    rintro _ ⟨ζ', hζ', rfl⟩
    exact mem_boxSet_dist_le hW.le hζ' (boxCtr_mem hn.le W C₀ hW.le jk)
  have hZp : ∀ ζ' ∈ boxSet n W C₀ jk.1 jk.2, X.passTime ω (plusPt g n W C₀ jk.1 jk.2) (g ζ') -
      ⟪g ζ' - plusPt g n W C₀ jk.1 jk.2, -frameDir g⟫ ≤ treePlus X g n W C₀ jk ω := by
    intro ζ' hζ'
    refine le_ciSup (f := fun z : g '' boxSet n W C₀ jk.1 jk.2 =>
      X.passTime ω (plusPt g n W C₀ jk.1 jk.2) z -
        ⟪(z : Pt m) - plusPt g n W C₀ jk.1 jk.2, -frameDir g⟫) ?_ ⟨g ζ', mem_image_of_mem g hζ'⟩
    exact bddAbove_tree X hB hB0 ω _ _ (by rw [norm_neg, norm_frameDir]) hR
  have hZm : ∀ ζ' ∈ boxSet n W C₀ jk.1 jk.2, X.passTime ω (minusPt g n W C₀ jk.1 jk.2) (g ζ') -
      ⟪g ζ' - minusPt g n W C₀ jk.1 jk.2, frameDir g⟫ ≤ treeMinus X g n W C₀ jk ω := by
    intro ζ' hζ'
    refine le_ciSup (f := fun z : g '' boxSet n W C₀ jk.1 jk.2 =>
      X.passTime ω (minusPt g n W C₀ jk.1 jk.2) z -
        ⟪(z : Pt m) - minusPt g n W C₀ jk.1 jk.2, frameDir g⟫) ?_ ⟨g ζ', mem_image_of_mem g hζ'⟩
    exact bddAbove_tree X hB hB0 ω _ _ (norm_frameDir g) hR
  have hstep := step2_box (g := g) (X.passTime ω) (fun x y z => Profiles.passTime_triangle hB ω x y z)
    (fun x y => Profiles.passTime_comm ω x y) (r := r) (Cp := Cp) (Qp := Q K A dp)
    (Qm := Q K A dm) (Pp := parentPlus X g n W C₀ Cp K A jk ω)
    (Pm := parentMinus X g n r W C₀ Cp K A jk ω) (by linarith only [hl1, hC₀n, hn])
    (by linarith only [hl2, hC₀n, hn, hr0]) hZp hZm le_rfl
    le_rfl hζ
  -- the curvature gains
  have hdp0 : 0 < dp := by linarith
  have hdm0 : 0 < dm := by linarith
  have hk0 : 0 ≤ W ^ 2 * k2 := by positivity
  have hgain : ∀ d : ℝ, 0 < d → d ≤ L₀ * n → Qn * k2 / (2 * L₀) ≤ W ^ 2 * k2 / (2 * d) := by
    intro d hd hdL
    rw [hWQ, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ Qn * k2 := mul_nonneg (Q_nonneg hA hn.le) (sq_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hdL this
    linarith only [h1]
  have g1 := hgain dp hdp0 hdp2
  have g2 := hgain dm hdm0 hdm2
  -- the parent scales
  have hQL : ∀ d : ℝ, 0 ≤ d → d ≤ L₀ * n → Q K A d ≤ Real.sqrt L₀ * Qn := fun d hd hdL =>
    (Profiles.Q_mono hK hA hd hdL).trans (Q_mul_le hA hL₀ hn.le)
  have hQp := hQL dp hdp0.le hdp2
  have hQm := hQL dm hdm0.le hdm2
  have hCQ : Cp * (Q K A dp + Q K A dm) ≤ 2 * Cp * Real.sqrt L₀ * Qn := by
    have := mul_le_mul_of_nonneg_left (add_le_add hQp hQm) hCp
    linarith only [this]
  -- the penalty dominates the box
  have hG : boxError X g n r W C₀ Cp K A jk ω - Qn * k2 / (2 * L₀) ≤
      boxPenalty X g n r W C₀ Cp K A L₀ ω := by
    rw [boxPenalty, Finset.sup'_apply]
    exact Finset.le_sup' (fun jk => boxError X g n r W C₀ Cp K A jk ω -
      Q K A n * ‖transverseIntegerPoint jk.2‖ ^ 2 / (2 * L₀)) hjk
  -- the transverse coordinate of the point
  have htr2 := norm_tr_sq_le hW.le hζ
  have hc : 1 / (4 * L₀) * ‖Pt.tr ζ‖ ^ 2 / n ≤ Qn * k2 / (2 * L₀) + m * Qn / (2 * L₀) := by
    rw [div_le_iff₀ hn]
    have e1 : (Qn * k2 / (2 * L₀) + m * Qn / (2 * L₀)) * n =
        (W ^ 2 * k2 + m * W ^ 2) / (2 * L₀) := by rw [hWQ]; field_simp
    rw [e1, one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right htr2 (by positivity : (0 : ℝ) ≤ 2 * L₀)
    linarith only [this]
  unfold boxError at hG
  linarith only [hstep, g1, g2, hCQ, hG, hc]

end IsotropicVariance.Paper.Proofs.Localization
