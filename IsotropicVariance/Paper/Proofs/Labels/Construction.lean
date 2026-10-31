/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Labels.Grid
public import IsotropicVariance.Paper.Proofs.Labels.Discretize

/-!
# The labels of Lemma `lem:labels`

Steps 2 and 3 of the proof. For a block `G = (i, z)`:

* `psiCode`: `Ψ_G`. For each pair of indices of the rounded points, the level of
  `(T_G(u_κ, v_κ) − n)/Q_n`, clipped to `[−M, M]` and rounded down to the mesh `κ`
  (`Labels.quantize`). The paper's `M` is `L⁴`, and for `κ = 1/(j + 1)` the levels `−M + rκ` are
  the multiples of `κ` of the paper (`dequantize_quantize_eq`). `T_G` enters through versions
  `V i z`, measurable for the information of `G`.
* `lambdaCode`: `X_G`, which is `Ψ_G` with each value of probability less than `θ` replaced by a
  value of largest probability (`Labels.mergeRare`), by one rule in every block.
* `tgFamily`: the family of labels, whose values are the functions of the endpoints relative to the
  corner of the block.

The family is determined by the noise in its blocks (`tgFamily_isDetermined`), has bounded values
(`tgFamily_hasBoundedValues`), and each value has probability `0` or at least `θ`
(`tgFamily_atomsGe`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper IsotropicVariance.Paper.Proofs.Labels

variable {m : ℕ}

/-- The pairs of indices of the rounded points of the two faces of a block. -/
abbrev GridPair (m L : ℕ) (κ : ℝ) : Type := GridCell m L κ × GridCell m L κ

/-- The values of `Ψ_G`: a level for each pair of indices. -/
abbrev GridCode (m L : ℕ) (κ M : ℝ) : Type := GridPair m L κ → Fin (levelCount M κ)

instance (m L : ℕ) (κ M : ℝ) : Nonempty (GridCode m L κ M) :=
  ⟨fun _ => ⟨0, Nat.succ_pos _⟩⟩

/-- **The levels are the multiples of `κ`**: for a natural number `N` and `κ = 1/(j + 1)`, the level
of `x` is the clip of `x` to `[−N, N]` rounded down to a multiple of `κ`, as in the definition of
`Ψ_G` (Step 2 of the proof of Lemma `lem:labels`), where `N = L⁴`. -/
theorem dequantize_quantize_eq (N j : ℕ) {κ : ℝ} (hκ : κ = 1 / ((j : ℝ) + 1)) (x : ℝ) :
    dequantize N κ (quantize N κ x) = κ * ⌊clampM N x / κ⌋ := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hκ0 : 0 < κ := by
    rw [hκ]
    positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨hc1, hc2⟩ := clampM_mem hN x
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = N * (j + 1) := ⟨_, rfl⟩
  have hAr : (A : ℝ) = N / κ := by
    rw [hA, hκ]
    push_cast
    field_simp
  obtain ⟨t, ht⟩ : ∃ t, t = clampM N x / κ := ⟨_, rfl⟩
  have hy : (clampM N x + N) / κ = t + A := by
    rw [hAr, ht, add_div]
  have hy0 : 0 ≤ t + A := by
    rw [← hy]
    exact div_nonneg (by linarith only [hc1]) hκ0.le
  have htop : levelCount (N : ℝ) κ - 1 = 2 * A := by
    have e : 2 * (N : ℝ) / κ = ((2 * A : ℕ) : ℝ) := by
      push_cast
      rw [hAr]
      ring
    rw [levelCount, e, Nat.ceil_natCast, Nat.add_sub_cancel]
  have hfl : ⌊t + A⌋₊ ≤ 2 * A := by
    refine Nat.floor_le_of_le ?_
    rw [← hy, div_le_iff₀ hκ0]
    push_cast
    have e : 2 * (A : ℝ) * κ = 2 * N := by
      rw [hAr]
      field_simp
    linarith only [hc2, e]
  have hq : ((quantize N κ x : ℕ) : ℝ) = ⌊t⌋ + A := by
    have e : (quantize N κ x : ℕ) = ⌊t + A⌋₊ := by
      simp only [quantize, hy, htop]
      exact min_eq_left hfl
    rw [e, natCast_floor_eq_intCast_floor hy0, Int.floor_add_natCast]
    push_cast
    rfl
  rw [dequantize, hq, ← ht]
  have e : (A : ℝ) * κ = N := by
    rw [hAr]
    field_simp
  linear_combination e

/-- The two points `(u_κ, v_κ)` of the pair of indices `pq`. -/
noncomputable def pairPts (n W : ℝ) (L : ℕ) (κ : ℝ) (i : ℕ) (z : Fin m → ℤ)
    (pq : GridPair m L κ) : Pt m × Pt m :=
  (blockCorner n W i z + gridRel 0 W κ pq.1, blockCorner n W i z + gridRel n W κ pq.2)

variable (X : Setting.{u} m)

/-- **`Ψ_G`** (Step 2 of the proof of Lemma `lem:labels`): the levels of `(T_G(u_κ, v_κ) − n)/Q`,
through versions `V` of the passage times of the blocks. -/
noncomputable def psiCode (V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ) (n W Q : ℝ) (L : ℕ)
    (κ M : ℝ) (i : ℕ) (z : Fin m → ℤ) (ω : X.Ω) : GridCode m L κ M :=
  fun pq => quantize M κ ((V i z ω (pairPts n W L κ i z pq) - n) / Q)

/-- **`X_G`** (Step 3 of the proof of Lemma `lem:labels`): `Ψ_G`, with each value of probability
less than `θ` replaced by a value of largest probability. -/
noncomputable def lambdaCode (V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ) (n W Q : ℝ) (L : ℕ)
    (κ M θ : ℝ) (i : ℕ) (z : Fin m → ℤ) (ω : X.Ω) : GridCode m L κ M :=
  mergeRare X.P (psiCode X V n W Q L κ M i z) θ (psiCode X V n W Q L κ M i z ω)

/-- **The family of the labels `X_G`**: a value of a label stands for the function of the endpoints
relative to the corner of the block that reads the level of their rounded points. -/
noncomputable def tgFamily (V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ) (n W Q : ℝ) (L : ℕ)
    (κ M θ : ℝ) : X.LabelFamily where
  V := GridCode m L κ M
  label := lambdaCode X V n W Q L κ M θ
  value := fun c x y => dequantize M κ (c (gridCell W L κ x, gridCell W L κ y))

/-- The fibers of `Ψ_G` are determined by the noise in `G`. -/
theorem measurableSet_psiCode_preimage {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W Q : ℝ}
    {L : ℕ} {κ M : ℝ} {i : ℕ} {z : Fin m → ℤ} (hV : Measurable[X.info (block n W L i z)] (V i z))
    (c : GridCode m L κ M) :
    MeasurableSet[X.info (block n W L i z)] (psiCode X V n W Q L κ M i z ⁻¹' {c}) := by
  have hm : ∀ pq : GridPair m L κ, Measurable[X.info (block n W L i z)]
      fun ω => quantize M κ ((V i z ω (pairPts n W L κ i z pq) - n) / Q) := fun pq =>
    (measurable_quantize M κ).comp
      (((measurable_pi_apply _).comp hV |>.sub_const n).div_const Q)
  have heq : psiCode X V n W Q L κ M i z ⁻¹' {c} =
      ⋂ pq : GridPair m L κ,
        (fun ω => quantize M κ ((V i z ω (pairPts n W L κ i z pq) - n) / Q)) ⁻¹' {c pq} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_iInter]
    exact ⟨fun h pq => h ▸ rfl, fun h => funext h⟩
  rw [heq]
  exact MeasurableSet.iInter fun pq => hm pq (measurableSet_singleton _)

/-- **Each label is determined by the noise in its block.** -/
theorem tgFamily_isDetermined {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W : ℝ} (Q : ℝ)
    {L : ℕ} (κ M θ : ℝ) (hV : ∀ i z, Measurable[X.info (block n W L i z)] (V i z)) :
    (tgFamily X V n W Q L κ M θ).IsDetermined n W L := fun i z c =>
  measurableSet_comp_preimage (measurableSet_psiCode_preimage X (hV i z))
    (mergeRare X.P (psiCode X V n W Q L κ M i z) θ) c

/-- **The values of the family are bounded functions.** -/
theorem tgFamily_hasBoundedValues (V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ) (n W Q : ℝ)
    (L : ℕ) {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M) (θ : ℝ) :
    (tgFamily X V n W Q L κ M θ).HasBoundedValues := fun _ =>
  ⟨M + κ, fun _ _ => abs_dequantize_le hM hκ _⟩

/-- **Each value of each label has probability `0` or at least `θ`**, for `θ` at most the inverse of
the number of values. -/
theorem tgFamily_atomsGe {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W : ℝ} (Q : ℝ) {L : ℕ}
    (κ M : ℝ) {θ : ℝ} (hV : ∀ i z, Measurable[X.info (block n W L i z)] (V i z))
    (hθ : θ ≤ 1 / Fintype.card (GridCode m L κ M)) :
    (tgFamily X V n W Q L κ M θ).AtomsGe θ := fun i z c =>
  atoms_mergeRare X.P (fun c => (X.info_le _) _ (measurableSet_psiCode_preimage X (hV i z) c)) hθ c

/-- `Ψ_G` is a random variable. -/
theorem measurable_psiCode {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W Q : ℝ} {L : ℕ}
    {κ M : ℝ} {i : ℕ} {z : Fin m → ℤ} (hV : Measurable[X.info (block n W L i z)] (V i z)) :
    Measurable (psiCode X V n W Q L κ M i z) :=
  measurable_to_countable' fun c => (X.info_le _) _ (measurableSet_psiCode_preimage X hV c)

/-- `X_G` is a random variable. -/
theorem measurable_lambdaCode {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W : ℝ} (Q : ℝ)
    {L : ℕ} (κ M θ : ℝ) (hV : ∀ i z, Measurable[X.info (block n W L i z)] (V i z)) (i : ℕ)
    (z : Fin m → ℤ) : Measurable (lambdaCode X V n W Q L κ M θ i z) :=
  measurable_to_countable' fun v => (X.info_le _) _
    (tgFamily_isDetermined X Q κ M θ hV i z v)

end IsotropicVariance.Paper.Proofs.Labels
