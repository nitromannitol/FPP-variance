/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusCore
import CurvatureVariance.Paper.Proofs.ShortLengths.ProfilesBounds
import Mathlib.Tactic.Linarith

/-!
# Lemma `lem:modulus`: the variable `D`

The quantity `D` of the proof of [AB26, Lemma 5.2], with `P = ℝ^d` only, in the proof of Lemma
`lem:modulus`: the pairs `(u, x)`, `(ũ, x)`, `(x', v)` and `(x', ṽ)` lie in at most `C(b) g^{−C}`
pairs of cubes as in Proposition `prop:profiles`, with `s = ⌈gℓ⌉` and sides `(gℓQ_{gℓ})^{1/2}`, in
its first case, and equation `eq:union` gives one `O₁` variable.

* `UnionOne`: equation `eq:union` at `s = 1`, in the universes of this file;
* `exists_isOs_box_pairs`: the union bound on the grids of cubes covering two pairs of boxes, of
  which there are `2 ((2n + 1)^m)²`;
* `grid_slope_le`: the slopes of the pairs of cubes are in the first case of Proposition
  `prop:profiles`: `|t' − t₀| ≤ (4/5) s^{δ/100−1/4}`, for `16 s ≤ ℓ`;
* `exists_box_bound`: the variable `D`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-- Equation `eq:union` at `s = 1`, with constant `CU`. It is the statement that
`Contracts.OsUnionStatement.{0, 0}` gives at `s = 1`. -/
def UnionOne (CU : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type}
    (T : Finset ι) (hT : T.Nonempty) (θ : ℝ), 0 < θ → ∀ X : ι → Ω → ℝ,
    (∀ i ∈ T, CurvatureVariance.IsOs P 1 θ (X i)) →
      CurvatureVariance.IsOs P 1 (CU * θ * Real.log (2 + T.card) ^ (1 / (1 : ℝ))) (T.sup' hT X)

/-- **The union bound on the pairs of cubes**: bounds on the grid pairs of cubes of side `s₀` for
two pairs of boxes (`ρ/s₀ + 1/2 ≤ n`), indexed by `i : Bool`, give one `O₁` variable, through
equation `eq:union`. -/
theorem exists_isOs_box_pairs {P : Measure (Config m)} [IsProbabilityMeasure P] {CU : ℝ}
    (hU : UnionOne CU) (F : Config m → Vertex m → Vertex m → ℝ) {n : ℕ} {s₀ ρ θ : ℝ}
    (hs₀ : 0 < s₀) (hn : ρ / s₀ + 1 / 2 ≤ n) (hθ : 0 < θ) (p q : Bool → ℤ)
    (z z' : Bool → EuclideanSpace ℝ (Fin m))
    (hpair : ∀ i, ∀ k ∈ gridIndices m n, ∀ k' ∈ gridIndices m n,
      ∃ X : Config m → ℝ, CurvatureVariance.IsOs P 1 θ X ∧ ∀ᵐ ω ∂P,
        ∀ u ∈ transverseCube (p i) (z i + s₀ • transversePoint k) s₀,
          ∀ x ∈ transverseCube (q i) (z' i + s₀ • transversePoint k') s₀, |F ω u x| ≤ X ω) :
    ∃ Y : Config m → ℝ, CurvatureVariance.IsOs P 1
      (CU * θ * Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ))) Y ∧
      ∀ᵐ ω ∂P, ∀ i, ∀ u ∈ transverseCube (p i) (z i) (2 * ρ),
        ∀ x ∈ transverseCube (q i) (z' i) (2 * ρ), |F ω u x| ≤ Y ω := by
  classical
  set J : Finset (Bool × (Fin m → ℤ) × (Fin m → ℤ)) :=
    (Finset.univ : Finset Bool) ×ˢ (gridIndices m n ×ˢ gridIndices m n) with hJdef
  have hJ : J.Nonempty := Finset.univ_nonempty.product
    ((gridIndices_nonempty m n).product (gridIndices_nonempty m n))
  have hcard : (J.card : ℝ) = ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ) := by
    rw [hJdef, Finset.card_product, Finset.card_product, card_gridIndices, ← sq]
    simp only [Finset.card_univ, Fintype.card_bool]
  have h : ∀ j ∈ J, ∃ X : Config m → ℝ, CurvatureVariance.IsOs P 1 θ X ∧ ∀ᵐ ω ∂P,
      ∀ u ∈ transverseCube (p j.1) (z j.1 + s₀ • transversePoint j.2.1) s₀,
        ∀ x ∈ transverseCube (q j.1) (z' j.1 + s₀ • transversePoint j.2.2) s₀,
          |F ω u x| ≤ X ω := by
    intro j hj
    have hj' := Finset.mem_product.mp (Finset.mem_product.mp hj).2
    exact hpair j.1 j.2.1 hj'.1 j.2.2 hj'.2
  choose! X hX hXb using h
  refine ⟨J.sup' hJ X, ?_, ?_⟩
  · have := hU P J hJ θ hθ X hX
    rwa [div_one, Real.rpow_one, hcard] at this
  · filter_upwards [(Filter.eventually_all_finset J).mpr hXb] with ω hω i u hu x hx
    obtain ⟨k, hk, hku⟩ := exists_mem_gridIndices_cube hs₀ hn hu.1
      (fun j => by have := hu.2 j; linarith only [this])
    obtain ⟨k', hk', hkx⟩ := exists_mem_gridIndices_cube hs₀ hn hx.1
      (fun j => by have := hx.2 j; linarith only [this])
    have hmem : (i, k, k') ∈ J := Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨hk, hk'⟩⟩
    refine (hω (i, k, k') hmem u hku x hkx).trans ?_
    rw [Finset.sup'_apply]
    exact Finset.le_sup' (fun j => X j ω) hmem

/-- The slopes of the pairs of cubes (the proof of Lemma `lem:modulus`): for `16 s ≤ ℓ`, the cubes
of side `s₀ ≤ η s^{3/4+δ/100}` have slopes in the first case of Proposition `prop:profiles`. The
margin is `(3/2) 16^{δ/100−1/4} < 4/5` (`slope_le_sixteen`), so that
`|t − t₀| ≤ (8/15) s^{δ/100−1/4}`. -/
theorem grid_slope_le {M : Model m} {s n : ℕ} {ℓ : ℝ} {t : EuclideanSpace ℝ (Fin m)} {s₀ ηw : ℝ}
    (hδ1 : M.δ ≤ 1) (hs : 0 < s) (hsℓ : 16 * (s : ℝ) ≤ ℓ)
    (ht : ‖t - M.t₀‖ ≤ ℓ ^ (M.δ / 100 - 1 / 4)) (hs₀ : 0 ≤ s₀)
    (hs₀W : s₀ ≤ ηw * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hηw : ηw * (2 * m * n) ≤ 1 / 4) {k k' : Fin m → ℤ} (hk : k ∈ gridIndices m n)
    (hk' : k' ∈ gridIndices m n) :
    ‖t + (s₀ / s) • (transversePoint k' - transversePoint k) - M.t₀‖ ≤
      4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  set e := M.δ / 100 - 1 / 4 with he
  have hse : 0 < (s : ℝ) ^ e := Real.rpow_pos_of_pos hs0 _
  have he0 : e ≤ 0 := by rw [he]; linarith only [hδ1]
  have h16 : (16 * (s : ℝ)) ^ e * (3 / 2) ≤ 4 / 5 * (s : ℝ) ^ e := by
    have := Proofs.ShortLengths.slope_le_sixteen hδ1 (s := 16 * (s : ℝ)) (by positivity)
    rw [mul_div_cancel_left₀ _ (by norm_num : (16 : ℝ) ≠ 0)] at this
    linarith only [this]
  have hℓ : ℓ ^ e ≤ (16 * (s : ℝ)) ^ e :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hsℓ he0
  have hs₀s : s₀ / s ≤ ηw * (s : ℝ) ^ e := by
    rw [div_le_iff₀ hs0, mul_assoc, ← Real.rpow_add_one hs0.ne']
    convert hs₀W using 3
    rw [he]; ring
  have hkn : ‖transversePoint k‖ ≤ m * n :=
    norm_transversePoint_le fun j => abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk j))
  have hkn' : ‖transversePoint k'‖ ≤ m * n :=
    norm_transversePoint_le fun j => abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk' j))
  have hdiff : ‖transversePoint k' - transversePoint k‖ ≤ 2 * m * n := by
    have := norm_sub_le (transversePoint k') (transversePoint k)
    linarith only [this, hkn, hkn']
  have hsL0 : 0 ≤ s₀ / s := div_nonneg hs₀ hs0.le
  have e1 : t + (s₀ / s) • (transversePoint k' - transversePoint k) - M.t₀ =
      (t - M.t₀) + (s₀ / s) • (transversePoint k' - transversePoint k) := by abel
  have n1 : ‖t + (s₀ / s) • (transversePoint k' - transversePoint k) - M.t₀‖ ≤
      ‖t - M.t₀‖ + s₀ / s * ‖transversePoint k' - transversePoint k‖ := by
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hsL0]
  have n2 : s₀ / s * ‖transversePoint k' - transversePoint k‖ ≤ 1 / 4 * (s : ℝ) ^ e := by
    calc s₀ / s * ‖transversePoint k' - transversePoint k‖
        ≤ s₀ / s * (2 * m * n) := mul_le_mul_of_nonneg_left hdiff hsL0
      _ ≤ ηw * (s : ℝ) ^ e * (2 * m * n) :=
          mul_le_mul_of_nonneg_right hs₀s (by positivity)
      _ = ηw * (2 * m * n) * (s : ℝ) ^ e := by ring
      _ ≤ 1 / 4 * (s : ℝ) ^ e := mul_le_mul_of_nonneg_right hηw hse.le
  linarith only [n1, n2, ht, hℓ, h16, hse]

/-- **The variable `D`** (the proof of Lemma `lem:modulus`): one `O₁` variable dominates
`|T(z,z') − μ(z'−z)|` for `z` in the box around `I` and `z'` in the box around the point of the line
at `s` from it, and the same at `I'`. Proposition `prop:profiles`, in its first case, enters through
`hS1`. -/
theorem exists_box_bound (M : Model m) [IsProbabilityMeasure M.P] {K : ℕ} {A CU C₁ s₀ ρ : ℝ}
    {p : ℤ} {ℓ s n : ℕ} {c c' t : EuclideanSpace ℝ (Fin m)} (hU : UnionOne CU) (hs : 0 < s)
    (hs₀ : 0 < s₀) (hs₀W : s₀ ≤ W M K A s) (hn : ρ / s₀ + 1 / 2 ≤ n)
    (hθ : 0 < C₁ * Q M K A s)
    (hgrid : ∀ k ∈ gridIndices m n, ∀ k' ∈ gridIndices m n,
      ‖t + (s₀ / s) • (transversePoint k' - transversePoint k) - M.t₀‖ ≤
        4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4))
    (hS1 : ∀ (τ : EuclideanSpace ℝ (Fin m)) (J J' : Set (Vertex m)),
      IsCubePair M K A s 1 τ J J' → ‖τ - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
      Contracts.ShortConclusion M K A s C₁ τ J J') :
    ∃ Y : Config m → ℝ, CurvatureVariance.IsOs M.P 1
      (CU * (C₁ * Q M K A s) * Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ))) Y ∧
      ∀ᵐ ω ∂M.P,
        (∀ u ∈ transverseCube p c (2 * ρ),
          ∀ x ∈ transverseCube (p + s) (c + (s : ℝ) • t) (2 * ρ),
            |passageTimeReal ω u x - M.μ.1 (point x - point u)| ≤ Y ω) ∧
        (∀ x ∈ transverseCube (p + ((ℓ : ℤ) - s)) (c' - (s : ℝ) • t) (2 * ρ),
          ∀ v ∈ transverseCube (p + ℓ) c' (2 * ρ),
            |passageTimeReal ω x v - M.μ.1 (point v - point x)| ≤ Y ω) := by
  have hs1024 : (0 : ℝ) ≤ (s : ℝ) / 1024 := by positivity
  obtain ⟨Y, hY, hYb⟩ := exists_isOs_box_pairs hU
    (fun ω u x => passageTimeReal ω u x - M.μ.1 (point x - point u)) hs₀ hn hθ
    (fun i => cond i p (p + ((ℓ : ℤ) - s))) (fun i => cond i (p + s) (p + ℓ))
    (fun i => cond i c (c' - (s : ℝ) • t)) (fun i => cond i (c + (s : ℝ) • t) c')
    (fun i k hk k' hk' => by
      cases i with
      | true =>
        obtain ⟨X, hXO, hXb⟩ := hS1 _ _ _ (isCubePair_grid M hs hs₀.le hs₀W p c t k k')
          (hgrid k hk k' hk')
        exact ⟨X, hXO, hXb.mono fun ω hω u hu x hx => hω.1 u (subset_thicken _ _ hs1024 hu)
          x (subset_thicken _ _ hs1024 hx)⟩
      | false =>
        have hcp := isCubePair_grid M hs hs₀.le hs₀W (p + ((ℓ : ℤ) - s)) (c' - (s : ℝ) • t) t k k'
        have e1 : p + ((ℓ : ℤ) - s) + (s : ℤ) = p + ℓ := by ring
        have e2 : c' - (s : ℝ) • t + (s : ℝ) • t = c' := sub_add_cancel _ _
        rw [e1, e2] at hcp
        obtain ⟨X, hXO, hXb⟩ := hS1 _ _ _ hcp (hgrid k hk k' hk')
        exact ⟨X, hXO, hXb.mono fun ω hω x hx v hv => hω.1 x (subset_thicken _ _ hs1024 hx)
          v (subset_thicken _ _ hs1024 hv)⟩)
  exact ⟨Y, hY, hYb.mono fun ω hω => ⟨hω true, hω false⟩⟩

end CurvatureVariance.Paper.Localization.Modulus
