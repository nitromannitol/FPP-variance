/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Translation
public import Mathlib.Algebra.Order.Group.PiLex

/-!
# Translating the minimizing chain

After equation `eq:cubes`: "Translating `ω` and the endpoints by a vector orthogonal to `e₁`
translates the `x_i` by the same vector." This is `lexMinimizer_act`, the fact of `F_eq_F_zero_act`
for the minimizing points. The translation by `v` preserves the constraints
(`isAdmissible_add_iff`), moves the sum and the minimum with the density (`slabSum_translate`,
`slabMinimum_translate`), and preserves the lexicographic order of the chains (`lexKey_add_le_iff`),
so it moves the least minimizer to the least minimizer (`isLexLeastMinimizer_translate`), which is
unique.
-/

@[expose] public section

open Set

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

variable {m : ℕ}

/-- The coordinates of a sum of points. -/
theorem Pt.coords_add (x v : Pt m) : Pt.coords (x + v) = Pt.coords x + Pt.coords v := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k <;> simp [Pt.coords]

/-- The lexicographic key of a translated chain is the key of the chain plus a constant. -/
theorem lexKey_add {M : ℕ} (x : Fin (M + 1) → Pt m) (v : Pt m) :
    lexKey (fun i => x i + v) =
      lexKey x + toLex fun p => Pt.coords v (finProdFinEquiv.symm p).2 := by
  simp only [lexKey, ← toLex_add]
  congr 1
  funext p
  simp [flatCoords, Pt.coords_add]

/-- **Translation preserves the lexicographic order of chains.** -/
theorem lexKey_add_le_iff {M : ℕ} {x y : Fin (M + 1) → Pt m} {v : Pt m} :
    lexKey (fun i => x i + v) ≤ lexKey (fun i => y i + v) ↔ lexKey x ≤ lexKey y := by
  rw [lexKey_add, lexKey_add]
  exact add_le_add_iff_right _

section Translate

variable {σ σ' : Pt m → ℝ} {v : Pt m}

/-- The sum `Σ_i D_i` for `σ' = σ(· + v)`, `v` transverse, is the sum for `σ` of the translated
chain. -/
theorem slabSum_translate (hv : Pt.lon v = 0) (hσ : ∀ x, σ' x = σ (x + v)) (b : ℝ) (M : ℕ) (s : ℝ)
    (τ : Pt m) (x : Fin (M + 1) → Pt m) :
    slabSum b σ M s (τ + v) (fun i => x i + v) = slabSum b σ' M s τ x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hslab : chainSlab s (τ + v) i = chainSlab s τ i := by simp [chainSlab, hv]
  rw [hslab]
  exact (e1Slab_passTime_translate hv _ s b hσ _ _).symm

/-- The slab minimum for `σ' = σ(· + v)`, `v` transverse, is the slab minimum for `σ` of the
translated chain. -/
theorem slabMinimum_translate (hv : Pt.lon v = 0) (hσ : ∀ x, σ' x = σ (x + v)) (b : ℝ) (M : ℕ)
    (s : ℝ) (τ : Pt m) : slabMinimum b σ M s (τ + v) = slabMinimum b σ' M s τ := by
  let e : {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x} ≃
      {x : Fin (M + 1) → Pt m // IsAdmissible M s (τ + v) x} :=
    { toFun := fun x => ⟨fun i => x.1 i + v, (isAdmissible_add_iff τ v x.1).2 x.2⟩
      invFun := fun y => ⟨fun i => y.1 i - v, (isAdmissible_add_iff τ v _).1 (by simpa using y.2)⟩
      left_inv := fun x => Subtype.ext (funext fun i => add_sub_cancel_right _ _)
      right_inv := fun y => Subtype.ext (funext fun i => sub_add_cancel _ _) }
  unfold slabMinimum
  rw [← e.iInf_comp]
  exact iInf_congr fun x => slabSum_translate hv hσ b M s τ x.1

/-- **The translate of the least minimizer for `σ' = σ(· + v)` is the least minimizer for `σ`** of
the chain translated by the transverse vector `v`. -/
theorem isLexLeastMinimizer_translate (hv : Pt.lon v = 0) (hσ : ∀ x, σ' x = σ (x + v)) {b : ℝ}
    {M : ℕ} {s : ℝ} {τ : Pt m} {x : Fin (M + 1) → Pt m} (hx : IsLexLeastMinimizer b σ' M s τ x) :
    IsLexLeastMinimizer b σ M s (τ + v) (fun i => x i + v) := by
  refine ⟨(isAdmissible_add_iff τ v x).2 hx.1, ?_, fun y hy hyv => ?_⟩
  · rw [slabSum_translate hv hσ, slabMinimum_translate hv hσ, hx.2.1]
  · have hyy : (fun i => (y i - v) + v) = y := funext fun i => sub_add_cancel _ _
    have hy' : IsAdmissible M s τ fun i => y i - v :=
      (isAdmissible_add_iff τ v _).1 (by rwa [hyy])
    have hyv' : slabSum b σ' M s τ (fun i => y i - v) = slabMinimum b σ' M s τ := by
      rw [← slabSum_translate hv hσ, hyy, hyv, slabMinimum_translate hv hσ]
    have hle := (lexKey_add_le_iff (v := v)).2 (hx.2.2 _ hy' hyv')
    rwa [hyy] at hle

end Translate

/-- **Translating the chain** (after equation `eq:cubes`): the least minimizing points for the noise
moved by `x ↦ x − v`, `v` orthogonal to `e₁`, from `τ`, are those for the noise from `τ + v`,
translated by `−v`. As in `F_eq_F_zero_act`, `X.act (shiftBy v)` moves the noise by `−v`, so the
paper's statement for the vector `w` is the case `v = −w`, `τ` the translated endpoint. -/
theorem lexMinimizer_act (X : Setting.{u} m) (b : ℝ) (M : ℕ) {s : ℝ} (hs : 0 ≤ s) (τ : Pt m)
    {v : Pt m} (hv : Pt.lon v = 0) (ω : X.Ω) (i : Fin (M + 1)) :
    lexMinimizer b (X.ρ ω) M s (τ + v) i =
      lexMinimizer b (X.ρ (X.act (shiftBy v) ω)) M s τ i + v := by
  have h := isLexLeastMinimizer_translate hv (ρ_act_shiftBy X v ω)
    (isLexLeastMinimizer_lexMinimizer b (X.isValidChain (X.act (shiftBy v) ω) hs) M τ)
  exact congrFun ((lexMinimizer_eq_iff b (X.isValidChain ω hs) M (τ + v)).2 h) i

end IsotropicVariance.Paper.Proofs.Gain
