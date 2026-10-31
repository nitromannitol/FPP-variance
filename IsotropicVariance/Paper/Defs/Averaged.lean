/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Labels

/-!
# The averaged minimum `F̄`, its conditional mean `f`, and the expectation `E_G`

Section `sec:gain`.

* `Proofs.Gain.averagedMin`: `F̄ = ⌈K^{2/3}⌉⁻¹ Σ_m F_m`, with `F_m` the slab minimum translated by
  `m L W e₂`, and with it `Proofs.Gain.e₂` and `Proofs.Gain.colCount`. They stay in the namespace
  `Proofs.Gain` of the proof of Proposition `prop:gain`, their users.
* `Setting.LabelFamily.allSigma`, `Setting.LabelFamily.otherSigma`: the information of all labels
  of the blocks with given offsets, and of all of them but one.
* `Setting.labelMean`: `f = E[F̄ | (X_G)_G]`.

**The expectation `E_G`.** Proposition `prop:BR` is applied to `f` with the `X_G` as the variables,
and `E_G` there is the expectation over the variable `X_G` alone. On the noise, `E_G[f]` is
`X.P[f | Λ.otherSigma K o i z]`. For independent labels the two agree: if
`f = φ ∘ (X_H)_H` almost surely, then almost surely
`X.P[f | Λ.otherSigma K o i z] = Σ_v P(X_G = v) φ((X_H)_H with X_G replaced by v)`. This is the
proposition `Proofs.Gain.condExp_otherSigma_eq_sum_label` of `Paper.Proofs.Gain.FewTranslates`.
-/

@[expose] public section

open MeasureTheory

universe u

namespace IsotropicVariance.Paper

namespace Proofs.Gain

/-- The transverse unit vector `e₂ = (0, 1, 0, …, 0)` (zero when `m = 0`). -/
noncomputable def e₂ (m : ℕ) : Pt m :=
  Pt.mk 0 (WithLp.toLp 2 fun k : Fin m => if (k : ℕ) = 0 then (1 : ℝ) else 0)

/-- `e₂` is transverse. -/
@[simp] theorem lon_e₂ {m : ℕ} : Pt.lon (e₂ m) = 0 := rfl

/-- The number `⌈K^{2/3}⌉` of translated slab minima averaged in Section `sec:gain`. -/
noncomputable def colCount (K : ℕ) : ℕ :=
  ⌈(K : ℝ) ^ ((2 : ℝ) / 3)⌉₊

/-- **The averaged minimum** `F̄ = ⌈K^{2/3}⌉⁻¹ Σ_{j < ⌈K^{2/3}⌉} F_j` (Section `sec:gain`): `F_j`
is the slab minimum of equation `eq:F` in the same `K` slabs of width `n`, from `j L W e₂` to `Kn
e₁ + j L W e₂`. -/
noncomputable def averagedMin {m : ℕ} (X : Setting.{u} m) (b : ℝ) (K : ℕ) (n W : ℝ) (L : ℕ)
    (ω : X.Ω) : ℝ :=
  ((colCount K : ℝ))⁻¹ *
    ∑ j ∈ Finset.range (colCount K), X.F b K n (((j : ℝ) * L * W) • e₂ m) ω

end Proofs.Gain

namespace Setting

namespace LabelFamily

variable {m L : ℕ} {X : Setting.{u} m} (Λ : X.LabelFamily)

/-- The information of all labels of the blocks with offsets `o`: `σ((X_G)_G)` over the blocks
`(i, z)`, `i < K`, `z ≡ o i (mod L)`. -/
@[instance_reducible]
def allSigma (K : ℕ) (o : Fin K → Fin m → Fin L) : MeasurableSpace X.Ω :=
  ⨆ (i : Fin K) (z : Fin m → ℤ) (_ : IsBlockIndex L (o i) z), Λ.sigma i z

/-- The information of the labels of the blocks with offsets `o`, without the block `(i, z)`. -/
@[instance_reducible]
def otherSigma (K : ℕ) (o : Fin K → Fin m → Fin L) (i : Fin K) (z : Fin m → ℤ) :
    MeasurableSpace X.Ω :=
  ⨆ (i' : Fin K) (z' : Fin m → ℤ) (_ : IsBlockIndex L (o i') z') (_ : (i', z') ≠ (i, z)),
    Λ.sigma i' z'

/-- Leaving out a block loses information. -/
theorem otherSigma_le_allSigma (K : ℕ) (o : Fin K → Fin m → Fin L) (i : Fin K)
    (z : Fin m → ℤ) : Λ.otherSigma K o i z ≤ Λ.allSigma K o :=
  iSup₂_le fun i' z' => iSup_le fun hz' => iSup_le fun _ =>
    le_iSup₂_of_le i' z' (le_iSup_of_le hz' le_rfl)

/-- The information of the labels is information about the noise. -/
theorem allSigma_le {n W : ℝ} (h : Λ.IsDetermined n W L) (K : ℕ)
    (o : Fin K → Fin m → Fin L) : Λ.allSigma K o ≤ X.measurableSpace :=
  iSup₂_le fun i z => iSup_le fun _ => (Λ.sigma_le h i z).trans (X.info_le _)

end LabelFamily

variable {m L : ℕ} (X : Setting.{u} m)

/-- `f = E[F̄ | (X_G)_G]` (Section `sec:gain`), for the blocks with offsets `o`. -/
noncomputable def labelMean (b : ℝ) (K : ℕ) (n W : ℝ) (Λ : X.LabelFamily)
    (o : Fin K → Fin m → Fin L) : X.Ω → ℝ :=
  X.P[Proofs.Gain.averagedMin X b K n W L | Λ.allSigma K o]

end Setting

end IsotropicVariance.Paper
