/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Gain
public import IsotropicVariance.Paper.Defs.Averaged

/-!
# Proposition `prop:gain`: the label energy

`labelCouplingEnergy`: for a function `Z` of the noise, the offsets `o` of the `K` slabs and a
family of resamplings of the blocks given their labels, `½ Σ_G E (Z(new) − Z(old))²`, the left side
of equation `eq:residual`. The sum runs over the blocks `(i, z)`, `i < K`, `z ≡ o i (mod L)`, in
`[0, ∞]`.

The averaged minimum `F̄ = ⌈K^{2/3}⌉⁻¹ Σ_{j < ⌈K^{2/3}⌉} F_j` of Section `sec:gain` is `averagedMin
X b K n W L` (`IsotropicVariance.Paper.Defs.Averaged`), where `F_j` is the slab minimum of equation
`eq:F` in the same `K` slabs of width `n` from `j L W e₂` to `Kn e₁ + j L W e₂`. Lean slabs are
0-based: slab `i` is `[in, (i+1)n] × ℝ^m` (`chainSlab n 0 i`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper IsotropicVariance.Paper.Contracts

section Energies

variable {m : ℕ} (X : Setting.{u} m) (n W : ℝ) (L K : ℕ)

/-- `½ Σ_G E (Z^{G, X_G} − Z)²` for a family of resamplings of the blocks given their labels: the
left side of equation `eq:residual` at fixed offsets (`ℛ_Z`). -/
noncomputable def labelCouplingEnergy (Λ : X.LabelFamily) (o : Fin K → Fin m → Fin L)
    (cpl : (i : ℕ) → (z : Fin m → ℤ) → X.LabelResamplingData Λ n W L i z)
    (Z : X.Ω → ℝ) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
    ∫⁻ ω, ENNReal.ofReal ((Z ((cpl i z).new ω) - Z ((cpl i z).old ω)) ^ 2) ∂(cpl i z).P'

end Energies

end IsotropicVariance.Paper.Proofs.Gain
