/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum

/-!
# The localization radii `R_i(j, k)`, blocks, couplings, the entries `Y_i(j, k)`

The setting of Lemma `lem:blocks`, stated before it in Section `sec:gain`: the slab
minimum `F` with `K` slabs of width `n` (`M = K`, `s = n`), the cubes `I_i(j)` and indices `J_i`
of Section `sec:exponential`; the radii `R_i(j, k)`; the blocks
`[(i−1)n, in] × W_n(z + [0, L)^m)`, `z ≡ o (mod L)`, of a slab with offset `o`; a coupling
replacing the noise in a block (exchangeable old and new noise, almost surely equal off the
block, the pair in the block independent of the noise off the block); the entries `Y_i(j, k)`.

The radii and the entries `Y_i(j, k)` are set to zero for `W_n |k − j| > n/2`, as in the paper.

Slabs and cubes are 0-based in Lean: the paper's slab `i ∈ {1, …, K}` is `i − 1`, and its cubes
`I_{i−1}(j)`, `I_i(k)` are `gridCube n W 0 (i − 1) j`, `gridCube n W 0 i k`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace IsotropicVariance.Paper

/-- The constant `(d − 1)^{1/2} + 2` in `R_i(j, k)` (here `m = d − 1`); it makes the tube of
radius `R_i W_n` contain the cubes and the unit neighborhoods of the curves once `W_n ≥ 1`. -/
noncomputable def radiusConst (m : ℕ) : ℝ := Real.sqrt m + 2

/-- The block `[in, (i+1)n] × W(z + [0, L)^m)` of the slab `i` (0-based) (Section `sec:gain`). -/
def block {m : ℕ} (n W : ℝ) (L : ℕ) (i : ℕ) (z : Fin m → ℤ) : Set (Pt m) :=
  {x | (i : ℝ) * n ≤ Pt.lon x ∧ Pt.lon x ≤ ((i : ℝ) + 1) * n ∧
    ∀ k, W * z k ≤ Pt.tr x k ∧ Pt.tr x k < W * (z k + L)}

/-- `z` indexes a block of a slab with offset `o ∈ {0, …, L−1}^m`: `z ≡ o (mod L)`. -/
def IsBlockIndex {m : ℕ} (L : ℕ) (o : Fin m → Fin L) (z : Fin m → ℤ) : Prop :=
  ∀ k, (L : ℤ) ∣ z k - (o k : ℕ)

namespace Setting

variable {m : ℕ} (X : Setting m)

/-- The radius `R_i(j, k)` (Section `sec:gain`) of a configuration: `C` plus `W⁻¹` times
the largest distance from the segment between the centers of `I_i(j)` and `I_{i+1}(k)` of the
points of the 1-optimal curves for the slab passage time `D_i` between these cubes (0-based
slab `i`), for `W |k − j| ≤ n/2`, and `0` for the other pairs. -/
noncomputable def R (b n W : ℝ) (c : X.Ω) (i : ℕ) (j k : Fin m → ℤ) : ℝ :=
  if W * zNorm (k - j) ≤ n / 2 then
    radiusConst m + W⁻¹ * maxDeviation ((chainSlab n 0 i).density b (X.ρ c))
      (chainSlab n 0 i).set (gridCube n W 0 i j) (gridCube n W 0 (i + 1) k)
      (gridCubeCenter n W 0 i j) (gridCubeCenter n W 0 (i + 1) k)
  else 0

/-- A coupling replacing the noise in `G` (Section `sec:gain`): on a probability space, old
and new outcomes of the noise, both with the law of the noise, exchangeable, indistinguishable by
the information off `G`, and the pair's information in `G` independent of the old information off
`G`. -/
structure IsBlockCoupling (G : Set (Pt m)) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (old new : Ω' → X.Ω) : Prop where
  /-- The old noise has the law of the noise. -/
  measurePreserving_old : MeasurePreserving old P' X.P
  /-- The new noise has the law of the noise. -/
  measurePreserving_new : MeasurePreserving new P' X.P
  /-- The pair is exchangeable. -/
  exchangeable : P'.map (fun ω => (old ω, new ω)) = P'.map (fun ω => (new ω, old ω))
  /-- Old and new noise agree off `G`: every event of the noise off `G` happens for both or for
  neither, almost surely (conditional resampling gives no more). -/
  agree_compl : ∀ A : Set X.Ω, MeasurableSet[X.info Gᶜ] A → ∀ᵐ ω ∂P', (old ω ∈ A ↔ new ω ∈ A)
  /-- The pair in `G` is independent of the noise off `G`. -/
  indep : Indep ((X.info G).comap old ⊔ (X.info G).comap new) ((X.info Gᶜ).comap old) P'

/-- `sup_{u ∈ I_i(j), v ∈ I_{i+1}(k)} (D_i^G(u, v) − D_i(u, v))₊` for old and new configurations
`c`, `c'` (Section `sec:gain`). -/
noncomputable def blockGain (b n W : ℝ) (i : ℕ) (j k : Fin m → ℤ)
    (c c' : X.Ω) : ℝ :=
  ⨆ (u : gridCube n W 0 i j) (v : gridCube n W 0 (i + 1) k),
    max (X.slabTime b (chainSlab n 0 i) c' u v - X.slabTime b (chainSlab n 0 i) c u v) 0

/-- The entry `Y_i(j, k) = Q⁻² Σ_G [sup (D_i^G − D_i)₊]²` (Section `sec:gain`), summed
over the blocks `z` of the slab, for the old noise `old` and the new noises `new z`, in `[0, ∞]`;
zero unless `W |k − j| ≤ n/2`, as every entry outside the pairs used. -/
noncomputable def Y (b n W Qn : ℝ) (i : ℕ) (j k : Fin m → ℤ) (blocks : Set (Fin m → ℤ))
    {Ω' : Type*} (old : Ω' → X.Ω) (new : (Fin m → ℤ) → Ω' → X.Ω)
    (ω : Ω') : ℝ≥0∞ :=
  if W * zNorm (k - j) ≤ n / 2 then
    ∑' z : blocks, ENNReal.ofReal ((X.blockGain b n W i j k (old ω) (new z ω) / Qn) ^ 2)
  else 0

/-- Couplings for all the blocks of a slab on one probability space (the entries `Y_i(j, k)` sum
over them): one old noise and a new noise for each block `z` of the slab. -/
structure BlockCouplingFamily (n W : ℝ) (L i : ℕ) (blocks : Set (Fin m → ℤ)) where
  /-- The probability space of the couplings. -/
  Ω' : Type
  [measurableSpace : MeasurableSpace Ω']
  /-- The probability. -/
  P' : Measure Ω'
  [isProbabilityMeasure : IsProbabilityMeasure P']
  /-- The old noise. -/
  old : Ω' → X.Ω
  /-- The new noise of each block. -/
  new : (Fin m → ℤ) → Ω' → X.Ω
  /-- Each pair is a coupling for its block. -/
  isBlockCoupling : ∀ z ∈ blocks, X.IsBlockCoupling (block n W L i z) P' old (new z)

attribute [instance] BlockCouplingFamily.measurableSpace BlockCouplingFamily.isProbabilityMeasure

end Setting

end IsotropicVariance.Paper
