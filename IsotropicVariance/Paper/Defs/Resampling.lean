/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
public import IsotropicVariance.Infra.Resampling.KernelProduct
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Condexp

/-!
# The resampling of the blocks

Section `sec:gain`: for each block `G`, let `σ_G` be a random variable determined by the noise in
`G`. The resampling of `G` is the noise `ω^G` that coincides with `ω` outside `G` and whose
restriction to `G` is drawn, given `ω`, from the conditional law of the noise in `G` given `σ_G`,
independently for distinct blocks.

* `NoiseModel.resampleKernel G σ`: the kernel `ω ↦ P[· | info Gᶜ ⊔ σ](ω)`.
* `NoiseModel.resamplingKernel G σ`: given `ω`, the independent draws from these kernels over a
  family of sets `G i`.
* `NoiseModel.resamplingLaw G σ`: the joint law of the noise `ω` and its resamplings `(ω^{G i})_i`.
  The old noise is `Prod.fst` and the new noise of `i` is `fun p => p.2 i`.
* `Setting.blockResampling n W L σ`: the same for all the blocks of side `L W`.
* `Setting.BlockInfo n W L`: the choices of the `σ_G`, each determined by the noise in its block.

Three choices of the formal statement.

* **`σ_G` is a σ-algebra.** Every random variable generates a σ-algebra, and the conditional law
  given the variable depends only on that σ-algebra. So `σ_G` of the paper is the argument `σ`, and
  "determined by the noise in `G`" is `σ ≤ info G`. For a label `X_G`, it is `Λ.sigma i z`.
* **The index is every block**, including blocks of different offsets `a_i`. The law of the
  resampling of a block does not depend on the offsets, and restricted to the blocks of one choice
  of offsets the family is the paper's family, because a marginal of `Measure.infinitePi` is the
  `Measure.infinitePi` of the marginals. So one probability space serves every choice of offsets,
  as the average over the `a_i` in Lemma `lem:residual` needs.
* **The noise off `G` is conditioned on.** The noise interface `NoiseModel` has no restriction map,
  so `ω^G` cannot be written as `ω` off `G` glued to a new noise in `G`. Instead "coincides with `ω`
  outside `G`" is the almost sure equality of the information of `Gᶜ`: the kernel conditions on
  `info Gᶜ`, and every event of `info Gᶜ` happens for both `ω` and `ω^G` or for neither.

The characterization of the resampling is in `IsotropicVariance.Paper.Proofs.Resampling`.

The kernel `condExpKernel` of Mathlib is a kernel from `Ω` with the σ-algebra `m`, so
`resampleKernel` takes `m = (info Gᶜ ⊔ σ) ⊓ mΩ` to get a kernel from the full σ-algebra of the
noise. For `σ ≤ mΩ`, the only case used, this `m` is `info Gᶜ ⊔ σ`.

**Local instances.** A variable `σ : MeasurableSpace N.Ω`, or a family of them, is a local instance:
it takes precedence over the instance `N.measurableSpace`. The `letI := N.measurableSpace` in the
signatures below puts the measurable space of the noise back. A statement with such a variable that
asks for a `MeasurableSpace N.Ω`, for example through `MeasurableSet A` or a type
`ι → N.Ω`, needs the same care; the statements about the resamplings of labels, with
`σ = fun p => Λ.sigma p.1 p.2`, have no such variable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open IsotropicVariance.Infra.Resampling

universe u

namespace IsotropicVariance.Paper

/-- All blocks `(i, z)`: slab `i` (0-based), transverse index `z`. -/
abbrev BlockIdx (m : ℕ) : Type := ℕ × (Fin m → ℤ)

namespace NoiseModel

variable {m : ℕ} (N : NoiseModel.{u} m)

/-- `ω ↦ P[· | info Gᶜ ⊔ σ](ω)`, the conditional law of the noise given the noise off `G`
and `σ`. For `σ ≤ info G` its restriction to `G` is the conditional law of the noise in `G` given
`σ` (`IsotropicVariance.Paper.Proofs.Resampling`). -/
noncomputable def resampleKernel (G : Set (Pt m)) (σ : MeasurableSpace N.Ω) :
    letI := N.measurableSpace; Kernel N.Ω N.Ω :=
  letI := N.measurableSpace
  (condExpKernel N.P ((N.info Gᶜ ⊔ σ) ⊓ N.measurableSpace)).comap id
    (measurable_id'' inf_le_right)

instance (G : Set (Pt m)) (σ : MeasurableSpace N.Ω) : IsMarkovKernel (N.resampleKernel G σ) := by
  let := N.measurableSpace
  unfold resampleKernel
  infer_instance

/-- Given `ω`, the independent draws from the kernels `resampleKernel (G i) (σ i) ω`. -/
noncomputable def resamplingKernel {ι : Type*} (G : ι → Set (Pt m))
    (σ : ι → MeasurableSpace N.Ω) : letI := N.measurableSpace; Kernel N.Ω (ι → N.Ω) :=
  letI := N.measurableSpace
  (coordinateProductKernel fun i => N.resampleKernel (G i) (σ i)).comap (fun ω _ => ω)
    (Measurable.of_eval fun _ => measurable_id)

instance {ι : Type*} (G : ι → Set (Pt m)) (σ : ι → MeasurableSpace N.Ω) :
    IsMarkovKernel (N.resamplingKernel G σ) := by
  let := N.measurableSpace
  unfold resamplingKernel
  infer_instance

/-- The draws given `ω` are independent, with the laws `resampleKernel (G i) (σ i) ω`. -/
theorem resamplingKernel_apply {ι : Type*} (G : ι → Set (Pt m)) (σ : ι → MeasurableSpace N.Ω)
    (ω : N.Ω) :
    N.resamplingKernel G σ ω = Measure.infinitePi fun i => N.resampleKernel (G i) (σ i) ω :=
  rfl

/-- The joint law of the noise `ω` and its resamplings `(ω^{G i})_i`: given `ω`, the `ω^{G i}` are
independent, with laws `resampleKernel (G i) (σ i) ω` (Section `sec:gain`). -/
noncomputable def resamplingLaw {ι : Type*} (G : ι → Set (Pt m))
    (σ : ι → MeasurableSpace N.Ω) : letI := N.measurableSpace; Measure (N.Ω × (ι → N.Ω)) :=
  letI := N.measurableSpace
  N.P ⊗ₘ N.resamplingKernel G σ

instance {ι : Type*} (G : ι → Set (Pt m)) (σ : ι → MeasurableSpace N.Ω) :
    IsProbabilityMeasure (N.resamplingLaw G σ) := by
  let := N.measurableSpace
  unfold resamplingLaw
  infer_instance

end NoiseModel

namespace Setting

variable {m : ℕ} (X : Setting.{u} m)

/-- The resampling of the blocks of side `L W`, for `σ_G = σ (i, z)`: the joint law of the old noise
`Prod.fst` and the new noises `fun p => p.2 (i, z)` (Section `sec:gain`). -/
noncomputable def blockResampling (n W : ℝ) (L : ℕ) (σ : BlockIdx m → MeasurableSpace X.Ω) :
    letI := X.measurableSpace; Measure (X.Ω × (BlockIdx m → X.Ω)) :=
  X.resamplingLaw (fun p => block n W L p.1 p.2) σ

instance (n W : ℝ) (L : ℕ) (σ : BlockIdx m → MeasurableSpace X.Ω) :
    IsProbabilityMeasure (X.blockResampling n W L σ) := by
  let := X.measurableSpace
  unfold blockResampling
  infer_instance

/-- The choices of the `σ_G` of Section `sec:gain` for the blocks of side `L W`: for each block,
information determined by the noise in that block. A statement over every choice of the `σ_G`
quantifies over this type: a variable of this type is not a local instance, while a variable
`σ : BlockIdx m → MeasurableSpace X.Ω` would be one (see the module docstring). -/
def BlockInfo (n W : ℝ) (L : ℕ) : Type u :=
  {σ : BlockIdx m → MeasurableSpace X.Ω // ∀ p, σ p ≤ X.info (block n W L p.1 p.2)}

end Setting

end IsotropicVariance.Paper
