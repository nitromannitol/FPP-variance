/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks

/-!
# Finite-valued approximations of blocks and resampling given them

The proof of Lemma `lem:labels`: every block `G` of the `i`-th slab has a
finite-valued approximation `X_G`, determined by the noise in `G`, each of whose values has
probability `0` or at least a positive number depending only on `L`, given by the same rule,
translated, in every block. Its value is a function of the two endpoints, compared on the cores of
the two faces `{in} × W(z + [√L, L − √L]^m)` and `{(i+1)n} × W(z + [√L, L − √L]^m)` (0-based slab
`i`). The resampling `F^{G, X_G}` uses a coupling whose new noise in `G` has the conditional law
of the old one given `X_G`, independently of everything else.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace IsotropicVariance.Paper

/-- The core `{in} × W(z + [√L, L − √L]^m)` of a face of the block `(i, z)`: the points at
distance at least `√L W` from the other blocks of the slab (the proof of Lemma `lem:labels`). -/
def coreFace {m : ℕ} (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) : Set (Pt m) :=
  {x | Pt.lon x = (i : ℝ) * n ∧
    ∀ k, W * (z k + Real.sqrt L) ≤ Pt.tr x k ∧ Pt.tr x k ≤ W * (z k + L - Real.sqrt L)}

/-- The corner `(in, Wz)` of the block `(i, z)`. -/
noncomputable def blockCorner {m : ℕ} (n W : ℝ) (i : ℕ) (z : Fin m → ℤ) : Pt m :=
  Pt.mk ((i : ℝ) * n) (WithLp.toLp 2 fun k => W * z k)

namespace Setting

variable {m : ℕ} (X : Setting m)

/-- A family of finite-valued approximations of the blocks: a label for each block `(i, z)`
with values in one finite type, and the function of the endpoints, relative to the corner of
the block, that each value stands for (the proof of Lemma `lem:labels`). -/
structure LabelFamily where
  /-- The finite set of values. -/
  V : Type
  [fintype : Fintype V]
  /-- The label `X_G` of the block `(i, z)`, a function of the configuration. -/
  label : ℕ → (Fin m → ℤ) → X.Ω → V
  /-- The function of the endpoints `(u − corner, v − corner)` that a value stands for. -/
  value : V → Pt m → Pt m → ℝ

attribute [instance] LabelFamily.fintype

namespace LabelFamily

variable {X} (Λ : X.LabelFamily)

/-- Each label is determined by the noise in its block. -/
def IsDetermined (n W : ℝ) (L : ℕ) : Prop :=
  ∀ i z v, MeasurableSet[X.info (block n W L i z)] (Λ.label i z ⁻¹' {v})

/-- Each value of each label has probability `0` or at least `τ`. -/
def AtomsGe (τ : ℝ) : Prop :=
  ∀ i z v, X.P ((Λ.label i z) ⁻¹' {v}) = 0 ∨
    ENNReal.ofReal τ ≤ X.P ((Λ.label i z) ⁻¹' {v})

/-- The values are bounded functions of the endpoints (Lemma `lem:labels`). -/
def HasBoundedValues : Prop :=
  ∀ v, ∃ C : ℝ, ∀ u w, |Λ.value v u w| ≤ C

/-- The information `σ_G` of the label of the block `(i, z)`: the σ-algebra it generates. -/
@[instance_reducible]
def sigma (i : ℕ) (z : Fin m → ℤ) : MeasurableSpace X.Ω :=
  MeasurableSpace.comap (Λ.label i z) ⊤

/-- A label determined by the noise in its block generates a part of the information of the
block. -/
theorem sigma_le {n W : ℝ} {L : ℕ} (h : Λ.IsDetermined n W L) (i : ℕ) (z : Fin m → ℤ) :
    Λ.sigma i z ≤ X.info (block n W L i z) := by
  rintro _ ⟨t, -, rfl⟩
  rw [show Λ.label i z ⁻¹' t = ⋃ v ∈ t, Λ.label i z ⁻¹' {v} by
    rw [← preimage_iUnion₂, biUnion_of_singleton]]
  exact @MeasurableSet.biUnion _ _ (X.info _) _ _ t.to_countable fun v _ => h i z v

end LabelFamily

/-- A coupling resampling the noise in the block `(i, z)` from its conditional law given the
label `X_G` (the proof of Lemma `lem:labels`): a block coupling, the label is
unchanged, and given each value of the label the old and new noise in the block are independent
with the same law. -/
structure IsLabelResampling (Λ : X.LabelFamily) (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (old new : Ω' → X.Ω) :
    Prop where
  /-- A coupling for the block. -/
  isBlockCoupling : X.IsBlockCoupling (block n W L i z) P' old new
  /-- The label is unchanged. -/
  label_eq : ∀ᵐ ω ∂P', Λ.label i z (new ω) = Λ.label i z (old ω)
  /-- Given the label, the old and new noise in the block are independent with the same law. -/
  condIndep : ∀ A B : Set (X.Ω),
    MeasurableSet[X.info (block n W L i z)] A →
    MeasurableSet[X.info (block n W L i z)] B → ∀ v : Λ.V,
      P' {ω | old ω ∈ A ∧ new ω ∈ B ∧ Λ.label i z (old ω) = v} *
          P' {ω | Λ.label i z (old ω) = v} =
        P' {ω | old ω ∈ A ∧ Λ.label i z (old ω) = v} *
          P' {ω | old ω ∈ B ∧ Λ.label i z (old ω) = v}

/-- A label resampling for the block `(i, z)`, bundled with its probability space. -/
structure LabelResamplingData (Λ : X.LabelFamily) (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) where
  /-- The probability space. -/
  Ω' : Type
  [measurableSpace : MeasurableSpace Ω']
  /-- The probability. -/
  P' : Measure Ω'
  [isProbabilityMeasure : IsProbabilityMeasure P']
  /-- The old noise. -/
  old : Ω' → X.Ω
  /-- The resampled noise. -/
  new : Ω' → X.Ω
  /-- The resampling properties. -/
  isLabelResampling : X.IsLabelResampling Λ n W L i z P' old new

attribute [instance] LabelResamplingData.measurableSpace LabelResamplingData.isProbabilityMeasure

end Setting

end IsotropicVariance.Paper
