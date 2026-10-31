/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Labels
public import Mathlib.Probability.ConditionalProbability

/-!
# Labels of blocks and resampling given a label (Lemmas `lem:labels` and `lem:residual`)

The objects through which the proofs of Section `sec:gain` talk to each other:

* `labelES P X G lam`: the mean square change `E (X − X^{G,λ})²` of `X` when the weights of the edge
  set `G` are resampled conditionally on the value of the label `λ` (Lemma `lem:residual`):
  `∫ω ∫ω' (X ω − X(ω^{G,ω'}))² dP[|λ = λ(ω)](ω') dP(ω)`, where `ω^{G,ω'} = resample G ω ω'`. For a
  function `λ` of the weights of `G` this is the Efron–Stein term of the resampling of `G` from its
  conditional law given `λ_G`. It depends on `λ` only through its level sets
  (`labelES_congr_level`). `l1Term P X G`: `E |X − X^G|`, the `L¹` influence of resampling `G` from
  the original law (the second bound of Lemma `lem:fewtranslates`).
* `IsBlockLabel`: the conclusion, equation `eq:labelprofile`, of Lemma `lem:labels`,
  for one block at an error `ε`: `λ` is a function of the weights of the block with finitely many
  values, measurable level sets, and `‖sup |(D_i(u,v) − P_t·(v−u))/Q_n − λ(u,v)|‖_{8d} ≤ ε` over
  the subcube faces.
* `offsetOf σ`: the offsets `o i = σ (i − 1)` of the slabs `1 ≤ i ≤ K` (`0` elsewhere) for
  `σ : Fin K → Fin m → Fin L`; `offsetAverage`: the average over the `L^{mK}` offset families
  (the average over `a` in equation `eq:residual`).
* `labelEnergy X lam o`: `½ ∑_G E (X − X^{G,λ_G})²` over the blocks `G` of the `K` slabs with the
  offsets `o`, for a family of labels `lam i o' g` indexed by the slab, the offset and the block
  index.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Resampling a set of edges given a label -/

/-- `E |X − X^G|`: the `L¹` influence of resampling the weights of `G` from the original law,
`∫∫ |X(ω) − X(ω^{G,ω'})| dP(ω') dP(ω)`. -/
noncomputable def l1Term (P : Measure (Config m)) (X : Config m → ℝ) (G : Set (Sym2 (Vertex m))) :
    ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal |X ω - X (resample G ω ω')| ∂P ∂P

/-! ### Label energies -/

/-- `½ ∑_G E (X − X^{G,λ_G})²` over the blocks `G = block n w L t (i + 1) (o (i + 1)) g`, `i < K`,
`g ∈ ℤ^{d-1}`, of the `K` slabs with the offsets `o`, for a family of labels `lam i o' g` of the
blocks (the first bound of equation `eq:residual`). -/
noncomputable def labelEnergy (P : Measure (Config m)) (X : Config m → ℝ) (n w L K : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) {β : Type*}
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β) (o : ℕ → Fin m → ℤ) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
    labelES P X (block n w L t (i + 1) (o (i + 1)) g) (lam (i + 1) (o (i + 1)) g)

end CurvatureVariance.Paper.Gain
