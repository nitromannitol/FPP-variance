/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.LabelResidual.Tau
public import CurvatureVariance.Paper.Proofs.LabelResidual.Small
public import CurvatureVariance.Paper.Proofs.LabelResidual.Replacement
import CurvatureVariance.Paper.Proofs.Responses.Energy
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Paper.Proofs.Responses.RadiusMoments

/-!
# The first bound of Lemma `lem:residual`: the assembly

Equation `eq:residual`. The pieces:

* the resampling of each block given its label, as a family of exchangeable replacements of the
  blocks indexed by the offset families (`IsLabelPairFamily`; their existence is
  `LabelPairFamiliesExist`);

Only the family structure is here; the rest of the argument is in `Proofs.Residual`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-- **A family of replacements resampling each block given its label** (the resampling of
Lemma `lem:residual`), indexed by the offset families `σ`: for each `σ` an exchangeable
replacement of the blocks with the offsets `offsetOf σ` on pairs of configurations, keeping the
label of the resampled block, whose block terms are the `labelES` terms, whose slab pairs are
independent, and whose slab pair of slab `i + 1` has a law depending only on `σ i`. -/
structure IsLabelPairFamily (M : Model m) (n w L K : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ)
    (Pr : (Fin K → Fin m → Fin L) → Measure (Config m × Config m)) : Prop where
  prob : ∀ σ, IsProbabilityMeasure (Pr σ)
  repl : ∀ σ, IsSlabReplacement M (Pr σ) n K w L t (offsetOf σ) Prod.fst
    (pairNew n w L t (offsetOf σ))
  lab : ∀ σ (i : ℕ), 1 ≤ i → i ≤ K → ∀ g, ∀ᵐ x ∂Pr σ,
    lam i (offsetOf σ i) g (pairNew n w L t (offsetOf σ) i g x) = lam i (offsetOf σ i) g x.1
  es : ∀ σ (i : ℕ), 1 ≤ i → i ≤ K → ∀ g (X : Config m → ℝ), Measurable X →
    labelES M.P X (block n w L t i (offsetOf σ i) g) (lam i (offsetOf σ i) g) =
      ∫⁻ x, ENNReal.ofReal ((X x.1 - X (pairNew n w L t (offsetOf σ) i g x)) ^ 2) ∂Pr σ
  ind : ∀ σ, iIndepFun (fun (i : Fin K) x => slabPair n ((i : ℕ) + 1) x) (Pr σ)
  loc : ∀ (i : Fin K) σ σ', σ i = σ' i →
    (Pr σ).map (slabPair n ((i : ℕ) + 1)) = (Pr σ').map (slabPair n ((i : ℕ) + 1))

/-- **The label-pair families exist** for labels of the blocks that are functions of the weights of
their blocks, with finitely many values and measurable level sets. -/
def LabelPairFamiliesExist (m : ℕ) : Prop :=
  ∀ M : Model m, M.Standing → ∀ n w L K : ℕ, 1 ≤ L → ∀ t : EuclideanSpace ℝ (Fin m),
  ∀ lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ,
    (∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ o g : Fin m → ℤ, (∀ k, 0 ≤ o k ∧ o k < L) →
      (∀ ω ω' : Config m, (∀ e : Edge m, e.1 ∈ block n w L t i o g → ω e = ω' e) →
        lam i o g ω = lam i o g ω') ∧
      (Set.range (lam i o g)).Finite ∧
      ∀ ω, MeasurableSet (lam i o g ⁻¹' {lam i o g ω})) →
    ∃ Pr, IsLabelPairFamily M n w L K t lam Pr

/-- **The label-pair families exist**: `labelPairLaw` for the offsets of each offset family. -/
theorem labelPairFamiliesExist : LabelPairFamiliesExist m := by
  intro M hM n w L K hL t lam hlam
  have := hM.probF
  have hfam : ∀ σ : Fin K → Fin m → Fin L, IsLabelFamily n w L K t (offsetOf σ) lam := fun σ =>
    { dep := fun i hi hiK g => (hlam i hi hiK _ g (offsetOf_mem hL σ i)).1
      finite := fun i hi hiK g => (hlam i hi hiK _ g (offsetOf_mem hL σ i)).2.1
      measurableSet := fun i hi hiK g => (hlam i hi hiK _ g (offsetOf_mem hL σ i)).2.2 }
  refine ⟨fun σ => labelPairLaw M n w L K t (offsetOf σ) lam,
    { prob := fun σ => inferInstance
      repl := fun σ => isSlabReplacement_labelPairLaw hM hL
      lab := fun σ i hi hiK g => ae_lam_pairNew_eq hM (hfam σ) hi hiK g
      es := fun σ i hi hiK g X hX => labelES_eq_lintegral_labelPairLaw hM (hfam σ) hi hiK g hX
      ind := fun σ => iIndepFun_slabPair_labelPairLaw hM hL
      loc := fun i σ σ' h => ?_ }⟩
  refine map_slabPair_labelPairLaw_congr hM hL i.isLt ?_
  rw [offsetOf_succ σ i, offsetOf_succ σ' i, h]

end CurvatureVariance.Paper.Gain.LabelResidual
