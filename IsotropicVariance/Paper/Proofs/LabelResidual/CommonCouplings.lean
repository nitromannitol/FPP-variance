/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.BridgeCoupling

/-!
# Decoding the noise from the reals

`decodeReal`: the measurable left inverse of a Borel embedding of the noise in the reals
(`embeddingReal`), which carries laws on the noise to laws on a probability space in `Type`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace IsotropicVariance.Paper.Proofs.LabelResidual

universe u

section Decode

variable {E : Type u} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]

/-- A measurable left inverse of the standard Borel embedding in the real line. -/
noncomputable def decodeReal : ℝ → E :=
  Function.extend (embeddingReal E) id fun _ => Classical.arbitrary _

theorem measurable_decodeReal : Measurable (decodeReal (E := E)) :=
  (measurableEmbedding_embeddingReal E).measurable_extend measurable_id measurable_const

theorem decodeReal_embeddingReal (x : E) : decodeReal (embeddingReal E x) = x :=
  (measurableEmbedding_embeddingReal E).injective.extend_apply _ _ x

end Decode

end IsotropicVariance.Paper.Proofs.LabelResidual
