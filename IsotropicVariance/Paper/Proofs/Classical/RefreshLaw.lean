/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.SigmaPairIndependent

/-! # The law of an old observable and an independent refreshed coordinate -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra.Resampling

/-- Conditional refresh gives the product law of a whole old observable and
a fresh observable of the independent regional information. -/
theorem map_sigmaPairLaw_old_new_eq_prod {Ω E Z : Type*} [M : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace E] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] {G H : MeasurableSpace Ω}
    (hG : G ≤ M) (hH : H ≤ M) (hInd : Indep H G P)
    {F : Ω → E} {R : Ω → Z} (hF : @Measurable Ω E M _ F) (hR : Measurable[H] R) :
    @Measure.map (Ω × Ω) (E × Z) (M.prod M) _
      (fun p => (F p.1, R p.2)) (sigmaPairLaw (mΩ := M) G P) =
      (@Measure.map Ω E M _ F P).prod (@Measure.map Ω Z M _ R P) := by
  let _ : MeasurableSpace Ω := M
  have hRm : Measurable R := hR.mono hH le_rfl
  have hPair : Measurable (fun p : Ω × Ω => (F p.1, R p.2)) :=
    (hF.comp measurable_fst).prodMk (hRm.comp measurable_snd)
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hPair (hA.prod hB), Measure.prod_prod,
    Measure.map_apply hF hA, Measure.map_apply hRm hB]
  change sigmaPairLaw (mΩ := M) G P ((F ⁻¹' A) ×ˢ (R ⁻¹' B)) = _
  exact sigmaPairLaw_prod_eq_of_indep P hG hH hInd (hF hA) (hR hB)

end IsotropicVariance.Paper.Proofs.Classical
