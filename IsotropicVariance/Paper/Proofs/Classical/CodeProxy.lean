/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.CodeEnergyCoupling
public import IsotropicVariance.Paper.Proofs.Classical.WeightedProxy

/-! # The variance proxy for a normalized negative coded passage time -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- The physical grid energy gives the normalized coded variance proxy. -/
theorem ae_neg_code_proxy_le {m n : ℕ} (X : Setting m) {a b : ℝ} (ha : 0 < a)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    (z : Fin n → Coord (Pt m) → ℤ) (hz : Function.Injective z)
    (Φ : Fin n → X.Ω → ℕ → Bool) (hΦ : ∀ i, Measurable[X.info (gridCell (z i))] (Φ i))
    (f : (Fin n → ℕ → Bool) → ℝ) (hf : Measurable f) (u v : Pt m)
    (hRep : (fun ω => f (fun i => Φ i ω)) =ᵐ[X.P] fun ω => X.passTime ω u v)
    (hLaw : X.P.map (fun ω i => Φ i ω) = Measure.pi (fun i => X.P.map (Φ i)))
    {r : ℝ} (hr : 0 < r) :
    let d := Module.finrank ℝ (Pt m)
    let B := (b / a) * (b * (5 * (d : ℝ)) + 1)
    ∀ᵐ x ∂Measure.pi (fun i => X.P.map (Φ i)),
      Cited.vPlus (fun i => X.P.map (Φ i)) (fun x => -f x / r) x ≤
        ENNReal.ofReal ((2 * B ^ 2 * (9 ^ d : ℕ) * (b * dist u v / a + 1)) / r ^ 2) := by
  obtain ⟨Q, hOld, hPair, hEnergy⟩ := exists_code_energy_coupling X ha hBounds z hz Φ hΦ f hf u v hRep hLaw
  exact ae_vPlus_div_le_of_coupling (fun i => X.P.map (Φ i)) (fun x => -f x)
    hf.neg Q hOld hPair hr hEnergy

end IsotropicVariance.Paper.Proofs.Classical
