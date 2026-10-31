/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Noise.Resampling
public import IsotropicVariance.Infra.Resampling.LabelPair
public import IsotropicVariance.Infra.Resampling.KernelProduct
public import IsotropicVariance.Infra.Resampling.ConditionalPair
public import IsotropicVariance.Infra.EfronStein.Conditional
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent regional coordinates and conditional Efron–Stein for the paper model

Measurable codes of independent regional information have their product law. This transports
the conditional Efron–Stein inequality of `IsotropicVariance.Infra.EfronStein.Conditional` back to
observables of the noise coordinates.
No common coordinate law is assumed. The mean conditional variance is written using the
product-coordinate conditional expectation, evaluated at the actual regional coordinates.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace IsotropicVariance.Infra.Noise
open IsotropicVariance.Paper
open IsotropicVariance.Infra.EfronStein
universe u
variable {m : ℕ} (N : NoiseModel.{u} m) {I : Type} [Countable I]
  {E : I → Type*} [∀ i, MeasurableSpace (E i)]
  (S : I → Set (Pt m)) (hS : ∀ i, MeasurableSet (S i))
  (hb : ∀ i, volume (frontier (S i)) = 0)
  (hd : Pairwise (Function.onFun Disjoint fun i => interior (S i)))
  (R : ∀ i, N.Ω → E i) (hR : ∀ i, Measurable[N.info (S i)] (R i))

include hS hb hd hR

/-- Codes measurable for independent regional information are independent random variables. -/
theorem iIndepFun_regionCoordinates : iIndepFun R N.P := by
  rw [iIndepFun_iff]
  intro t B hB
  exact (N.iIndep_info I S hS hb hd).meas_biInter (fun i hi => (hR i).comap_le _ (hB i hi))

/-- The joint law of the regional coordinates is the product of their own marginal laws. -/
theorem map_regionCoordinates_eq_infinitePi :
    N.P.map (fun ω i => R i ω) = Measure.infinitePi (fun i => N.P.map (R i)) :=
  iIndepFun.map_fun_eq_infinitePi_map
    (fun i => (hR i).mono (N.info_le _) le_rfl)
    (iIndepFun_regionCoordinates N S hS hb hd R hR)

end IsotropicVariance.Infra.Noise
