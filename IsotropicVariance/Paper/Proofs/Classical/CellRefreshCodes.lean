/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.RefreshLaw
public import IsotropicVariance.Paper.Proofs.Classical.CellIndependence
import IsotropicVariance.Paper.Proofs.Gain.BridgeInfo

/-! # Regional codes under an actual cell refresh -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- The new regional code is independent of every old observable. -/
theorem map_resampleLaw_old_code_eq_prod {m : ℕ} (N : NoiseModel m)
    {E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]
    {S : Set (Pt m)} (hS : MeasurableSet S) (hNull : volume (frontier S) = 0)
    {F : N.Ω → E} {R : N.Ω → Z} (hF : Measurable F) (hR : Measurable[N.info S] R) :
    (Noise.resampleLaw N S).map (fun p => (F p.1, R p.2)) =
      (N.P.map F).prod (N.P.map R) := by
  have : Nonempty N.Ω := nonempty_of_isProbabilityMeasure N.P
  exact map_sigmaPairLaw_old_new_eq_prod N.P (N.info_le _) (N.info_le _)
    (Gain.Bridge.indep_info_compl N hS hNull) hF hR

/-- An actual refresh changes only the owned coordinate in a finite vector
of disjoint regional codes. -/
theorem resampleLaw_ae_codes_eq_update {m n : ℕ} (N : NoiseModel m)
    (S : Fin n → Set (Pt m))
    (hDisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (Φ : Fin n → N.Ω → ℕ → Bool) (hΦ : ∀ j, Measurable[N.info (S j)] (Φ j))
    (i : Fin n) :
    ∀ᵐ p ∂Noise.resampleLaw N (S i),
      (fun j => Φ j p.2) = Function.update (fun j => Φ j p.1) i (Φ i p.2) := by
  have hKeep (j : Fin n) : ∀ᵐ p ∂Noise.resampleLaw N (S i),
      j ≠ i → Φ j p.1 = Φ j p.2 := by
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ h => (h hji).elim
    · have hSub : S j ⊆ (S i)ᶜ := by
        intro x hx hxi
        exact Set.disjoint_left.mp (hDisjoint hji) hx hxi
      have hMeas : Measurable[N.info (S i)ᶜ] (Φ j) :=
        (hΦ j).mono (N.info_mono hSub) le_rfl
      exact (Noise.resampleLaw_ae_variable_eq N (S i) hMeas).mono fun _ hp _ => hp
  filter_upwards [ae_all_iff.mpr hKeep] with p hp
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
  · rw [Function.update_of_ne hji]
    exact (hp j hji).symm

end IsotropicVariance.Paper.Proofs.Classical
