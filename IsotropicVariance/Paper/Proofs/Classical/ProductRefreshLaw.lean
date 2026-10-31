/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.CellRefreshCodes

/-! # Physical regional refreshes induce ordinary product-coordinate refreshes -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra

/-- The full pair of code vectors has the law obtained by retaining the old
vector and independently refreshing its owned coordinate. -/
theorem map_resampleLaw_codes_eq_update {m n : ℕ} (N : NoiseModel m)
    (S : Fin n → Set (Pt m)) (hS : ∀ i, MeasurableSet (S i))
    (hNull : ∀ i, volume (frontier (S i)) = 0)
    (hDisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (Φ : Fin n → N.Ω → ℕ → Bool) (hΦ : ∀ j, Measurable[N.info (S j)] (Φ j))
    (i : Fin n) :
    (Noise.resampleLaw N (S i)).map (fun p => ((fun j => Φ j p.1), (fun j => Φ j p.2))) =
      ((N.P.map (fun ω j => Φ j ω)).prod (N.P.map (Φ i))).map
        (fun p => (p.1, Function.update p.1 i p.2)) := by
  let F : N.Ω → Fin n → ℕ → Bool := fun ω j => Φ j ω
  have hF : Measurable F := Measurable.of_eval fun j => (hΦ j).mono (N.info_le _) le_rfl
  have hOwn : Measurable (fun p : N.Ω × N.Ω => (F p.1, Φ i p.2)) :=
    (hF.comp measurable_fst).prodMk (((hΦ i).mono (N.info_le _) le_rfl).comp measurable_snd)
  have hUpd : Measurable (fun p : (Fin n → ℕ → Bool) × (ℕ → Bool) =>
      (p.1, Function.update p.1 i p.2)) := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_snd : Measurable (Prod.snd :
        (Fin n → ℕ → Bool) × (ℕ → Bool) → ℕ → Bool))
    · simpa only [Function.update_of_ne hji, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  have hLaw := map_resampleLaw_old_code_eq_prod N (hS i) (hNull i) hF (hΦ i)
  have hKeep := resampleLaw_ae_codes_eq_update N S hDisjoint Φ hΦ i
  calc
    _ = ((Noise.resampleLaw N (S i)).map (fun p => (F p.1, Φ i p.2))).map
        (fun p => (p.1, Function.update p.1 i p.2)) := by
      rw [Measure.map_map hUpd hOwn]
      apply Measure.map_congr
      exact hKeep.mono fun p hp => congrArg (fun y => (F p.1, y)) hp
    _ = _ := by rw [hLaw]

end IsotropicVariance.Paper.Proofs.Classical
