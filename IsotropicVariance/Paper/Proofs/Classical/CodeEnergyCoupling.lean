/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.CoupledGridEnergy
public import IsotropicVariance.Paper.Proofs.Classical.ProductRefreshLaw

/-! # The common-field energy bound transported to finite regional codes -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Classical
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- A coded passage time admits a product-refresh coupling with the checked
linear summed-energy bound for its negative. -/
theorem exists_code_energy_coupling {m n : ℕ} (X : Setting m) {a b : ℝ} (ha : 0 < a)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    (z : Fin n → Coord (Pt m) → ℤ) (hz : Function.Injective z)
    (Φ : Fin n → X.Ω → ℕ → Bool) (hΦ : ∀ i, Measurable[X.info (gridCell (z i))] (Φ i))
    (f : (Fin n → ℕ → Bool) → ℝ) (hf : Measurable f) (u v : Pt m)
    (hRep : (fun ω => f (fun i => Φ i ω)) =ᵐ[X.P] fun ω => X.passTime ω u v)
    (hLaw : X.P.map (fun ω i => Φ i ω) = Measure.pi (fun i => X.P.map (Φ i))) :
    ∃ Q : Measure ((Fin n → ℕ → Bool) × (Fin n → Fin n → ℕ → Bool)),
      Q.map Prod.fst = Measure.pi (fun i => X.P.map (Φ i)) ∧
      (∀ i, Q.map (fun p => (p.1, p.2 i)) =
        ((Measure.pi (fun j => X.P.map (Φ j))).prod (X.P.map (Φ i))).map
          (fun p => (p.1, Function.update p.1 i p.2))) ∧
      (∀ᵐ p ∂Q,
        let d := Module.finrank ℝ (Pt m)
        let B := (b / a) * (b * (5 * (d : ℝ)) + 1)
        (∑ i : Fin n, max (-f p.1 - -f (p.2 i)) 0 ^ 2) ≤
          2 * B ^ 2 * (9 ^ d : ℕ) * (b * dist u v / a + 1)) := by
  let F : X.Ω → Fin n → ℕ → Bool := fun ω j => Φ j ω
  have hF : Measurable F := Measurable.of_eval fun j => (hΦ j).mono (X.info_le _) le_rfl
  let Ψ : X.Ω × (Fin n → X.Ω) → (Fin n → ℕ → Bool) × (Fin n → Fin n → ℕ → Bool) :=
    fun p => (F p.1, fun i => F (p.2 i))
  have hΨ : Measurable Ψ := (hF.comp measurable_fst).prodMk
    (Measurable.of_eval fun i => hF.comp ((measurable_pi_apply i).comp measurable_snd))
  obtain ⟨Q, _hQ, hFirst, hPairs, hEnergy⟩ := exists_grid_energy_coupling X ha hBounds z hz u v
  have hg (i : Fin n) : Measurable (fun p : X.Ω × (Fin n → X.Ω) => (p.1, p.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have hFF : Measurable (fun p : X.Ω × X.Ω => (F p.1, F p.2)) :=
    (hF.comp measurable_fst).prodMk (hF.comp measurable_snd)
  refine ⟨Q.map Ψ, ?_, ?_, ?_⟩
  · calc
      _ = (Q.map Prod.fst).map F := by
        rw [Measure.map_map measurable_fst hΨ, Measure.map_map hF measurable_fst]
        rfl
      _ = _ := by rw [hFirst]; exact hLaw
  · intro i
    have hDis : Pairwise (fun j k => Disjoint (gridCell (z j)) (gridCell (z k))) :=
      fun j k hjk => pairwiseDisjoint_gridCell (fun he => hjk (hz he))
    have hRefresh := map_resampleLaw_codes_eq_update X.toNoiseModel (fun j => gridCell (z j))
      (fun _ => measurableSet_gridCell _) (fun _ => volume_frontier_gridCell _) hDis Φ hΦ i
    rw [hLaw] at hRefresh
    have hCodeg : Measurable (fun p : (Fin n → ℕ → Bool) ×
        (Fin n → Fin n → ℕ → Bool) => (p.1, p.2 i)) :=
      measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    calc
      _ = (Q.map (fun p => (p.1, p.2 i))).map (fun p => (F p.1, F p.2)) := by
        rw [Measure.map_map hCodeg hΨ, Measure.map_map hFF (hg i)]
        rfl
      _ = _ := by rw [hPairs i]; exact hRefresh
  · have hOld : ∀ᵐ p ∂Q, f (F p.1) = X.passTime p.1 u v :=
      ae_of_ae_map measurable_fst.aemeasurable (by rw [hFirst]; exact hRep)
    have hNew (i : Fin n) : ∀ᵐ p ∂Q, f (F (p.2 i)) = X.passTime (p.2 i) u v := by
      have hMarg : Q.map (fun p => p.2 i) = X.P := by
        have hh := congrArg (fun μ => μ.map Prod.snd) (hPairs i)
        rw [Measure.map_map measurable_snd (hg i),
          (Noise.resampleLaw_new X.toNoiseModel (gridCell (z i))).map_eq] at hh
        simpa only [Function.comp_def] using hh
      have hm : Measurable (fun p : X.Ω × (Fin n → X.Ω) => p.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      exact ae_of_ae_map hm.aemeasurable (by rw [hMarg]; exact hRep)
    apply (ae_map_iff hΨ.aemeasurable (measurableSet_le (by fun_prop) measurable_const)).mpr
    filter_upwards [hOld, ae_all_iff.mpr hNew, hEnergy] with p hp0 hp1 hpE
    change (∑ i : Fin n, max (-f (F p.1) - -f (F (p.2 i))) 0 ^ 2) ≤ _
    simp_rw [hp0, hp1, neg_sub_neg]
    exact hpE

end IsotropicVariance.Paper.Proofs.Classical
