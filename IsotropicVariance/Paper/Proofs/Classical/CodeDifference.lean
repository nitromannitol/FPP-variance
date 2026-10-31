/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.ProductRefreshLaw
public import IsotropicVariance.Paper.Proofs.Classical.GridDensity
public import IsotropicVariance.Paper.Proofs.Classical.UniformReplacement
public import IsotropicVariance.Infra.Concentration.ProductEntropy

/-! # Almost-sure bounded coordinate changes for the coded passage time -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- The deterministic physical bounded-change estimate transfers to product
refreshes almost surely, with no assertion at invalid coordinate values. -/
theorem ae_code_difference_le {m n : ℕ} (X : Setting m) {a b : ℝ} (ha : 0 < a)
    (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b)
    (z : Fin n → Coord (Pt m) → ℤ) (hz : Function.Injective z)
    (Φ : Fin n → X.Ω → ℕ → Bool) (hΦ : ∀ i, Measurable[X.info (gridCell (z i))] (Φ i))
    (f : (Fin n → ℕ → Bool) → ℝ) (hf : Measurable f) (u v : Pt m)
    (hRep : (fun ω => f (fun i => Φ i ω)) =ᵐ[X.P] fun ω => X.passTime ω u v)
    (hLaw : X.P.map (fun ω i => Φ i ω) = Measure.pi (fun i => X.P.map (Φ i)))
    (i : Fin n) :
    ∀ᵐ p ∂(Measure.pi (fun j => X.P.map (Φ j))).prod (X.P.map (Φ i)),
      |f p.1 - f (Function.update p.1 i p.2)| ≤
        (b / a) * (b * (5 * (Module.finrank ℝ (Pt m) : ℝ)) + 1) := by
  let F : X.Ω → Fin n → ℕ → Bool := fun ω j => Φ j ω
  let q := Noise.resampleLaw X.toNoiseModel (gridCell (z i))
  let B := (b / a) * (b * (5 * (Module.finrank ℝ (Pt m) : ℝ)) + 1)
  have hF : Measurable F := Measurable.of_eval fun j => (hΦ j).mono (X.info_le _) le_rfl
  have hPair : Measurable (fun p : X.Ω × X.Ω => (F p.1, F p.2)) :=
    (hF.comp measurable_fst).prodMk (hF.comp measurable_snd)
  have hPred : MeasurableSet {p : (Fin n → ℕ → Bool) × (Fin n → ℕ → Bool) |
      |f p.1 - f p.2| ≤ B} := by
    have hm : Measurable (fun p : (Fin n → ℕ → Bool) × (Fin n → ℕ → Bool) =>
        f p.1 - f p.2) := (hf.comp measurable_fst).sub (hf.comp measurable_snd)
    simp only [abs_le]
    exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hPhysical : ∀ᵐ p ∂q, |f (F p.1) - f (F p.2)| ≤ B := by
    have hOld := ae_of_ae_map (Noise.resampleLaw_old X.toNoiseModel (gridCell (z i))).aemeasurable
      (by rw [(Noise.resampleLaw_old X.toNoiseModel (gridCell (z i))).map_eq]; exact hRep)
    have hNew := ae_of_ae_map (Noise.resampleLaw_new X.toNoiseModel (gridCell (z i))).aemeasurable
      (by rw [(Noise.resampleLaw_new X.toNoiseModel (gridCell (z i))).map_eq]; exact hRep)
    filter_upwards [hOld, hNew, resampleLaw_ae_density_eq_grid X (z i)] with p hp0 hp1 hp
    rw [hp0, hp1, abs_sub_comm]
    exact abs_passage_change_le X ha (by positivity) hBounds p.1 p.2
      (isClosed_gridNeighborhood _) (fun _ hx _ hy => dist_le_of_mem_gridNeighborhood hx hy)
      (fun x hx => (hp x hx).symm) u v
  have hMapped : ∀ᵐ p ∂q.map (fun p => (F p.1, F p.2)), |f p.1 - f p.2| ≤ B :=
    (ae_map_iff hPair.aemeasurable hPred).mpr hPhysical
  have hDis : Pairwise (fun j k => Disjoint (gridCell (z j)) (gridCell (z k))) :=
    fun j k hjk => pairwiseDisjoint_gridCell (fun he => hjk (hz he))
  have hRefresh := map_resampleLaw_codes_eq_update X.toNoiseModel (fun j => gridCell (z j))
    (fun j => measurableSet_gridCell _) (fun j => volume_frontier_gridCell _) hDis Φ hΦ i
  rw [hLaw] at hRefresh
  change q.map (fun p => (F p.1, F p.2)) = _ at hRefresh
  rw [hRefresh] at hMapped
  have hD : Measurable (fun p : (Fin n → ℕ → Bool) × (ℕ → Bool) =>
      (p.1, Function.update p.1 i p.2)) :=
    measurable_fst.prodMk (IsotropicVariance.Infra.Entropy.measurable_update i)
  exact ae_of_ae_map hD.aemeasurable hMapped

end IsotropicVariance.Paper.Proofs.Classical
