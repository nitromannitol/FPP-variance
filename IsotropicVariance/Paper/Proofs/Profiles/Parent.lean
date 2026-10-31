/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.ParentBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:parent`: the statement `ParentStatement`

The proof in the paper: fix an integer `M`, depending only on `β₂` and the
constant of equation `eq:rowenergy`, with `s = ℓ/M ≤ N/4` and `C₁ M^{−2/5} ≤ 1/200`
(`parentSlabs`). Lemma `lem:rowenergy` with `β₁/M` in place of `β₁`, and equation `eq:columns` in
its `O_1` form, give `|T_ℓ − ℓ| ≤ C M Q_s + O_1(C₁ Q_s + C M log²(2 + ℓ))`. Since
`Q_s ≤ M^{−2/5} Q_ℓ` and `C M log²(2 + ℓ) ≤ Q_ℓ/200` for `N` large, this is equation `eq:parent`.
-/

@[expose] public section

open MeasureTheory Set Metric

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Infra.Os

/-- `log(2 + ℓ) ≤ 2 log(2 + N)` for `ℓ ≤ c N` and `c ≤ N`. -/
lemma log_two_add_le_two_mul {c N ℓ : ℝ} (hN : 0 ≤ N) (hc : c ≤ N) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ c * N) :
    Real.log (2 + ℓ) ≤ 2 * Real.log (2 + N) := by
  have h1 : ℓ ≤ N * N := hℓ.trans (mul_le_mul_of_nonneg_right hc hN)
  have h2 : 2 + ℓ ≤ (2 + N) ^ 2 := by nlinarith only [h1, hN]
  have h3 := Real.log_le_log (by linarith only [hℓ0]) h2
  rw [Real.log_pow] at h3
  exact_mod_cast h3

/-- **Lemma `lem:parent`, equation `eq:parent`**, from Lemma
`lem:rowenergy` and equation `eq:columns`. -/
theorem parentStatement_of (hR : Contracts.RowEnergyStatement.{u})
    (hS : Contracts.SlabStatement.{u}) : Contracts.ParentStatement.{u} := by
  intro m hm X hX Cstar hCstar c₂ hc₂
  obtain ⟨Bd, hBd0, hBd⟩ := exists_upperBound X
  have hb : X.IsUpperBound Bd := hBd
  obtain ⟨CR, hCR, hrow⟩ := hR m hm X hX Bd hb Cstar hCstar
  obtain ⟨CS, hCS, -, hcol⟩ := hS m hm X hX Bd hb
  set M := parentSlabs c₂ CR with hMdef
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast one_le_parentSlabs c₂ CR
  have hMpos : (0 : ℝ) < M := by linarith only [hM1]
  refine ⟨CR * M, by positivity, fun c₁ hc₁ K => ?_⟩
  obtain ⟨NR, hNR⟩ := hrow (c₁ / M) (by positivity) K
  obtain ⟨NL, hNL⟩ := exists_log_le (800 * (M * CS)) c₁ hc₁
  refine ⟨max (max NR NL) (max (max 2 c₂) (max (4 * c₂) (3 * M / c₁))),
    fun A N hN hst ℓ hℓ1 hℓ2 => ?_⟩
  obtain ⟨hK, hA, hN2, -, -⟩ := id hst
  obtain ⟨hN1, hN3⟩ := max_le_iff.mp hN
  obtain ⟨hNR', hNL'⟩ := max_le_iff.mp hN1
  obtain ⟨hN4, hN5⟩ := max_le_iff.mp hN3
  obtain ⟨-, hNc⟩ := max_le_iff.mp hN4
  obtain ⟨-, hNM⟩ := max_le_iff.mp hN5
  have hNpos : 0 < N := by linarith only [hN2]
  have hℓpos : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ1
  set s := ℓ / M with hs
  have hMs : (M : ℝ) * s = ℓ := by rw [hs]; field_simp
  have hs1 : c₁ / M * N ≤ s := by
    rw [hs, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hMpos]
    linarith only [hℓ1]
  have hs2 : s ≤ N / 4 := by
    rw [hs, div_le_iff₀ hMpos]
    have h4 : 4 * c₂ ≤ (M : ℝ) := le_parentSlabs c₂ CR
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ N / 4)
    linarith only [h5, hℓ2]
  have hs3 : 2 < s := by
    have h3 : 3 ≤ c₁ / M * N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hMpos]
      have h6 := mul_le_mul_of_nonneg_left hNM hc₁.le
      rw [mul_div_cancel₀ _ hc₁.ne'] at h6
      linarith only [h6]
    linarith only [hs1, h3]
  have hM1' : 1 ≤ parentSlabs c₂ CR := one_le_parentSlabs c₂ CR
  obtain ⟨hnn, HS⟩ := hcol M s 0 hM1' hs3
  simp only [hMs, zero_add] at hnn HS
  have HR := hNR A N hNR' hst M s hM1' hs1 hs2
  have hA0 : 0 < A := by linarith only [hA]
  have hQs : 0 < Q K A s := Q_pos hA0 (by linarith only [hs3])
  have hQℓ : 0 < Q K A ℓ := Q_pos hA0 hℓpos
  have hQsℓ : Q K A s ≤ Q K A ℓ := Q_mono hK hA0.le (by linarith only [hs3]) (by
    rw [← hMs]
    exact le_mul_of_one_le_left (by linarith only [hs3]) hM1)
  have hθ₁ : CR * Q K A s ≤ Q K A ℓ / 200 := by
    have h1 : Q K A s ≤ ((M : ℝ)⁻¹) ^ (2 / 5 : ℝ) * Q K A ℓ :=
      Q_le_rpow_mul hK hA0.le (by linarith only [hs3]) hℓpos.le (by positivity)
        (inv_le_one_of_one_le₀ hM1) (by rw [← hMs]; field_simp; rfl)
    have h2 := rpow_parentSlabs c₂ hCR
    rw [← hMdef] at h2
    calc CR * Q K A s ≤ CR * (((M : ℝ)⁻¹) ^ (2 / 5 : ℝ) * Q K A ℓ) :=
          mul_le_mul_of_nonneg_left h1 hCR.le
      _ = CR * ((M : ℝ)⁻¹) ^ (2 / 5 : ℝ) * Q K A ℓ := by ring
      _ ≤ 1 / 200 * Q K A ℓ := mul_le_mul_of_nonneg_right h2 hQℓ.le
      _ = Q K A ℓ / 200 := by ring
  have hθ₂ : CS * (M : ℝ) * Real.log (2 + ℓ) ^ 2 ≤ Q K A ℓ / 200 := by
    have hlogle := log_two_add_le_two_mul hNpos.le hNc hℓpos.le hℓ2
    have hlog0 : 0 ≤ Real.log (2 + ℓ) := Real.log_nonneg (by linarith only [hℓpos])
    have h1 : Real.log (2 + ℓ) ^ 2 ≤ (2 * Real.log (2 + N)) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlogle 2
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ CS * (M : ℝ))
    have h3 := hNL K hK A N hA hNL' ℓ hℓ1
    have h4 : CS * (M : ℝ) * (2 * Real.log (2 + N)) ^ 2 =
        800 * (M * CS) * Real.log (2 + N) ^ 2 / 200 := by ring
    linarith only [h2, h3, h4]
  have hE : ∀ ω, 0 ≤ s⁻¹ * ∑ i : Fin (parentSlabs c₂ CR),
      ‖lexMinimizer Bd (X.ρ ω) (parentSlabs c₂ CR) s 0 i.succ -
        lexMinimizer Bd (X.ρ ω) (parentSlabs c₂ CR) s 0 i.castSucc - s • e₁‖ ^ 2 := fun ω =>
    mul_nonneg (inv_pos.2 (by linarith only [hs3])).le (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hMs] at HR
  have hlog0 : 0 < Real.log (2 + ℓ) := Real.log_pos (by linarith only [hℓpos])
  exact parent_core (Fv := fun ω => X.F Bd (parentSlabs c₂ CR) s 0 ω) (T := X.TRV ℓ)
    (G := fun ω => X.F Bd (parentSlabs c₂ CR) s 0 ω - X.TRV ℓ ω)
    (c' := CR * M * Q K A ℓ) (θ₁ := CR * Q K A s) (θ₂ := CS * M * Real.log (2 + ℓ) ^ 2)
    (by positivity) (by positivity) HR hE HS
    (aemeasurable_passTime 0 (ℓ • e₁)) (fun ω => ⟨hnn ω, le_rfl⟩)
    (by
      have h1 := mul_le_mul_of_nonneg_left hQsℓ (by positivity : (0 : ℝ) ≤ CR * M)
      linarith only [h1])
    (η := Q K A ℓ / 100) (by linarith only [hθ₁, hθ₂])

end IsotropicVariance.Paper.Proofs.Profiles
