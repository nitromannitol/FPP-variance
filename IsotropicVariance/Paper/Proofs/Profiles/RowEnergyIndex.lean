/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Profiles
import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
import IsotropicVariance.Infra.Os.Basic
import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry
import IsotropicVariance.Paper.Proofs.Profiles.RowEnergy
import IsotropicVariance.Paper.Proofs.Profiles.TreeGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Equation `eq:rowenergy` in the indices of the cubes

Lemma `lem:rowenergy` bounds the penalty `s⁻¹ Σ_i |x_i − x_{i−1} − s e₁|²`. The proofs that count
cubes use the penalty `Q_s Σ_i |J_i − J_{i−1}|²` of the indices of the cubes containing the `x_i`.
`RowEnergyIndexStatement` is the equation with that penalty, an internal statement (the paper has no
indices `J_i`), and `rowEnergyIndexStatement_of_rowEnergy` derives it from the lemma, with other
constants. The comparison of the two penalties is the converse of the last display of the proof of
the lemma:
`s Q_s |J_i − J_{i−1}|² ≤ 2 |x_i − x_{i−1} − s e₁|² + 2 s Q_s (d − 1)` (`index_move_le`).
-/

@[expose] public section

open MeasureTheory

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os Contracts

variable {m : ℕ}

/-- **Equation `eq:rowenergy` in the indices of the cubes**: for every `M ≥ 1` and every width
`c₁N ≤ s ≤ N/4`, `|F − Ms| + Q_s Σ_{i=1}^M |J_i − J_{i−1}|² ≤ C M Q_s + O_1(C Q_s)`, with `C`
independent of `M`. -/
def RowEnergyIndexStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ (M : ℕ) (s : ℝ), 1 ≤ M →
        c₁ * N ≤ s → s ≤ N / 4 →
          Cited.IsOs X.P 1 (C * Q K A s) (fun ω =>
            |X.F b M s 0 ω - M * s| +
              Q K A s * ∑ i : Fin M,
                zNorm (X.J b M s (W K A s) 0 ω i.succ -
                  X.J b M s (W K A s) 0 ω i.castSucc) ^ 2 -
              C * M * Q K A s)

private lemma sq_floor_sub_le (a b : ℝ) : ((⌊b⌋ : ℝ) - ⌊a⌋) ^ 2 ≤ 2 * (b - a) ^ 2 + 2 := by
  obtain ⟨h₁, h₂⟩ := floor_sub_floor_close a b
  exact sq_le_two_mul_sq_add_two (by linarith only [h₂]) (by linarith only [h₁])

/-- The comparison of the indices of two cubes with the transverse move between their points. -/
private lemma index_move_le {x y : Pt m} {s W : ℝ} (hW : 0 < W) (hlon : Pt.lon y - Pt.lon x = s)
    {j k : Fin m → ℤ} (hj : ∀ l, j l = ⌊Pt.tr x l / W⌋) (hk : ∀ l, k l = ⌊Pt.tr y l / W⌋) :
    W ^ 2 * zNorm (k - j) ^ 2 ≤ 2 * ‖y - x - s • (e₁ : Pt m)‖ ^ 2 + 2 * W ^ 2 * m := by
  have hl : ∀ l, W ^ 2 * ((k l : ℝ) - j l) ^ 2 ≤ 2 * (Pt.tr y l - Pt.tr x l) ^ 2 + 2 * W ^ 2 := by
    intro l
    have h₂ := sq_floor_sub_le (Pt.tr x l / W) (Pt.tr y l / W)
    rw [← hj l, ← hk l] at h₂
    have e : Pt.tr y l - Pt.tr x l = W * (Pt.tr y l / W - Pt.tr x l / W) := by
      field_simp
    rw [e, mul_pow]
    have := mul_le_mul_of_nonneg_left h₂ (sq_nonneg W)
    linarith only [this]
  rw [norm_sub_sub_smul_sq hlon, zNorm_sub_sq]
  calc W ^ 2 * ∑ l, ((k l : ℝ) - j l) ^ 2
      = ∑ l, W ^ 2 * ((k l : ℝ) - j l) ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ l, (2 * (Pt.tr y l - Pt.tr x l) ^ 2 + 2 * W ^ 2) :=
        Finset.sum_le_sum fun l _ => hl l
    _ = 2 * ∑ l, (Pt.tr y l - Pt.tr x l) ^ 2 + 2 * W ^ 2 * m := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [mul_comm]

/-- The penalty of the indices along the minimizing points is at most twice the penalty of the
moves, up to `2(d − 1) M q`, where `W² = sq`. -/
private lemma index_penalty_le (X : Setting.{u} m) (b : ℝ) {M : ℕ} {s q W : ℝ} (hs : 0 < s)
    (hW : 0 < W) (hW2 : W ^ 2 = s * q) (ω : X.Ω) :
    q * ∑ i : Fin M, zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2 ≤
      2 * (s⁻¹ * ∑ i : Fin M, ‖lexMinimizer b (X.ρ ω) M s 0 i.succ -
        lexMinimizer b (X.ρ ω) M s 0 i.castSucc - s • e₁‖ ^ 2) + 2 * m * M * q := by
  have hmove : ∀ i : Fin M,
      W ^ 2 * zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2 ≤
        2 * ‖lexMinimizer b (X.ρ ω) M s 0 i.succ -
          lexMinimizer b (X.ρ ω) M s 0 i.castSucc - s • e₁‖ ^ 2 + 2 * W ^ 2 * m :=
    fun i => index_move_le hW (lon_lexMinimizer_succ_sub X hs.le ω i)
      (J_apply X hW ω i.castSucc) (J_apply X hW ω i.succ)
  have hs' : s⁻¹ * s = 1 := inv_mul_cancel₀ hs.ne'
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  calc ∑ i : Fin M, q * zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2
      ≤ ∑ i : Fin M, (2 * (s⁻¹ * ‖lexMinimizer b (X.ρ ω) M s 0 i.succ -
          lexMinimizer b (X.ρ ω) M s 0 i.castSucc - s • e₁‖ ^ 2) + 2 * m * q) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := mul_le_mul_of_nonneg_left (hmove i) (inv_pos.2 hs).le
        rw [hW2] at h
        calc _ = (s⁻¹ * s) * (q * zNorm (X.J b M s W 0 ω i.succ -
              X.J b M s W 0 ω i.castSucc) ^ 2) := by rw [hs']; ring
          _ = s⁻¹ * (s * q * zNorm (X.J b M s W 0 ω i.succ -
              X.J b M s W 0 ω i.castSucc) ^ 2) := by ring
          _ ≤ _ := h
          _ = (2 * (s⁻¹ * ‖lexMinimizer b (X.ρ ω) M s 0 i.succ -
              lexMinimizer b (X.ρ ω) M s 0 i.castSucc - s • e₁‖ ^ 2) +
                (s⁻¹ * s) * (2 * m * q)) := by ring
          _ = _ := by rw [hs']; ring
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The transfer of an `O_1` bound from one penalty to a comparable one. -/
private lemma isOs_transfer {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E pen pen' : Ω → ℝ}
    {C q a : ℝ} (hC : 0 < C) (hq : 0 < q) (ha : 0 ≤ a) (hE : ∀ ω, 0 ≤ E ω)
    (h : Cited.IsOs P 1 (C * q) (fun ω => E ω + pen ω - C * a * q))
    (hmeas : AEMeasurable (fun ω => E ω + pen' ω - (2 * C + 2 * m) * a * q) P)
    (hpen : ∀ ω, pen' ω ≤ 2 * pen ω + 2 * m * a * q) :
    Cited.IsOs P 1 ((2 * C + 2 * m) * q) (fun ω => E ω + pen' ω - (2 * C + 2 * m) * a * q) := by
  have h₂ := (isOs_mul_iff (a := 2) two_pos).2 h
  refine IsOs.mono_scale (IsOs.mono h₂ zero_le_one (by positivity) hmeas
    (Filter.Eventually.of_forall fun ω => ?_)) zero_le_one (by positivity) ?_
  · have h₁ := hE ω
    have h₃ := hpen ω
    have : 0 ≤ m * a * q := by positivity
    simp only
    linarith
  · nlinarith [(by positivity : (0 : ℝ) ≤ m * q)]

private lemma scales_pos {K : ℕ} {A N s c₁ : ℝ} (hA : 1 ≤ A) (hN : 2 ≤ N) (hc₁ : 0 < c₁)
    (hs : c₁ * N ≤ s) :
    0 < s ∧ 0 < Q K A s ∧ 0 < W K A s ∧ W K A s ^ 2 = s * Q K A s := by
  have hs₀ : 0 < s := lt_of_lt_of_le (mul_pos hc₁ (by linarith)) hs
  have hq : 0 < Q K A s := mul_pos (by linarith) (Real.rpow_pos_of_pos hs₀ _)
  exact ⟨hs₀, hq, Real.sqrt_pos.2 (mul_pos hs₀ hq), Real.sq_sqrt (mul_pos hs₀ hq).le⟩

/-- The form of Lemma `lem:rowenergy` in the indices, from the lemma. -/
theorem rowEnergyIndexStatement_of_rowEnergy (h : RowEnergyStatement.{u}) :
    RowEnergyIndexStatement.{u} := by
  intro m hm X hX b hb Cstar hCstar
  obtain ⟨C, hC, H⟩ := h m hm X hX b hb Cstar hCstar
  refine ⟨2 * C + 2 * m, by positivity, fun c₁ hc₁ K => ?_⟩
  obtain ⟨N₀, hN₀⟩ := H c₁ hc₁ K
  refine ⟨N₀, fun A N hN hst M s hM hs₁ hs₂ => ?_⟩
  obtain ⟨hs, hq, hW, hW2⟩ := scales_pos (K := K) hst.2.1 hst.2.2.1 hc₁ hs₁
  exact isOs_transfer (a := (M : ℝ)) hC hq (by positivity) (fun ω => abs_nonneg _)
    (hN₀ A N hN hst M s hM hs₁ hs₂) (aemeasurable_rowSum X hb hs _)
    fun ω => index_penalty_le X b hs hW hW2 ω

end IsotropicVariance.Paper.Proofs.Profiles
