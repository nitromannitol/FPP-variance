/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.RowEnergy
public import IsotropicVariance.Paper.Proofs.Profiles.ProfilesShort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:rowenergy`: the statement `RowEnergyStatement`

The proof in the paper. The arrays over the cubes and the union over the sequences
of cubes are `rowEnergy_bound`, with Proposition `prop:profiles` for the `i`th slab as the input.
It bounds `|F − ℓ| + Q_s Σ_i |k_i − k_{i−1}|²`, with `k_i` the index of the cube containing `x_i`.
The last display of the proof, that is `move_sq_le`, turns this into
equation `eq:rowenergy`.
-/

@[expose] public section

open MeasureTheory Set Metric

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os Infra.Slab

variable {m : ℕ}

lemma sq_sub_le_floor (a b : ℝ) : (b - a) ^ 2 ≤ 2 * (((⌊b⌋ : ℝ) - ⌊a⌋) ^ 2 + 1) := by
  obtain ⟨h₁, h₂⟩ := floor_sub_floor_close a b
  linarith only [sq_le_two_mul_sq_add_two h₁ h₂]

/-- **The last display of the proof of Lemma `lem:rowenergy`**: for points
`x`, `y` at distance `s` along `e₁`, in the cubes with indices `j`, `k`,
`|y − x − s e₁|² ≤ 2 W² (|k − j|² + d − 1)`. -/
lemma move_sq_le {x y : Pt m} {s W : ℝ} (hW : 0 < W) (hlon : Pt.lon y - Pt.lon x = s)
    {j k : Fin m → ℤ} (hj : ∀ l, j l = ⌊Pt.tr x l / W⌋) (hk : ∀ l, k l = ⌊Pt.tr y l / W⌋) :
    ‖y - x - s • (e₁ : Pt m)‖ ^ 2 ≤ 2 * W ^ 2 * (zNorm (k - j) ^ 2 + m) := by
  have hl : ∀ l, (Pt.tr y l - Pt.tr x l) ^ 2 ≤ 2 * W ^ 2 * (((k l : ℝ) - j l) ^ 2 + 1) := by
    intro l
    have h₁ := sq_sub_le_floor (Pt.tr x l / W) (Pt.tr y l / W)
    rw [← hj l, ← hk l] at h₁
    have e : Pt.tr y l - Pt.tr x l = W * (Pt.tr y l / W - Pt.tr x l / W) := by
      field_simp
    rw [e, mul_pow]
    have := mul_le_mul_of_nonneg_left h₁ (sq_nonneg W)
    linarith only [this]
  rw [norm_sub_sub_smul_sq hlon, zNorm_sub_sq]
  calc ∑ l, (Pt.tr y l - Pt.tr x l) ^ 2
      ≤ ∑ l, 2 * W ^ 2 * (((k l : ℝ) - j l) ^ 2 + 1) :=
        Finset.sum_le_sum fun l _ => hl l
    _ = 2 * W ^ 2 * (∑ l, ((k l : ℝ) - j l) ^ 2 + m) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        simp

/-- The sum of the moves of the minimizing points is at most twice the sum over their indices, up
to `2(d − 1) M q`, where `W² = sq`. -/
lemma moves_le (X : Setting.{u} m) (b : ℝ) {M : ℕ} {s q W : ℝ} (hs : 0 < s) (hW : 0 < W)
    (hW2 : W ^ 2 = s * q) (ω : X.Ω) :
    s⁻¹ * ∑ i : Fin M, ‖lexMinimizer b (X.ρ ω) M s 0 i.succ -
          lexMinimizer b (X.ρ ω) M s 0 i.castSucc - s • e₁‖ ^ 2 ≤
      2 * (q * ∑ i : Fin M, zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2) +
        2 * m * M * q := by
  have hmove : ∀ i : Fin M, ‖lexMinimizer b (X.ρ ω) M s 0 i.succ -
      lexMinimizer b (X.ρ ω) M s 0 i.castSucc - s • e₁‖ ^ 2 ≤
        2 * W ^ 2 * (zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2 + m) :=
    fun i => move_sq_le hW (lon_lexMinimizer_succ_sub X hs.le ω i)
      (J_apply X hW ω i.castSucc) (J_apply X hW ω i.succ)
  have hs' : s⁻¹ * s = 1 := inv_mul_cancel₀ hs.ne'
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  calc ∑ i : Fin M, s⁻¹ * ‖lexMinimizer b (X.ρ ω) M s 0 i.succ -
          lexMinimizer b (X.ρ ω) M s 0 i.castSucc - s • e₁‖ ^ 2
      ≤ ∑ i : Fin M, (2 * (q * zNorm (X.J b M s W 0 ω i.succ -
          X.J b M s W 0 ω i.castSucc) ^ 2) + 2 * m * q) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := mul_le_mul_of_nonneg_left (hmove i) (inv_pos.2 hs).le
        rw [hW2] at h
        refine h.trans_eq ?_
        calc _ = (s⁻¹ * s) * (2 * q * (zNorm (X.J b M s W 0 ω i.succ -
              X.J b M s W 0 ω i.castSucc) ^ 2 + m)) := by ring
          _ = _ := by rw [hs']; ring
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

lemma aemeasurable_rowMoves (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ}
    {s : ℝ} (hs : 0 < s) (c : ℝ) :
    AEMeasurable (fun ω => |X.F b M s 0 ω - M * s| + s⁻¹ * ∑ i : Fin M,
      ‖lexMinimizer b (X.ρ ω) M s 0 i.succ - lexMinimizer b (X.ρ ω) M s 0 i.castSucc -
        s • e₁‖ ^ 2 - c) X.P := by
  obtain ⟨g, hg, Fv, hFv, hae⟩ := Infra.Slab.exists_measurable_lexMinimizer_ae X hb hs 0 M
  have hΦ : Measurable fun x : Fin (M + 1) → Pt m =>
      s⁻¹ * ∑ i : Fin M, ‖x i.succ - x i.castSucc - s • (e₁ : Pt m)‖ ^ 2 :=
    Continuous.measurable (by fun_prop)
  have hF : Measurable fun ω => |Fv ω - M * s| :=
    continuous_abs.measurable.comp (hFv.sub_const _)
  refine ⟨fun ω => |Fv ω - M * s| + (s⁻¹ * ∑ i : Fin M,
    ‖g ω i.succ - g ω i.castSucc - s • (e₁ : Pt m)‖ ^ 2) - c,
    (hF.add (hΦ.comp hg)).sub_const c, hae.mono fun ω h => ?_⟩
  simp only [h.1, h.2]

/-- **Equation `eq:rowenergy` at one length**, from the bound on the cubes: `rowEnergy_bound`
followed by the last display of the proof. -/
theorem rowEnergy_moves (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ} {s W q θ : ℝ}
    (hs : 0 < s) (hW : 0 < W) (hWm : 4 * Real.sqrt m * W ≤ s) (hWq : W ^ 2 = s * q)
    (hq : 0 < q) (hθ : 0 < θ)
    (hprof : ∀ (i : ℕ) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 → IsOs X.P 1 θ fun ω =>
      ⨆ (u : (gridPair s W i j k).first) (v : (gridPair s W i j k).second),
        |X.slabTime b (gridPair s W i j k).slab ω u v - dist (u : Pt m) v|) :
    IsOs X.P 1 (2 * (13 * θ + 12 * θ)) fun ω => |X.F b M s 0 ω - M * s| + s⁻¹ * ∑ i : Fin M,
      ‖lexMinimizer b (X.ρ ω) M s 0 i.succ - lexMinimizer b (X.ρ ω) M s 0 i.castSucc -
        s • e₁‖ ^ 2 - (2 * (25 * (θ * M * penaltyLog (q / (12 * θ)) m) + 12 * (m / 3 * M * q)) +
          2 * m * M * q) := by
  have H := rowEnergy_bound X hb (M := M) hs hW hWm hWq hq hθ hprof
  have H2 := (isOs_mul_iff (a := 2) two_pos).mpr H
  refine IsOs.mono H2 zero_le_one (by positivity) (aemeasurable_rowMoves X hb hs _)
    (ae_of_all _ fun ω => ?_)
  have h1 := moves_le X b (M := M) hs hW hWq ω
  have h2 := abs_nonneg (X.F b M s 0 ω - M * s)
  simp only
  linarith only [h1, h2]

/-- **Lemma `lem:rowenergy`, equation `eq:rowenergy`**, from
Proposition `prop:profiles` for `s ≤ N/4`, the only result that its proof cites, with `P = S` the
`i`th slab. -/
theorem rowEnergyStatement_of (hP : Contracts.ProfilesShortStatement.{u}) :
    Contracts.RowEnergyStatement.{u} := by
  intro m hm X hX b hb Cstar hCstar
  obtain ⟨CP, hCP, hP'⟩ := hP m hm X hX b hb Cstar hCstar
  set pL := penaltyLog (1 / (12 * CP)) m with hpL
  have hpL0 : 0 < pL := penaltyLog_pos (by positivity) m
  refine ⟨50 * CP * (pL + 1) + 10 * m + 1, by positivity, fun c₁ hc₁ K => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hP' c₁ hc₁ K
  obtain ⟨N₂, hN₂⟩ := exists_profile_thresholds m Cstar 0 c₁ hc₁
  refine ⟨max N₁ N₂, fun A N hN hst M s _ hs1 hs2 => ?_⟩
  obtain ⟨hK, hA, hN2, -, hReg⟩ := id hst
  obtain ⟨hs256, hW, -⟩ := hN₂ K hK A N hA (le_trans (le_max_right _ _) hN) hReg s hs1
    (by linarith only [hs2, hN2])
  have hspos : 0 < s := by linarith only [hs256]
  have hQ : 0 < Q K A s := Q_pos (by linarith only [hA]) hspos
  have hWpos : 0 < W K A s := Real.sqrt_pos.mpr (mul_pos hspos hQ)
  have H := rowEnergy_moves X hb (M := M) (q := Q K A s) (θ := CP * Q K A s) hspos hWpos
    (by linarith only [hW, hs256]) (W_sq (by linarith only [hA]) hspos.le) hQ (by positivity)
    fun i j k h => (hN₁ A N (le_trans (le_max_left _ _) hN) hst s hs1 hs2 _
      (gridPair_isAdmissible hspos hWpos.le h)).2
  have hc : Q K A s / (12 * (CP * Q K A s)) = 1 / (12 * CP) := by
    field_simp
  rw [hc, ← hpL] at H
  have hMq : 0 ≤ (M : ℝ) * Q K A s := by positivity
  have hCq : 0 ≤ (50 * CP + 1) * ((M : ℝ) * Q K A s) := by positivity
  refine (IsOs.mono H zero_le_one (by positivity) (aemeasurable_rowMoves X hb hspos _)
    (ae_of_all _ fun ω => ?_)).mono_scale zero_le_one (by positivity) ?_
  · have e1 : 2 * (25 * (CP * Q K A s * M * pL) + 12 * (m / 3 * M * Q K A s)) +
        2 * m * M * Q K A s + (50 * CP + 1) * ((M : ℝ) * Q K A s) =
        (50 * CP * (pL + 1) + 10 * m + 1) * M * Q K A s := by ring
    simp only
    linarith only [e1, hCq]
  · have e2 : (50 * CP * (pL + 1) + 10 * m + 1) * Q K A s =
        2 * (13 * (CP * Q K A s) + 12 * (CP * Q K A s)) +
          (50 * CP * pL + 10 * m + 1) * Q K A s := by
      ring
    have e3 : 0 ≤ (50 * CP * pL + 10 * m + 1) * Q K A s := by positivity
    linarith only [e2, e3]

end IsotropicVariance.Paper.Proofs.Profiles
