/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.ProfileBounds
public import IsotropicVariance.Paper.Proofs.Profiles.Asymptotics
public import IsotropicVariance.Paper.Contracts.Profiles
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proposition `prop:profiles` for `s ≤ N/4`: the statement `ProfilesShortStatement`

The proof in the paper: the triangle inequality through `∓(s/16)e`, Lemma
`lem:tree` at `t = s/16`, the induction hypothesis `eq:premise` on the line of the centers, and
`|v − u| − (v − u)·e ≤ C Q_s` (`profile_passTime`); then equation `eq:slab` with `z` the center of
`I` for `P = S`.

* `profile_bounds_of`: both bounds at one length, from the two inputs; the proof for `N/4 < s ≤ N`
  uses it too, with another bound on the line.
* `exists_profile_thresholds`: what "for `N` large" means at lengths comparable to `N`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

universe u

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os Infra.Slab

variable {m : ℕ}

/-- The left side of equation `eq:slab` is a genuine supremum: `T_P − T ≤ b|y − x|` at every
pair. -/
lemma le_iSup_slabPair {X : Setting.{u} m} {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m)
    (z : Pt m) (hw : 0 ≤ sl.width) (ω : X.Ω) {x y : Pt m} (h : Contracts.IsSlabPair sl z x y) :
    X.slabTime b sl ω x y - X.passTime ω x y ≤
      ⨆ q : {q : Pt m × Pt m // Contracts.IsSlabPair sl z q.1 q.2},
        (X.slabTime b sl ω q.1.1 q.1.2 - X.passTime ω q.1.1 q.1.2) := by
  have hb0 : 0 ≤ b := upperBound_nonneg X hb ω
  have hface₀ : sl.face₀ ⊆ sl.set := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨hu.ge, by rw [mem_ofPred_eq.mp hu]; exact hw⟩, rfl⟩
  have hface₁ : sl.face₁ ⊆ sl.set := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨by rw [mem_ofPred_eq.mp hu]; exact hw, hu.le⟩, rfl⟩
  have hmem : ∀ {x y : Pt m}, Contracts.IsSlabPair sl z x y → x ∈ sl.set ∧ y ∈ sl.set := by
    rintro x y ⟨h' | h', -, -⟩
    · exact ⟨hface₀ h'.1, hface₁ h'.2⟩
    · exact ⟨hface₁ h'.1, hface₀ h'.2⟩
  have hbdd : BddAbove (range fun q : {q : Pt m × Pt m // Contracts.IsSlabPair sl z q.1 q.2} =>
      X.slabTime b sl ω q.1.1 q.1.2 - X.passTime ω q.1.1 q.1.2) := by
    refine ⟨b * (Real.sqrt 5 * sl.width), ?_⟩
    rintro _ ⟨⟨q, hq⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hmem hq
    have h3 := slabTime_le_mul_dist X hb sl ω h1 h2
    have h4 : dist q.1 q.2 ≤ Real.sqrt 5 * sl.width := by
      rw [dist_comm, dist_eq_norm]
      exact hq.2.2
    have h5 := mul_le_mul_of_nonneg_left h4 hb0
    have h6 := passTime_nonneg (X := X) ω q.1 q.2
    simp only
    linarith only [h3, h5, h6]
  exact le_ciSup hbdd (⟨(x, y), h⟩ : {q : Pt m × Pt m // Contracts.IsSlabPair sl z q.1 q.2})

/-- **Proposition `prop:profiles` at one length**: from Lemma
`lem:tree` at `t = s/16`, equation `eq:slab`, and a bound on `|T(a, b) − |b − a||` for `|b − a|`
between `7s/8` and `2s` (from `eq:premise` for `s ≤ N/4`, from `eq:parent` otherwise), the two
suprema of equation `eq:profiles` are `O_1(C Q_s)`. The thresholds are explicit hypotheses. -/
theorem profile_bounds_of (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {Bd : ℝ}
    (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd) {CS : ℝ} (hCS : 0 < CS)
    (hslab : ∀ (sl : Slab m) (z : Pt m), 2 < sl.width →
      (∀ ω, ∀ x y : Pt m, Contracts.IsSlabPair sl z x y →
        0 ≤ X.slabTime b sl ω x y - X.passTime ω x y) ∧
      Cited.IsOs X.P 1 (CS * Real.log (2 + sl.width) ^ 2) (fun ω =>
        ⨆ p : {p : Pt m × Pt m // Contracts.IsSlabPair sl z p.1 p.2},
          (X.slabTime b sl ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2)))
    {K : ℕ} (hK : 10 ≤ K) {A : ℝ} (hA : 1 ≤ A) {Ct Cl s : ℝ} (hs : 256 ≤ s) (hCt : 0 < Ct)
    (hCl : 0 < Cl) (hW : 4 * Real.sqrt m * W K A s ≤ s / 128)
    (hlog : CS * Real.log (2 + s) ^ 2 ≤ Q K A s)
    (htree : ∀ x e : Pt m, ‖e‖ = 1 → ∀ B : Set (Pt m), IsRectBox B (x + (s / 16) • e) →
      (∀ z ∈ B, ∀ z' ∈ B, dist z z' ≤ s / 16 / 8) →
      (∀ z ∈ B, infDist z (range fun r : ℝ => x + r • e) ≤
        16 * Real.sqrt (m + 1) * W K A (s / 16)) →
      IsOs X.P 1 (Ct * Q K A (s / 16))
        fun ω => ⨆ z : B, (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫))
    (hline : ∀ a c : Pt m, 7 / 8 * s ≤ dist a c → dist a c ≤ 2 * s →
      IsOs X.P 1 (Cl * Q K A s) fun ω => |X.passTime ω a c - dist a c|)
    (p : CubePair m) (hp : p.IsAdmissible s (W K A s) 1) :
    IsOs X.P 1 (profileConst m Ct Cl * Q K A s)
        (fun ω => ⨆ (u : p.first) (v : p.second), |X.passTime ω u v - dist (u : Pt m) v|) ∧
      IsOs X.P 1 ((profileConst m Ct Cl + 1) * Q K A s)
        (fun ω => ⨆ (u : p.first) (v : p.second),
          |X.slabTime b p.slab ω u v - dist (u : Pt m) v|) := by
  have hspos : 0 < s := by linarith only [hs]
  have hQ : 0 < Q K A s := Q_pos (by linarith only [hA]) hspos
  have hPC : 0 < profileConst m Ct Cl := by
    unfold profileConst
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have HT := profile_passTime X hBd hBd0 hK hA hs hCt hCl hW htree hline p hp
  refine ⟨HT, ?_⟩
  obtain ⟨hu_c, hv_c, hrs, hr32⟩ := cubePair_dists hp hspos hW
  obtain ⟨hdist, h1₀, -, h2₀, -, -⟩ := hp
  have hwidth : p.slab.width = s := hdist
  have hduv : ∀ u ∈ p.first, ∀ v ∈ p.second, dist u v ≤ 2 * s := fun u hu v hv => by
    have h := dist_triangle4 u p.center₁ p.center₂ v
    rw [dist_comm p.center₂ v] at h
    linarith only [h, hu_c u hu, hv_c v hv, hr32, hspos]
  have hsqrt5 : 2 ≤ Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpair : ∀ u ∈ p.first, ∀ v ∈ p.second, Contracts.IsSlabPair p.slab p.center₁ u v :=
    fun u hu v hv => ⟨Or.inl ⟨cubePair_first_subset_face₀ p hu, cubePair_second_subset_face₁ p hv⟩,
      by
        rw [← dist_eq_norm, hwidth]
        linarith only [hu_c u hu, hspos],
      by
        rw [← dist_eq_norm, dist_comm, hwidth]
        have := mul_le_mul_of_nonneg_right hsqrt5 hspos.le
        linarith only [this, hduv u hu v hv]⟩
  obtain ⟨hnn, HS⟩ := hslab p.slab p.center₁ (by rw [hwidth]; linarith only [hs])
  rw [hwidth] at HS
  have hlogpos : 0 < Real.log (2 + s) := Real.log_pos (by linarith only [hspos])
  have HD := profile_slabTime hb hBd hBd0 p.slab
    (cubePair_first_subset_set p (by rw [hdist]; exact hspos.le))
    (cubePair_second_subset_set p (by rw [hdist]; exact hspos.le))
    ⟨_, cubePair_center₁_mem p h1₀⟩ ⟨_, cubePair_center₂_mem p h2₀⟩ hduv
    (by positivity) (by positivity) HT HS
    fun ω u hu v hv =>
      ⟨le_iSup_slabPair hb p.slab p.center₁ (by rw [hwidth]; exact hspos.le) ω (hpair u hu v hv),
        hnn ω u v (hpair u hu v hv)⟩
  refine IsOs.mono_scale HD zero_le_one (by positivity) ?_
  have e1 : (profileConst m Ct Cl + 1) * Q K A s =
      profileConst m Ct Cl * Q K A s + Q K A s := by ring
  rw [e1]
  linarith only [hlog]

/-- "For `N` large", at lengths comparable to `N`: `s ≥ 256`, `4√m W_s ≤ s/128` and
`C log²(2 + s) ≤ Q_s`. -/
lemma exists_profile_thresholds (m : ℕ) (Cstar CS c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ N₀ : ℝ, ∀ K : ℕ, 10 ≤ K → ∀ A N : ℝ, 1 ≤ A → N₀ ≤ N → Regime Cstar K A N →
      ∀ s : ℝ, c₁ * N ≤ s → s ≤ N →
        256 ≤ s ∧ 4 * Real.sqrt m * W K A s ≤ s / 128 ∧ CS * Real.log (2 + s) ^ 2 ≤ Q K A s := by
  have hε : 0 < 1 / (512 * (Real.sqrt m + 1)) := by positivity
  obtain ⟨NW, hNW⟩ := exists_W_le Cstar c₁ _ hc₁ hε
  obtain ⟨NL, hNL⟩ := exists_log_le CS c₁ hc₁
  refine ⟨max (max NW NL) (256 / c₁), fun K hK A N hA hN hReg s hs1 hs2 => ?_⟩
  obtain ⟨hN1, hNc⟩ := max_le_iff.mp hN
  obtain ⟨hNW', hNL'⟩ := max_le_iff.mp hN1
  have hs256 : 256 ≤ s := by
    have h := mul_le_mul_of_nonneg_left hNc hc₁.le
    rw [mul_div_cancel₀ _ hc₁.ne'] at h
    linarith only [h, hs1]
  have hspos : 0 < s := by linarith only [hs256]
  have hsqm := Real.sqrt_nonneg (m : ℝ)
  refine ⟨hs256, ?_, ?_⟩
  · have h := hNW K hK A N (by linarith only [hA]) hNW' hReg s hs1 hs2
    calc 4 * Real.sqrt m * W K A s ≤ 4 * Real.sqrt m * (1 / (512 * (Real.sqrt m + 1)) * s) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = s / 128 * (Real.sqrt m / (Real.sqrt m + 1)) := by field_simp; ring
      _ ≤ s / 128 * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).mpr (by linarith only [hsqm])) (by positivity)
      _ = s / 128 := mul_one _
  · have h1 := hNL K hK A N hA hNL' s hs1
    have h2 : Real.log (2 + s) ≤ Real.log (2 + N) :=
      Real.log_le_log (by linarith only [hspos]) (by linarith only [hs2])
    have h3 : Real.log (2 + s) ^ 2 ≤ Real.log (2 + N) ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith only [hspos])) h2 2
    by_cases hCS : 0 ≤ CS
    · exact (mul_le_mul_of_nonneg_left h3 hCS).trans h1
    · have h4 : 0 ≤ Q K A s := Q_nonneg (by linarith only [hA]) hspos.le
      have h5 : CS * Real.log (2 + s) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_le.mp hCS).le (sq_nonneg _)
      exact h5.trans h4

/-- The inputs of `profile_bounds_of` on the line: `eq:premise`, for `r ± s/8 ≤ 2s ≤ N/2`
(the proof of Proposition `prop:profiles` for `s ≤ N/4`). -/
lemma line_of_premise {X : Setting.{u} m} (hm : 1 ≤ m) {K : ℕ} (hK : 10 ≤ K) {A N : ℝ}
    (hA : 1 ≤ A) (hP : Premise X K A N) {s : ℝ} (hs : 8 ≤ s) (hsN : s ≤ N / 4) (a c : Pt m)
    (h1 : 7 / 8 * s ≤ dist a c) (h2 : dist a c ≤ 2 * s) :
    IsOs X.P 1 (2 * Q K A s) fun ω => |X.passTime ω a c - dist a c| :=
  (lineAbs_of_premise hm hP a c (by linarith only [hs, h1])
    (by linarith only [h2, hsN])).mono_scale zero_le_one
    (Q_pos (by linarith only [hA]) (by linarith only [hs, h1]))
    (Q_le_two_mul hK (by linarith only [hA]) (by linarith only [hs]) dist_nonneg h2)

/-- **The first part of the proof of Proposition `prop:profiles`**:
equation `eq:profiles` for `s ≤ N/4`, from Lemma `lem:tree` and Lemma `lem:slab`. -/
theorem profilesShortStatement_of (hT : Contracts.TreeStatement.{u})
    (hS : Contracts.SlabStatement.{u}) : Contracts.ProfilesShortStatement.{u} := by
  intro m hm X hX b hb Cstar _
  obtain ⟨Bd, hBd0, hBd⟩ := exists_upperBound X
  obtain ⟨Ct, hCt, hT'⟩ := hT m hm X hX
  obtain ⟨CS, hCS, hS', -⟩ := hS m hm X hX b hb
  have hC : 0 < profileConst m Ct 2 := by
    unfold profileConst
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  refine ⟨profileConst m Ct 2 + 1, by positivity, fun c₁ hc₁ K => ?_⟩
  obtain ⟨N₀, hN₀⟩ := exists_profile_thresholds m Cstar CS c₁ hc₁
  refine ⟨N₀, fun A N hN hst s hs1 hs2 p hp => ?_⟩
  obtain ⟨hK, hA, hN2, hP, hReg⟩ := hst
  obtain ⟨hs256, hW, hlog⟩ := hN₀ K hK A N hA hN hReg s hs1 (by linarith only [hs2, hN2])
  obtain ⟨HT, HD⟩ := profile_bounds_of X hb hBd hBd0.le hCS hS' hK hA hs256 hCt two_pos hW hlog
    (fun x e he B hB hdiam hline => hT' K A N hK hA hN2 hP (s / 16) (by linarith only [hs256])
      (by linarith only [hs2, hs256]) x e he B hB hdiam hline)
    (line_of_premise hm hK hA hP (by linarith only [hs256]) hs2) p hp
  have hQ : 0 < Q K A s := Q_pos (by linarith only [hA]) (by linarith only [hs256])
  exact ⟨HT.mono_scale zero_le_one (by positivity) (by linarith only [hQ]), HD⟩

end IsotropicVariance.Paper.Proofs.Profiles
