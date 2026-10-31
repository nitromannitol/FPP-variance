/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusReroute
public import IsotropicVariance.Paper.Proofs.Modulus.ModulusEvent
public import IsotropicVariance.Paper.Proofs.Modulus.SmallFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:modulus`, equation `eq:modulus`

The proof of Lemma `lem:modulus` in the paper, for `T_S`, with `h = γ³`.

* `eLpNorm_modulus_phi_le`: equation `eq:localization` and equation `eq:profiles`, at the lengths
  `n` and `γn`, bound the `L^{8d}` norm of `Z` by the three terms of the last display of the
  proof.
* `log_card_box_le_log`, `tail_le`, `euclid_terms_le`, `exists_gamma_le`: the arithmetic of
  the last paragraph of the proof.
* `modulus_pair_le_eta`: equation `eq:modulus` for one pair, from the last display and the closing
  line of the proof.
* `modulusStatement_of`: equation `eq:modulus` from equations `eq:profiles` and `eq:localization`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Modulus

open Cited Infra.Os

variable {m : ℕ}

/-! ## The arithmetic -/

/-- The constant of the logarithm of the number of pairs of cubes. -/
noncomputable def logConst (m : ℕ) : ℝ :=
  (Real.log 6 + 2 * m * Real.log (2 * (3 / 2 + 4 * Real.sqrt m + 2) + 1)) / Real.log 2 + 4 * m

/-- `log(2 + #pairs) ≤ C log(2/γ)`: at most `Cγ^{−4d}` pairs of cubes. -/
lemma log_card_box_le_log (m : ℕ) {h : ℝ} (hh : 0 < h) (h8 : h ≤ 1 / 8) :
    Real.log (2 + 4 * ((box m (boxRadius m h)).card : ℝ) ^ 2) ≤
      logConst m * Real.log (2 / cutRatio h) := by
  have hlog := log_card_box_le m hh h8
  have hγ : 0 < cutRatio h := cutRatio_pos hh
  have hγ1 : cutRatio h ≤ 1 := (cutRatio_le_half hh h8).trans (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlγ : Real.log (cutRatio h) ≤ 0 := Real.log_nonpos hγ.le hγ1
  rw [logConst, Real.log_div two_ne_zero hγ.ne']
  have hsq := Real.sqrt_nonneg (m : ℝ)
  have hc₀ : 0 ≤ Real.log 6 + 2 * m * Real.log (2 * (3 / 2 + 4 * Real.sqrt m + 2) + 1) :=
    add_nonneg (Real.log_nonneg (by norm_num))
      (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg m))
        (Real.log_nonneg (by linarith only [hsq])))
  set c₀ := Real.log 6 + 2 * m * Real.log (2 * (3 / 2 + 4 * Real.sqrt m + 2) + 1)
  have h1 : c₀ ≤ c₀ / Real.log 2 * (Real.log 2 - Real.log (cutRatio h)) := by
    calc c₀ = c₀ / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hlγ]) (div_nonneg hc₀ hl2.le)
  have hm : (0 : ℝ) ≤ 4 * m := mul_nonneg (by norm_num) (Nat.cast_nonneg m)
  have h2 := mul_le_mul_of_nonneg_left (show -Real.log (cutRatio h) ≤
    Real.log 2 - Real.log (cutRatio h) by linarith only [hl2]) hm
  have e : (c₀ / Real.log 2 + 4 * m) * (Real.log 2 - Real.log (cutRatio h)) =
      c₀ / Real.log 2 * (Real.log 2 - Real.log (cutRatio h)) +
        4 * m * (Real.log 2 - Real.log (cutRatio h)) := by ring
  rw [e]
  linarith only [hlog, h1, h2]

/-- `(2e^{−t²})^{1/(2k)} ≤ 2e^{−t²/(2k)}`. -/
lemma tail_le (t : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (2 * Real.exp (-t ^ 2)) ^ (1 / (2 * (k : ℝ))) ≤ 2 * Real.exp (-(t ^ 2 / (2 * k))) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith only [hk1]
  rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
  have h2 : (2 : ℝ) ^ (1 / (2 * (k : ℝ))) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / (2 * (k : ℝ))) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            rw [div_le_iff₀ (by positivity)]
            linarith only [hk1])
      _ = 2 := Real.rpow_one 2
  rw [show -t ^ 2 * (1 / (2 * (k : ℝ))) = -(t ^ 2 / (2 * k)) by ring]
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-- The `φ` terms, with the slack `3`: "`1 ≤ γQ_n`" and "at most `CγQ_n`". -/
lemma euclid_terms_le {γ n Wn Qn s : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hn : 0 < n) (hs : 0 ≤ s)
    (hQ : 0 ≤ Qn) (hW : Wn ^ 2 = n * Qn) (hQ1 : 1 ≤ γ * Qn) :
    3 + (4 * (γ⁻¹ * Wn + 2 * (2 * s * Wn)) / (γ * n) * (γ ^ 3 * Wn) +
        8 * (2 * s * Wn) / n * (γ ^ 3 * Wn)) ≤ (7 + 32 * s) * γ * Qn := by
  have hWQ : Wn ^ 2 / n = Qn := by rw [hW]; field_simp
  have e1 : 4 * (γ⁻¹ * Wn + 2 * (2 * s * Wn)) / (γ * n) * (γ ^ 3 * Wn) =
      (4 * γ + 16 * s * γ ^ 2) * (Wn ^ 2 / n) := by
    field_simp
    ring
  have e2 : 8 * (2 * s * Wn) / n * (γ ^ 3 * Wn) = 16 * s * γ ^ 3 * (Wn ^ 2 / n) := by
    field_simp
    ring
  rw [e1, e2, hWQ]
  have hsQ : 0 ≤ s * Qn := mul_nonneg hs hQ
  have h2 : γ ^ 2 ≤ γ := pow_le_of_le_one hγ.le hγ1 two_ne_zero
  have h3 : γ ^ 3 ≤ γ := pow_le_of_le_one hγ.le hγ1 three_ne_zero
  have t2 := mul_le_mul_of_nonneg_right h2 hsQ
  have t3 := mul_le_mul_of_nonneg_right h3 hsQ
  linarith only [hQ1, t2, t3]

private lemma euclid_terms_nonneg {γ n Wn s : ℝ} (hγ : 0 < γ) (hn : 0 < n) (hW : 0 < Wn)
    (hs : 0 ≤ s) :
    0 ≤ 3 + (4 * (γ⁻¹ * Wn + 2 * (2 * s * Wn)) / (γ * n) * (γ ^ 3 * Wn) +
        8 * (2 * s * Wn) / n * (γ ^ 3 * Wn)) := by
  positivity

/-- The closing line of the proof of Lemma `lem:modulus`: the factor of `Q_n` is small for `γ`
small. -/
theorem exists_gamma_le (C : ℝ) {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 4 ∧
      C * (Real.exp (-(c * γ⁻¹ ^ 2)) + γ ^ (2 / 5 : ℝ) * Real.log (2 / γ) + γ) ≤ η := by
  let g : ℝ → ℝ := fun γ => Real.exp (-(c * γ⁻¹ ^ 2)) +
    (Real.log 2 * γ ^ (2 / 5 : ℝ) - Real.log γ * γ ^ (2 / 5 : ℝ)) + γ
  have hg : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun γ : ℝ => Real.exp (-(c * γ⁻¹ ^ 2))) (𝓝[>] 0) (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (((tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero).const_mul_atTop hc)
    have h1 : Tendsto (fun γ : ℝ => γ ^ (2 / 5 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (2 / 5) (Or.inr (by norm_num))).tendsto
      rw [Real.zero_rpow (by norm_num)] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := tendsto_log_mul_rpow_nhdsGT_zero (r := 2 / 5) (by norm_num)
    have h3 : Tendsto (fun γ : ℝ => γ) (𝓝[>] 0) (𝓝 0) :=
      (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
    have := (h0.add ((h1.const_mul (Real.log 2)).sub h2)).add h3
    simpa only [mul_zero, sub_zero, add_zero] using this
  have hC : Tendsto (fun γ => C * g γ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hg.const_mul C
  have hev := (tendsto_order.1 hC).2 η hη
  have h4 : Ioo (0 : ℝ) (1 / 4) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨γ, hγη, hγ0, hγ4⟩ := (hev.and h4).exists
  refine ⟨γ, hγ0, hγ4, ?_⟩
  have e : Real.exp (-(c * γ⁻¹ ^ 2)) + γ ^ (2 / 5 : ℝ) * Real.log (2 / γ) + γ = g γ := by
    simp only [g]
    rw [Real.log_div two_ne_zero hγ0.ne']
    ring
  rw [e]
  exact hγη.le

/-- The union term: `‖D‖ ≤ C Q_{γn} log(2/γ) ≤ C γ^{2/5} log(2/γ) Q_n`, with `G` the logarithm of
the number of pairs of cubes. -/
lemma union_term_le {c Qγ Qn G CG r l : ℝ} (hc : 0 ≤ c) (hG0 : 0 ≤ G) (hQn : 0 ≤ Qn) (hr : 0 ≤ r)
    (hQ : Qγ ≤ r * Qn) (hG : G ≤ CG * l) :
    c * (Qγ * G) ≤ c * CG * (r * l) * Qn := by
  have h := mul_le_mul_of_nonneg_left (mul_le_mul hQ hG hG0 (mul_nonneg hr hQn)) hc
  calc c * (Qγ * G) ≤ c * (r * Qn * (CG * l)) := h
    _ = c * CG * (r * l) * Qn := by ring

/-- The closing inequality of the proof of Lemma `lem:modulus`. -/
lemma final_le {a e f x y z Q η : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (hf : 0 ≤ f) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hQ : 0 ≤ Q) (h : (a + e + f) * (x + y + z) ≤ η) :
    a * y * Q + f * z * Q + e * x * Q ≤ η * Q := by
  have h1 : a * y + f * z + e * x ≤ (a + e + f) * (x + y + z) := by
    linarith only [mul_nonneg ha hx, mul_nonneg ha hz, mul_nonneg he hy, mul_nonneg he hz,
      mul_nonneg hf hx, mul_nonneg hf hy]
  calc a * y * Q + f * z * Q + e * x * Q = (a * y + f * z + e * x) * Q := by ring
    _ ≤ η * Q := mul_le_mul_of_nonneg_right (h1.trans h) hQ

/-- `cutRatio` at `h = γ³`. -/
lemma cutRatio_cube {γ : ℝ} (hγ : 0 < γ) : cutRatio (γ ^ 3) = γ := by
  rw [cutRatio, show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hγ.le (by norm_num)

/-! ## One pair -/

/-- **The three terms of the last display of the proof of Lemma `lem:modulus`** for one pair, in
the `L^k` norm: the union bound at the length `γn` for `D`, the slack and the `φ` terms, and the
event `E`. -/
theorem eLpNorm_modulus_phi_le (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {CP CL γ A n : ℝ}
    {K : ℕ} {p : CubePair m} (hCP : 0 < CP) (hCL : 0 < CL) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hA : 1 ≤ A) (hn : 2 < n) (hp : p.IsAdmissible n (W K A n) (1 / 2))
    (hσL : W K A (γ * n) * (Real.sqrt m * boxRadius m (γ ^ 3)) ≤ γ * n / 4)
    (hprofκ : ∀ q : CubePair m, q.IsAdmissible (γ * n) (W K A (γ * n)) 1 →
      IsOs X.P 1 (CP * Q K A (γ * n)) (fun ω => pairSup (X.passTime ω) q.first q.second) ∧
        IsOs X.P 1 (CP * Q K A (γ * n))
          (fun ω => pairSup (X.slabTime b q.slab ω) q.first q.second))
    (hprofn : IsOs X.P 1 (CP * Q K A n)
      (fun ω => pairSup (X.slabTime b p.slab ω) p.first p.second))
    (hlocn : IsOs X.P 2 CL (fun ω => (W K A n)⁻¹ *
      Contracts.maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first p.second))
    {k : ℕ} (hk : 1 ≤ k) :
    eLpNorm (fun ω => Contracts.modulusSup (X.slabTime b p.slab ω) p.first p.second
        (γ ^ 3 * W K A n)) k X.P ≤
      ENNReal.ofReal (4 * (momentConst 1 k * (2 / Real.log 2 * (CP * Q K A (γ * n)) *
          Real.log (2 + 4 * ((box m (boxRadius m (γ ^ 3))).card : ℝ) ^ 2))) +
        (3 + (4 * (γ⁻¹ * W K A n + 2 * (2 * Real.sqrt m * W K A n)) / (γ * n) *
            (γ ^ 3 * W K A n) + 8 * (2 * Real.sqrt m * W K A n) / n * (γ ^ 3 * W K A n))) +
        2 * (momentConst 1 (2 * k) * (CP * Q K A n)) *
          (2 * Real.exp (-(γ⁻¹ / CL) ^ 2)) ^ (1 / (2 * (k : ℝ)))) := by
  have hn0 : 0 < n := by linarith only [hn]
  have hA0 : 0 < A := by linarith only [hA]
  have hh : 0 < γ ^ 3 := pow_pos hγ 3
  have h8 : γ ^ 3 ≤ 1 / 8 :=
    (pow_le_pow_left₀ hγ.le hγ2 3).trans_eq (by norm_num)
  have hcut := cutRatio_cube hγ
  have htube : tubeRatio (γ ^ 3) = γ⁻¹ := by rw [tubeRatio_eq_inv hh, hcut]
  have hγ1 : γ ≤ 1 := hγ2.trans (by norm_num)
  have hγn : 0 < γ * n := mul_pos hγ hn0
  have hWn : 0 < W K A n := Real.sqrt_pos.mpr (mul_pos hn0 (Profiles.Q_pos hA0 hn0))
  have hσ : 0 < W K A (γ * n) := Real.sqrt_pos.mpr (mul_pos hγn (Profiles.Q_pos hA0 hγn))
  have hQn := Profiles.Q_pos (K := K) hA0 hn0
  have hQγ := Profiles.Q_pos (K := K) hA0 hγn
  have H : CutData p (γ * n) (W K A (γ * n)) (γ⁻¹ * W K A n) (boxRadius m (γ ^ 3)) := by
    have := cutData_of (m := m) hp hn hh h8 hσ
      (by rw [hcut]; exact W_le_rpow_mul_W hA0.le hγ hγ1 hn0.le)
    rwa [hcut, htube] at this
  have hfam := isOs_smallFamily X b H.hn H.hoff H.hκ0 hσ.le (by linarith only [hσ]) hσL hprofκ
  have hU := isOs_smallMax X b p (γ * n) (W K A (γ * n)) (boxRadius m (γ ^ 3)) (mul_pos hCP hQγ) hfam
  have hG : 0 < Real.log (2 + 4 * ((box m (boxRadius m (γ ^ 3))).card : ℝ) ^ 2) :=
    Real.log_pos (by
      have := sq_nonneg ((box m (boxRadius m (γ ^ 3))).card : ℝ)
      linarith only [this])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Bd, hBd0, hBd⟩ := Profiles.exists_upperBound X
  obtain ⟨hd, -, h1W, -, h2W, -⟩ := id hp
  have hsq := Real.sqrt_nonneg (m : ℝ)
  have hR₁ : Real.sqrt m * (p.side₁ / 2) ≤ 2 * Real.sqrt m * W K A n := by
    linarith only [mul_le_mul_of_nonneg_left h1W hsq]
  have hR₂ : Real.sqrt m * (p.side₂ / 2) ≤ 2 * Real.sqrt m * W K A n := by
    linarith only [mul_le_mul_of_nonneg_left h2W hsq]
  have hδ : 0 ≤ γ ^ 3 * W K A n := mul_nonneg hh.le hWn.le
  have hZm : AEMeasurable (fun ω => Contracts.modulusSup (X.slabTime b p.slab ω) p.first p.second
      (γ ^ 3 * W K A n)) X.P :=
    Localization.aemeasurable_modulusSup_slabTime X hb p.slab
      (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_first p H.h1))
      (Profiles.isCompact_of_isRectBox (Profiles.cubePair_isRectBox_second p H.h2))
      (Profiles.cubePair_first_subset_set p H.hn.le) (Profiles.cubePair_second_subset_set p H.hn.le)
      _
  have hc : 0 ≤ 3 + (4 * (γ⁻¹ * W K A n + 2 * (2 * Real.sqrt m * W K A n)) / (γ * n) *
      (γ ^ 3 * W K A n) + 8 * (2 * Real.sqrt m * W K A n) / n * (γ ^ 3 * W K A n)) :=
    euclid_terms_nonneg hγ hn0 hWn hsq
  refine eLpNorm_le_of_off_event hZm hU hprofn hlocn
    (mul_pos (mul_pos (div_pos two_pos hl2) (mul_pos hCP hQγ)) hG) (mul_pos hCP hQn) hCL hc
    (div_pos (inv_pos.2 hγ) hCL).le (fun ω => pairSup_nonneg _ _ _)
    (fun ω => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
      Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _)
    (fun ω => ?_) (fun ω hω => ?_) hk
  · obtain ⟨c, hc'⟩ := pairBound_slabTime X hb p H.h1 H.h2 H.hn.le ω
    exact modulusSup_le_two_mul hc' _
  · rw [mul_div_cancel₀ _ hCL.ne', inv_mul_lt_iff₀ hWn] at hω
    have hgood : Contracts.maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first
        p.second ≤ γ⁻¹ * W K A n := by
      rw [mul_comm]
      exact hω.le
    have := modulusSup_le_phi X hb hBd hBd0.le H hR₁ hR₂ hδ ω hgood
    rw [hd] at this
    linarith only [this]

/-- **Equation `eq:modulus` for one pair**: the last display of the proof and the choice of `γ`
give `E[Z^{8d}]^{1/(8d)} ≤ ηQ_n`. The hypothesis `hγη` is that the factor of `Q_n` is at most
`η`. -/
theorem modulus_pair_le_eta (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {CP CL γ η A n : ℝ}
    {K : ℕ} {p : CubePair m} (hCP : 0 < CP) (hCL : 0 < CL) (hγ : 0 < γ) (hγ4 : γ < 1 / 4)
    (hK : 10 ≤ K) (hA : 1 ≤ A) (hn : 2 < n) (hp : p.IsAdmissible n (W K A n) (1 / 2))
    (hσL : W K A (γ * n) * (Real.sqrt m * boxRadius m (γ ^ 3)) ≤ γ * n / 4)
    (hQ1 : 1 ≤ γ * Q K A n)
    (hprofκ : ∀ q : CubePair m, q.IsAdmissible (γ * n) (W K A (γ * n)) 1 →
      IsOs X.P 1 (CP * Q K A (γ * n)) (fun ω => pairSup (X.passTime ω) q.first q.second) ∧
        IsOs X.P 1 (CP * Q K A (γ * n))
          (fun ω => pairSup (X.slabTime b q.slab ω) q.first q.second))
    (hprofn : IsOs X.P 1 (CP * Q K A n)
      (fun ω => pairSup (X.slabTime b p.slab ω) p.first p.second))
    (hlocn : IsOs X.P 2 CL (fun ω => (W K A n)⁻¹ *
      Contracts.maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first p.second))
    (hγη : (4 * momentConst 1 (8 * (m + 1)) * (2 / Real.log 2) * CP * logConst m +
        4 * momentConst 1 (2 * (8 * (m + 1))) * CP + (7 + 32 * Real.sqrt m)) *
        (Real.exp (-(1 / (2 * ((8 * (m + 1) : ℕ) : ℝ) * CL ^ 2) * γ⁻¹ ^ 2)) +
          γ ^ (2 / 5 : ℝ) * Real.log (2 / γ) + γ) ≤ η) :
    eLpNorm (fun ω => Contracts.modulusSup (X.slabTime b p.slab ω) p.first p.second
        (γ ^ 3 * W K A n)) (8 * (m + 1) : ℝ≥0∞) X.P ≤ ENNReal.ofReal (η * Q K A n) := by
  have hn0 : 0 < n := by linarith only [hn]
  have hA0 : 0 < A := by linarith only [hA]
  have hγ1 : γ ≤ 1 := by linarith only [hγ4]
  have hγ2 : γ ≤ 1 / 2 := by linarith only [hγ4]
  have hh : 0 < γ ^ 3 := pow_pos hγ 3
  have h8 : γ ^ 3 ≤ 1 / 8 := (pow_le_pow_left₀ hγ.le hγ2 3).trans_eq (by norm_num)
  have hγn : 0 < γ * n := mul_pos hγ hn0
  have hQn := Profiles.Q_pos (K := K) hA0 hn0
  have hk : 1 ≤ 8 * (m + 1) := by omega
  have hkc : (((8 * (m + 1) : ℕ)) : ℝ≥0∞) = 8 * (m + 1) := by push_cast; ring
  have hmain := eLpNorm_modulus_phi_le X hb hCP hCL hγ hγ2 hA hn hp hσL hprofκ hprofn hlocn hk
  rw [hkc] at hmain
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  set k := 8 * (m + 1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm1 := momentConst_pos 1 k
  have hm2 := momentConst_pos 1 (2 * k)
  have hG0 : 0 ≤ Real.log (2 + 4 * ((box m (boxRadius m (γ ^ 3))).card : ℝ) ^ 2) :=
    Real.log_nonneg (by
      have := sq_nonneg ((box m (boxRadius m (γ ^ 3))).card : ℝ)
      linarith only [this])
  have hlog : 0 ≤ Real.log (2 / γ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hγ]; linarith only [hγ1])
  have hG : Real.log (2 + 4 * ((box m (boxRadius m (γ ^ 3))).card : ℝ) ^ 2) ≤
      logConst m * Real.log (2 / γ) := by
    have := log_card_box_le_log m hh h8
    rwa [cutRatio_cube hγ] at this
  have hlc : 0 ≤ logConst m := by
    have hsq := Real.sqrt_nonneg (m : ℝ)
    have : 0 ≤ Real.log (2 * (3 / 2 + 4 * Real.sqrt m + 2) + 1) :=
      Real.log_nonneg (by linarith only [hsq])
    have h6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact add_nonneg (div_nonneg (add_nonneg h6 (mul_nonneg (mul_nonneg zero_le_two hm0) this))
      hl2.le) (mul_nonneg (by norm_num) hm0)
  have hr : 0 ≤ γ ^ (2 / 5 : ℝ) := Real.rpow_nonneg hγ.le _
  have hQ := Profiles.Q_le_rpow_mul (K := K) hK hA0.le hγn.le hn0.le hγ hγ1 le_rfl
  have t₂ := euclid_terms_le hγ hγ1 hn0 (Real.sqrt_nonneg (m : ℝ)) hQn.le
    (Profiles.W_sq (K := K) (A := A) hA0.le hn0.le) hQ1
  have hc₁ : 0 ≤ 4 * momentConst 1 k * (2 / Real.log 2) * CP :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm1.le) (div_nonneg zero_le_two hl2.le)) hCP.le
  have t₁ := union_term_le hc₁ hG0 hQn.le hr hQ hG
  have hk' : 1 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk'
  set x := Real.exp (-(1 / (2 * (k : ℝ) * CL ^ 2) * γ⁻¹ ^ 2)) with hxdef
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have htail : (2 * Real.exp (-(γ⁻¹ / CL) ^ 2)) ^ (1 / (2 * (k : ℝ))) ≤ 2 * x := by
    refine (tail_le _ hk').trans_eq ?_
    rw [hxdef, show (γ⁻¹ / CL) ^ 2 / (2 * (k : ℝ)) = 1 / (2 * (k : ℝ) * CL ^ 2) * γ⁻¹ ^ 2 by
      field_simp]
  have t₃ := mul_le_mul_of_nonneg_left htail
    (mul_nonneg zero_le_two (mul_nonneg hm2.le (mul_pos hCP hQn).le))
  have hfin := final_le (Q := Q K A n) (mul_nonneg hc₁ hlc)
    (mul_nonneg (mul_nonneg (by norm_num) hm2.le) hCP.le)
    (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    hx0 (mul_nonneg hr hlog) hγ.le hQn.le hγη
  have e₁ : 4 * (momentConst 1 k * (2 / Real.log 2 * (CP * Q K A (γ * n)) *
      Real.log (2 + 4 * ((box m (boxRadius m (γ ^ 3))).card : ℝ) ^ 2))) =
      4 * momentConst 1 k * (2 / Real.log 2) * CP *
        (Q K A (γ * n) * Real.log (2 + 4 * ((box m (boxRadius m (γ ^ 3))).card : ℝ) ^ 2)) := by
    ring
  exact (add_le_add (add_le_add (e₁.le.trans t₁) t₂) (t₃.trans_eq (by ring))).trans hfin

/-- **Lemma `lem:modulus`, equation `eq:modulus`**: from
equation `eq:profiles` and equation `eq:localization`. The number `γ` is chosen first, as in the
closing line of the proof, and `h = γ³`; so `h` depends only on `η` and the constants of the two
equations, and not on `c₁`, `K` or `A`. Equation `eq:profiles` is used at the lengths `n` and `γn`,
with the lower multiple `γc₁`. -/
theorem modulusStatement_of (hprof : Contracts.ProfilesStatement.{u})
    (hloc : Contracts.LocalizationStatement.{u}) : Contracts.ModulusStatement.{u} := by
  intro m hm X hX b hb Cstar hC η hη
  obtain ⟨CP, hCP, HP⟩ := hprof m hm X hX b hb Cstar hC
  obtain ⟨CL, hCL, HL⟩ := hloc m hm X hX b hb Cstar hC
  obtain ⟨γ, hγ, hγ4, hγη⟩ := exists_gamma_le
    (4 * momentConst 1 (8 * (m + 1)) * (2 / Real.log 2) * CP * logConst m +
      4 * momentConst 1 (2 * (8 * (m + 1))) * CP + (7 + 32 * Real.sqrt m))
    (c := 1 / (2 * ((8 * (m + 1) : ℕ) : ℝ) * CL ^ 2)) (by positivity) hη
  refine ⟨γ ^ 3, pow_pos hγ 3, fun c₁ hc₁ hc₁1 K => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hγ1 : γ ≤ 1 := by linarith only [hγ4]
  set ε : ℝ := 1 / (4 * (Real.sqrt m * boxRadius m (γ ^ 3) + 1)) with hεdef
  have hsb : 0 ≤ Real.sqrt m * boxRadius m (γ ^ 3) :=
    mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have hden : 0 < 4 * (Real.sqrt m * boxRadius m (γ ^ 3) + 1) :=
    mul_pos four_pos (add_pos_of_nonneg_of_pos hsb one_pos)
  have hε : 0 < ε := div_pos one_pos hden
  obtain ⟨NP, HP'⟩ := HP (γ * c₁) (mul_pos hγ hc₁) K
  obtain ⟨NL, HL'⟩ := HL c₁ hc₁ hc₁1 K
  obtain ⟨NW, HW⟩ := Proofs.Profiles.exists_W_le Cstar (γ * c₁) ε (mul_pos hγ hc₁) hε
  obtain ⟨NQ, HQ⟩ := Proofs.Profiles.exists_log_le (γ⁻¹ / Real.log 2 ^ 2) c₁ hc₁
  refine ⟨max (max NP NL) (max (max NW NQ) (3 / c₁)), fun A N hN hS n hn hnN p hp => ?_⟩
  have hNP : NP ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNL : NL ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNW : NW ≤ N :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hNQ : NQ ≤ N :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : 3 / c₁ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hK, hA, -, -, hreg⟩ := id hS
  have h3 : 3 ≤ c₁ * N := by rw [div_le_iff₀ hc₁] at hN3; linarith only [hN3]
  have hn3 : 3 ≤ n := h3.trans hn
  have hn0 : 0 < n := by linarith only [hn3]
  have hlo : γ * c₁ * N ≤ γ * n := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hn hγ.le
  have hhi : γ * n ≤ N := (mul_le_of_le_one_left hn0.le hγ1).trans hnN
  have hlo' : γ * c₁ * N ≤ n := by
    rw [mul_assoc]; exact (mul_le_of_le_one_left (zero_le_three.trans h3) hγ1).trans hn
  -- the side of the small cubes
  have hσε := HW K hK A N (by linarith only [hA]) hNW hreg (γ * n) hlo hhi
  have hεL : ε * (Real.sqrt m * boxRadius m (γ ^ 3)) ≤ 1 / 4 := by
    rw [hεdef, div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
    linarith only
  have hσL : W K A (γ * n) * (Real.sqrt m * boxRadius m (γ ^ 3)) ≤ γ * n / 4 := by
    calc W K A (γ * n) * (Real.sqrt m * boxRadius m (γ ^ 3)) ≤
          ε * (γ * n) * (Real.sqrt m * boxRadius m (γ ^ 3)) :=
          mul_le_mul_of_nonneg_right hσε hsb
      _ = γ * n * (ε * (Real.sqrt m * boxRadius m (γ ^ 3))) := by ring
      _ ≤ γ * n * (1 / 4) := mul_le_mul_of_nonneg_left hεL (mul_pos hγ hn0).le
      _ = γ * n / 4 := by ring
  -- `1 ≤ γQ_n`
  have hQ1 : 1 ≤ γ * Q K A n := by
    have hq := HQ K hK A N hA hNQ n hn
    have hlog : Real.log 2 ≤ Real.log (2 + N) :=
      Real.log_le_log (by norm_num) (by linarith only [hn3, hnN])
    have hlog2 : Real.log 2 ^ 2 ≤ Real.log (2 + N) ^ 2 := pow_le_pow_left₀ hl2.le hlog 2
    have hγQ : γ⁻¹ ≤ Q K A n := by
      have h2 := mul_le_mul_of_nonneg_left hlog2
        (div_nonneg (inv_nonneg.2 hγ.le) (sq_nonneg (Real.log 2)))
      have e : γ⁻¹ / Real.log 2 ^ 2 * Real.log 2 ^ 2 = γ⁻¹ := by field_simp
      linarith only [h2, e, hq]
    calc (1 : ℝ) = γ * γ⁻¹ := (mul_inv_cancel₀ hγ.ne').symm
      _ ≤ γ * Q K A n := mul_le_mul_of_nonneg_left hγQ hγ.le
  have hp1 : p.IsAdmissible n (W K A n) 1 :=
    ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.trans (by norm_num)⟩
  exact modulus_pair_le_eta X hb hCP hCL hγ hγ4 hK hA (by linarith only [hn3]) hp hσL hQ1
    (fun q hq => HP' A N hNP hS (γ * n) hlo hhi q hq)
    (HP' A N hNP hS n hlo' hnN p hp1).2 (HL' A N hNL hS n hn hnN p hp) hγη

end IsotropicVariance.Paper.Proofs.Modulus
