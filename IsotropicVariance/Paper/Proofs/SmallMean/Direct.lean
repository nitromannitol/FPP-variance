/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.DirectChain

/-!
# The proof of Lemma `lem:smallmean`

`smallMeanStatement_of_contracts` proves Lemma `lem:smallmean`
from the statements that its proof cites: Lemma `lem:classical`, Lemma `lem:slab`, Proposition
`prop:profiles`, equation `eq:chainsum` and equation `eq:modulus`. The argument is the paper's,
with `b`, any deterministic upper bound of the density, for `sup ρ`.

**The constants.** They are chosen in the order of the paper, none depending on `K`: `κ` from the
constant of equation `eq:chainsum` and `b`; then the mesh `h` of equation `eq:modulus`, for
`η = κ/3`, and a net of the unit cube of radius `h`; then the interpolation parameter `λ` and the
variance threshold `δ`.

**The thresholds.** For each `K` they come from equations `eq:profiles`, `eq:chainsum` and
`eq:modulus`, together with conditions that are eventually true for `s ≥ N/8`, uniformly in `K ≥ 10`
and `A ≥ 1`:
* `W_s(1 + √(d−1)) ≤ s/4`, from the regime, equation `eq:regime`;
* the second moment of `T^{(i)} − T` is at most `δQ_s²`, by equation `eq:slab`;
* `C log²(2 + s) ≤ s^{2/5} ≤ Q_s`.

**The proof.** `excess_le_at_scale` is the argument at a fixed scale:
1. The second paragraph of the paper's proof, the moment bound of the arrays, is
   `lintegral_fluct_pow_le_of_pair`, fed by `slabSupSqrt` from equation `eq:slab`, by
   `isOs_slabTime_sub_dist_pair` from equation `eq:profiles`, and by `lintegral_modulusSup_pair`
   from equation `eq:modulus`.
2. `exists_fluct_arrays` gives the arrays `X_i/κ`, and `lintegral_sum_fluct_le` applies equation
   `eq:chainsum` to them.
3. `chain_mean_ge` bounds `E F − ⌈s⌉s` from below.
4. `excess_le_of_chain` closes with equations `eq:columns` and `eq:classical` at the length
   `s⌈s⌉ ≤ 2s²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.SmallMean

open Infra.Slab

variable {m : ℕ}

/-! ### The classical bounds at the length `s⌈s⌉` -/

/-- `log(2 + Ms) ≤ 3 log(2 + s)` for `M ≤ 2s`. -/
theorem log_two_add_mul_le {s : ℝ} {M : ℕ} (hs : 0 ≤ s) (hM2 : (M : ℝ) ≤ 2 * s) :
    Real.log (2 + M * s) ≤ 3 * Real.log (2 + s) := by
  have hMs : (M : ℝ) * s ≤ 2 * s ^ 2 := by
    calc (M : ℝ) * s ≤ (2 * s) * s := mul_le_mul_of_nonneg_right hM2 hs
      _ = 2 * s ^ 2 := by ring
  have hMs0 : 0 ≤ (M : ℝ) * s := by positivity
  calc Real.log (2 + M * s) ≤ Real.log (2 + 2 * s ^ 2) :=
        Real.log_le_log (by linarith only [hMs0]) (by linarith only [hMs])
    _ ≤ 3 * Real.log (2 + s) := log_two_add_two_mul_sq_le hs

/-- `(Ms log(2 + Ms))^{1/2} ≤ 3M log²(2 + s)` for `1 ≤ s ≤ M ≤ 2s`. -/
theorem sqrt_mul_log_le {s : ℝ} {M : ℕ} (hs1 : 1 ≤ s) (hsM : s ≤ M) (hM2 : (M : ℝ) ≤ 2 * s) :
    Real.sqrt (M * s * Real.log (2 + M * s)) ≤ M * (3 * Real.log (2 + s) ^ 2) := by
  have hs0 : 0 < s := by linarith only [hs1]
  have hM0 : (0 : ℝ) < M := by linarith only [hs1, hsM]
  have hL1 : 1 ≤ Real.log (2 + s) := Profiles.one_le_log_two_add hs1
  set L := Real.log (2 + s) with hLdef
  have hlog2 : Real.log (2 + M * s) ≤ 3 * L := log_two_add_mul_le hs0.le hM2
  have hMs0 : 0 ≤ (M : ℝ) * s := by positivity
  have hlog2' : 0 ≤ Real.log (2 + M * s) := Real.log_nonneg (by linarith only [hMs0])
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : (M : ℝ) * s * Real.log (2 + M * s) ≤ M ^ 2 * (3 * L) := by
    have : (M : ℝ) * s ≤ M ^ 2 := by
      calc (M : ℝ) * s ≤ M * M := mul_le_mul_of_nonneg_left hsM hM0.le
        _ = M ^ 2 := by ring
    calc (M : ℝ) * s * Real.log (2 + M * s) ≤ M ^ 2 * Real.log (2 + M * s) :=
          mul_le_mul_of_nonneg_right this hlog2'
      _ ≤ M ^ 2 * (3 * L) := mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have h2 : 3 * L ≤ (3 * L ^ 2) ^ 2 := by
    calc 3 * L ≤ 9 * L * L ^ 3 := by
          have := mul_le_mul_of_nonneg_left hL3 (by linarith only [hL1] : (0 : ℝ) ≤ 9 * L)
          linarith only [this, hL1]
      _ = (3 * L ^ 2) ^ 2 := by ring
  calc (M : ℝ) * s * Real.log (2 + M * s) ≤ M ^ 2 * (3 * L) := h1
    _ ≤ M ^ 2 * (3 * L ^ 2) ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (M * (3 * L ^ 2)) ^ 2 := by ring

/-- **The end of the proof of Lemma `lem:smallmean`**: the lower bound of
`E F − Ms`, equation `eq:columns` and equation `eq:classical` at the length `Ms ≤ 2s²` give
`a ≤ CκQ + C log²(2 + s)`, for `a = (E T_s − s)/(1 + b)`, and hence `(1 + b)a ≤ Q/100` once `κ` is
small and `C log²(2 + s) ≤ s^{2/5} ≤ Q`. -/
theorem excess_le_of_chain {s Q a κ D Csl Ccl b EF meanMs : ℝ} {M : ℕ} (hs1 : 1 ≤ s)
    (hsM : s ≤ M) (hM2 : (M : ℝ) ≤ 2 * s) (hQ : s ^ (2 / 5 : ℝ) ≤ Q) (hb : 0 ≤ b)
    (hCsl : 0 ≤ Csl) (hCcl : 0 ≤ Ccl)
    (hchain : (M : ℝ) * s + M * a ≤ EF + Q * κ * (D * M))
    (hcol : EF ≤ meanMs + 4 * (Csl * M * Real.log (2 + M * s) ^ 2))
    (hcl : meanMs - M * s ≤ Ccl * Real.sqrt (M * s * Real.log (2 + M * s)))
    (hκ : κ * ((1 + b) * D) ≤ 1 / 200)
    (hasym : 200 * ((1 + b) * (36 * Csl + 3 * Ccl)) * Real.log (2 + s) ^ 2 ≤ s ^ (2 / 5 : ℝ)) :
    (1 + b) * a ≤ Q / 100 := by
  have hs0 : 0 < s := by linarith only [hs1]
  have hM0 : (0 : ℝ) < M := by linarith only [hs1, hsM]
  have hQ0 : 0 ≤ Q := (Real.rpow_nonneg hs0.le _).trans hQ
  have hMs0 : 0 ≤ (M : ℝ) * s := by positivity
  have hlog : Real.log (2 + M * s) ≤ 3 * Real.log (2 + s) := log_two_add_mul_le hs0.le hM2
  have hlog0 : 0 ≤ Real.log (2 + M * s) := Real.log_nonneg (by linarith only [hMs0])
  have hsqrt := sqrt_mul_log_le hs1 hsM hM2
  set L := Real.log (2 + s) with hLdef
  have h1 : Real.log (2 + M * s) ^ 2 ≤ 9 * L ^ 2 := by
    calc Real.log (2 + M * s) ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
      _ = 9 * L ^ 2 := by ring
  have h2 : 4 * (Csl * M * Real.log (2 + M * s) ^ 2) ≤ M * (36 * Csl * L ^ 2) := by
    calc 4 * (Csl * M * Real.log (2 + M * s) ^ 2)
        ≤ 4 * (Csl * M * (9 * L ^ 2)) := by gcongr
      _ = M * (36 * Csl * L ^ 2) := by ring
  have h3 : Ccl * Real.sqrt (M * s * Real.log (2 + M * s)) ≤ M * (3 * Ccl * L ^ 2) := by
    calc Ccl * Real.sqrt (M * s * Real.log (2 + M * s))
        ≤ Ccl * (M * (3 * L ^ 2)) := mul_le_mul_of_nonneg_left hsqrt hCcl
      _ = M * (3 * Ccl * L ^ 2) := by ring
  have h4 : (M : ℝ) * a ≤ M * ((36 * Csl + 3 * Ccl) * L ^ 2 + Q * κ * D) := by
    have e : (M : ℝ) * ((36 * Csl + 3 * Ccl) * L ^ 2 + Q * κ * D) =
        M * (36 * Csl * L ^ 2) + M * (3 * Ccl * L ^ 2) + Q * κ * (D * M) := by ring
    rw [e]
    linarith only [hchain, hcol, hcl, h2, h3]
  have h5 : a ≤ (36 * Csl + 3 * Ccl) * L ^ 2 + Q * κ * D := le_of_mul_le_mul_left h4 hM0
  have hb1 : 0 ≤ 1 + b := by linarith only [hb]
  have h6 := mul_le_mul_of_nonneg_left h5 hb1
  have h7 : Q * (κ * ((1 + b) * D)) ≤ Q * (1 / 200) := mul_le_mul_of_nonneg_left hκ hQ0
  have e : (1 + b) * ((36 * Csl + 3 * Ccl) * L ^ 2 + Q * κ * D) =
      (1 + b) * (36 * Csl + 3 * Ccl) * L ^ 2 + Q * (κ * ((1 + b) * D)) := by ring
  rw [e] at h6
  linarith only [h6, h7, hasym, hQ]

/-! ### The inputs at the scale of Lemma `lem:smallmean` -/

/-- The second moment of `T^{(i)} − T` is at most `δQ_s²` for `s` large (the second paragraph of the
proof of Lemma `lem:smallmean`). -/
theorem slab_error_le_of_log {s Q δ Csl : ℝ} (hs : 1 ≤ s) (hδ : 0 < δ) (hCsl : 0 ≤ Csl)
    (hQs : s ^ (2 / 5 : ℝ) ≤ Q)
    (hasym : 12 * Csl ^ 2 / δ * Real.log (2 + s) ^ 4 ≤ s ^ (4 / 5 : ℝ)) :
    12 * (1 : ℝ) ^ 2 * (Real.sqrt Csl * Real.log (2 + s)) ^ 4 ≤ δ * Q ^ 2 := by
  have hs0 : 0 < s := by linarith only [hs]
  have h1 : (Real.sqrt Csl * Real.log (2 + s)) ^ 4 = Csl ^ 2 * Real.log (2 + s) ^ 4 := by
    rw [mul_pow, show Real.sqrt Csl ^ 4 = (Real.sqrt Csl ^ 2) ^ 2 by ring, Real.sq_sqrt hCsl]
  have h2 : s ^ (4 / 5 : ℝ) ≤ Q ^ 2 := by
    calc s ^ (4 / 5 : ℝ) = (s ^ (2 / 5 : ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
          norm_num
      _ ≤ Q ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hs0.le _) hQs 2
  have h3 : 12 * Csl ^ 2 * Real.log (2 + s) ^ 4 ≤ δ * s ^ (4 / 5 : ℝ) := by
    calc 12 * Csl ^ 2 * Real.log (2 + s) ^ 4 = δ * (12 * Csl ^ 2 / δ * Real.log (2 + s) ^ 4) := by
          field_simp
      _ ≤ δ * s ^ (4 / 5 : ℝ) := mul_le_mul_of_nonneg_left hasym hδ.le
  rw [h1, one_pow, mul_one, ← mul_assoc]
  exact h3.trans (mul_le_mul_of_nonneg_left h2 hδ.le)

/-- The mean of a nonnegative variable `O_1(θ)` is at most `4θ`. -/
theorem integral_le_of_isOs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ} {θ : ℝ}
    (hθ : 0 < θ) (h : Cited.IsOs P 1 θ Y) (hY0 : ∀ ω, 0 ≤ Y ω) : ∫ ω, Y ω ∂P ≤ 4 * θ := by
  have h1 := h.integral_pos_rpow_le zero_lt_one hθ (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [Real.rpow_one, div_one, Nat.ceil_one, Nat.factorial_one, Nat.cast_one] at h1
  have heq : ∀ ω, max (Y ω) 0 = Y ω := fun ω => max_eq_left (hY0 ω)
  simp only [heq] at h1
  linarith only [h1, hθ]

/-- `F` is integrable, with `E F ≤ E T_ℓ + 4θ`, by equation `eq:columns`. -/
theorem integrable_F_of_columns (X : Setting.{u} m) {b : ℝ} {M : ℕ} {s θ : ℝ} (hθ : 0 < θ)
    (hlow : ∀ ω, 0 ≤ X.F b M s 0 ω - X.passTime ω 0 (0 + ((M : ℝ) * s) • e₁))
    (hO : Cited.IsOs X.P 1 θ (fun ω =>
      X.F b M s 0 ω - X.passTime ω 0 (0 + ((M : ℝ) * s) • e₁))) :
    Integrable (X.F b M s 0) X.P ∧ ∫ ω, X.F b M s 0 ω ∂X.P ≤ X.mean (M * s) + 4 * θ := by
  simp only [zero_add] at hlow hO
  have hT := Infra.TimeConstant.integrable_TRV X ((M : ℝ) * s)
  have hO' : Cited.IsOs X.P 1 θ fun ω => X.F b M s 0 ω - X.TRV (M * s) ω := hO
  have hdiff : Integrable (fun ω => X.F b M s 0 ω - X.TRV (M * s) ω) X.P :=
    hO'.integrable one_pos hθ (Eventually.of_forall hlow)
  have hF : Integrable (X.F b M s 0) X.P := by
    refine (hdiff.add hT).congr (Eventually.of_forall fun ω => ?_)
    simp
  refine ⟨hF, ?_⟩
  have h1 := integral_le_of_isOs hθ hO' hlow
  rw [integral_sub hF hT] at h1
  simp only [Setting.mean]
  linarith only [h1]

/-! ### The proof at one scale -/

/-- **The proof of Lemma `lem:smallmean` at one scale**. -/
theorem excess_le_at_scale (hm : 1 ≤ m) (X : Setting.{u} m) (hX : X.IsNormalized) {b : ℝ}
    (hb : X.IsUpperBound b) {CC Csl Ccl Cpr κ δ l h η : ℝ} (hCC : 0 < CC) (hCsl : 0 < Csl)
    (hCcl : 0 ≤ Ccl) (hCpr : 0 < Cpr) (hκ : 0 < κ) (hδ : 0 < δ) (hl : 0 < l) (hη : 0 ≤ η)
    {T₀ : Finset (EuclideanSpace ℝ (Fin m))} (hT₀ : ∀ t ∈ T₀, t ∈ unitCube m)
    (hnet : ∀ y ∈ unitCube m, ∃ t ∈ T₀, dist y t ≤ h)
    (hconst : κ⁻¹ ^ (4 * (m + 1)) * (3 ^ (4 * (m + 1) - 1) *
      ((T₀.card : ℝ) ^ 2 * (l ^ (4 * (m + 1) - 2) * (5 * δ) +
        momentConst (4 * (m + 1)) Cpr / l ^ (4 * (m + 1))) +
          η ^ (4 * (m + 1)) + η ^ (4 * (m + 1)))) ≤ 1)
    (hκc : κ * ((1 + b) * CC) ≤ 1 / 200)
    (hsl : ∀ (sl : Slab m) (z : Pt m), 2 < sl.width →
      (∀ ω, ∀ x y : Pt m, Contracts.IsSlabPair sl z x y →
        0 ≤ X.slabTime b sl ω x y - X.passTime ω x y) ∧
      Cited.IsOs X.P 1 (Csl * Real.log (2 + sl.width) ^ 2) (fun ω =>
        ⨆ p : {p : Pt m × Pt m // Contracts.IsSlabPair sl z p.1 p.2},
          (X.slabTime b sl ω p.1.1 p.1.2 - X.passTime ω p.1.1 p.1.2)))
    (hcol : ∀ (M : ℕ) (s : ℝ) (τ : Pt m), 1 ≤ M → 2 < s →
      (∀ ω, 0 ≤ X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁)) ∧
      Cited.IsOs X.P 1 (Csl * M * Real.log (2 + M * s) ^ 2) (fun ω =>
        X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁)))
    (hcl : ∀ t : ℝ, 1 ≤ t → X.mean t - t ≤ Ccl * Real.sqrt (t * Real.log (2 + t)))
    {s W Q : ℝ} (hs : 3 ≤ s) (hW : 0 < W) (hQ : 0 < Q)
    (hWs : W * (1 + Real.sqrt m) ≤ s / 4) (hQs : s ^ (2 / 5 : ℝ) ≤ Q)
    (hvar : ∀ r, s ≤ r → r ≤ 2 * s → variance (X.TRV r) X.P ≤ 2 * δ * Q ^ 2)
    (hprof : ∀ (i : ℕ) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
      ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 (i + 1) k,
        Cited.IsOs X.P 1 (Cpr * Q) fun ω =>
          |X.slabTime b (chainSlab s 0 i) ω u v - dist u v|)
    (hmod : ∀ (i : ℕ) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
      ∫⁻ ω, ENNReal.ofReal (Contracts.modulusSup (X.slabTime b (chainSlab s 0 i) ω)
          (gridCube s W 0 i j) (gridCube s W 0 (i + 1) k) (h * W)) ^
            (2 * (4 * (m + 1)) : ℝ) ∂X.P ≤
        ENNReal.ofReal (η * Q) ^ (2 * (4 * (m + 1)) : ℝ))
    (hCh : Profiles.ChainSumBound X b ⌈s⌉₊ s W CC)
    (hasym₁ : 12 * Csl ^ 2 / δ * Real.log (2 + s) ^ 4 ≤ s ^ (4 / 5 : ℝ))
    (hasym₂ : 200 * ((1 + b) * (36 * Csl + 3 * Ccl)) * Real.log (2 + s) ^ 2 ≤ s ^ (2 / 5 : ℝ)) :
    X.mean s - s ≤ Q / 100 := by
  have hs0 : 0 < s := by linarith only [hs]
  have hs2 : 2 < s := by linarith only [hs]
  have hs1 : 1 ≤ s := by linarith only [hs]
  have hWs' : W * Real.sqrt m ≤ s / 4 := by
    linarith only [hWs, hW, mul_add W 1 (Real.sqrt m)]
  obtain ⟨ω₀⟩ : Nonempty X.Ω := nonempty_of_isProbabilityMeasure X.P
  have hb0 : 0 ≤ b := upperBound_nonneg X hb ω₀
  -- the second paragraph of the proof: equation `eq:slab` for the pairs of cubes
  set L := Real.log (2 + s) with hL
  have hL0 : 0 < L := Real.log_pos (by linarith only [hs])
  set θ := Real.sqrt Csl * L with hθdef
  have hθ : 0 < θ := mul_pos (Real.sqrt_pos.2 hCsl) hL0
  have hθ2 : θ ^ 2 = Csl * L ^ 2 := by rw [hθdef, mul_pow, Real.sq_sqrt hCsl.le]
  have hw : ∀ i : ℕ, 2 < (chainSlab (m := m) s 0 i).width := fun i => by
    rw [chainSlab_width]
    exact hs2
  have hSos : ∀ (i : ℕ) (j : Fin m → ℤ), Cited.IsOs X.P 2 θ (slabSupSqrt X b s W i j) := by
    intro i j
    refine isOs_slabSupSqrt X b s W i j ?_
    have h' := (hsl (chainSlab s 0 i) (meshPt s W i j 0) (hw i)).2
    rw [chainSlab_width] at h'
    rw [hθ2]
    exact h'
  have hDT := slabTime_sub_passTime_le_slabSupSqrt X hb hs0 hW.le hWs
    (fun i j ω x y hp => (hsl _ _ (hw i)).1 ω x y hp)
  have herr := slab_error_le_of_log hs1 hδ hCsl.le hQs hasym₁
  -- the moment bound of one array entry
  have hA : 0 ≤ (T₀.card : ℝ) ^ 2 * (l ^ (4 * (m + 1) - 2) * (5 * δ) +
      momentConst (4 * (m + 1)) Cpr / l ^ (4 * (m + 1))) := by
    have := momentConst_nonneg (4 * (m + 1)) hCpr.le
    positivity
  obtain ⟨Z, hZm, hZ0, hZind, hZmom, hZ⟩ := exists_fluct_arrays X hb hs0 hW.le hQ hκ ⌈s⌉₊
    (fun i j k hc V hVm hV q hq => lintegral_inv_mul_pow_le_one hκ hA hη
      (lintegral_fluct_pow_le_of_pair hm X hb hs0 hW hQ hWs hc hVm hV hq hT₀ hnet hδ.le hvar
        zero_le_one hθ (hSos i j) (slabSupSqrt_nonneg X b s W i j) (hDT i j k hc) herr hCpr
        (hprof i j k hc) hη (hmod i j k hc) hl) hconst)
  -- equation `eq:chainsum`, applied to the arrays `X_i/κ`
  have hsum := lintegral_sum_fluct_le X hCh Z hZm hZ0 hZind hZmom
  have hsM : s ≤ ⌈s⌉₊ := Nat.le_ceil s
  have hM2 : (⌈s⌉₊ : ℝ) ≤ 2 * s := by
    have := Nat.ceil_lt_add_one hs0.le
    linarith only [this, hs]
  have hM1 : (1 : ℝ) ≤ ⌈s⌉₊ := by linarith only [hsM, hs]
  have hM1' : 1 ≤ ⌈s⌉₊ := by exact_mod_cast hM1
  -- the lower bound of `E F`
  have hcolM := hcol ⌈s⌉₊ s 0 hM1' hs2
  have hMs1 : 1 ≤ (⌈s⌉₊ : ℝ) * s := one_le_mul_of_one_le_of_one_le hM1 hs1
  have hLc : 0 < Csl * ⌈s⌉₊ * Real.log (2 + ⌈s⌉₊ * s) ^ 2 := by
    have hlog : 0 < Real.log (2 + ⌈s⌉₊ * s) := Real.log_pos (by linarith only [hMs1])
    positivity
  obtain ⟨hFint, hFle⟩ := integrable_F_of_columns X hLc hcolM.1 hcolM.2
  have hchain := chain_mean_ge X hm hX hb hs0 hW hQ hκ (by positivity) hWs' Z
    (fun i j k hc u hu v hv ω => sub_nonneg.1 (hDT i j k hc u hu v hv ω).1) hZ hsum hFint
  -- equations `eq:columns` and `eq:classical`
  have hfin := excess_le_of_chain hs1 hsM hM2 hQs hb0 hCsl.le hCcl hchain hFle (hcl _ hMs1) hκc
    hasym₂
  have hb1 : (1 + b) ≠ 0 := by positivity
  rwa [mul_div_cancel₀ _ hb1] at hfin

/-! ### Lemma `lem:smallmean` -/

/-- **Lemma `lem:smallmean`** (nonrandom fluctuations), from the
statements that the paper's proof cites: Lemma `lem:classical`, Lemma `lem:slab`, Proposition
`prop:profiles`, equation `eq:chainsum` and equation `eq:modulus`. -/
theorem smallMeanStatement_of_contracts (hCl : Contracts.ClassicalBoundsStatement.{u})
    (hSlab : Contracts.SlabStatement.{u}) (hProf : Contracts.ProfilesStatement.{u})
    (hC : Contracts.ChainSumStatement.{u}) (hMod : Contracts.ModulusStatement.{u}) :
    Contracts.SmallMeanStatement.{u} := by
  intro m hm X hX Cstar hCstar
  -- the constants, none depending on `K`
  obtain ⟨b, hb0, hbX⟩ := Profiles.exists_upperBound X
  have hb : X.IsUpperBound b := hbX
  obtain ⟨CC, hCC, hch⟩ := hC m hm X hX b hb Cstar hCstar
  obtain ⟨Cpr, hCpr, hprof⟩ := hProf m hm X hX b hb Cstar hCstar
  obtain ⟨Csl, hCsl, hsl, hcol⟩ := hSlab m hm X hX b hb
  obtain ⟨Ccl, hCcl, hcl⟩ := hCl m hm X hX
  have hb1 : 0 ≤ 1 + b := by linarith only [hb0]
  obtain ⟨κ, hκ0, -, hκc⟩ := exists_kappa (c := 1 / 100) (d := (1 + b) * CC) (by norm_num)
    (by positivity)
  have hκc' : κ * ((1 + b) * CC) ≤ 1 / 200 := by linarith only [hκc]
  have hη : 0 < 12 * κ / 36 := by positivity
  obtain ⟨h, hh, hmod⟩ := hMod m hm X hX b hb Cstar hCstar (12 * κ / 36) hη
  obtain ⟨T₀, hT₀, hnet⟩ := exists_unitCube_net m hh
  obtain ⟨l, δ, hl0, hδ, hconst⟩ := exists_l_delta (T₀.card : ℝ)
    (mul_pos (by norm_num) hκ0 : 0 < 12 * κ) (momentConst_nonneg (4 * (m + 1)) hCpr.le)
    (p := 4 * (m + 1)) (by omega)
  rw [show 12 / (12 * κ) = κ⁻¹ by field_simp] at hconst
  refine ⟨δ, hδ, fun K hK => ?_⟩
  -- the thresholds
  obtain ⟨Np, hNp⟩ := hprof (1 / 8) (by norm_num) K
  obtain ⟨Nm, hNm⟩ := hmod (1 / 8) (by norm_num) (by norm_num) K
  obtain ⟨Nr, hNr⟩ := hch (1 / 8) (by norm_num) K
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (eventually_sqrt_mul_log_le (128 * Cstar * (1 + Real.sqrt m) ^ 2) one_pos)
  obtain ⟨s₃, hs₃⟩ := eventually_atTop.1
    (eventually_log_pow_le (12 * Csl ^ 2 / δ) 4 (a := 4 / 5) (by norm_num))
  obtain ⟨s₄, hs₄⟩ := eventually_atTop.1
    (eventually_log_pow_le (200 * ((1 + b) * (36 * Csl + 3 * Ccl))) 2 (a := 2 / 5) (by norm_num))
  refine ⟨max (max Np Nm) (max Nr (max N₂ (8 * max (max s₃ s₄) 3))),
    fun A N hN hst s hs1 hs2 hvar => ?_⟩
  have hst' := hst
  obtain ⟨hK10, hA, -, -, hreg⟩ := hst'
  have hNp' : Np ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNm' : Nm ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNr' : Nr ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₂' : N₂ ≤ N :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hNs₀ : 8 * max (max s₃ s₄) 3 ≤ N :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN
  have hss₀ : max (max s₃ s₄) 3 ≤ s := by linarith only [hNs₀, hs1]
  have hs3 : 3 ≤ s := (le_max_right _ _).trans hss₀
  have hss₃ : s₃ ≤ s := ((le_max_left _ _).trans (le_max_left _ _)).trans hss₀
  have hss₄ : s₄ ≤ s := ((le_max_right _ _).trans (le_max_left _ _)).trans hss₀
  have hs0 : 0 < s := by linarith only [hs3]
  have hsN : s ≤ N := by linarith only [hs2, hs0]
  have hsl' : (1 / 8 : ℝ) * N ≤ s := by linarith only [hs1]
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hQ : 0 < Q K A s := Profiles.Q_pos hA0 hs0
  have hW : 0 < W K A s := Real.sqrt_pos.2 (mul_pos hs0 hQ)
  have hWs : W K A s * (1 + Real.sqrt m) ≤ s / 4 :=
    W_mul_le_of_regime hK10 hA0.le hreg hs0 hsN hs1 (by simpa using hN₂ N hN₂')
  exact excess_le_at_scale hm X hX hb hCC hCsl hCcl.le hCpr hκ0 hδ hl0 hη.le hT₀
    hnet hconst hκc' hsl hcol (fun t ht => (hcl t ht).2.2) hs3 hW hQ hWs
    (rpow_le_Q hK10 hA (by linarith only [hs3]))
    (variance_TRV_le_pair X hK10 hA0 hs0 hδ.le hvar)
    (isOs_slabTime_sub_dist_pair X hb hs0 hW hQ hCpr hWs
      (fun p hp => (hNp A N hNp' hst s hsl' hsN p hp).2))
    (lintegral_modulusSup_pair X hs0 hW (fun p hp => hNm A N hNm' hst s hsl' hsN p hp))
    (hNr A N hNr' hst ⌈s⌉₊ s (Nat.one_le_ceil_iff.2 hs0) hsl' hs2) (hs₃ s hss₃) (hs₄ s hss₄)

end IsotropicVariance.Paper.Proofs.SmallMean
