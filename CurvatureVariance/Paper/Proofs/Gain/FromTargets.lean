/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Proofs.Gain.Basic
public import CurvatureVariance.Infra.FPP.Walks
import CurvatureVariance.Infra.FPP.Model
import CurvatureVariance.Paper.Proofs.Chart.Rounding
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds

/-!
# Proposition `prop:gain` from its targets

`gainStatement_of` proves `Contracts.GainStatement` (Proposition `prop:gain`) from
`GainOnTargetsStatement`, by the reduction at the beginning of Section `sec:gain`.
* A target `(ℓ, y)` with `ℓ ∈ [N/8, N]` and `y ∈ 𝒟(ℓ)` is mapped to `(ℓ', y')`: `ℓ' = K⌊ℓ/K⌋` is
  `ℓ` rounded down to a multiple of `K`, and `y'` is given by equation `eq:rounding`
  (`Chart.roundingStatement_holds`) for the point `(ℓ'/ℓ) y`, which lies in the ball centred at
  `ℓ' t₀` of radius `ℓ'^{3/4+δ/100}` since `ℓ' ≤ ℓ`; so `y' ∈ 𝒟(ℓ')` and
  `|y' − (ℓ'/ℓ) y| ≤ 2√(d−1)`.
  For `N` large this is a target of Section `sec:gain`, with `ℓ' = Kn ∈ [N/9, N]`.
* The two points are at `ℓ¹` distance at most `K + (d − 1)⌈(1 + |t₀|)K + 2√(d−1)⌉`, since
  `|y| ≤ (1 + |t₀|)ℓ`. So `T(0,(ℓ,y))` and `T(0,(ℓ',y'))` differ by at most the passage time
  between them, whose second moment is bounded by (W) (`exists_integral_sq_passageTime_le`).
* Then `Var T ≤ 2 Var T' + 2 ‖T − T'‖₂² ≤ (2φ(K) + 2/(K+1)) Q_ℓ²` for `N` large.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-! ### Second moments of passage times between nearby points -/

/-- `‖f‖₂² = ∫ f²`. -/
private theorem eLpNorm_two_sq_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    (hf : MemLp f 2 P) : eLpNorm f 2 P ^ 2 = ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- Doubling two bounds in `ℝ≥0∞`. -/
private theorem two_mul_add_two_mul_le {a b c d : ℝ≥0∞} (h1 : a ≤ c) (h2 : b ≤ d) :
    2 * a + 2 * b ≤ 2 * c + 2 * d := by
  gcongr

/-- Cancel `c` in `(a / c) * (b * c)`. -/
private theorem div_mul_mul_cancel {a b c : ℝ} (hc : c ≠ 0) : a / c * (b * c) = a * b := by
  field_simp

/-- Passage times between points at `ℓ¹` distance at most `L` have a uniformly bounded second
moment, from the exponential moment of (W). The bound depends only on the law of the bounds. -/
theorem exists_integral_sq_passageTime_le {bd : Bounds m} (hbd : bd.Valid) (L : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ u v : Vertex m, Infra.FPP.l1Dist u v ≤ L →
        Integrable (fun ω => passageTimeReal ω u v ^ 2) M.P ∧
          ∫ ω, passageTimeReal ω u v ^ 2 ∂M.P ≤ C := by
  obtain ⟨α, hα, hαi⟩ := hbd.law.assumptionW.1
  set Mα := mgf (fun x : ℝ≥0 => (x : ℝ)) bd.law.F α with hMα
  refine ⟨2 / α ^ 2 * max Mα 1 ^ L, by positivity, fun M hMs hfit u v huv => ?_⟩
  have := hMs.probP
  have := hMs.probF
  rw [← hfit.F_eq] at hαi hMα
  obtain ⟨γ, hγ, hlen⟩ := Infra.FPP.exists_isPath_length_eq_l1Dist u v
  have hexp : Integrable (fun ω => Real.exp (α * (walkCost ω γ : ℝ))) M.P :=
    Infra.FPP.IsIIDWeights.integrable_exp_mul_walkCost hMs.iid γ hγ.edges_nodup hαi
  have hpt : ∀ ω, passageTimeReal ω u v ^ 2 ≤ 2 / α ^ 2 * Real.exp (α * (walkCost ω γ : ℝ)) := by
    intro ω
    have hT0 : 0 ≤ passageTimeReal ω u v := NNReal.coe_nonneg _
    have hTle : passageTimeReal ω u v ≤ (walkCost ω γ : ℝ) := by
      exact_mod_cast Infra.FPP.passageTime_le_walkCost ω γ
    have hq := Real.quadratic_le_exp_of_nonneg
      (mul_nonneg hα.le (NNReal.coe_nonneg (walkCost ω γ)))
    have hsq : passageTimeReal ω u v ^ 2 ≤ (walkCost ω γ : ℝ) ^ 2 :=
      pow_le_pow_left₀ hT0 hTle 2
    have hW0 : 0 ≤ (walkCost ω γ : ℝ) := NNReal.coe_nonneg _
    have h1 : (α * (walkCost ω γ : ℝ)) ^ 2 / 2 ≤ Real.exp (α * (walkCost ω γ : ℝ)) := by
      linarith only [hq, mul_nonneg hα.le hW0]
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hα 2)]
    have h2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg α)
    have e : (walkCost ω γ : ℝ) ^ 2 * α ^ 2 = (α * (walkCost ω γ : ℝ)) ^ 2 := by ring
    linarith only [h1, h2, e]
  have hTm : Measurable fun ω : Config m => passageTimeReal ω u v ^ 2 :=
    (Infra.FPP.measurable_passageTime_real u v).pow_const 2
  have hint : Integrable (fun ω => passageTimeReal ω u v ^ 2) M.P :=
    (hexp.const_mul (2 / α ^ 2)).mono' hTm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ω)
  refine ⟨hint, ?_⟩
  have hmgf : ∫ ω, Real.exp (α * (walkCost ω γ : ℝ)) ∂M.P = Mα ^ γ.length :=
    by rw [hMα]; exact Infra.FPP.IsIIDWeights.mgf_walkCost hMs.iid γ hγ.edges_nodup α
  have hMα1 : 1 ≤ max Mα 1 := le_max_right _ _
  calc ∫ ω, passageTimeReal ω u v ^ 2 ∂M.P
      ≤ ∫ ω, 2 / α ^ 2 * Real.exp (α * (walkCost ω γ : ℝ)) ∂M.P :=
        integral_mono hint (hexp.const_mul _) hpt
    _ = 2 / α ^ 2 * Mα ^ γ.length := by rw [integral_const_mul, hmgf]
    _ ≤ 2 / α ^ 2 * max Mα 1 ^ L := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc Mα ^ γ.length ≤ max Mα 1 ^ γ.length := by
              have hM0 : 0 ≤ Mα := by
                rw [hMα, mgf]; exact integral_nonneg fun x => (Real.exp_pos _).le
              exact pow_le_pow_left₀ hM0 (le_max_left _ _) _
          _ ≤ max Mα 1 ^ L := pow_le_pow_right₀ hMα1 (by omega)

/-! ### The reduction -/

/-- **Proposition `prop:gain` at the lengths `ℓ = Kn`** (the statement on the targets of Section
`sec:gain`, `ℓ = Kn ∈ [N/9, N]` and `y ∈ 𝒟(ℓ)`): there is `φ(K) = o_K(1)` such that, for `K` large,
`N` large under equation `eq:premise` and every target `(ℓ, y)`, `ℓ = Kn`,
`Var T(0,(ℓ,y)) ≤ φ(K) Q_ℓ²`. It has the body of `Contracts.GainOnTargetsStatement`. -/
def GainOnTargetsStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ φ : ℕ → ℝ, Tendsto φ atTop (𝓝 0) ∧
  ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
    evariance (fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y)) M.P ≤
      ENNReal.ofReal (φ K * Q M K A ℓ ^ 2)

/-- **Proposition `prop:gain`** from its case of the targets of Section `sec:gain`, by the
reduction at the beginning of that section.
Its constants and thresholds come before the model and depend only on the bounds `bd`. -/
theorem gainStatement_of (hT : GainOnTargetsStatement m) : GainStatement m := by
  intro bd hbd Cstar
  obtain ⟨φ, hφ, K₀, hT⟩ := hT bd hbd Cstar
  refine ⟨fun K => 2 * max (φ K) 0 + 2 / ((K : ℝ) + 1), ?_, K₀, fun K hK₀ hK => ?_⟩
  · have h1 : Tendsto (fun K : ℕ => 2 * max (φ K) 0) atTop (𝓝 0) := by
      simpa only [max_self, mul_zero] using
        (hφ.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))).const_mul 2
    have h2 : Tendsto (fun K : ℕ => 2 / ((K : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
      rw [mul_zero] at this
      exact this.congr fun K => mul_one_div _ _
    simpa only [add_zero] using h1.add h2
  obtain ⟨N₀, hN₀⟩ := hT K hK₀ hK
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  set D : ℕ := ⌈(1 + bd.T) * K + 2 * Real.sqrt m⌉₊ with hDdef
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_integral_sq_passageTime_le hbd (K + m * D)
  set e : ℝ := (1 : ℝ) / 2 - bd.law.δ / K with he
  have he0 : 0 < e := by
    have h1 : bd.law.δ / K ≤ 1 / K := div_le_div_of_nonneg_right hbd.law.delta_le_one hKr.le
    have h2 : (1 : ℝ) / K < 1 / 2 := by
      rw [div_lt_div_iff₀ hKr (by norm_num)]
      have : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
      linarith only [this]
    rw [he]
    linarith only [h1, h2]
  -- `N` large: `(N/8)^{2e} ≥ (K+1) C₂` and `N ≥ 72 K + 36 m + 8`
  have hgrow : Tendsto (fun N : ℕ => ((N : ℝ) / 8) ^ (2 * e)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith only [he0])).comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hgrow.eventually_ge_atTop (((K : ℝ) + 1) * C₂))
  refine ⟨max (max N₀ N₁) (72 * K + 36 * m + 8),
    fun M hMs hfit N hN A hA hp hr ℓ hℓ8 hℓN y hy => ?_⟩
  have := hMs.probP
  have hMe : (1 : ℝ) / 2 - M.δ / K = e := by rw [he, hfit.δ_eq]
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN72 : 72 * K + 36 * m + 8 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : ((72 * K + 36 * m + 8 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN72
  push_cast at hNr
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hℓpos : (0 : ℝ) < ℓ := by linarith only [hℓ8, hNr, hm0, hKr]
  have hℓpos' : 0 < ℓ := by exact_mod_cast hℓpos
  -- the target of Section `sec:gain`
  set n := ℓ / K with hn
  set ℓ' := K * n with hℓ'
  have hℓ'le : ℓ' ≤ ℓ := Nat.mul_div_le ℓ K
  have hℓ'gt : (ℓ : ℝ) - K < ℓ' := by
    have h := Nat.lt_mul_div_succ ℓ hKpos
    have : ((ℓ : ℕ) : ℝ) < ((K * (ℓ / K + 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    simp only [hℓ', hn]; push_cast; linarith only [this]
  have hℓ'r : (ℓ' : ℝ) ≤ ℓ := by exact_mod_cast hℓ'le
  have hℓ'pos : (0 : ℝ) < ℓ' := by linarith only [hℓ'gt, hℓ8, hNr, hm0, hKr]
  have hℓ'4m : 4 * (m : ℝ) ≤ ℓ' := by linarith only [hℓ'gt, hℓ8, hNr, hm0, hKr]
  have hexp1 : (3 : ℝ) / 4 + M.δ / 100 ≤ 1 := by have := hMs.delta_le_one; linarith only [this]
  set a : ℝ := (3 : ℝ) / 4 + M.δ / 100 with ha
  -- the rounded target, by equation `eq:rounding` (the beginning of Section `sec:gain`)
  set x : EuclideanSpace ℝ (Fin m) := ((ℓ' : ℝ) / ℓ) • transversePoint y with hxdef
  have hxc : ‖x - (ℓ' : ℝ) • M.t₀‖ ≤ (ℓ' : ℝ) ^ a := by
    have e1 : x - (ℓ' : ℝ) • M.t₀ = ((ℓ' : ℝ) / ℓ) • (transversePoint y - (ℓ : ℝ) • M.t₀) := by
      rw [hxdef, smul_sub, smul_smul, div_mul_cancel₀ _ hℓpos.ne']
    have hc : 0 ≤ (ℓ' : ℝ) / ℓ := div_nonneg hℓ'pos.le hℓpos.le
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    refine (mul_le_mul_of_nonneg_left hy hc).trans ?_
    -- `(ℓ'/ℓ) ℓ^{a} ≤ ℓ'^{a}` for `a ≤ 1`
    have h1 : (ℓ' : ℝ) / ℓ * (ℓ : ℝ) ^ a = (ℓ' : ℝ) * (ℓ : ℝ) ^ (a - 1) := by
      rw [Real.rpow_sub hℓpos, Real.rpow_one]; field_simp
    have h2 : (ℓ' : ℝ) ^ a = (ℓ' : ℝ) * (ℓ' : ℝ) ^ (a - 1) := by
      rw [Real.rpow_sub hℓ'pos, Real.rpow_one]; field_simp
    rw [h1, h2]
    refine mul_le_mul_of_nonneg_left ?_ hℓ'pos.le
    exact Real.rpow_le_rpow_of_nonpos hℓ'pos hℓ'r (by linarith only [hexp1])
  have hR : 2 * Real.sqrt m ≤ (ℓ' : ℝ) ^ a := by
    have h1 : 2 * Real.sqrt m ≤ Real.sqrt ℓ' := by
      rw [show 2 * Real.sqrt m = Real.sqrt (4 * m) by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      exact Real.sqrt_le_sqrt hℓ'4m
    have hℓ'1 : (1 : ℝ) ≤ ℓ' := by linarith only [hℓ'gt, hℓ8, hNr, hm0, hKr]
    refine h1.trans ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hℓ'1 (by linarith only [ha, hMs.delta_pos])
  obtain ⟨y', hy'c, hy'x⟩ :=
    Chart.roundingStatement_holds (m := m) ((ℓ' : ℝ) • M.t₀) x ((ℓ' : ℝ) ^ a) hR hxc
  have htarget : IsTarget M K N n ℓ' y' :=
    ⟨rfl, by linarith only [hℓ'gt, hℓ8, hNr, hm0, hKr], le_trans hℓ'le hℓN, hy'c⟩
  have hvar' := hN₀ M hMs hfit N hN0 A hA hp hr n ℓ' y' htarget
  -- the two points are close
  have hdist : Infra.FPP.l1Dist ((ℓ : ℤ), y) ((ℓ' : ℤ), y') ≤ K + m * D := by
    have hl : (((ℓ : ℤ) - ℓ').natAbs : ℝ) ≤ K := by
      rw [Nat.cast_natAbs, Int.cast_abs]; push_cast
      rw [abs_of_nonneg (by linarith only [hℓ'r])]; linarith only [hℓ'gt]
    have hyx : ‖transversePoint y - x‖ ≤ (1 + bd.T) * K := by
      have e1 : transversePoint y - x = (((ℓ : ℝ) - ℓ') / ℓ) • transversePoint y := by
        rw [hxdef, sub_div, div_self hℓpos.ne', sub_smul, one_smul]
      have hc : 0 ≤ ((ℓ : ℝ) - ℓ') / ℓ := div_nonneg (sub_nonneg.2 hℓ'r) hℓpos.le
      rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      have hyn := Responses.target_norm_le_length hMs (by exact_mod_cast hℓpos') hy
      calc ((ℓ : ℝ) - ℓ') / ℓ * ‖transversePoint y‖ ≤ ((ℓ : ℝ) - ℓ') / ℓ * ((1 + ‖M.t₀‖) * ℓ) :=
            mul_le_mul_of_nonneg_left hyn hc
        _ = ((ℓ : ℝ) - ℓ') * (1 + ‖M.t₀‖) := div_mul_mul_cancel hℓpos.ne'
        _ ≤ K * (1 + bd.T) :=
            mul_le_mul (by linarith only [hℓ'gt]) (by linarith only [hfit.t₀_le])
              (add_nonneg zero_le_one (norm_nonneg _)) hKr.le
        _ = (1 + bd.T) * K := by ring
    have htp : transversePoint (y - y') = transversePoint y - transversePoint y' := by
      ext j
      simp [transversePoint]
    have hyy : ‖transversePoint (y - y')‖ ≤ D := by
      rw [htp]
      calc ‖transversePoint y - transversePoint y'‖
          = ‖(transversePoint y - x) + (x - transversePoint y')‖ := by
            congr 1; abel
        _ ≤ ‖transversePoint y - x‖ + ‖x - transversePoint y'‖ := norm_add_le _ _
        _ ≤ (1 + bd.T) * K + 2 * Real.sqrt m := by
            rw [norm_sub_rev x]
            linarith only [hyx, hy'x]
        _ ≤ D := Nat.le_ceil _
    have hj : ∀ j, (((y j - y' j : ℤ)).natAbs : ℝ) ≤ D := by
      intro j
      rw [Nat.cast_natAbs, Int.cast_abs]
      have h := Responses.abs_coord_le_norm_transversePoint (y - y') j
      simp only [Pi.sub_apply] at h
      exact h.trans hyy
    have hsum : ((∑ j, (y j - y' j).natAbs : ℕ) : ℝ) ≤ m * D := by
      push_cast
      calc ∑ j, (((y j - y' j).natAbs : ℕ) : ℝ) ≤ ∑ _j : Fin m, (D : ℝ) :=
            Finset.sum_le_sum fun j _ => hj j
        _ = m * D := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ((Infra.FPP.l1Dist ((ℓ : ℤ), y) ((ℓ' : ℤ), y') : ℕ) : ℝ) ≤
        ((K + m * D : ℕ) : ℝ) := by
      unfold Infra.FPP.l1Dist
      push_cast at hsum ⊢
      linarith only [hl, hsum]
    exact_mod_cast this
  obtain ⟨hint2, hC₂'⟩ := hC₂ M hMs hfit _ _ hdist
  -- `‖T − T'‖₂² ≤ C₂`
  have hdiff : eLpNorm ((fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y)) -
      fun ω => passageTimeReal ω 0 ((ℓ' : ℤ), y')) 2 M.P ^ 2 ≤ ENNReal.ofReal C₂ := by
    have hpt : ∀ ω, |passageTimeReal ω 0 ((ℓ : ℤ), y) - passageTimeReal ω 0 ((ℓ' : ℤ), y')| ≤
        passageTimeReal ω ((ℓ : ℤ), y) ((ℓ' : ℤ), y') := by
      intro ω
      have h := Infra.FPP.abs_passageTime_sub_le ω 0 ((ℓ : ℤ), y) 0 ((ℓ' : ℤ), y')
      simpa [passageTimeReal, Infra.FPP.passageTime_self] using h
    have hS2 : MemLp (fun ω => passageTimeReal ω ((ℓ : ℤ), y) ((ℓ' : ℤ), y')) 2 M.P :=
      (memLp_two_iff_integrable_sq
        (Infra.FPP.measurable_passageTime_real _ _).aestronglyMeasurable).2 hint2
    have hmono : eLpNorm ((fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y)) -
        fun ω => passageTimeReal ω 0 ((ℓ' : ℤ), y')) 2 M.P ≤
        eLpNorm (fun ω => passageTimeReal ω ((ℓ : ℤ), y) ((ℓ' : ℤ), y')) 2 M.P :=
      eLpNorm_mono_real (((Infra.FPP.measurable_passageTime_real _ _).sub
        (Infra.FPP.measurable_passageTime_real _ _)).aestronglyMeasurable) fun ω => by
        rw [Pi.sub_apply, Real.norm_eq_abs]
        exact hpt ω
    calc _ ≤ eLpNorm (fun ω => passageTimeReal ω ((ℓ : ℤ), y) ((ℓ' : ℤ), y')) 2 M.P ^ 2 :=
          pow_le_pow_left₀ bot_le hmono 2
      _ = _ := eLpNorm_two_sq_eq hS2
      _ ≤ ENNReal.ofReal C₂ := ENNReal.ofReal_le_ofReal hC₂'
  have key := evariance_le_two_mul_add (P := M.P) (X := fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y))
    (Y := fun ω => passageTimeReal ω 0 ((ℓ' : ℤ), y'))
    (Infra.FPP.measurable_passageTime_real _ _).aestronglyMeasurable
  refine key.trans ?_
  -- assemble
  have hQ : Q M K A ℓ' ≤ Q M K A ℓ := by
    unfold Q
    rw [hMe]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hℓ'pos.le hℓ'r he0.le) (by linarith only [hA])
  have hQ0 : 0 ≤ Q M K A ℓ' :=
    mul_nonneg (by linarith only [hA]) (Real.rpow_nonneg hℓ'pos.le _)
  have hQℓ2 : ((K : ℝ) + 1) * C₂ ≤ Q M K A ℓ ^ 2 := by
    have h1 := hN₁ N hN1
    have h2 : ((N : ℝ) / 8) ^ (2 * e) ≤ (ℓ : ℝ) ^ (2 * e) :=
      Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg N) (by norm_num)) hℓ8
        (by linarith only [he0])
    have h3 : (ℓ : ℝ) ^ (2 * e) ≤ Q M K A ℓ ^ 2 := by
      unfold Q
      rw [hMe, mul_pow, ← Real.rpow_natCast ((ℓ : ℝ) ^ e) 2, ← Real.rpow_mul hℓpos.le]
      have : (1 : ℝ) ≤ A ^ 2 := one_le_pow₀ hA
      rw [show e * ((2 : ℕ) : ℝ) = 2 * e by push_cast; ring]
      calc (ℓ : ℝ) ^ (2 * e) = 1 * (ℓ : ℝ) ^ (2 * e) := (one_mul _).symm
        _ ≤ A ^ 2 * (ℓ : ℝ) ^ (2 * e) :=
            mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hℓpos.le _)
    linarith only [h1, h2, h3]
  have hC₂Q : C₂ ≤ 1 / ((K : ℝ) + 1) * Q M K A ℓ ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith only [hKr])]
    linarith only [hQℓ2]
  have hT' : evariance (fun ω => passageTimeReal ω 0 ((ℓ' : ℤ), y')) M.P ≤
      ENNReal.ofReal (max (φ K) 0 * Q M K A ℓ ^ 2) :=
    hvar'.trans (ENNReal.ofReal_le_ofReal (by
      calc φ K * Q M K A ℓ' ^ 2 ≤ max (φ K) 0 * Q M K A ℓ' ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
        _ ≤ max (φ K) 0 * Q M K A ℓ ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQ 2) (le_max_right _ _)))
  have h1 : 0 ≤ max (φ K) 0 * Q M K A ℓ ^ 2 := mul_nonneg (le_max_right _ _) (sq_nonneg _)
  calc 2 * evariance (fun ω => passageTimeReal ω 0 ((ℓ' : ℤ), y')) M.P +
        2 * eLpNorm ((fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y)) -
          fun ω => passageTimeReal ω 0 ((ℓ' : ℤ), y')) 2 M.P ^ 2
      ≤ 2 * ENNReal.ofReal (max (φ K) 0 * Q M K A ℓ ^ 2) + 2 * ENNReal.ofReal C₂ :=
        two_mul_add_two_mul_le hT' hdiff
    _ = ENNReal.ofReal (2 * (max (φ K) 0 * Q M K A ℓ ^ 2) + 2 * C₂) := by
        rw [ENNReal.ofReal_add (mul_nonneg zero_le_two h1) (mul_nonneg zero_le_two hC₂0),
          ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal ((2 * max (φ K) 0 + 2 / ((K : ℝ) + 1)) * Q M K A ℓ ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : 2 / ((K : ℝ) + 1) * Q M K A ℓ ^ 2 = 2 * (1 / ((K : ℝ) + 1) * Q M K A ℓ ^ 2) := by
          ring
        linarith only [hC₂Q, this]

end CurvatureVariance.Paper.Gain
