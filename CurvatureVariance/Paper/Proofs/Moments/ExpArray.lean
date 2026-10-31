/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Moments.ExpArrayBounds
import CurvatureVariance.Paper.Proofs.Moments.Scales
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.SupportAngular
import CurvatureVariance.Paper.Proofs.Moments.ParentBounds

/-!
# Equation `eq:rowenergy`: the exponential array bound

`expArray_of`: the contract `Contracts.ExpArrayStatement` (equation `eq:rowenergy` of Lemma
`lem:rowenergy`) from Proposition `prop:profiles` for `s ≤ N/2`
(`Contracts.ProfilesShortStatement`) and equation `eq:support` (`Contracts.SupportStatement`); the
width margin is `exists_width_margin`, from equation `eq:scales`.

The proof follows the proof of Lemma `lem:rowenergy`, that of [AB26, Lemma 4.3] with the changes of
the paper: fix a subgradient `P_t` of `μ` at `(1, t)`; for `N` large the scale facts `Scale` hold
(`scale_of`); the lower bound `exists_lower` (entries, slab variables with mean at most two by
Proposition `prop:profiles`, independence
over the slabs and the sum over index paths keeping half the quadratic term) and the upper bound
`exists_upper` (the floor tuple) combine ([AKM, Lemma A.4]) into equation `eq:rowenergy`, with
constants `c = c₀/4` and `C` independent of `M`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

namespace ExpArray

/-- The scale facts hold for `s ≥ √N`, `N ≥ max(2, 9216 m, r₁^{−5})²` and the width margin. -/
theorem scale_of {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {r₁ : ℝ} (hr₁ : 0 < r₁) {N Ms s : ℕ} (hMs : 128 ≤ Ms)
    (hN : (max 2 (max (9216 * (m : ℝ)) ((1 / r₁) ^ 5))) ^ 2 ≤ N) (hs : Real.sqrt N ≤ s)
    (hW : W M K A s ≤ 1 / (32 * (Real.sqrt m + 1)) * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100))
    {z : Fin m → ℤ}
    (hz : ‖transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
      2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4))) :
    Scale M K A s Ms (targetSlope (Ms * s) z) r₁ := by
  have hδ1 := hM.delta_le_one
  have hδ := hM.delta_pos
  set S₀ : ℝ := max 2 (max (9216 * (m : ℝ)) ((1 / r₁) ^ 5)) with hS₀
  have hS₀2 : (2 : ℝ) ≤ S₀ := le_max_left _ _
  have hsS : S₀ ≤ s :=
    calc S₀ = Real.sqrt (S₀ ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hN
      _ ≤ s := hs
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hspos : (0 : ℝ) < s := by linarith
  have hs2 : 2 ≤ s := by exact_mod_cast hS₀2.trans hsS
  have hMspos : 0 < Ms * s := Nat.mul_pos (by omega) (by omega)
  have hMsR : (0 : ℝ) < ((Ms * s : ℕ) : ℝ) := by exact_mod_cast hMspos
  refine ⟨hK, hA, hs2, hMs, ?_, ?_, ?_, ?_⟩
  · have heq : targetSlope (Ms * s) z - M.t₀ =
        (((Ms * s : ℕ) : ℝ))⁻¹ • (transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀) := by
      rw [targetSlope, smul_sub, inv_smul_smul₀ hMsR.ne']
    rw [heq, norm_smul, norm_inv, Real.norm_of_nonneg hMsR.le, inv_mul_le_iff₀ hMsR]
    calc ‖transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
          2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := hz
      _ = ((Ms * s : ℕ) : ℝ) * (2 * ((Ms * s : ℕ) : ℝ) ^ (M.δ / 100 - 1 / 4)) := by
        rw [Real.rpow_add hMsR, Real.rpow_one]; ring
  · calc W M K A s ≤ 1 / (32 * (Real.sqrt m + 1)) * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := hW
      _ = _ := by ring
  · have h1 : (9216 * m : ℝ) ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hsS)
    have h2 : Real.sqrt s ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
    have h3 : 96 * Real.sqrt m = Real.sqrt (9216 * m) := by
      rw [Real.sqrt_mul (by norm_num), show (9216 : ℝ) = 96 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h3]
    exact (Real.sqrt_le_sqrt h1).trans h2
  · have h1 : (1 / r₁) ^ 5 ≤ (s : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hsS)
    have h2 : (s : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ (s : ℝ) ^ (-(1 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
    have h3 : 1 / r₁ ≤ (s : ℝ) ^ (1 / 5 : ℝ) := by
      have h4 : ((1 / r₁) ^ 5) ^ (1 / 5 : ℝ) = 1 / r₁ := by
        rw [show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
      rw [← h4]
      exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    refine h2.trans ?_
    rw [Real.rpow_neg hspos.le, inv_le_comm₀ (by positivity) hr₁]
    simpa only [one_div] using h3

/-- The final combination ([AKM, Lemma A.4]): from `−D + X ≤ a₁ + G₁` and `D ≤ a₂ + G₂`,
`|D| + X ≤ a₁ + 2a₂ + G₁ + 2 max(G₂, 0)`. -/
theorem abs_add_le {D X a₁ a₂ G₁ G₂ B : ℝ} (hL : -D + X ≤ a₁ + G₁) (hU : D ≤ a₂ + G₂)
    (ha₂ : 0 ≤ a₂) (hB : a₁ + 2 * a₂ ≤ B) : |D| + X ≤ B + (G₁ + 2 * max G₂ 0) := by
  have hm2 := le_max_left G₂ 0
  have hm0 := le_max_right G₂ 0
  rcases le_or_gt 0 D with hD | hD
  · rw [abs_of_nonneg hD]; linarith
  · rw [abs_of_neg hD]; linarith

/-- `log(2 Bⁿ) ≤ n log(2B)` for `B ≥ 1`, `n ≥ 1`. -/
theorem log_two_mul_pow_le {B : ℝ} (hB : 1 ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    Real.log (2 * B ^ n) ≤ n * Real.log (2 * B) := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    Real.log_mul (by norm_num) (by positivity)]
  have h1 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 := Real.log_nonneg hB
  nlinarith

end ExpArray

open ExpArray

/-- **Equation `eq:rowenergy`** (the proof of Lemma `lem:rowenergy`), from Proposition
`prop:profiles` for `s ≤ N/2` (`ProfilesShortStatement`), equation `eq:support` (`SupportStatement`)
and equation `eq:scales` (`ScalesStatement`). -/
theorem expArray_of (hShort : Contracts.ProfilesShortStatement m)
    (hSupport : Contracts.SupportStatement m) (hScales : Contracts.ScalesStatement m) :
    Contracts.ExpArrayStatement m := by
  intro bd hbd Cstar
  obtain ⟨c₀, C₀, r₁, hc₀, hC₀, hr₁, -, hsupp₀⟩ := hSupport bd hbd
  obtain ⟨Cb, hCb, hShortB⟩ := hShort bd hbd Cstar 1 le_rfl
  set Bc : ℝ := 2 * (4 / Real.sqrt (min (c₀ / (4 * Cb)) 1)) ^ m with hBc
  have hBc1 : 1 ≤ Bc := by
    have hc' : 0 < c₀ / (4 * Cb) := by positivity
    have h1 : Real.sqrt (min (c₀ / (4 * Cb)) 1) ≤ 1 := Real.sqrt_le_one.mpr (min_le_right _ _)
    have h2 : 0 < Real.sqrt (min (c₀ / (4 * Cb)) 1) := Real.sqrt_pos.mpr (lt_min hc' one_pos)
    have h3 : 1 ≤ 4 / Real.sqrt (min (c₀ / (4 * Cb)) 1) := by rw [le_div_iff₀ h2]; linarith
    have h4 : 1 ≤ (4 / Real.sqrt (min (c₀ / (4 * Cb)) 1)) ^ m := one_le_pow₀ h3
    linarith
  have hlogBc : 0 ≤ Real.log (2 * Bc) := Real.log_nonneg (by linarith)
  have hlog4 : 0 ≤ Real.log (2 * 2) := Real.log_nonneg (by norm_num)
  set Cfin : ℝ := 3 * Cb + (9 * c₀ * m + 8 * C₀) + Cb * Real.log (2 * Bc) +
    2 * ((C₀ * m + 8 * C₀) + Cb * Real.log (2 * 2)) with hCf
  have hCfin : 0 < Cfin := by positivity
  refine ⟨c₀ / 4, Cfin, by positivity, hCfin, fun K hK => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hShortB K hK
  obtain ⟨N₂, hN₂⟩ := exists_width_margin hScales bd hbd Cstar
    (η := 1 / (32 * (Real.sqrt m + 1))) (by positivity)
  refine ⟨max N₁ (max N₂ ⌈(max 2 (max (9216 * (m : ℝ)) ((1 / r₁) ^ 5))) ^ 2⌉₊),
    fun M hM hfit N hN A hA hPrem hRange Ms s hMs hs hMsN z hz => ?_⟩
  have := hM.probP
  obtain ⟨hsupp, -⟩ := hsupp₀ M hM hfit
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3' : ⌈(max 2 (max (9216 * (m : ℝ)) ((1 / r₁) ^ 5))) ^ 2⌉₊ ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN3 : (max 2 (max (9216 * (m : ℝ)) ((1 / r₁) ^ 5))) ^ 2 ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN3')
  have hsc := scale_of hM hK hA hr₁ hMs hN3 hs
    (hN₂ K hK M hM hfit N hN2 A hA hRange s (by have := Real.sqrt_nonneg (N : ℝ); linarith)) hz
  have hMspos : 0 < Ms * s := Nat.mul_pos (by omega) (by have := hsc.two_le; omega)
  have hsN2 : (s : ℝ) ≤ N / 2 := by
    have h1 : ((Ms * s : ℕ) : ℝ) = Ms * s := by push_cast; ring
    have hMs' : (128 : ℝ) ≤ Ms := by exact_mod_cast hMs
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    rw [h1] at hMsN
    nlinarith
  have hShortK : ShortAt M K A s Cb :=
    fun t' I I' hp hsl => hN₁ M hM hfit N hN1 A hA hPrem hRange s hs hsN2 t' I I' hp hsl
  obtain ⟨P, hP⟩ := Proofs.Geometry.exists_isSubgradient M.μ (slopeVec (targetSlope (Ms * s) z))
  have hQ := hsc.one_le_Q hM
  have hθ : 0 < Cb * Q M K A s := mul_pos hCb (by linarith)
  obtain ⟨G₁, hG₁, hae₁⟩ := exists_lower hM hsc hCb hShortK hc₀ hC₀ hsupp hP hMspos
  obtain ⟨G₂, hG₂, hae₂⟩ := exists_upper hM hsc hCb hShortK hC₀ (c₀ := c₀) hsupp hP hMspos
  refine ⟨fun ω => G₁ ω + 2 * max (G₂ ω) 0, ?_, ?_⟩
  · have h2 : IsOs M.P 1 (2 * (Cb * Q M K A s)) (fun ω => 2 * max (G₂ ω) 0) :=
      (isOs_mul_iff (by norm_num)).mpr (Parent.isOs_max_zero hG₂)
    refine (isOs_add hG₁ h2 hθ (by positivity)).mono_scale zero_le_one (by positivity) ?_
    have h3 : 3 * Cb ≤ Cfin := by
      have : 0 ≤ 9 * c₀ * m + 8 * C₀ := by positivity
      have : 0 ≤ C₀ * m + 8 * C₀ := by positivity
      have : 0 ≤ Cb * Real.log (2 * Bc) := by positivity
      have : 0 ≤ Cb * Real.log (2 * 2) := by positivity
      rw [hCf]; linarith
    have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ Q M K A s)
    linarith
  filter_upwards [hae₁, hae₂] with ω h1 h2 Y hY
  have hL := h1 Y hY
  have hMs1 : 1 ≤ Ms := by omega
  have hQ0 : 0 ≤ Q M K A s := by linarith
  have hlogL : Cb * Q M K A s * Real.log (2 * Bc ^ Ms) ≤
      Ms * (Cb * Real.log (2 * Bc) * Q M K A s) := by
    have := mul_le_mul_of_nonneg_left (log_two_mul_pow_le hBc1 hMs1) hθ.le
    linarith
  have hlogU : Cb * Q M K A s * Real.log (2 * 2 ^ Ms) ≤
      Ms * (Cb * Real.log (2 * 2) * Q M K A s) := by
    have := mul_le_mul_of_nonneg_left (log_two_mul_pow_le one_le_two hMs1) hθ.le
    linarith
  refine abs_add_le (a₁ := Ms * ((9 * c₀ * m + 8 * C₀) * Q M K A s) +
      Ms * (Cb * Real.log (2 * Bc) * Q M K A s))
    (a₂ := Ms * ((C₀ * m + 8 * C₀) * Q M K A s) + Ms * (Cb * Real.log (2 * 2) * Q M K A s))
    (by linarith) (by linarith) (by positivity) ?_
  rw [hCf]
  have : 0 ≤ Cb * (Ms * Q M K A s) := by positivity
  linarith

end CurvatureVariance.Paper.Moments
