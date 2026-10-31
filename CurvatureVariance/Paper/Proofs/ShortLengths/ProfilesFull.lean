/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.ShortLengths.ProfilesShort
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.Moments.Links
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proposition `prop:profiles`: the statement `ProfilesStatement`

The proof of Proposition `prop:profiles` for `κN ≤ s ≤ 2N`: "The proof for `s ≤ N/2` applies,
with equation `eq:parent` in place of equation `eq:premise` at the lengths `9s/8` and `7s/8`, which
lie in `[κN/2, 3N]`. Lemma `lem:tree` still applies at the length `s/16`, since
`(3/2) 16^{δ/100−1/4} < 4/5`."

As in the continuum library (`IsotropicVariance.Paper.Proofs.Profiles.profilesStatement_of`): the
first case is the contract
`ProfilesShortStatement`, and the second is `exists_profile_bounds` with the line bound from
equation `eq:parent` (`lineBound_of_parent`, for the continuum's `line_of_parent` and
`lineAbs_of_parent`). The margin `(3/2) 16^{δ/100−1/4} < 4/5` is `slope_le_sixteen`, which is
inside `exists_profile_bounds`.

* `exists_link_domain`: the displacement of a link lies in the domain `|y − ℓt₀| ≤ Θ ℓ^{3/4+δ/100}`,
  for `Θ ≥ 1`. It is `exists_premise_link` without equation `eq:premise`.
* `parent_slope_le`: `λ|t − t₀| ≤ (27/16) λ^{3/4+δ/100}` for `λ ≤ 9s/8` and
  `|t − t₀| ≤ (3/2) s^{δ/100−1/4}`, the room left by the range `7/4` of equation `eq:parent`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- **A link in the domain of radius `Θ`.** If the displacement of `x' − x` is `λ(1, t) + (0, ω)` up
to `ε₀`, then `x'₁ − x₁` is an integer `ℓ ≥ 1` within `ε₀` of `λ`, and
`|(x' − x)₂ − ℓt₀| ≤ Θ ℓ^{3/4+δ/100}`. As `exists_premise_link`, with the radius `Θ` in place
of `1`. -/
theorem exists_link_domain {M : Model m} (hM : M.Standing) {x x' : Vertex m} {t ω : E}
    {lam ε₀ θ Θ : ℝ} (hε₀ : 1 ≤ ε₀) (hΘ : 0 ≤ Θ)
    (hdisp : ‖(point x' - point x) - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))‖ ≤ ε₀)
    (hlam : ε₀ + 1 ≤ lam) (hslope : lam * ‖t - M.t₀‖ ≤ θ * lam ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hmargin : ‖ω‖ + (2 + ‖M.t₀‖ + Θ) * ε₀ ≤ (Θ - θ) * lam ^ ((3 : ℝ) / 4 + M.δ / 100)) :
    ∃ ℓ : ℕ, x'.1 - x.1 = ℓ ∧ 1 ≤ ℓ ∧ |(ℓ : ℝ) - lam| ≤ ε₀ ∧
      ‖transversePoint (x'.2 - x.2) - (ℓ : ℝ) • M.t₀‖ ≤
        Θ * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  set e : ℝ := (3 : ℝ) / 4 + M.δ / 100 with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by rw [he]; linarith only [hδ1]
  have hfst := Proofs.Geometry.abs_fst_le_norm ((point x' - point x) - (lam • slopeVec t +
    WithLp.toLp 2 ((0 : ℝ), ω)))
  rw [Moments.fst_sub_link] at hfst
  have hsnd := Proofs.Geometry.norm_snd_le_norm ((point x' - point x) - (lam • slopeVec t +
    WithLp.toLp 2 ((0 : ℝ), ω)))
  rw [Moments.snd_sub_link] at hsnd
  have h1 := (abs_le.mp (hfst.trans hdisp))
  -- the longitudinal displacement
  have hpos : (1 : ℝ) ≤ ((x'.1 - x.1 : ℤ) : ℝ) := by push_cast; linarith only [h1.1, hlam]
  have hposZ : (1 : ℤ) ≤ x'.1 - x.1 := by exact_mod_cast hpos
  set ℓ : ℕ := (x'.1 - x.1).toNat with hℓ
  have hℓZ : x'.1 - x.1 = (ℓ : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  have hℓR : (ℓ : ℝ) = (x'.1 : ℝ) - x.1 := by
    have : ((ℓ : ℤ) : ℝ) = ((x'.1 - x.1 : ℤ) : ℝ) := by rw [hℓZ]
    push_cast at this; exact_mod_cast this
  have hℓ1 : 1 ≤ ℓ := by have : (1 : ℤ) ≤ (ℓ : ℤ) := hℓZ ▸ hposZ; exact_mod_cast this
  have hℓlam : |(ℓ : ℝ) - lam| ≤ ε₀ := by rw [hℓR, abs_le]; exact h1
  refine ⟨ℓ, hℓZ, hℓ1, hℓlam, ?_⟩
  -- the transverse displacement
  have hlam0 : 0 ≤ lam := by linarith only [hlam, hε₀]
  have hsplit : transversePoint (x'.2 - x.2) - (ℓ : ℝ) • M.t₀ =
      (transversePoint (x'.2 - x.2) - (lam • t + ω)) + (lam • (t - M.t₀) + ω) +
        (lam - ℓ) • M.t₀ := by
    rw [smul_sub, sub_smul]; abel
  have hn1 : ‖transversePoint (x'.2 - x.2) - (ℓ : ℝ) • M.t₀‖ ≤
      ε₀ + ‖lam • (t - M.t₀) + ω‖ + ‖(lam - ℓ) • M.t₀‖ := by
    rw [hsplit]
    refine (norm_add₃_le).trans ?_
    linarith only [hsnd, hdisp]
  have hn2 : ‖lam • (t - M.t₀) + ω‖ ≤ lam * ‖t - M.t₀‖ + ‖ω‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0]
  have hn3 : ‖(lam - ℓ) • M.t₀‖ ≤ ε₀ * ‖M.t₀‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right hℓlam (norm_nonneg _)
  have hsub : lam ^ e ≤ (lam - ε₀) ^ e + ε₀ := by
    have h := Real.rpow_add_le_add_rpow (a := lam - ε₀) (b := ε₀) (by linarith only [hlam])
      (by linarith only [hε₀]) he0 he1
    rw [sub_add_cancel] at h
    have hε : ε₀ ^ e ≤ ε₀ := by
      calc ε₀ ^ e ≤ ε₀ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hε₀ he1
        _ = ε₀ := Real.rpow_one ε₀
    linarith only [h, hε]
  have hmono : (lam - ε₀) ^ e ≤ (ℓ : ℝ) ^ e :=
    Real.rpow_le_rpow (by linarith only [hlam]) (by linarith only [(abs_le.mp hℓlam).1]) he0
  have hΘe : Θ * lam ^ e ≤ Θ * ((ℓ : ℝ) ^ e + ε₀) :=
    mul_le_mul_of_nonneg_left (by linarith only [hsub, hmono]) hΘ
  have hexp1 : (2 + ‖M.t₀‖ + Θ) * ε₀ = 2 * ε₀ + ε₀ * ‖M.t₀‖ + Θ * ε₀ := by ring
  have hexp2 : (Θ - θ) * lam ^ e = Θ * lam ^ e - θ * lam ^ e := by ring
  have hexp3 : Θ * ((ℓ : ℝ) ^ e + ε₀) = Θ * (ℓ : ℝ) ^ e + Θ * ε₀ := by ring
  linarith only [hn1, hn2, hn3, hslope, hmargin, hΘe, hexp1, hexp2, hexp3, hε₀]

/-- The slope of a link of length `λ ≤ 9s/8`, for `|t − t₀| ≤ (3/2) s^{δ/100−1/4}` (used with
`τ = |t − t₀|`): `λ τ ≤ (27/16) λ^{3/4+δ/100}`, since `(9/8)^{1/4−δ/100} ≤ 9/8`. -/
theorem parent_slope_le {δ s lam τ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hls : lam ≤ 9 / 8 * s) (ht : τ ≤ 3 / 2 * s ^ (δ / 100 - 1 / 4)) :
    lam * τ ≤ 27 / 16 * lam ^ ((3 : ℝ) / 4 + δ / 100) := by
  set e := δ / 100 - 1 / 4 with he
  have he0 : e ≤ 0 := by rw [he]; linarith only [hδ1]
  have he1 : -1 ≤ e := by rw [he]; linarith only [hδ]
  have h1 : s ^ e ≤ (8 / 9 * lam) ^ e :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith only [hls]) he0
  have h2 : ((8 : ℝ) / 9) ^ e ≤ 9 / 8 := by
    calc ((8 : ℝ) / 9) ^ e ≤ ((8 : ℝ) / 9) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) he1
      _ = 9 / 8 := by rw [Real.rpow_neg_one]; norm_num
  have h3 : τ ≤ 27 / 16 * lam ^ e := by
    have h4 : (8 / 9 * lam) ^ e ≤ 9 / 8 * lam ^ e := by
      rw [Real.mul_rpow (by norm_num) hlam.le]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith only [ht, h1, h4]
  rw [show (3 : ℝ) / 4 + δ / 100 = e + 1 by rw [he]; ring, Real.rpow_add hlam, Real.rpow_one]
  calc lam * τ ≤ lam * (27 / 16 * lam ^ e) := mul_le_mul_of_nonneg_left h3 hlam.le
    _ = 27 / 16 * (lam ^ e * lam) := by ring

/-- **Equation `eq:parent` on the line** (the proof of Proposition `prop:profiles` for
`κN ≤ s ≤ 2N`): the two lengths lie in `[κN/2, 3N]`, and the slopes lie in the range `7/4` of
equation `eq:parent`. For the continuum's `IsotropicVariance.Paper.Proofs.Profiles.line_of_parent`,
with stationarity for its `lineAbs_of_parent`. -/
theorem lineBound_of_parent {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {N : ℕ} {κ Cp T : ℝ} (hCp : 0 ≤ Cp) (hTM : ‖M.t₀‖ ≤ T)
    (hpar : ∀ ℓ : ℕ, κ / 2 * N ≤ ℓ → (ℓ : ℝ) ≤ 3 * N → ∀ y : Fin m → ℤ,
      ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤ 7 / 4 * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) →
      CurvatureVariance.IsOs M.P 1 (Q M K A ℓ / 100) (fun ω =>
        |passageTimeReal ω 0 ((ℓ : ℤ), y) - M.μ.1 (point ((ℓ : ℤ), y))| - Cp * Q M K A ℓ))
    {s : ℕ} (hκ : κ * N ≤ s) (hs2 : (s : ℝ) ≤ 2 * N)
    (hsm : 2 * 10 ^ 4 * ((1 + T) ^ 2 * ((m : ℝ) + 1)) ≤ s) {t : E}
    (ht : ‖t - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4)) :
    LineBound M K A s t (2 * (1 / 100 + 2 * Cp)) := by
  intro x x' lam w hlam hw hd
  have := hM.probP
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  obtain ⟨hsq1, hsqs, hs1, hlam1, hlam2, hlamlo⟩ := link_regime hTM hsm hlam
  have hT0 : 0 ≤ ‖M.t₀‖ := norm_nonneg _
  have hs0 : (0 : ℝ) ≤ s := by linarith only [hs1]
  have hsq2 : Real.sqrt ((m : ℝ) + 1) + 1 ≤ lam := by linarith only [hsqs, hsq1, hlam1, hs1]
  have hlam0 : 0 < lam := by linarith only [hsq2, hsq1]
  set e : ℝ := (3 : ℝ) / 4 + M.δ / 100 with he
  have hslope := parent_slope_le hδ.le hδ1 hlam0 hlam2 ht
  -- the margin
  have hmargin : ‖w‖ + (2 + ‖M.t₀‖ + 7 / 4) * Real.sqrt ((m : ℝ) + 1) ≤
      (7 / 4 - 27 / 16) * lam ^ e := by
    have hTq := mul_nonneg hT0 (Real.sqrt_nonneg ((m : ℝ) + 1))
    have h1 := link_margin_le (m := m) hδ.le hT0 hlamlo
      (x := 2 / 3 * (‖w‖ + (2 + ‖M.t₀‖ + 7 / 4) * Real.sqrt ((m : ℝ) + 1))) (by
        have e1 : (2 + ‖M.t₀‖ + 7 / 4) * Real.sqrt ((m : ℝ) + 1) =
            15 / 4 * Real.sqrt ((m : ℝ) + 1) + ‖M.t₀‖ * Real.sqrt ((m : ℝ) + 1) := by ring
        have e2 : (4 + ‖M.t₀‖) * Real.sqrt ((m : ℝ) + 1) =
            4 * Real.sqrt ((m : ℝ) + 1) + ‖M.t₀‖ * Real.sqrt ((m : ℝ) + 1) := by ring
        linarith only [hw, hTq, e1, e2, hsq1])
    have h2 : 0 ≤ lam ^ e := by positivity
    linarith only [h1, h2]
  obtain ⟨ℓ, hℓZ, hℓ1, hℓlam, hy⟩ := exists_link_domain hM hsq1 (by norm_num : (0 : ℝ) ≤ 7 / 4) hd
    hsq2 hslope hmargin
  have hℓ' := abs_le.mp hℓlam
  have hA0 : (0 : ℝ) ≤ A := by linarith only [hA]
  have hℓκ : κ / 2 * N ≤ ℓ := by linarith only [hκ, hℓ'.1, hlam1, hsqs, hs0]
  have hℓ3 : (ℓ : ℝ) ≤ 3 * N := by linarith only [hs2, hℓ'.2, hlam2, hsqs, hs0]
  have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  -- stationarity
  have h := Moments.isOs_comp_measurePreserving (Moments.standing_measurePreserving_translate hM x)
    (hpar ℓ hℓκ hℓ3 (x'.2 - x.2) hy)
  have hx' : x' = x + ((ℓ : ℤ), x'.2 - x.2) := by
    ext
    · simp only [Prod.fst_add]; omega
    · simp
  have hpt : point ((ℓ : ℤ), x'.2 - x.2) = point x' - point x := by
    rw [← Infra.FPP.point_sub]; congr 1; ext
    · simp only [Prod.fst_sub]; omega
    · simp
  have h' : CurvatureVariance.IsOs M.P 1 (Q M K A ℓ / 100) (fun ω =>
      |passageTimeReal ω x x' - M.μ.1 (point x' - point x)| - Cp * Q M K A ℓ) := by
    have h'' : CurvatureVariance.IsOs M.P 1 (Q M K A ℓ / 100) (fun ω =>
        |passageTimeReal ω x (x + ((ℓ : ℤ), x'.2 - x.2)) - M.μ.1 (point x' - point x)| -
          Cp * Q M K A ℓ) := by
      simpa only [Moments.passageTimeReal_translate, zero_add, add_comm x, hpt] using h
    rwa [← hx'] at h''
  have hQ1 := one_le_Q hM hK hA hℓ1'
  have hQℓ : Q M K A ℓ ≤ 2 * Q M K A s :=
    Q_le_two_mul hM hK hA0 (by linarith only [hℓ1']) hs0
      (by linarith only [hℓ'.2, hlam2, hsqs, hs0])
  have h2 := Moments.isOs_add_const h' (by positivity) (by positivity : 0 ≤ Cp * Q M K A ℓ)
  simp only [sub_add_cancel] at h2
  refine h2.mono_scale zero_le_one (by positivity) ?_
  have hC : 0 ≤ 1 / 100 + 2 * Cp := by positivity
  calc Q M K A ℓ / 100 + 2 * (Cp * Q M K A ℓ) = (1 / 100 + 2 * Cp) * Q M K A ℓ := by ring
    _ ≤ (1 / 100 + 2 * Cp) * (2 * Q M K A s) := mul_le_mul_of_nonneg_left hQℓ hC
    _ = 2 * (1 / 100 + 2 * Cp) * Q M K A s := by ring

/-- **Proposition `prop:profiles`, equation `eq:profiles`**, from its first case, Lemma
`lem:parent`, Lemma `lem:tree`, equations `eq:profiledifference`, `eq:support` and `eq:scales`, as
in its proof for `κN ≤ s ≤ 2N`. The sum rule is used in the form of [AKM, Lemma A.4], via
`Moments.isOs_add`, so the premise `SignedOsSumStatement` of the implication is not used here. -/
theorem profilesStatement (hShort : ProfilesShortStatement m) (hPar : ParentStatement m)
    (hT : TreeStatement m) (hPD : ProfileDifferenceStatement m) (hSupp : SupportStatement m)
    (hS : ScalesStatement m) (_hSum : SignedOsSumStatement.{0, 0}) : ProfilesStatement m := by
  intro bd hbd Cstar b hb
  obtain ⟨C₁, hC₁, hsh⟩ := hShort bd hbd Cstar b hb
  obtain ⟨C₀, hC₀, h⟩ := exists_profile_bounds hT hPD hSupp hS bd hbd Cstar hb
  obtain ⟨Cp, hCp, hparK⟩ := hPar bd hbd Cstar
  obtain ⟨Nth, hNth⟩ := exists_profile_thresholds hS bd hbd Cstar hb (ρ := 1) one_pos
  have hCl : 0 < 2 * (1 / 100 + 2 * Cp) := by positivity
  set Cl := 2 * (1 / 100 + 2 * Cp) with hCldef
  refine ⟨C₁ + C₀ + 2 * Cl, by positivity, fun κ hκ K hK => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hsh K hK
  obtain ⟨N₂, hN₂⟩ := h K hK
  obtain ⟨N₃, hN₃⟩ := hparK (κ / 2) (by positivity) K hK
  set N₄ := ⌈1 / κ ^ 2⌉₊ with hN₄
  refine ⟨max N₁ (max N₂ (max N₃ (max N₄ Nth))), fun M hM hfit N hN A hA hPrem hRange s t I I'
    hpair hcases => ?_⟩
  have hN1' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2' : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN3' : N₃ ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN4' : N₄ ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hNth' : Nth ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  rcases hcases with ⟨hs1, hs2, ht⟩ | ⟨hs1, hs2, ht⟩
  · -- the first case
    obtain ⟨X, hX, hXb⟩ := hN₁ M hM hfit N hN1' A hA hPrem hRange s hs1 hs2 t I I' hpair ht
    obtain ⟨-, hs32, -, -, -⟩ := hNth K hK M hM hfit N hNth' A hA hRange s hs1
    have hQ := one_le_Q hM hK hA (by linarith only [hs32] : (1 : ℝ) ≤ s)
    exact ⟨X, hX.mono_scale zero_le_one (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith only [hC₀, hCl]) (by linarith only [hQ])), hXb⟩
  · -- the second case
    have hNκ : 1 / κ ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN4')
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hsN : Real.sqrt N ≤ s := by
      refine le_trans ?_ hs1
      have h1 : 1 ≤ κ ^ 2 * N := by
        rw [div_le_iff₀ (by positivity)] at hNκ
        linarith only [hNκ]
      have hsq := Real.sq_sqrt hN0
      have hsq0 := Real.sqrt_nonneg (N : ℝ)
      have h2 : 1 ≤ κ * Real.sqrt N := by
        have h3 : 1 ≤ (κ * Real.sqrt N) ^ 2 := by rw [mul_pow, hsq]; exact h1
        have h4 : 0 ≤ κ * Real.sqrt N := by positivity
        nlinarith only [h3, h4]
      calc Real.sqrt N = 1 * Real.sqrt N := (one_mul _).symm
        _ ≤ (κ * Real.sqrt N) * Real.sqrt N := mul_le_mul_of_nonneg_right h2 hsq0
        _ = κ * (Real.sqrt N * Real.sqrt N) := by ring
        _ = κ * N := by rw [Real.mul_self_sqrt hN0]
    obtain ⟨-, hs32, hsm, -, -⟩ := hNth K hK M hM hfit N hNth' A hA hRange s hsN
    obtain ⟨X, hX, hXb⟩ := hN₂ M hM hfit N hN2' A hA hPrem hRange s hsN hs2 t I I' hpair ht Cl hCl
      (lineBound_of_parent hM hK hA hCp.le hfit.t₀_le (hN₃ M hM hfit N hN3' A hA hPrem hRange) hs1
        hs2 hsm ht)
    have hQ := one_le_Q hM hK hA (by linarith only [hs32] : (1 : ℝ) ≤ s)
    exact ⟨X, hX.mono_scale zero_le_one (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith only [hC₁]) (by linarith only [hQ])), hXb⟩

end CurvatureVariance.Paper.Proofs.ShortLengths
