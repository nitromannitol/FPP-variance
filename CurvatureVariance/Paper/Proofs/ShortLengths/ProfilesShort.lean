/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Inputs
public import CurvatureVariance.Paper.Proofs.ShortLengths.ProfilesBounds
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.Moments.Links
import CurvatureVariance.Paper.Proofs.Moments.Scales
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proposition `prop:profiles` for `s ≤ N/2`: the statement `ProfilesShortStatement`

The proof of Proposition `prop:profiles` for `s ≤ N/2`: the proof of [AB26, Proposition 4.2]
with the changes of the paper. As in the continuum library
(`IsotropicVariance.Paper.Proofs.Profiles.profilesShortStatement_of`):

* `exists_profile_thresholds`: what "for `N` large" means, from equation `eq:scales`;
* `exists_profile_bounds`: `profile_bounds_of` with Lemma `lem:tree` at `s/16`, equation
  `eq:profiledifference`, equation `eq:support` and these thresholds, for every bound on the line.
  Both cases of the proposition come from this one theorem;
* `lineBound_of_premise`: equation `eq:premise` on the line: "The vectors between these points have
  lengths `9s/8` and `7s/8` along `e₁` and slopes within `(4/5)s^{δ/100−1/4} + C/s <
  (9s/8)^{δ/100−1/4}` of `t₀`, so equation `eq:premise` applies to them". The link is
  `exists_premise_link`, with the margin `λ|t − t₀| ≤ (24/25) λ^{3/4+δ/100}` of `link_slope_le`,
  which holds for `λ ≤ 2s`, and the paper's `(4/5) < (9/8)^{δ/100−1/4}` is the same step at
  `λ = 9s/8`.
* `profilesShortStatement`: the contract. It uses neither `ExpArrayStatement` nor
  `ParentStatement`, which is what breaks the cycle Proposition `prop:profiles` → Lemma
  `lem:rowenergy` → Lemma `lem:parent` → Proposition `prop:profiles`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- "For `N` large", for Proposition `prop:profiles`, from equation `eq:scales`: for `s ≥ √N`,
`s` is large, the width margin holds, and a slope within `(3/2)s^{δ/100−1/4}` of `t₀` is within
`ρ/2` of it with `s|t − t₀|^{2+δ} ≤ Q_s`. -/
theorem exists_profile_thresholds (hS : ScalesStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) {b ρ : ℝ} (hb : 1 ≤ b) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → RangeA M K A N Cstar → ∀ s : ℕ, Real.sqrt N ≤ s →
        1 ≤ N ∧ (32 : ℝ) ≤ s ∧ 2 * 10 ^ 4 * ((1 + bd.T) ^ 2 * ((m : ℝ) + 1)) ≤ s ∧
        4 * (2 + bd.T) * ((b + 4) * Real.sqrt ((m : ℝ) + 1)) * W M K A s ≤ ρ * s ∧
        ∀ t : E, ‖t - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
          ‖t - M.t₀‖ ≤ ρ / 2 ∧ (s : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Q M K A s := by
  have hT0 : 0 ≤ bd.T := hbd.T_nonneg
  have hsq1 : 1 ≤ Real.sqrt ((m : ℝ) + 1) :=
    Real.one_le_sqrt.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) m])
  have hb0 : 0 < b := by linarith only [hb]
  have hB0 : 0 < 4 * (2 + bd.T) * ((b + 4) * Real.sqrt ((m : ℝ) + 1)) := by positivity
  obtain ⟨Nw, hNw⟩ := Moments.exists_width_margin hS bd hbd Cstar
    (div_pos hρ hB0)
  obtain ⟨r₂, hr₂, hcost⟩ := Moments.exists_slope_cost hS bd hbd Cstar
  obtain ⟨S₀, hS₀1, hS₀m, hS₀t⟩ := exists_large_scale (ρ := 2 * ρ / 3) (by positivity) m bd.T
  set S₁ := max S₀ r₂ with hS₁
  refine ⟨max Nw (max 2 ⌈S₁ ^ 2⌉₊), fun K hK M hM hfit N hN A hA hR s hsN => ?_⟩
  have hδ1 := hM.delta_le_one
  have hNw' : Nw ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNS : ⌈S₁ ^ 2⌉₊ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hS₁1 : 1 ≤ S₁ := hr₂.trans (le_max_right _ _)
  have hSs : S₁ ≤ (s : ℝ) := by
    have h1 : S₁ ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNS)
    exact (Real.le_sqrt_of_sq_le h1).trans hsN
  have hsS₀ : S₀ ≤ (s : ℝ) := (le_max_left _ _).trans hSs
  have hsr₂ : r₂ ≤ (s : ℝ) := (le_max_right _ _).trans hSs
  have hs32 : (32 : ℝ) ≤ s := hS₀1.trans hsS₀
  have hs1 : (1 : ℝ) ≤ s := by linarith only [hs32]
  have hs0 : (0 : ℝ) < s := by linarith only [hs1]
  have hse0 : 0 ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := Real.rpow_nonneg hs0.le _
  have hsqN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  refine ⟨by omega, hs32, hS₀m.trans hsS₀, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · -- the width margin
    have hW := hNw K hK M hM hfit N hNw' A hA hR s (by linarith only [hsN, hsqN])
    have h1 := rpow_le_self_of_one_le hs1 hδ1
    have h2 : W M K A s ≤ ρ / (4 * (2 + bd.T) * ((b + 4) * Real.sqrt ((m : ℝ) + 1))) * s :=
      hW.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    calc 4 * (2 + bd.T) * ((b + 4) * Real.sqrt ((m : ℝ) + 1)) * W M K A s
        ≤ 4 * (2 + bd.T) * ((b + 4) * Real.sqrt ((m : ℝ) + 1)) *
            (ρ / (4 * (2 + bd.T) * ((b + 4) * Real.sqrt ((m : ℝ) + 1))) * s) :=
          mul_le_mul_of_nonneg_left h2 hB0.le
      _ = ρ * s := by field_simp
  · have h1 : (s : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 2 * ρ / 3 / 2 :=
      (Real.rpow_le_rpow_of_exponent_le hs1 (by linarith only [hδ1])).trans (hS₀t s hsS₀)
    linarith only [ht, h1]
  · exact hcost K hK M hM hfit N hN2 A hA hR s (by linarith only [hsN, hsqN]) hsr₂ t
      (by linarith only [ht, hse0])

/-- **Proposition `prop:profiles` for every bound on the line**: from Lemma `lem:tree`, equations
`eq:profiledifference`, `eq:support` and `eq:scales`, for `√N ≤ s ≤ 2N` and slopes within
`(3/2) s^{δ/100−1/4}` of `t₀`, a bound `LineBound` at the scale `Cl` gives `ShortConclusion`. -/
theorem exists_profile_bounds (hT : TreeStatement m) (hPD : ProfileDifferenceStatement m)
    (hSupp : SupportStatement m) (hS : ScalesStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → RangeA M K A N Cstar →
      ∀ s : ℕ, Real.sqrt N ≤ s → (s : ℝ) ≤ 2 * N → ∀ (t : E) (I I' : Set (Vertex m)),
      IsCubePair M K A s b t I I' → ‖t - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
      ∀ Cl : ℝ, 0 < Cl → LineBound M K A s t Cl → ShortConclusion M K A s (C₀ + 2 * Cl) t I I' := by
  obtain ⟨cS, CS, r₁, -, hCS, hr₁, -, hsupp⟩ := hSupp bd hbd
  have hb8 : 1 ≤ 8 * b := by linarith only [hb]
  obtain ⟨Ct, hCt, hTK⟩ := hT bd hbd Cstar (8 * b) hb8
  obtain ⟨Cpd, hCpd, hPDb⟩ := hPD bd hbd Cstar
  set T := bd.T with hTdef
  have hT0 : 0 ≤ T := hbd.T_nonneg
  have hsq1 : 1 ≤ Real.sqrt ((m : ℝ) + 1) :=
    Real.one_le_sqrt.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) m])
  have hρ0 : 0 < min r₁ 1 := lt_min hr₁ one_pos
  obtain ⟨Nth, hNth⟩ := exists_profile_thresholds hS bd hbd Cstar hb hρ0
  refine ⟨2 * Ct + Cpd + 2 * (2 * (2 + T) ^ 2 * CS * ((b + 4) * Real.sqrt ((m : ℝ) + 1)) ^ 2 +
    2 * CS + 100 * Cpd), by positivity, fun K hK => ?_⟩
  obtain ⟨Nt, hNt⟩ := hTK K hK
  obtain ⟨Npd, hNpd⟩ := hPDb b hb K hK
  refine ⟨max Nt (max Npd Nth), fun M hM hfit N hN A hA hPrem hRange s hsN hs2 t I I' hpair ht Cl
    hCl hline => ?_⟩
  have hNt' : Nt ≤ N := (le_max_left _ _).trans hN
  have hNpd' : Npd ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNth' : Nth ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hN1, hs32, -, hBW, hslope⟩ := hNth K hK M hM hfit N hNth' A hA hRange s hsN
  obtain ⟨htρ, hsQ⟩ := hslope t ht
  have hδ1 := hM.delta_le_one
  have hTM : ‖M.t₀‖ ≤ T := hfit.t₀_le
  have hs0 : (0 : ℝ) < s := by linarith only [hs32]
  obtain ⟨h24, -⟩ := hsupp M hM hfit
  obtain ⟨p, c, c', a₀, a₀', rfl, rfl, ha0, ha0b, ha0', ha0'b, hcc⟩ := id hpair
  obtain ⟨Xpd, hXpd, hpd⟩ := hNpd M hM hfit N hNpd' A hA hRange s hsN hs2 t _ _ hpair ht
  have ht16 : ‖t - M.t₀‖ ≤ 4 / 5 * ((s : ℝ) / 16) ^ (M.δ / 100 - 1 / 4) :=
    ht.trans (slope_le_sixteen hδ1 hs0)
  have hsN16 : Real.sqrt N / 16 ≤ (s : ℝ) / 16 := by linarith only [hsN]
  have hNpos : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hX := profile_bounds_of hM hK hA hN1 hb hTM hCS h24 (min_le_left _ _) (min_le_right _ _)
    hCt hCl hCpd hsN hs32 htρ hsQ ha0 ha0b ha0' ha0'b hcc hBW
    (fun q z a₁ ha₁ ha₁b P hP a a' ha ha' => hNt M hM hfit N hNt' A hA hPrem hRange ((s : ℝ) / 16)
      hsN16 (by linarith only [hs2, hNpos]) q z t a₁ ha₁ ha₁b ht16 P hP a a' ha ha')
    hline hXpd hpd
  rw [show 2 * Ct + Cpd + 2 * (2 * (2 + T) ^ 2 * CS * ((b + 4) * Real.sqrt ((m : ℝ) + 1)) ^ 2 +
      2 * CS + 100 * Cpd) + 2 * Cl = 2 * Ct + 2 * Cl + Cpd + 2 * (2 * (2 + T) ^ 2 * CS * ((b + 4) *
      Real.sqrt ((m : ℝ) + 1)) ^ 2 + 2 * CS + 100 * Cpd) by ring]
  exact hX

/-- The regime of the two vectors between the points, at the lengths `7s/8` and `9s/8` along `e₁`:
a rounding error is small against `s`, and the length is large against `(1 + |t₀|)²d`. -/
theorem link_regime {M : Model m} {T : ℝ} (hTM : ‖M.t₀‖ ≤ T) {s : ℕ}
    (hsm : 2 * 10 ^ 4 * ((1 + T) ^ 2 * ((m : ℝ) + 1)) ≤ s) {lam : ℝ}
    (hlam : lam = 7 / 8 * s ∨ lam = 9 / 8 * s) :
    1 ≤ Real.sqrt ((m : ℝ) + 1) ∧ Real.sqrt ((m : ℝ) + 1) ≤ s / (2 * 10 ^ 4) ∧ (1 : ℝ) ≤ s ∧
      7 / 8 * (s : ℝ) ≤ lam ∧ lam ≤ 9 / 8 * (s : ℝ) ∧
      10 ^ 4 * ((1 + ‖M.t₀‖) ^ 2 * ((m : ℝ) + 1)) ≤ lam := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hT0 : 0 ≤ ‖M.t₀‖ := norm_nonneg _
  have hsq1 : 1 ≤ Real.sqrt ((m : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith only [hm0])
  have hsql : Real.sqrt ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    calc Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (((m : ℝ) + 1) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith only [hm0])
      _ = (m : ℝ) + 1 := Real.sqrt_sq (by linarith only [hm0])
  have hTsq : (1 + ‖M.t₀‖) ^ 2 ≤ (1 + T) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [hT0]) (by linarith only [hTM]) 2
  have hd0 : (m : ℝ) + 1 ≤ (1 + ‖M.t₀‖) ^ 2 * ((m : ℝ) + 1) :=
    le_mul_of_one_le_left (by linarith only [hm0]) (by nlinarith only [hT0])
  have hsmT : 2 * 10 ^ 4 * ((1 + ‖M.t₀‖) ^ 2 * ((m : ℝ) + 1)) ≤ s := by
    have := mul_le_mul_of_nonneg_right hTsq (by linarith only [hm0] : (0 : ℝ) ≤ (m : ℝ) + 1)
    linarith only [this, hsm]
  have hsqs : Real.sqrt ((m : ℝ) + 1) ≤ s / (2 * 10 ^ 4) := by
    rw [le_div_iff₀ (by norm_num)]; linarith only [hsmT, hd0, hsql]
  have hs1 : (1 : ℝ) ≤ s := by linarith only [hsqs, hsq1]
  have hs0 : (0 : ℝ) ≤ s := by linarith only [hs1]
  have hlam1 : 7 / 8 * (s : ℝ) ≤ lam := by
    rcases hlam with rfl | rfl <;> linarith only [hs0]
  have hlam2 : lam ≤ 9 / 8 * (s : ℝ) := by
    rcases hlam with rfl | rfl <;> linarith only [hs0]
  exact ⟨hsq1, hsqs, hs1, hlam1, hlam2, by linarith only [hsmT, hlam1, hs0]⟩

/-- **Equation `eq:premise` on the line** (the proof of Proposition `prop:profiles` for
`s ≤ N/2`). -/
theorem lineBound_of_premise {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {N : ℕ} (hPrem : Premise M K A N) {T : ℝ} (hTM : ‖M.t₀‖ ≤ T) {s : ℕ}
    (hsN2 : (s : ℝ) ≤ N / 2) (hsm : 2 * 10 ^ 4 * ((1 + T) ^ 2 * ((m : ℝ) + 1)) ≤ s) {t : E}
    (ht : ‖t - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4)) : LineBound M K A s t 2 := by
  intro x x' lam w hlam hw hd
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  obtain ⟨hsq1, hsqs, hs1, hlam1, hlam2, hlamlo⟩ := link_regime hTM hsm hlam
  have hT0 : 0 ≤ ‖M.t₀‖ := norm_nonneg _
  have hs0 : (0 : ℝ) ≤ s := by linarith only [hs1]
  have hlamlo' : (1 : ℝ) ≤ lam := by
    have hd : (1 : ℝ) ≤ (1 + ‖M.t₀‖) ^ 2 * ((m : ℝ) + 1) := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have h1 : (1 : ℝ) ≤ (1 + ‖M.t₀‖) ^ 2 := by nlinarith only [hT0]
      nlinarith only [h1, hm0]
    linarith only [hd, hlamlo]
  have hω : ‖w‖ + (2 + ‖M.t₀‖) * Real.sqrt ((m : ℝ) + 1) ≤
      (4 + ‖M.t₀‖) * Real.sqrt ((m : ℝ) + 1) := by linarith only [hw]
  have hsq2 : Real.sqrt ((m : ℝ) + 1) + 1 ≤ lam := by linarith only [hsqs, hsq1, hlam1, hs1]
  obtain ⟨s₁, -, hs₁, hL⟩ := Moments.exists_premise_link hM hPrem hsq1 hd hsq2
    (by linarith only [hsN2, hlam2, hsqs])
    (link_slope_le hδ.le hδ1 (by linarith only [hlamlo']) (by linarith only [hlam2, hs0]) ht)
    (link_margin_le hδ.le hT0 hlamlo hω)
  have hs₁' := abs_le.mp hs₁
  have hA0 : (0 : ℝ) ≤ A := by linarith only [hA]
  have hs₁1 : (1 : ℝ) ≤ s₁ := by linarith only [hs₁'.1, hsq2]
  exact hL.2.mono_scale zero_le_one (by linarith only [one_le_Q hM hK hA hs₁1])
    (Q_le_two_mul hM hK hA0 (by linarith only [hs₁1]) hs0
      (by linarith only [hs₁'.2, hlam2, hsqs, hs0]))

/-- **Proposition `prop:profiles` for `s ≤ N/2`** (its first case), from Lemma `lem:tree`, equations
`eq:profiledifference`, `eq:support` and `eq:scales`. The sum rule is used in the form of
[AKM, Lemma A.4], via `Moments.isOs_add`, so the premise `SignedOsSumStatement` of the implication
is not used here. -/
theorem profilesShortStatement (hT : TreeStatement m) (hPD : ProfileDifferenceStatement m)
    (hSupp : SupportStatement m) (hS : ScalesStatement m)
    (_hSum : SignedOsSumStatement.{0, 0}) : ProfilesShortStatement m := by
  intro bd hbd Cstar b hb
  obtain ⟨C₀, hC₀, h⟩ := exists_profile_bounds hT hPD hSupp hS bd hbd Cstar hb
  obtain ⟨Nth, hNth⟩ := exists_profile_thresholds hS bd hbd Cstar hb (ρ := 1) one_pos
  refine ⟨C₀ + 2 * 2, by positivity, fun K hK => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h K hK
  refine ⟨max N₀ Nth, fun M hM hfit N hN A hA hPrem hRange s hsN hsN2 t I I' hpair ht => ?_⟩
  have hNth' : Nth ≤ N := (le_max_right _ _).trans hN
  obtain ⟨-, hs32, hsm, -, -⟩ := hNth K hK M hM hfit N hNth' A hA hRange s hsN
  have hs0 : (0 : ℝ) < s := by linarith only [hs32]
  have hse0 : 0 ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := Real.rpow_nonneg hs0.le _
  have hNpos : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact hN₀ M hM hfit N ((le_max_left _ _).trans hN) A hA hPrem hRange s hsN
    (by linarith only [hsN2, hNpos]) t I I' hpair (by linarith only [ht, hse0]) 2 two_pos
    (lineBound_of_premise hM hK hA hPrem hfit.t₀_le hsN2 hsm ht)

end CurvatureVariance.Paper.Proofs.ShortLengths
