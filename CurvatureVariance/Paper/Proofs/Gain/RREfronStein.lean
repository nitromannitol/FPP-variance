/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.RRReplacement
public import CurvatureVariance.Paper.Proofs.Gain.RRTuples
import CurvatureVariance.Paper.Proofs.Responses.PositiveResponse
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The second bound of equation `eq:rewardmoment` for an exchangeable replacement

The third paragraph of the proof of [AB26, Lemma 6.1], which the proof of Lemma `lem:blocks`
applies:

* `IsSlabReplacement.lintegral_swap`, `IsSlabReplacement.lintegral_sq_sub_eq`: since `(F, F^G)` is
  exchangeable, `E(F − F^G)² = 2E(F^G − F)₊²`, for every measurable function `F` of the weights.
* `ofReal_posPart_sq_targetMin_new_le` (the first display of that paragraph): after a replacement in
  slab `i`, the old minimizing tuple remains admissible with only its `i`-th term changed, so
  `(F^G − F)₊² ≤ (sup_{I_{i−1}(J_{i−1}) × I_i(J_i)} (D_i^G − D_i)_+)²`. From
  `Responses.ofReal_posPart_sq_targetMin_resample_le`, as `new = resample G old new`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

section Exchange

variable {M : Model m} {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {n K w L : ℕ}
  {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ} {old : Ω → Config m}
  {new : ℕ → (Fin m → ℤ) → Ω → Config m}

/-- **Exchangeability**: `E h(old, new) = E h(new, old)` for the pair of a block. -/
theorem IsSlabReplacement.lintegral_swap (hR : IsSlabReplacement M Pr n K w L t o old new)
    {h : Config m × Config m → ℝ≥0∞} (hh : Measurable h) (i : ℕ) (g : Fin m → ℤ) :
    ∫⁻ ω, h (old ω, new i g ω) ∂Pr = ∫⁻ ω, h (new i g ω, old ω) ∂Pr := by
  rw [← lintegral_map hh (hR.measurable_old.prodMk (hR.measurable_new i g)),
    hR.exchangeable i g, lintegral_map hh ((hR.measurable_new i g).prodMk hR.measurable_old)]

/-- The square of a difference splits into the squares of its two positive parts. -/
theorem ofReal_sq_sub_eq (a b : ℝ) : ENNReal.ofReal ((a - b) ^ 2) =
    ENNReal.ofReal (max (b - a) 0 ^ 2) + ENNReal.ofReal (max (a - b) 0 ^ 2) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

/-- **`E(F − F^G)² = 2E(F^G − F)₊²`** (by exchangeability, in the proof of [AB26, Lemma 6.1]), for
every measurable `F`. -/
theorem IsSlabReplacement.lintegral_sq_sub_eq (hR : IsSlabReplacement M Pr n K w L t o old new)
    {F : Config m → ℝ} (hF : Measurable F) (i : ℕ) (g : Fin m → ℤ) :
    ∫⁻ ω, ENNReal.ofReal ((F (old ω) - F (new i g ω)) ^ 2) ∂Pr =
      2 * ∫⁻ ω, ENNReal.ofReal (max (F (new i g ω) - F (old ω)) 0 ^ 2) ∂Pr := by
  have hpos : Measurable fun p : Config m × Config m =>
      ENNReal.ofReal (max (F p.2 - F p.1) 0 ^ 2) :=
    ((((hF.comp measurable_snd).sub (hF.comp measurable_fst)).max measurable_const).pow_const
      2).ennreal_ofReal
  have hneg : Measurable fun p : Config m × Config m =>
      ENNReal.ofReal (max (F p.1 - F p.2) 0 ^ 2) :=
    ((((hF.comp measurable_fst).sub (hF.comp measurable_snd)).max measurable_const).pow_const
      2).ennreal_ofReal
  have hswap := IsSlabReplacement.lintegral_swap hR hneg i g
  simp only at hswap
  have hm₀ := hpos.comp (hR.measurable_old.prodMk (hR.measurable_new i g))
  have hm : Measurable fun ω => ENNReal.ofReal (max (F (new i g ω) - F (old ω)) 0 ^ 2) := hm₀
  simp_rw [ofReal_sq_sub_eq]
  rw [lintegral_add_left hm, hswap, two_mul]

end Exchange

/-- `(x)_+` as an extended number: `ofReal (max x 0 ^ 2) = ofReal x ^ 2`. -/
theorem ofReal_max_sq_eq (x : ℝ) : ENNReal.ofReal (max x 0 ^ 2) = ENNReal.ofReal x ^ 2 := by
  rw [ENNReal.ofReal_pow (le_max_right _ _)]
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

/-- **The first display of the third paragraph of the proof of [AB26, Lemma 6.1], for a
replacement**: the squared positive response of the minimum `F` to the replacement of a block of
slab `i + 1` is at most the squared block supremum on the two row cubes of an old minimizing tuple.
-/
theorem ofReal_posPart_sq_targetMin_new_le {M : Model m} {K : ℕ} {A : ℝ} {n L ℓ : ℕ}
    {y : Fin m → ℤ} {o : ℕ → Fin m → ℤ} {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {old : Ω → Config m} {new : ℕ → (Fin m → ℤ) → Ω → Config m}
    (hR : IsSlabReplacement M Pr n K (wInt M K A n) L (targetSlope ℓ y) o old new)
    (hn : 2 ≤ n) {ω : Ω} {Y : Fin (K + 1) → Fin m → ℤ}
    (hY : IsMinTuple M (old ω) n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y) (i : Fin K)
    (g : Fin m → ℤ) :
    ENNReal.ofReal (max (targetMin M (new ((i : ℕ) + 1) g ω) n K ℓ y -
        targetMin M (old ω) n K ℓ y) 0 ^ 2) ≤
      blockSup n ((i : ℕ) + 1)
        (rowCube n (wInt M K A n) (targetSlope ℓ y) ((((i : ℕ) + 1 : ℕ) : ℤ) - 1)
          (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc))
        (rowCube n (wInt M K A n) (targetSlope ℓ y) (((i : ℕ) + 1 : ℕ) : ℤ)
          (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ))
        (old ω) (new ((i : ℕ) + 1) g ω) ^ 2 := by
  classical
  set G := block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) (o ((i : ℕ) + 1)) g
  have hres : new ((i : ℕ) + 1) g ω = resample G (old ω) (new ((i : ℕ) + 1) g ω) := by
    funext e
    by_cases he : e.1 ∈ G
    · simp only [resample, he, ite_true]
    · simp only [resample, he, ite_false]
      exact hR.agree _ _ ω e he
  have h := Responses.ofReal_posPart_sq_targetMin_resample_le (w := wInt M K A n) (L := L)
    (o := o ((i : ℕ) + 1)) (g := g) (ω' := new ((i : ℕ) + 1) g ω) hn hY i
  rw [← hres] at h
  refine h.trans (iSup₂_le fun u hu => iSup₂_le fun v hv => ?_)
  have hc1 : ((((i : ℕ) + 1 : ℕ) : ℤ) - 1) = (i : ℤ) := by push_cast; ring
  have hc2 : (((i : ℕ) + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
  unfold blockSup
  rw [hc1, hc2, ofReal_max_sq_eq]
  refine pow_le_pow_left₀ bot_le ?_ 2
  apply le_iSup₂_of_le u hu
  apply le_iSup₂_of_le v hv
  exact le_rfl

end CurvatureVariance.Paper.Gain
