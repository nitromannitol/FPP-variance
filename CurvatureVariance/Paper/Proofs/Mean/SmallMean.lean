/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Arrays
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Mean
public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Infra.FPP.MeanDefs
import CurvatureVariance.Paper.Proofs.Geometry.SupportSubgradient
import CurvatureVariance.Paper.Proofs.Mean.Domain
import CurvatureVariance.Paper.Proofs.Mean.MeanWidth
import CurvatureVariance.Paper.Proofs.Mean.SmallMeanArrays
import CurvatureVariance.Paper.Proofs.Mean.SmallMeanBelow
import CurvatureVariance.Paper.Proofs.Mean.SmallMeanFluct
import CurvatureVariance.Paper.Proofs.Mean.SmallMeanUpper

/-!
# Lemma `lem:smallmean`

`smallMeanStatement_of` follows the paper's proof of Lemma `lem:smallmean`, and its fluctuation
part follows the proof of [AB26, Lemma 7.1] with the changes of the paper:

* the set-up of the proof: `s` slabs of width `s` from `0` to `(s², s y₀)`,
  `t = y₀/s`, a subgradient `ζ_t`, and the contradiction hypothesis;
* equation `eq:meanbelow`: `exists_meanbelow`
  (`CurvatureVariance.Paper.Proofs.Mean.SmallMeanBelow`);
* the entries: `smallMean_row_entry_lower`
  (`CurvatureVariance.Paper.Proofs.Mean.SmallMeanArrays`);
* the fluctuations: `exists_smallMean_rows`
  (`CurvatureVariance.Paper.Proofs.Mean.SmallMeanFluct`);
* the arrays: `exists_smallMean_lower`
  (`CurvatureVariance.Paper.Proofs.Mean.SmallMeanArrays`);
* the upper bound and the contradiction, the last paragraph: `long_slabMin_mean_le_of_good`
  (`CurvatureVariance.Paper.Proofs.Mean.SmallMeanUpper`).

The constants are as in the paper: `h` and `c₁` before `K`, `θ` from `c₁` and the constant of
[AB26, Lemma 2.4], and `c` from `θ`.

The premise `ChainsExistStatement` of the edge is not used: the tuples of `F` are nonempty by the
chain `i(s, y₀)` that the last paragraph of the proof uses (`straight_tuple_admissible`), and it
needs no rounding, since `y₀` is a lattice vector.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

/-- **Lemma `lem:smallmean`**, with its proof, from the premises of the edge `smallMean` of the
graph in `Closing.Main`. The premise `ChainsExistStatement` is not used. -/
theorem smallMeanStatement_of {m : ℕ} (hsupport : SupportStatement m) (hscales : ScalesStatement m)
    (hclassical : ClassicalStatement m) (hmodulus : ModulusStatement m)
    (hparent : ParentStatement m) (hdifference : ProfileDifferenceStatement m)
    (harrays : ArraysStatement.{0} m) (hgood : GoodStatement m) (hslabs : SlabsStatement m)
    (_hchains : ChainsExistStatement m) : SmallMeanStatement m := by
  intro bd hbd Cstar
  obtain ⟨c₁, hc₁, hbelow⟩ := exists_meanbelow hsupport hscales hclassical hmodulus bd hbd Cstar
  obtain ⟨Carr, hCarr, hlower⟩ := exists_smallMean_lower harrays
  -- `θ` small: `θ ≤ c₁/2` and `(c₁ − 2dθ) − Cθ ≥ c₁/2`
  let d : ℝ := (m : ℝ) + 1
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  let θ : ℝ := min 1 (c₁ / (2 * (1 + 2 * d + Carr)))
  have hbig : 0 < 1 + 2 * d + Carr := by positivity
  have hθ : 0 < θ := lt_min zero_lt_one (by positivity)
  have hθ₂ : θ * (1 + 2 * d + Carr) ≤ c₁ / 2 := by
    have hh : θ ≤ c₁ / (2 * (1 + 2 * d + Carr)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at hh
    linarith only [hh]
  have hθc : θ ≤ c₁ / 2 := by
    have h1 : 0 ≤ θ * (2 * d + Carr) := by positivity
    linarith only [hθ₂, h1]
  have hθsum : θ * (2 * d + Carr) ≤ c₁ / 2 := by
    linarith only [hθ₂, hθ]
  obtain ⟨cvar, hcvar, hrows⟩ := exists_smallMean_rows hparent hmodulus hdifference hscales
    bd hbd Cstar hθ
  obtain ⟨supper, hupper⟩ := long_slabMin_mean_le_of_good hclassical hgood hslabs bd hbd
    (c₁ / 4) (by positivity)
  obtain ⟨_B, _hB, hdomination⟩ := exists_long_slabMin_domination bd hbd
  obtain ⟨Nwidth, hwidth⟩ := exists_smallMean_width hscales bd hbd Cstar
  refine ⟨cvar, hcvar, fun K hK => ?_⟩
  obtain ⟨Nbelow, hbelowK⟩ := hbelow K hK
  obtain ⟨Nrows, hrowsK⟩ := hrows K hK
  refine ⟨max Nbelow (max Nrows (max Nwidth (8 * max 2 supper))), ?_⟩
  intro M hM hfit N hN A hA hPrem hRange s hsLower hsUpper hvar y₀ hy₀
  let : IsProbabilityMeasure M.P := hM.probP
  have hNbelow : Nbelow ≤ N := (le_max_left _ _).trans hN
  have hNrows : Nrows ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNwidth : Nwidth ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNS : 8 * max 2 supper ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hsS : max 2 supper ≤ s := by
    have hhNS : (8 : ℝ) * max 2 supper ≤ N := by exact_mod_cast hNS
    have hhSs : ((max 2 supper : ℕ) : ℝ) ≤ s := by linarith only [hhNS, hsLower]
    exact_mod_cast hhSs
  have hs2 : 2 ≤ s := (le_max_left _ _).trans hsS
  have hssupper : supper ≤ s := (le_max_right _ _).trans hsS
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hsN : (s : ℝ) ≤ N := by linarith only [hsUpper, Nat.cast_nonneg (α := ℝ) N]
  have hyDom : y₀ ∈ premiseDomain M s := by
    have he := Real.rpow_le_rpow_of_nonpos hspos hsN
      (show M.δ / 100 - 1 / 4 ≤ 0 by linarith only [hM.delta_le_one])
    have hh := hy₀.trans (mul_le_mul_of_nonneg_left he hspos.le)
    have heq : (s : ℝ) * (s : ℝ) ^ (M.δ / 100 - 1 / 4) =
        (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
      rw [show (3 : ℝ) / 4 + M.δ / 100 = 1 + (M.δ / 100 - 1 / 4) by ring,
        Real.rpow_add hspos, Real.rpow_one]
    exact hh.trans_eq heq
  have hySmall : ‖transversePoint y₀‖ ≤ (bd.T + 1) * s :=
    norm_transverse_le_of_mem_fit hM hfit hs1 hyDom
  -- the set-up: `t = y₀/s`, `ζ_t`, and the contradiction hypothesis
  let t := (s : ℝ)⁻¹ • transversePoint y₀
  have hst : (s : ℝ) • t = transversePoint y₀ := by
    dsimp only [t]
    rw [smul_inv_smul₀ hspos.ne']
  obtain ⟨p, hp⟩ := Proofs.Geometry.exists_isSubgradient M.μ (slopeVec t)
  by_contra hnot
  have hbias := lt_of_not_ge hnot
  have hmean := hbelowK M hM hfit N hNbelow A hA hPrem hRange s hsLower hsUpper y₀ hy₀ hbias p hp
  have hcenter := hrowsK M hM hfit N hNrows A hA hPrem hRange s hsLower hsUpper y₀ hy₀ hvar
  have hwide := hwidth K hK M hM hfit N hNwidth A hA hRange s hsLower
  have hQ : 0 < Q M K A s := mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hspos _)
  obtain ⟨hw, hwQ⟩ := mean_wInt_bounds hM hK hA hs1
  obtain ⟨_H, _hH₁, _hH₂, _hHdom, _hHsq, hF⟩ := hdomination M hM hfit s hs2 y₀ hySmall
  have hnonempty : ∃ Y, IsAdmissibleTuple M s s t 0 (s • ((s : ℤ), y₀)) Y :=
    ⟨_, straight_tuple_admissible M (by omega) y₀⟩
  -- the lower bound and the upper bound on `E[F]`
  have hlo := hlower M hM hs2 hw y₀ t hst p hQ hc₁ hθ hθc hwQ hwide hmean hnonempty hF hcenter
  have hcontact := inner_target_eq_of_isSubgradient (by omega : 0 < s) hst hp
  have hinner : inner ℝ p (point (s • ((s : ℤ), y₀))) = s * M.μ.1 (point ((s : ℤ), y₀)) := by
    rw [point_nsmul, inner_smul_right, hcontact]
  rw [hinner] at hlo
  have hup := hupper M hM hfit s hssupper y₀ hyDom K hK A hA
  change _ ≤ (c₁ / 4) * s * Q M K A s at hup
  have hsQ : 0 < (s : ℝ) * Q M K A s := mul_pos hspos hQ
  have hloss := mul_le_mul_of_nonneg_right hθsum hsQ.le
  have hpos := mul_pos hc₁ hsQ
  dsimp only [d] at hloss
  nlinarith only [hlo, hup, hloss, hpos]

end CurvatureVariance.Paper.Mean
