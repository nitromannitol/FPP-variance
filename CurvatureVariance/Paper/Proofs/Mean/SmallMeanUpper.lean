/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Mean.MeanUpper
import CurvatureVariance.Infra.FPP.Lattice
import CurvatureVariance.Infra.FPP.MeanDefs
import CurvatureVariance.Paper.Proofs.Mean.Domain
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The upper bound in the proof of Lemma `lem:smallmean`

The paper (the last paragraph of the proof of Lemma `lem:smallmean`): `E[F] − sμ(s,y₀) ≤ C s log²s`
follows from Lemma `lem:slabs` (2), with `s²` in place of `N`, `n = s` and `S = log(s²)`, and from
equation `eq:classical` at `(s², s y₀)`; off `𝒢_{s²}(log(s²))`, Hölder's inequality and the moments
of `F ≤ ∑ᵢ T^{(i)}((i−1)(s,y₀), i(s,y₀))` bound the contribution by `1`.

`long_slabMin_mean_le_of_good` is the paper's argument, over the contracts `GoodStatement` and
`SlabsStatement`. Its conclusion is `≤ ε s Q_s`, the form in which the last sentence of the paper's
proof uses the bound, "Since `log²s` is much smaller than `Q_s`". The moments of `F` are
`exists_long_slabMin_domination`, the chain `i(s,y₀)` of the paper.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

/-- **The upper bound** (the last paragraph of the proof of Lemma `lem:smallmean`): at the long
target, `E[F] − sμ(s,y₀) = o(s Q_s)`. It uses no induction premise. The onset is uniform over the
fitting models and over `K` and `A`: the moment constants use the common law and `bd.T`, and the
decay thresholds use `bd.law.δ`. The slope `|t − t₀| ≤ s^{δ/100−1/4}` is at most
`(s²)^{−1/9} ≤ 3 (s²)^{−1/9}`, the range of Lemma `lem:slabs` at `N = s²`. -/
theorem long_slabMin_mean_le_of_good {m : ℕ} (hclassical : ClassicalStatement m)
    (hgood : GoodStatement m) (hslabs : SlabsStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd → ∀ s : ℕ, s₀ ≤ s → ∀ y₀ ∈ premiseDomain M s,
      ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ A : ℝ, 1 ≤ A →
        (∫ ω, (slabMin M ω s s ((s : ℝ)⁻¹ • transversePoint y₀) 0
          (s • ((s : ℤ), y₀))).toReal ∂M.P) -
            s * M.μ.1 (point ((s : ℤ), y₀)) ≤ ε * s * Q M K A s := by
  obtain ⟨cg, Cg, hcg, hCg, Ngood, hgood⟩ := hgood bd hbd
  obtain ⟨C, hC, Nslab, hslabs⟩ := hslabs bd hbd Cg cg hCg hcg
  obtain ⟨B, hB, hdomination⟩ := exists_long_slabMin_domination bd hbd
  obtain ⟨smean, _, hmean⟩ := classical_long_mean_le_mul_Q hclassical bd hbd (ε / 3) (by positivity)
  obtain ⟨slog, _, hlog⟩ := log_sq_le_mul_Q bd hbd (4 * C) (ε / 3) (by positivity)
  have hlogratio := (isLittleO_log_rpow_atTop
    (show 0 < bd.law.δ / 1000 by
      exact div_pos hbd.law.delta_pos (by norm_num))).tendsto_div_nhds_zero
  obtain ⟨Rlog, hRlog⟩ := eventually_atTop.1 (hlogratio.eventually (eventually_lt_nhds zero_lt_one))
  have hrec : Tendsto (fun s : ℝ => B / (2 * s ^ 2)) atTop (𝓝 0) := by
    simpa only [div_div] using (tendsto_const_nhds (x := B / 2)).div_atTop
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have herr : Tendsto (fun s : ℝ => B / (2 * s ^ 2) +
      s ^ 6 * Real.exp (-((Real.log s / Cg) ^ 2))) atTop (𝓝 0) := by
    simpa only [zero_add] using hrec.add (tendsto_pow_six_mul_exp_neg_log_sq hCg)
  obtain ⟨serr, hserr⟩ := eventually_atTop.1 (herr.eventually (eventually_lt_nhds zero_lt_one))
  have hprop : ∀ᶠ s : ℕ in atTop, ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ y₀ ∈ premiseDomain M s, ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ A : ℝ, 1 ≤ A →
        (∫ ω, (slabMin M ω s s ((s : ℝ)⁻¹ • transversePoint y₀) 0
          (s • ((s : ℤ), y₀))).toReal ∂M.P) -
            s * M.μ.1 (point ((s : ℤ), y₀)) ≤ ε * s * Q M K A s := by
    filter_upwards [eventually_ge_atTop (max (max Ngood Nslab) 2),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop smean,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop slog,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop Rlog,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop serr,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (3 / ε)]
      with s hs hsmean hslog hsRlog hserr' hsε
    intro M hM hfit y₀ hy₀ K hK A hA
    have : IsProbabilityMeasure M.P := hM.probP
    simp only [← hfit.δ_eq] at hRlog
    have hs2 : 2 ≤ s := (le_max_right _ _).trans hs
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
    have hspos : (0 : ℝ) < s := zero_lt_one.trans_le hs1
    have hsG : Ngood ≤ s * s :=
      (((le_max_left _ _).trans (le_max_left _ _)).trans hs).trans (Nat.le_mul_self s)
    have hsS : Nslab ≤ s * s :=
      (((le_max_right _ _).trans (le_max_left _ _)).trans hs).trans (Nat.le_mul_self s)
    have hss : (s : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith only [hs1, sq_nonneg ((s : ℝ) - 1)]
    have hSsmall : Real.log ((s * s : ℕ) : ℝ) ≤ ((s * s : ℕ) : ℝ) ^ (M.δ / 1000) := by
      have hR : Rlog ≤ ((s * s : ℕ) : ℝ) := by
        have hh := hsRlog.trans hss
        simpa only [Nat.cast_mul, pow_two] using hh
      simpa only [one_mul] using
        (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (s * s : ℕ)) _)).1
          (hRlog _ hR).le
    have hyshort : ‖transversePoint y₀‖ ≤ (bd.T + 1) * s :=
      norm_transverse_le_of_mem_fit hM hfit hs1 hy₀
    obtain ⟨H, hHI, hH2I, hdom, hH2, hFI⟩ := hdomination M hM hfit s hs2 y₀ hyshort
    obtain ⟨G, _, hbad, hG⟩ := hgood M hM hfit (s * s) hsG
    let S : ℝ := Real.log ((s * s : ℕ) : ℝ)
    let t := (s : ℝ)⁻¹ • transversePoint y₀
    let x : Vertex m := s • ((s : ℤ), y₀)
    let F : Config m → ℝ := fun ω => (slabMin M ω s s t 0 x).toReal
    let T : Config m → ℝ := fun ω => passageTimeReal ω 0 x
    have hS : S = 2 * Real.log s := by
      dsimp [S]
      rw [Nat.cast_mul, Real.log_mul hspos.ne' hspos.ne']
      ring
    have hlogpos : 0 < Real.log (s : ℝ) := Real.log_pos (by exact_mod_cast hs2)
    have hSpos : 0 < S := by rw [hS]; positivity
    have hx0 : x ≠ 0 := by
      intro hx
      have hh := congrArg Prod.fst hx
      have hsNat : 0 < s := by omega
      simp [x, nsmul_eq_mul, Nat.ne_of_gt hsNat] at hh
    obtain ⟨_Ccl, _, hcl⟩ := hclassical bd hbd
    obtain ⟨hTI, _, _, _⟩ := hcl M hM hfit x hx0
    have htslope₁ : ‖t - M.t₀‖ ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
      have he : t - M.t₀ = (s : ℝ)⁻¹ •
          (transversePoint y₀ - (s : ℝ) • M.t₀) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
      rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hspos.le)]
      calc (s : ℝ)⁻¹ * ‖transversePoint y₀ - (s : ℝ) • M.t₀‖ ≤
          (s : ℝ)⁻¹ * (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
            mul_le_mul_of_nonneg_left hy₀ (inv_nonneg.mpr hspos.le)
        _ = (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
            rw [show (3 : ℝ) / 4 + M.δ / 100 = (M.δ / 100 - 1 / 4) + 1 by ring,
              Real.rpow_add hspos, Real.rpow_one]
            field_simp
    have htslope : ‖t - M.t₀‖ ≤ 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := htslope₁.trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hspos.le _) (by norm_num))
    have hsmallslope : ‖t - M.t₀‖ ≤ 3 * ((s * s : ℕ) : ℝ) ^ (-(1 : ℝ) / 9) := by
      have hpow : ((s * s : ℕ) : ℝ) ^ (-(1 : ℝ) / 9) = (s : ℝ) ^ (-(2 : ℝ) / 9) := by
        rw [Nat.cast_mul, Real.mul_rpow hspos.le hspos.le, ← Real.rpow_add hspos]
        congr 1
        ring
      rw [hpow]
      have h1 : (s : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ (s : ℝ) ^ (-(2 : ℝ) / 9) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (by linarith only [hM.delta_le_one])
      have h2 := Real.rpow_nonneg hspos.le (-(2 : ℝ) / 9)
      linarith only [htslope₁, h1, h2]
    have hbox0 : InBox (3 * (1 + ‖M.t₀‖) * ((s * s : ℕ) : ℝ)) (0 : Vertex m) := by
      constructor
      · simp only [Prod.fst_zero, Int.cast_zero, abs_zero]
        positivity
      · intro j
        simp only [Prod.snd_zero, Pi.zero_apply, Int.cast_zero, abs_zero]
        positivity
    have hboxx : InBox (3 * (1 + ‖M.t₀‖) * ((s * s : ℕ) : ℝ)) x := by
      constructor
      · simp only [x, nsmul_eq_mul, Prod.fst_mul, Prod.fst_natCast, Int.cast_mul,
          Int.cast_natCast, Nat.cast_mul]
        rw [abs_of_nonneg (mul_nonneg hspos.le hspos.le)]
        nlinarith only [sq_nonneg (s : ℝ), norm_nonneg M.t₀]
      · intro j
        have hh := (PiLp.norm_apply_le (transversePoint y₀) j).trans
          (norm_transverse_le_of_mem hM hs1 hy₀)
        change ‖(y₀ j : ℝ)‖ ≤ (‖M.t₀‖ + 1) * s at hh
        rw [Real.norm_eq_abs] at hh
        have hmul := mul_le_mul_of_nonneg_left hh hspos.le
        simp only [x, nsmul_eq_mul, Prod.snd_mul, Prod.snd_natCast, Pi.mul_apply,
          Pi.natCast_apply, Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_nonneg hspos.le,
          Nat.cast_mul]
        nlinarith only [hmul, sq_nonneg (s : ℝ), norm_nonneg M.t₀]
    have hdisp : point x - point (0 : Vertex m) = ((s * s : ℕ) : ℝ) • slopeVec t := by
      rw [Infra.FPP.point_zero, sub_zero]
      change point (s • ((s : ℤ), y₀)) = _
      rw [point_nsmul]
      apply pt_ext
      · simp [point_fst, slopeVec]
      · ext j
        simp [point_snd, slopeVec, t, PiLp.smul_apply]
        field_simp
    have hgood : ∀ ω ∈ G S, F ω ≤ T ω + C * s * S ^ 2 := by
      intro ω hω
      have hgeom := hslabs M hM hfit (s * s) hsS S le_rfl ω (hG S le_rfl ω hω) (s * s) t 0 x
        hdisp (Nat.mul_pos (by omega) (by omega))
        (by exact_mod_cast (show s * s ≤ 3 * (s * s) by omega)) hsmallslope
      have hupper := (hgeom.2 s s rfl (by omega) (by
          have heq : ((s * s : ℕ) : ℝ) = (s : ℝ) ^ 2 := by push_cast; ring
          rw [heq, Real.sqrt_sq hspos.le]) htslope hSsmall hbox0 hboxx).2.2
      have hh := ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩) hupper
      change (slabMin M ω s s t 0 x).toReal ≤ (passageTime ω 0 x : ℝ) + C * s * S ^ 2
      simpa only [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.ofReal_ne_top,
        ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity : 0 ≤ C * s * S ^ 2)] using hh
    have hupper := integral_le_of_good_event (b := C * s * S ^ 2) (C := Cg) (S := S)
      (R := (s : ℝ) ^ 6) (by positivity) hCg hSpos (by positivity)
      hFI hTI hH2I (fun _ => NNReal.coe_nonneg _) hdom hgood (hbad S le_rfl)
    have hpoly : (∫ ω, H ω ^ 2 ∂M.P) / (2 * (s : ℝ) ^ 6) ≤ B / (2 * (s : ℝ) ^ 2) := by
      calc (∫ ω, H ω ^ 2 ∂M.P) / (2 * (s : ℝ) ^ 6) ≤ B * (s : ℝ) ^ 4 / (2 * (s : ℝ) ^ 6) :=
            div_le_div_of_nonneg_right hH2 (by positivity)
        _ = B / (2 * (s : ℝ) ^ 2) := by field_simp
    have hexptail : Real.exp (-((S / Cg) ^ 2)) ≤ Real.exp (-((Real.log s / Cg) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      rw [hS]
      have heq : 2 * Real.log (s : ℝ) / Cg = 2 * (Real.log s / Cg) := by ring
      rw [heq]
      nlinarith only [sq_nonneg (Real.log (s : ℝ) / Cg)]
    have herrbound : (∫ ω, F ω ∂M.P) - (∫ ω, T ω ∂M.P) ≤ C * s * S ^ 2 + 1 := by
      have hh := mul_le_mul_of_nonneg_left hexptail (by positivity : 0 ≤ (s : ℝ) ^ 6)
      have hh' := hserr _ hserr'
      linarith only [hupper, hpoly, hh, hh']
    have hmeanbound := hmean M hM hfit s hsmean y₀ hyshort K hK A hA
    have hlogbound := hlog M hM hfit s hslog K hK A hA
    have hb : C * s * S ^ 2 ≤ ε / 3 * s * Q M K A s := by
      rw [hS]
      have hh := mul_le_mul_of_nonneg_left hlogbound hspos.le
      nlinarith only [hh]
    have hQ1 : 1 ≤ Q M K A s := by
      have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
      have hK4 : (4 : ℝ) ≤ K := by exact_mod_cast (show 4 ≤ K by omega)
      have hq : 0 ≤ (1 : ℝ) / 2 - M.δ / K := by
        have hh : M.δ / K ≤ (1 : ℝ) / 4 :=
          (div_le_iff₀ hKpos).2 (by linarith only [hM.delta_le_one, hK4])
        linarith only [hh]
      have hh := Real.one_le_rpow hs1 hq
      change 1 ≤ A * (s : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K)
      exact (by simpa only [one_mul] using mul_le_mul hA hh zero_le_one (by linarith only [hA]))
    have hone : 1 ≤ ε / 3 * s * Q M K A s := by
      have hh : 1 ≤ ε / 3 * s := by
        have hmult := mul_le_mul_of_nonneg_left hsε hε.le
        have heq : ε * (3 / ε) = 3 := by field_simp
        linarith only [hmult, heq]
      have hmult := mul_le_mul_of_nonneg_left hQ1 (by positivity : 0 ≤ ε / 3 * s)
      linarith only [hh, hmult]
    change (∫ ω, F ω ∂M.P) - s * M.μ.1 (point ((s : ℤ), y₀)) ≤ ε * s * Q M K A s
    change (∫ ω, T ω ∂M.P) - s * M.μ.1 (point ((s : ℤ), y₀)) ≤ ε / 3 * s * Q M K A s at hmeanbound
    nlinarith only [herrbound, hmeanbound, hb, hone]
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hprop
  exact ⟨s₀, fun M hM hfit s hs => hs₀ s hs M hM hfit⟩

end CurvatureVariance.Paper.Mean
