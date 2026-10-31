/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Classical.BoundedGridRepresentation
public import IsotropicVariance.Paper.Proofs.Classical.BoundedProductConcentration
public import IsotropicVariance.Paper.Proofs.Classical.CodeDifference
public import IsotropicVariance.Paper.Proofs.Classical.CodeProxy

/-! # Uniform concentration of the actual passage time

The first bound of Lemma `lem:classical`, by [BLM03, Corollary 3] and [BLM03, Theorem 7] as in
its proof, uniformly over the endpoints. The passage time is a function of independent
codes of the noise in disjoint unit cubes, and the proof uses the two facts of the paper:
* `ae_code_difference_le`: resampling one cube changes the passage time by at most a constant `r`;
* `ae_neg_code_proxy_le`: the squared increases sum over the cubes to at most
  `C (dist u v + 1)`.

It also uses `0 ≤ T ≤ b (dist u v)`, for `b` an upper bound of the density. The paper leaves this
step implicit: the lower tail of [BLM03, Theorem 7] holds only up to a threshold, and the bounded
range makes the tail trivial above it.

All finite regional representations and physical replacement estimates are
constructed internally from the setting. Constants depend only on its fixed
ellipticity bounds and the dimension.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.Classical
open IsotropicVariance.Infra IsotropicVariance.Infra.WhiteNoise

/-- The concentration half, uniformly over all pairs of endpoints. -/
theorem exists_passage_concentration_constant {m : ℕ} (X : Setting m)
    {a b : ℝ} (ha : 0 < a) (hBounds : ∀ ω x, a ≤ X.ρ ω x ∧ X.ρ ω x ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Pt m,
      Cited.IsOs X.P 2 (C * sqrt (dist u v + 1))
        (fun ω => |X.passTime ω u v - ∫ η, X.passTime η u v ∂X.P|) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure X.P
  have hb : 0 < b := ha.trans_le ((hBounds ω₀ 0).1.trans (hBounds ω₀ 0).2)
  let d := Module.finrank ℝ (Pt m)
  let M : ℝ := (9 ^ d : ℕ)
  let r := (b / a) * (b * (5 * (d : ℝ)) + 1)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hM : 0 ≤ M := Nat.cast_nonneg _
  let K := 2 * M * (b / a + 1) + b / r + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have he : 1 ≤ exp 1 - 1 := by linarith only [add_one_le_exp (1 : ℝ)]
  have hePos : 0 < exp 1 - 1 := zero_lt_one.trans_le he
  let C := r * (2 * ((2 : ℝ) ^ (1 / 2 : ℝ) * (4 * sqrt ((exp 1 - 1) * K))))
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u v
  let s := dist u v
  have hs : 0 ≤ s := dist_nonneg
  have hs1 : 0 < s + 1 := by positivity
  let c := K * (s + 1)
  have hc : 0 < c := mul_pos hK hs1
  obtain ⟨n, _hn, z, hz, Φ, hΦ, f, hf, hfb, hRep, hLaw⟩ :=
    exists_bounded_grid_passTime_representation X ha hBounds u v
  let μ := fun i : Fin n => X.P.map (Φ i)
  have hF : Measurable (fun ω i => Φ i ω) :=
    Measurable.of_eval fun i => (hΦ i).mono (X.info_le _) le_rfl
  have hV := ae_neg_code_proxy_le X ha hBounds z hz Φ hΦ f hf u v hRep hLaw hr
  change ∀ᵐ x ∂Measure.pi μ, Cited.vPlus μ (fun x => -f x / r) x ≤
    ENNReal.ofReal ((2 * r ^ 2 * M * (b * s / a + 1)) / r ^ 2) at hV
  have hId : (2 * r ^ 2 * M * (b * s / a + 1)) / r ^ 2 = 2 * M * (b * s / a + 1) := by
    field_simp
  have hBase : 2 * M * (b * s / a + 1) ≤ (2 * M * (b / a + 1)) * (s + 1) := by
    have h0 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
      (add_nonneg (div_nonneg hb.le ha.le) hs)
    have hbs : b * s / a = (b / a) * s := by ring
    rw [hbs]
    nlinarith only [h0]
  have hCK : 2 * M * (b / a + 1) ≤ K := by
    have hh := div_nonneg hb.le hr.le
    dsimp only [K]
    linarith only [hh]
  have hProxy : ∀ᵐ x ∂Measure.pi μ, Cited.vPlus μ (fun x => -f x / r) x ≤ ENNReal.ofReal c :=
    hV.mono fun x hx => hx.trans (ENNReal.ofReal_le_ofReal (by
      rw [hId]
      exact hBase.trans (mul_le_mul_of_nonneg_right hCK hs1.le)))
  have hbK : b / r ≤ K := by
    dsimp only [K]
    have hh : 0 ≤ 2 * M * (b / a + 1) := by positivity
    linarith only [hh]
  have hRange : (b * dist u v) / r ≤ (exp 1 - 1) * c := by
    have h1 : b * s / r ≤ (b / r) * (s + 1) := by
      have hh := div_nonneg hb.le hr.le
      calc
        b * s / r = (b / r) * s := by ring
        _ ≤ (b / r) * (s + 1) := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right zero_le_one) hh
    have h2 := mul_le_mul_of_nonneg_right hbK hs1.le
    have h3 : c ≤ (exp 1 - 1) * c := by
      have hh := mul_le_mul_of_nonneg_right he hc.le
      simpa only [one_mul] using hh
    exact h1.trans (h2.trans h3)
  have hDiff := ae_code_difference_le X ha hBounds z hz Φ hΦ f hf u v hRep hLaw
  have hOs := isOs_abs_centered_of_neg_proxy μ f hf hr hc hfb hRange hProxy hDiff
  have hMean : (∫ x, f x ∂Measure.pi μ) = ∫ η, X.passTime η u v ∂X.P := by
    rw [← hLaw, integral_map hF.aemeasurable hf.aestronglyMeasurable]
    exact integral_congr_ae hRep
  have hMP : MeasurePreserving (fun ω i => Φ i ω) X.P (Measure.pi μ) := ⟨hF, hLaw⟩
  have hPull := Infra.Os.isOs_comp_measurePreserving hMP hOs
  have hScale : r * (2 * ((2 : ℝ) ^ (1 / 2 : ℝ) * (4 * sqrt ((exp 1 - 1) * c)))) =
      C * sqrt (dist u v + 1) := by
    dsimp only [C, c, s]
    rw [show (exp 1 - 1) * (K * (dist u v + 1)) =
      ((exp 1 - 1) * K) * (dist u v + 1) by ring,
      Real.sqrt_mul (mul_nonneg hePos.le hK.le)]
    ring
  rw [hScale] at hPull
  apply hPull.congr
  filter_upwards [hRep] with ω hω
  rw [hω, hMean]

end IsotropicVariance.Paper.Proofs.Classical
