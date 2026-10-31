/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.Fluctuation

/-!
# The fluctuation of one pair of cubes

The second paragraph of the proof of Lemma `lem:smallmean`.

For a pair of sets `I`, `I'`, a random field `D(u, v)` with a measurable version `V` and a mean
`e(u, v) = E D(u, v)`, the normalized fluctuation `Q⁻¹ sup_n |V(q_n) − e(q_n)|` along a sequence
`q_n` of `I × I'` is bounded in `L^p` (`lintegral_fluct_pow_le`) by three terms:
- the moments at the points of a finite mesh of `I × I'` of spacing `r`;
- the modulus quantity of equation `eq:modulus` at scale `r`;
- its mean.

Indeed, every point `x` of `I × I'` is within `r` of a point `g` of the mesh, and
`|D(x) − e(x)| ≤ |D(g) − e(g)| + |D(x) − D(g) − Δ| + |e(x) − e(g) − Δ|`, where `Δ` is the
difference of the Euclidean distances, which cancels.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.Paper.Proofs.SmallMean

variable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `∫⁻ f^{1}` against `∫⁻ f^{2p}`: Jensen with the bound in the form used below. -/
theorem lintegral_ofReal_le_of_rpow {f : Ω → ℝ} {p : ℕ} (hp : 1 ≤ p) {B : ℝ}
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ^ (2 * p : ℝ) ∂P ≤ ENNReal.ofReal B ^ (2 * p : ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal B := by
  have hq : (1 : ℝ) ≤ 2 * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hq0 : (0 : ℝ) < 2 * p := by linarith
  refine (lintegral_le_lintegral_rpow (fun ω => ENNReal.ofReal (f ω)) hq).trans ?_
  calc (∫⁻ ω, ENNReal.ofReal (f ω) ^ (2 * p : ℝ) ∂P) ^ (1 / (2 * p : ℝ))
      ≤ (ENNReal.ofReal B ^ (2 * p : ℝ)) ^ (1 / (2 * p : ℝ)) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal B := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]

/-- `∫⁻ f^p` against `∫⁻ f^{2p}`: Jensen. -/
theorem lintegral_ofReal_pow_le_of_rpow {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) {p : ℕ}
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ^ (2 * p : ℝ) ∂P ≤ ENNReal.ofReal B ^ (2 * p : ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂P ≤ ENNReal.ofReal (B ^ p) := by
  have h2 := lintegral_le_lintegral_rpow (P := P) (fun ω => ENNReal.ofReal (f ω ^ p))
    (q := 2) one_le_two
  have heq : ∀ ω, ENNReal.ofReal (f ω ^ p) ^ (2 : ℝ) = ENNReal.ofReal (f ω) ^ (2 * p : ℝ) := by
    intro ω
    rw [ENNReal.ofReal_pow (hf ω), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  simp_rw [heq] at h2
  refine h2.trans ?_
  calc (∫⁻ ω, ENNReal.ofReal (f ω) ^ (2 * p : ℝ) ∂P) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal B ^ (2 * p : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal (B ^ p) := by
        rw [← ENNReal.rpow_mul, ENNReal.ofReal_pow hB, ← ENNReal.rpow_natCast]
        congr 1
        ring

/-- **The fluctuation bound for one pair of cubes.** -/
theorem lintegral_fluct_pow_le {D : Ω → Pt m → Pt m → ℝ} {V : Ω → Pt m × Pt m → ℝ}
    (hVm : Measurable (Function.uncurry V)) {I I' : Set (Pt m)}
    (hV : ∀ᵐ ω ∂P, ∀ u ∈ I, ∀ v ∈ I', V ω (u, v) = D ω u v) {e : Pt m × Pt m → ℝ}
    (he : ∀ x ∈ I ×ˢ I', e x = ∫ ω, D ω x.1 x.2 ∂P)
    (hDint : ∀ x ∈ I ×ˢ I', Integrable (fun ω => D ω x.1 x.2) P)
    {q : ℕ → Pt m × Pt m} (hq : ∀ n, q n ∈ I ×ˢ I')
    {G : Finset (Pt m × Pt m)} (hG : ∀ g ∈ G, g ∈ I ×ˢ I') {r : ℝ}
    (hcov : ∀ x ∈ I ×ˢ I', ∃ g ∈ G, dist x.1 g.1 ≤ r ∧ dist x.2 g.2 ≤ r)
    {Bd : ℝ} (hBd : ∀ ω, ∀ u ∈ I, ∀ u₁ ∈ I, ∀ v ∈ I', ∀ v₁ ∈ I',
      |D ω u v - D ω u₁ v₁ - dist u v + dist u₁ v₁| ≤ Bd)
    {Q : ℝ} (hQ : 0 < Q) {p : ℕ} (hp : 1 ≤ p) {A₁ η : ℝ} (hη : 0 ≤ η)
    (hmom : ∀ g ∈ G, ∫⁻ ω, ENNReal.ofReal (|D ω g.1 g.2 - e g| ^ p) ∂P ≤
      ENNReal.ofReal (A₁ * Q ^ p))
    (hmod : ∫⁻ ω, ENNReal.ofReal (Contracts.modulusSup (D ω) I I' r) ^ (2 * p : ℝ) ∂P ≤
      ENNReal.ofReal (η * Q) ^ (2 * p : ℝ)) :
    ∫⁻ ω, ENNReal.ofReal ((Q⁻¹ * ⨆ n, |V ω (q n) - e (q n)|) ^ p) ∂P ≤
      ENNReal.ofReal (3 ^ (p - 1)) *
        (ENNReal.ofReal (G.card * A₁) + ENNReal.ofReal (η ^ p) + ENNReal.ofReal (η ^ p)) := by
  classical
  obtain ⟨g₀, hg₀G, hg₀1, -⟩ := hcov (q 0) (hq 0)
  have hr : 0 ≤ r := dist_nonneg.trans hg₀1
  have hBd' : ∀ ω, ∀ u ∈ I, ∀ u₁ ∈ I, ∀ v ∈ I', ∀ v₁ ∈ I',
      |D ω u v - D ω u₁ v₁ - dist u v + dist u₁ v₁| ≤ max Bd 0 :=
    fun ω u hu u₁ hu₁ v hv v₁ hv₁ => (hBd ω u hu u₁ hu₁ v hv v₁ hv₁).trans (le_max_left _ _)
  have hmodsup0 : ∀ ω, 0 ≤ Contracts.modulusSup (D ω) I I' r := fun ω =>
    (abs_nonneg _).trans (le_modulusSup (hBd ω) (hq 0).1 (hq 0).1 (hq 0).2 (hq 0).2
      (by simp only [dist_self]; exact ⟨hr, hr⟩))
  have hmodsupB : ∀ ω, Contracts.modulusSup (D ω) I I' r ≤ max Bd 0 := fun ω =>
    modulusSup_le (le_max_right _ _) (hBd' ω)
  -- the three terms
  set Mo : Ω → ℝ := fun ω => Q⁻¹ * Contracts.modulusSup (D ω) I I' r with hMo
  set c₃ : ℝ := (∫⁻ ω, ENNReal.ofReal (Contracts.modulusSup (D ω) I I' r) ∂P).toReal with hc₃
  set Y : Ω → ℝ := fun ω => ⨆ g : G, Q⁻¹ * |V ω g - e g| with hY
  have hfinmod : ∫⁻ ω, ENNReal.ofReal (Contracts.modulusSup (D ω) I I' r) ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ω, ENNReal.ofReal (max Bd 0) ∂P) (by simp) ?_
    exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hmodsupB ω)
  have hGne : Nonempty G := ⟨⟨g₀, hg₀G⟩⟩
  have hYb : ∀ ω, BddAbove (range fun g : G => Q⁻¹ * |V ω g - e g|) := fun ω =>
    (Set.finite_range _).bddAbove
  have hYle : ∀ ω, ∀ g : G, Q⁻¹ * |V ω g - e g| ≤ Y ω := fun ω g => le_ciSup (hYb ω) g
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω =>
    (mul_nonneg (inv_nonneg.2 hQ.le) (abs_nonneg _)).trans (hYle ω ⟨g₀, hg₀G⟩)
  have hYm : Measurable Y := by
    refine Measurable.iSup fun g => ?_
    exact (continuous_abs.measurable.comp
      ((hVm.comp (measurable_id.prodMk measurable_const)).sub_const _)).const_mul _
  -- the pointwise bound
  have hc₃le : ∀ x ∈ I ×ˢ I', ∀ g ∈ I ×ˢ I', dist x.1 g.1 ≤ r → dist x.2 g.2 ≤ r →
      |e x - e g - dist x.1 x.2 + dist g.1 g.2| ≤ c₃ := by
    intro x hx g hg h1 h2
    have h₁ : Integrable (fun ω => D ω x.1 x.2 - D ω g.1 g.2 - dist x.1 x.2) P :=
      ((hDint x hx).sub (hDint g hg)).sub (integrable_const _)
    have hint : Integrable (fun ω => D ω x.1 x.2 - D ω g.1 g.2 - dist x.1 x.2 + dist g.1 g.2) P :=
      h₁.add (integrable_const _)
    have hA : ∫ ω, (D ω x.1 x.2 - D ω g.1 g.2 - dist x.1 x.2 + dist g.1 g.2) ∂P =
        ∫ ω, (D ω x.1 x.2 - D ω g.1 g.2 - dist x.1 x.2) ∂P + dist g.1 g.2 := by
      rw [integral_add h₁ (integrable_const _)]
      simp
    have hB : ∫ ω, (D ω x.1 x.2 - D ω g.1 g.2 - dist x.1 x.2) ∂P =
        ∫ ω, (D ω x.1 x.2 - D ω g.1 g.2) ∂P - dist x.1 x.2 := by
      have h₂ : Integrable (fun ω => D ω x.1 x.2 - D ω g.1 g.2) P := (hDint x hx).sub (hDint g hg)
      rw [integral_sub h₂ (integrable_const _)]
      simp
    have hC : ∫ ω, (D ω x.1 x.2 - D ω g.1 g.2) ∂P =
        ∫ ω, D ω x.1 x.2 ∂P - ∫ ω, D ω g.1 g.2 ∂P := integral_sub (hDint x hx) (hDint g hg)
    have heq : e x - e g - dist x.1 x.2 + dist g.1 g.2 =
        ∫ ω, (D ω x.1 x.2 - D ω g.1 g.2 - dist x.1 x.2 + dist g.1 g.2) ∂P := by
      rw [he x hx, he g hg]
      linarith
    rw [heq]
    refine (abs_integral_le_integral_abs).trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => abs_nonneg _)
      hint.abs.aestronglyMeasurable]
    refine ENNReal.toReal_mono hfinmod (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_)
    exact le_modulusSup (hBd ω) hx.1 hg.1 hx.2 hg.2 ⟨h1, h2⟩
  have hbound : ∀ᵐ ω ∂P, Q⁻¹ * ⨆ n, |V ω (q n) - e (q n)| ≤ Y ω + Mo ω + Q⁻¹ * c₃ := by
    filter_upwards [hV] with ω hω
    have hterm : ∀ n, |V ω (q n) - e (q n)| ≤
        Q * Y ω + Contracts.modulusSup (D ω) I I' r + c₃ := by
      intro n
      obtain ⟨g, hgG, hg1, hg2⟩ := hcov (q n) (hq n)
      have hgI := hG g hgG
      have hVn : V ω (q n) = D ω (q n).1 (q n).2 := hω _ (hq n).1 _ (hq n).2
      have hVg : V ω g = D ω g.1 g.2 := hω _ hgI.1 _ hgI.2
      have h1 : |V ω g - e g| ≤ Q * Y ω := by
        have := hYle ω ⟨g, hgG⟩
        calc |V ω g - e g| = Q * (Q⁻¹ * |V ω g - e g|) := by field_simp
          _ ≤ Q * Y ω := mul_le_mul_of_nonneg_left this hQ.le
      have h2 := le_modulusSup (hBd ω) (hq n).1 hgI.1 (hq n).2 hgI.2 ⟨hg1, hg2⟩
      have h3 := hc₃le (q n) (hq n) g hgI hg1 hg2
      calc |V ω (q n) - e (q n)|
          = |(V ω g - e g) + (D ω (q n).1 (q n).2 - D ω g.1 g.2 - dist (q n).1 (q n).2 +
              dist g.1 g.2) - (e (q n) - e g - dist (q n).1 (q n).2 + dist g.1 g.2)| := by
            rw [hVn, hVg]
            ring_nf
        _ ≤ |V ω g - e g| + |D ω (q n).1 (q n).2 - D ω g.1 g.2 - dist (q n).1 (q n).2 +
              dist g.1 g.2| + |e (q n) - e g - dist (q n).1 (q n).2 + dist g.1 g.2| :=
            (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ Q * Y ω + Contracts.modulusSup (D ω) I I' r + c₃ := by gcongr
    have hsup : ⨆ n, |V ω (q n) - e (q n)| ≤
        Q * Y ω + Contracts.modulusSup (D ω) I I' r + c₃ := ciSup_le hterm
    calc Q⁻¹ * ⨆ n, |V ω (q n) - e (q n)|
        ≤ Q⁻¹ * (Q * Y ω + Contracts.modulusSup (D ω) I I' r + c₃) :=
          mul_le_mul_of_nonneg_left hsup (inv_nonneg.2 hQ.le)
      _ = Y ω + Mo ω + Q⁻¹ * c₃ := by
          simp only [hMo]
          field_simp
  have hF0 : ∀ ω, 0 ≤ Q⁻¹ * ⨆ n, |V ω (q n) - e (q n)| := fun ω =>
    mul_nonneg (inv_nonneg.2 hQ.le) (Real.iSup_nonneg fun n => abs_nonneg _)
  have hMo0 : ∀ ω, 0 ≤ Mo ω := fun ω => mul_nonneg (inv_nonneg.2 hQ.le) (hmodsup0 ω)
  have hc0 : 0 ≤ Q⁻¹ * c₃ := mul_nonneg (inv_nonneg.2 hQ.le) ENNReal.toReal_nonneg
  refine (lintegral_pow_le_of_le_add hYm hY0 hMo0 hc0 hF0 hbound hp).trans ?_
  refine mul_le_mul' le_rfl (add_le_add (add_le_add ?_ ?_) ?_)
  · -- the mesh term
    have hpt : ∀ ω, ENNReal.ofReal (Y ω ^ p) ≤
        ∑ g ∈ G.attach, ENNReal.ofReal ((Q⁻¹ * |V ω g - e g|) ^ p) := by
      intro ω
      obtain ⟨g, hg⟩ := exists_eq_ciSup_of_finite (f := fun g : G => Q⁻¹ * |V ω g - e g|)
      rw [show Y ω = Q⁻¹ * |V ω g - e g| from hg.symm]
      exact Finset.single_le_sum (f := fun g : G => ENNReal.ofReal ((Q⁻¹ * |V ω g - e g|) ^ p))
        (fun _ _ => zero_le) (Finset.mem_attach _ g)
    refine (lintegral_mono hpt).trans ?_
    have hmg : ∀ g : G, Measurable fun ω => ENNReal.ofReal ((Q⁻¹ * |V ω g - e g|) ^ p) := by
      intro g
      have h1 : Measurable fun ω => V ω g := hVm.comp (measurable_id.prodMk measurable_const)
      have h2 : Measurable fun ω => |V ω g - e g| :=
        continuous_abs.measurable.comp (h1.sub_const _)
      exact ((h2.const_mul _).pow_const p).ennreal_ofReal
    rw [lintegral_finsetSum _ fun g _ => hmg g]
    calc ∑ g ∈ G.attach, ∫⁻ ω, ENNReal.ofReal ((Q⁻¹ * |V ω g - e g|) ^ p) ∂P
        ≤ ∑ _g ∈ G.attach, ENNReal.ofReal A₁ := by
          refine Finset.sum_le_sum fun g _ => ?_
          have hgI := hG g g.2
          have hae : ∀ᵐ ω ∂P, ENNReal.ofReal ((Q⁻¹ * |V ω g - e g|) ^ p) =
              ENNReal.ofReal (Q⁻¹ ^ p) * ENNReal.ofReal (|D ω (g : Pt m × Pt m).1 g.1.2 - e g| ^ p) := by
            filter_upwards [hV] with ω hω
            rw [← ENNReal.ofReal_mul (by positivity), mul_pow,
              show V ω g = D ω (g : Pt m × Pt m).1 g.1.2 from hω _ hgI.1 _ hgI.2]
          rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          calc ENNReal.ofReal (Q⁻¹ ^ p) *
                ∫⁻ ω, ENNReal.ofReal (|D ω (g : Pt m × Pt m).1 g.1.2 - e g| ^ p) ∂P
              ≤ ENNReal.ofReal (Q⁻¹ ^ p) * ENNReal.ofReal (A₁ * Q ^ p) := by
                gcongr
                exact hmom g g.2
            _ = ENNReal.ofReal A₁ := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                rw [inv_pow]
                field_simp
      _ = ENNReal.ofReal (G.card * A₁) := by
          rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  · -- the modulus term
    refine lintegral_ofReal_pow_le_of_rpow hMo0 hη ?_
    have heq : ∀ ω, ENNReal.ofReal (Mo ω) ^ (2 * p : ℝ) = ENNReal.ofReal Q⁻¹ ^ (2 * p : ℝ) *
        ENNReal.ofReal (Contracts.modulusSup (D ω) I I' r) ^ (2 * p : ℝ) := by
      intro ω
      rw [hMo, ENNReal.ofReal_mul (inv_nonneg.2 hQ.le),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      ENNReal.ofReal_ne_top)]
    calc ENNReal.ofReal Q⁻¹ ^ (2 * p : ℝ) *
          ∫⁻ ω, ENNReal.ofReal (Contracts.modulusSup (D ω) I I' r) ^ (2 * p : ℝ) ∂P
        ≤ ENNReal.ofReal Q⁻¹ ^ (2 * p : ℝ) * ENNReal.ofReal (η * Q) ^ (2 * p : ℝ) := by
          gcongr
      _ = ENNReal.ofReal η ^ (2 * p : ℝ) := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ← ENNReal.ofReal_mul (inv_nonneg.2 hQ.le)]
          congr 2
          field_simp
  · -- the mean of the modulus
    have hc₃η : c₃ ≤ η * Q := by
      have h := lintegral_ofReal_le_of_rpow hp hmod
      rw [hc₃]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc0 ?_ p)
    calc Q⁻¹ * c₃ ≤ Q⁻¹ * (η * Q) := mul_le_mul_of_nonneg_left hc₃η (inv_nonneg.2 hQ.le)
      _ = η := by field_simp

end IsotropicVariance.Paper.Proofs.SmallMean
