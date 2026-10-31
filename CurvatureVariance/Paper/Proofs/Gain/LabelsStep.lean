/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.LabelsPsi
import CurvatureVariance.Paper.Proofs.Gain.FAClip
import CurvatureVariance.Paper.Proofs.Gain.FACore
import CurvatureVariance.Paper.Proofs.Gain.FAMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `Ψ` inherits the bounds of `Φ`, and the bound of `Φ − Ψ`

The estimates of the proof of Lemma `lem:labels` that do not depend on the geometry of the block.
Throughout, `Φ` is `normSlabTime` and `Ψ` is `labelPsi`.

* `psiMean`: the conditional expectation of a variable `Z`, given `τ|_G`, as an integral. Its
  moments are at most those of `Z` (`lintegral_ofReal_psiMean_pow_le`), and an almost sure bound by
  `Z` passes to the integrals (`ae_abs_integral_splice_le`). This is the conditional Jensen
  inequality of the paper's proof.
* `ae_abs_labelPsi_le`: "`Ψ` inherits" the bound of `sup_{Γ_G}|Φ|`: a bound `|Φ| ≤ a + Y` gives
  `|Ψ| ≤ a + E[Y | τ|_G]`, and the integrability of `Φ` at the splice.
* `ae_abs_labelPsi_sub_le`: "`Ψ` inherits" the modulus of continuity.
* `exists_abs_sub_labelPsi_le`: the Hölder step: from a bound `|Φ − Φ'| ≤ 1_E (g(τ) + g(τ'))`, with
  the affine parts cancelled, `P ⊗ P(E) ≤ π` and the moment of order `2k` of `g`, a variable `Y` of
  `L^k` norm at most `ε` with `|Φ − Ψ| ≤ Y`, whenever `√π (2^{2k} · 2 E g^{2k})^{1/2} ≤ ε^k`.
* `max_abs_sub_le_of_le`: the clipping error at the level `B`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Moments and `L^k` norms -/

/-- The `k`-th moment from an `L^k` bound (`k ≥ 1` an integer). -/
theorem lintegral_ofReal_pow_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 ≤ c) (h : eLpNorm f k P ≤ ENNReal.ofReal c) :
    ∫⁻ ω, ENNReal.ofReal (|f ω| ^ k) ∂P ≤ ENNReal.ofReal (c ^ k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hf : AEStronglyMeasurable f P := by
    by_contra hf
    rw [eLpNorm_of_not_aestronglyMeasurable hf] at h
    exact absurd h (not_le.mpr ENNReal.ofReal_lt_top)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hk1 (ENNReal.natCast_ne_top k) hf,
    ENNReal.toReal_natCast] at h
  have heq : ∀ ω, ‖f ω‖ₑ ^ (k : ℝ) = ENNReal.ofReal (|f ω| ^ k) := fun ω => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_natCast, ENNReal.ofReal_pow (abs_nonneg _)]
  simp_rw [heq] at h
  calc ∫⁻ ω, ENNReal.ofReal (|f ω| ^ k) ∂P
      = ((∫⁻ ω, ENNReal.ofReal (|f ω| ^ k) ∂P) ^ (1 / (k : ℝ))) ^ k := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel hk0, ENNReal.rpow_one]
    _ ≤ ENNReal.ofReal c ^ k := by gcongr
    _ = ENNReal.ofReal (c ^ k) := (ENNReal.ofReal_pow hc k).symm

/-- A measurable version of a variable with a finite `L^k` bound. -/
theorem exists_measurable_eq_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} {k : ℕ} {c : ℝ} (h : eLpNorm f k P ≤ ENNReal.ofReal c) :
    ∃ f' : Ω → ℝ, Measurable f' ∧ f =ᵐ[P] f' ∧ eLpNorm f' k P ≤ ENNReal.ofReal c := by
  have hf : AEStronglyMeasurable f P := by
    by_contra hf
    rw [eLpNorm_of_not_aestronglyMeasurable hf] at h
    exact absurd h (not_le.mpr ENNReal.ofReal_lt_top)
  refine ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk, ?_⟩
  rwa [← eLpNorm_congr_ae hf.ae_eq_mk]

/-! ### The conditional expectation of a variable -/

/-- The conditional expectation of `Z` given `τ|_G`, as an integral over an independent copy of the
weights outside `G`. -/
noncomputable def psiMean (P : Measure (Config m)) (G : Set (Sym2 (Vertex m))) (Z : Config m → ℝ)
    (ω : Config m) : ℝ :=
  ∫ ω', Z (outsideSplice G (ω', ω)) ∂P

theorem measurable_psiMean {P : Measure (Config m)} [IsProbabilityMeasure P]
    (G : Set (Sym2 (Vertex m))) {Z : Config m → ℝ} (hZ : Measurable Z) :
    Measurable (psiMean P G Z) :=
  (hZ.comp (measurable_outsideSplice G)).stronglyMeasurable.integral_prod_left'.measurable

/-- **The moments of the conditional expectation** are at most those of `Z`. -/
theorem lintegral_ofReal_psiMean_pow_le {M : Model m} (hM : M.Standing)
    (G : Set (Sym2 (Vertex m))) {Z : Config m → ℝ} (hZ : Measurable Z) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ ω, ENNReal.ofReal (|psiMean M.P G Z ω| ^ k) ∂M.P ≤
      ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ k) ∂M.P := by
  have := hM.probP
  have hσ := measurePreserving_outsideSplice hM G
  have h := lintegral_ofReal_fiberIntegral_pow_le (P := M.P)
    (hZ.comp (measurable_outsideSplice G)) hk
  have hm : Measurable fun ω => ENNReal.ofReal (|Z ω| ^ k) :=
    ((_root_.continuous_abs.measurable.comp hZ).pow_const k).ennreal_ofReal
  have e : ∫⁻ z, ENNReal.ofReal (|(Z ∘ outsideSplice G) z| ^ k) ∂(M.P.prod M.P) =
      ∫⁻ ω, ENNReal.ofReal (|Z ω| ^ k) ∂M.P := hσ.lintegral_comp hm
  rw [e] at h
  exact h

/-- A variable composed with the splice is integrable on the product. -/
theorem integrable_comp_outsideSplice {M : Model m} (hM : M.Standing)
    (G : Set (Sym2 (Vertex m))) {Z : Config m → ℝ} (hZm : Measurable Z)
    (hZ : Integrable Z M.P) : Integrable (Z ∘ outsideSplice G) (M.P.prod M.P) :=
  ((measurePreserving_outsideSplice hM G).integrable_comp hZm.aestronglyMeasurable).mpr hZ

/-- **The conditional Jensen inequality**: an almost sure bound by `Z`, for all `i ∈ A` at once,
passes to the integrals over an independent copy of the weights outside `G`. -/
theorem ae_abs_integral_splice_le {M : Model m} (hM : M.Standing) (G : Set (Sym2 (Vertex m)))
    {ι : Type*} {A : Set ι} {F : ι → Config m → ℝ} {Z : Config m → ℝ} (hZm : Measurable Z)
    (hZ : Integrable Z M.P) (hF : ∀ᵐ ω ∂M.P, ∀ i ∈ A, |F i ω| ≤ Z ω) :
    ∀ᵐ ω ∂M.P, ∀ i ∈ A, |∫ ω', F i (outsideSplice G (ω', ω)) ∂M.P| ≤ psiMean M.P G Z ω := by
  have := hM.probP
  have hσ := measurePreserving_outsideSplice hM G
  exact ae_abs_fiberIntegral_le (P := M.P) (F := fun i z => F i (outsideSplice G z))
    (Z := Z ∘ outsideSplice G) (integrable_comp_outsideSplice hM G hZm hZ)
    (hσ.quasiMeasurePreserving.ae hF)

/-! ### `Ψ` inherits the bounds of `Φ` -/

/-- **`Ψ` inherits the bound of `sup_{Γ_G}|Φ|`**: if `|Φ| ≤ a + Y` on `Γ`, almost surely, then for
almost every `ω` the function `Φ` at the splice is integrable on `Γ` and `|Ψ| ≤ a + E[Y | τ|_G]`. -/
theorem ae_abs_labelPsi_le {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {n : ℕ} {P : Pt m}
    {i : ℕ} (G : Set (Sym2 (Vertex m))) {Γ : Set (Vertex m × Vertex m)} {a : ℝ}
    {Y : Config m → ℝ} (hYm : Measurable Y) (hY : Integrable Y M.P)
    (hsup : ∀ᵐ ω ∂M.P, ∀ p ∈ Γ, |normSlabTime M K A ω n P i p.1 p.2| ≤ a + Y ω) :
    ∀ᵐ ω ∂M.P, ∀ p ∈ Γ,
      Integrable (fun ω' => normSlabTime M K A (outsideSplice G (ω', ω)) n P i p.1 p.2) M.P ∧
      |labelPsi M K A n P i G ω p.1 p.2| ≤ a + psiMean M.P G Y ω := by
  have := hM.probP
  have hσ := measurePreserving_outsideSplice hM G
  have hYσ := integrable_comp_outsideSplice hM G hYm hY
  have hb : ∀ᵐ z ∂(M.P.prod M.P), ∀ p ∈ Γ,
      |normSlabTime M K A (outsideSplice G z) n P i p.1 p.2| ≤ a + Y (outsideSplice G z) :=
    hσ.quasiMeasurePreserving.ae hsup
  filter_upwards [hYσ.prod_left_ae, ae_ae_swap hb] with ω hint₀ hbω p hp
  have hint : Integrable (fun ω' => Y (outsideSplice G (ω', ω))) M.P := hint₀
  have hint' : Integrable (fun ω' => a + Y (outsideSplice G (ω', ω))) M.P :=
    (integrable_const a).add hint
  have hbp : ∀ᵐ ω' ∂M.P, ‖normSlabTime M K A (outsideSplice G (ω', ω)) n P i p.1 p.2‖ ≤
      a + Y (outsideSplice G (ω', ω)) := hbω.mono fun ω' h => h p hp
  have hmeas : Measurable fun ω' => normSlabTime M K A (outsideSplice G (ω', ω)) n P i p.1 p.2 :=
    (measurable_normSlabTime M K A n P i _ _).comp
      ((measurable_outsideSplice G).comp (measurable_id.prodMk measurable_const))
  refine ⟨hint'.mono' hmeas.aestronglyMeasurable hbp, ?_⟩
  have h := norm_integral_le_of_norm_le hint' hbp
  rw [integral_add (integrable_const a) hint, integral_const, probReal_univ, one_smul] at h
  rw [labelPsi_eq]
  exact h

/-- **`Ψ` inherits the modulus of continuity**: if `|Φ(p) − Φ(ρ p)| ≤ Z` on `Γ`, almost surely, and
`Φ` at the splice is integrable at `p` and at `ρ p` for almost every `ω`, then
`|Ψ(p) − Ψ(ρ p)| ≤ E[Z | τ|_G]`. -/
theorem ae_abs_labelPsi_sub_le {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {n : ℕ} {P : Pt m}
    {i : ℕ} (G : Set (Sym2 (Vertex m))) {Γ : Set (Vertex m × Vertex m)}
    {ρ : Vertex m × Vertex m → Vertex m × Vertex m} (hρ : ∀ p ∈ Γ, ρ p ∈ Γ)
    {Z : Config m → ℝ} (hZm : Measurable Z) (hZ : Integrable Z M.P)
    (hmod : ∀ᵐ ω ∂M.P, ∀ p ∈ Γ, |normSlabTime M K A ω n P i p.1 p.2 -
      normSlabTime M K A ω n P i (ρ p).1 (ρ p).2| ≤ Z ω)
    (hint : ∀ᵐ ω ∂M.P, ∀ p ∈ Γ,
      Integrable (fun ω' => normSlabTime M K A (outsideSplice G (ω', ω)) n P i p.1 p.2) M.P) :
    ∀ᵐ ω ∂M.P, ∀ p ∈ Γ,
      |labelPsi M K A n P i G ω p.1 p.2 - labelPsi M K A n P i G ω (ρ p).1 (ρ p).2| ≤
        psiMean M.P G Z ω := by
  have h := ae_abs_integral_splice_le hM G hZm hZ hmod
  filter_upwards [h, hint] with ω h1 h2 p hp
  have e := h1 p hp
  rw [integral_sub (h2 p hp) (h2 _ (hρ p hp))] at e
  rw [labelPsi_eq, labelPsi_eq]
  exact e

/-! ### The Hölder step -/

/-- **The Hölder step** (the proof of Lemma `lem:labels`): from a bound
`|Φ − Φ'| ≤ 1_E (g(τ) + g(τ'))` on `Γ`, `P ⊗ P(E) ≤ π` and the moment of order `2k` of `g`, there is
`Y` with `‖Y‖_k ≤ ε` and `|Φ − Ψ| ≤ Y` on `Γ`, whenever `√π √(2^{2k} 2 c) ≤ ε^k`. -/
theorem exists_abs_sub_labelPsi_le {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {n : ℕ}
    {P : Pt m} {i : ℕ} (G : Set (Sym2 (Vertex m))) {Γ : Set (Vertex m × Vertex m)}
    {g : Config m → ℝ} (hgm : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω)
    {E : Set (Config m × Config m)} (hE : MeasurableSet E)
    (hEae : ∀ᵐ z ∂(M.P.prod M.P), ∀ p ∈ Γ, |normSlabTime M K A z.2 n P i p.1 p.2 -
        normSlabTime M K A (outsideSplice G z) n P i p.1 p.2| ≤
      E.indicator (fun z => g z.2 + g (outsideSplice G z)) z)
    (hint : ∀ᵐ ω ∂M.P, ∀ p ∈ Γ,
      Integrable (fun ω' => normSlabTime M K A (outsideSplice G (ω', ω)) n P i p.1 p.2) M.P)
    {k : ℕ} (hk : 1 ≤ k) {π c ε : ℝ} (hπ0 : 0 ≤ π) (hπ : (M.P.prod M.P) E ≤ ENNReal.ofReal π)
    (hc0 : 0 ≤ c) (hc : ∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * k)) ∂M.P ≤ ENNReal.ofReal c)
    (hε0 : 0 ≤ ε) (hε : Real.sqrt π * Real.sqrt (2 ^ (2 * k) * (2 * c)) ≤ ε ^ k) :
    ∃ Y : Config m → ℝ, Measurable Y ∧ eLpNorm Y k M.P ≤ ENNReal.ofReal ε ∧
      ∀ᵐ ω ∂M.P, ∀ p ∈ Γ, |normSlabTime M K A ω n P i p.1 p.2 -
        labelPsi M K A n P i G ω p.1 p.2| ≤ Y ω := by
  have := hM.probP
  set σ := outsideSplice G with hσdef
  have hσ : MeasurePreserving σ (M.P.prod M.P) M.P := measurePreserving_outsideSplice hM G
  have hsnd : MeasurePreserving Prod.snd (M.P.prod M.P) M.P := measurePreserving_snd
  let f₀ : Config m × Config m → ℝ := fun z => g z.2 + g (σ z)
  have hf₀m : Measurable f₀ := (hgm.comp measurable_snd).add (hgm.comp hσ.measurable)
  let F : Config m × Config m → ℝ := E.indicator f₀
  have hFm : Measurable F := hf₀m.indicator hE
  have hF0 : ∀ z, 0 ≤ F z := fun z => Set.indicator_nonneg (fun z _ =>
    add_nonneg (hg0 _) (hg0 _)) z
  -- the moment bound on the product: the Hölder inequality, with the cancelled moment
  have hmom : ∫⁻ z, ENNReal.ofReal (F z ^ k) ∂(M.P.prod M.P) ≤ ENNReal.ofReal (ε ^ k) := by
    refine (lintegral_indicator_pow_le hE hf₀m hk).trans ?_
    have h2 := lintegral_ofReal_add_pow_comp_le hsnd hσ hgm hg0 (2 * k)
    have h3 : ∫⁻ z, ENNReal.ofReal (f₀ z ^ (2 * k)) ∂(M.P.prod M.P) ≤
        ENNReal.ofReal (2 ^ (2 * k) * (2 * c)) := by
      refine h2.trans ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat]
      gcongr
    calc (M.P.prod M.P) E ^ (1 / 2 : ℝ) *
          (∫⁻ z, ENNReal.ofReal (f₀ z ^ (2 * k)) ∂(M.P.prod M.P)) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal π ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (2 ^ (2 * k) * (2 * c)) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal (Real.sqrt π * Real.sqrt (2 ^ (2 * k) * (2 * c))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hπ0 (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
            ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      _ ≤ ENNReal.ofReal (ε ^ k) := ENNReal.ofReal_le_ofReal hε
  have hmom' : ∫⁻ z, ENNReal.ofReal (|F z| ^ k) ∂(M.P.prod M.P) ≤ ENNReal.ofReal (ε ^ k) := by
    refine le_trans (le_of_eq (lintegral_congr fun z => ?_)) hmom
    rw [abs_of_nonneg (hF0 z)]
  have hFint : Integrable F (M.P.prod M.P) :=
    integrable_of_lintegral_ofReal_pow_lt hFm.aestronglyMeasurable hk hmom'
  refine ⟨fun ω => ∫ ω', F (ω', ω) ∂M.P, hFm.stronglyMeasurable.integral_prod_left'.measurable,
    ?_, ?_⟩
  · exact eLpNorm_le_ofReal_of_lintegral_le
      hFm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable hk hε0
      ((lintegral_ofReal_fiberIntegral_pow_le hFm hk).trans hmom')
  · have hab := ae_abs_fiberIntegral_le (P := M.P) (A := Γ)
      (F := fun (p : Vertex m × Vertex m) z => normSlabTime M K A z.2 n P i p.1 p.2 -
        normSlabTime M K A (σ z) n P i p.1 p.2) hFint hEae
    filter_upwards [hab, hint] with ω h1 h2 p hp
    have e := h1 p hp
    rw [integral_sub (integrable_const _) (h2 p hp), integral_const, probReal_univ, one_smul] at e
    rw [labelPsi_eq]
    exact e

/-! ### The clipping error -/

/-- The clipping error of a value bounded by `a + x`: for `B > 0` and `x ≥ 0`,
`(|y| − B)₊ ≤ (a − B/2)₊ + x²/(2B)`. -/
theorem max_abs_sub_le_of_le {a x y B : ℝ} (hB : 0 < B) (hy : |y| ≤ a + x) :
    max (|y| - B) 0 ≤ max (a - B / 2) 0 + x ^ 2 / (2 * B) := by
  have hb0 : 0 ≤ max (a - B / 2) 0 := le_max_right _ _
  have hq : 0 ≤ x ^ 2 / (2 * B) := by positivity
  refine max_le ?_ (by linarith)
  have h1 : a - B / 2 ≤ max (a - B / 2) 0 := le_max_left _ _
  have h2 : x - B / 2 ≤ x ^ 2 / (2 * B) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - B)]
  linarith

end CurvatureVariance.Paper.Gain
