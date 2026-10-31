/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.AVLabels
public import CurvatureVariance.Paper.Proofs.Gain.AVEnergy
import CurvatureVariance.Paper.Proofs.Gain.AVBridge
import CurvatureVariance.Paper.Proofs.Moments.Basic

/-!
# The second bound of equation `eq:residual`: the label residual of the averaged minimum

The proof of the second bound of equation `eq:residual` (the third paragraph of the proof of
[AB26, Lemma 6.3]) bounds the residual of the averaged minimum `F̄ = V⁻¹ ∑_v F_v` under resampling
each block given its label by the average over the translates `v` of the residuals of the `F_v`
(Jensen), and uses translation covariance: `F_v` is `F` at the translate by `v L w e₂`, which maps
the blocks to blocks, so the residual of `F_v` is that of `F` for the labels transported by the
translation. The transported labels are again labels of the blocks with the same error, so the
first bound of equation `eq:residual` applies to them.

* `measurable_lintegral_cond`: integrating against the law conditioned on the level set of a
  finite-valued label is measurable in the configuration.
* `labelES_average_le`: Jensen over an average.
* `labelES_comp_translate`: `E(X∘θ_a − (X∘θ_a)^{G,λ})² = E(X − X^{G−a,λ∘θ_{−a}})²`.
* `shiftLabel a λ`: the label `λ` transported by the translation `a` (`shiftLabel_eq_iff`).
* `labelEnergy_translatedMin_eq`: the label energy of `F_v` for a family of labels is that of `F`
  for the transported label family `shiftFamily`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Integrals against conditioned laws -/

/-- Integrating a jointly measurable function against the law conditioned on the level set of a
finite-valued label with measurable level sets is measurable in the configuration. -/
theorem measurable_lintegral_cond (P : Measure (Config m)) [IsFiniteMeasure P] {β : Type*}
    (lam : Config m → β) (hfin : (Set.range lam).Finite)
    (hmeas : ∀ ω, MeasurableSet (lam ⁻¹' {lam ω})) {h : Config m × Config m → ℝ≥0∞}
    (hh : Measurable h) :
    Measurable fun ω => ∫⁻ ω', h (ω, ω') ∂(P[|lam ⁻¹' {lam ω}]) := by
  classical
  have hmb : ∀ b ∈ hfin.toFinset, MeasurableSet (lam ⁻¹' {b}) := by
    intro b hb
    obtain ⟨ω, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hb
    exact hmeas ω
  have heq : (fun ω => ∫⁻ ω', h (ω, ω') ∂(P[|lam ⁻¹' {lam ω}])) = fun ω =>
      ∑ b ∈ hfin.toFinset, (lam ⁻¹' {b}).indicator
        (fun ω => ∫⁻ ω', h (ω, ω') ∂(P[|lam ⁻¹' {b}])) ω := by
    funext ω
    rw [Finset.sum_eq_single (lam ω)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro b _ hb
      rw [Set.indicator_of_notMem]
      simp only [mem_preimage, mem_singleton_iff]
      exact fun h' => hb h'.symm
    · intro h'
      exact absurd ((Set.Finite.mem_toFinset hfin).2 ⟨ω, rfl⟩) h'
  rw [heq]
  refine Finset.measurable_sum _ fun b hb => ?_
  exact (hh.lintegral_prod_right').indicator (hmb b hb)

/-- **Jensen over an average** for the residual given a label: the residual of an average
`V⁻¹ ∑_{v<V} F_v` is at most the average of those of the `F_v`. -/
theorem labelES_average_le (P : Measure (Config m)) [IsFiniteMeasure P] (F : ℕ → Config m → ℝ)
    (hF : ∀ v, Measurable (F v)) {V : ℕ} (hV : 0 < V) (G : Set (Sym2 (Vertex m))) {β : Type*}
    (lam : Config m → β) (hfin : (Set.range lam).Finite)
    (hmeas : ∀ ω, MeasurableSet (lam ⁻¹' {lam ω})) :
    labelES P (fun ω => (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω) G lam ≤
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, labelES P (F v) G lam := by
  have hjoint : ∀ v, Measurable fun p : Config m × Config m =>
      ENNReal.ofReal ((F v p.1 - F v (resample G p.1 p.2)) ^ 2) := fun v =>
    ((((hF v).comp measurable_fst).sub ((hF v).comp (Responses.measurable_resample G))).pow_const
      2).ennreal_ofReal
  have hinner : ∀ v ω, Measurable fun ω' =>
      ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) := fun v ω =>
    (hjoint v).comp (measurable_const.prodMk measurable_id)
  have hout : ∀ v, Measurable fun ω => ∫⁻ ω',
      ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) ∂(P[|lam ⁻¹' {lam ω}]) := fun v =>
    measurable_lintegral_cond P lam hfin hmeas (hjoint v)
  have hpt : ∀ ω ω', ENNReal.ofReal (((V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω -
      (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v (resample G ω ω')) ^ 2) ≤
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) :=
    fun ω ω' => ofReal_sq_sub_average_le hV (fun v => F v ω) (fun v => F v (resample G ω ω'))
  unfold labelES
  refine (lintegral_mono fun ω => lintegral_mono fun ω' => hpt ω ω').trans (le_of_eq ?_)
  have h1 : ∀ ω, ∫⁻ ω', (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V,
      ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) ∂(P[|lam ⁻¹' {lam ω}]) =
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ∫⁻ ω',
        ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) ∂(P[|lam ⁻¹' {lam ω}]) :=
    fun ω => by
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun v _ => hinner v ω),
        lintegral_finsetSum _ fun v _ => hinner v ω]
  simp_rw [h1]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun v _ => hout v),
    lintegral_finsetSum _ fun v _ => hout v]

/-- **The residual of a translated observable**: under a translation invariant law,
`E(X∘θ_a − (X∘θ_a)^{G,λ})² = E(X − X^{G−a, λ∘θ_{−a}})²`, `G − a` the set of the edges whose
translate by `a` lies in `G`. -/
theorem labelES_comp_translate {P : Measure (Config m)} {a : Vertex m}
    (ha : MeasurePreserving (translate a) P P) (X : Config m → ℝ) (G : Set (Sym2 (Vertex m)))
    {β : Type*} (lam : Config m → β) (hmeas : ∀ ω, MeasurableSet (lam ⁻¹' {lam ω})) :
    labelES P (fun ω => X (translate a ω)) G lam =
      labelES P X {s | Sym2.map (· + a) s ∈ G} (fun ω => lam (translate (-a) ω)) := by
  have hemb : MeasurableEmbedding (translate a : Config m → Config m) :=
    (translateEquiv a).measurableEmbedding
  have hinv : ∀ ω, translate (-a) (translate a ω) = ω := fun ω => by
    rw [translate_translate, neg_add_cancel, translate_zero]
  unfold labelES
  symm
  rw [← ha.lintegral_comp_emb hemb]
  refine lintegral_congr fun ω => ?_
  simp only [hinv]
  have hS : MeasurableSet ((fun ω' => lam (translate (-a) ω')) ⁻¹' {lam ω}) := by
    have h := (measurable_translate (-a)) (hmeas ω)
    simpa only [preimage_preimage] using h
  have hpre : translate a ⁻¹' ((fun ω' => lam (translate (-a) ω')) ⁻¹' {lam ω}) =
      lam ⁻¹' {lam ω} := by
    ext ω'
    simp only [mem_preimage, mem_singleton_iff, hinv]
  conv_lhs => rw [← ha.map_eq, cond_map_eq P (measurable_translate a) hS, hpre]
  rw [show (Measure.map (translate a) (P[|lam ⁻¹' {lam ω}])) =
      Measure.map (translateEquiv a) (P[|lam ⁻¹' {lam ω}]) from rfl, lintegral_map_equiv]
  refine lintegral_congr fun ω' => ?_
  rw [show (translateEquiv a) ω' = translate a ω' from rfl, ← translate_resample]

/-! ### Transported labels -/

/-- The label `λ` (of some block) transported by the translation `a`:
`(shiftLabel a λ)(ω)(u, v) = λ(θ_{−a} ω)(u + a, v + a)`. -/
def shiftLabel (a : Vertex m) (lam : Config m → Vertex m → Vertex m → ℝ) :
    Config m → Vertex m → Vertex m → ℝ :=
  fun ω u v => lam (translate (-a) ω) (u + a) (v + a)

/-- The transported label has the level sets of `λ ∘ θ_{−a}`. -/
theorem shiftLabel_eq_iff (a : Vertex m) (lam : Config m → Vertex m → Vertex m → ℝ)
    (ω ω' : Config m) :
    shiftLabel a lam ω' = shiftLabel a lam ω ↔
      lam (translate (-a) ω') = lam (translate (-a) ω) := by
  constructor
  · intro h
    funext u v
    have := congr_fun₂ h (u - a) (v - a)
    simpa [shiftLabel] using this
  · intro h
    funext u v
    simp only [shiftLabel, h]

/-! ### The common translations `v L w e₂` -/

/-- The common translation `v L w e₂` of the minima `F_m` (the text before Lemma `lem:residual`). -/
def commonShift (m v L w : ℕ) : Vertex m :=
  ((0 : ℤ), ((v * L * w : ℕ) : ℤ) • transverseUnit m)

/-- The label families transported by `v L w e₂`: the block `g` gets the label of the block
`g + v e₂` transported by the translation. -/
def shiftFamily (v L w : ℕ)
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ) :
    ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ :=
  fun i o g => shiftLabel (commonShift m v L w) (lam i o (g + (v : ℤ) • transverseUnit m))

/-- **Translation covariance of the label energy** (the third paragraph of the proof of
[AB26, Lemma 6.3]): the label energy of `F_v` for a family of labels is that of `F` for the
transported family. -/
theorem labelEnergy_translatedMin_eq {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {L n : ℕ}
    (hw : 0 < wInt M K A n) (ℓ : ℕ) (y : Fin m → ℤ) (v : ℕ)
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ)
    (o : ℕ → Fin m → ℤ)
    (hmeas : ∀ i < K, ∀ g ω, MeasurableSet (lam (i + 1) (o (i + 1)) g ⁻¹'
      {lam (i + 1) (o (i + 1)) g ω})) :
    labelEnergy M.P (fun ω => translatedMin M ω n K ℓ y
        (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m)) n (wInt M K A n) L K
        (targetSlope ℓ y) lam o =
      labelEnergy M.P (fun ω => targetMin M ω n K ℓ y) n (wInt M K A n) L K (targetSlope ℓ y)
        (shiftFamily v L (wInt M K A n) lam) o := by
  set w := wInt M K A n
  set t := targetSlope ℓ y
  set a : Vertex m := commonShift m v L w
  set s : Fin m → ℤ := (v : ℤ) • transverseUnit m
  have hmp := Moments.standing_measurePreserving_translate hM a
  unfold labelEnergy
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiK : i < K := Finset.mem_range.1 hi
  have h1 : ∀ g, labelES M.P (fun ω => translatedMin M ω n K ℓ y
      (((v * L * w : ℕ) : ℤ) • transverseUnit m)) (block n w L t (i + 1) (o (i + 1)) g)
      (lam (i + 1) (o (i + 1)) g) =
      labelES M.P (fun ω => targetMin M ω n K ℓ y) (block n w L t (i + 1) (o (i + 1)) (g - s))
        (fun ω => lam (i + 1) (o (i + 1)) g (translate (-a) ω)) := by
    intro g
    simp_rw [Gain.translatedMin_eq_targetMin]
    rw [show (((0 : ℤ), ((v * L * w : ℕ) : ℤ) • transverseUnit m) : Vertex m) = a from rfl,
      labelES_comp_translate hmp (fun ω => targetMin M ω n K ℓ y) _ _ (hmeas i hiK g)]
    congr 1
    exact setOf_map_add_mem_block hw t (i + 1) v (o (i + 1)) g
  simp_rw [h1]
  rw [← (Equiv.addRight s).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  refine labelES_congr_level _ _ _ fun ω ω' => ?_
  exact (shiftLabel_eq_iff a _ ω ω').symm

end CurvatureVariance.Paper.Gain
