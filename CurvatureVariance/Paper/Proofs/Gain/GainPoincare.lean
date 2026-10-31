/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Inputs
public import CurvatureVariance.Paper.Proofs.Gain.FewTranslates
import CurvatureVariance.Infra.EfronStein.CountableProduct
import CurvatureVariance.Infra.Entropy.Martingale
import CurvatureVariance.Paper.Proofs.Gain.FewTranslatesBound
import Mathlib.Probability.Independence.InfinitePi

/-!
# [AB26, Proposition 1.3] for `f`, with the `X_G` as the variables

As `IsotropicVariance.Paper.Proofs.Gain.PoincareBound` in the continuum library, adapted. The
first step of the proof of [AB26, Proposition 6.5], which the paper applies in the proof of
Proposition `prop:gain`, applies [AB26, Proposition 1.3] to `f = E[F̄ | (X_G)_G]`, "with the `X_G`
as the variables and `E_G[f]` the expectation of `f` with respect to `X_G` alone" (the text before
[AB26, Lemma 6.3]). That proposition is a statement on a product measure, and `f` lives on the
weights. This file makes the transfer.

* `modifiedPoincare_of_labels`: the transfer for independent finite-valued variables on a
  probability space, written with the variables `f − E_c`, where `E_c` is the sum over the values
  of the variable `c`. It also gives the case left open by the Lean form of the proposition: when
  `Σ_c E[|f − E_c|]² = 0` the logarithm is `0`, and Efron–Stein gives `Var[f] = 0`. Here Efron–Stein
  is `Infra.EfronStein.evariance_le_half_tsum_resampleEnergy`, which rests on
  `CurvatureVariance.blm_proposition1`. The continuum's variables have one type of values. Here
  each variable has its own finite type, its set of values (`labelOf`).
* `IsOffsetLabels.modifiedPoincare_labelMean`: the inequality of the first display of the proof of
  [AB26, Proposition 6.5] for `f` measurable for the labels of the blocks with offsets `o`, with the
  two sums of `Contracts.FewTranslatesStatement`. The conditional expectations given the other
  labels are identified with the expectations over `X_G` alone by `Gain.condExp_other_eq_sum_label`.

The continuum's independence of the labels is that of the noise in disjoint sets. Here it is
`iIndepFun_of_disjoint_edges`, which generalizes `Responses.iIndepFun_slab_functions`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain.Printed

open CurvatureVariance.Paper

/-! ### Independent finite-valued variables -/

section Generic

variable {ι : Type} {V : ι → Type} {Ω : Type*} [Countable ι] [DecidableEq ι] [∀ c, Fintype (V c)]
  [∀ c, MeasurableSpace (V c)] [∀ c, MeasurableSingletonClass (V c)] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- `E[|g|]² ≤ E[g²]` for `g ∈ L²`. -/
theorem sq_integral_abs_le_integral_sq {Ω' : Type*} {_ : MeasurableSpace Ω'} {ν : Measure Ω'}
    [IsProbabilityMeasure ν] {g : Ω' → ℝ} (hg : MemLp g 2 ν) :
    (∫ x, |g x| ∂ν) ^ 2 ≤ ∫ x, g x ^ 2 ∂ν := by
  have h := variance_nonneg (|g|) ν
  rw [variance_eq_sub hg.abs] at h
  simp only [Pi.pow_apply, Pi.abs_apply, sq_abs] at h
  linarith only [h]

/-- **[AB26, Proposition 1.3] for a function of independent variables on a probability space**: for
independent finite-valued variables `lab c`, each value of probability `0` or at least `α`, and
`f = φ((lab c)_c)` almost surely, with `E_c` the expectation of `f` over the variable `c` alone
(`hE`), the inequality of the proposition holds for `f`. If the sum of the `L¹` terms vanishes, then
`Var[f] = 0` by Efron–Stein: the Lean form of the logarithm of `V/0` is `0`, so this case is not
contained in the inequality. As `modifiedPoincare_of_labels` of the continuum library's module
`IsotropicVariance.Paper.Proofs.Gain.PoincareBound`. The Efron–Stein step is
`Infra.EfronStein.evariance_le_half_tsum_resampleEnergy` of this library, the extension of
`CurvatureVariance.blm_proposition1` to countably many variables. -/
theorem modifiedPoincare_of_labels (hMP : Contracts.ModifiedPoincareStatement.{0, 0})
    (lab : ∀ c, Ω → V c) (hlab : ∀ c, Measurable (lab c)) (hind : iIndepFun lab P) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hatom : ∀ c v, P (lab c ⁻¹' {v}) = 0 ∨ ENNReal.ofReal α ≤ P (lab c ⁻¹' {v}))
    {f : Ω → ℝ} {φ : (∀ c, V c) → ℝ} (hφ : Measurable φ)
    (hfφ : f =ᵐ[P] φ ∘ fun ω c => lab c ω) (hf : MemLp f 2 P) (E : ι → Ω → ℝ)
    (hE : ∀ c, E c =ᵐ[P] fun ω =>
      ∑ v, P.real (lab c ⁻¹' {v}) * φ (Function.update (fun c' => lab c' ω) c v))
    (hsum : Summable fun c => ∫ ω, (f ω - E c ω) ^ 2 ∂P) :
    variance f P * Real.log (variance f P / ∑' c, (∫ ω, |f ω - E c ω| ∂P) ^ 2) ≤
        4 / α * ∑' c, ∫ ω, (f ω - E c ω) ^ 2 ∂P ∧
      (∑' c, (∫ ω, |f ω - E c ω| ∂P) ^ 2 = 0 → variance f P = 0) := by
  set Φ : Ω → ∀ c, V c := fun ω c => lab c ω with hΦdef
  have hΦ : Measurable Φ := measurable_pi_iff.2 hlab
  set μ : ∀ c, Measure (V c) := fun c => P.map (lab c) with hμdef
  have hμ : ∀ c, IsProbabilityMeasure (μ c) := fun c =>
    (Measure.isProbabilityMeasure_map_iff (hlab c).aemeasurable).2 inferInstance
  have hmap : P.map Φ = Measure.infinitePi μ :=
    (iIndepFun_iff_map_fun_eq_infinitePi_map hlab).1 hind
  have hμv : ∀ c (v : V c), μ c {v} = P (lab c ⁻¹' {v}) := fun c v =>
    Measure.map_apply (hlab c) (measurableSet_singleton v)
  have hatom' : ∀ c (v : V c), μ c {v} = 0 ∨ ENNReal.ofReal α ≤ μ c {v} := fun c v => by
    rw [hμv]
    exact hatom c v
  have hφL : MemLp φ 2 (Measure.infinitePi μ) := by
    rw [← hmap]
    exact (memLp_map_measure_iff hφ.aestronglyMeasurable hΦ.aemeasurable).2 (hf.ae_eq hfφ)
  -- the coordinate differences
  set D : ι → (∀ c, V c) → ℝ := fun c => coordDiff μ c φ with hDdef
  have hDeq : ∀ c, D c = coordDiff μ c φ := fun _ => rfl
  have hDm : ∀ c, Measurable (D c) := fun c => by
    rw [hDeq]
    exact hφ.sub (Infra.Entropy.measurable_coordAvg c hφ)
  have hDL : ∀ c, MemLp (D c) 2 (Measure.infinitePi μ) := fun c => by
    rw [hDeq]
    exact Infra.Entropy.memLp_coordDiff c hφL
  have hD : ∀ c, D c ∘ Φ =ᵐ[P] fun ω => f ω - E c ω := by
    intro c
    filter_upwards [hE c, hfφ] with ω h1 h2
    have e : ∫ y, φ (Function.update (Φ ω) c y) ∂μ c =
        ∑ v, P.real (lab c ⁻¹' {v}) * φ (Function.update (Φ ω) c v) := by
      rw [integral_fintype Integrable.of_finite]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_eq_mul, measureReal_def, measureReal_def, hμv]
    change φ (Φ ω) - ∫ y, φ (Function.update (Φ ω) c y) ∂μ c = f ω - E c ω
    rw [e, h1, h2]
    rfl
  have e2 : ∀ c, ∫ x, D c x ^ 2 ∂Measure.infinitePi μ = ∫ ω, (f ω - E c ω) ^ 2 ∂P := by
    intro c
    rw [← hmap, integral_map hΦ.aemeasurable ((hDm c).pow_const 2).aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hD c] with ω h
    rw [← h]
    rfl
  have e1 : ∀ c, ∫ x, |D c x| ∂Measure.infinitePi μ = ∫ ω, |f ω - E c ω| ∂P := by
    intro c
    have hm : AEStronglyMeasurable (fun x => |D c x|) (P.map Φ) :=
      (continuous_abs.measurable.comp (hDm c)).aestronglyMeasurable
    rw [← hmap, integral_map hΦ.aemeasurable hm]
    refine integral_congr_ae ?_
    filter_upwards [hD c] with ω h
    rw [← h]
    rfl
  have hV : variance φ (Measure.infinitePi μ) = variance f P := by
    rw [← hmap, variance_map (hmap ▸ hφ.aemeasurable) hΦ.aemeasurable]
    exact variance_congr hfφ.symm
  have hsum' : Summable fun c => ∫ x, D c x ^ 2 ∂Measure.infinitePi μ := by
    simpa only [e2] using hsum
  have hmain := hMP μ hα hα1 hatom' hφ hφL hsum'
  have e2' : ∀ c, ∫ x, coordDiff μ c φ x ^ 2 ∂Measure.infinitePi μ =
      ∫ ω, (f ω - E c ω) ^ 2 ∂P := e2
  have e1' : ∀ c, ∫ x, |coordDiff μ c φ x| ∂Measure.infinitePi μ =
      ∫ ω, |f ω - E c ω| ∂P := e1
  simp only [hV, e2', e1'] at hmain
  refine ⟨hmain, fun h0 => ?_⟩
  -- Efron–Stein, when the `L¹` sum vanishes
  have hle : ∀ c, (∫ ω, |f ω - E c ω| ∂P) ^ 2 ≤ ∫ ω, (f ω - E c ω) ^ 2 ∂P := fun c => by
    rw [← e2, ← e1]
    exact sq_integral_abs_le_integral_sq (hDL c)
  have hsum1 : Summable fun c => (∫ ω, |f ω - E c ω| ∂P) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle hsum
  have hzero := (hasSum_zero_iff_of_nonneg fun _ => sq_nonneg _).1 (h0 ▸ hsum1.hasSum)
  have hD0 : ∀ c, ∫ x, D c x ^ 2 ∂Measure.infinitePi μ = 0 := by
    intro c
    have h1 : ∫ x, |D c x| ∂Measure.infinitePi μ = 0 := by
      rw [e1]
      exact pow_eq_zero_iff two_ne_zero |>.1 (congrFun hzero c)
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _)
      ((hDL c).integrable one_le_two).abs).1 h1
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    simp only [Pi.zero_apply, abs_eq_zero] at hx ⊢
    simp [hx]
  have hE0 : ∀ c, Infra.EfronStein.resampleEnergy μ φ c = 0 := fun c => by
    have h := ofReal_integral_eq_lintegral_ofReal (hDL c).integrable_sq
      (ae_of_all _ fun x => sq_nonneg (D c x))
    rw [hD0 c, ENNReal.ofReal_zero] at h
    rw [Infra.EfronStein.resampleEnergy_eq_two_mul_lintegral_sub_coordAverage μ hφ hφL c]
    exact mul_eq_zero_of_right _ h.symm
  -- `CurvatureVariance.blm_proposition1`, through its extension to countably many variables
  have hES := Infra.EfronStein.evariance_le_half_tsum_resampleEnergy μ hφL
  simp only [hE0, tsum_zero, ENNReal.zero_div, nonpos_iff_eq_zero] at hES
  rw [← hV, variance, hES, ENNReal.toReal_zero]

omit [Countable ι] [DecidableEq ι] in
/-- A sum of real terms bounded in `[0, ∞]` is a convergent real sum. -/
theorem summable_tsum_le_of_tsum_ofReal_le {a : ι → ℝ} (ha : ∀ c, 0 ≤ a c) {A : ℝ} (hA : 0 ≤ A)
    (h : ∑' c, ENNReal.ofReal (a c) ≤ ENNReal.ofReal A) : Summable a ∧ ∑' c, a c ≤ A := by
  have htop : ∑' c, ENNReal.ofReal (a c) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hs := ENNReal.summable_toReal htop
  simp only [ENNReal.toReal_ofReal (ha _)] at hs
  refine ⟨hs, ?_⟩
  have e := ENNReal.tsum_toReal_eq (f := fun c => ENNReal.ofReal (a c))
    fun _ => ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal (ha _)] at e
  rw [← e]
  exact ENNReal.toReal_le_of_le_ofReal hA h

end Generic

/-! ### Functions of disjoint sets of edges -/

section Edges

variable {m : ℕ}

/-- **Functions of pairwise disjoint sets of edges are independent** under an i.i.d. law:
`Responses.iIndepFun_slab_functions` for any family of sets of edges. -/
theorem iIndepFun_of_disjoint_edges {P : Measure (Config m)} {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] (hP : IsIIDWeights P F) {κ : Type*} {γ : κ → Type*}
    [∀ k, MeasurableSpace (γ k)] (E : κ → Set (Edge m))
    (hE : Pairwise fun k k' => Disjoint (E k) (E k')) (Z : ∀ k, Config m → γ k)
    (hZ : ∀ k, Measurable (Z k))
    (hlocal : ∀ k (ω ω' : Config m), (∀ e ∈ E k, ω e = ω' e) → Z k ω = Z k ω') :
    iIndepFun Z P := by
  classical
  let ext : ∀ k, (E k → ℝ≥0) → Config m := fun k ξ e =>
    if h : e ∈ E k then ξ ⟨e, h⟩ else 0
  have hext : ∀ k, Measurable (ext k) := by
    intro k
    refine measurable_pi_iff.mpr fun e => ?_
    by_cases he : e ∈ E k
    · simpa only [ext, he, dite_true] using measurable_pi_apply (⟨e, he⟩ : E k)
    · simpa only [ext, he, dite_false] using
        (measurable_const : Measurable (fun _ : E k → ℝ≥0 => (0 : ℝ≥0)))
  rw [Infra.FPP.IsIIDWeights.eq_infinitePi hP]
  have hind := Infra.EfronStein.iIndepFun_comp_restrict_infinitePi
    (fun _ : Edge m => F) E hE (fun k ξ => Z k (ext k ξ)) (fun k => (hZ k).comp (hext k))
  convert hind using 1
  funext k ω
  exact hlocal k ω (ext k fun e => ω e.1) (fun e he => by simp only [ext, he, dite_true])

end Edges

/-! ### The labels of the blocks with given offsets -/

section Labels

variable {m n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ} {β : Type}
  {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β} {M : Model m}

/-- The label of the block `c = (i, g)` of slab `i + 1`, with values in the set of its values. -/
def labelOf (o : ℕ → Fin m → ℤ) (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β)
    (c : Fin K × (Fin m → ℤ)) :
    Config m → Set.range (lam ((c.1 : ℕ) + 1) (o ((c.1 : ℕ) + 1)) c.2) :=
  Set.rangeFactorization _

/-- The label with values in its set of values has the information of the label. -/
theorem comap_labelOf (c : Fin K × (Fin m → ℤ)) :
    MeasurableSpace.comap (labelOf o lam c) ⊤ =
      MeasurableSpace.comap (lam ((c.1 : ℕ) + 1) (o ((c.1 : ℕ) + 1)) c.2) ⊤ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨S, -, rfl⟩
    refine ⟨Subtype.val '' S, MeasurableSpace.measurableSet_top, ?_⟩
    ext ω
    simp [labelOf, Set.rangeFactorization]
  · rintro _ ⟨S, -, rfl⟩
    exact ⟨Subtype.val ⁻¹' S, MeasurableSpace.measurableSet_top, rfl⟩

/-- A sum over the blocks of the `K` slabs. -/
theorem tsum_blockIdx (T : ℕ → (Fin m → ℤ) → ℝ≥0∞) :
    ∑' c : Fin K × (Fin m → ℤ), T (c.1 : ℕ) c.2 =
      ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ, T i g := by
  rw [ENNReal.tsum_prod', tsum_fintype, Finset.sum_range]

/-- **[AB26, Proposition 1.3] for `f`** (the second paragraph of the proof of
[AB26, Proposition 6.5]): for `f ∈ L²` measurable for the labels of the blocks with offsets `o`,
each value of a label of probability at least `α`, and `Σ_G ‖f − E_G[f]‖₂² ≤ a` and
`Σ_G ‖f − E_G[f]‖₁² ≤ b`, the two sums `S ≤ a` and `B ≤ b` satisfy the inequality of the paper,
`Var[f] log(Var[f]/B) ≤ (4/α) S`. Moreover `B = 0` forces `Var[f] = 0`. -/
theorem _root_.CurvatureVariance.Paper.Gain.IsOffsetLabels.modifiedPoincare_labelMean
    (hMP : Contracts.ModifiedPoincareStatement.{0, 0}) (hM : M.Standing)
    (h : IsOffsetLabels n w L K t o lam) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hat : ∀ i < K, ∀ (g : Fin m → ℤ) (ω : Config m),
      ENNReal.ofReal α ≤ M.P (lam (i + 1) (o (i + 1)) g ⁻¹' {lam (i + 1) (o (i + 1)) g ω}))
    {f : Config m → ℝ} (hf : MemLp f 2 M.P)
    (hfm : StronglyMeasurable[blockLabelSigma K o lam Set.univ] f) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h2 : ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
      eLpNorm (f - integrateLabel M.P f K o lam i g) 2 M.P ^ 2 ≤ ENNReal.ofReal a)
    (h1 : ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
      eLpNorm (f - integrateLabel M.P f K o lam i g) 1 M.P ^ 2 ≤ ENNReal.ofReal b) :
    ∃ S B : ℝ, 0 ≤ B ∧ S ≤ a ∧ B ≤ b ∧
      variance f M.P * Real.log (variance f M.P / B) ≤ 4 / α * S ∧
      (B = 0 → variance f M.P = 0) := by
  classical
  have := hM.probP
  have := hM.probF
  let ι := Fin K × (Fin m → ℤ)
  let V : ι → Type := fun c => Set.range (lam ((c.1 : ℕ) + 1) (o ((c.1 : ℕ) + 1)) c.2)
  have hfin : ∀ c : ι, (Set.range (lam ((c.1 : ℕ) + 1) (o ((c.1 : ℕ) + 1)) c.2)).Finite :=
    fun c => (h c.1 c.1.2 c.2).finite
  let _ : ∀ c, Fintype (V c) := fun c => (hfin c).fintype
  let _ : ∀ c, MeasurableSpace (V c) := fun _ => ⊤
  have _ : ∀ c, MeasurableSingletonClass (V c) :=
    fun _ => ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  set lab : ∀ c : ι, Config m → V c := fun c => labelOf o lam c with hlabdef
  have hcomap : ∀ c : ι, MeasurableSpace.comap (lab c) ⊤ ≤
      (inferInstance : MeasurableSpace (Config m)) := fun c =>
    (show MeasurableSpace.comap (lab c) ⊤ = _ from comap_labelOf c).le.trans
      (h c.1 c.1.2 c.2).comap_le
  have hlab : ∀ c, Measurable (lab c) := fun c => Measurable.of_comap_le (hcomap c)
  have hind : iIndepFun lab M.P := by
    refine iIndepFun_of_disjoint_edges hM.iid
      (fun c : ι => {e : Edge m | e.1 ∈ block n w L t ((c.1 : ℕ) + 1) (o ((c.1 : ℕ) + 1)) c.2}) ?_
      lab hlab fun c ω ω' he => ?_
    · intro c c' hne
      refine Set.disjoint_left.2 fun e he he' => hne ?_
      obtain ⟨h₁, h₂⟩ := LabelResidual.eq_of_mem_block_of_mem_block he he'
      exact Prod.ext (Fin.ext h₁) h₂
    · exact Subtype.ext ((h c.1 c.1.2 c.2).dep ω ω' he)
  have hatom : ∀ c v, M.P (lab c ⁻¹' {v}) = 0 ∨ ENNReal.ofReal α ≤ M.P (lab c ⁻¹' {v}) := by
    rintro c ⟨_, ω, rfl⟩
    refine Or.inr ((hat c.1 c.1.2 c.2 ω).trans (le_of_eq ?_))
    congr 1
    ext ω'
    simp only [mem_preimage, mem_singleton_iff, hlabdef, labelOf, Set.rangeFactorization]
    exact ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
  -- `f` is a measurable function of the labels
  set labels : Config m → ∀ c, V c := fun ω c => lab c ω with hlabels
  have hle : blockLabelSigma K o lam Set.univ ≤
      MeasurableSpace.comap labels MeasurableSpace.pi := by
    refine iSup₂_le fun p hp => ?_
    let c : ι := (⟨p.1, hp.1⟩, p.2)
    have e : MeasurableSpace.comap (lam (p.1 + 1) (o (p.1 + 1)) p.2) ⊤ =
        MeasurableSpace.comap (lab c) ⊤ := (comap_labelOf c).symm
    rw [e]
    change MeasurableSpace.comap ((fun x => x c) ∘ labels) ⊤ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  obtain ⟨φ, hφ, hfφ⟩ := (hfm.measurable.mono hle le_rfl).exists_eq_measurable_comp
  set E : ι → Config m → ℝ := fun c => integrateLabel M.P f K o lam c.1 c.2 with hEdef
  have hE : ∀ c, E c =ᵐ[M.P] fun ω => ∑ v, M.P.real (lab c ⁻¹' {v}) *
      φ (Function.update (fun c' => lab c' ω) c v) := by
    intro c
    have hO : blockLabelSigma K o lam {((c.1 : ℕ), c.2)}ᶜ ≤
        (inferInstance : MeasurableSpace (Config m)) := h.blockLabelSigma_le _
    have hindc : Indep (MeasurableSpace.comap (lab c) ⊤)
        (blockLabelSigma K o lam {((c.1 : ℕ), c.2)}ᶜ) M.P := by
      rw [show MeasurableSpace.comap (lab c) ⊤ = _ from comap_labelOf c]
      exact h.indep_label_otherLabels hM c.1.2 c.2
    have hother : ∀ c' : ι, c' ≠ c → MeasurableSpace.comap (lab c') ⊤ ≤
        blockLabelSigma K o lam {((c.1 : ℕ), c.2)}ᶜ := fun c' hne => by
      rw [show MeasurableSpace.comap (lab c') ⊤ = _ from comap_labelOf c']
      refine le_iSup₂_of_le ((c'.1 : ℕ), c'.2) ⟨c'.1.2, fun hmem => hne ?_⟩ le_rfl
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj hmem
      exact Prod.ext (Fin.ext h₁) h₂
    exact condExp_other_eq_sum_label lab c hO (hcomap c) hindc hother hφ
      (EventuallyEq.of_eq hfφ) (hf.integrable one_le_two)
  have hL2 : ∀ c, MemLp (f - E c) 2 M.P := fun c => hf.sub (hf.condExp one_le_two)
  -- the two sums, as real sums
  have e2 : ∀ c, ENNReal.ofReal (∫ ω, (f ω - E c ω) ^ 2 ∂M.P) = eLpNorm (f - E c) 2 M.P ^ 2 := by
    intro c
    change ENNReal.ofReal (∫ ω, (f - E c) ω ^ 2 ∂M.P) = _
    rw [ofReal_integral_eq_lintegral_ofReal (hL2 c).integrable_sq
      (ae_of_all _ fun _ => sq_nonneg _), sq_eLpNorm_two_eq M.P (hL2 c).aestronglyMeasurable]
  have e1 : ∀ c, ENNReal.ofReal ((∫ ω, |f ω - E c ω| ∂M.P) ^ 2) =
      eLpNorm (f - E c) 1 M.P ^ 2 := by
    intro c
    change ENNReal.ofReal ((∫ ω, |(f - E c) ω| ∂M.P) ^ 2) = _
    rw [ENNReal.ofReal_pow (integral_nonneg fun _ => abs_nonneg _),
      ofReal_integral_eq_lintegral_ofReal ((hL2 c).integrable one_le_two).abs
        (ae_of_all _ fun _ => abs_nonneg _),
      eLpNorm_one_eq_ofReal M.P (hL2 c).aestronglyMeasurable]
  have hs2 : ∑' c, ENNReal.ofReal (∫ ω, (f ω - E c ω) ^ 2 ∂M.P) ≤ ENNReal.ofReal a := by
    simp only [e2]
    exact (tsum_blockIdx fun i g =>
      eLpNorm (f - integrateLabel M.P f K o lam i g) 2 M.P ^ 2).le.trans h2
  have hs1 : ∑' c, ENNReal.ofReal ((∫ ω, |f ω - E c ω| ∂M.P) ^ 2) ≤ ENNReal.ofReal b := by
    simp only [e1]
    exact (tsum_blockIdx fun i g =>
      eLpNorm (f - integrateLabel M.P f K o lam i g) 1 M.P ^ 2).le.trans h1
  obtain ⟨hsum2, hle2⟩ := summable_tsum_le_of_tsum_ofReal_le
    (fun _ => integral_nonneg fun _ => sq_nonneg _) ha hs2
  obtain ⟨hsum1, hle1⟩ := summable_tsum_le_of_tsum_ofReal_le (fun _ => sq_nonneg _) hb hs1
  obtain ⟨hmain, hzero⟩ := modifiedPoincare_of_labels hMP lab hlab hind hα hα1 hatom hφ
    (EventuallyEq.of_eq hfφ) hf E hE hsum2
  exact ⟨_, _, tsum_nonneg fun _ => sq_nonneg _, hle2, hle1, hmain, hzero⟩

end Labels

end CurvatureVariance.Paper.Gain.Printed
