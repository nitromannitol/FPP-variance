/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.TubeGeodesics
import CurvatureVariance.Paper.Proofs.Responses.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayMoments

/-!
# Exchangeable replacements: laws, block suprema and the cell bound

Basic facts about an exchangeable replacement of the blocks (`IsSlabReplacement`, the resampling of
[AB26, Section 6] that Section `sec:gain` uses) and the block sums `rewardSum` (the variables
`Y_i(j,k)` defined there):

* `IsSlabReplacement.map_new`: the new weights have the original law (in the proof of
  [AB26, Lemma 6.1], "`ω^G` has the law of `ω`"); `IsSlabReplacement.ae_old`, `ae_new`: almost sure
  properties of the law transfer to the old and new weights.
* `blockSup`: the block supremum `sup_{I × I'} (D_i(ω') − D_i(ω))_+`, and `rewardSum_eq`: the
  block sum is `Q_n^{-2} ∑_G blockSup²`; `measurable_blockSup`, `measurable_rewardSum`.
* `blockSup_le_of_abs_sub_le`: `sup (D_i^G − D_i)_+ ≤ X^G + X` when both are within `X^G`, `X` of
  a common centring on `I × I'`; `blockSup_eq_zero_of_disjoint`: the supremum vanishes for a block
  that misses a set of fine cubes containing those of the old geodesics (the text before Lemma
  `lem:blocks`).
* `tsum_sq_le_tsum_indicator_blockOf`: the count over cells instead of blocks in the proof of
  Lemma `lem:blocks` — a sum over blocks meeting `T` is at most a sum over the fine cubes of `T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Laws of the old and new weights -/

section Replacement

variable {M : Model m} {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {n K w L : ℕ}
  {t : EuclideanSpace ℝ (Fin m)} {o : ℕ → Fin m → ℤ} {old : Ω → Config m}
  {new : ℕ → (Fin m → ℤ) → Ω → Config m}

/-- **The new weights have the original law**: the second marginal of the exchangeable pair
`(old, new i g)` is the first one. -/
theorem IsSlabReplacement.map_new (h : IsSlabReplacement M Pr n K w L t o old new) (i : ℕ)
    (g : Fin m → ℤ) : Pr.map (new i g) = M.P := by
  have h1 : (Pr.map (fun ω => (old ω, new i g ω))).map Prod.snd = Pr.map (new i g) := by
    rw [Measure.map_map measurable_snd (h.measurable_old.prodMk (h.measurable_new i g))]
    rfl
  have h2 : (Pr.map (fun ω => (new i g ω, old ω))).map Prod.snd = Pr.map old := by
    rw [Measure.map_map measurable_snd ((h.measurable_new i g).prodMk h.measurable_old)]
    rfl
  rw [← h1, h.exchangeable i g, h2, h.law_old]

/-- An almost sure property of the law holds for the old weights. -/
theorem IsSlabReplacement.ae_old (h : IsSlabReplacement M Pr n K w L t o old new)
    {p : Config m → Prop} (hp : ∀ᵐ ω ∂M.P, p ω) : ∀ᵐ ω ∂Pr, p (old ω) := by
  rw [← h.law_old] at hp
  exact ae_of_ae_map h.measurable_old.aemeasurable hp

/-- An almost sure property of the law holds for the new weights of every block. -/
theorem IsSlabReplacement.ae_new (h : IsSlabReplacement M Pr n K w L t o old new)
    {p : Config m → Prop} (hp : ∀ᵐ ω ∂M.P, p ω) : ∀ᵐ ω ∂Pr, ∀ i g, p (new i g ω) := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro g
  rw [← IsSlabReplacement.map_new h i g] at hp
  exact ae_of_ae_map (h.measurable_new i g).aemeasurable hp

/-- The `L^p` norm of a function of the new weights is that under the law. -/
theorem IsSlabReplacement.eLpNorm_comp_new (h : IsSlabReplacement M Pr n K w L t o old new)
    {f : Config m → ℝ≥0∞} (hf : Measurable f) (p : ℝ≥0∞) (i : ℕ) (g : Fin m → ℤ) :
    eLpNorm (fun ω => f (new i g ω)) p Pr = eLpNorm f p M.P := by
  rw [← IsSlabReplacement.map_new h i g, eLpNorm_map_measure hf.aestronglyMeasurable
    (h.measurable_new i g).aemeasurable]
  rfl

/-- The `L^p` norm of a function of the old weights is that under the law. -/
theorem IsSlabReplacement.eLpNorm_comp_old (h : IsSlabReplacement M Pr n K w L t o old new)
    {f : Config m → ℝ≥0∞} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (fun ω => f (old ω)) p Pr = eLpNorm f p M.P := by
  rw [← h.law_old, eLpNorm_map_measure hf.aestronglyMeasurable h.measurable_old.aemeasurable]
  rfl

/-- The integral of a function of the old weights is that under the law. -/
theorem IsSlabReplacement.lintegral_comp_old (h : IsSlabReplacement M Pr n K w L t o old new)
    {f : Config m → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (old ω) ∂Pr = ∫⁻ ω, f ω ∂M.P := by
  rw [← h.law_old, lintegral_map hf h.measurable_old]

end Replacement

/-! ### Block suprema -/

/-- The block supremum `sup_{u ∈ I, v ∈ I'} (D_i(ω')(u, v) − D_i(ω)(u, v))_+` for slab `i`, the slab
`[(i−1)n, in]`. -/
noncomputable def blockSup (n i : ℕ) (I I' : Set (Vertex m)) (ω ω' : Config m) : ℝ≥0∞ :=
  ⨆ (u : Vertex m) (_ : u ∈ I) (v : Vertex m) (_ : v ∈ I'),
    ENNReal.ofReal (slabTimeReal ω' (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v -
      slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v)

/-- The block sum is `Q_n^{-2}` times the sum of the squared block suprema. -/
theorem rewardSum_eq (M : Model m) (K : ℕ) (A : ℝ) {Ω : Type*} (n : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (old : Ω → Config m) (new : ℕ → (Fin m → ℤ) → Ω → Config m)
    (i : ℕ) (j k : Fin m → ℤ) (ω : Ω) :
    rewardSum M K A n t old new i j k ω = (ENNReal.ofReal (Q M K A n ^ 2))⁻¹ *
      ∑' g : Fin m → ℤ, blockSup n i (rowCube n (wInt M K A n) t ((i : ℤ) - 1) j)
        (rowCube n (wInt M K A n) t i k) (old ω) (new i g ω) ^ 2 :=
  rfl

/-- The block supremum is jointly measurable in the old and the new weights. -/
theorem measurable_blockSup (n i : ℕ) (I I' : Set (Vertex m)) :
    Measurable fun p : Config m × Config m => blockSup n i I I' p.1 p.2 := by
  unfold blockSup
  refine Measurable.iSup fun u => Measurable.iSup_Prop _ (Measurable.iSup fun v =>
    Measurable.iSup_Prop _ ?_)
  exact (((Moments.ExpArray.measurable_slabTimeReal _ _ u v).comp measurable_snd).sub
    ((Moments.ExpArray.measurable_slabTimeReal _ _ u v).comp measurable_fst)).ennreal_ofReal

/-- The block sum is measurable when the old and new weights are. -/
theorem measurable_rewardSum (M : Model m) (K : ℕ) (A : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (t : EuclideanSpace ℝ (Fin m)) {old : Ω → Config m}
    {new : ℕ → (Fin m → ℤ) → Ω → Config m} (hold : Measurable old)
    (hnew : ∀ i g, Measurable (new i g)) (i : ℕ) (j k : Fin m → ℤ) :
    Measurable fun ω => rewardSum M K A n t old new i j k ω := by
  simp only [rewardSum_eq]
  refine measurable_const.mul (Measurable.tsum fun g => ?_)
  exact ((measurable_blockSup n i _ _).comp (hold.prodMk (hnew i g))).pow_const 2

/-- **The block supremum is at most `X' + X`** when, on `I × I'`, the new and old slab passage times
are within `Q X'` and `Q X` of a common centring `c` (the proof of [AB26, Lemma 6.1]). -/
theorem blockSup_le_of_abs_sub_le {n i : ℕ} {I I' : Set (Vertex m)} {ω ω' : Config m}
    {c : Vertex m → Vertex m → ℝ} {Q X X' : ℝ} (hQ : 0 < Q)
    (h : ∀ u ∈ I, ∀ v ∈ I', |slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - c u v| ≤
      Q * X)
    (h' : ∀ u ∈ I, ∀ v ∈ I', |slabTimeReal ω' (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - c u v| ≤
      Q * X') :
    (ENNReal.ofReal Q)⁻¹ * blockSup n i I I' ω ω' ≤ ENNReal.ofReal X' + ENNReal.ofReal X := by
  have hQ' : ENNReal.ofReal Q ≠ 0 := by simpa using hQ
  rw [mul_comm, ← div_eq_mul_inv, ENNReal.div_le_iff hQ' ENNReal.ofReal_ne_top]
  refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
  have h1 := h u hu v hv
  have h2 := h' u hu v hv
  have hd : slabTimeReal ω' (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v -
      slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v ≤ Q * X' + Q * X := by
    have := abs_le.1 h1
    have := abs_le.1 h2
    linarith
  calc ENNReal.ofReal (slabTimeReal ω' (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v -
        slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v)
      ≤ ENNReal.ofReal (Q * X' + Q * X) := ENNReal.ofReal_le_ofReal hd
    _ ≤ ENNReal.ofReal (Q * X') + ENNReal.ofReal (Q * X) := ENNReal.ofReal_add_le
    _ = (ENNReal.ofReal X' + ENNReal.ofReal X) * ENNReal.ofReal Q := by
      rw [ENNReal.ofReal_mul hQ.le, ENNReal.ofReal_mul hQ.le]
      ring

/-- **A block missing the tube has zero supremum** (the text before Lemma `lem:blocks`: the term of
`G` in `Y_i(j,k)` vanishes unless a cell of `G` is near `[j, k]`): if old slab geodesics exist
between all pairs of `I × I'` and their edges lie in fine cubes of `T`, and the block `g` has no
fine cube in `T`, then the block supremum of a configuration `ω'` agreeing with `ω` off the block
vanishes. -/
theorem blockSup_eq_zero_of_disjoint {n w L i : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {o g : Fin m → ℤ} {I I' : Set (Vertex m)} {ω ω' : Config m} {T : Set (Fin m → ℤ)}
    (hgeo : ∀ u ∈ I, ∀ v ∈ I', ∃ γ : (latticeGraph m).Walk u v,
      IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ)
    (htube : ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v,
      IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
      ∀ e ∈ γ.edges, fineIndex w t (edgeMid e) ∈ T)
    (hdisj : Disjoint (blockIndices L o g) T)
    (hω' : ∀ e : Edge m, e.1 ∉ block n w L t i o g → ω' e = ω e) :
    blockSup n i I I' ω ω' = 0 := by
  refine le_antisymm (iSup₂_le fun u hu => iSup₂_le fun v hv => le_of_eq ?_) bot_le
  obtain ⟨γ, hγ⟩ := hgeo u hu v hv
  have hle := slabTime_le_of_disjoint_tube ⟨γ, hγ⟩ (htube u hu v hv) hdisj hω'
  exact ENNReal.ofReal_eq_zero.2 (sub_nonpos.2
    (ENNReal.toReal_mono (slabTime_ne_top_of_isSlabGeodesic hγ) hle))

/-- **Counting fine cubes instead of blocks** (the proof of Lemma `lem:blocks`): if `S g ≤ U g` for
every block and `S g = 0` for the blocks with no fine cube in `T`, then
`∑_g S_g² ≤ ∑_{j' ∈ T} U_{G(j')}²`, `G(j')` the block of the fine cube `j'`. -/
theorem tsum_sq_le_tsum_indicator_blockOf {L : ℕ} (hL : 1 ≤ L) (o : Fin m → ℤ)
    (T : Set (Fin m → ℤ)) (S U : (Fin m → ℤ) → ℝ≥0∞) (hSU : ∀ g, S g ≤ U g)
    (hS0 : ∀ g, Disjoint (blockIndices L o g) T → S g = 0) :
    ∑' g, S g ^ 2 ≤ ∑' j', T.indicator (fun j' => U (blockOf L o j') ^ 2) j' := by
  set F : (Fin m → ℤ) → ℝ≥0∞ := fun j' => T.indicator (fun j' => U (blockOf L o j') ^ 2) j'
    with hF
  have hfib : ∀ j', (∑' g : Fin m → ℤ, if blockOf L o j' = g then F j' else 0) = F j' :=
    fun j' => by simp
  calc ∑' g, S g ^ 2
      ≤ ∑' g : Fin m → ℤ, ∑' j' : Fin m → ℤ, if blockOf L o j' = g then F j' else 0 := by
        refine ENNReal.tsum_le_tsum fun g => ?_
        by_cases hg : Disjoint (blockIndices L o g) T
        · rw [hS0 g hg]
          simp
        · obtain ⟨j', hj'g, hj'T⟩ := Set.not_disjoint_iff.1 hg
          have hgi := (mem_blockIndices_iff_blockOf_eq hL o g j').1 hj'g
          refine le_trans ?_ (ENNReal.le_tsum j')
          simp only [hgi, ite_true, hF, Set.indicator_of_mem hj'T]
          exact pow_le_pow_left₀ bot_le (hSU g) 2
    _ = ∑' j' : Fin m → ℤ, ∑' g : Fin m → ℤ,
          if blockOf L o j' = g then F j' else 0 := ENNReal.tsum_comm
    _ = ∑' j', F j' := tsum_congr hfib

end CurvatureVariance.Paper.Gain
