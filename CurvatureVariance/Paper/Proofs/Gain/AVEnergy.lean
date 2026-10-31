/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.Common
public import CurvatureVariance.Paper.Proofs.Responses.Exchange
import Mathlib.Algebra.Order.Chebyshev
import CurvatureVariance.Paper.Proofs.Moments.Basic
public import CurvatureVariance.Infra.Percolation.Lattice

/-!
# The Efron–Stein energy of the averaged minimum

The first bound of Lemma `lem:fewtranslates` starts from the Efron–Stein energy of the averaged
minimum `F̄ = V⁻¹ ∑_{v<V} F_v`, `V = ⌈K^{2/3}⌉`, under resampling of the blocks from the original
law. By Jensen's inequality over `v`, translation covariance (`F_v` is `F` at the translate by
`v L w e₂`, and the translation maps the blocks of a slab onto blocks of the same slab), and a
reindexing of the blocks, it is at most the Efron–Stein energy of `F` itself
(`tsum_esTerm_averagedMin_le`, `sum_tsum_esTerm_averagedMin_le`), which the second bound of equation
`eq:rewardmoment` bounds by `C K Q_n²`.
* `translate_resample`: translating commutes with resampling a set of edges.
* `esTerm_comp_translate`: the Efron–Stein term of `X ∘ θ_a` for `G` is that of `X` for `G − a`.
* `esTerm_averagedMin_le`: Jensen over the translates.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- Translation as a measurable equivalence of configurations. -/
noncomputable def translateEquiv (a : Vertex m) : Config m ≃ᵐ Config m where
  toFun := translate a
  invFun := translate (-a)
  left_inv ω := by simp [translate_translate]
  right_inv ω := by simp [translate_translate]
  measurable_toFun := measurable_translate a
  measurable_invFun := measurable_translate (-a)

/-- **Translating commutes with resampling**: `θ_a (ω^{G, ω'}) = (θ_a ω)^{G − a, θ_a ω'}`, where
`G − a` is the set of the edges whose translate by `a` lies in `G`. -/
theorem translate_resample (a : Vertex m) (G : Set (Sym2 (Vertex m))) (ω ω' : Config m) :
    translate a (resample G ω ω') =
      resample {s | Sym2.map (· + a) s ∈ G} (translate a ω) (translate a ω') := by
  funext e
  by_cases h : Sym2.map (· + a) e.1 ∈ G
  · have h' : ((Infra.Percolation.latticeShift a).mapEdgeSet e).1 ∈ G := h
    simp only [translate_apply, resample, h', ite_true, mem_ofPred_eq, h]
  · have h' : ((Infra.Percolation.latticeShift a).mapEdgeSet e).1 ∉ G := h
    simp only [translate_apply, resample, h', ite_false, mem_ofPred_eq, h]

/-- **The Efron–Stein term of a translated observable**: under a translation invariant law, the
term of `X ∘ θ_a` for the set `G` is that of `X` for `G − a`. -/
theorem esTerm_comp_translate {P : Measure (Config m)} {a : Vertex m}
    (ha : MeasurePreserving (translate a) P P) (X : Config m → ℝ) (G : Set (Sym2 (Vertex m))) :
    esTerm P (fun ω => X (translate a ω)) G = esTerm P X {s | Sym2.map (· + a) s ∈ G} := by
  have hemb : MeasurableEmbedding (translate a : Config m → Config m) :=
    (translateEquiv a).measurableEmbedding
  unfold esTerm
  simp only [translate_resample]
  have hin : ∀ ω, ∫⁻ ω', ENNReal.ofReal ((X (translate a ω) - X (resample
      {s | Sym2.map (· + a) s ∈ G} (translate a ω) (translate a ω'))) ^ 2) ∂P =
      ∫⁻ x', ENNReal.ofReal ((X (translate a ω) - X (resample
        {s | Sym2.map (· + a) s ∈ G} (translate a ω) x')) ^ 2) ∂P := fun ω =>
    ha.lintegral_comp_emb hemb (fun x' => ENNReal.ofReal ((X (translate a ω) - X (resample
      {s | Sym2.map (· + a) s ∈ G} (translate a ω) x')) ^ 2))
  simp_rw [hin]
  exact ha.lintegral_comp_emb hemb (fun x => ∫⁻ x', ENNReal.ofReal ((X x - X (resample
    {s | Sym2.map (· + a) s ∈ G} x x')) ^ 2) ∂P)

/-- The common translation `v L w e₂` of the minima `F_m` (the text before Lemma `lem:residual`) is
`(0, w (L (v e₂)))` in the form of `map_add_mem_block_iff`. -/
theorem translate_vector_eq (v L w : ℕ) :
    (((0 : ℤ), ((v * L * w : ℕ) : ℤ) • transverseUnit m) : Vertex m) =
      ((0 : ℤ), fun k => (w : ℤ) * ((L : ℤ) * (((v : ℤ) • transverseUnit m) k))) := by
  refine Prod.ext rfl ?_
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The translate of a block by `−v L w e₂` is the block `g − v e₂` (the set of edges whose
translate by `v L w e₂` lies in the block `g`). -/
theorem setOf_map_add_mem_block {n w L : ℕ} (hw : 0 < w) (t : EuclideanSpace ℝ (Fin m)) (i v : ℕ)
    (o g : Fin m → ℤ) :
    {s : Sym2 (Vertex m) | Sym2.map (· + (((0 : ℤ), ((v * L * w : ℕ) : ℤ) • transverseUnit m) :
        Vertex m)) s ∈ block n w L t i o g} =
      block n w L t i o (g - (v : ℤ) • transverseUnit m) := by
  ext s
  rw [mem_ofPred_eq, translate_vector_eq]
  have h := map_add_mem_block_iff (n := n) (L := L) hw t i o (g - (v : ℤ) • transverseUnit m)
    ((v : ℤ) • transverseUnit m) s
  rwa [sub_add_cancel] at h

/-- `numTranslates K = ⌈K^{2/3}⌉` is positive for `K ≥ 1`. -/
theorem numTranslates_pos {K : ℕ} (hK : 1 ≤ K) : 0 < numTranslates K := by
  unfold numTranslates
  rw [Nat.ceil_pos]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hK) _

/-- Jensen's inequality for the square of a difference of averages. -/
theorem ofReal_sq_sub_average_le {V : ℕ} (hV : 0 < V) (a b : ℕ → ℝ) :
    ENNReal.ofReal (((V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, a v -
        (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, b v) ^ 2) ≤
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ENNReal.ofReal ((a v - b v) ^ 2) := by
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range V) (f := fun v => a v - b v)
  rw [Finset.card_range] at hcs
  have hreal : ((V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, a v -
      (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, b v) ^ 2 ≤
      (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, (a v - b v) ^ 2 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, mul_pow]
    have h1 : ((V : ℝ)⁻¹) ^ 2 * (∑ v ∈ Finset.range V, (a v - b v)) ^ 2 ≤
        ((V : ℝ)⁻¹) ^ 2 * ((V : ℝ) * ∑ v ∈ Finset.range V, (a v - b v) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    refine h1.trans (le_of_eq ?_)
    field_simp
  refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hV0, ENNReal.ofReal_natCast,
    ENNReal.ofReal_sum_of_nonneg (fun v _ => sq_nonneg _)]

/-- **Jensen over an average**: the Efron–Stein term of an average `V⁻¹ ∑_{v<V} F_v` is at most
the average of those of the `F_v`. -/
theorem esTerm_average_le (P : Measure (Config m)) [SFinite P] (F : ℕ → Config m → ℝ)
    (hF : ∀ v, Measurable (F v)) {V : ℕ} (hV : 0 < V) (G : Set (Sym2 (Vertex m))) :
    esTerm P (fun ω => (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω) G ≤
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, esTerm P (F v) G := by
  have hjoint : ∀ v, Measurable fun p : Config m × Config m =>
      ENNReal.ofReal ((F v p.1 - F v (resample G p.1 p.2)) ^ 2) := fun v =>
    ((((hF v).comp measurable_fst).sub ((hF v).comp (Responses.measurable_resample G))).pow_const
      2).ennreal_ofReal
  have hinner : ∀ v ω, Measurable fun ω' =>
      ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) := fun v ω =>
    (hjoint v).comp (measurable_const.prodMk measurable_id)
  have hout : ∀ v, Measurable fun ω => ∫⁻ ω',
      ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) ∂P := fun v =>
    (hjoint v).lintegral_prod_right'
  have hpt : ∀ ω ω', ENNReal.ofReal (((V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v ω -
      (V : ℝ)⁻¹ * ∑ v ∈ Finset.range V, F v (resample G ω ω')) ^ 2) ≤
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) :=
    fun ω ω' => ofReal_sq_sub_average_le hV (fun v => F v ω) (fun v => F v (resample G ω ω'))
  unfold esTerm
  refine (lintegral_mono fun ω => lintegral_mono fun ω' => hpt ω ω').trans (le_of_eq ?_)
  have h1 : ∀ ω, ∫⁻ ω', (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V,
      ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) ∂P =
      (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ∫⁻ ω',
        ENNReal.ofReal ((F v ω - F v (resample G ω ω')) ^ 2) ∂P := fun ω => by
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun v _ => hinner v ω),
      lintegral_finsetSum _ fun v _ => hinner v ω]
  simp_rw [h1]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun v _ => hout v),
    lintegral_finsetSum _ fun v _ => hout v]

/-- **Jensen over the translates**: the Efron–Stein term of `F̄` for a set `G` is at most the
average over `v` of those of the `F_v`. -/
theorem esTerm_averagedMin_le {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 1 ≤ K) (A : ℝ)
    (L n ℓ : ℕ)
    (y : Fin m → ℤ) (G : Set (Sym2 (Vertex m))) :
    esTerm M.P (fun ω => averagedMin M K A L ω n ℓ y) G ≤
      (numTranslates K : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range (numTranslates K),
        esTerm M.P (fun ω => translatedMin M ω n K ℓ y
          (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m)) G :=
  haveI := hM.probP
  esTerm_average_le M.P (fun v ω => translatedMin M ω n K ℓ y
    (((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m))
    (fun _ => measurable_translatedMin M n K ℓ y _) (numTranslates_pos hK) G

/-- **The Efron–Stein energy of a slab for `F̄` is at most that for `F`** (the proof of Lemma
`lem:fewtranslates`): summed over the blocks `g` of slab `i` (offset `o`), the Efron–Stein terms of
the averaged minimum are at most those of the minimum `F`. -/
theorem tsum_esTerm_averagedMin_le {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 1 ≤ K)
    {A : ℝ} {L n : ℕ} (hw : 0 < wInt M K A n) (ℓ : ℕ) (y : Fin m → ℤ) (i : ℕ)
    (o : Fin m → ℤ) :
    ∑' g : Fin m → ℤ, esTerm M.P (fun ω => averagedMin M K A L ω n ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) i o g) ≤
      ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) i o g) := by
  set V := numTranslates K
  have hV := numTranslates_pos hK
  set w := wInt M K A n
  set t := targetSlope ℓ y
  set S := ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y) (block n w L t i o g)
  -- each translate has the energy of `F`
  have htr : ∀ v : ℕ, ∑' g : Fin m → ℤ, esTerm M.P (fun ω => translatedMin M ω n K ℓ y
      (((v * L * w : ℕ) : ℤ) • transverseUnit m)) (block n w L t i o g) = S := by
    intro v
    have hmp := Moments.standing_measurePreserving_translate hM
      (((0 : ℤ), ((v * L * w : ℕ) : ℤ) • transverseUnit m) : Vertex m)
    simp_rw [translatedMin_eq_targetMin]
    simp_rw [esTerm_comp_translate hmp (fun ω => targetMin M ω n K ℓ y),
      setOf_map_add_mem_block hw t i v o]
    exact (Equiv.subRight ((v : ℤ) • transverseUnit m)).tsum_eq
      (fun g => esTerm M.P (fun ω => targetMin M ω n K ℓ y) (block n w L t i o g))
  calc ∑' g, esTerm M.P (fun ω => averagedMin M K A L ω n ℓ y) (block n w L t i o g)
      ≤ ∑' g, (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, esTerm M.P (fun ω => translatedMin M ω n K ℓ y
          (((v * L * w : ℕ) : ℤ) • transverseUnit m)) (block n w L t i o g) :=
        ENNReal.tsum_le_tsum fun g => esTerm_averagedMin_le hM hK A L n ℓ y _
    _ = (V : ℝ≥0∞)⁻¹ * ∑ v ∈ Finset.range V, ∑' g, esTerm M.P (fun ω => translatedMin M ω n K ℓ y
          (((v * L * w : ℕ) : ℤ) • transverseUnit m)) (block n w L t i o g) := by
        rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = S := by
        simp_rw [htr]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast hV.ne') (ENNReal.natCast_ne_top V), one_mul]

/-- **The Efron–Stein energy of `F̄` is at most that of `F`**, summed over the blocks of the `K`
slabs with offsets `o` (the first bound of Lemma `lem:fewtranslates` then follows from the second
bound of equation `eq:rewardmoment`). -/
theorem sum_tsum_esTerm_averagedMin_le {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 1 ≤ K)
    {A : ℝ} {L n : ℕ} (hw : 0 < wInt M K A n) (ℓ : ℕ) (y : Fin m → ℤ) (o : ℕ → Fin m → ℤ) :
    ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ, esTerm M.P
        (fun ω => averagedMin M K A L ω n ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) ≤
      ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ, esTerm M.P (fun ω => targetMin M ω n K ℓ y)
        (block n (wInt M K A n) L (targetSlope ℓ y) (i + 1) (o (i + 1)) g) :=
  Finset.sum_le_sum fun i _ => tsum_esTerm_averagedMin_le hM hK hw ℓ y (i + 1) (o (i + 1))

end CurvatureVariance.Paper.Gain
