/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.ChainArrays
public import IsotropicVariance.Paper.Proofs.SmallMean.PairMoments

/-!
# The moment bound of one array entry

The second paragraph of the proof of Lemma `lem:smallmean`.

For a pair of cubes `I = I_i(j)`, `I' = I_{i+1}(k)` with `W|k − j| ≤ s/2`, the fluctuation
`X_i(j, k)` of the slab passage time `D` of the slab `i` satisfies
`E X_i(j,k)^p ≤ 3^{p−1}(n_T² A₁ + 2η^p)`, `p = 4d` (`lintegral_fluct_pow_le_of_pair`). Here:
- `n_T` is the size of a net of the unit cube of radius `h`, so the mesh of `I × I'` has at most
  `n_T²` points, at spacing `hW`;
- `A₁ = λ^{p−2}·5δ + C₈/λ^p` bounds the `p`-th moments at the mesh points, by interpolating
  between the second moment and the `2p`-th moment;
- `η` is the modulus bound, equation `eq:modulus`, at scale `hW`.

The second moment: `Var D ≤ 2 Var T + 12C²θ⁴ ≤ 5δQ²`, by isotropy, the variance hypothesis and
the slab comparison. The `2p`-th moment: `C₈ Q^{2p}`, from the profile bound, equation
`eq:profiles`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.Paper.Proofs.SmallMean

open Infra.Slab

variable {m : ℕ}

/-- The constant of the `2p`-th moments. -/
noncomputable def momentConst (p : ℕ) (Cpr : ℝ) : ℝ :=
  2 ^ (2 * p - 1) * (2 * (1 + ((2 * p).factorial : ℝ)) + 4 ^ (2 * p)) * Cpr ^ (2 * p)

theorem momentConst_nonneg (p : ℕ) {Cpr : ℝ} (hC : 0 ≤ Cpr) : 0 ≤ momentConst p Cpr := by
  unfold momentConst
  positivity

/-- **The moment bound of one array entry.** -/
theorem lintegral_fluct_pow_le_of_pair (hm : 1 ≤ m) (X : Setting m) {b : ℝ}
    (hb : X.IsUpperBound b) {s W Q : ℝ} (hs : 0 < s) (hW : 0 < W) (hQ : 0 < Q)
    (hWs : W * (1 + Real.sqrt m) ≤ s / 4) {i : ℕ} {j k : Fin m → ℤ}
    (hjk : W * zNorm (k - j) ≤ s / 2)
    {V : X.Ω → Pt m × Pt m → ℝ} (hVm : Measurable (Function.uncurry V))
    (hV : ∀ᵐ ω ∂X.P, ∀ u ∈ (chainSlab s 0 i).set, ∀ v ∈ (chainSlab s 0 i).set,
      V ω (u, v) = X.slabTime b (chainSlab s 0 i) ω u v)
    {q : ℕ → Pt m × Pt m} (hq : ∀ n, q n ∈ gridCube s W 0 i j ×ˢ gridCube s W 0 (i + 1) k)
    {h : ℝ} {T₀ : Finset (EuclideanSpace ℝ (Fin m))}
    (hT₀ : ∀ t ∈ T₀, t ∈ unitCube m) (hnet : ∀ y ∈ unitCube m, ∃ t ∈ T₀, dist y t ≤ h)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hvar : ∀ r, s ≤ r → r ≤ 2 * s → variance (X.TRV r) X.P ≤ 2 * δ * Q ^ 2)
    {S : X.Ω → ℝ} {Csl θ : ℝ} (hCsl : 0 ≤ Csl) (hθ : 0 < θ) (hS : Cited.IsOs X.P 2 θ S)
    (hS0 : ∀ ω, 0 ≤ S ω)
    (hDT : ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 (i + 1) k, ∀ ω,
      0 ≤ X.slabTime b (chainSlab s 0 i) ω u v - X.passTime ω u v ∧
        X.slabTime b (chainSlab s 0 i) ω u v - X.passTime ω u v ≤ Csl * S ω ^ 2)
    (herr : 12 * Csl ^ 2 * θ ^ 4 ≤ δ * Q ^ 2)
    {Cpr : ℝ} (hCpr : 0 < Cpr)
    (hprof : ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 (i + 1) k,
      Cited.IsOs X.P 1 (Cpr * Q) fun ω => |X.slabTime b (chainSlab s 0 i) ω u v - dist u v|)
    {η : ℝ} (hη : 0 ≤ η)
    (hmod : ∫⁻ ω, ENNReal.ofReal (Contracts.modulusSup (X.slabTime b (chainSlab s 0 i) ω)
        (gridCube s W 0 i j) (gridCube s W 0 (i + 1) k) (h * W)) ^ (2 * (4 * (m + 1)) : ℝ) ∂X.P ≤
      ENNReal.ofReal (η * Q) ^ (2 * (4 * (m + 1)) : ℝ))
    {l : ℝ} (hl : 0 < l) :
    ∫⁻ ω, ENNReal.ofReal (fluct (V ω)
        (fun x => ∫ ω', X.slabTime b (chainSlab s 0 i) ω' x.1 x.2 ∂X.P) q Q ^ (4 * (m + 1))) ∂X.P ≤
      ENNReal.ofReal (3 ^ (4 * (m + 1) - 1)) *
        (ENNReal.ofReal ((T₀.card : ℝ) ^ 2 * (l ^ (4 * (m + 1) - 2) * (5 * δ) +
            momentConst (4 * (m + 1)) Cpr / l ^ (4 * (m + 1)))) +
          ENNReal.ofReal (η ^ (4 * (m + 1))) + ENNReal.ofReal (η ^ (4 * (m + 1)))) := by
  classical
  set p : ℕ := 4 * (m + 1) with hpdef
  have hp1 : 1 ≤ p := by omega
  have hp2 : 2 ≤ p := by omega
  set I := gridCube s W 0 i j with hIdef
  set I' := gridCube s W 0 (i + 1) k with hI'def
  set D : X.Ω → Pt m → Pt m → ℝ := fun ω => X.slabTime b (chainSlab s 0 i) ω with hDdef
  set e : Pt m × Pt m → ℝ := fun x => ∫ ω', D ω' x.1 x.2 ∂X.P with hedef
  have hjk' : W * (zNorm (k - j) + Real.sqrt m) ≤ s := by linarith only [hjk, hWs, hW, hs]
  have hmemI : ∀ u ∈ I, u ∈ (chainSlab s 0 i).set := fun u hu =>
    gridCube_subset_set hs.le W i j hu
  have hmemI' : ∀ v ∈ I', v ∈ (chainSlab s 0 i).set := fun v hv =>
    gridCube_succ_subset_set hs.le W i k hv
  have hb0 : 0 ≤ b := by
    obtain ⟨ω⟩ : Nonempty X.Ω := nonempty_of_isProbabilityMeasure X.P
    exact upperBound_nonneg X hb ω
  have hdist : ∀ u ∈ I, ∀ v ∈ I', dist u v ≤ 2 * s := fun u hu v hv =>
    dist_gridCube_le hs.le hW.le hu hv hjk'
  have hDle : ∀ ω, ∀ u ∈ I, ∀ v ∈ I', 0 ≤ D ω u v ∧ D ω u v ≤ b * (2 * s) := fun ω u hu v hv =>
    ⟨slabTime_nonneg X b _ ω u v, (slabTime_le_mul_dist X hb _ ω (hmemI u hu) (hmemI' v hv)).trans
      (mul_le_mul_of_nonneg_left (hdist u hu v hv) hb0)⟩
  have hDint : ∀ x ∈ I ×ˢ I', Integrable (fun ω => D ω x.1 x.2) X.P := by
    intro x hx
    refine Integrable.mono' (integrable_const (b * (2 * s)))
      (aemeasurable_slabTime X hb _ x.1 x.2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hDle ω x.1 hx.1 x.2 hx.2).1]
    exact (hDle ω x.1 hx.1 x.2 hx.2).2
  have hDmem : ∀ x ∈ I ×ˢ I', MemLp (fun ω => D ω x.1 x.2) 2 X.P := by
    intro x hx
    refine MemLp.of_bound (aemeasurable_slabTime X hb _ x.1 x.2).aestronglyMeasurable
      (b * (2 * s)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hDle ω x.1 hx.1 x.2 hx.2).1]
    exact (hDle ω x.1 hx.1 x.2 hx.2).2
  -- the mesh
  set G : Finset (Pt m × Pt m) := (T₀ ×ˢ T₀).image
    fun tt => (meshPt s W i j tt.1, meshPt s W (i + 1) k tt.2) with hGdef
  have hGcard : (G.card : ℝ) ≤ (T₀.card : ℝ) ^ 2 := by
    have := Finset.card_image_le (s := T₀ ×ˢ T₀)
      (f := fun tt => (meshPt s W i j tt.1, meshPt s W (i + 1) k tt.2))
    rw [Finset.card_product] at this
    rw [sq]
    exact_mod_cast this
  have hG : ∀ g ∈ G, g ∈ I ×ˢ I' := by
    intro g hg
    obtain ⟨tt, htt, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 htt
    exact ⟨meshPt_mem hW.le i j (hT₀ _ h1), by
      simpa using meshPt_mem (s := s) hW.le (i + 1) k (hT₀ _ h2)⟩
  have hcov : ∀ x ∈ I ×ˢ I', ∃ g ∈ G, dist x.1 g.1 ≤ h * W ∧ dist x.2 g.2 ≤ h * W := by
    intro x hx
    obtain ⟨t₁, ht₁, hd₁⟩ := exists_meshPt_near hW hnet hx.1
    obtain ⟨t₂, ht₂, hd₂⟩ := exists_meshPt_near (i := i + 1) hW hnet hx.2
    refine ⟨(meshPt s W i j t₁, meshPt s W (i + 1) k t₂),
      Finset.mem_image.2 ⟨(t₁, t₂), Finset.mem_product.2 ⟨ht₁, ht₂⟩, rfl⟩, ?_, ?_⟩
    · simpa [mul_comm] using hd₁
    · simpa [mul_comm] using hd₂
  -- the bound of the modulus terms
  have hBd : ∀ ω, ∀ u ∈ I, ∀ u₁ ∈ I, ∀ v ∈ I', ∀ v₁ ∈ I',
      |D ω u v - D ω u₁ v₁ - dist u v + dist u₁ v₁| ≤ 4 * b * s + 4 * s := by
    intro ω u hu u₁ hu₁ v hv v₁ hv₁
    have h1 := hDle ω u hu v hv
    have h2 := hDle ω u₁ hu₁ v₁ hv₁
    have h3 := hdist u hu v hv
    have h4 := hdist u₁ hu₁ v₁ hv₁
    have h5 := dist_nonneg (x := u) (y := v)
    have h6 := dist_nonneg (x := u₁) (y := v₁)
    have hbs : 0 ≤ b * s := mul_nonneg hb0 hs.le
    rw [abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3, h4, h5, h6, hbs, hs]
  -- the moments at the mesh points
  have hmom : ∀ g ∈ G, ∫⁻ ω, ENNReal.ofReal (|D ω g.1 g.2 - e g| ^ p) ∂X.P ≤
      ENNReal.ofReal ((l ^ (p - 2) * (5 * δ) + momentConst p Cpr / l ^ p) * Q ^ p) := by
    intro g hg
    have hgI := hG g hg
    have hint := hDint g hgI
    refine lintegral_abs_pow_le_of_moments ((hint.aemeasurable).sub_const _) hQ hl hp2 ?_ ?_
    · -- the second moment
      have hT : MemLp (fun ω => X.passTime ω g.1 g.2) 2 X.P := by
        obtain ⟨a', b', ha', hab'⟩ := Infra.TimeConstant.setting_passTime_bounds X
        refine MemLp.of_bound (Infra.TimeConstant.aestronglyMeasurable_passTime X g.1 g.2)
          (|b'| * dist g.1 g.2) (Eventually.of_forall fun ω => ?_)
        have hh := hab' ω g.1 g.2
        rw [Real.norm_eq_abs, abs_of_nonneg ((mul_nonneg ha'.le dist_nonneg).trans hh.1)]
        exact hh.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) dist_nonneg)
      have hcomp := evariance_le_of_comparison (hDmem g hgI) hT hCsl hθ hS hS0
        (fun ω => hDT g.1 hgI.1 g.2 hgI.2 ω)
      have hvarT : variance (fun ω => X.passTime ω g.1 g.2) X.P ≤ 2 * δ * Q ^ 2 := by
        have heq : variance (fun ω => X.passTime ω g.1 g.2) X.P =
            variance (X.TRV (dist g.1 g.2)) X.P := by
          rw [variance, variance, evariance_passTime_eq hm X g.1 g.2]
        rw [heq]
        exact hvar _ (le_dist_gridCube hs.le hgI.1 hgI.2) (hdist _ hgI.1 _ hgI.2)
      have hev : ∫⁻ ω, ENNReal.ofReal ((D ω g.1 g.2 - e g) ^ 2) ∂X.P =
          evariance (fun ω => D ω g.1 g.2) X.P := by
        rw [evariance_eq_lintegral_ofReal]
      rw [hev]
      refine hcomp.trans (ENNReal.ofReal_le_ofReal ?_)
      linarith only [hvarT, herr]
    · -- the `2p`-th moment
      have h2p := lintegral_abs_sub_integral_pow_le hint (mul_pos hCpr hQ)
        (hprof g.1 hgI.1 g.2 hgI.2) (q := 2 * p) (by omega)
      refine h2p.trans (le_of_eq ?_)
      congr 1
      rw [momentConst, mul_pow]
      ring
  -- the modulus
  have hmod' : ∫⁻ ω, ENNReal.ofReal (Contracts.modulusSup (D ω) I I' (h * W)) ^ (2 * p : ℝ) ∂X.P ≤
      ENNReal.ofReal (η * Q) ^ (2 * p : ℝ) := by
    have hexp : (2 * (p : ℝ)) = (2 * (4 * (m + 1)) : ℝ) := by rw [hpdef]; push_cast; ring
    rw [hexp]
    exact hmod
  have hpair := lintegral_fluct_pow_le hVm (I := I) (I' := I')
    (hV.mono fun ω hω u hu v hv => hω u (hmemI u hu) v (hmemI' v hv))
    (e := e) (fun x _ => rfl) hDint hq hG hcov hBd hQ hp1 hη hmom hmod'
  refine hpair.trans (mul_le_mul' le_rfl (add_le_add (add_le_add ?_ le_rfl) le_rfl))
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hGcard ?_)
  exact add_nonneg (mul_nonneg (pow_nonneg hl.le _) (mul_nonneg (by norm_num) hδ))
    (div_nonneg (momentConst_nonneg p hCpr.le) (pow_nonneg hl.le _))

end IsotropicVariance.Paper.Proofs.SmallMean
