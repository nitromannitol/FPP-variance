/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Inputs
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.Gain.LabelsFamily
public import CurvatureVariance.Paper.Proofs.Gain.LabelsParams
import CurvatureVariance.Paper.Proofs.Gain.FAClip
import CurvatureVariance.Paper.Proofs.Gain.FALarge
import CurvatureVariance.Paper.Proofs.Gain.FAMesh
import CurvatureVariance.Paper.Proofs.Gain.FAMoments
import CurvatureVariance.Paper.Proofs.Gain.TubeGeodesics
import CurvatureVariance.Paper.Proofs.Moments.WidthMargin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:labels`

The proof of Lemma `lem:labels` in the paper.

* `exists_labelError_of_inputs`: in one block, from the contracts already instantiated. The union
  bound (equation `eq:union`) over the at most `(L+1)^{2(d−1)}` pairs of cubes covering `Γ_G` gives
  `S`, the bound of `|D − μ|` on `Γ_G` of `O₁(C log(2+L) Q_n)` (Proposition `prop:profiles`), which
  is both the cancelled variable of the Hölder step and the fluctuation in
  `sup_{Γ_G}|Φ| ≤ CL² + S/Q_n`.
* `labelsStatement_of`: the contract `LabelsStatement` from the premises of the edge `labels`.
  The functions of `L`: `η = 1/(L+1)`; `h(L)` of Lemma `lem:modulus` at `b = 2L + 2` and `η` (the
  paper has `b = 2L`, and the faces lie in a pair of cubes of both sizes, `isCubePair_blockCubes`);
  the paper's `g`, taken as `g(L) = min(h(L), η)`, which is the rounding step `ξ`; the mesh step
  `τ(L)` with `(d−1) w τ ≤ g W_n`; the clipping level `L⁴`; `α_L`; and
  `ω_L = ε₁ + 2η + (a − L⁴/2)₊ + ε₃ + g + η`. None of them depends on `K`, `N`, `A`, the target, the
  subgradient, the slab, the offset or the block.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Scales -/

/-- The arithmetic of `label_scale_bounds`, over abstract reals. -/
private theorem label_scale_aux {K X N n : ℝ} (hK : 1 ≤ K) (hX : 1 ≤ X) (hN0 : 0 ≤ N)
    (hN : 1296 * K ^ 2 * X ≤ N) (hn : N / (9 * K) ≤ n) :
    16 * X ≤ n ∧ Real.sqrt N ≤ n ∧ 2 ≤ n := by
  have h9K : 0 < 9 * K := by linarith only [hK]
  have hNK : 144 * K * X ≤ N / (9 * K) := by
    rw [le_div_iff₀ h9K]
    have e : 144 * K * X * (9 * K) = 1296 * K ^ 2 * X := by ring
    rw [e]
    exact hN
  have hKX : X ≤ K * X := le_mul_of_one_le_left (by linarith only [hX]) hK
  have h16 : 16 * X ≤ n := by linarith only [hNK, hn, hKX, hX]
  refine ⟨h16, ?_, by linarith only [h16, hX]⟩
  have hs : 9 * K ≤ Real.sqrt N := by
    rw [Real.le_sqrt h9K.le hN0]
    have h1 : K ^ 2 ≤ K ^ 2 * X := le_mul_of_one_le_right (sq_nonneg K) hX
    have e : (9 * K) ^ 2 = 81 * K ^ 2 := by ring
    rw [e]
    linarith only [hN, h1, sq_nonneg K]
  have hsq := Real.mul_self_sqrt hN0
  refine le_trans ?_ hn
  rw [le_div_iff₀ h9K]
  have := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg N)
  linarith only [this, hsq]

/-- The sizes for equation `eq:support`, over abstract reals. -/
private theorem mul_div_le_of_W_le {a b w W r x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r)
    (hx : 0 < x) (hw : w ≤ 2 * W) (hW : W ≤ r / (2 * (a + 1) * (b + 1)) * x) :
    a * (b * w) / x ≤ r := by
  have ha1 : 0 < a + 1 := by linarith only [ha]
  have hb1 : 0 < b + 1 := by linarith only [hb]
  rw [div_le_iff₀ hx]
  have h1 : a * (b * w) ≤ a * (b * (2 * (r / (2 * (a + 1) * (b + 1)) * x))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith only [hw, hW]) hb) ha
  have h2 : a * (b * (2 * (r / (2 * (a + 1) * (b + 1)) * x))) =
      (a / (a + 1)) * (b / (b + 1)) * (r * x) := by
    field_simp
  have a1 : a / (a + 1) ≤ 1 := by
    rw [div_le_one ha1]
    linarith only
  have a2 : b / (b + 1) ≤ 1 := by
    rw [div_le_one hb1]
    linarith only
  have h3 : (a / (a + 1)) * (b / (b + 1)) ≤ 1 * 1 :=
    mul_le_mul a1 a2 (div_nonneg hb hb1.le) zero_le_one
  rw [mul_one] at h3
  calc a * (b * w)
      ≤ (a / (a + 1)) * (b / (b + 1)) * (r * x) := h1.trans_eq h2
    _ ≤ 1 * (r * x) := mul_le_mul_of_nonneg_right h3 (mul_pos hr hx).le
    _ = r * x := one_mul _

/-- From half of `e` to `e`, `3e/2` and `3e`. -/
private theorem le_of_le_half {x e : ℝ} (h : x ≤ 1 / 2 * e) (he : 0 ≤ e) :
    x ≤ e ∧ x ≤ 3 / 2 * e ∧ x ≤ 3 * e :=
  ⟨by linarith only [h, he], by linarith only [h, he], by linarith only [h, he]⟩

/-- The mesh spacing, over abstract reals. -/
private theorem mesh_spacing_le {a w W τ ξ h : ℝ} (ha : 0 ≤ a) (hW : 0 ≤ W) (hξ : 0 ≤ ξ)
    (hτ : 0 ≤ τ) (hw : w ≤ 2 * W) (hξh : ξ ≤ h) (hτdef : τ = ξ / (2 * (a + 1))) :
    a * (w * τ) ≤ h * W := by
  have ha1 : 0 < a + 1 := by linarith only [ha]
  have e : a * ((2 * W) * τ) = (a / (a + 1)) * (ξ * W) := by
    rw [hτdef]
    field_simp
  have hfrac : a / (a + 1) ≤ 1 := by
    rw [div_le_one ha1]
    linarith only
  calc a * (w * τ) ≤ a * ((2 * W) * τ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hτ) ha
    _ = (a / (a + 1)) * (ξ * W) := e
    _ ≤ 1 * (ξ * W) := mul_le_mul_of_nonneg_right hfrac (mul_nonneg hξ hW)
    _ = ξ * W := one_mul _
    _ ≤ h * W := mul_le_mul_of_nonneg_right hξh hW

/-- The scales of a target for `N ≥ 1296 K² d²`: `n ≥ 16 d²`, `n ≥ √N` and `n ≥ 2`. -/
theorem label_scale_bounds {K N n : ℕ} (hK : 1 ≤ K)
    (hN : 1296 * K ^ 2 * (m + 1) ^ 2 ≤ N) (hn : (N : ℝ) / (9 * K) ≤ n) :
    16 * ((m : ℝ) + 1) ^ 2 ≤ n ∧ Real.sqrt N ≤ n ∧ 2 ≤ n := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hN' : 1296 * (K : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2 ≤ N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 :=
    one_le_pow₀ (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  obtain ⟨h16, hs, h2⟩ := label_scale_aux hK1 hm1 (Nat.cast_nonneg N) hN' hn
  exact ⟨h16, hs, by exact_mod_cast h2⟩

/-- `C N^{−δ/250} log^{1/4}(2 + N) ≤ η` for `N` large: the first bound of equation `eq:scales` is
small. -/
theorem exists_scales_small {C δ η : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      C * (N : ℝ) ^ (-δ / 250) * Real.log (2 + N) ^ ((1 : ℝ) / 4) ≤ η := by
  have h1 := Moments.eventually_log_two_add_le_rpow (r := δ / 250) (c := 1) (by positivity)
    one_pos
  have h2 : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(3 * δ / 1000))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (y := 3 * δ / 1000) (by positivity)).comp
      tendsto_natCast_atTop_atTop).const_mul C
    rwa [mul_zero] at this
  have h3 := h2.eventually (gt_mem_nhds hη)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((h1.and h3).and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨⟨hlog, hsmall⟩, hN1⟩ := hN₀ N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlog0 : 0 ≤ Real.log (2 + N) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ N := hN0.le; linarith)
  rw [one_mul] at hlog
  have h4 : Real.log (2 + N) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ (δ / 1000) := by
    calc Real.log (2 + N) ^ ((1 : ℝ) / 4) ≤ ((N : ℝ) ^ (δ / 250)) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hlog0 hlog (by norm_num)
      _ = (N : ℝ) ^ (δ / 1000) := by
          rw [← Real.rpow_mul hN0.le]
          congr 1
          ring
  have h5 : C * (N : ℝ) ^ (-δ / 250) * (N : ℝ) ^ (δ / 1000) = C * (N : ℝ) ^ (-(3 * δ / 1000)) := by
    rw [mul_assoc, ← Real.rpow_add hN0]
    congr 2
    ring
  calc C * (N : ℝ) ^ (-δ / 250) * Real.log (2 + N) ^ ((1 : ℝ) / 4)
      ≤ C * (N : ℝ) ^ (-δ / 250) * (N : ℝ) ^ (δ / 1000) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = C * (N : ℝ) ^ (-(3 * δ / 1000)) := h5
    _ ≤ η := hsmall.le

/-- `n^{−1/5} ≤ r` for `n` large. -/
theorem exists_nat_rpow_neg_le {r : ℝ} (hr : 0 < r) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤ r := by
  have h := ((tendsto_rpow_neg_atTop (y := 1 / 5) (by norm_num)).comp
    tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hr)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  exact ⟨n₀, fun n hn => (hn₀ n hn).le⟩

/-- For `L ≥ 16`, the pairs of cubes covering `Γ_G` are not empty. -/
theorem finePairs_nonempty {L : ℕ} (hL : 16 ≤ L) (o g : Fin m → ℤ) :
    (finePairs L o g).Nonempty := by
  have hL' : (16 : ℝ) ≤ L := by exact_mod_cast hL
  have hs : (4 : ℝ) ≤ Real.sqrt L := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL'
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) L)
  have hceil := Nat.ceil_lt_add_one (Real.sqrt_nonneg (L : ℝ))
  have h2 : (2 * ⌈Real.sqrt L⌉₊ : ℝ) ≤ L := by nlinarith only [hs, hsq, hceil]
  have h3 : 2 * ⌈Real.sqrt L⌉₊ ≤ L := by exact_mod_cast h2
  have hne : (rowBox L o g).Nonempty := by
    refine ⟨fun k => (L : ℤ) * g k + o k + ⌈Real.sqrt L⌉₊,
      Fintype.mem_piFinset.mpr fun k => Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
    omega
  exact hne.product hne

/-! ### One block -/

/-- **Steps 1 and 2 of the proof of [AB26, Lemma 6.2], as changed by the paper, in one block, from
the instantiated contracts.** -/
theorem exists_labelError_of_inputs {M : Model m} (hM : M.Standing) {Cd T : ℝ} (hCd : 0 ≤ Cd)
    (hTube : TubeProperty m Cd T) {K : ℕ} {A : ℝ} (hA : 1 ≤ A) {n L i : ℕ} (hn : 2 ≤ n)
    (hL : 16 ≤ L) (hw : 1 ≤ wInt M K A n) (hQ : 0 < Q M K A n) {t : EuclideanSpace ℝ (Fin m)}
    (ht : ‖t‖ ≤ T) (hi : 1 ≤ i) {P : Pt m} {o g : Fin m → ℤ} {C₁ CS : ℝ} (hC₁ : 0 < C₁)
    (hCS : 0 < CS)
    (hU : ∀ (T' : Finset ((Fin m → ℤ) × (Fin m → ℤ))) (hT' : T'.Nonempty) (θ : ℝ), 0 < θ →
      ∀ X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ,
        (∀ i ∈ T', CurvatureVariance.IsOs M.P 1 θ (X i)) →
        CurvatureVariance.IsOs M.P 1 (C₁ * θ * Real.log (2 + T'.card) ^ (1 / (1 : ℝ))) (T'.sup' hT' X))
    (hshortF : ∀ jk ∈ finePairs L o g, ∃ X : Config m → ℝ,
      CurvatureVariance.IsOs M.P 1 (CS * Q M K A n) X ∧ ∀ᵐ ω ∂M.P,
        ∀ u ∈ finePairCube₁ n (wInt M K A n) t i jk.1,
        ∀ v ∈ finePairCube₂ n (wInt M K A n) t i jk.2,
          |slabTimeReal ω u.1 v.1 u v - M.μ.1 (point v - point u)| ≤ X ω)
    {CR : ℝ} (hCR : 0 ≤ CR)
    (hrad : ∀ jk ∈ finePairs L o g,
      ∫⁻ ω, fineRadius n (wInt M K A n) t i (W M K A n) jk ω ^ (8 * (m + 1)) ∂M.P ≤
        ENNReal.ofReal CR)
    {a : ℝ} (hdrift : ∀ u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n),
      ∀ v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n),
        |M.μ.1 (point v - point u) - inner ℝ P (point v - point u)| ≤ a * Q M K A n)
    {τ h : ℝ} (hτ : 0 < τ) (hτh : (m : ℝ) * ((wInt M K A n : ℝ) * τ) ≤ h * W M K A n)
    {I I' : Set (Vertex m)}
    (hI : subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n) ⊆ I)
    (hI' : subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n) ⊆ I')
    {η : ℝ} (hη : 0 ≤ η)
    (hmodF : ∃ X : Config m → ℝ,
      eLpNorm X (8 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal (η * Q M K A n) ∧
      ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ u₂ ∈ I, ∀ v ∈ I', ∀ v₂ ∈ I',
        ‖point u - point u₂‖ ≤ h * W M K A n → ‖point v - point v₂‖ ≤ h * W M K A n →
        |passageTimeReal ω u v - passageTimeReal ω u₂ v₂ -
          inner ℝ P (point v - point u - point v₂ + point u₂)| ≤ X ω)
    {c Cpd : ℝ} (hc : 0 ≤ c) (hCpd : 0 < Cpd)
    (hpdF : ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 Cpd X ∧ ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I',
      (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v ∧
      slabTimeReal ω u.1 v.1 u v - passageTimeReal ω u v ≤ c + X ω)
    (hcQ : 2 * c / Q M K A n +
      2 * ((2 * (1 + ((faExp m).factorial : ℝ))) ^ (1 / (faExp m : ℝ)) * Cpd) / Q M K A n ≤ η) :
    ∃ Y : Config m → ℝ, eLpNorm Y (8 * (m + 1) : ℕ) M.P ≤
        ENNReal.ofReal (labelHolder m Cd CR (C₁ * CS) L + 2 * η +
          (max (a - (L : ℝ) ^ 4 / 2) 0 + labelClipError m (C₁ * CS) L)) ∧
      ∀ᵐ ω ∂M.P, ∀ u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n),
        ∀ v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n),
        |normSlabTime M K A ω n P i u v -
            labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω u v| +
          |labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω u v -
            labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω
              (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n)
                (meshIndex (wInt M K A n) L t o g τ u))
              (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n)
                (meshIndex (wInt M K A n) L t o g τ v))| +
          max (|labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω
              (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n)
                (meshIndex (wInt M K A n) L t o g τ u))
              (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n)
                (meshIndex (wInt M K A n) L t o g τ v))| - (L : ℝ) ^ 4) 0 ≤ Y ω := by
  have := hM.probP
  have hne := finePairs_nonempty (m := m) hL o g
  have hk := one_le_faExp m
  have hL1 : 1 ≤ L := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  obtain ⟨X, hXm, hXos, hXae⟩ := exists_measurable_family (finePairs L o g)
    (R := fun jk ω x => ∀ u ∈ finePairCube₁ n (wInt M K A n) t i jk.1,
      ∀ v ∈ finePairCube₂ n (wInt M K A n) t i jk.2,
        |slabTimeReal ω u.1 v.1 u v - M.μ.1 (point v - point u)| ≤ x) hshortF
  have hgood : ∀ᵐ ω ∂M.P, FineGood n (wInt M K A n) L t i o g M.μ X ω := by
    filter_upwards [ae_exists_isSlabGeodesic_of_mem hM, hXae] with ω h1 h2
    exact ⟨h1, h2⟩
  -- the union bound, equation `eq:union`, over the pairs of cubes
  set θ : ℝ := C₁ * CS * labelLog m L with hθdef
  have hθ : 0 < θ := mul_pos (mul_pos hC₁ hCS) (labelLog_pos m L)
  have hsup : CurvatureVariance.IsOs M.P 1 (θ * Q M K A n) ((finePairs L o g).sup' hne X) := by
    have h1 := hU _ hne (CS * Q M K A n) (mul_pos hCS hQ) X hXos
    refine h1.mono_scale zero_le_one ?_ ?_
    · have hlog : 0 < Real.log (2 + ((finePairs L o g).card : ℝ)) :=
        Real.log_pos (by
          linarith only [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (finePairs L o g).card)])
      rw [div_one, Real.rpow_one]
      positivity
    · rw [div_one, Real.rpow_one]
      have hlog : Real.log (2 + ((finePairs L o g).card : ℝ)) ≤ labelLog m L := by
        refine Real.log_le_log ?_ ?_
        · linarith only [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (finePairs L o g).card)]
        · linarith only [card_finePairs_le (m := m) L o g]
      calc C₁ * (CS * Q M K A n) * Real.log (2 + ((finePairs L o g).card : ℝ))
          ≤ C₁ * (CS * Q M K A n) * labelLog m L :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = θ * Q M K A n := by simp only [θ]; ring
  set S : Config m → ℝ := fun ω => max ((finePairs L o g).sup' hne X ω) 0 with hSdef
  have hSm : Measurable S :=
    (Finset.measurable_sup' hne fun jk _ => hXm jk).max measurable_const
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => le_max_right _ _
  have hXS : ∀ jk ∈ finePairs L o g, ∀ ω, X jk ω ≤ S ω := fun jk hjk ω => by
    refine le_max_of_le_left ?_
    rw [Finset.sup'_apply]
    exact Finset.le_sup' (fun jk => X jk ω) hjk
  have hmom : ∫⁻ ω, ENNReal.ofReal ((S ω / Q M K A n) ^ (2 * faExp m)) ∂M.P ≤
      ENNReal.ofReal (labelMoment m θ) :=
    lintegral_ofReal_posPart_div_pow_le hθ hQ hsup (2 * faExp m)
  -- the modulus
  obtain ⟨Z, hZm, hZ, hZae⟩ := exists_labelModError hM hQ hn hw hτ hτh hI hI' hk hη hmodF hc hCpd
    hpdF
  have hZ' : eLpNorm Z (8 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal (2 * η) :=
    hZ.trans (ENNReal.ofReal_le_ofReal (by linarith only [hcQ]))
  have hCCS : 0 ≤ C₁ * CS := (mul_pos hC₁ hCS).le
  exact exists_labelBlockError hM hCd hTube hA hn hw hQ ht hi hgood hSm hS0 hXS hk
    (labelMoment_nonneg m hθ.le) hmom hCR hrad hdrift hZm hZ' hZae (by positivity)
    (labelHolder_nonneg m Cd hCR hCCS L) (by positivity) (labelClipError_nonneg m _ L)
    (sqrt_mul_sqrt_le_labelHolder m Cd hCR hCCS L) (labelMoment_le_clipError m hL1 _)

/-! ### Lemma `lem:labels` -/

/-- **Lemma `lem:labels`**, by the paper's proof: Steps 1 and 2 of the proof of [AB26, Lemma 6.2] as
the paper changes them, and Step 3 of that proof, from Proposition `prop:profiles`, Lemma
`lem:localization` with `p = 8d`, Lemma `lem:modulus`, equations `eq:profiledifference`,
`eq:support` and `eq:scales`, and the tube property. -/
theorem labelsStatement_of (hprof : Contracts.ProfilesStatement m)
    (hloc : Contracts.LocalizationStatement m) (hmod : Contracts.ModulusStatement m)
    (hpd : Contracts.ProfileDifferenceStatement m) (hsupp : Contracts.SupportStatement m)
    (hscales : Contracts.ScalesStatement m) (htube : Contracts.TubeStatement m) :
    Contracts.LabelsStatement m := by
  intro bd hbd Cstar
  have hm1 : 1 ≤ m := hbd.law.one_le_m
  have hδb := hbd.law.delta_pos
  have hk1 : 1 ≤ 8 * (m + 1) := by omega
  obtain ⟨CS, hCS, hProf⟩ := hprof bd hbd Cstar 2 one_le_two
  obtain ⟨CR, hCR, hRad⟩ := hloc bd hbd Cstar 2 one_le_two ((8 * (m + 1) : ℕ) : ℝ)
    (by exact_mod_cast hk1)
  obtain ⟨Cpd, hCpd, hPD⟩ := hpd bd hbd Cstar
  obtain ⟨Cd, hCd, hTube⟩ := exists_tubeProperty htube (T := bd.T + 1)
    (by linarith only [hbd.T_nonneg])
  obtain ⟨c₀, C₀, r₁, hc₀, hC₀, hr₁, -, hSupp⟩ := hsupp bd hbd
  obtain ⟨Csc, hCsc, hSc⟩ := hscales bd hbd Cstar
  obtain ⟨C₁, hC₁, hU⟩ := Contracts.osUnionStatement_holds.{0, 0} 1 one_pos
  have hb : ∀ L : ℕ, (1 : ℝ) ≤ 2 * L + 2 := fun L => by
    linarith only [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  choose h hh hmodh using fun L : ℕ =>
    hmod bd hbd Cstar (2 * L + 2) (hb L) (faStep L) (faStep_pos L)
  -- the functions of `L`
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℕ → ℝ, ξ = fun L => min (h L) (faStep L) := ⟨_, rfl⟩
  have hξ : ∀ L, 0 < ξ L := fun L => by
    rw [hξdef]
    exact lt_min (hh L) (faStep_pos L)
  have hξh : ∀ L, ξ L ≤ h L := fun L => by
    rw [hξdef]
    exact min_le_left _ _
  have hξs : ∀ L, ξ L ≤ faStep L := fun L => by
    rw [hξdef]
    exact min_le_right _ _
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℕ → ℝ, τ = fun L => ξ L / (2 * ((m : ℝ) + 1)) := ⟨_, rfl⟩
  have hτ : ∀ L, 0 < τ L := fun L => by
    rw [hτdef]
    exact div_pos (hξ L) (by positivity)
  obtain ⟨a, hadef⟩ : ∃ a : ℕ → ℝ, a = fun L : ℕ =>
      C₀ * (4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2 + Csc) := ⟨_, rfl⟩
  have hCCS : 0 ≤ C₁ * CS := (mul_pos hC₁ hCS).le
  have hψ : Tendsto (fun L : ℕ => labelHolder m Cd CR (C₁ * CS) L + 2 * faStep L +
      (max (a L - (L : ℝ) ^ 4 / 2) 0 + labelClipError m (C₁ * CS) L) + ξ L + faStep L)
      atTop (𝓝 0) := by
    have h1 := tendsto_labelHolder hm1 hCd hCR.le hCCS
    have h2 : Tendsto faStep atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 : Tendsto (fun L : ℕ => max (a L - (L : ℝ) ^ 4 / 2) 0) atTop (𝓝 0) := by
      have h := tendsto_max_sub_clip (C := C₀ * (4 * (m : ℝ) ^ 2)) (D := C₀ * Csc)
        (by positivity) (by positivity)
      refine h.congr fun L => ?_
      rw [hadef]
      ring_nf
    have h4 := tendsto_labelClipError hm1 (C₁ * CS)
    have h5 : Tendsto ξ atTop (𝓝 0) :=
      squeeze_zero (fun L => (hξ L).le) hξs h2
    have h := (((h1.add (h2.const_mul 2)).add (h3.add h4)).add h5).add h2
    simpa only [mul_zero, add_zero] using h
  refine ⟨fun L => labelAlpha m L (τ L) (ξ L), _, fun L => labelAlpha_pos m L _ (hξ L), hψ,
    fun K hK L hL => ?_⟩
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have h9K : (0 : ℝ) < 9 * K := by linarith only [hK1r]
  have hκ : (0 : ℝ) < 1 / (9 * K) := div_pos one_pos h9K
  have hκ1 : 1 / (9 * (K : ℝ)) ≤ 1 := by
    rw [div_le_one h9K]
    linarith only [hK1r]
  have hL1 : 1 ≤ L := by omega
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  obtain ⟨N₁, hN₁⟩ := hProf (1 / (9 * K)) hκ K hK
  obtain ⟨N₂, hN₂⟩ := hRad (1 / (9 * K)) hκ K hK
  obtain ⟨N₃, hN₃⟩ := hmodh L K hK (1 / (9 * K)) hκ hκ1
  obtain ⟨N₄, hN₄⟩ := hPD (2 * L + 2) (hb L) K hK
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1' : (0 : ℝ) < (m : ℝ) + 1 := by linarith only [hm0]
  have hL1' : (0 : ℝ) < (L : ℝ) + 1 := by linarith only [hLr]
  have h2L : (0 : ℝ) ≤ 2 * ((L : ℝ) + 1) := (mul_pos two_pos hL1').le
  obtain ⟨η₀, hη₀def⟩ : ∃ η₀ : ℝ, η₀ = min (1 / (8 * ((m : ℝ) + 1) * ((L : ℝ) + 1)))
      (r₁ / (2 * ((m : ℝ) + 1) * ((L : ℝ) + 1))) := ⟨_, rfl⟩
  have hη₀ : 0 < η₀ := by
    rw [hη₀def]
    exact lt_min (div_pos one_pos (mul_pos (mul_pos (by norm_num) hm1') hL1'))
      (div_pos hr₁ (mul_pos (mul_pos two_pos hm1') hL1'))
  obtain ⟨N₅, hN₅⟩ := exists_scales_small hCsc hδb hη₀
  obtain ⟨Cp, hCpdef⟩ : ∃ Cp : ℝ, Cp =
      (2 * (1 + ((faExp m).factorial : ℝ))) ^ (1 / (faExp m : ℝ)) * Cpd := ⟨_, rfl⟩
  have hCp : 0 ≤ Cp := by
    rw [hCpdef]
    positivity
  obtain ⟨N₆, hN₆⟩ := exists_log_sq_add_le (a := 2 * ((L : ℝ) + 1) * Cpd)
    (b := 2 * ((L : ℝ) + 1) * Cp) (c := 9 * K) (mul_nonneg h2L hCpd.le) (mul_nonneg h2L hCp) h9K
  obtain ⟨n₇, hn₇⟩ := exists_nat_rpow_neg_le hr₁
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆)
      (max (1296 * K ^ 2 * (m + 1) ^ 2) (9 * K * n₇))),
    fun M hM hfit N hN A hA hPrem hRange n ℓ y hT P hP => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hN1, hN2⟩, hN3, hN4⟩, ⟨hN5, hN6⟩, hNb, hN7⟩ := hN
  -- the scales of the target
  have hn9 := IsTarget.div_le_n hT hK1
  have hnN := IsTarget.n_le hT hK1
  obtain ⟨hn16, hnsq, hn2⟩ := label_scale_bounds hK1 hNb hn9
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hn0 : 0 < n := hn1
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hn2N : (n : ℝ) ≤ 2 * N := by linarith only [hnN', (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hκn : 1 / (9 * (K : ℝ)) * N ≤ n := by rwa [one_div_mul_eq_div]
  have hQ1 := one_le_Q hM hK hA hn1
  have hQ : 0 < Q M K A n := lt_of_lt_of_le one_pos hQ1
  let w := wInt M K A n
  have hw1 : 1 ≤ w := one_le_wInt hM hK hA hn1
  have hw2 : (w : ℝ) ≤ 2 * W M K A n := wInt_le_two_mul_W hM hK hA hn1
  have hWn : W M K A n ^ 2 = n * Q M K A n := Real.sq_sqrt (mul_pos hn0r hQ).le
  have hδeq : M.δ = bd.law.δ := hfit.δ_eq
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  let t := targetSlope ℓ y
  -- the slope
  have hnE : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1r (by linarith only [hδ1])
  have hnE0 : 0 ≤ (n : ℝ) ^ (M.δ / 100 - 1 / 4) := Real.rpow_nonneg hn0r.le _
  have ht : ‖t - M.t₀‖ ≤ 1 / 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) :=
    norm_targetSlope_le_half hM hK hT hn1
  have ht1 : ‖t‖ ≤ bd.T + 1 :=
    (norm_le_norm_sub_add t M.t₀).trans (by linarith only [hfit.t₀_le, ht, hnE])
  obtain ⟨ht0, ht32, ht3⟩ := le_of_le_half ht hnE0
  have hn₇n : n₇ ≤ n := by
    have h1 : ((9 * K * n₇ : ℕ) : ℝ) ≤ N := by exact_mod_cast hN7
    have h2 : (n₇ : ℝ) ≤ (N : ℝ) / (9 * K) := by
      rw [le_div_iff₀ h9K]
      push_cast at h1
      linarith only [h1]
    exact_mod_cast h2.trans hn9
  have htr : ‖t - M.t₀‖ ≤ r₁ := by
    have h1 : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ (n : ℝ) ^ (-(1 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1r (by linarith only [hδ1])
    exact ht0.trans (h1.trans (hn₇ n hn₇n))
  -- the first bound of equation `eq:scales`
  have hN2' : 2 ≤ N := hn2.trans hnN
  have hsn16 : Real.sqrt N / 16 ≤ n := by linarith only [hnsq, Real.sqrt_nonneg (N : ℝ)]
  have hSc1 := hSc K hK M hM hfit N hN2' A hA hRange (n : ℝ) hsn16
  have hE0 : 0 < (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := Real.rpow_pos_of_pos hn0r _
  have hWm : W M K A n ≤ η₀ * (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
    have h1 := hSc1.1
    have h2 := hN₅ N hN5
    rw [← hδeq] at h2
    rw [div_le_iff₀ hE0] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hE0.le)
  have hW8 : W M K A n ≤ 1 / (8 * ((m : ℝ) + 1) * ((L : ℝ) + 1)) *
      (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
    hWm.trans (mul_le_mul_of_nonneg_right (hη₀def ▸ min_le_left _ _) hE0.le)
  have hwide := mul_one_add_le_of_W_le hδ.le hn16 hw2 hW8
  have hslope : ∀ o g : Fin m → ℤ, ∀ (i : ℕ), ∀ jk ∈ finePairs L o g,
      ‖rowPairSlope n w t i jk.1 jk.2 - M.t₀‖ ≤ (n : ℝ) ^ (M.δ / 100 - 1 / 4) := fun o g i jk hjk =>
    norm_rowPairSlope_le_of_wide hn1 ht hwide i (Finset.mem_product.mp hjk).1
      (Finset.mem_product.mp hjk).2
  -- the sizes for equation `eq:support`
  have hr : (m : ℝ) * ((L : ℝ) * (w : ℝ)) / n ≤ r₁ := by
    have hnEn : (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) ≤ n := by
      calc (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1r (by linarith only [hδ1])
        _ = n := Real.rpow_one _
    have hr₂ : 0 < r₁ / (2 * ((m : ℝ) + 1) * ((L : ℝ) + 1)) :=
      div_pos hr₁ (mul_pos (mul_pos two_pos hm1') hL1')
    have hW1 : W M K A n ≤ r₁ / (2 * ((m : ℝ) + 1) * ((L : ℝ) + 1)) * n :=
      hWm.trans ((mul_le_mul_of_nonneg_right (hη₀def ▸ min_le_right _ _) hE0.le).trans
        (mul_le_mul_of_nonneg_left hnEn hr₂.le))
    exact mul_div_le_of_W_le hm0 (Nat.cast_nonneg L) hr₁ hn0r hw2 hW1
  have hD : (n : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Csc * Q M K A n := by
    have h1 := hSc1.2 t ht3
    rw [div_le_iff₀ hQ] at h1
    have h2 : (n : ℝ) ^ (-M.δ / 5) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1r (by linarith only [hδ])
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCsc.le) hQ.le
    rw [mul_one] at h3
    exact h1.trans h3
  have haL : a L = C₀ * (4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2 + Csc) := congrFun hadef L
  -- the error of the comparison
  have hcQ : 2 * (Cpd * Real.log N ^ 2) / Q M K A n + 2 * Cp / Q M K A n ≤ faStep L := by
    have h6 := hN₆ N hN6
    have h7 : ((N : ℝ) / (9 * K)) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg N) h9K.le) hn9 (by norm_num)
    have h8 := rpow_le_Q hM hK hA hn1
    rw [← add_div, faStep, div_le_div_iff₀ hQ hL1', one_mul]
    linarith only [h6, h7, h8]
  -- the mesh spacing
  have hτh : (m : ℝ) * ((w : ℝ) * τ L) ≤ h L * W M K A n :=
    mesh_spacing_le hm0 (Real.sqrt_nonneg _) (hξ L).le (hτ L).le hw2 (hξh L) (congrFun hτdef L)
  have := hM.probP
  have hblock : ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ o g : Fin m → ℤ, (∀ k, 0 ≤ o k ∧ o k < L) →
      ∃ Y : Config m → ℝ, eLpNorm Y (8 * (m + 1) : ℕ) M.P ≤
          ENNReal.ofReal (labelHolder m Cd CR (C₁ * CS) L + 2 * faStep L +
            (max (a L - (L : ℝ) ^ 4 / 2) 0 + labelClipError m (C₁ * CS) L)) ∧
        ∀ᵐ ω ∂M.P, ∀ u ∈ subcubeFace w L t o g (((i : ℤ) - 1) * n),
          ∀ v ∈ subcubeFace w L t o g ((i : ℤ) * n),
          |normSlabTime M K A ω n P i u v - labelPsi M K A n P i (block n w L t i o g) ω u v| +
            |labelPsi M K A n P i (block n w L t i o g) ω u v -
              labelPsi M K A n P i (block n w L t i o g) ω
                (blockRep w L t o g (τ L) (((i : ℤ) - 1) * n) (meshIndex w L t o g (τ L) u))
                (blockRep w L t o g (τ L) ((i : ℤ) * n) (meshIndex w L t o g (τ L) v))| +
            max (|labelPsi M K A n P i (block n w L t i o g) ω
                (blockRep w L t o g (τ L) (((i : ℤ) - 1) * n) (meshIndex w L t o g (τ L) u))
                (blockRep w L t o g (τ L) ((i : ℤ) * n) (meshIndex w L t o g (τ L) v))| -
              (L : ℝ) ^ 4) 0 ≤ Y ω := by
    intro i hi _ o g _
    -- Proposition `prop:profiles` and Lemma `lem:localization` on the pairs covering `Γ_G`
    have hshortF : ∀ jk ∈ finePairs L o g, ∃ X : Config m → ℝ,
        CurvatureVariance.IsOs M.P 1 (CS * Q M K A n) X ∧ ∀ᵐ ω ∂M.P,
          ∀ u ∈ finePairCube₁ n w t i jk.1, ∀ v ∈ finePairCube₂ n w t i jk.2,
            |slabTimeReal ω u.1 v.1 u v - M.μ.1 (point v - point u)| ≤ X ω := by
      intro jk hjk
      obtain ⟨X, hXos, hXae⟩ := hN₁ M hM hfit N hN1 A hA hPrem hRange n _ _ _
        (isCubePair_rowCubes hn0 hw2 t i jk.1 jk.2)
        (Or.inr ⟨hκn, hn2N, by linarith only [hslope o g i jk hjk, hnE0]⟩)
      exact ⟨X, hXos, hXae.mono fun ω hω => hω.2⟩
    have hradF : ∀ jk ∈ finePairs L o g,
        ∫⁻ ω, fineRadius n w t i (W M K A n) jk ω ^ (8 * (m + 1)) ∂M.P ≤ ENNReal.ofReal CR := by
      intro jk hjk
      have h1 := (hN₂ M hM hfit N hN2 A hA hPrem hRange n hκn hnN _ _ _
        (isCubePair_rowCubes hn0 hw2 t i jk.1 jk.2) (hslope o g i jk hjk)).2 _ fun _ hu => hu.1
      simp only [ENNReal.rpow_natCast] at h1
      exact h1
    -- the pair of cubes containing the two faces
    have hface : (i : ℤ) * n = ((i : ℤ) - 1) * n + n := by ring
    have hI : subcubeFace w L t o g (((i : ℤ) - 1) * n) ⊆
        transverseCube (((i : ℤ) - 1) * n) (blockCenter w L t o g (((i : ℤ) - 1) * n))
          ((L : ℝ) * w) := subcubeFace_subset_transverseCube _
    have hI' : subcubeFace w L t o g ((i : ℤ) * n) ⊆
        transverseCube (((i : ℤ) - 1) * n + n)
          (blockCenter w L t o g (((i : ℤ) - 1) * n + n)) ((L : ℝ) * w) := by
      rw [hface]
      exact subcubeFace_subset_transverseCube _
    have hcube := isCubePair_blockCubes (L := L) hw2 t o g (((i : ℤ) - 1) * n)
    have hmodF := hN₃ M hM hfit N hN3 A hA hPrem hRange n hκn hnN t _ _ hcube ht0 P hP
    have hpdF := hN₄ M hM hfit N hN4 A hA hRange n hnsq hn2N t _ _ hcube ht32
    have hdrift : ∀ u ∈ subcubeFace w L t o g (((i : ℤ) - 1) * n),
        ∀ v ∈ subcubeFace w L t o g ((i : ℤ) * n),
          |M.μ.1 (point v - point u) - inner ℝ P (point v - point u)| ≤ a L * Q M K A n := by
      intro u hu v hv
      rw [haL]
      exact abs_drift_le hC₀.le (hSupp M hM hfit).1 hP htr hn0 hw2 hWn hr hD hu hv
    exact exists_labelError_of_inputs hM hCd hTube hA hn2 hL hw1 hQ ht1 hi hC₁ hCS
      (fun T' hT' θ hθ X hX => hU M.P T' hT' θ hθ X hX) hshortF hCR.le hradF hdrift (hτ L) hτh
      hI hI' (faStep_pos L).le hmodF (mul_nonneg hCpd.le (sq_nonneg _)) hCpd hpdF (hCpdef ▸ hcQ)
  have hε₀ : 0 ≤ labelHolder m Cd CR (C₁ * CS) L + 2 * faStep L +
      (max (a L - (L : ℝ) ^ 4 / 2) 0 + labelClipError m (C₁ * CS) L) := by
    have h1 := labelHolder_nonneg m Cd hCR.le hCCS L
    have h2 := (faStep_pos L).le
    have h3 : 0 ≤ max (a L - (L : ℝ) ^ 4 / 2) 0 := le_max_right _ _
    have h4 := labelClipError_nonneg m (C₁ * CS) L
    linarith only [h1, h2, h3, h4]
  exact exists_isLabelFamily hM hw1 t P (hτ L) (by positivity) (hξ L)
    (labelAlpha_pos m L _ (hξ L)).le (labelAlpha_mul_card_le_one m hL1 _ (hξ L)) hε₀
    (faStep_pos L).le (merge_le_labelAlpha m L _ (hξ L)) hblock

end CurvatureVariance.Paper.Gain
