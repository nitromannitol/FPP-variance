/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocPack
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry
import CurvatureVariance.Paper.Proofs.Geometry.SlabsPair
import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet
import CurvatureVariance.Infra.FPP.Walks

/-!
# Lemma `lem:localization`: the assembly at fixed `N`, `A`, `ℓ`

`normal_core`: the proof of Lemma `lem:localization` for a pair of cubes with `|ū| ≤ d^{1/2}`, from
the instances of the premises at fixed `N`, `A`, `ℓ` and the numerical conditions (`Pack`).

* `cost_of_cubes`: `μ(v − u) − ζ_t·(v − u) ≤ C(b)Q_ℓ`, equation `eq:support` for the pair.
* `oneNorm_le_of_cubes`: the length of `v − u`, for the edge count off the good event.
* `Loc.finalConst`: the constant `C(b, p)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts
  CurvatureVariance.Paper.Proofs.Geometry CurvatureVariance.Infra.Os Radius

variable {m : ℕ}

/-- The constant `C(b, p)` of Lemma `lem:localization`. -/
noncomputable def finalConst (T Cv Cp c₂ B τ q : ℝ) : ℝ :=
  2 ^ q * (2 * (1 + ((Nat.ceil (q / 2)).factorial : ℝ)) *
    (2 * (1 + ((1 + T) * (2 + Real.sqrt (2 * (Cv + Cp) / c₂)) + B)) +
      (1 + T) * Real.sqrt (2 / c₂) * Real.sqrt τ) ^ q + 1)

/-- Equation `eq:support` for the pair: `μ(v − u) − ζ_t·(v − u) ≤ C Q_ℓ`, through
`ShortLengths.cost_le_Q`. -/
theorem cost_of_cubes {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {cS CS r₁ ρ T Bq wb a₀ a₀' : ℝ} (hCS : 0 < CS)
    (h24 : ∀ t h : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hρ : ρ ≤ r₁) (hρ1 : ρ ≤ 1) {t c c' : EuclideanSpace ℝ (Fin m)} {p : ℤ} {P : Pt m}
    (hP : IsSubgradient M.μ (slopeVec t) P) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (ht : ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4)) (htr : ‖t - M.t₀‖ ≤ ρ / 2)
    (ha₀ : 0 ≤ a₀) (ha₀' : 0 ≤ a₀') (ha₀b : a₀ ≤ wb) (ha₀'b : a₀' ≤ wb)
    (hcc : ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1))
    (hWB : Real.sqrt m * wb + 2 * Real.sqrt ((m : ℝ) + 1) ≤ Bq * W M K A ℓ)
    (hρ₂ : 4 * (2 + T) * Bq * W M K A ℓ ≤ ρ * ℓ) (ht₀ : ‖M.t₀‖ ≤ T) {u v : Vertex m}
    (hu : u ∈ transverseCube p c a₀) (hv : v ∈ transverseCube (p + ℓ) c' a₀') :
    M.μ.1 (point v - point u) - ⟪P, point v - point u⟫ ≤
      (2 * (2 + T) ^ 2 * CS * Bq ^ 2 + 2 * CS) * Q M K A ℓ := by
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hT0 : 0 ≤ ‖M.t₀‖ := norm_nonneg _
  have hy := Proofs.ShortLengths.norm_transverse_sub_le_of_cubes ha₀ ha₀' ha₀b ha₀'b hcc hu hv
  set y := transversePoint (v.2 - u.2) with hy'
  have hsub : point v - point u =
      (ℓ : ℝ) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), y - (ℓ : ℝ) • t) := by
    rw [Moments.ExpArray.point_sub_eq (s := ℓ) (by rw [hv.1, hu.1])]
    apply Infra.FPP.pt_ext
    · simp [slopeVec]
    · simp [slopeVec, hy']
  have hw : ‖(WithLp.toLp 2 ((0 : ℝ), y - (ℓ : ℝ) • t) : Pt m)‖ ≤ Bq * W M K A ℓ :=
    (Proofs.ShortLengths.norm_toLp_zero_le _).trans (hy.trans hWB)
  have hbw : 0 ≤ Bq * W M K A ℓ := (norm_nonneg _).trans hw
  have hBW : 4 * (2 + ‖M.t₀‖) * Bq * W M K A ℓ ≤ ρ * ℓ := by
    refine le_trans ?_ hρ₂
    have h1 : (2 + ‖M.t₀‖) * (Bq * W M K A ℓ) ≤ (2 + T) * (Bq * W M K A ℓ) :=
      mul_le_mul_of_nonneg_right (by linarith only [ht₀]) hbw
    linarith only [h1]
  have h := Proofs.ShortLengths.cost_le_Q hM hK hA hCS h24 hρ hρ1 hP hℓ1 ht htr hsub
    (by rw [sub_self, abs_zero]; positivity) hw hBW
  refine h.trans (mul_le_mul_of_nonneg_right ?_
    (Proofs.ShortLengths.Q_nonneg (by linarith only [hA]) (by linarith only [hℓ1])))
  have h2 : (2 + ‖M.t₀‖) ^ 2 ≤ (2 + T) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [hT0]) (by linarith only [ht₀]) 2
  have h3 : 0 ≤ CS * Bq ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right h2 h3
  nlinarith only [this]

/-- The `ℓ¹` length of `v − u`. -/
theorem oneNorm_le_of_cubes {M : Model m} {Γ τ T : ℝ} {ℓ : ℕ} {t c : EuclideanSpace ℝ (Fin m)}
    {p : ℤ} {u v : Vertex m} (hℓ : 0 < ℓ) (hu1 : u.1 = p) (hv1 : v.1 = p + ℓ)
    (hΓu : ‖ofs t p c u‖ ≤ Γ) (hΓv : ‖ofs t p c v‖ ≤ Γ)
    (hτ : ‖t - M.t₀‖ + 2 * Γ / ℓ ≤ τ) (hTT : ‖M.t₀‖ + τ ≤ T) :
    oneNorm (v - u) ≤ ((m : ℝ) + 1) * ((1 + T) * ℓ) := by
  obtain ⟨huv, -, ht'⟩ := slope_near (M := M) hℓ hu1 hv1 hΓu hΓv hτ hTT
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  rw [oneNorm_sub_eq_l1Dist]
  refine (l1Dist_le_mul_norm u v).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [huv, norm_smul, Real.norm_of_nonneg hℓ0.le, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_slopeVec_le ht') hℓ0.le

/-- A real form of the bound of Lemma `lem:slabs` (1): `a ≤ b + c` for extended reals of the
passage times. -/
theorem real_le_of_coe_le {a b : ℝ≥0} {c : ℝ} (hc : 0 ≤ c)
    (h : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) + ENNReal.ofReal c) : (a : ℝ) ≤ b + c := by
  have h1 : (a : ℝ≥0∞) ≤ ((b + c.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_add]; exact h
  have h2 : a ≤ b + c.toNNReal := by exact_mod_cast h1
  have h3 : (a : ℝ) ≤ ((b + c.toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast h2
  rwa [NNReal.coe_add, Real.coe_toNNReal c hc] at h3

/-- **The proof of Lemma `lem:localization`** for a pair of cubes, at fixed `N`, `A`, `ℓ`, from the
instances of the premises. The good event `G` is `𝒢_N(log N)`; on it, Lemma `lem:cone` holds at
`S = Cs log N`, and Lemma `lem:slabs` (1) at `log N`. -/
theorem normal_core (hSum : SignedOsSumStatement.{0, 0}) (hUnion : OsUnionStatement.{0, 0})
    {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ} (hA : 1 ≤ A) {N ℓ : ℕ}
    {κ b CT CPb CP cS CS r₁ C₃ Cc Csl Cs Clen τG q T c₀ C₀ K₁ Bq ρ η : ℝ} {κT : ℕ}
    {t c c' : EuclideanSpace ℝ (Fin m)} {p : ℤ} {a₀ a₀' : ℝ} {a a' : Vertex m}
    {G : Set (Config m)} (hℓ : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (hκℓ : κ * N ≤ ℓ) (hN1 : Real.sqrt N ≤ ℓ)
    (hb : 0 ≤ b) (hCT : 0 < CT) (hCPb : 0 < CPb) (hCP : 0 < CP) (hcS : 0 < cS) (hCS : 0 < CS)
    (hC₃ : 0 < C₃) (hCc : 0 < Cc) (hClen : 0 < Clen) (hq : 1 ≤ q) (hBq : 0 ≤ Bq)
    (hTree : TreeAt M K A N (8 * b) CT)
    (hshort : ShortConclusion M K A ℓ CPb t (transverseCube p c a₀)
      (transverseCube (p + ℓ) c' a₀'))
    (hprof : ProfAt M K A N (κ / 32) CP)
    (h24 : ∀ t h : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hτ3 : (ℓ : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ C₃ * Q M K A ℓ)
    (hlen : ∀ u v : Vertex m, ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 Clen X ∧ ∀ᵐ ω ∂M.P,
      (∀ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ →
        (γ.length : ℝ) ≤ Clen * (1 + oneNorm (v - u)) + X ω) ∧
      (∀ p q : ℤ, p + 2 ≤ q → p ≤ u.1 → u.1 ≤ q → p ≤ v.1 → v.1 ≤ q →
        ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω p q γ →
          (γ.length : ℝ) ≤ Clen * (1 + oneNorm (v - u)) + X ω))
    (hG : CurvatureVariance.IsOs M.P 2 τG (Gᶜ.indicator fun _ => (1 : ℝ)))
    (hGcone : ∀ ω ∈ G, ConeAt M Cc (Cs * Real.log N) N ω)
    (hGslab : ∀ ω ∈ G, ∀ u ∈ transverseCube p c a₀, ∀ v ∈ transverseCube (p + ℓ) c' a₀',
      slabTime ω u.1 v.1 u v ≤ (passageTime ω u v : ℝ≥0∞) +
        ENNReal.ofReal (Csl * Real.log N ^ 2))
    (hpack : Pack M K A ℓ t p c a a' T c₀ C₀ κT ((ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200))
      (K₁ * (Cs * Real.log N) ^ 2) (2 * (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4)) (Real.log N)
      (Cs * Real.log N) K₁ Cc (Real.sqrt m * (b * W M K A ℓ) + 2 * rtd m) Bq r₁ ρ Csl)
    (ha : ‖point a - (basePt p c - ((ℓ : ℝ) / 16) • slopeVec t)‖ ≤ rtd m)
    (ha' : ‖point a' - (basePt (p + ℓ) c' + ((ℓ : ℝ) / 16) • slopeVec t)‖ ≤ rtd m)
    (ha₀ : 0 ≤ a₀) (ha₀b : a₀ ≤ b * W M K A ℓ) (ha₀' : 0 ≤ a₀') (ha₀'b : a₀' ≤ b * W M K A ℓ)
    (hcc : ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * rtd m)
    (ht : ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4))
    (hbI : ∀ u ∈ transverseCube p c a₀, InBox ((N : ℝ) ^ 2) u)
    (hbI' : ∀ v ∈ transverseCube (p + ℓ) c' a₀', InBox ((N : ℝ) ^ 2) v)
    (hρ : ρ ≤ r₁) (hρ1 : ρ ≤ 1) (hCsl : Csl ≤ Cs ^ 2) (hCsl0 : 0 ≤ Csl)
    (hK₁ : Cc ≤ K₁) (hK₁' : (Cc / (aperture T / 2)) ^ 4 ≤ K₁) (hS : 1 ≤ Cs * Real.log N)
    (hlg : 0 ≤ Real.log N) (ht₀ : ‖M.t₀‖ ≤ T) (hℓ3 : (ℓ : ℝ) ≤ 3 * N)
    (hτN : 2 * (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9))
    (hη0 : 0 < η)
    (hη : unionConst hUnion * Clen * Real.log (2 + ((cubeFinset p c a₀ ×ˢ
      cubeFinset (p + ℓ) c' a₀').card : ℕ)) ≤ η)
    (hnum : 2 ^ (2 * q) * ((1 + Clen * (1 + ((m : ℝ) + 1) * ((1 + T) * ℓ))) ^ (2 * q) +
        2 * (1 + ((Nat.ceil (2 * q / 1)).factorial : ℝ)) * η ^ (2 * q)) *
        (2 * Real.exp (-(1 / τG) ^ 2)) ≤ 1)
    (hne : (transverseCube p c a₀).Nonempty) (hne' : (transverseCube (p + ℓ) c' a₀').Nonempty) :
    (∫⁻ ω, locRadius ω (transverseCube p c a₀) (transverseCube (p + ℓ) c' a₀')
        (W M K A ℓ) ^ q ∂M.P ≤
        ENNReal.ofReal (finalConst T (2 * (2 + T) ^ 2 * CS * Bq ^ 2 + 2 * CS) (2 * CS * C₃) (cS / 8)
          Bq (2 * CT + CPb + Real.logb 2 (1 + 2 * annuliSum m κT c₀ (cS / 8 / (16 * CP))) *
            (8 * CP)) q)) ∧
      ∫⁻ ω, locRadiusSlab ω p (p + ℓ) (transverseCube p c a₀) (transverseCube (p + ℓ) c' a₀')
          (W M K A ℓ) ^ q ∂M.P ≤
        ENNReal.ofReal (finalConst T (2 * (2 + T) ^ 2 * CS * Bq ^ 2 + 2 * CS) (2 * CS * C₃) (cS / 8)
          Bq (2 * CT + CPb + Real.logb 2 (1 + 2 * annuliSum m κT c₀ (cS / 8 / (16 * CP))) *
            (8 * CP)) q) := by
  classical
  have hprob := hM.probP
  have hcfg := hpack.cfg
  have hQ := hcfg.Q_pos
  have hW := hcfg.W_pos
  have hd0 := rtd_nonneg m
  have hℓ0 : 0 < ℓ := hℓ
  obtain ⟨P, hP⟩ := exists_isSubgradient M.μ (slopeVec t)
  set Wl := W M K A ℓ with hWl
  set Ql := Q M K A ℓ with hQl
  set Γ := Real.sqrt m * (b * Wl) + 2 * rtd m with hΓ
  set I := transverseCube p c a₀ with hI
  set I' := transverseCube (p + ℓ) c' a₀' with hI'
  have hsq := Real.sqrt_nonneg (m : ℝ)
  have hΓu : ∀ u ∈ I, ‖ofs t p c u‖ ≤ Γ := fun u hu => by
    have h1 := norm_ofs_left_le (t := t) ha₀ hu
    have h2 := mul_le_mul_of_nonneg_left ha₀b hsq
    linarith only [h1, h2, hΓ, hd0]
  have hΓv : ∀ v ∈ I', ‖ofs t p c v‖ ≤ Γ := fun v hv => by
    have h1 := norm_ofs_right_le ha₀' hcc hv
    have h2 := mul_le_mul_of_nonneg_left ha₀'b hsq
    have e : Real.sqrt ((m : ℝ) + 1) = rtd m := rfl
    rw [e] at h1
    linarith only [h1, h2, hΓ]
  have huv : ∀ u ∈ I, ∀ v ∈ I', u.1 = p ∧ v.1 = p + ℓ := fun u hu v hv => ⟨hu.1, hv.1⟩
  have hCvb : ∀ u ∈ I, ∀ v ∈ I', M.μ.1 (point v - point u) - ⟪P, point v - point u⟫ ≤
      (2 * (2 + T) ^ 2 * CS * Bq ^ 2 + 2 * CS) * Ql := fun u hu v hv =>
    cost_of_cubes hM hK hA hCS h24 hρ hρ1 hP hℓ ht hpack.hρ₁ ha₀ ha₀' ha₀b ha₀'b hcc
      (by simpa only [hΓ, rtd] using hpack.hΓW) hpack.hρ₂ ht₀ hu hv
  obtain ⟨Z, hZ, hZae⟩ := exists_upper hSum hM hK hA hTree hCT hCPb hshort hb hℓ0 hN1 hℓN ha₀ ha₀b
    ha₀' ha₀'b ht hP ha ha' hCvb
  have hc₂ : 0 < cS / 8 := by positivity
  obtain ⟨Y, hY, hYae⟩ := hcfg.exists_annuli hSum hCP hc₂ hprof hκℓ hℓN
  set Cann := Real.logb 2 (1 + 2 * annuliSum m κT c₀ (cS / 8 / (16 * CP))) * (8 * CP) with hCann
  have hS1 : 1 ≤ annuliSum m κT c₀ (cS / 8 / (16 * CP)) := by
    have h0 := tsum_pow_mul_exp_neg_pos (c := cS / 8 / (16 * CP)) (by positivity) (m + 1)
    have hc := hcfg.hc₀
    have : 0 ≤ (2 / c₀ + 3) * (3 * (κT : ℝ)) ^ m *
        ∑' n : ℕ, (n : ℝ) ^ (m + 1) * Real.exp (-(cS / 8 / (16 * CP)) * n) := by positivity
    rw [annuliSum]; linarith only [this]
  have hCann0 : 0 < Cann := by
    have h1 : 0 < Real.logb 2 (1 + 2 * annuliSum m κT c₀ (cS / 8 / (16 * CP))) :=
      Real.logb_pos one_lt_two (by linarith only [hS1])
    positivity
  have hΨ := isOs_psi hSum hQ (by positivity : 0 < 2 * CT + CPb) hCann0 hZ hY
  have hpen : ∀ x : Vertex m, Conf t p c ℓ (K₁ * (Cs * Real.log N) ^ 2)
      ((ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200)) x → ∀ β : ℕ, 1 ≤ β →
      (β : ℝ) * Wl ≤ ‖ofs t p c x‖ →
      ⟪P, point a' - point a⟫ + cS / 8 * (β : ℝ) ^ 2 * Ql - 2 * CS * C₃ * Ql ≤
        M.μ.1 (point x - point a) + M.μ.1 (point a' - point x) := fun x hx β hβ hβx =>
    hcfg.penalty hcS hCS h24 hP hpack.ht₁ hpack.hDr hτ3 hx hβ hβx
  have hup₁ : ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ →
      passageTimeReal ω a u + (walkCost ω γ : ℝ) + passageTimeReal ω v a' ≤
        ⟪P, point a' - point a⟫ + (2 * (2 + T) ^ 2 * CS * Bq ^ 2 + 2 * CS) * Ql + Z ω := by
    filter_upwards [hZae] with ω h u hu v hv γ hγ
    have e : (walkCost ω γ : ℝ) = passageTimeReal ω u v := by rw [passageTimeReal, hγ.2]
    rw [e]
    exact (h u hu v hv).1
  have hup₂ : ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v,
      IsSlabGeodesic ω p (p + ℓ) γ →
      passageTimeReal ω a u + (walkCost ω γ : ℝ) + passageTimeReal ω v a' ≤
        ⟪P, point a' - point a⟫ + (2 * (2 + T) ^ 2 * CS * Bq ^ 2 + 2 * CS) * Ql + Z ω := by
    filter_upwards [hZae] with ω h u hu v hv γ hγ
    have e : (walkCost ω γ : ℝ) = slabTimeReal ω u.1 v.1 u v := by
      rw [slabTimeReal, hu.1, hv.1, ← hγ.2.2]; rfl
    rw [e]
    exact (h u hu v hv).2
  have hS2 : 0 ≤ (Cs * Real.log N) ^ 2 := sq_nonneg _
  have hconf : ∀ ω ∈ G, ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v, γ.IsPath →
      (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + (Cs * Real.log N) ^ 2 →
      ∀ x ∈ γ.support, Conf t p c ℓ (K₁ * (Cs * Real.log N) ^ 2)
        ((ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200)) x := fun ω hω u hu v hv γ hγ hcost =>
    conf_path hM (hGcone ω hω) hCc hS hK₁ hK₁' hℓ0 hu.1 hv.1 hlg (hΓu u hu) (hΓv v hv) hpack.hτ
      hpack.hTT hpack.htlog hpack.hL hpack.hDD (hbI u hu) (hbI' v hv) hℓ3 hτN hγ hcost
  have hconf₁ : ∀ᵐ ω ∂M.P, ω ∈ G → ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v,
      IsGeodesic ω γ → ∀ x ∈ γ.support, Conf t p c ℓ (K₁ * (Cs * Real.log N) ^ 2)
        ((ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200)) x :=
    Filter.Eventually.of_forall fun ω hω u hu v hv γ hγ =>
      hconf ω hω u hu v hv γ hγ.1 (by
        have e : (walkCost ω γ : ℝ) = passageTimeReal ω u v := by rw [passageTimeReal, hγ.2]
        linarith only [e, hS2])
  have hconf₂ : ∀ᵐ ω ∂M.P, ω ∈ G → ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v,
      IsSlabGeodesic ω p (p + ℓ) γ → ∀ x ∈ γ.support, Conf t p c ℓ (K₁ * (Cs * Real.log N) ^ 2)
        ((ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200)) x :=
    Filter.Eventually.of_forall fun ω hω u hu v hv γ hγ =>
      hconf ω hω u hu v hv γ hγ.1 (by
        have h1 := hGslab ω hω u hu v hv
        rw [hu.1, hv.1, ← hγ.2.2] at h1
        have h2 := real_le_of_coe_le (by positivity) h1
        have h3 : Csl * Real.log N ^ 2 ≤ (Cs * Real.log N) ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right hCsl (sq_nonneg _)
        have e : ((passageTime ω u v : ℝ≥0) : ℝ) = passageTimeReal ω u v := rfl
        linarith only [h2, h3, e])
  -- off the good event
  set T₀ := cubeFinset p c a₀ ×ˢ cubeFinset (p + ℓ) c' a₀' with hT₀
  have hT₀ne : T₀.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    obtain ⟨v, hv⟩ := hne'
    exact ⟨(u, v), Finset.mem_product.2 ⟨mem_cubeFinset.2 hu, mem_cubeFinset.2 hv⟩⟩
  obtain ⟨Λ, hΛ, hΛae⟩ := exists_length_sup hUnion hClen T₀ hT₀ne
    (Q := fun uv ω x =>
      (∀ γ : (latticeGraph m).Walk uv.1 uv.2, IsGeodesic ω γ →
        (γ.length : ℝ) ≤ Clen * (1 + oneNorm (uv.2 - uv.1)) + x) ∧
      (∀ p q : ℤ, p + 2 ≤ q → p ≤ uv.1.1 → uv.1.1 ≤ q → p ≤ uv.2.1 → uv.2.1 ≤ q →
        ∀ γ : (latticeGraph m).Walk uv.1 uv.2, IsSlabGeodesic ω p q γ →
          (γ.length : ℝ) ≤ Clen * (1 + oneNorm (uv.2 - uv.1)) + x))
    (fun uv => hlen uv.1 uv.2)
    (fun uv ω x y hxy h => ⟨fun γ hγ => (h.1 γ hγ).trans (by linarith only [hxy]),
      fun p q h1 h2 h3 h4 h5 γ hγ => (h.2 p q h1 h2 h3 h4 h5 γ hγ).trans (by linarith only [hxy])⟩)
  have hlog2 : 0 < Real.log (2 + (T₀.card : ℝ)) :=
    Real.log_pos (by have := (Nat.cast_nonneg T₀.card : (0 : ℝ) ≤ T₀.card); linarith only [this])
  have hΛ' : CurvatureVariance.IsOs M.P 1 η Λ :=
    hΛ.mono_scale zero_le_one (mul_pos (mul_pos (unionConst_pos hUnion) hClen) hlog2) hη
  set L := Clen * (1 + ((m : ℝ) + 1) * ((1 + T) * ℓ)) with hL
  have hT1 : 0 ≤ T := (norm_nonneg _).trans ht₀
  have hL0 : 0 ≤ L := by positivity
  have hW1 := hcfg.one_le_W
  have hlenB : ∀ u ∈ I, ∀ v ∈ I', Clen * (1 + oneNorm (v - u)) ≤ L := fun u hu v hv => by
    have h1 := oneNorm_le_of_cubes (M := M) hℓ0 hu.1 hv.1 (hΓu u hu) (hΓv v hv) hpack.hτ hpack.hTT
    exact mul_le_mul_of_nonneg_left (by linarith only [h1]) hClen.le
  have hWB : ∀ B : ℝ, 0 ≤ B → ENNReal.ofReal B ≤ ENNReal.ofReal (Wl * B) := fun B hB =>
    ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hB hW1)
  have hmem : ∀ u ∈ I, ∀ v ∈ I', (u, v) ∈ T₀ := fun u hu v hv =>
    Finset.mem_product.2 ⟨mem_cubeFinset.2 hu, mem_cubeFinset.2 hv⟩
  have hBpos : ∀ ω, 0 ≤ L + max (Λ ω) 0 := fun ω => by positivity
  have hall₁ : ∀ᵐ ω ∂M.P, deviation (fun {u v} (γ : (latticeGraph m).Walk u v) => IsGeodesic ω γ)
      I I' ≤ ENNReal.ofReal (Wl * (L + max (Λ ω) 0)) := by
    filter_upwards [hΛae] with ω h
    refine (deviation_le_of_length fun u hu v hv γ hγ => ?_).trans (hWB _ (hBpos ω))
    have h1 := (h (u, v) (hmem u hu v hv)).1 γ hγ
    have h2 := hlenB u hu v hv
    have h3 := le_max_left (Λ ω) 0
    linarith only [h1, h2, h3]
  have hall₂ : ∀ᵐ ω ∂M.P, deviation
      (fun {u v} (γ : (latticeGraph m).Walk u v) => IsSlabGeodesic ω p (p + ℓ) γ)
      I I' ≤ ENNReal.ofReal (Wl * (L + max (Λ ω) 0)) := by
    filter_upwards [hΛae] with ω h
    refine (deviation_le_of_length fun u hu v hv γ hγ => ?_).trans (hWB _ (hBpos ω))
    have hℓ2 : p + 2 ≤ p + ℓ := by
      have h1 := hpack.hL
      have h2 := hcfg.hL
      have h3 : (1 : ℝ) ≤ rtd m := by
        unfold rtd
        exact Real.one_le_sqrt.mpr (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
      have h4 : (2 : ℝ) ≤ ℓ := by linarith only [h2, h3, hcfg.hL₀]
      have h5 : 2 ≤ ℓ := by exact_mod_cast h4
      omega
    have h1 := (h (u, v) (hmem u hu v hv)).2 p (p + ℓ) hℓ2 hu.1.ge
      (by change u.1 ≤ _; rw [hu.1]; omega) (by change _ ≤ v.1; rw [hv.1]; omega) hv.1.le γ hγ
    have h2 := hlenB u hu v hv
    have h3 := le_max_left (Λ ω) 0
    linarith only [h1, h2, h3]
  have hCv0 : 0 ≤ 2 * (2 + T) ^ 2 * CS * Bq ^ 2 + 2 * CS := by positivity
  have hCp0 : 0 ≤ 2 * CS * C₃ := by positivity
  have hτ0 : 0 < 2 * CT + CPb + Cann := by positivity
  have hLW := hpack.hLW
  refine ⟨?_, ?_⟩
  · exact hcfg.moment_geo (geo := fun ω _ _ γ => IsGeodesic ω γ) hSum hc₂ hCv0 hCp0 hpen hYae hup₁
      hconf₁ hΓu hΓv huv hpack.hΓW hLW hBq hτ0 hη0 hL0 hq hΨ hΛ' hG hall₁ hnum
  · exact hcfg.moment_geo (geo := fun ω _ _ γ => IsSlabGeodesic ω p (p + ℓ) γ) hSum hc₂ hCv0 hCp0
      hpen hYae hup₂ hconf₂ hΓu hΓv huv hpack.hΓW hLW hBq hτ0 hη0 hL0 hq hΨ hΛ' hG hall₂ hnum

end CurvatureVariance.Paper.Localization.Loc
