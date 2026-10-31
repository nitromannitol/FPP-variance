/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocFinal
public import CurvatureVariance.Paper.Proofs.Localization.LocNumeric
public import CurvatureVariance.Paper.Proofs.Geometry.Cone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.Moments.Parent
public import CurvatureVariance.Paper.Proofs.Moments.Shear
import CurvatureVariance.Paper.Proofs.Localization.Common
import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet

/-!
# Lemma `lem:localization`: the pieces at fixed `N`, `A`, `ℓ`

* `Loc.TreeAt`: Lemma `lem:tree` at fixed `N`, `A`.
* `W_le_eight_mul`, `slope_le_tree`: the two facts that Lemma `lem:tree` at the length `ℓ/16` with
  `8b` needs: `(ℓQ_ℓ)^{1/2} ≤ 8((ℓ/16)Q_{ℓ/16})^{1/2}`, and a slope `|t − t₀| ≤ ℓ^{δ/100−1/4}` is
  within `(4/5)(ℓ/16)^{δ/100−1/4}`.
* `end_left`, `end_right`: the points `a`, `a'`.
* `exists_upper`: the upper bound in the proof of Lemma `lem:localization`.
* `conf_path`: the first change, along a path of passage time at most `T(u, v) + S²`.
* `isOs_psi`, `Cfg.moment_geo`: the moment bound for one family of paths.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts
  CurvatureVariance.Paper.Proofs.Geometry CurvatureVariance.Infra.Os Radius

variable {m : ℕ}

/-- Lemma `lem:tree` at fixed `N`, `A`. -/
def TreeAt (M : Model m) (K : ℕ) (A : ℝ) (N : ℕ) (b C : ℝ) : Prop :=
  ∀ s : ℝ, Real.sqrt N / 16 ≤ s → s ≤ N / 2 → ∀ (p : ℤ) (c t : EuclideanSpace ℝ (Fin m)) (a₀ : ℝ),
    0 ≤ a₀ → a₀ ≤ b * W M K A s → ‖t - M.t₀‖ ≤ 4 / 5 * s ^ (M.δ / 100 - 1 / 4) →
    ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P → ∀ a a' : Vertex m,
    ‖point a - (WithLp.toLp 2 ((p : ℝ), c) - s • slopeVec t)‖ ≤ Real.sqrt ((m : ℝ) + 1) →
    ‖point a' - (WithLp.toLp 2 ((p : ℝ), c) + s • slopeVec t)‖ ≤ Real.sqrt ((m : ℝ) + 1) →
    ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (C * Q M K A s) X ∧ ∀ᵐ ω ∂M.P,
      ∀ u ∈ thicken (transverseCube p c a₀) t (s / 64),
        passageTimeReal ω a u - inner ℝ P (point u - point a) ≤ X ω ∧
        passageTimeReal ω u a' - inner ℝ P (point a' - point u) ≤ X ω

/-- `(ℓQ_ℓ)^{1/2} ≤ 8((ℓ/16)Q_{ℓ/16})^{1/2}`, the bound of the proof of Proposition `prop:profiles`
for `s = ℓ`. -/
theorem W_le_eight_mul {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 0 ≤ A) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : W M K A ℓ ≤ 8 * W M K A (ℓ / 16) := by
  obtain ⟨hq1, hq2⟩ := Localization.Q_exponent_bounds hM hK
  set e := (1 : ℝ) / 2 - M.δ / K with he
  have h16 : (16 : ℝ) ^ e ≤ 4 := by
    calc (16 : ℝ) ^ e ≤ 16 ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
      _ = 4 := by
          rw [← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
  have hs : 0 ≤ ℓ / 16 := by positivity
  have hQ : Q M K A ℓ ≤ 4 * Q M K A (ℓ / 16) := by
    have e1 : ℓ = 16 * (ℓ / 16) := by ring
    unfold Q
    rw [← he]
    conv_lhs => rw [e1, Real.mul_rpow (by norm_num) hs]
    have h0 : 0 ≤ A * (ℓ / 16) ^ e := by positivity
    have := mul_le_mul_of_nonneg_right h16 h0
    linarith only [this]
  have h1 : ℓ * Q M K A ℓ ≤ 8 ^ 2 * (ℓ / 16 * Q M K A (ℓ / 16)) := by
    have := mul_le_mul_of_nonneg_left hQ hℓ
    linarith only [this]
  unfold W
  calc Real.sqrt (ℓ * Q M K A ℓ) ≤ Real.sqrt (8 ^ 2 * (ℓ / 16 * Q M K A (ℓ / 16))) :=
        Real.sqrt_le_sqrt h1
    _ = 8 * Real.sqrt (ℓ / 16 * Q M K A (ℓ / 16)) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- The slope of the pair is within the range of Lemma `lem:tree` at the length `ℓ/16`. -/
theorem slope_le_tree {δ : ℝ} (hδ1 : δ ≤ 1) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ℓ ^ (δ / 100 - 1 / 4) ≤ 4 / 5 * (ℓ / 16) ^ (δ / 100 - 1 / 4) := by
  have h3 := four_thirds_le_rpow hδ1
  have h2 : (ℓ / 16) ^ (δ / 100 - 1 / 4) =
      ℓ ^ (δ / 100 - 1 / 4) * (16 : ℝ) ^ (-(δ / 100 - 1 / 4)) := by
    rw [Real.div_rpow hℓ.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]
  have h4 : 0 ≤ ℓ ^ (δ / 100 - 1 / 4) := Real.rpow_nonneg hℓ.le _
  rw [h2]
  nlinarith only [h3, h4]

/-- The point `a`: its first coordinate and its offset. -/
theorem end_left {t c : EuclideanSpace ℝ (Fin m)} {p : ℤ} {s T : ℝ} (ht : ‖t‖ ≤ T) {a : Vertex m}
    (ha : ‖point a - (basePt p c - s • slopeVec t)‖ ≤ rtd m) :
    |(a.1 : ℝ) - ((p : ℝ) - s)| ≤ rtd m ∧ ‖ofs t p c a‖ ≤ (1 + T) * rtd m := by
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  constructor
  · have h := (abs_fst_le_norm _).trans ha
    simpa [slopeVec] using h
  · have e : ofs t p c a = transOff t (point a - (basePt p c - s • slopeVec t)) := by
      have e2 : point a - basePt p c = (point a - (basePt p c - s • slopeVec t)) +
          (-s) • slopeVec t := by
        rw [neg_smul]; abel
      rw [ofs, e2, transOff_add, transOff_smul_slopeVec, add_zero]
    rw [e]
    exact (norm_transOff_le ht _).trans (mul_le_mul_of_nonneg_left ha (by positivity))

/-- The point `a'`: its first coordinate and its offset. -/
theorem end_right {t c c' : EuclideanSpace ℝ (Fin m)} {p : ℤ} {ℓ : ℕ} {s T : ℝ} (ht : ‖t‖ ≤ T)
    (hcc : ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * rtd m) {a' : Vertex m}
    (ha : ‖point a' - (basePt (p + ℓ) c' + s • slopeVec t)‖ ≤ rtd m) :
    |(a'.1 : ℝ) - ((p : ℝ) + ℓ + s)| ≤ rtd m ∧ ‖ofs t p c a'‖ ≤ (3 + T) * rtd m := by
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  constructor
  · have h := (abs_fst_le_norm _).trans ha
    simpa [slopeVec, add_assoc] using h
  · have e : ofs t p c a' = transOff t (point a' - (basePt (p + ℓ) c' + s • slopeVec t)) +
        (c' - c - (ℓ : ℝ) • t) := by
      have e2 : point a' - basePt p c = (point a' - (basePt (p + ℓ) c' + s • slopeVec t)) +
          (s • slopeVec t + (basePt (p + ℓ) c' - basePt p c)) := by abel
      have e3 : transOff t (basePt (p + ℓ) c' - basePt p c) = c' - c - (ℓ : ℝ) • t := by
        simp [transOff]
      rw [ofs, e2, transOff_add, transOff_add, transOff_smul_slopeVec, zero_add, e3]
    rw [e]
    have h1 := norm_transOff_le ht (point a' - (basePt (p + ℓ) c' + s • slopeVec t))
    have h2 := mul_le_mul_of_nonneg_left ha (show 0 ≤ 1 + T by positivity)
    refine (norm_add_le _ _).trans ?_
    have e4 : (3 + T) * rtd m = (1 + T) * rtd m + 2 * rtd m := by ring
    linarith only [h1, h2, hcc, e4]

/-- The rounded point is within `√d`. -/
theorem round_le (z : Pt m) :
    ‖point (Moments.roundVertex z) - z‖ ≤ Real.sqrt ((m : ℝ) + 1) := by
  have h := Moments.norm_point_roundVertex_sub_le z
  have h0 : 0 ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
  linarith only [h, h0]

/-- **The upper bound** (the proof of Lemma `lem:localization`): one
`O₁(C(b)Q_ℓ)` variable `Z` with `T(a, u) + T(u, v) + T(v, a') ≤ ζ_t·(a' − a) + Cv Q_ℓ + Z`, and the
same with `T_P`, uniformly in `u ∈ I`, `v ∈ I'`, from Lemma `lem:tree` at the length `ℓ/16` with
`8b`, Proposition `prop:profiles`, and `Cv`, equation `eq:support`. -/
theorem exists_upper (hSum : SignedOsSumStatement.{0, 0}) {M : Model m} (hM : M.Standing) {K : ℕ}
    (hK : 10 ^ 4 ≤ K) {A : ℝ} (hA : 1 ≤ A) {N ℓ : ℕ} {b CT CP Cv a₀ a₀' : ℝ}
    {t c c' : EuclideanSpace ℝ (Fin m)} {p : ℤ} {P : Pt m} {a a' : Vertex m}
    (hTree : TreeAt M K A N (8 * b) CT) (hCT : 0 < CT) (hCP : 0 < CP)
    (hshort : ShortConclusion M K A ℓ CP t (transverseCube p c a₀)
      (transverseCube (p + ℓ) c' a₀')) (hb : 0 ≤ b) (hℓ : 0 < ℓ)
    (hN1 : Real.sqrt N ≤ ℓ) (hN2 : ℓ ≤ N) (ha₀ : 0 ≤ a₀) (ha₀b : a₀ ≤ b * W M K A ℓ)
    (ha₀' : 0 ≤ a₀') (ha₀'b : a₀' ≤ b * W M K A ℓ)
    (ht : ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4)) (hP : IsSubgradient M.μ (slopeVec t) P)
    (ha : ‖point a - (basePt p c - ((ℓ : ℝ) / 16) • slopeVec t)‖ ≤ rtd m)
    (ha' : ‖point a' - (basePt (p + ℓ) c' + ((ℓ : ℝ) / 16) • slopeVec t)‖ ≤ rtd m)
    (hCv : ∀ u ∈ transverseCube p c a₀, ∀ v ∈ transverseCube (p + ℓ) c' a₀',
      M.μ.1 (point v - point u) - ⟪P, point v - point u⟫ ≤ Cv * Q M K A ℓ) :
    ∃ Z : Config m → ℝ, CurvatureVariance.IsOs M.P 1 ((2 * CT + CP) * Q M K A ℓ) Z ∧ ∀ᵐ ω ∂M.P,
      ∀ u ∈ transverseCube p c a₀, ∀ v ∈ transverseCube (p + ℓ) c' a₀',
        passageTimeReal ω a u + passageTimeReal ω u v + passageTimeReal ω v a' ≤
            ⟪P, point a' - point a⟫ + Cv * Q M K A ℓ + Z ω ∧
          passageTimeReal ω a u + slabTimeReal ω u.1 v.1 u v + passageTimeReal ω v a' ≤
            ⟪P, point a' - point a⟫ + Cv * Q M K A ℓ + Z ω := by
  have hprob := hM.probP
  have hA0 : (0 : ℝ) ≤ A := by linarith only [hA]
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  set s : ℝ := (ℓ : ℝ) / 16 with hs
  have hs0 : 0 < s := by positivity
  have hs1 : Real.sqrt N / 16 ≤ s := div_le_div_of_nonneg_right hN1 (by norm_num)
  have hs2 : s ≤ N / 2 := by
    have : (ℓ : ℝ) ≤ N := by exact_mod_cast hN2
    linarith only [this, hs, hℓ0]
  have hWs := W_le_eight_mul hM hK hA0 hℓ0.le
  rw [← hs] at hWs
  have hab : ∀ a₁ : ℝ, a₁ ≤ b * W M K A ℓ → a₁ ≤ 8 * b * W M K A s := fun a₁ h => by
    have := mul_le_mul_of_nonneg_left hWs hb
    linarith only [this, h]
  have hts : ‖t - M.t₀‖ ≤ 4 / 5 * s ^ (M.δ / 100 - 1 / 4) :=
    ht.trans (slope_le_tree hM.delta_le_one hℓ0)
  obtain ⟨X₁, hX₁, hae₁⟩ := hTree s hs1 hs2 p c t a₀ ha₀ (hab _ ha₀b) hts P hP a
    (Moments.roundVertex (basePt p c + s • slopeVec t)) ha
    (round_le _)
  obtain ⟨X₂, hX₂, hae₂⟩ := hTree s hs1 hs2 (p + ℓ) c' t a₀' ha₀' (hab _ ha₀'b) hts P hP
    (Moments.roundVertex (basePt (p + ℓ) c' - s • slopeVec t)) a'
    (round_le _) ha'
  obtain ⟨X₃, hX₃, hae₃⟩ := hshort
  have hQ : 0 < Q M K A ℓ := Localization.Q_pos (by linarith only [hA]) hℓ0
  have hQs : 0 < Q M K A s := Localization.Q_pos (by linarith only [hA]) hs0
  have hQle : Q M K A s ≤ Q M K A ℓ :=
    Localization.Q_le_Q hM hK hA0 hs0.le (by linarith only [hs, hℓ0])
  have h12 := isOs_add_of hSum le_rfl hX₁ hX₂ (by positivity) (by positivity)
  have h123 := isOs_add_of hSum le_rfl h12 hX₃ (by positivity) (by positivity)
  refine ⟨fun ω => X₁ ω + X₂ ω + X₃ ω, h123.mono_scale zero_le_one (by positivity) ?_, ?_⟩
  · nlinarith only [hQle, hCT]
  have hr : 0 ≤ s / 64 := by positivity
  filter_upwards [hae₁, hae₂, hae₃] with ω h₁ h₂ h₃ u hu v hv
  have b₁ := (h₁ u (mem_thicken_of_mem hr hu)).1
  have b₂ := (h₂ v (mem_thicken_of_mem hr hv)).2
  have hu' := mem_thicken_of_mem (t := t) (show (0 : ℝ) ≤ (ℓ : ℝ) / 1024 by positivity) hu
  have hv' := mem_thicken_of_mem (t := t) (show (0 : ℝ) ≤ (ℓ : ℝ) / 1024 by positivity) hv
  have b₃ := abs_le.1 (h₃.1 u hu' v hv')
  have b₄ := abs_le.1 (h₃.2 u hu v hv)
  exact ⟨upper_bound_cost b₁ b₂ (by linarith only [b₃.2]) (hCv u hu v hv),
    upper_bound_cost b₁ b₂ (by linarith only [b₄.2]) (hCv u hu v hv)⟩

/-- The slope `t'` of `v − u`, from the offsets of `u` and `v`. -/
theorem slope_near {M : Model m} {Γ τ T : ℝ} {ℓ : ℕ} {t c : EuclideanSpace ℝ (Fin m)} {p : ℤ}
    {u v : Vertex m} (hℓ : 0 < ℓ) (hu1 : u.1 = p) (hv1 : v.1 = p + ℓ)
    (hΓu : ‖ofs t p c u‖ ≤ Γ) (hΓv : ‖ofs t p c v‖ ≤ Γ)
    (hτ : ‖t - M.t₀‖ + 2 * Γ / ℓ ≤ τ) (hTT : ‖M.t₀‖ + τ ≤ T) :
    point v - point u = (ℓ : ℝ) • slopeVec ((ℓ : ℝ)⁻¹ • transversePoint (v.2 - u.2)) ∧
      ‖(ℓ : ℝ)⁻¹ • transversePoint (v.2 - u.2) - M.t₀‖ ≤ τ ∧
      ‖(ℓ : ℝ)⁻¹ • transversePoint (v.2 - u.2)‖ ≤ T := by
  set t' := (ℓ : ℝ)⁻¹ • transversePoint (v.2 - u.2) with ht'
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have huv : point v - point u = (ℓ : ℝ) • slopeVec t' :=
    Proofs.ShortLengths.point_sub_eq_smul_slopeVec hℓ (by rw [hv1, hu1])
  have hsl := smul_slope_sub_eq (t := t) (p := p) (c := c) huv
  have hdiff : ‖t' - t‖ ≤ 2 * Γ / ℓ := by
    refine (norm_sub_le_of_smul hℓ0 hsl).trans (div_le_div_of_nonneg_right ?_ hℓ0.le)
    exact (norm_sub_le _ _).trans (by linarith only [hΓu, hΓv])
  have htau : ‖t' - M.t₀‖ ≤ τ :=
    (norm_sub_le_norm_sub_add_norm_sub t' t M.t₀).trans (by linarith only [hdiff, hτ])
  refine ⟨huv, htau, ?_⟩
  have := norm_le_norm_sub_add t' M.t₀
  linarith only [this, htau, hTT]

/-- **The first change along one path** of passage time at most `T(u, v) + S²`, from Lemma
`lem:cone` on the good event. -/
theorem conf_path {M : Model m} (hM : M.Standing) {C S K₁ T τ Γ D : ℝ} {N ℓ : ℕ}
    {t c : EuclideanSpace ℝ (Fin m)} {p : ℤ} {u v : Vertex m} {ω : Config m}
    (hcone : ConeAt M C S N ω) (hC : 0 < C) (hS : 1 ≤ S)
    (hK₁ : C ≤ K₁) (hK₁' : (C / (aperture T / 2)) ^ 4 ≤ K₁) (hℓ : 0 < ℓ)
    (hu1 : u.1 = p) (hv1 : v.1 = p + ℓ) (hlg : 0 ≤ Real.log N)
    (hΓu : ‖ofs t p c u‖ ≤ Γ) (hΓv : ‖ofs t p c v‖ ≤ Γ)
    (hτ : ‖t - M.t₀‖ + 2 * Γ / ℓ ≤ τ) (hTT : ‖M.t₀‖ + τ ≤ T)
    (htlog : C * (τ ^ (1 + M.δ / 2) * Real.log N) ≤ aperture T / 2)
    (hL : K₁ * S ^ 2 ≤ ℓ)
    (hDD : 5 * Γ + coneRadius M.δ C K₁ T S (Real.log N) ℓ τ ≤ D)
    (hbu : InBox ((N : ℝ) ^ 2) u) (hbv : InBox ((N : ℝ) ^ 2) v) (hℓ3 : (ℓ : ℝ) ≤ 3 * N)
    (hτN : τ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9)) {γ : (latticeGraph m).Walk u v} (hγ : γ.IsPath)
    (hcost : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2) :
    ∀ z ∈ γ.support, Conf t p c ℓ (K₁ * S ^ 2) D z := by
  obtain ⟨huv, htau, -⟩ := slope_near (M := M) hℓ hu1 hv1 hΓu hΓv hτ hTT
  intro z hz
  obtain ⟨h1, h2⟩ := hcone ℓ _ u v hbu hbv huv hℓ hℓ3 (htau.trans hτN) γ hγ hcost z hz
  exact conf_of_cone hM hC hS hK₁ hK₁' hℓ hu1 hv1 hlg hΓu hΓv hτ hTT htlog hL hDD h1 h2

/-- `Ψ = (Z₊ + Y₊)/Q ≤ O₁(θ₁ + θ₂)`. -/
theorem isOs_psi (hSum : SignedOsSumStatement.{0, 0}) {P : Measure (Config m)}
    [IsProbabilityMeasure P] {Z Y : Config m → ℝ} {θ₁ θ₂ Q : ℝ} (hQ : 0 < Q) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) (hZ : CurvatureVariance.IsOs P 1 (θ₁ * Q) Z) (hY : CurvatureVariance.IsOs P 1 (θ₂ * Q) Y) :
    CurvatureVariance.IsOs P 1 (θ₁ + θ₂) (fun ω => (max (Z ω) 0 + max (Y ω) 0) / Q) := by
  have h := isOs_add_of hSum le_rfl (Moments.Parent.isOs_max_zero hZ)
    (Moments.Parent.isOs_max_zero hY) (by positivity) (by positivity)
  have hi : 0 < Q⁻¹ := inv_pos.2 hQ
  have h2 := (isOs_mul_iff (P := P) (s := 1) hi).2 h
  have e : Q⁻¹ * (θ₁ * Q + θ₂ * Q) = θ₁ + θ₂ := by field_simp
  rw [e] at h2
  have e2 : (fun ω => Q⁻¹ * (max (Z ω) 0 + max (Y ω) 0)) =
      fun ω => (max (Z ω) 0 + max (Y ω) 0) / Q := by
    funext ω; rw [div_eq_inv_mul]
  rwa [e2] at h2

section Moment

variable {M : Model m} {K : ℕ} {A : ℝ} {ℓ : ℕ} {t : EuclideanSpace ℝ (Fin m)} {p : ℤ}
  {c : EuclideanSpace ℝ (Fin m)} {a a' : Vertex m} {T c₀ C₀ D L₀ : ℝ} {κT : ℕ}

/-- `1 ≤ W`, from `Cfg`. -/
theorem Cfg.one_le_W (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) : 1 ≤ W M K A ℓ := by
  have h1 := h.hW
  have h2 := rtd_nonneg m
  have h3 := h.hT
  have : 0 ≤ (1 + T) * rtd m := by positivity
  linarith only [h1, this]

/-- **The moment bound for one family of paths**: `Cfg.deviation_le_good` on the good event,
`moment_of_bounds` off it. -/
theorem Cfg.moment_geo (hSum : SignedOsSumStatement.{0, 0})
    (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {I I' : Set (Vertex m)} {G : Set (Config m)}
    {geo : Config m → ∀ {u v : Vertex m}, (latticeGraph m).Walk u v → Prop}
    {P : Pt m} {Z Y Λ : Config m → ℝ} {c₂ Cv Cp Γ B τ η τG L q : ℝ}
    (hc₂ : 0 < c₂) (hCv : 0 ≤ Cv) (hCp : 0 ≤ Cp)
    (hpen : ∀ x : Vertex m, Conf t p c ℓ L₀ D x → ∀ β : ℕ, 1 ≤ β →
      (β : ℝ) * W M K A ℓ ≤ ‖ofs t p c x‖ →
      ⟪P, point a' - point a⟫ + c₂ * (β : ℝ) ^ 2 * Q M K A ℓ - Cp * Q M K A ℓ ≤
        M.μ.1 (point x - point a) + M.μ.1 (point a' - point x))
    (hY : ∀ᵐ ω ∂M.P, ∀ x : Vertex m, Conf t p c ℓ L₀ D x → 1 ≤ annulus t p c (W M K A ℓ) x →
      M.μ.1 (point x - point a) + M.μ.1 (point a' - point x) -
          (passageTimeReal ω a x + passageTimeReal ω x a') -
          c₂ / 2 * ((annulus t p c (W M K A ℓ) x : ℕ) : ℝ) ^ 2 * Q M K A ℓ ≤ Y ω)
    (hup : ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v, geo ω γ →
      passageTimeReal ω a u + (walkCost ω γ : ℝ) + passageTimeReal ω v a' ≤
        ⟪P, point a' - point a⟫ + Cv * Q M K A ℓ + Z ω)
    (hconf : ∀ᵐ ω ∂M.P, ω ∈ G → ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v, geo ω γ →
      ∀ x ∈ γ.support, Conf t p c ℓ L₀ D x)
    (hΓu : ∀ u ∈ I, ‖ofs t p c u‖ ≤ Γ) (hΓv : ∀ v ∈ I', ‖ofs t p c v‖ ≤ Γ)
    (huv : ∀ u ∈ I, ∀ v ∈ I', u.1 = p ∧ v.1 = p + ℓ) (hΓW : Γ ≤ B * W M K A ℓ)
    (hLW : L₀ ≤ W M K A ℓ) (hB : 0 ≤ B) (hτ : 0 < τ) (hη : 0 < η) (hL : 0 ≤ L) (hq : 1 ≤ q)
    (hΨ : CurvatureVariance.IsOs M.P 1 τ fun ω => (max (Z ω) 0 + max (Y ω) 0) / Q M K A ℓ)
    (hΛ : CurvatureVariance.IsOs M.P 1 η Λ) (hG : CurvatureVariance.IsOs M.P 2 τG (Gᶜ.indicator fun _ => (1 : ℝ)))
    (hall : ∀ᵐ ω ∂M.P, deviation (geo ω) I I' ≤
      ENNReal.ofReal (W M K A ℓ * (L + max (Λ ω) 0)))
    (hnum : 2 ^ (2 * q) * ((1 + L) ^ (2 * q) +
        2 * (1 + ((Nat.ceil (2 * q / 1)).factorial : ℝ)) * η ^ (2 * q)) *
        (2 * Real.exp (-(1 / τG) ^ 2)) ≤ 1) :
    ∫⁻ ω, (1 + deviation (geo ω) I I' / ENNReal.ofReal (W M K A ℓ)) ^ q ∂M.P ≤
      ENNReal.ofReal (2 ^ q * (2 * (1 + ((Nat.ceil (q / 2)).factorial : ℝ)) *
        (2 * (1 + ((1 + T) * (2 + Real.sqrt (2 * (Cv + Cp) / c₂)) + B)) +
          (1 + T) * Real.sqrt (2 / c₂) * Real.sqrt τ) ^ q + 1)) := by
  have hprob := h.hM.probP
  have hT := h.hT
  have hQ := h.Q_pos
  have hd := h.deviation_le_good hc₂ hCv hCp hpen hY hup hconf hΓu hΓv huv hΓW hLW
  have hT1 : 0 < 1 + T := by linarith only [hT]
  have hA₁ : 0 < (1 + T) * Real.sqrt (2 / c₂) := by positivity
  have hA₀ : 0 ≤ (1 + T) * (2 + Real.sqrt (2 * (Cv + Cp) / c₂)) + B := by positivity
  refine moment_of_bounds hSum (Ψ := fun ω => (max (Z ω) 0 + max (Y ω) 0) / Q M K A ℓ)
    h.one_le_W hτ hη hA₀ hA₁ hL hq hΨ hΛ hG ?_ hall hnum
  filter_upwards [hd] with ω hω hmem
  have hΨ0 : 0 ≤ (max (Z ω) 0 + max (Y ω) 0) / Q M K A ℓ := by positivity
  rw [max_eq_left hΨ0]
  exact hω hmem

end Moment

end CurvatureVariance.Paper.Localization.Loc
