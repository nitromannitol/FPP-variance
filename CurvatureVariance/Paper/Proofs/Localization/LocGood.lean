/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocAnnuli
public import CurvatureVariance.Paper.Proofs.Localization.LocConfine
import CurvatureVariance.Paper.Proofs.Geometry.TurningArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# Lemma `lem:localization` on the good event

The end of the second change in the proof of Lemma `lem:localization`:

* `conf_of_cone`: the first change along one path, from the conclusion of Lemma `lem:cone`;
* `upper_bound_cost`: the upper bound in the proof of Lemma `lem:localization`, at one outcome;
* `passageTime_through_le`, `le_sqrt_of_sq_le`: for a confined vertex `x` of a path `π` of the
  upper bound, in the annulus `β ≥ 1`, `T(a, x) + T(x, a') ≤ T(a, u) + T(π) + T(v, a')` gives
  `(c/2)β²Q ≤ CQ + Z + Y`, for the two `O₁` variables of the upper bound and of the union over the
  thickenings, hence a bound on `β`;
* `Cfg.deviation_le_good`: on the good event, `sup dist(x, [u, v]) ≤ W (A₀ + A₁ √Ψ₊)`, which is
  `R 1_𝒢 ≤ O₂(C(b))` once `Ψ ≤ O₁(C(b))`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts
  CurvatureVariance.Paper.Proofs.Geometry Radius

variable {m : ℕ}

/-- The first change along one path, from the conclusion of Lemma `lem:cone` at the slope of
`v − u`, with `‖t' − t₀‖ ≤ ‖t − t₀‖ + 2Γ/ℓ ≤ τ`. -/
theorem conf_of_cone {M : Model m} (hM : M.Standing) {C S K₁ T τ Γ D : ℝ} {N ℓ : ℕ}
    {t c : EuclideanSpace ℝ (Fin m)} {p : ℤ} {u v : Vertex m} (hC : 0 < C) (hS : 1 ≤ S)
    (hK₁ : C ≤ K₁) (hK₁' : (C / (aperture T / 2)) ^ 4 ≤ K₁) (hℓ : 0 < ℓ)
    (hu1 : u.1 = p) (hv1 : v.1 = p + ℓ) (hlg : 0 ≤ Real.log N)
    (hΓu : ‖ofs t p c u‖ ≤ Γ) (hΓv : ‖ofs t p c v‖ ≤ Γ)
    (hτ : ‖t - M.t₀‖ + 2 * Γ / ℓ ≤ τ) (hTT : ‖M.t₀‖ + τ ≤ T)
    (htlog : C * (τ ^ (1 + M.δ / 2) * Real.log N) ≤ aperture T / 2)
    (hL : K₁ * S ^ 2 ≤ ℓ)
    (hDD : 5 * Γ + coneRadius M.δ C K₁ T S (Real.log N) ℓ τ ≤ D)
    {z : Vertex m}
    (hcb₁ : ConeBound M C S N ((ℓ : ℝ)⁻¹ • transversePoint (v.2 - u.2)) (point v - point z))
    (hcb₂ : ConeBound M C S N ((ℓ : ℝ)⁻¹ • transversePoint (v.2 - u.2)) (point z - point u)) :
    Conf t p c ℓ (K₁ * S ^ 2) D z := by
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
  have htT : ‖t'‖ ≤ T := by
    have := norm_le_norm_sub_add t' M.t₀
    linarith only [this, htau, hTT]
  obtain ⟨h1, h2, h3⟩ := cone_confine hM hC hS hK₁ hK₁' htT hlg htau htlog huv hcb₁ hcb₂
  rw [hu1] at h1
  rw [hv1] at h2
  push_cast at h2
  refine ⟨h1, h2, ?_⟩
  have h4 := ofs_le_of_confine (t := t) (p := p) (c := c) hℓ huv hΓu hΓv hL (by rw [hu1]; exact h1)
    (by rw [hv1]; push_cast; exact h2) h3
  linarith only [h4, hDD]

/-- **The upper bound** at one outcome: `T(a, u) + cost + T(v, a') ≤ ζ_t·(a' − a) + C + X₁ + X₂ +
X₃`, from Lemma `lem:tree` (`X₁`, `X₂`), Proposition `prop:profiles` (`X₃`), and
equation `eq:support` (`Cv`). -/
theorem upper_bound_cost {μ : PtNorm m} {P : Pt m} {ω : Config m} {a a' u v : Vertex m}
    {cost X₁ X₂ X₃ Cv : ℝ} (h1 : passageTimeReal ω a u - ⟪P, point u - point a⟫ ≤ X₁)
    (h2 : passageTimeReal ω v a' - ⟪P, point a' - point v⟫ ≤ X₂)
    (h3 : cost ≤ μ.1 (point v - point u) + X₃)
    (hCv : μ.1 (point v - point u) - ⟪P, point v - point u⟫ ≤ Cv) :
    passageTimeReal ω a u + cost + passageTimeReal ω v a' ≤
      ⟪P, point a' - point a⟫ + Cv + (X₁ + X₂ + X₃) := by
  have hsplit : ⟪P, point a' - point a⟫ = ⟪P, point a' - point v⟫ + ⟪P, point v - point u⟫ +
      ⟪P, point u - point a⟫ := by
    rw [← inner_add_right, ← inner_add_right]; congr 1; abel
  linarith only [h1, h2, h3, hCv, hsplit]

/-- `T(a, x) + T(x, a')` is at most the sum of `T(a, u)`, the cost of a walk from `u` to `v` through
`x`, and `T(v, a')`. -/
theorem passageTime_through_le (ω : Config m) {a a' u v x : Vertex m}
    (γ : (latticeGraph m).Walk u v) (hx : x ∈ γ.support) :
    passageTimeReal ω a x + passageTimeReal ω x a' ≤
      passageTimeReal ω a u + (walkCost ω γ : ℝ) + passageTimeReal ω v a' := by
  have h1 := passageTime_add_le_walkCost ω γ hx
  have h2 := Moments.passageTimeReal_triangle ω a u x
  have h3 := Moments.passageTimeReal_triangle ω x v a'
  linarith only [h1, h2, h3]

/-- The bound of the annulus: `β ≤ √(2(C₁ + C₂)/c) + √(2/c) √Ψ` from
`(c/2)β² ≤ C₁ + C₂ + Ψ`. -/
theorem le_sqrt_of_sq_le {β c C Ψ : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hΨ : 0 ≤ Ψ)
    (h : c / 2 * β ^ 2 ≤ C + Ψ) :
    β ≤ Real.sqrt (2 * C / c) + Real.sqrt (2 / c) * Real.sqrt Ψ := by
  have h1 : β ^ 2 ≤ 2 * C / c + 2 / c * Ψ := by
    have e : 2 * C / c + 2 / c * Ψ = 2 / c * (C + Ψ) := by ring
    rw [e, ← div_le_iff₀' (by positivity)]
    have e2 : β ^ 2 / (2 / c) = c / 2 * β ^ 2 := by field_simp
    rw [e2]; exact h
  have h2 : β ≤ Real.sqrt (2 * C / c + 2 / c * Ψ) := Real.le_sqrt_of_sq_le h1
  have h3 := Proofs.Geometry.sqrt_add_le_add_sqrt (a := 2 * C / c) (b := 2 / c * Ψ)
    (by positivity) (by positivity)
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / c) Ψ] at h3
  linarith only [h2, h3]

section Deviation

variable {M : Model m} {K : ℕ} {A : ℝ} {ℓ : ℕ} {t : EuclideanSpace ℝ (Fin m)} {p : ℤ}
  {c : EuclideanSpace ℝ (Fin m)} {a a' : Vertex m} {T c₀ C₀ D L₀ : ℝ} {κT : ℕ}

/-- **The bound on the good event.** Suppose that, at the outcomes of the event `G`, every path
of `geo` from `I` to `I'` has confined vertices, and satisfies the upper bound with the variable
`Z`; and let `Y` be the variable of the union over the thickenings. Then the deviation is at most
`W (A₀ + A₁ √Ψ₊)` on `G`, with `Ψ = (Z₊ + Y₊)/Q`, `A₁ = (1 + T)√(2/c₂)` and
`A₀ = (1 + T)(2 + √(2(C_v + C_p)/c₂)) + B`. -/
theorem Cfg.deviation_le_good (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT)
    {I I' : Set (Vertex m)} {G : Set (Config m)}
    {geo : Config m → ∀ {u v : Vertex m}, (latticeGraph m).Walk u v → Prop}
    {P : Pt m} {Z Y : Config m → ℝ} {c₂ Cv Cp Γ B : ℝ}
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
    (hLW : L₀ ≤ W M K A ℓ) :
    ∀ᵐ ω ∂M.P, ω ∈ G → deviation (geo ω) I I' ≤
      ENNReal.ofReal (W M K A ℓ * ((1 + T) * (2 + Real.sqrt (2 * (Cv + Cp) / c₂)) + B +
        (1 + T) * Real.sqrt (2 / c₂) *
          Real.sqrt ((max (Z ω) 0 + max (Y ω) 0) / Q M K A ℓ))) := by
  have hW := h.W_pos
  have hQ := h.Q_pos
  have hT := h.hT
  have hT1 : 0 < 1 + T := by linarith only [hT]
  filter_upwards [hY, hup, hconf] with ω hYω hupω hconfω hG
  set Wl := W M K A ℓ with hWl
  set Ql := Q M K A ℓ with hQl
  set Ψ := (max (Z ω) 0 + max (Y ω) 0) / Ql with hΨ
  have hΨ0 : 0 ≤ Ψ := by positivity
  simp only [deviation]
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv =>
    iSup_le fun γ => iSup_le fun hγ => iSup_le fun x => iSup_le fun hx => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hc := hconfω hG u hu v hv γ hγ x hx
  obtain ⟨hu1, hv1⟩ := huv u hu v hv
  set β := annulus t p c Wl x with hβdef
  obtain ⟨hβl, hβu⟩ := annulus_bounds t p c hW x
  rw [← hβdef] at hβl hβu
  have hdo := distLine_le_norm_ofs t p c x
  have hoT := norm_ofs_le h.htT p c x
  -- the bound on the annulus
  have hkey : c₂ / 2 * (β : ℝ) ^ 2 ≤ Cv + Cp + Ψ := by
    rcases Nat.eq_zero_or_pos β with h0 | hβ1
    · rw [h0]
      have : 0 ≤ Cv + Cp + Ψ := by positivity
      simpa using this
    · have h1 := hpen x hc β hβ1 (hβl.trans hdo)
      have h2 := hYω x hc hβ1
      have h3 := passageTime_through_le ω (a := a) (a' := a') γ hx
      have h4 := hupω u hu v hv γ hγ
      have h5 : c₂ / 2 * (β : ℝ) ^ 2 * Ql ≤ (Cv + Cp) * Ql + (Z ω + Y ω) := by
        rw [← hβdef] at h2
        have e1 : c₂ * (β : ℝ) ^ 2 * Ql =
            c₂ / 2 * (β : ℝ) ^ 2 * Ql + c₂ / 2 * (β : ℝ) ^ 2 * Ql := by
          ring
        have e2 : (Cv + Cp) * Ql = Cv * Ql + Cp * Ql := by ring
        linarith only [h1, h2, h3, h4, e1, e2]
      have h6 : Z ω + Y ω ≤ Ψ * Ql := by
        rw [hΨ, div_mul_cancel₀ _ hQ.ne']
        exact add_le_add (le_max_left _ _) (le_max_left _ _)
      have h7 : c₂ / 2 * (β : ℝ) ^ 2 * Ql ≤ (Cv + Cp + Ψ) * Ql := by
        have e3 : (Cv + Cp + Ψ) * Ql = (Cv + Cp) * Ql + Ψ * Ql := by ring
        linarith only [h5, h6, e3]
      exact le_of_mul_le_mul_right h7 hQ
  have hβb := le_sqrt_of_sq_le hc₂ (add_nonneg hCv hCp) hΨ0 hkey
  -- the distance to the segment
  have hdist := dist_segment_le h.htT (x := x) (u := u) (v := v) (p := p) (c := c)
    (Γ := Γ) (Ω := L₀) (by rw [hu1, hv1]; have := h.hℓ; omega) (hΓu u hu) (hΓv v hv) h.hL₀
    (by rw [hv1]; push_cast; linarith only [hc.2.1]) (by rw [hu1]; linarith only [hc.1])
  have hofs : ‖ofs t p c x‖ ≤ (1 + T) * (((β : ℝ) + 1) * Wl) :=
    hoT.trans (mul_le_mul_of_nonneg_left hβu.le hT1.le)
  have hLT : (1 + T) * L₀ ≤ (1 + T) * Wl := mul_le_mul_of_nonneg_left hLW hT1.le
  have hβW : ((β : ℝ) + 1) ≤ 1 + (Real.sqrt (2 * (Cv + Cp) / c₂) +
      Real.sqrt (2 / c₂) * Real.sqrt Ψ) := by linarith only [hβb]
  have h8 := mul_le_mul_of_nonneg_right hβW hW.le
  have h9 := mul_le_mul_of_nonneg_left h8 hT1.le
  have e : Wl * ((1 + T) * (2 + Real.sqrt (2 * (Cv + Cp) / c₂)) + B +
      (1 + T) * Real.sqrt (2 / c₂) * Real.sqrt Ψ) =
      (1 + T) * ((1 + (Real.sqrt (2 * (Cv + Cp) / c₂) +
        Real.sqrt (2 / c₂) * Real.sqrt Ψ)) * Wl) + B * Wl + (1 + T) * Wl := by ring
  rw [e]
  linarith only [hdist, hofs, hLT, h9, hΓW]

end Deviation

/-- `1 + dev/W ≤ 1 + Φ` from `dev ≤ WΦ`, in `[0, ∞]`. -/
theorem radius_le_of_deviation_le {dev : ℝ≥0∞} {W Φ : ℝ} (hΦ : 0 ≤ Φ)
    (h : dev ≤ ENNReal.ofReal (W * Φ)) :
    1 + dev / ENNReal.ofReal W ≤ ENNReal.ofReal (1 + Φ) := by
  have h1 : dev / ENNReal.ofReal W ≤ ENNReal.ofReal Φ := by
    apply ENNReal.div_le_of_le_mul
    rw [← ENNReal.ofReal_mul hΦ, mul_comm]
    exact h
  rw [ENNReal.ofReal_add zero_le_one hΦ, ENNReal.ofReal_one]
  exact add_le_add le_rfl h1

end CurvatureVariance.Paper.Localization.Loc
