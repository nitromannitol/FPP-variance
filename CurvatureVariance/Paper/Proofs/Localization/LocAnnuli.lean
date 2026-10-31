/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocCfg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry

/-!
# Lemma `lem:localization`: the second change, the annuli

The rest of the second change (the proof of Lemma `lem:localization`), at a
vertex `x` with the confinement of the first change (`Loc.Conf`) in the annulus
`β = ⌊dist(x, line)/W⌋ ≥ 1`:

* `Cfg.penalty`: by equations `eq:support` and `eq:scales`,
  `μ(x − a) + μ(a' − x) ≥ ζ_t·(a' − a) + cβ²Q_ℓ − CQ_ℓ`;
* `Cfg.exists_annuli`: the sum of the tails of the `O₁` terms over the thickenings and over `β`
  (`isOs_sup'_sub`, as in the proof of [AB26, (5.3)], whose Lean is
  `IsotropicVariance.Paper.Proofs.Localization.isOs_boxPenalty`): one `O₁(CQ_ℓ)` variable
  dominates `μ(x − a) + μ(a' − x) − T(a, x) − T(x, a') − (c/2)β²Q_ℓ` at all such vertices.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts Radius

variable {m : ℕ}

/-- The confinement of the first change: `x` lies within `L₀` of `P` along `e₁`, and within `D` of
the line, measured by the offset. -/
def Conf (t : EuclideanSpace ℝ (Fin m)) (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) (ℓ : ℕ)
    (L₀ D : ℝ) (x : Vertex m) : Prop :=
  (p : ℝ) - L₀ ≤ x.1 ∧ (x.1 : ℝ) ≤ p + ℓ + L₀ ∧ ‖ofs t p c x‖ ≤ D

/-- The annulus of `x`: `⌊dist(x, line)/W⌋`. -/
noncomputable def annulus (t : EuclideanSpace ℝ (Fin m)) (p : ℤ)
    (c : EuclideanSpace ℝ (Fin m)) (W : ℝ) (x : Vertex m) : ℕ :=
  ⌊distLine t p c x / W⌋₊

/-- `βW ≤ dist(x, line) < (β + 1)W`. -/
theorem annulus_bounds (t : EuclideanSpace ℝ (Fin m)) (p : ℤ) (c : EuclideanSpace ℝ (Fin m))
    {W : ℝ} (hW : 0 < W) (x : Vertex m) :
    (annulus t p c W x : ℝ) * W ≤ distLine t p c x ∧
      distLine t p c x < ((annulus t p c W x : ℝ) + 1) * W := by
  have h0 : 0 ≤ distLine t p c x / W := div_nonneg (distLine_nonneg _ _ _ _) hW.le
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one (distLine t p c x / W)
  rw [le_div_iff₀ hW] at h1
  rw [div_lt_iff₀ hW] at h2
  exact ⟨h1, h2⟩

section Penalty

variable {M : Model m} {K : ℕ} {A : ℝ} {ℓ : ℕ} {t : EuclideanSpace ℝ (Fin m)} {p : ℤ}
  {c : EuclideanSpace ℝ (Fin m)} {a a' : Vertex m} {T c₀ C₀ D L₀ : ℝ} {κT : ℕ}

/-- **The penalty** (the second change in the proof of Lemma `lem:localization`): by equations
`eq:support` and `eq:scales`, for a confined vertex `x` with offset at least `βW`, `β ≥ 1`,
`μ(x − a) + μ(a' − x) ≥ ζ_t·(a' − a) + (c/8)β²Q_ℓ − 2CC₃Q_ℓ`. Only the piece from `a` to `x` is
needed: `μ(a' − x) ≥ ζ_t·(a' − x)`, `ζ_t` being a subgradient. -/
theorem Cfg.penalty (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {cS CS r₁ C₃ : ℝ} (hcS : 0 < cS)
    (hCS : 0 < CS)
    (h24 : ∀ t h : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    {P : Pt m} (hP : IsSubgradient M.μ (slopeVec t) P) (ht₁ : ‖t - M.t₀‖ ≤ r₁)
    (hDr : 64 * D ≤ r₁ * ℓ) (hτ : (ℓ : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ C₃ * Q M K A ℓ)
    {x : Vertex m} (hx : Conf t p c ℓ L₀ D x) {β : ℕ} (hβ : 1 ≤ β)
    (hβx : (β : ℝ) * W M K A ℓ ≤ ‖ofs t p c x‖) :
    ⟪P, point a' - point a⟫ + cS / 8 * (β : ℝ) ^ 2 * Q M K A ℓ - 2 * CS * C₃ * Q M K A ℓ ≤
      M.μ.1 (point x - point a) + M.μ.1 (point a' - point x) := by
  have hℓ := h.ℓ_pos
  have hW := h.W_pos
  have hQ := h.Q_pos
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨a1, a2⟩ := abs_le.1 h.ha₁
  have hL := h.hL
  have hL0 := h.hL₀
  have hd0 := rtd_nonneg m
  set s : ℝ := (x.1 : ℝ) - a.1 with hs
  have hs1 : (ℓ : ℝ) / 32 ≤ s := by rw [hs]; linarith only [a1, a2, hx1, hx2, hL, hL0, hd0, hℓ]
  have hs2 : s ≤ 2 * ℓ := by rw [hs]; linarith only [a1, a2, hx1, hx2, hL, hL0, hd0, hℓ]
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs1
  set y : EuclideanSpace ℝ (Fin m) := transversePoint x.2 - transversePoint a.2 with hy
  have hz : point x - point a = WithLp.toLp 2 (s, y) := by
    apply Infra.FPP.pt_ext <;> simp [hs, hy]
  have hoff : y - s • t = ofs t p c x - ofs t p c a := by
    rw [ofs_sub_ofs, hz]
    simp [transOff]
  -- the slope of `x − a` is near `t`
  have hCD : ‖ofs t p c a‖ ≤ D := (h.hao).trans (by
    have := h.hC₀; have := h.hDW; linarith only [h.hC₀, h.hDW, hW])
  have hβ1 : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hyr : ‖y - s • t‖ ≤ 2 * D := by
    rw [hoff]
    exact (norm_sub_le _ _).trans (by linarith only [hx3, hCD])
  have hsl : ‖s⁻¹ • y - t‖ ≤ r₁ := by
    have e : s⁻¹ • y - t = s⁻¹ • (y - s • t) := by
      rw [smul_sub s⁻¹ y (s • t), inv_smul_smul₀ hs0.ne']
    rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, inv_mul_le_iff₀ hs0]
    have h1 : r₁ * (ℓ : ℝ) / 32 ≤ s * r₁ := by
      have hr0 : 0 ≤ r₁ := (norm_nonneg _).trans ht₁
      have := mul_le_mul_of_nonneg_right hs1 hr0
      linarith only [this]
    linarith only [hyr, hDr, h1]
  obtain ⟨hlow, -⟩ := Moments.ExpArray.support_bounds h24 hP hs0 y ht₁ hsl
  rw [← hz] at hlow
  -- the offset of `x` from the line through `a` is at least `βW/2`
  have hlow1 : (β : ℝ) * W M K A ℓ / 2 ≤ ‖y - s • t‖ := by
    rw [hoff]
    have h1 := norm_sub_norm_le (ofs t p c x) (ofs t p c a)
    have h2 := h.hao
    have h3 : W M K A ℓ ≤ (β : ℝ) * W M K A ℓ := le_mul_of_one_le_left hW.le hβ1
    linarith only [h1, h2, h3, h.hC₀, hβx]
  have hlow2 : ((β : ℝ) * W M K A ℓ / 2) ^ 2 ≤ ‖y - s • t‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlow1 2
  have hWQ := h.W_eq
  have e1 : ((β : ℝ) * W M K A ℓ / 2) ^ 2 = (β : ℝ) ^ 2 * (ℓ * Q M K A ℓ) / 4 := by
    rw [div_pow, mul_pow, hWQ]; ring
  rw [e1] at hlow2
  have hterm : cS / 8 * (β : ℝ) ^ 2 * Q M K A ℓ ≤ cS * ‖y - s • t‖ ^ 2 / s := by
    rw [le_div_iff₀ hs0]
    have h1 : cS / 8 * (β : ℝ) ^ 2 * Q M K A ℓ * s ≤
        cS / 8 * (β : ℝ) ^ 2 * Q M K A ℓ * (2 * ℓ) :=
      mul_le_mul_of_nonneg_left hs2 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hlow2 hcS.le
    have e2 : cS / 8 * (β : ℝ) ^ 2 * Q M K A ℓ * (2 * ℓ) =
        cS * ((β : ℝ) ^ 2 * (ℓ * Q M K A ℓ) / 4) := by ring
    linarith only [h1, h2, e2]
  have hτ2 : CS * s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 2 * CS * C₃ * Q M K A ℓ := by
    have h0 : 0 ≤ ‖t - M.t₀‖ ^ (2 + M.δ) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hs2 h0
    have h2 : s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 2 * (C₃ * Q M K A ℓ) := by
      linarith only [h1, hτ]
    have h3 := mul_le_mul_of_nonneg_left h2 hCS.le
    linarith only [h3]
  have hsplit : ⟪P, point a' - point a⟫ = ⟪P, point a' - point x⟫ + ⟪P, point x - point a⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have hsub := hP.2 (point a' - point x)
  linarith only [hlow, hterm, hτ2, hsplit, hsub]

end Penalty

/-! ## The union over the thickenings and the annuli -/

/-- The bound of the sum of the tails, `S` in `isOs_sup'_sub`. -/
noncomputable def annuliSum (m κT : ℕ) (c₀ c₃ : ℝ) : ℝ :=
  1 + (2 / c₀ + 3) * (3 * (κT : ℝ)) ^ m * ∑' n : ℕ, (n : ℝ) ^ (m + 1) * Real.exp (-c₃ * n)

section Annuli

variable {M : Model m} {K : ℕ} {A : ℝ} {ℓ : ℕ} {t : EuclideanSpace ℝ (Fin m)} {p : ℤ}
  {c : EuclideanSpace ℝ (Fin m)} {a a' : Vertex m} {T c₀ C₀ D L₀ : ℝ} {κT : ℕ}

/-- The number of cubes at `β`: `(ℓ/g_β + 3)(2κβ + 1)^m ≤ (2/c₀ + 3)(3κ)^m β^{m+1}`. -/
theorem Cfg.count_le (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {β : ℕ} (hβ : 1 ≤ β)
    (hβD : (β : ℝ) * W M K A ℓ ≤ D) :
    (((ℓ / gapOf (c₀ * ℓ) β : ℕ) : ℝ) + 3) * (2 * ((κT * β : ℕ) : ℝ) + 1) ^ m ≤
      (2 / c₀ + 3) * (3 * (κT : ℝ)) ^ m * (β : ℝ) ^ (m + 1) := by
  have hβ1 : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hβ0 : (0 : ℝ) < β := by linarith only [hβ1]
  have hc := h.hc₀
  have hℓ := h.ℓ_pos
  have hκ : (1 : ℝ) ≤ κT := by exact_mod_cast h.hκT
  obtain ⟨hg1, -, hg3⟩ := h.gap_bounds hβ hβD
  set g := gapOf (c₀ * ℓ) β
  have hg0 : (0 : ℝ) < g := by
    have := rtd_nonneg m; have := h.hL₀; linarith only [hg3, this, rtd_nonneg m]
  have h1 : ((ℓ / g : ℕ) : ℝ) ≤ (ℓ : ℝ) / g := Nat.cast_div_le
  have h2 : (ℓ : ℝ) / g ≤ 2 / c₀ * β := by
    rw [div_le_iff₀ hg0]
    have h3 := mul_le_mul_of_nonneg_left hg1 (by positivity : 0 ≤ 2 / c₀ * (β : ℝ))
    have e : 2 / c₀ * (β : ℝ) * (c₀ * ℓ / (2 * β)) = ℓ := by field_simp
    linarith only [h3, e]
  have h3 : ((ℓ / g : ℕ) : ℝ) + 3 ≤ (2 / c₀ + 3) * β := by
    have : (2 / c₀ + 3) * (β : ℝ) = 2 / c₀ * β + 3 * β := by ring
    linarith only [h1, h2, this, hβ1]
  have h4 : 2 * ((κT * β : ℕ) : ℝ) + 1 ≤ 3 * κT * β := by
    push_cast
    nlinarith only [hκ, hβ1]
  have h5 : (2 * ((κT * β : ℕ) : ℝ) + 1) ^ m ≤ (3 * κT * β) ^ m :=
    pow_le_pow_left₀ (by positivity) h4 m
  calc (((ℓ / g : ℕ) : ℝ) + 3) * (2 * ((κT * β : ℕ) : ℝ) + 1) ^ m
      ≤ ((2 / c₀ + 3) * β) * (3 * κT * β) ^ m := mul_le_mul h3 h5 (by positivity) (by positivity)
    _ = (2 / c₀ + 3) * (3 * (κT : ℝ)) ^ m * (β : ℝ) ^ (m + 1) := by
        rw [mul_pow, pow_succ]; ring

/-- **The sum of the tails** over the family, with `c₃ = c₂/(16C')`. -/
theorem Cfg.sum_family_le (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {B : ℕ}
    (hB : (B : ℝ) * W M K A ℓ ≤ D) {c₃ : ℝ} (hc₃ : 0 < c₃) :
    ∑ i ∈ family m B κT ℓ (c₀ * ℓ), Real.exp (-c₃ * (i.1 : ℝ) ^ 2) ≤ annuliSum m κT c₀ c₃ := by
  have hc := h.hc₀
  have hκ : (1 : ℝ) ≤ κT := by exact_mod_cast h.hκT
  have hW := h.W_pos
  rw [sum_family_eq (fun β => Real.exp (-c₃ * (β : ℝ) ^ 2))]
  have hK0 : 0 ≤ (2 / c₀ + 3) * (3 * (κT : ℝ)) ^ m := by positivity
  have hs := sum_pow_mul_exp_neg_sq_le hc₃ (m + 1) B
  have hterm : ∀ β ∈ Finset.Icc 1 B,
      (((ℓ / gapOf (c₀ * ℓ) β : ℕ) : ℝ) + 3) * (2 * ((κT * β : ℕ) : ℝ) + 1) ^ m *
          Real.exp (-c₃ * (β : ℝ) ^ 2) ≤
        (2 / c₀ + 3) * (3 * (κT : ℝ)) ^ m *
          ((β : ℝ) ^ (m + 1) * Real.exp (-c₃ * (β : ℝ) ^ 2)) := by
    intro β hβ
    obtain ⟨hβ1, hβB⟩ := Finset.mem_Icc.1 hβ
    have hβB' : (β : ℝ) ≤ B := by exact_mod_cast hβB
    have hβD : (β : ℝ) * W M K A ℓ ≤ D := (mul_le_mul_of_nonneg_right hβB' hW.le).trans hB
    have := mul_le_mul_of_nonneg_right (h.count_le hβ1 hβD) (Real.exp_pos (-c₃ * (β : ℝ) ^ 2)).le
    linarith only [this]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, annuliSum]
  have := mul_le_mul_of_nonneg_left hs hK0
  linarith only [this]

/-- **The union over the thickenings and over the annuli**
(the last sentence of the second change in the proof of Lemma `lem:localization`, as in the proof of
[AB26, (5.3)]). -/
theorem Cfg.exists_annuli (hSum : SignedOsSumStatement.{0, 0})
    (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {N : ℕ} {κ C' c₂ : ℝ} (hC' : 0 < C')
    (hc₂ : 0 < c₂) (hprof : ProfAt M K A N (κ / 32) C') (hκℓ : κ * N ≤ ℓ) (hℓN : ℓ ≤ N) :
    ∃ Y : Config m → ℝ, CurvatureVariance.IsOs M.P 1
        (Real.logb 2 (1 + 2 * annuliSum m κT c₀ (c₂ / (16 * C'))) * (8 * C') * Q M K A ℓ) Y ∧
      ∀ᵐ ω ∂M.P, ∀ x : Vertex m, Conf t p c ℓ L₀ D x → 1 ≤ annulus t p c (W M K A ℓ) x →
        M.μ.1 (point x - point a) + M.μ.1 (point a' - point x) -
            (passageTimeReal ω a x + passageTimeReal ω x a') -
            c₂ / 2 * ((annulus t p c (W M K A ℓ) x : ℕ) : ℝ) ^ 2 * Q M K A ℓ ≤ Y ω := by
  classical
  have hprob := h.hM.probP
  have hW := h.W_pos
  have hQ := h.Q_pos
  have hℓ := h.ℓ_pos
  have hc := h.hc₀
  set Wl := W M K A ℓ with hWl
  set Ql := Q M K A ℓ with hQl
  set B := ⌊D / Wl⌋₊ with hBdef
  have hD0 : 0 ≤ D / Wl := div_nonneg (hW.le.trans h.hDW) hW.le
  have hB : (B : ℝ) * Wl ≤ D := by
    have := Nat.floor_le hD0
    rwa [le_div_iff₀ hW] at this
  have hB1 : 1 ≤ B := Nat.le_floor (by
    rw [Nat.cast_one, le_div_iff₀ hW, one_mul]; exact h.hDW)
  set T₀ := family m B κT ℓ (c₀ * ℓ) with hT₀
  have hne : T₀.Nonempty := ⟨⟨1, 0, 0⟩, mem_family le_rfl hB1 (by norm_num)
    (by positivity) (fun i => by simp)⟩
  have hthick := fun (i : Idx m) (hi : i ∈ T₀) =>
    h.exists_thick hSum hC' hprof hκℓ hℓN hB hi
  choose! U hU hUae using hthick
  set θ := 4 * C' * Ql with hθ
  have hθ0 : 0 < θ := by positivity
  set c₃ := c₂ / (16 * C') with hc₃
  have hc₃0 : 0 < c₃ := by positivity
  set w : Idx m → ℝ := fun i => c₂ / 2 * (i.1 : ℝ) ^ 2 * Ql with hw
  have hexp : ∀ i : Idx m, Real.exp (-(w i) / (2 * θ)) = Real.exp (-c₃ * (i.1 : ℝ) ^ 2) := by
    intro i
    congr 1
    simp only [hw, hθ, hc₃]
    field_simp
    ring
  have hsum : ∑ i ∈ T₀, Real.exp (-(w i) / (2 * θ)) ≤ annuliSum m κT c₀ c₃ := by
    simp only [hexp]
    exact h.sum_family_le hB hc₃0
  have hS1 : 1 ≤ annuliSum m κT c₀ c₃ := by
    have h0 := tsum_pow_mul_exp_neg_pos hc₃0 (m + 1)
    have : 0 ≤ (2 / c₀ + 3) * (3 * (κT : ℝ)) ^ m *
        ∑' n : ℕ, (n : ℝ) ^ (m + 1) * Real.exp (-c₃ * n) := by positivity
    rw [annuliSum]; linarith only [this]
  have hY := isOs_sup'_sub T₀ hne hθ0 hS1 U w hU hsum
  refine ⟨T₀.sup' hne fun i ω => U i ω - w i, ?_, ?_⟩
  · have e : Real.logb 2 (1 + 2 * annuliSum m κT c₀ c₃) * (2 * θ) =
        Real.logb 2 (1 + 2 * annuliSum m κT c₀ c₃) * (8 * C') * Ql := by
      rw [hθ]; ring
    rwa [e] at hY
  have hae := (Filter.eventually_all_finset T₀).mpr hUae
  filter_upwards [hae] with ω hω x hx hβ1
  set β := annulus t p c Wl x with hβdef
  obtain ⟨hβl, hβu⟩ := annulus_bounds t p c hW x
  rw [← hβdef] at hβl hβu
  have hdo := distLine_le_norm_ofs t p c x
  have hoT := norm_ofs_le h.htT p c x
  have hβD : (β : ℝ) * Wl ≤ D := hβl.trans (hdo.trans hx.2.2)
  have hβB : β ≤ B := by
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hW]; exact hβD
  obtain ⟨hg1, hg2, hg3⟩ := h.gap_bounds hβ1 hβD
  set g := gapOf (c₀ * ℓ) β with hgdef
  have hd0 := rtd_nonneg m
  have hL0 := h.hL₀
  have hg0 : (0 : ℝ) < g := by linarith only [hg3, hd0, hL0]
  have hg0' : 0 < g := by exact_mod_cast hg0
  have hg0'' : (0 : ℤ) < g := by exact_mod_cast hg0'
  set G := Wl - 1 with hG
  have hG0 : 0 < G := by have := h.G_ge; linarith only [this, hW]
  have hGW : Wl / 2 ≤ G := h.G_ge
  set j : ℤ := (x.1 - p) / g with hj
  set k : Fin m → ℤ := fun i => round (ofs t p c x i / G) with hk
  have hLg : L₀ ≤ g := by linarith only [hg3, hd0]
  have hj1 : -1 ≤ j := by
    have h1 : -(g : ℤ) ≤ x.1 - p := by
      have : -(g : ℝ) ≤ ((x.1 - p : ℤ) : ℝ) := by push_cast; linarith only [hx.1, hLg]
      exact_mod_cast this
    exact Int.le_ediv_of_mul_le hg0'' (by linarith only [h1])
  have hj2 : j ≤ ((ℓ / g : ℕ) : ℤ) + 1 := by
    have h1 : ℓ < g * (ℓ / g + 1) := Nat.lt_mul_div_succ ℓ hg0'
    have h2 : (ℓ : ℤ) < g * (((ℓ / g : ℕ) : ℤ) + 1) := by exact_mod_cast h1
    have h3 : x.1 - p ≤ (ℓ : ℤ) + g := by
      have : ((x.1 - p : ℤ) : ℝ) ≤ ((ℓ + g : ℤ) : ℝ) := by push_cast; linarith only [hx.2.1, hLg]
      exact_mod_cast this
    have h4 : x.1 - p < (((ℓ / g : ℕ) : ℤ) + 2) * g := by nlinarith only [h2, h3]
    have := Int.ediv_lt_of_lt_mul hg0'' h4
    omega
  have hkb : ∀ i, |(k i : ℝ)| ≤ ((κT * β : ℕ) : ℝ) := by
    intro i
    have h1 := abs_round_le (t := t) p c hG0 x i
    have hβ1' : (1 : ℝ) ≤ β := by exact_mod_cast hβ1
    have hT := h.hT
    have h2 : ‖ofs t p c x‖ / G ≤ 4 * (1 + T) * β := by
      rw [div_le_iff₀ hG0]
      have h3 : ‖ofs t p c x‖ ≤ (1 + T) * (((β : ℝ) + 1) * Wl) :=
        hoT.trans (mul_le_mul_of_nonneg_left hβu.le (by linarith only [hT]))
      have h4 : (1 + T) * (((β : ℝ) + 1) * Wl) ≤ (1 + T) * (2 * β * (2 * G)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hT])
        exact mul_le_mul (by linarith only [hβ1']) (by linarith only [hGW]) hW.le (by positivity)
      linarith only [h3, h4]
    have h5 := mul_le_mul_of_nonneg_right h.hκT' (show (0 : ℝ) ≤ β by positivity)
    have h6 : (1 / 2 : ℝ) ≤ 1 / 2 * β := by linarith only [hβ1']
    push_cast
    simp only [hk]
    have e : (4 * (1 + T) + 1 / 2) * (β : ℝ) = 4 * (1 + T) * β + 1 / 2 * β := by ring
    linarith only [h1, h2, h5, h6, e]
  have hi : (⟨β, j, k⟩ : Idx m) ∈ T₀ := mem_family hβ1 hβB hj1 hj2 hkb
  have hxt : x ∈ thicken (transverseCube (p + j * g) (ctr t c G (j * g) k) Wl) t (c₀ * ℓ / β) := by
    have h1 := mem_thicken_cube (t := t) p c hG0 hg0' x
    rw [show G + 1 = Wl by rw [hG]; ring] at h1
    exact thicken_mono hg2 h1
  have hb := hω ⟨β, j, k⟩ hi x hxt
  have hsup : U ⟨β, j, k⟩ ω - w ⟨β, j, k⟩ ≤ T₀.sup' hne (fun i ω => U i ω - w i) ω := by
    rw [Finset.sup'_apply]
    exact Finset.le_sup' (fun i => U i ω - w i) hi
  simp only [hw] at hsup
  linarith only [hb, hsup]

end Annuli

end CurvatureVariance.Paper.Localization.Loc
