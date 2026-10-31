/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocThick
public import CurvatureVariance.Paper.Proofs.Localization.LocOs
public import CurvatureVariance.Paper.Contracts.Inputs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry
import CurvatureVariance.Paper.Proofs.Localization.Common
import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet

/-!
# Lemma `lem:localization`: the configuration of the second change

`Loc.Cfg` collects the facts of the second change in the proof of Lemma `lem:localization` at fixed
`N`, `A`, `ℓ`, for the points `a`, `a'`: the conditions "for `N` large" are its fields, which
`CurvatureVariance.Paper.Proofs.Localization.LocPack` proves. From it, for one index of the family
`Loc.family`:

* `Cfg.gap_bounds`, `Cfg.exists_lengths`: the cube lies at distances in `[ℓ/32, 9ℓ/8]` from `a` and
  `a'` along `e₁`;
* `Cfg.exists_thick`: the thickening lies in the thickenings of `I''` given by Proposition
  `prop:profiles`, with `κ/32` in place of `κ`, for the pairs `{a}, I''` and `I'', {a'}`.

The slopes satisfy `|t_i − t₀| ≤ (3/2) s^{δ/100−1/4}` for the lengths `s ≤ 9ℓ/8` of the two pairs,
which implies the bound of the paper at `s = 9ℓ/8`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts Radius

variable {m : ℕ}

/-- The bound `√d`. -/
noncomputable def rtd (m : ℕ) : ℝ := Real.sqrt ((m : ℝ) + 1)

theorem rtd_nonneg (m : ℕ) : 0 ≤ rtd m := Real.sqrt_nonneg _

/-- **The configuration of the proof**, at fixed `N`, `A`, `ℓ`, for the line `ū + ℝ(1, t)` with
`ū = (p, c)`, the points `a`, `a'` within `√d` of `ū − (ℓ/16)(1, t)` and of
`v̄ + (ℓ/16)(1, t)`, a constant `c₀`, the confinement `L₀`, `D` of the first change, and the bound
`C₀` of the offsets of `a` and `a'`. The fields below `hc₀` are the conditions "for `N` large". -/
structure Cfg (M : Model m) (K : ℕ) (A : ℝ) (ℓ : ℕ) (t : EuclideanSpace ℝ (Fin m)) (p : ℤ)
    (c : EuclideanSpace ℝ (Fin m)) (a a' : Vertex m) (T c₀ C₀ D L₀ : ℝ) (κT : ℕ) : Prop where
  hM : M.Standing
  hK : 10 ^ 4 ≤ K
  hA : 1 ≤ A
  hℓ : 1 ≤ ℓ
  ht : ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4)
  htT : ‖t‖ ≤ T
  hT : 1 ≤ T
  hκT : 1 ≤ κT
  hκT' : 4 * (1 + T) + 1 / 2 ≤ κT
  ha₁ : |(a.1 : ℝ) - ((p : ℝ) - (ℓ : ℝ) / 16)| ≤ rtd m
  ha₂ : |(a'.1 : ℝ) - ((p : ℝ) + 17 * (ℓ : ℝ) / 16)| ≤ rtd m
  hao : ‖ofs t p c a‖ ≤ C₀
  ha'o : ‖ofs t p c a'‖ ≤ C₀
  hc₀ : 0 < c₀
  hc₀1 : 2 ^ 16 * c₀ ≤ 1
  hc₀2 : 512 * Real.sqrt m * κT * c₀ ≤ 1
  hW : 4 * ((1 + T) * rtd m + 1) ≤ W M K A ℓ
  hC₀ : 2 * C₀ ≤ W M K A ℓ
  hDW : W M K A ℓ ≤ D
  hDslope : 64 * Real.sqrt m * κT * D / ℓ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) / 4
  hρ : 2 * D * (rtd m + L₀ + 1) ≤ c₀ * ℓ * W M K A ℓ
  hL₀ : 0 ≤ L₀
  hL : 64 * (L₀ + rtd m) ≤ ℓ

namespace Cfg

variable {M : Model m} {K : ℕ} {A : ℝ} {ℓ : ℕ} {t : EuclideanSpace ℝ (Fin m)} {p : ℤ}
  {c : EuclideanSpace ℝ (Fin m)} {a a' : Vertex m} {T c₀ C₀ D L₀ : ℝ} {κT : ℕ}

theorem ℓ_pos (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) : (0 : ℝ) < ℓ := by
  exact_mod_cast h.hℓ

theorem W_pos (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) : 0 < W M K A ℓ := by
  have h1 := h.hW
  have h2 := rtd_nonneg m
  have h3 := h.hT
  have : 0 ≤ (1 + T) * rtd m := by positivity
  linarith only [h1, this]

theorem W_eq (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) :
    W M K A ℓ ^ 2 = ℓ * Q M K A ℓ :=
  Proofs.ShortLengths.W_sq (by linarith only [h.hA]) (Nat.cast_nonneg ℓ)

theorem Q_pos (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) : 0 < Q M K A ℓ :=
  Localization.Q_pos (by linarith only [h.hA]) h.ℓ_pos

theorem sqrt_m_ge_one (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) : 1 ≤ Real.sqrt m := by
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast h.hM.one_le_m
  exact Real.one_le_sqrt.mpr h1

theorem sqrt_κ_ge_one (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) :
    1 ≤ Real.sqrt m * κT := by
  have h1 := h.sqrt_m_ge_one
  have h2 : (1 : ℝ) ≤ κT := by exact_mod_cast h.hκT
  nlinarith only [h1, h2]

/-- The offset spacing `G = W − 1` is at least `W/2`. -/
theorem G_ge (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) :
    W M K A ℓ / 2 ≤ W M K A ℓ - 1 := by
  have h1 := h.hW
  have h2 := rtd_nonneg m
  have h3 := h.hT
  have : 0 ≤ (1 + T) * rtd m := by positivity
  linarith only [h1, this]

/-- For an annulus `βW ≤ D`, the thickening radius `ρ_β = c₀ℓ/β` is at least `2(√d + L₀ + 1)`. -/
theorem rho_ge (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {β : ℕ} (hβ : 1 ≤ β)
    (hβD : (β : ℝ) * W M K A ℓ ≤ D) : 2 * (rtd m + L₀ + 1) ≤ c₀ * ℓ / β := by
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hW := h.W_pos
  have h0 : 0 ≤ rtd m + L₀ + 1 := by have := rtd_nonneg m; have := h.hL₀; linarith
  rw [le_div_iff₀ hβ0]
  have h1 : (β : ℝ) * W M K A ℓ * (2 * (rtd m + L₀ + 1)) ≤ c₀ * ℓ * W M K A ℓ := by
    have := mul_le_mul_of_nonneg_right hβD (by positivity : 0 ≤ 2 * (rtd m + L₀ + 1))
    linarith only [this, h.hρ]
  have h2 : (2 * (rtd m + L₀ + 1) * β) * W M K A ℓ ≤ (c₀ * ℓ) * W M K A ℓ := by
    linarith only [h1]
  exact le_of_mul_le_mul_right h2 hW

/-- The spacing of the annulus `β`: `ρ_β/2 ≤ g_β ≤ ρ_β`, and `g_β ≥ √d + L₀ + 1`. -/
theorem gap_bounds (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {β : ℕ} (hβ : 1 ≤ β)
    (hβD : (β : ℝ) * W M K A ℓ ≤ D) :
    c₀ * ℓ / (2 * β) ≤ gapOf (c₀ * ℓ) β ∧ (gapOf (c₀ * ℓ) β : ℝ) ≤ c₀ * ℓ / β ∧
      rtd m + L₀ + 1 ≤ gapOf (c₀ * ℓ) β := by
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hρ := h.rho_ge hβ hβD
  have h0 : 0 ≤ rtd m + L₀ := by have := rtd_nonneg m; have := h.hL₀; linarith
  have hle : (β : ℝ) ≤ c₀ * ℓ := by
    have : 1 ≤ c₀ * ℓ / β := by linarith only [hρ, h0]
    rwa [le_div_iff₀ hβ0, one_mul] at this
  obtain ⟨h1, h2⟩ := gapOf_bounds hβ hle
  refine ⟨h1, h2, ?_⟩
  have e : c₀ * ℓ / (2 * β) = c₀ * ℓ / β / 2 := by field_simp
  rw [e] at h1
  linarith only [h1, hρ]

/-- `ρ_β ≤ c₀ℓ ≤ ℓ/2¹⁶`. -/
theorem rho_le (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {β : ℕ} (hβ : 1 ≤ β) :
    c₀ * ℓ / β ≤ ℓ / 2 ^ 16 := by
  have hβ1 : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have hℓ := h.ℓ_pos
  have hc := h.hc₀
  have h1 : c₀ * ℓ / β ≤ c₀ * ℓ := div_le_self (by positivity) hβ1
  have h2 := mul_le_mul_of_nonneg_right h.hc₀1 hℓ.le
  linarith only [h1, h2]

/-- **The lengths of the two pairs**: a cube at `p + h`, with `−g ≤ h ≤ ℓ + g`, lies at distances
`s₁, s₂ ∈ [ℓ/32, 9ℓ/8]` from `a` and `a'` along `e₁`. -/
theorem exists_lengths (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {g : ℕ} {r : ℤ}
    (hg : (g : ℝ) ≤ ℓ / 2 ^ 16) (h1 : -(g : ℤ) ≤ r) (h2 : r ≤ ℓ + g) :
    ∃ s₁ s₂ : ℕ, p + r = a.1 + s₁ ∧ a'.1 = p + r + s₂ ∧
      (ℓ : ℝ) / 32 ≤ s₁ ∧ (s₁ : ℝ) ≤ 9 * ℓ / 8 ∧ (ℓ : ℝ) / 32 ≤ s₂ ∧ (s₂ : ℝ) ≤ 9 * ℓ / 8 := by
  have hℓ := h.ℓ_pos
  obtain ⟨a1, a2⟩ := abs_le.1 h.ha₁
  obtain ⟨a3, a4⟩ := abs_le.1 h.ha₂
  have hL := h.hL
  have hd : rtd m ≤ ℓ / 64 := by have := h.hL₀; linarith only [hL, this]
  have h1' : -(g : ℝ) ≤ r := by exact_mod_cast h1
  have h2' : (r : ℝ) ≤ ℓ + g := by exact_mod_cast h2
  have hd0 := rtd_nonneg m
  have hs1 : (0 : ℝ) ≤ ((p + r - a.1 : ℤ) : ℝ) := by
    push_cast; linarith only [a1, a2, h1', hg, hd, hℓ]
  have hs2 : (0 : ℝ) ≤ ((a'.1 - (p + r) : ℤ) : ℝ) := by
    push_cast; linarith only [a3, a4, h2', hg, hd, hℓ]
  have hs1' : 0 ≤ p + r - a.1 := by exact_mod_cast hs1
  have hs2' : 0 ≤ a'.1 - (p + r) := by exact_mod_cast hs2
  refine ⟨(p + r - a.1).toNat, (a'.1 - (p + r)).toNat, by omega, by omega, ?_, ?_, ?_, ?_⟩
  all_goals
    have e1 : (((p + r - a.1).toNat : ℕ) : ℝ) = ((p + r - a.1 : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hs1'
    have e2 : (((a'.1 - (p + r)).toNat : ℕ) : ℝ) = ((a'.1 - (p + r) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hs2'
    try rw [e1]
    try rw [e2]
    push_cast
    linarith only [a1, a2, a3, a4, h1', h2', hg, hd, hℓ]

/-- The index of a member of the family: its hyperplane lies at `−g_β ≤ j g_β ≤ ℓ + g_β`. -/
theorem index_bounds {B : ℕ} {ρ₀ : ℝ} {i : Idx m} (hi : i ∈ family m B κT ℓ ρ₀) :
    -(gapOf ρ₀ i.1 : ℤ) ≤ i.2.1 * gapOf ρ₀ i.1 ∧
      i.2.1 * gapOf ρ₀ i.1 ≤ ℓ + gapOf ρ₀ i.1 := by
  obtain ⟨h1, h2⟩ := family_snd hi
  set g := gapOf ρ₀ i.1
  have hg0 : (0 : ℤ) ≤ g := Int.natCast_nonneg g
  constructor
  · nlinarith only [h1, hg0]
  · have h3 : i.2.1 * g ≤ (((ℓ / g : ℕ) : ℤ) + 1) * g := mul_le_mul_of_nonneg_right h2 hg0
    have h4 : (((ℓ / g : ℕ) : ℤ)) * g ≤ ℓ := by exact_mod_cast Nat.div_mul_le_self ℓ g
    linarith only [h3, h4]

/-- The norm of the offset index of a member of the family: `|k| ≤ √m κ β`. -/
theorem norm_index_le {B : ℕ} {ρ₀ : ℝ} {i : Idx m} (hi : i ∈ family m B κT ℓ ρ₀) :
    ‖transversePoint i.2.2‖ ≤ Real.sqrt m * ((κT * i.1 : ℕ) : ℝ) := by
  refine Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (by positivity) fun l => ?_
  simpa using family_abs_le hi l

end Cfg

/-! ## The thickenings and Proposition `prop:profiles` -/

/-- Proposition `prop:profiles` in its second range, at fixed `N`, `A`, at the side `512`. -/
def ProfAt (M : Model m) (K : ℕ) (A : ℝ) (N : ℕ) (κ C : ℝ) : Prop :=
  ∀ (s : ℕ) (t : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
    IsCubePair M K A s 512 t I I' → κ * N ≤ s → (s : ℝ) ≤ 2 * N →
    ‖t - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) → ShortConclusion M K A s C t I I'

/-- The sum rule, equation `eq:sum`, for two summands, `s ≥ 1`, with the premise
`SignedOsSumStatement`. -/
theorem isOs_add_of (hSum : SignedOsSumStatement.{0, 0}) {P : Measure (Config m)}
    [IsProbabilityMeasure P] {s θ η : ℝ} (hs : 1 ≤ s) {X Y : Config m → ℝ}
    (hX : CurvatureVariance.IsOs P s θ X) (hY : CurvatureVariance.IsOs P s η Y) (hθ : 0 < θ) (hη : 0 < η) :
    CurvatureVariance.IsOs P s (θ + η) (fun ω => X ω + Y ω) := by
  obtain ⟨C, -, hC1, h⟩ := hSum s (by linarith only [hs])
  have := h P (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty ![θ, η]
    (fun i _ => by fin_cases i <;> simp [hθ, hη]) ![X, Y]
    (fun i _ => by fin_cases i <;> simpa)
  simpa [hC1 hs, Fin.sum_univ_two] using this

/-- `4/3 ≤ 16^{1/4 − δ/100}` for `δ ≤ 1`. -/
theorem four_thirds_le_rpow {δ : ℝ} (hδ1 : δ ≤ 1) :
    (4 / 3 : ℝ) ≤ (16 : ℝ) ^ (-(δ / 100 - 1 / 4)) := by
  have h1 : (16 : ℝ) ^ ((1 : ℝ) / 8) ≤ (16 : ℝ) ^ (-(δ / 100 - 1 / 4)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  refine le_trans ?_ h1
  set x := (16 : ℝ) ^ ((1 : ℝ) / 8)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by norm_num) _
  have hx8 : x ^ 8 = 16 := by
    simp only [x]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  by_contra h
  push Not at h
  have := pow_lt_pow_left₀ h hx0 (by norm_num : (8 : ℕ) ≠ 0)
  rw [hx8] at this; norm_num at this

/-- `(5/6) ℓ^e ≤ s^e` for `0 < s ≤ 2ℓ` and `e = δ/100 − 1/4`. -/
theorem five_sixths_rpow_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {s ℓ : ℝ} (hs : 0 < s)
    (hℓ : 0 < ℓ) (hsℓ : s ≤ 2 * ℓ) :
    5 / 6 * ℓ ^ (δ / 100 - 1 / 4) ≤ s ^ (δ / 100 - 1 / 4) := by
  have h1 : (2 * ℓ) ^ (δ / 100 - 1 / 4) ≤ s ^ (δ / 100 - 1 / 4) :=
    Real.rpow_le_rpow_of_nonpos hs hsℓ (by linarith)
  rw [Real.mul_rpow (by norm_num) hℓ.le] at h1
  have h2 : (5 / 6 : ℝ) ≤ 2 ^ (δ / 100 - 1 / 4) := by
    have h5 : (5 / 6 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
      calc (5 / 6 : ℝ) = ((5 / 6 : ℝ) ^ (4 : ℕ)) ^ (((4 : ℕ) : ℝ)⁻¹) :=
            (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
        _ ≤ (2⁻¹ : ℝ) ^ (((4 : ℕ) : ℝ)⁻¹) :=
            Real.rpow_le_rpow (by positivity) (by norm_num) (by positivity)
        _ = (2⁻¹ : ℝ) ^ (1 / 4 : ℝ) := by norm_num
    exact h5.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  have h3 : 0 ≤ ℓ ^ (δ / 100 - 1 / 4) := Real.rpow_nonneg hℓ.le _
  nlinarith

/-- `W_ℓ ≤ 256 W_s` for `ℓ/32 ≤ s`. -/
theorem W_le_of_ge {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ} (hA : 0 ≤ A)
    {ℓ s : ℝ} (hℓ : 0 ≤ ℓ) (hs : ℓ / 32 ≤ s) : W M K A ℓ ≤ 256 * W M K A s := by
  have hs0 : 0 ≤ s := (div_nonneg hℓ (by norm_num)).trans hs
  have h1 := Proofs.ShortLengths.W_le_sixteen_mul hM hK (r := 2 * s) (s := ℓ) hA (by positivity) hℓ
    (by linarith only [hs])
  have h2 := Proofs.ShortLengths.W_le_sixteen_mul hM hK (r := s) (s := 2 * s) hA hs0
    (by positivity) (by linarith only [hs0])
  linarith only [h1, h2]

section Thick

variable {M : Model m} {K : ℕ} {A : ℝ} {ℓ : ℕ} {t : EuclideanSpace ℝ (Fin m)} {p : ℤ}
  {c : EuclideanSpace ℝ (Fin m)} {a a' : Vertex m} {T c₀ C₀ D L₀ : ℝ} {κT : ℕ}

/-- The bound for one pair of slopes: `|t_i − t| ≤ 64 √m κ β W/ℓ`, from `s(t_i − t) = E`,
`|E| ≤ W √m κ β + C₀`, `s ≥ ℓ/32`. -/
theorem Cfg.norm_slope_le (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {β : ℕ} (hβ : 1 ≤ β)
    {s : ℕ} (hs : (ℓ : ℝ) / 32 ≤ s) {u e : EuclideanSpace ℝ (Fin m)}
    (hu : (s : ℝ) • (u - t) = e)
    (he : ‖e‖ ≤ W M K A ℓ * (Real.sqrt m * ((κT * β : ℕ) : ℝ)) + C₀) :
    ‖u - t‖ ≤ 64 * Real.sqrt m * κT * β * W M K A ℓ / ℓ := by
  have hℓ := h.ℓ_pos
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (by positivity) hs
  have hW := h.W_pos
  have hβ1 : (1 : ℝ) ≤ β := by exact_mod_cast hβ
  have h1 := norm_sub_le_of_smul hs0 hu
  have hk1 := h.sqrt_κ_ge_one
  set X := Real.sqrt m * (κT : ℝ) * β * W M K A ℓ with hX
  have hX1 : W M K A ℓ ≤ X := by
    have : (1 : ℝ) ≤ Real.sqrt m * (κT : ℝ) * β := by nlinarith only [hk1, hβ1]
    rw [hX]
    nlinarith only [this, hW]
  have he' : ‖e‖ ≤ 2 * X := by
    have e1 : W M K A ℓ * (Real.sqrt m * ((κT * β : ℕ) : ℝ)) = X := by
      rw [hX]; push_cast; ring
    rw [e1] at he
    linarith only [he, h.hC₀, hX1, hW]
  have hX0 : 0 ≤ X := hW.le.trans hX1
  refine h1.trans ?_
  rw [div_le_div_iff₀ hs0 hℓ]
  have e2 : 64 * Real.sqrt m * (κT : ℝ) * β * W M K A ℓ = 64 * X := by rw [hX]; ring
  rw [e2]
  have h3 : ‖e‖ * (ℓ : ℝ) ≤ 2 * X * ℓ := mul_le_mul_of_nonneg_right he' hℓ.le
  have h4 : 2 * X * (ℓ : ℝ) ≤ 64 * X * s := by
    have := mul_le_mul_of_nonneg_left hs hX0
    nlinarith only [this]
  linarith only [h3, h4]

/-- The product `(ρ_β + √d) |t_i − t|` is at most `W/4`, "for `c₀` small". -/
theorem Cfg.rho_mul_slope_le (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {β : ℕ} (hβ : 1 ≤ β)
    (hβD : (β : ℝ) * W M K A ℓ ≤ D) :
    (c₀ * ℓ / β + rtd m) * (64 * Real.sqrt m * κT * β * W M K A ℓ / ℓ) ≤ W M K A ℓ / 4 := by
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have hℓ := h.ℓ_pos
  have hW := h.W_pos
  have hc := h.hc₀
  have hρ := h.rho_ge hβ hβD
  have hL0 := h.hL₀
  have hd0 := rtd_nonneg m
  have h1 : c₀ * ℓ / β + rtd m ≤ 2 * (c₀ * ℓ / β) := by linarith only [hρ, hL0, hd0]
  have hk : 0 ≤ Real.sqrt m * (κT : ℝ) := by positivity
  have h2 : 0 ≤ 64 * Real.sqrt m * κT * β * W M K A ℓ / ℓ := by positivity
  have e : 2 * (c₀ * ℓ / β) * (64 * Real.sqrt m * κT * β * W M K A ℓ / ℓ) =
      128 * (Real.sqrt m * κT * c₀) * W M K A ℓ := by
    field_simp
    ring
  have h3 : 128 * (Real.sqrt m * (κT : ℝ) * c₀) ≤ 1 / 4 := by linarith only [h.hc₀2]
  have h4 := mul_le_mul_of_nonneg_right h3 hW.le
  have h5 := mul_le_mul_of_nonneg_right h1 h2
  linarith only [h4, h5, e]

/-- The slope bound of a pair: `|t_i − t₀| ≤ (3/2) s^{δ/100−1/4}` for `s ≤ 2ℓ`, `(5/4) ℓ^{…}` being
`(3/2)(5/6) ℓ^{…}` (`five_sixths_rpow_le`). -/
theorem Cfg.slope_ge (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {β : ℕ}
    (hβD : (β : ℝ) * W M K A ℓ ≤ D) {s : ℕ} (hs0 : 0 < s) (hs : (s : ℝ) ≤ 2 * ℓ)
    {u : EuclideanSpace ℝ (Fin m)}
    (hu : ‖u - t‖ ≤ 64 * Real.sqrt m * κT * β * W M K A ℓ / ℓ) :
    ‖u - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  have hℓ := h.ℓ_pos
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs0
  have h1 := five_sixths_rpow_le h.hM.delta_pos h.hM.delta_le_one hs' hℓ hs
  have h2 : ‖u - M.t₀‖ ≤ ‖u - t‖ + ‖t - M.t₀‖ := norm_sub_le_norm_sub_add_norm_sub u t M.t₀
  have hk : 0 ≤ 64 * Real.sqrt m * (κT : ℝ) := by positivity
  have h3 : 64 * Real.sqrt m * κT * β * W M K A ℓ / ℓ ≤ 64 * Real.sqrt m * κT * D / ℓ := by
    refine div_le_div_of_nonneg_right ?_ hℓ.le
    have := mul_le_mul_of_nonneg_left hβD hk
    linarith only [this]
  have h4 := h.hDslope
  have h5 := h.ht
  linarith only [h1, h2, hu, h3, h4, h5]

/-- **One thickening**, for a member `i` of the family: by the inclusions in the thickenings of
`I''`, and Proposition `prop:profiles` for the pairs `{a}, I''` and `I'', {a'}`, a single `O₁`
variable `U` bounds `μ(x − a) + μ(a' − x) − T(a, x) − T(x, a')` on the thickening of the cube of
side `W`, by `ρ_β = c₀ℓ/β`, along `(1, t)`. -/
theorem Cfg.exists_thick (hSum : SignedOsSumStatement.{0, 0})
    (h : Cfg M K A ℓ t p c a a' T c₀ C₀ D L₀ κT) {N : ℕ} {κ C' : ℝ} (hC' : 0 < C')
    (hprof : ProfAt M K A N (κ / 32) C') (hκℓ : κ * N ≤ ℓ) (hℓN : ℓ ≤ N) {B : ℕ}
    (hB : (B : ℝ) * W M K A ℓ ≤ D) {i : Idx m} (hi : i ∈ family m B κT ℓ (c₀ * ℓ)) :
    ∃ U : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (4 * C' * Q M K A ℓ) U ∧ ∀ᵐ ω ∂M.P,
      ∀ x ∈ thicken (transverseCube (p + i.2.1 * gapOf (c₀ * ℓ) i.1)
          (ctr t c (W M K A ℓ - 1) (i.2.1 * gapOf (c₀ * ℓ) i.1) i.2.2) (W M K A ℓ)) t
          (c₀ * ℓ / i.1),
        M.μ.1 (point x - point a) + M.μ.1 (point a' - point x) ≤
          passageTimeReal ω a x + passageTimeReal ω x a' + U ω := by
  have hprob := h.hM.probP
  have hA0 : (0 : ℝ) ≤ A := by linarith only [h.hA]
  obtain ⟨hβ1, hβB⟩ := family_fst hi
  have hβ0 : (0 : ℝ) < i.1 := by exact_mod_cast hβ1
  have hW := h.W_pos
  have hβD : (i.1 : ℝ) * W M K A ℓ ≤ D := by
    have : (i.1 : ℝ) ≤ B := by exact_mod_cast hβB
    exact (mul_le_mul_of_nonneg_right this hW.le).trans hB
  have hℓ := h.ℓ_pos
  obtain ⟨hg1, hg2, hg3⟩ := h.gap_bounds hβ1 hβD
  obtain ⟨hr1, hr2⟩ := Cfg.index_bounds (ℓ := ℓ) (κT := κT) hi
  set g := gapOf (c₀ * ℓ) i.1 with hgdef
  set r : ℤ := i.2.1 * g with hrdef
  have hgℓ : (g : ℝ) ≤ ℓ / 2 ^ 16 := hg2.trans (h.rho_le hβ1)
  obtain ⟨s₁, s₂, he₁, he₂, hs₁l, hs₁u, hs₂l, hs₂u⟩ := h.exists_lengths hgℓ hr1 hr2
  set G := W M K A ℓ - 1 with hG
  have hG0 : 0 < G := by have := h.G_ge; linarith only [this, hW]
  have hGW : G ≤ W M K A ℓ := by linarith only [hG]
  set z := ctr t c G r i.2.2 with hz
  have hs₁0 : 0 < s₁ := by
    have : (0 : ℝ) < s₁ := lt_of_lt_of_le (by positivity) hs₁l
    exact_mod_cast this
  have hs₂0 : 0 < s₂ := by
    have : (0 : ℝ) < s₂ := lt_of_lt_of_le (by positivity) hs₂l
    exact_mod_cast this
  have hk := Cfg.norm_index_le (ℓ := ℓ) (κT := κT) hi
  have hkW : ‖G • transversePoint i.2.2‖ ≤ W M K A ℓ * (Real.sqrt m * ((κT * i.1 : ℕ) : ℝ)) := by
    rw [norm_smul, Real.norm_of_nonneg hG0.le]
    exact mul_le_mul hGW hk (norm_nonneg _) hW.le
  have hE₁ : ‖G • transversePoint i.2.2 - ofs t p c a‖ ≤
      W M K A ℓ * (Real.sqrt m * ((κT * i.1 : ℕ) : ℝ)) + C₀ :=
    (norm_sub_le _ _).trans (add_le_add hkW h.hao)
  have hE₂ : ‖ofs t p c a' - G • transversePoint i.2.2‖ ≤
      W M K A ℓ * (Real.sqrt m * ((κT * i.1 : ℕ) : ℝ)) + C₀ := by
    rw [add_comm (W M K A ℓ * _)]
    exact (norm_sub_le _ _).trans (add_le_add h.ha'o hkW)
  have ht₁ := h.norm_slope_le hβ1 hs₁l (smul_slopeL_sub (G := G) (k := i.2.2) hs₁0 he₁) hE₁
  have ht₂ := h.norm_slope_le hβ1 hs₂l (smul_slopeR_sub (G := G) (k := i.2.2) hs₂0 he₂) hE₂
  have hsℓ₁ : (s₁ : ℝ) ≤ 2 * ℓ := by linarith only [hs₁u, hℓ]
  have hsℓ₂ : (s₂ : ℝ) ≤ 2 * ℓ := by linarith only [hs₂u, hℓ]
  have hsl₁ := h.slope_ge hβD hs₁0 hsℓ₁ ht₁
  have hsl₂ := h.slope_ge hβD hs₂0 hsℓ₂ ht₂
  have hNr : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓN
  have hκs : ∀ s : ℝ, (ℓ : ℝ) / 32 ≤ s → κ / 32 * N ≤ s := fun s hs => by
    have : κ * N / 32 ≤ ℓ / 32 := div_le_div_of_nonneg_right hκℓ (by norm_num)
    linarith only [this, hs]
  have hW₁ := W_le_of_ge h.hM h.hK hA0 hℓ.le hs₁l
  have hW₂ := W_le_of_ge h.hM h.hK hA0 hℓ.le hs₂l
  have hb₁ : 0 ≤ (512 : ℝ) * W M K A s₁ := by
    have := Localization.W_nonneg (M := M) (K := K) (A := A) (s₁ : ℝ); positivity
  have hb₂ : 0 ≤ (512 : ℝ) * W M K A s₂ := by
    have := Localization.W_nonneg (M := M) (K := K) (A := A) (s₂ : ℝ); positivity
  have hpair₁ := isCubePair_left M K A (b₀ := 512) a hs₁0 z hW.le (by linarith only [hW₁]) hb₁
  have hpair₂ := isCubePair_right M K A (b₀ := 512) a' hs₂0 he₂ z hW.le
    (by linarith only [hW₂]) hb₂
  obtain ⟨X₁, hX₁, hae₁⟩ := hprof s₁ _ _ _ hpair₁ (hκs _ hs₁l) (by linarith only [hs₁u, hNr, hℓ])
    hsl₁
  obtain ⟨X₂, hX₂, hae₂⟩ := hprof s₂ _ _ _ hpair₂ (hκs _ hs₂l) (by linarith only [hs₂u, hNr, hℓ])
    hsl₂
  have hQ := h.Q_pos
  have hQ₁ : Q M K A s₁ ≤ 2 * Q M K A ℓ :=
    Proofs.ShortLengths.Q_le_two_mul h.hM h.hK hA0 (Nat.cast_nonneg _) hℓ.le hsℓ₁
  have hQ₂ : Q M K A s₂ ≤ 2 * Q M K A ℓ :=
    Proofs.ShortLengths.Q_le_two_mul h.hM h.hK hA0 (Nat.cast_nonneg _) hℓ.le hsℓ₂
  have hQ₁0 : 0 < Q M K A s₁ := Localization.Q_pos (by linarith only [h.hA])
    (by exact_mod_cast hs₁0)
  have hQ₂0 : 0 < Q M K A s₂ := Localization.Q_pos (by linarith only [h.hA])
    (by exact_mod_cast hs₂0)
  refine ⟨fun ω => X₁ ω + X₂ ω, ?_, ?_⟩
  · have h1 := isOs_add_of hSum le_rfl hX₁ hX₂ (by positivity) (by positivity)
    refine h1.mono_scale zero_le_one (by positivity) ?_
    nlinarith only [hQ₁, hQ₂, hC']
  -- the inclusions
  have hρ := h.rho_ge hβ1 hβD
  have hρ0 : 0 ≤ c₀ * ℓ / i.1 := by have := h.hc₀; positivity
  have hrs : ∀ s : ℝ, (ℓ : ℝ) / 32 ≤ s → c₀ * ℓ / i.1 + rtd m ≤ s / 1024 := fun s hs => by
    have h1 := h.rho_le hβ1
    have hd : rtd m ≤ c₀ * ℓ / i.1 := by
      have := h.hL₀; have := rtd_nonneg m; linarith only [hρ, this, h.hL₀]
    linarith only [h1, hd, hs, hℓ]
  have hsub : ∀ {u : EuclideanSpace ℝ (Fin m)},
      ‖u - t‖ ≤ 64 * Real.sqrt m * κT * i.1 * W M K A ℓ / ℓ →
      ∀ x ∈ thicken (transverseCube (p + r) z (W M K A ℓ)) t (c₀ * ℓ / i.1),
      x ∈ thicken (transverseCube (p + r) z (2 * W M K A ℓ)) u (c₀ * ℓ / i.1 + rtd m) := by
    intro u hu x hx
    refine thicken_subset_thicken h.htT le_rfl ?_ ?_ hx
    · have h1 := h.rho_mul_slope_le hβ1 hβD
      have h0 : 0 ≤ c₀ * ℓ / i.1 + rtd m := by have := rtd_nonneg m; linarith only [hρ0, this]
      have hu' : ‖t - u‖ ≤ 64 * Real.sqrt m * κT * i.1 * W M K A ℓ / ℓ := by
        rw [norm_sub_rev]; exact hu
      exact (mul_le_mul_of_nonneg_left hu' h0).trans h1
    · show (1 + T) * rtd m + 1 / 2 ≤ _
      linarith only [h.hW]
  filter_upwards [hae₁, hae₂] with ω hω₁ hω₂ x hx
  have hx₁ := thicken_mono (hrs _ hs₁l) (hsub ht₁ x hx)
  have hx₂ := thicken_mono (hrs _ hs₂l) (hsub ht₂ x hx)
  rw [he₁] at hx₁
  have ha₁ : a ∈ thicken (pointCube a) (slopeL s₁ a z) ((s₁ : ℝ) / 1024) :=
    mem_thicken_of_mem (by positivity) (mem_pointCube a)
  have ha₂ : a' ∈ thicken (pointCube a') (slopeR s₂ a' z) ((s₂ : ℝ) / 1024) :=
    mem_thicken_of_mem (by positivity) (mem_pointCube a')
  have b₁ := abs_le.1 (hω₁.1 a ha₁ x hx₁)
  have b₂ := abs_le.1 (hω₂.1 x hx₂ a' ha₂)
  linarith only [b₁.1, b₂.1]

end Thick

end CurvatureVariance.Paper.Localization.Loc
