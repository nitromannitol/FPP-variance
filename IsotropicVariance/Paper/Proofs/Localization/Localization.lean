/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.LocalFinal
public import IsotropicVariance.Paper.Proofs.Localization.Measurable
public import IsotropicVariance.Paper.Contracts.Profiles
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum
import IsotropicVariance.Paper.Proofs.Profiles.Scales

/-!
# Lemma `lem:localization`: helpers of the proof

The numerical facts, the two inputs at fixed `K, A, N` (`TreeAt`, equation `eq:tree`, and
`ParentAt`, equation `eq:parent`), and the errors of the boxes of the proof of Lemma
`lem:localization`. The proof is `Proofs.Localization.localizationStatement_of`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

universe u

open IsotropicVariance.Paper.Proofs.Profiles (Q_pos W_sq)
open IsotropicVariance.Paper.Proofs.Responses (transverseIntegerPoint)
namespace IsotropicVariance.Paper.Proofs.Localization

open Contracts Cited Infra.Os

variable {m : ℕ}

/-- A point of the supremum of the tree bound. -/
lemma le_treeSup (X : Setting m) {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (hB0 : 0 ≤ B) (ω : X.Ω)
    (x e : Pt m) (he : ‖e‖ = 1) {Z : Set (Pt m)} {c : Pt m} {R : ℝ}
    (hZ : ∀ z ∈ Z, dist z c ≤ R) {z : Pt m} (hz : z ∈ Z) :
    X.passTime ω x z - ⟪z - x, e⟫ ≤ ⨆ z : Z, (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫) :=
  le_ciSup (f := fun z : Z => X.passTime ω x z - ⟪(z : Pt m) - x, e⟫)
    (bddAbove_tree X hB hB0 ω x e he hZ) ⟨z, hz⟩

/-- A point of the supremum of the profile bound. -/
lemma le_profileSup {I I' : Set (Pt m)} (D : Pt m → Pt m → ℝ) {M : ℝ}
    (hD : ∀ u ∈ I, ∀ v ∈ I', |D u v - dist u v| ≤ M) {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I') :
    |D u v - dist u v| ≤ ⨆ (u : I) (v : I'), |D u v - dist (u : Pt m) (v : Pt m)| := by
  have hin : ∀ u' : I, BddAbove (range fun v : I' => |D u' v - dist (u' : Pt m) (v : Pt m)|) :=
    fun u' => ⟨M, by rintro _ ⟨v', rfl⟩; exact hD u' u'.2 v' v'.2⟩
  refine le_trans ?_ (le_ciSup (f := fun u' : I => ⨆ v : I', |D u' v - dist (u' : Pt m) (v : Pt m)|)
    ⟨max M 0, ?_⟩ ⟨u, hu⟩)
  · exact le_ciSup (f := fun v : I' => |D u v - dist u (v : Pt m)|) (hin ⟨u, hu⟩) ⟨v, hv⟩
  · rintro _ ⟨u', rfl⟩
    exact Real.iSup_le (fun v' => (hD u' u'.2 v' v'.2).trans (le_max_left _ _)) (le_max_right _ _)

/-! ## Numerical facts -/

lemma eps_le_of_W_le {n Wn : ℝ} (hn : 0 ≤ n) (hW : Wn ≤ 1 / (1000 * (Real.sqrt m + 1)) * n) :
    2 * Real.sqrt m * Wn ≤ n / 500 ∧ Wn ≤ n := by
  have hsm := Real.sqrt_nonneg (m : ℝ)
  have hd : 0 < 1000 * (Real.sqrt m + 1) := by positivity
  have hW' : Wn * (1000 * (Real.sqrt m + 1)) ≤ n := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hd] at hW; exact hW
  constructor <;> nlinarith [mul_nonneg hsm hn]

lemma region_le {a₀ b n r ε : ℝ} (ha₀ : 0 < a₀) (hb : 0 ≤ b) (hn : 1 ≤ n)
    (hr : r ≤ 2 * n) (hε : ε ≤ n / 500) :
    (b * (r + 2 * ε) + 1) / a₀ + ε ≤ (4 * (b + 1) / a₀ + 4) * n := by
  have h1 : b * (r + 2 * ε) + 1 ≤ (3 * b + 1) * n := by
    have e1 := mul_le_mul_of_nonneg_left (by linarith only [hr, hε, hn] :
      r + 2 * ε ≤ 3 * n) hb
    linarith only [e1, hn]
  have h2 : (b * (r + 2 * ε) + 1) / a₀ ≤ (3 * b + 1) * n / a₀ :=
    div_le_div_of_nonneg_right h1 ha₀.le
  have h3 : (3 * b + 1) * n / a₀ ≤ 4 * (b + 1) / a₀ * n := by
    rw [div_mul_eq_mul_div]
    have e3 := mul_nonneg (by linarith only [hb] : (0 : ℝ) ≤ b + 3)
      (by linarith only [hn] : (0 : ℝ) ≤ n)
    exact div_le_div_of_nonneg_right (by linarith only [e3]) ha₀.le
  linarith only [h2, h3, hε, hn]

/-! ## The contracts at fixed `K, A, N` -/

/-- The tree bound, equation `eq:tree`, at fixed `K, A, N`, for `16 ≤ t ≤ c₂N`. -/
def TreeAt (X : Setting m) (c₂ C : ℝ) (K : ℕ) (A N : ℝ) : Prop :=
  ∀ t : ℝ, 16 ≤ t → t ≤ c₂ * N →
    ∀ (x e : Pt m), ‖e‖ = 1 → ∀ B : Set (Pt m), IsRectBox B (x + t • e) →
      (∀ z ∈ B, ∀ z' ∈ B, dist z z' ≤ t / 8) →
      (∀ z ∈ B, infDist z (range fun r : ℝ => x + r • e) ≤
        16 * Real.sqrt (m + 1) * W K A t) →
        Cited.IsOs X.P 1 (C * Q K A t)
          (fun ω => ⨆ z : B, (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫))

/-- The parent bound, equation `eq:parent`, at fixed `K, A, N` (the body of `ParentStatement`). -/
def ParentAt (X : Setting m) (c₁ c₂ C : ℝ) (K : ℕ) (A N : ℝ) : Prop :=
  ∀ ℓ : ℝ, c₁ * N ≤ ℓ → ℓ ≤ c₂ * N →
    Cited.IsOs X.P 1 (Q K A ℓ / 100) (fun ω => |X.TRV ℓ ω - ℓ| - C * Q K A ℓ)

/-! ## The errors of the boxes -/

section Boxes

variable (X : Setting m) {C₀ CT CPar c₁ : ℝ} {K : ℕ} {A N n r : ℝ} (g : Pt m ≃ᵃⁱ[ℝ] Pt m)

lemma box_diam {W : ℝ} (hW : 0 ≤ W) (hε : 2 * Real.sqrt m * W ≤ n / 500)
    (jk : ℕ × (Fin m → ℤ)) :
    ∀ z ∈ g '' boxSet n W C₀ jk.1 jk.2, ∀ z' ∈ g '' boxSet n W C₀ jk.1 jk.2,
      dist z z' ≤ n / 16 / 8 := by
  rintro _ ⟨ζ, hζ, rfl⟩ _ ⟨ζ', hζ', rfl⟩
  have := mem_boxSet_dist_le (g := g) hW hζ hζ'
  have h0 : 0 ≤ 2 * Real.sqrt m * W := by positivity
  linarith

lemma measurable_parentFun (d c : ℝ) : Measurable fun x : ℝ => |x - d| - c :=
  ((continuous_abs.comp (continuous_id.sub continuous_const)).sub continuous_const).measurable

/-- The parent error for `T(a, x₊)` is `O_1(√L₀ Q_n/100)`. -/
lemma isOs_parentPlus (hm : 1 ≤ m) (hPK : ParentAt X c₁ (boxL m C₀) CPar K A N)
    (hK : 10 ≤ K) (hA : 0 < A) (hC₀ : 1 ≤ C₀) (hn : 0 < n) (hc₁n : c₁ * N ≤ n) (hnN : n ≤ N)
    (hr0 : 0 ≤ r) (hr2 : r ≤ 2 * n) (hW : 0 < W K A n) (hWn : W K A n ≤ n)
    {jk : ℕ × (Fin m → ℤ)} (hjk : jk ∈ boxIndex m n (W K A n) C₀) :
    IsOs X.P 1 (Real.sqrt (boxL m C₀) * Q K A n / 100)
      (parentPlus X g n (W K A n) C₀ CPar K A jk) := by
  obtain ⟨⟨hd1, hd2⟩, -⟩ := dist_box_bounds (r := r) g hn hW hWn hC₀ hr0 hr2 hjk
  have hL := one_le_boxL (m := m) (by linarith : (0 : ℝ) ≤ C₀)
  set d := dist (anchorA g n C₀) (plusPt g n (W K A n) C₀ jk.1 jk.2)
  have hdN := mul_le_mul_of_nonneg_left hnN (by linarith only [hL] : (0 : ℝ) ≤ boxL m C₀)
  have h := hPK d (by linarith only [hc₁n, hd1]) (by linarith only [hd2, hdN])
  have h2 := Profiles.isOs_passTime_of_TRV (X := X) hm (measurable_parentFun d (CPar * Q K A d))
    (anchorA g n C₀) (plusPt g n (W K A n) C₀ jk.1 jk.2) h
  refine IsOs.mono_scale h2 zero_le_one ?_ ?_
  · have := Q_pos (K := K) hA (by linarith only [hd1, hn] : 0 < d)
    positivity
  · have := (Profiles.Q_mono hK hA.le (by linarith only [hd1, hn]) hd2).trans
      (Q_mul_le hA.le hL hn.le)
    linarith only [this]

/-- The parent error for `T(x₋, b)` is `O_1(√L₀ Q_n/100)`. -/
lemma isOs_parentMinus (hm : 1 ≤ m) (hPK : ParentAt X c₁ (boxL m C₀) CPar K A N)
    (hK : 10 ≤ K) (hA : 0 < A) (hC₀ : 1 ≤ C₀) (hn : 0 < n) (hc₁n : c₁ * N ≤ n) (hnN : n ≤ N)
    (hr0 : 0 ≤ r) (hr2 : r ≤ 2 * n) (hW : 0 < W K A n) (hWn : W K A n ≤ n)
    {jk : ℕ × (Fin m → ℤ)} (hjk : jk ∈ boxIndex m n (W K A n) C₀) :
    IsOs X.P 1 (Real.sqrt (boxL m C₀) * Q K A n / 100)
      (parentMinus X g n r (W K A n) C₀ CPar K A jk) := by
  obtain ⟨-, ⟨hd1, hd2⟩⟩ := dist_box_bounds (r := r) g hn hW hWn hC₀ hr0 hr2 hjk
  have hL := one_le_boxL (m := m) (by linarith : (0 : ℝ) ≤ C₀)
  set d := dist (minusPt g n (W K A n) C₀ jk.1 jk.2) (anchorB g n r C₀)
  have hdN := mul_le_mul_of_nonneg_left hnN (by linarith only [hL] : (0 : ℝ) ≤ boxL m C₀)
  have h := hPK d (by linarith only [hc₁n, hd1]) (by linarith only [hd2, hdN])
  have h2 := Profiles.isOs_passTime_of_TRV (X := X) hm (measurable_parentFun d (CPar * Q K A d))
    (minusPt g n (W K A n) C₀ jk.1 jk.2) (anchorB g n r C₀) h
  refine IsOs.mono_scale h2 zero_le_one ?_ ?_
  · have := Q_pos (K := K) hA (by linarith only [hd1, hn] : 0 < d)
    positivity
  · have := (Profiles.Q_mono hK hA.le (by linarith only [hd1, hn]) hd2).trans
      (Q_mul_le hA.le hL hn.le)
    linarith only [this]

/-- The error of a box is `O_1(θ_U Q_n)`, `θ_U = 2C_T + 2√L₀/100`. -/
lemma isOs_boxError {W θT θP : ℝ} {jk : ℕ × (Fin m → ℤ)} (hθT : 0 < θT) (hθP : 0 < θP)
    (h1 : IsOs X.P 1 θT (treePlus X g n W C₀ jk))
    (h2 : IsOs X.P 1 θT (treeMinus X g n W C₀ jk))
    (h3 : IsOs X.P 1 θP (parentPlus X g n W C₀ CPar K A jk))
    (h4 : IsOs X.P 1 θP (parentMinus X g n r W C₀ CPar K A jk)) :
    IsOs X.P 1 (2 * θT + 2 * θP) (boxError X g n r W C₀ CPar K A jk) := by
  have h := Profiles.isOs_add (Profiles.isOs_add (Profiles.isOs_add h1 h2 hθT hθT) h3 (by positivity) hθP) h4
    (by positivity) hθP
  have e : θT + θT + θP + θP = 2 * θT + 2 * θP := by ring
  rw [e] at h
  exact h

/-- **The penalty** `G = max_{jk} (U_{jk} − Q_n|k|²/(2L₀))` is `O_1`: the weighted union bound
over the boxes, with the Gaussian sum `Σ_k e^{−c|k|²}` (the proof of Lemma `lem:localization`). -/
lemma isOs_boxPenalty {W Qn θ L₀ : ℝ} (hQn : Qn = Q K A n) (hθ : 0 < θ) (hQ : 0 < Qn)
    (hL₀ : 0 < L₀)
    (hU : ∀ jk ∈ boxIndex m n W C₀, IsOs X.P 1 (θ * Qn) (boxError X g n r W C₀ CPar K A jk)) :
    IsOs X.P 1 (Real.logb 2 (1 + 2 * (((boxCountLon C₀ : ℝ) + 1) *
        (2 / (1 - Real.exp (-(1 / (4 * L₀ * θ))))) ^ m)) * (2 * (θ * Qn)))
      (boxPenalty X g n r W C₀ CPar K A L₀) := by
  set cG := 1 / (4 * L₀ * θ)
  have hcG : 0 < cG := by positivity
  have hq : Real.exp (-cG) < 1 := Real.exp_lt_one_iff.2 (by linarith only [hcG])
  have hq0 : 0 < 1 - Real.exp (-cG) := by linarith only [hq]
  have hS : 1 ≤ ((boxCountLon C₀ : ℝ) + 1) * (2 / (1 - Real.exp (-cG))) ^ m := by
    have h2 : 1 ≤ 2 / (1 - Real.exp (-cG)) := by
      rw [le_div_iff₀ hq0]; linarith only [Real.exp_pos (-cG)]
    have h3 : 1 ≤ (2 / (1 - Real.exp (-cG))) ^ m := one_le_pow₀ h2
    have h4 : (1 : ℝ) ≤ (boxCountLon C₀ : ℝ) + 1 := by
      have := (boxCountLon C₀).cast_nonneg (α := ℝ)
      linarith only [this]
    exact one_le_mul_of_one_le_of_one_le h4 h3
  refine isOs_sup'_sub (boxIndex m n W C₀) (boxIndex_nonempty n W C₀) (by positivity) hS
    (fun jk => boxError X g n r W C₀ CPar K A jk)
    (fun jk => Q K A n * ‖transverseIntegerPoint jk.2‖ ^ 2 / (2 * L₀))
    (fun jk hjk => hQn ▸ hU jk hjk) ?_
  -- the Gaussian sum over the boxes
  have hterm : ∀ jk : ℕ × (Fin m → ℤ),
      Real.exp (-(Q K A n * ‖transverseIntegerPoint jk.2‖ ^ 2 / (2 * L₀)) / (2 * (θ * Qn))) =
        Real.exp (-cG * ∑ i, ((jk.2 i : ℝ)) ^ 2) := by
    intro jk
    rw [← norm_kvec_sq, ← hQn]
    congr 1
    simp only [cG]
    field_simp
    ring
  simp_rw [hterm]
  rw [boxIndex, Finset.sum_product]
  dsimp only
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum := sum_exp_neg_sq_le hcG m (boxRange n W C₀)
  have hpos : (0 : ℝ) ≤ (boxCountLon C₀ : ℝ) + 1 := by positivity
  push_cast
  exact mul_le_mul_of_nonneg_left hsum hpos

end Boxes

/-! ## The final scale -/

lemma curv_eq {n W Q : ℝ} (hn : 0 < n) (hWQ : W ^ 2 = n * Q) :
    4 * (2 * Real.sqrt m * W) ^ 2 / n = 16 * m * Q := by
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), hWQ]
  field_simp
  ring

lemma final_scale_le {θ₁ θ₂ θ₃ θ₄ κ e Q c' KH α A₀ : ℝ} (hc' : 0 < c') (hQ : 0 < Q)
    (hα : 0 ≤ α) (hsum : θ₁ + θ₂ + θ₃ + θ₄ + (κ + 1 + e + 1) / Real.log 2 ≤ KH * Q) :
    Real.sqrt (α * ((θ₁ + θ₂ + θ₃ + θ₄ + (κ + 1 + e + 1) / Real.log 2) / (c' * Q)) + A₀) ≤
      Real.sqrt (α * (KH / c') + A₀) := by
  refine Real.sqrt_le_sqrt (add_le_add (mul_le_mul_of_nonneg_left ?_ hα) le_rfl)
  rw [div_le_div_iff₀ (by positivity) hc']
  have := mul_le_mul_of_nonneg_right hsum hc'.le
  linarith only [this]

lemma abs_sub_dist_le {D d b : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ b * d) (hd : 0 ≤ d) :
    |D - d| ≤ (b + 1) * d := by
  rw [abs_le]; constructor <;> linarith only [hD0, hD, hd]

lemma dist_cubes_le {p : CubePair m} {n W κ : ℝ} (hp : p.IsAdmissible n W κ) {u v : Pt m}
    (hu : u ∈ p.first) (hv : v ∈ p.second) :
    dist u v ≤ dist p.center₁ p.center₂ + 4 * Real.sqrt m * W := by
  have h1 := CubePairFacts.dist_first_le hp hu
  have h2 := CubePairFacts.dist_second_le hp hv
  have := dist_triangle4 u p.center₁ p.center₂ v
  rw [dist_comm p.center₂ v] at this
  linarith only [h1, h2, this]

lemma slabDensity_ge (sl : Slab m) {b : ℝ} {σ : Pt m → ℝ} (hσ : ∀ x, σ x ≤ b) (x : Pt m) :
    σ x ≤ sl.density b σ x := by
  unfold Slab.density
  split_ifs
  · exact hσ x
  · exact le_rfl

end IsotropicVariance.Paper.Proofs.Localization
