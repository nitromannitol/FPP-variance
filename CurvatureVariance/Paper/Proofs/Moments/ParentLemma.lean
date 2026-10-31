/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Inputs
public import CurvatureVariance.Paper.Proofs.Moments.Parent
public import CurvatureVariance.Paper.Proofs.Moments.ParentCombine
public import CurvatureVariance.Paper.Proofs.Moments.ExpArrayBounds
import CurvatureVariance.Infra.Os.Basic
import CurvatureVariance.Paper.Proofs.Moments.Weights
import CurvatureVariance.Paper.Proofs.Chart.Rounding
import CurvatureVariance.Paper.Proofs.Moments.WidthMargin
import CurvatureVariance.Infra.FPP.TimeConstantNorm
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.ShortLengths.ShortDet

/-!
# Lemma `lem:parent`

`parent_instance` and `parentStatement` (the latter below): the proof of Lemma `lem:parent` with
`t := y/(Ms)` and the range `7/4`, from equation `eq:rowenergy`, Lemma `lem:good`, Lemma
`lem:slabs` (2) and the classical estimates. The target is `(Ms, y)`, as in the paper, with no
rounding: `norm_sub_target_le` gives `|t − t₀| ≤ 2(Ms)^{δ/100−1/4}` from the range
`7/4`, for `N` large, and `l1Dist_same_le` the distance from `(Ms, y)` to `(ℓ, y)`, at most `Ms`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

namespace Parent

/-- The coordinates differ by at most `Ms` when `z = y`: the points `(Ms s, y)` and `(ℓ, y)` with
`Ms s ≤ ℓ < Ms s + Ms` are at distance at most `Ms`, which is at most `pathBound`. -/
theorem l1Dist_same_le {M : Model m} {ℓ s Ms : ℕ} {y : Fin m → ℤ}
    (h1 : Ms * s ≤ ℓ) (h2 : ℓ < Ms * s + Ms) :
    (Infra.FPP.l1Dist (((Ms * s : ℕ) : ℤ), y) ((ℓ : ℤ), y) : ℝ) ≤ pathBound m Ms ‖M.t₀‖ := by
  have h3 : Infra.FPP.l1Dist (((Ms * s : ℕ) : ℤ), y) ((ℓ : ℤ), y) ≤ Ms := by
    simp only [Infra.FPP.l1Dist, sub_self, Int.natAbs_zero, Finset.sum_const_zero, add_zero]
    omega
  have h4 : (Infra.FPP.l1Dist (((Ms * s : ℕ) : ℤ), y) ((ℓ : ℤ), y) : ℝ) ≤ Ms := by
    exact_mod_cast h3
  refine h4.trans ?_
  have hτ := norm_nonneg M.t₀
  have hm1 : (1 : ℝ) ≤ m + 1 := by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hsq := Real.sqrt_nonneg (m : ℝ)
  have hMs0 : (0 : ℝ) ≤ Ms := Nat.cast_nonneg Ms
  unfold pathBound
  have h6 := mul_le_mul_of_nonneg_left (by linarith only [hτ] : (1 : ℝ) ≤ ‖M.t₀‖ + 1)
    (by linarith only [hMs0] : (0 : ℝ) ≤ (Ms : ℝ) + 1)
  have h5 : (Ms : ℝ) ≤ ((Ms : ℝ) + 1) * (‖M.t₀‖ + 1) + 2 * Real.sqrt m := by
    linarith only [h6, hsq]
  exact h5.trans (le_mul_of_one_le_left (hMs0.trans h5) hm1)

/-- `(L + x)^e ≤ L^e + x` for `L ≥ 1`, `x ≥ 0` and `0 < e ≤ 1`. -/
private theorem rpow_add_le_rpow_add {L x e : ℝ} (hL1 : 1 ≤ L) (hx : 0 ≤ x) (he0 : 0 < e)
    (he1 : e ≤ 1) : (L + x) ^ e ≤ L ^ e + x := by
  have hL0 : 0 < L := by linarith only [hL1]
  have hxL : 0 ≤ x / L := div_nonneg hx hL0.le
  have a2 : L + x = L * (1 + x / L) := by field_simp
  have a3 := rpow_one_add_le_one_add_mul_self (s := x / L) (by linarith only [hxL]) he0.le he1
  have a4 : L ^ e ≤ L := by
    calc L ^ e ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 he1
      _ = L := Real.rpow_one L
  have hLe0 : 0 ≤ L ^ e := Real.rpow_nonneg hL0.le e
  have a5 : (L + x) ^ e = L ^ e * (1 + x / L) ^ e := by
    rw [a2, Real.mul_rpow hL0.le (by linarith only [hxL])]
  have a6 : L ^ e * (1 + x / L) ^ e ≤ L ^ e * (1 + e * (x / L)) :=
    mul_le_mul_of_nonneg_left a3 hLe0
  have a7 : L ^ e * (e * (x / L)) ≤ x := by
    have e7 : L ^ e * (e * (x / L)) = (L ^ e / L) * e * x := by field_simp
    rw [e7]
    have b2 := mul_le_mul ((div_le_one hL0).mpr a4) he1 he0.le zero_le_one
    rw [mul_one] at b2
    exact mul_le_of_le_one_left hx b2
  rw [a5]
  refine a6.trans ?_
  rw [mul_add, mul_one]
  exact add_le_add le_rfl a7

/-- **`y` is within `2L^{3/4+δ/100}` of `Lt₀`**, for `L = Ms s`: from `|y − ℓt₀| ≤ (7/4)ℓ^{3/4+δ/100}`
with `L ≤ ℓ < L + Ms`, once `(7 + 4τ)Ms ≤ L^{3/4+δ/100}`. This is the step of the proof of Lemma
`lem:parent`: `|t − t₀| ≤ 2(Ms)^{δ/100−1/4}` for `t = y/(Ms)`. -/
theorem norm_sub_target_le {M : Model m} (hM : M.Standing) {s Ms ℓ : ℕ} {y : Fin m → ℤ} {τ : ℝ}
    (hs1 : 1 ≤ s) (hMs : 1 ≤ Ms) (h1 : Ms * s ≤ ℓ) (h2 : ℓ < Ms * s + Ms)
    (hτ : ‖M.t₀‖ ≤ τ)
    (hy : ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤ 7 / 4 * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hL : (7 + 4 * τ) * Ms ≤ ((Ms * s : ℕ) : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) :
    ‖transversePoint y - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
      2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := by
  set L : ℝ := ((Ms * s : ℕ) : ℝ) with hLdef
  set e : ℝ := (3 : ℝ) / 4 + M.δ / 100 with he
  have hδ0 := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have he0 : 0 < e := by rw [he]; linarith only [hδ0]
  have he1 : e ≤ 1 := by rw [he]; linarith only [hδ1]
  have hMs' : (1 : ℝ) ≤ Ms := by exact_mod_cast hMs
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]; exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hℓL : (ℓ : ℝ) ≤ L + Ms := by
    have : ℓ ≤ Ms * s + Ms := by omega
    rw [hLdef]; push_cast; exact_mod_cast this
  have hLℓ : L ≤ (ℓ : ℝ) := by rw [hLdef]; exact_mod_cast h1
  have hτ0 := norm_nonneg M.t₀
  have hMs0 : (0 : ℝ) ≤ Ms := Nat.cast_nonneg Ms
  have hℓpow : (ℓ : ℝ) ^ e ≤ L ^ e + Ms :=
    (Real.rpow_le_rpow (Nat.cast_nonneg ℓ) hℓL he0.le).trans
      (rpow_add_le_rpow_add hL1 hMs0 he0 he1)
  have hsplit : transversePoint y - L • M.t₀ =
      (transversePoint y - (ℓ : ℝ) • M.t₀) + ((ℓ : ℝ) - L) • M.t₀ := by
    rw [sub_smul]; abel
  rw [show (1 : ℝ) + (M.δ / 100 - 1 / 4) = e by rw [he]; ring]
  have b1 : ‖((ℓ : ℝ) - L) • M.t₀‖ ≤ Ms * τ := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith only [hLℓ])]
    exact mul_le_mul (by linarith only [hℓL]) hτ hτ0 hMs0
  have b2 := mul_le_mul_of_nonneg_left hℓpow (by norm_num : (0 : ℝ) ≤ 7 / 4)
  calc ‖transversePoint y - L • M.t₀‖
      ≤ ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ + ‖((ℓ : ℝ) - L) • M.t₀‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ 7 / 4 * (L ^ e + Ms) + Ms * τ := add_le_add (hy.trans b2) b1
    _ ≤ 2 * L ^ e := by linarith only [hL]

/-- **Lemma `lem:parent` at one scale**, as in the paper: the conclusion for `κN ≤ ℓ ≤ 3N`,
`|y − ℓt₀| ≤ (7/4)ℓ^{3/4+δ/100}`, from equation `eq:rowenergy` at `(Ms, y)` with `t = y/(Ms)`
(no rounding), Lemma `lem:slabs` (2), `μ ≤ E T`, the lower deviations, the bounded paths and the
conditions on `N`. -/
theorem parent_instance {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {N : ℕ} {κ : ℝ} (hκ : 0 < κ) {Ms : ℕ} (hMs128 : 128 ≤ Ms)
    {cE CE Csl C₁ θ₀ hi : ℝ} (hcE : 0 < cE) (hCE : 0 < CE) (hCsl : 0 < Csl) (hC₁ : 0 < C₁)
    (hθ₀ : 0 < θ₀) (hhi0 : 0 ≤ hi)
    (hMsCE : CE * (1 / (Ms : ℝ)) ^ ((1 : ℝ) / 3) ≤ 1 / 200)
    (hExpN : ∀ s : ℕ, Real.sqrt N ≤ s → ((Ms * s : ℕ) : ℝ) ≤ 3 * N →
      ∀ z : Fin m → ℤ, ‖transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
        2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) →
      ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (CE * Q M K A s) X ∧ ∀ᵐ ω ∂M.P,
        ∀ Y : Fin (Ms + 1) → Fin m → ℤ,
          IsMinTuple M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) Y →
          |(slabMin M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)).toReal -
              M.μ.1 (point (((Ms * s : ℕ) : ℤ), z))| +
            cE * Q M K A s * ∑ i : Fin Ms,
              indexJumpSq s (wInt M K A s) (targetSlope (Ms * s) z) Y i ≤
            CE * Ms * Q M K A s + X ω)
    {G : ℝ → Set (Config m)}
    (hGind : ∀ S : ℝ, Real.log N ≤ S →
      CurvatureVariance.IsOs M.P 2 (Csl / S) ((G S)ᶜ.indicator fun _ => (1 : ℝ)))
    (hGiii : ∀ S : ℝ, Real.log N ≤ S → ∀ ω ∈ G S, ∀ (n ℓ' : ℕ) (t : EuclideanSpace ℝ (Fin m)),
      Real.sqrt N ≤ n → n ≤ ℓ' → (ℓ' : ℝ) ≤ 3 * N → ∀ u v : Vertex m,
      point v - point u = (ℓ' : ℝ) • slopeVec t → ‖t - M.t₀‖ ≤ 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) →
      InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) u → InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) v →
      ∀ K' : ℕ, ℓ' = K' * n →
      S ≤ (N : ℝ) ^ (M.δ / 1000) →
      slabMin M ω n K' t u v ≤ (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (Csl * K' * S ^ 2))
    (hcl : ∀ x : Vertex m, x ≠ 0 → M.μ.1 (point x) ≤ ∫ ω, passageTimeReal ω 0 x ∂M.P)
    (hdev : ∀ x : Vertex m, x ≠ 0 →
      CurvatureVariance.IsOs M.P 2 (2 * Real.sqrt ((l1Norm x + 1) / C₁)) (fun ω =>
        max ((∫ ω', passageTimeReal ω' 0 x ∂M.P) - passageTimeReal ω 0 x) 0))
    (hw : ∀ e : Edge m, CurvatureVariance.IsOs M.P 1 θ₀ (fun ω => (ω e : ℝ)))
    (hb : ∀ x : Pt m, M.μ.1 x ≤ hi * ‖x‖)
    (hN1 : (1 : ℝ) ≤ N) (hE2 : 2 * Ms / κ + 2 + 256 * m ≤ Real.sqrt N) (hE3 : 32 ≤ κ * N)
    (hE4 : Real.log N ≤ (N : ℝ) ^ (M.δ / 1000))
    (hE5 : Csl * Ms + 400 * (θ₀ * (pathBound m Ms ‖M.t₀‖ + 1)) ≤
      κ ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3 - M.δ / 500))
    (hE6 : 2400 * Csl * Real.sqrt ((m + 2) * (1 + ‖M.t₀‖) / C₁) ≤ (N : ℝ) ^ (9 * M.δ / 10000))
    (hE7 : (7 + 4 * ‖M.t₀‖) * Ms ≤ (N : ℝ) ^ ((3 : ℝ) / 8))
    {ℓ : ℕ} (hℓ1 : κ * N ≤ ℓ) (hℓ2 : (ℓ : ℝ) ≤ 3 * N) {y : Fin m → ℤ}
    (hy : ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤ 7 / 4 * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) :
    CurvatureVariance.IsOs M.P 1 (Q M K A ℓ / 100) (fun ω =>
      |passageTimeReal ω 0 ((ℓ : ℤ), y) - M.μ.1 (point ((ℓ : ℤ), y))| -
        (Ms / 200 + hi * pathBound m Ms ‖M.t₀‖ + 1) * Q M K A ℓ) := by
  have := hM.probP
  have hδ := hM.delta_pos
  set D : ℝ := pathBound m Ms ‖M.t₀‖ with hD
  have hD0 : 0 ≤ D := pathBound_nonneg m Ms (norm_nonneg _)
  have hMs1 : (1 : ℝ) ≤ Ms := by exact_mod_cast (by omega : 1 ≤ Ms)
  -- the scale `s`
  set s : ℕ := ℓ / Ms with hsdef
  have hℓ32' : (32 : ℝ) ≤ ℓ := hE3.trans hℓ1
  have hℓ32 : 32 ≤ ℓ := by exact_mod_cast hℓ32'
  have hℓ0 : 0 < ℓ := by omega
  have hm0 : (0 : ℝ) ≤ 256 * m := mul_nonneg (by norm_num) (Nat.cast_nonneg m)
  have hMk0 : (0 : ℝ) ≤ 2 * Ms / κ :=
    div_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg Ms)) hκ.le
  have hsN : Real.sqrt N ≤ s := sqrt_le_parentS hκ (by omega) hℓ1 (by linarith only [hE2, hm0])
  have hs256 : (256 * m : ℝ) ≤ s := by linarith only [hsN, hE2, hMk0]
  have hs2' : (2 : ℝ) ≤ s := by linarith only [hsN, hE2, hMk0, hm0]
  have hs2 : 2 ≤ s := by exact_mod_cast hs2'
  have hs1 : 1 ≤ s := by omega
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hMspos : 0 < Ms * s := Nat.mul_pos (by omega) (by omega)
  have hMsℓ : Ms * s ≤ ℓ := mul_div_le ℓ Ms
  have hMsℓ' : ((Ms * s : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast hMsℓ
  have hMsℓ'' : (Ms : ℝ) * s ≤ ℓ := by push_cast at hMsℓ'; exact hMsℓ'
  have hMsN : ((Ms * s : ℕ) : ℝ) ≤ 3 * N := hMsℓ'.trans hℓ2
  have hMs32 : 32 ≤ Ms * s := by
    have : 128 * 1 ≤ Ms * s := Nat.mul_le_mul hMs128 hs1
    omega
  -- `1 ≤ Ms s` and `m ≤ Ms s`
  have hMs1' : (1 : ℝ) ≤ ((Ms * s : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Ms * s)
  have hmMs : (m : ℝ) ≤ ((Ms * s : ℕ) : ℝ) := by
    have h1 : (s : ℝ) ≤ ((Ms * s : ℕ) : ℝ) := by
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hMs1
    have h2 : (m : ℝ) ≤ 256 * m := by have := Nat.cast_nonneg (α := ℝ) m; linarith only [this]
    linarith only [h1, h2, hs256]
  -- the target `(Ms, y)`, with `t = y/(Ms)`: no rounding
  set z : Fin m → ℤ := y with hzdef
  have hMsN32 : (1 : ℝ) ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hLe : (N : ℝ) ^ ((3 : ℝ) / 8) ≤ ((Ms * s : ℕ) : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
    have h1 : (N : ℝ) ^ ((3 : ℝ) / 8) = Real.sqrt N ^ ((3 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith only [hN1])]; norm_num
    have hsL : (Real.sqrt N) ≤ ((Ms * s : ℕ) : ℝ) := by
      refine hsN.trans ?_
      push_cast; exact le_mul_of_one_le_left (Nat.cast_nonneg _) hMs1
    rw [h1]
    exact (Real.rpow_le_rpow (Real.sqrt_nonneg _) hsL (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith only [hMsN32, hsL])
        (by linarith only [hM.delta_pos]))
  have hz : ‖transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
      2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) :=
    norm_sub_target_le hM hs1 (by omega) (mul_div_le ℓ Ms) (lt_mul_div_add (by omega) ℓ)
      le_rfl hy (hE7.trans hLe)
  set t := targetSlope (Ms * s) z with ht
  have hℓ1' : (1 : ℝ) ≤ ℓ := by linarith only [hℓ32']
  have hQℓ1 : 1 ≤ Q M K A ℓ := by
    have h1 := rpow_third_le_Q hM hK hA hℓ1'
    have h2 : (1 : ℝ) ≤ (ℓ : ℝ) ^ ((1 : ℝ) / 3) := Real.one_le_rpow hℓ1' (by norm_num)
    linarith only [h1, h2]
  have hQℓ0 : 0 < Q M K A ℓ := by linarith only [hQℓ1]
  have hQs1 := Proofs.ShortLengths.one_le_Q hM hK hA hs1'
  have hQ5 := Q_ge_of_E5 hM hK hA hκ hN1 hℓ1 hℓ1' hE5
  have hNp : (1 : ℝ) ≤ (N : ℝ) ^ (M.δ / 500) := Real.one_le_rpow hN1 (by linarith only [hδ])
  have hθD : 0 ≤ θ₀ * (D + 1) := mul_nonneg hθ₀.le (by linarith only [hD0])
  have hCslMs : 0 ≤ Csl * Ms := mul_nonneg hCsl.le (Nat.cast_nonneg Ms)
  have h400 : 0 ≤ 400 * (θ₀ * (D + 1)) := mul_nonneg (by norm_num) hθD
  have hB5 : 0 ≤ Csl * Ms + 400 * (θ₀ * (D + 1)) := add_nonneg hCslMs h400
  have hQ5' : Csl * Ms + 400 * (θ₀ * (D + 1)) ≤ Q M K A ℓ :=
    (le_mul_of_one_le_right hB5 hNp).trans hQ5
  -- equation `eq:rowenergy`
  obtain ⟨X, hX, hXae⟩ := hExpN s hsN hMsN z hz
  have hsE := scale_E hM hK hA hCE.le hs1' hMs1 hMsℓ'' hMsCE
  have hXs : CurvatureVariance.IsOs M.P 1 (Q M K A ℓ / 200) X :=
    hX.mono_scale zero_le_one (mul_pos hCE (by linarith only [hQs1])) hsE
  -- Lemma `lem:slabs` (2)
  set S : ℝ := (N : ℝ) ^ (M.δ / 1000) with hS
  have hpt : point (((Ms * s : ℕ) : ℤ), z) - point (0 : Vertex m) =
      ((Ms * s : ℕ) : ℝ) • slopeVec t := by
    rw [Infra.FPP.point_zero, sub_zero]; exact ExpArray.point_target hMspos z
  have hτ := norm_nonneg M.t₀
  have hbox00 : 0 ≤ 3 * (1 + ‖M.t₀‖) * (N : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hτ])) (Nat.cast_nonneg N)
  have hbox0 : InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) (0 : Vertex m) :=
    ⟨by simpa only [Prod.fst_zero, Int.cast_zero, abs_zero] using hbox00, fun j => by
      simpa only [Prod.snd_zero, Pi.zero_apply, Int.cast_zero, abs_zero] using hbox00⟩
  have hbox : InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) (((Ms * s : ℕ) : ℤ), z) := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    refine ⟨?_, fun j => ?_⟩
    · simp only [Int.cast_natCast]
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      linarith only [hMsN, mul_nonneg hτ hN0]
    · refine (abs_round_le hM hMs32 hz j).trans ?_
      have := mul_le_mul_of_nonneg_left hMsN (by linarith only [hτ] : (0 : ℝ) ≤ 1 + ‖M.t₀‖)
      linarith only [this]
  have hGF : ∀ ω ∈ G S, slabMin M ω s Ms t 0 (((Ms * s : ℕ) : ℤ), z) ≤
      (passageTime ω 0 (((Ms * s : ℕ) : ℤ), z) : ℝ≥0∞) +
        ENNReal.ofReal (Csl * Ms * S ^ 2) := fun ω hω =>
    hGiii S hE4 ω hω s (Ms * s) t hsN (Nat.le_mul_of_pos_left s (by omega)) hMsN 0 _
      hpt (norm_targetSlope_le hM hs1 (by omega) hz) hbox0 hbox Ms rfl le_rfl
  have hS2 : S ^ 2 = (N : ℝ) ^ (M.δ / 500) := by
    rw [hS, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1; push_cast; ring
  -- the classical estimates and the lower deviations at `(Ms, Mst)`
  have hx0 : (((Ms * s : ℕ) : ℤ), z) ≠ (0 : Vertex m) := by
    intro h
    have := congrArg Prod.fst h
    simp only [Prod.fst_zero] at this
    omega
  have hθd : 0 < 2 * Real.sqrt ((l1Norm (((Ms * s : ℕ) : ℤ), z) + 1) / C₁) :=
    mul_pos two_pos (Real.sqrt_pos.mpr (div_pos (Nat.cast_add_one_pos _) hC₁))
  have hB0 : 0 < ((m : ℝ) + 2) * (1 + ‖M.t₀‖) :=
    mul_pos (by linarith only [hm0]) (by linarith only [hτ])
  have hprodScale := prod_scale_le (M := M) (A := A)
    (L := (l1Norm (((Ms * s : ℕ) : ℤ), z) : ℝ) + 1) hM hK hA hCsl hC₁ hB0 hN1 hℓ1'
    hℓ2 (l1Norm_parent_le (Ms := Ms) hM hℓ32 hMs32 hz) hE6
  -- the coordinate path
  have hl1' : (Infra.FPP.l1Dist (((Ms * s : ℕ) : ℤ), z) ((ℓ : ℤ), y) : ℝ) ≤ D :=
    l1Dist_same_le (Ms := Ms) (mul_div_le ℓ Ms) (lt_mul_div_add (by omega) ℓ)
  have hTc : CurvatureVariance.IsOs M.P 1 (Q M K A ℓ / 400)
      (fun ω => passageTimeReal ω (((Ms * s : ℕ) : ℤ), z) ((ℓ : ℤ), y)) := by
    refine (isOs_passageTimeReal_l1Dist hM hθ₀ hw _ _).mono_scale zero_le_one
      (mul_pos hθ₀ (Nat.cast_add_one_pos _)) ?_
    have h2 : θ₀ * ((Infra.FPP.l1Dist (((Ms * s : ℕ) : ℤ), z) ((ℓ : ℤ), y) : ℝ) + 1) ≤
        θ₀ * (D + 1) := mul_le_mul_of_nonneg_left (by linarith only [hl1']) hθ₀.le
    linarith only [h2, hCslMs, hQ5']
  have hd := abs_mu_sub_le hhi0 hb ((ℓ : ℤ), y) (((Ms * s : ℕ) : ℤ), z)
  have hd' : |M.μ.1 (point ((ℓ : ℤ), y)) - M.μ.1 (point (((Ms * s : ℕ) : ℤ), z))| ≤ hi * D :=
    hd.trans (mul_le_mul_of_nonneg_left hl1' hhi0)
  -- the deterministic terms
  have hBE : CE * Ms * Q M K A s ≤ Ms / 200 * Q M K A ℓ := by
    have h := mul_le_mul_of_nonneg_left hsE (by linarith only [hMs1] : (0 : ℝ) ≤ Ms)
    calc CE * Ms * Q M K A s = Ms * (CE * Q M K A s) := by ring
      _ ≤ Ms * (Q M K A ℓ / 200) := h
      _ = Ms / 200 * Q M K A ℓ := by ring
  have hC : CE * Ms * Q M K A s + hi * D + Csl * Ms * S ^ 2 ≤
      (Ms / 200 + hi * D + 1) * Q M K A ℓ := by
    rw [hS2]
    have h1 : hi * D ≤ hi * D * Q M K A ℓ := le_mul_of_one_le_right (mul_nonneg hhi0 hD0) hQℓ1
    have h2 : Csl * Ms * (N : ℝ) ^ (M.δ / 500) ≤ Q M K A ℓ := by
      have h3 := mul_nonneg h400 (zero_le_one.trans hNp)
      have h4 := hQ5
      rw [add_mul] at h4
      linarith only [h3, h4]
    have h5 : (Ms / 200 + hi * D + 1) * Q M K A ℓ =
        Ms / 200 * Q M K A ℓ + hi * D * Q M K A ℓ + Q M K A ℓ := by ring
    linarith only [hBE, h1, h2, h5]
  have hS0 : 0 < S := Real.rpow_pos_of_pos (by linarith only [hN1]) _
  exact parent_combine hM hs2 hQℓ0 hcE.le (by linarith only [hQs1]) hXs hXae
    (floorTuple_adm' hM hs256 hs1 hMspos z) (mul_nonneg hCslMs (sq_nonneg S)) hGF
    (div_pos hCsl hS0) hθd (hGind S hE4) (hdev _ hx0) hprodScale (hcl _ hx0) hTc hd' hC

end Parent

open Parent

/-- **Lemma `lem:parent`**, equation `eq:parent`, from equation `eq:rowenergy`, Lemma `lem:good`,
Lemma `lem:slabs` (2), the classical estimates and the sum rule, with `t := y/(Ms)` as in the
paper. `ChainsExistStatement` and `SignedOsSumStatement` are premises of the implication that the
proof does not use: the chain of the comparison is that of Lemma `lem:slabs` (2), and the sum rule
is used in the form of [AKM, Lemma A.4], via `Moments.isOs_add`. -/
theorem parentStatement (hExp : Contracts.ExpArrayStatement m)
    (hGood : Contracts.GoodStatement m) (hSlabs : Contracts.SlabsStatement m)
    (_hChains : Contracts.ChainsExistStatement m) (hClassical : Contracts.ClassicalStatement m)
    (_hSigned : Contracts.SignedOsSumStatement.{0, 0}) : Contracts.ParentStatement m := by
  intro bd hbd Cstar
  obtain ⟨cE, CE, hcE, hCE, hExpK⟩ := hExp bd hbd Cstar
  obtain ⟨cg, Cg, hcg, hCg, Ng, hGoodK⟩ := hGood bd hbd
  obtain ⟨Csl₀, hCsl₀, Nsl, hNsl⟩ := hSlabs bd hbd Cg cg hCg hcg
  set Csl : ℝ := max Cg Csl₀ with hCsldef
  have hCsl : 0 < Csl := lt_max_of_lt_left hCg
  obtain ⟨Ccl, -, hcl⟩ := hClassical bd hbd
  obtain ⟨C₁, hC₁, hdev₀⟩ := isOs_lowerDev hbd.law
  obtain ⟨θ₀, hθ₀, hw₀⟩ := exists_isOs_weight hbd.law
  obtain ⟨lo, hi, -, hhi0, hb'⟩ := Infra.FPP.PtNorm.exists_bounds bd.law.μ
  set T := bd.T with hTdef
  have hT0 : 0 ≤ T := hbd.T_nonneg
  set Ms : ℕ := max 128 ⌈(200 * CE) ^ 3⌉₊ with hMsdef
  have hMs128 : 128 ≤ Ms := le_max_left _ _
  have hMsCE : CE * (1 / (Ms : ℝ)) ^ ((1 : ℝ) / 3) ≤ 1 / 200 := by
    have h1 : (200 * CE) ^ (3 : ℕ) ≤ (Ms : ℝ) :=
      (Nat.le_ceil _).trans (by
        have h : ⌈(200 * CE) ^ (3 : ℕ)⌉₊ ≤ Ms := le_max_right _ _
        exact_mod_cast h)
    have h2 : 200 * CE ≤ (Ms : ℝ) ^ ((1 : ℝ) / 3) := by
      have h3 : ((200 * CE) ^ 3) ^ ((1 : ℝ) / 3) = 200 * CE := by
        rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
      rw [← h3]
      exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have hMs1 : (1 : ℝ) ≤ Ms := by exact_mod_cast (by omega : 1 ≤ Ms)
    have hMs0 : (0 : ℝ) < Ms := by linarith only [hMs1]
    rw [Real.div_rpow zero_le_one hMs0.le, Real.one_rpow, ← div_eq_mul_one_div,
      div_le_iff₀ (Real.rpow_pos_of_pos hMs0 _)]
    linarith only [h2]
  refine ⟨Ms / 200 + hi * pathBound m Ms T + 1,
    add_pos_of_nonneg_of_pos (add_nonneg (by positivity)
      (mul_nonneg hhi0.le (pathBound_nonneg m Ms hT0))) one_pos,
    fun κ hκ K hK => ?_⟩
  obtain ⟨NE, hNE⟩ := hExpK K hK
  obtain ⟨Nev, hNev⟩ := eventually_atTop.mp
    ((eventually_parent bd.law hbd.law hκ
      (2 * Ms / κ + 2 + 256 * m) (Csl * Ms + 400 * (θ₀ * (pathBound m Ms T + 1)))
      (2400 * Csl * Real.sqrt ((m + 2) * (1 + T) / C₁))).and
      (eventually_le_rpow ((7 + 4 * T) * Ms) (p := (3 : ℝ) / 8) (by norm_num)))
  refine ⟨max NE (max Ng (max Nsl Nev)), fun M hM hfit N hN A hA hPrem hRange ℓ hℓ1 hℓ2 y hy => ?_⟩
  have hTM : ‖M.t₀‖ ≤ T := hfit.t₀_le
  have hdev := hdev₀
  rw [← hfit.P_eq] at hdev
  have hw := hw₀
  rw [← hfit.P_eq] at hw
  have hb : ∀ x : Pt m, M.μ.1 x ≤ hi * ‖x‖ := fun x => by rw [hfit.μ_eq]; exact (hb' x).2
  have hNE' : NE ≤ N := le_trans (le_max_left _ _) hN
  have hNg' : Ng ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNsl' : Nsl ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNev' : Nev ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  obtain ⟨⟨hN1, hE2, hE3, hE4, hE5, hE6⟩, hE7⟩ := hNev N hNev'
  rw [← hfit.δ_eq] at hE4 hE5 hE6
  have hpath : pathBound m Ms ‖M.t₀‖ ≤ pathBound m Ms T := by
    have h1 : ((Ms : ℝ) + 1) * (‖M.t₀‖ + 1) ≤ ((Ms : ℝ) + 1) * (T + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [hTM]) (by positivity)
    unfold pathBound
    exact mul_le_mul_of_nonneg_left (by linarith only [h1]) (by positivity)
  have hE5' : Csl * Ms + 400 * (θ₀ * (pathBound m Ms ‖M.t₀‖ + 1)) ≤
      κ ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3 - M.δ / 500) := by
    have := mul_le_mul_of_nonneg_left hpath hθ₀.le
    linarith only [this, hE5]
  have hE6' : 2400 * Csl * Real.sqrt ((m + 2) * (1 + ‖M.t₀‖) / C₁) ≤
      (N : ℝ) ^ (9 * M.δ / 10000) := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hTM])
        (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])) hC₁.le))
      (mul_nonneg (by norm_num) hCsl.le)) hE6
  have hE7' : (7 + 4 * ‖M.t₀‖) * Ms ≤ (N : ℝ) ^ ((3 : ℝ) / 8) :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith only [hTM]) (Nat.cast_nonneg Ms)) hE7
  -- the good events and Lemma `lem:slabs` (2)
  obtain ⟨G, -, hGind₀, hGprop⟩ := hGoodK M hM hfit N hNg'
  have hN4 : (2 : ℝ) ≤ Real.sqrt N := by
    have : (0 : ℝ) ≤ 2 * Ms / κ := div_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg Ms)) hκ.le
    have h256 : (0 : ℝ) ≤ 256 * m := mul_nonneg (by norm_num) (Nat.cast_nonneg m)
    linarith only [hE2, this, h256]
  have hN1' : (1 : ℝ) < N := by
    have := (Real.le_sqrt' (by norm_num)).mp hN4
    linarith only [this]
  have hlogN : 0 < Real.log N := Real.log_pos hN1'
  have hGind : ∀ S : ℝ, Real.log N ≤ S →
      CurvatureVariance.IsOs M.P 2 (Csl / S) ((G S)ᶜ.indicator fun _ => (1 : ℝ)) := fun S hS => by
    have hSpos : 0 < S := lt_of_lt_of_le hlogN hS
    exact (hGind₀ S hS).mono_scale (by norm_num) (div_pos hCg hSpos)
      (div_le_div_of_nonneg_right (le_max_left _ _) hSpos.le)
  have hGiii : ∀ S : ℝ, Real.log N ≤ S → ∀ ω ∈ G S, ∀ (n ℓ' : ℕ) (t : EuclideanSpace ℝ (Fin m)),
      Real.sqrt N ≤ n → n ≤ ℓ' → (ℓ' : ℝ) ≤ 3 * N → ∀ u v : Vertex m,
      point v - point u = (ℓ' : ℝ) • slopeVec t → ‖t - M.t₀‖ ≤ 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) →
      InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) u → InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) v →
      ∀ K' : ℕ, ℓ' = K' * n →
      S ≤ (N : ℝ) ^ (M.δ / 1000) →
      slabMin M ω n K' t u v ≤ (passageTime ω u v : ℝ≥0∞) +
        ENNReal.ofReal (Csl * K' * S ^ 2) := by
    intro S hS ω hω n ℓ' t hn hnℓ hℓ3 u v hpt ht hu hv K' hK' hS'
    have hn1 : (1 : ℝ) ≤ n := le_trans (by linarith only [hN4]) hn
    have hn0 : 0 < n := by exact_mod_cast (by linarith only [hn1] : (0 : ℝ) < n)
    have hK1 : 1 ≤ K' := by
      rcases Nat.eq_zero_or_pos K' with h | h
      · rw [h, zero_mul] at hK'; omega
      · exact h
    have hℓ1' : 1 ≤ ℓ' := le_trans hn0 hnℓ
    have hslope : ‖t - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) := by
      have he : M.δ / 100 - 1 / 4 ≤ 0 := by linarith only [hM.delta_le_one]
      have hsq : 0 < Real.sqrt N := by linarith only [hN4]
      have h1 : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ Real.sqrt N ^ (M.δ / 100 - 1 / 4) :=
        Real.rpow_le_rpow_of_nonpos hsq hn he
      have h2 : Real.sqrt N ^ (M.δ / 100 - 1 / 4) = (N : ℝ) ^ ((M.δ / 100 - 1 / 4) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith only [hN1'])]; ring_nf
      have h3 : (N : ℝ) ^ ((M.δ / 100 - 1 / 4) / 2) ≤ (N : ℝ) ^ (-(1 : ℝ) / 9) :=
        Real.rpow_le_rpow_of_exponent_le hN1'.le (by linarith only [hM.delta_le_one])
      have h4 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 9) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      linarith only [ht, h1, h2, h3, h4]
    have hgood := hGprop S hS ω hω
    have := ((hNsl M hM hfit N hNsl' S hS ω hgood ℓ' t u v hpt hℓ1' hℓ3 hslope).2 K' n hK'
      hK1 hn ht hS' hu hv).2.2
    refine this.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg K')) (sq_nonneg S)
  have hconcl := parent_instance hM hK hA hκ hMs128 hcE hCE hCsl hC₁ hθ₀ hhi0.le hMsCE
    (fun s hs hMsN z hz => hNE M hM hfit N hNE' A hA hPrem hRange Ms s hMs128 hs hMsN z hz) hGind
    hGiii
    (fun x hx => by obtain ⟨-, -, h, -⟩ := hcl M hM hfit x hx; linarith only [h]) hdev hw hb
    hN1 hE2 hE3 hE4 hE5' hE6' hE7' hℓ1 hℓ2 hy
  have hℓ1' : (1 : ℝ) ≤ ℓ := by linarith only [hE3, hℓ1]
  have hQ1 := Proofs.ShortLengths.one_le_Q hM hK hA hℓ1'
  have hQ0 : 0 ≤ Q M K A ℓ := zero_le_one.trans hQ1
  have hQpos : 0 < Q M K A ℓ / 100 := div_pos (by linarith only [hQ1]) (by norm_num)
  have hconst : (Ms / 200 + hi * pathBound m Ms ‖M.t₀‖ + 1) * Q M K A ℓ ≤
      (Ms / 200 + hi * pathBound m Ms T + 1) * Q M K A ℓ :=
    mul_le_mul_of_nonneg_right (by linarith only [mul_le_mul_of_nonneg_left hpath hhi0.le]) hQ0
  refine hconcl.mono zero_le_one hQpos ?_ (Eventually.of_forall fun ω => ?_)
  · convert hconcl.1.add_const ((Ms / 200 + hi * pathBound m Ms ‖M.t₀‖ + 1) * Q M K A ℓ -
      (Ms / 200 + hi * pathBound m Ms T + 1) * Q M K A ℓ) using 1
    funext ω
    ring
  · dsimp only
    linarith only [hconst]

end CurvatureVariance.Paper.Moments
