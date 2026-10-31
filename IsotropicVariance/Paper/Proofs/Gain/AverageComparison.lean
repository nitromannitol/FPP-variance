/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Cited
public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Paper.Proofs.Gain.GainVariance
import IsotropicVariance.Infra.Measurability.SlabTime
import IsotropicVariance.Paper.Defs.SetTime
import IsotropicVariance.Paper.Proofs.Labels.Extract
import IsotropicVariance.Paper.Proofs.Profiles.Basic

/-!
# The comparison of `F̄` with `T_{Kn}`

The last paragraph of the proof of Proposition `prop:gain`. Let `S = [0, Kn] × ℝ^{d−1}`.

* `slabTime_le_F`: `ρ^{(i)} ≥ ρ_S` on the `i`th slab, so concatenating curves gives
  `T_S(τ, τ + Kn e₁) ≤ F_τ`.
* `W_div_eq`, `translate_le`: `(nQ_n/(KnQ_{Kn}))^{1/2} = K^{−3/4 + 1/(2K)}`, and the vectors `τ` of
  the translates satisfy `|τ| ≤ 2 K^{−1/24 + 1/(2K)} (KnQ_{Kn})^{1/2}` when `L ≤ K^{1/24}`.
* `abs_F_sub_TRV_le`: `|F_τ − T_{Kn}|` is at most `F_τ − T(τ, τ + Kn e₁)`, plus `F_0 − T_{Kn}`, plus
  the modulus quantity of equation `eq:modulus` for `T_S` at the length `Kn`.
* `lintegral_sq_averagedMin_sub_le`: with Jensen's inequality over the translates, the second
  moment of `F̄ − T_{Kn}`.

The first group of lemmas is general.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper IsotropicVariance.Paper.Contracts

/-! ### General facts -/

/-- An `L^p` bound, `p ≥ 2`, on a probability space gives the second moment:
`‖f‖_p ≤ c` implies `E f² ≤ c²`. -/
theorem lintegral_ofReal_sq_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {p : ℝ≥0∞} (hp : 2 ≤ p) {c : ℝ} (hc : 0 ≤ c)
    (h : eLpNorm f p P ≤ ENNReal.ofReal c) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ENNReal.ofReal (c ^ 2) := by
  have h2 : eLpNorm f 2 P ≤ ENNReal.ofReal c := (eLpNorm_le_eLpNorm_of_exponent_le hp).trans h
  have hf : AEStronglyMeasurable f P :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2)
  have key := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (μ := P) two_ne_zero hf
  have e : ∀ ω, ENNReal.ofReal (f ω ^ 2) = ‖f ω‖ₑ ^ ((2 : ℝ≥0) : ℝ) := by
    intro ω
    rw [Real.enorm_eq_ofReal_abs, NNReal.coe_ofNat, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
      (by norm_num), Real.rpow_two, sq_abs]
  simp_rw [e, ← key]
  rw [ENNReal.ofReal_pow hc, NNReal.coe_ofNat, ENNReal.rpow_two]
  exact pow_le_pow_left₀ bot_le (by simpa using h2) 2

/-- `c log⁴(2 + x) ≤ x^{4/5}` for all large `x`. -/
theorem exists_log_bound (c : ℝ) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * Real.log (2 + x) ^ 4 ≤ x ^ (4 / 5 : ℝ) := by
  set c' := max c 0 with hc'
  have hc'0 : 0 ≤ c' := le_max_right _ _
  refine ⟨max 1 ((30000 * c') ^ (5 / 2 : ℝ)), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_of_max_le_left hx
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 + x) ≤ 10 * (3 * x) ^ (1 / 10 : ℝ) := by
    have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 2 + x)
      (by norm_num : (0 : ℝ) < 1 / 10)
    have h' : (2 + x) ^ (1 / 10 : ℝ) ≤ (3 * x) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    calc Real.log (2 + x) ≤ (2 + x) ^ (1 / 10 : ℝ) / (1 / 10) := h
      _ = 10 * (2 + x) ^ (1 / 10 : ℝ) := by ring
      _ ≤ 10 * (3 * x) ^ (1 / 10 : ℝ) := by gcongr
  have h4 : Real.log (2 + x) ^ 4 ≤ 30000 * x ^ (2 / 5 : ℝ) := by
    have e1 : ((3 * x) ^ (1 / 10 : ℝ)) ^ 4 = (3 * x) ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have e2 : (3 * x) ^ (2 / 5 : ℝ) = 3 ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) :=
      Real.mul_rpow (by norm_num) hx0.le
    have e3 : (3 : ℝ) ^ (2 / 5 : ℝ) ≤ 3 := by
      calc (3 : ℝ) ^ (2 / 5 : ℝ) ≤ 3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    calc Real.log (2 + x) ^ 4 ≤ (10 * (3 * x) ^ (1 / 10 : ℝ)) ^ 4 :=
          pow_le_pow_left₀ hlog0 hlog 4
      _ = 10000 * (3 ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ)) := by
          rw [mul_pow, e1, e2]
          norm_num
      _ ≤ 10000 * (3 * x ^ (2 / 5 : ℝ)) := by gcongr
      _ = 30000 * x ^ (2 / 5 : ℝ) := by ring
  have hc : 30000 * c' ≤ x ^ (2 / 5 : ℝ) := by
    have hc0 : 0 ≤ 30000 * c' := by positivity
    have := Real.rpow_le_rpow (by positivity) (le_of_max_le_right hx)
      (by norm_num : (0 : ℝ) ≤ 2 / 5)
    rwa [← Real.rpow_mul hc0, show (5 / 2 : ℝ) * (2 / 5) = 1 by norm_num, Real.rpow_one] at this
  have hsplit : x ^ (4 / 5 : ℝ) = x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  calc c * Real.log (2 + x) ^ 4 ≤ c' * Real.log (2 + x) ^ 4 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ c' * (30000 * x ^ (2 / 5 : ℝ)) := mul_le_mul_of_nonneg_left h4 hc'0
    _ = (30000 * c') * x ^ (2 / 5 : ℝ) := by ring
    _ ≤ x ^ (2 / 5 : ℝ) * x ^ (2 / 5 : ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = x ^ (4 / 5 : ℝ) := hsplit.symm

/-! ### The scales -/

/-- `⌈K^{2/3}⌉ ≤ 2 K^{2/3}` for `K ≥ 1`. -/
theorem colCount_le {K : ℕ} (hK : 1 ≤ K) :
    (colCount K : ℝ) ≤ 2 * (K : ℝ) ^ ((2 : ℝ) / 3) := by
  unfold colCount
  have h1 : (1 : ℝ) ≤ (K : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.one_le_rpow (by exact_mod_cast hK) (by norm_num)
  have h2 := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg K) ((2 : ℝ) / 3))
  linarith

/-- `⌈K^{2/3}⌉ > 0` for `K ≥ 1`. -/
theorem colCount_pos {K : ℕ} (hK : 1 ≤ K) : (0 : ℝ) < colCount K := by
  unfold colCount
  exact_mod_cast Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by exact_mod_cast hK) _)

/-! ### Geometry -/

section Geometry

variable {m : ℕ}

/-- `|e₂| ≤ 1`. -/
theorem norm_e₂_le : ‖e₂ m‖ ≤ 1 := by
  rw [WithLp.prod_norm_eq_of_L2]
  have h1 : (e₂ m).fst = 0 := rfl
  have h2 : ‖(e₂ m).snd‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
    have e : ∀ k : Fin m, ‖(e₂ m).snd k‖ ^ 2 = if (k : ℕ) = 0 then 1 else 0 := by
      intro k
      change ‖Pt.tr (e₂ m) k‖ ^ 2 = _
      rw [tr_e₂]
      split_ifs <;> simp
    simp_rw [e]
    rw [Finset.sum_boole]
    have : (Finset.univ.filter fun k : Fin m => (k : ℕ) = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (ha.trans hb.symm)
    exact_mod_cast this
  rw [h1, norm_zero, Real.sqrt_le_one]
  nlinarith [norm_nonneg (e₂ m).snd]

/-- `|c e₂| ≤ c` for `c ≥ 0`. -/
theorem norm_smul_e₂_le {c : ℝ} (hc : 0 ≤ c) : ‖c • e₂ m‖ ≤ c := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  exact mul_le_of_le_one_right hc norm_e₂_le

/-- The transverse coordinates of `c e₂` are at most `c` in absolute value. -/
theorem abs_tr_smul_e₂_le {c : ℝ} (hc : 0 ≤ c) (k : Fin m) : |Pt.tr (c • e₂ m) k| ≤ c := by
  rw [Pt.tr_smul_apply, tr_e₂]
  split_ifs <;> simp [abs_of_nonneg hc, hc]

/-- The pair of transverse cubes of side `2r` centered at `0` and `ℓ e₁`. -/
noncomputable def centeredPair (ℓ r : ℝ) : CubePair m :=
  ⟨AffineIsometryEquiv.refl ℝ (Pt m), ℓ, 2 * r, 2 * r, 0⟩

/-- The points of `{t = 0}` with transverse coordinates at most `r` lie in the first cube. -/
theorem mem_centeredPair_first {ℓ r : ℝ} {x : Pt m} (h0 : Pt.lon x = 0)
    (h1 : ∀ k, |Pt.tr x k| ≤ r) : x ∈ (centeredPair ℓ r).first :=
  ⟨x, ⟨h0, fun k => by simpa [centeredPair] using h1 k⟩, rfl⟩

/-- The points of `{t = ℓ}` with transverse coordinates at most `r` lie in the second cube. -/
theorem mem_centeredPair_second {ℓ r : ℝ} {x : Pt m} (h0 : Pt.lon x = ℓ)
    (h1 : ∀ k, |Pt.tr x k| ≤ r) : x ∈ (centeredPair ℓ r).second :=
  ⟨x, ⟨h0, fun k => by simpa [centeredPair] using h1 k⟩, rfl⟩

/-- The centered pair is admissible at the distance `ℓ` when `2r ≤ 4W`. -/
theorem centeredPair_isAdmissible {ℓ r W κ : ℝ} (hr : 0 ≤ r) (hrW : 2 * r ≤ 4 * W)
    (hκ : 0 ≤ κ) : (centeredPair (m := m) ℓ r).IsAdmissible ℓ W κ := by
  refine ⟨rfl, by simp [centeredPair, hr], hrW, by simp [centeredPair, hr], hrW, ?_⟩
  simp [CubePair.centerSlope, centeredPair, hκ]

end Geometry

/-! ### The scales of the translates -/

/-- `(nQ_n)^{1/2} = K^{−3/4 + 1/(2K)} (KnQ_{Kn})^{1/2}`, for `ℓ = Kn` (proof of Proposition
`prop:gain`). -/
theorem W_div_eq {K : ℕ} (hK : 1 ≤ K) (A : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    W K A (ℓ / K) = (K : ℝ) ^ (-(3 / 4 : ℝ) + 1 / (2 * K)) * W K A ℓ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  set a : ℝ := 1 / 2 - 1 / (K : ℝ) with ha
  have hsq : (K : ℝ) ^ (-(3 / 4 : ℝ) + 1 / (2 * K)) =
      Real.sqrt ((K : ℝ) ^ (-(1 + a))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hK0.le]
    congr 1
    rw [ha]
    ring
  unfold W Q
  rw [← ha, hsq, ← Real.sqrt_mul (Real.rpow_nonneg hK0.le _), Real.div_rpow hℓ hK0.le]
  congr 1
  rw [Real.rpow_neg hK0.le, Real.rpow_add hK0, Real.rpow_one]
  have hKa0 : (K : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hK0 a).ne'
  field_simp

/-- **The vectors of the translates** (proof of Proposition `prop:gain`): for `L ≤ K^{1/24}` and
`j < ⌈K^{2/3}⌉`, `j L (nQ_n)^{1/2} ≤ 2 K^{−1/24 + 1/(2K)} (KnQ_{Kn})^{1/2}`. -/
theorem translate_le {K : ℕ} (hK : 1 ≤ K) (A : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {L : ℕ}
    (hL : (L : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 24)) {j : ℕ} (hj : j < colCount K) :
    (j : ℝ) * L * W K A (ℓ / K) ≤ 2 * (K : ℝ) ^ (-(1 / 24 : ℝ) + 1 / (2 * K)) * W K A ℓ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hj' : (j : ℝ) ≤ 2 * (K : ℝ) ^ ((2 : ℝ) / 3) :=
    (by exact_mod_cast hj.le : (j : ℝ) ≤ colCount K).trans (colCount_le hK)
  have hWℓ : 0 ≤ W K A ℓ := Real.sqrt_nonneg _
  have hexp : (K : ℝ) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((1 : ℝ) / 24) *
      (K : ℝ) ^ (-(3 / 4 : ℝ) + 1 / (2 * K)) = (K : ℝ) ^ (-(1 / 24 : ℝ) + 1 / (2 * K)) := by
    rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
    congr 1
    ring
  rw [W_div_eq hK A hℓ]
  calc (j : ℝ) * L * ((K : ℝ) ^ (-(3 / 4 : ℝ) + 1 / (2 * K)) * W K A ℓ)
      ≤ (2 * (K : ℝ) ^ ((2 : ℝ) / 3)) * (K : ℝ) ^ ((1 : ℝ) / 24) *
          ((K : ℝ) ^ (-(3 / 4 : ℝ) + 1 / (2 * K)) * W K A ℓ) := by
        gcongr
    _ = 2 * ((K : ℝ) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((1 : ℝ) / 24) *
          (K : ℝ) ^ (-(3 / 4 : ℝ) + 1 / (2 * K))) * W K A ℓ := by ring
    _ = _ := by rw [hexp]

/-- `K^{−1/24 + 1/(2K)} ≤ K^{−1/48}` for `K ≥ 24`. -/
theorem rpow_translation_le {K : ℕ} (hK : 24 ≤ K) :
    (K : ℝ) ^ (-(1 / 24 : ℝ) + 1 / (2 * K)) ≤ (K : ℝ) ^ (-(1 / 48 : ℝ)) := by
  have hK24 : (24 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : 1 / (2 * (K : ℝ)) ≤ 1 / 48 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith only [hK24]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hK24]) (by linarith only [h1])

/-! ### The slab `S = [0, Kn] × ℝ^{d−1}` -/

section Comparison

variable {m : ℕ} {X : Setting.{u} m}

/-- The slab of the pair `centeredPair ℓ r` is `[0, ℓ] × ℝ^{d−1}`. -/
theorem mem_slab_centeredPair {ℓ r : ℝ} {x : Pt m} :
    x ∈ (centeredPair ℓ r).slab.set ↔ 0 ≤ Pt.lon x ∧ Pt.lon x ≤ ℓ := by
  simp [Slab.set, CubePair.slab, centeredPair]

/-- The triangle inequality along a chain of points of a slab. -/
theorem slabTime_le_sum_chain {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) (ω : X.Ω) (M : ℕ) :
    ∀ x : Fin (M + 2) → Pt m, (∀ i, x i ∈ sl.set) →
      X.slabTime b sl ω (x 0) (x (Fin.last (M + 1))) ≤
        ∑ i : Fin (M + 1), X.slabTime b sl ω (x i.castSucc) (x i.succ) := by
  induction M with
  | zero =>
    intro x _
    rw [Fin.sum_univ_one]
    exact le_rfl
  | succ M ih =>
    intro x hx
    rw [Fin.sum_univ_castSucc]
    have h := Infra.Slab.slabTime_triangle X hb sl ω (hx 0) (hx (Fin.last (M + 1)).castSucc)
      (hx (Fin.last (M + 2)))
    exact h.trans (add_le_add (ih (fun i => x i.castSucc) fun i => hx _) le_rfl)

/-- **`T_S(τ, τ + Kn e₁) ≤ F_τ`** (proof of Proposition `prop:gain`): `ρ^{(i)} ≥ ρ_S` on the `i`th
slab, so concatenating curves gives the bound, for `S = [0, Kn] × ℝ^{d−1}` and `τ` transverse. -/
theorem slabTime_le_F {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ} (hM : 1 ≤ M) {s : ℝ} (hs : 0 < s)
    {τ : Pt m} (hτ : Pt.lon τ = 0) (r : ℝ) (ω : X.Ω) :
    X.slabTime b (centeredPair ((M : ℝ) * s) r).slab ω τ (τ + ((M : ℝ) * s) • e₁) ≤
      X.F b M s τ ω := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  set S := (centeredPair (m := m) (((M' + 1 : ℕ) : ℝ) * s) r).slab with hS
  have hw : 0 < S.width := by
    change 0 < ((M' + 1 : ℕ) : ℝ) * s
    positivity
  have hne : Nonempty {x : Fin (M' + 1 + 1) → Pt m // IsAdmissible (M' + 1) s τ x} :=
    ⟨⟨_, isAdmissible_straight _ _ hs.le τ⟩⟩
  refine le_ciInf fun x => ?_
  obtain ⟨hx0, hxl, hlon, -⟩ := x.2
  have hmem : ∀ i, x.1 i ∈ S.set := fun i => by
    rw [hS, mem_slab_centeredPair]
    have h := hlon i
    rw [Pt.lon_sub, hτ, sub_zero] at h
    rw [h]
    have hi : (i : ℝ) ≤ ((M' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 i.2
    exact ⟨by positivity, by gcongr⟩
  have h := slabTime_le_sum_chain hb S ω M' x.1 hmem
  rw [hx0, hxl] at h
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨h1, h2⟩ := mem_chainSlab_set_of_isAdmissible x.2 i
  have hsub : (chainSlab s τ i).set ⊆ S.set := by
    intro y hy
    rw [hS, mem_slab_centeredPair]
    rw [mem_chainSlab_set, hτ, zero_add] at hy
    have hi : ((i : ℕ) : ℝ) + 1 ≤ ((M' + 1 : ℕ) : ℝ) := by exact_mod_cast i.isLt
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 := mul_le_mul_of_nonneg_right hi hs.le
    have h4 := mul_nonneg hi0 hs.le
    exact ⟨by linarith only [hy.1, h4], by linarith only [hy.2, h3]⟩
  have hle := X.setTime_le_setTime hb (Infra.Slab.isClosed_slab_set _)
    (Infra.Slab.convex_slab_set _) hsub ω h1 h2
  rwa [X.setTime_slab S hw, X.setTime_slab _ (show 0 < (chainSlab s τ i).width from hs)] at hle

/-- **The pointwise comparison** (proof of Proposition `prop:gain`): for the translation
`τ = c e₂`, `|c| ≤ r`, `|F_τ − T_{Kn}|` is at most `F_τ − T(τ, τ + Kn e₁)` plus `F_0 − T_{Kn}`
plus the modulus quantity of equation `eq:modulus` for `T_S`, since `T(τ, ·) ≤ T_S(τ, ·) ≤ F_τ`,
the same at `0`, and the translation preserves the distance of the endpoints. -/
theorem abs_F_sub_TRV_le {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ} (hM : 1 ≤ M) {s ℓ r ρ c : ℝ}
    (hs : 0 < s) (hℓ : (M : ℝ) * s = ℓ) (hc : 0 ≤ c) (hcr : c ≤ r) (hrρ : r ≤ ρ) (ω : X.Ω) :
    |X.F b M s (c • e₂ m) ω - X.TRV ℓ ω| ≤
      (X.F b M s (c • e₂ m) ω - X.passTime ω (c • e₂ m) (c • e₂ m + ℓ • e₁)) +
        (X.F b M s 0 ω - X.passTime ω 0 (0 + ℓ • e₁)) +
        modulusSup (X.slabTime b (centeredPair ℓ r).slab ω) (centeredPair ℓ r).first
          (centeredPair ℓ r).second ρ := by
  subst hℓ
  set ℓ := (M : ℝ) * s with hℓdef
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hℓ0 : 0 < ℓ := mul_pos hM0 hs
  have hr0 : 0 ≤ r := hc.trans hcr
  set p := centeredPair (m := m) ℓ r with hp
  set τ := c • e₂ m with hτ
  have hτlon : Pt.lon τ = 0 := by rw [hτ, Pt.lon_smul, lon_e₂, mul_zero]
  have hτtr : ∀ k, |Pt.tr τ k| ≤ c := abs_tr_smul_e₂_le hc
  have hτ'lon : Pt.lon (τ + ℓ • e₁) = ℓ := by
    rw [Pt.lon_add, hτlon, Pt.lon_smul, Pt.lon_e₁, mul_one, zero_add]
  have hτ'tr : ∀ k, |Pt.tr (τ + ℓ • e₁) k| ≤ c := by
    intro k
    rw [Pt.tr_add_apply, Pt.tr_smul_apply ℓ, Pt.tr_e₁_apply, mul_zero, add_zero]
    exact hτtr k
  have hd₁ : dist τ 0 ≤ ρ := by
    rw [dist_zero_right]
    exact ((norm_smul_e₂_le hc).trans hcr).trans hrρ
  have hd₂ : dist (τ + ℓ • e₁) (ℓ • e₁) ≤ ρ := by
    have := dist_add_right τ 0 (ℓ • e₁)
    rw [zero_add] at this
    rw [this]
    exact hd₁
  have hdd : dist τ (τ + ℓ • e₁) = dist (0 : Pt m) (ℓ • e₁) := by
    have := dist_add_left τ 0 (ℓ • e₁)
    rwa [add_zero] at this
  have hmod := Labels.abs_slabTime_sub_sub_add_le_modulusSup X hb p hℓ0.le ω
    (mem_centeredPair_first hτlon fun k => (hτtr k).trans hcr)
    (mem_centeredPair_first Pt.lon_zero fun k => by rw [Pt.tr_zero_apply, abs_zero]; exact hr0)
    (mem_centeredPair_second hτ'lon fun k => (hτ'tr k).trans hcr)
    (mem_centeredPair_second (by rw [Pt.lon_smul, Pt.lon_e₁, mul_one]) fun k => by
      rw [Pt.tr_smul_apply, Pt.tr_e₁_apply, mul_zero, abs_zero]; exact hr0)
    hd₁ hd₂
  rw [hdd, sub_add_cancel] at hmod
  have hw : 0 < p.slab.width := hℓ0
  have hmemτ : τ ∈ p.slab.set := mem_slab_centeredPair.2 ⟨hτlon.ge, hτlon.le.trans hℓ0.le⟩
  have hmemτ' : τ + ℓ • e₁ ∈ p.slab.set :=
    mem_slab_centeredPair.2 (by rw [hτ'lon]; exact ⟨hℓ0.le, le_rfl⟩)
  have hmem0 : (0 : Pt m) ∈ p.slab.set :=
    mem_slab_centeredPair.2 ⟨Pt.lon_zero.ge, Pt.lon_zero.le.trans hℓ0.le⟩
  have hmem0' : ℓ • e₁ ∈ p.slab.set := by
    refine mem_slab_centeredPair.2 ?_
    rw [Pt.lon_smul, Pt.lon_e₁, mul_one]
    exact ⟨hℓ0.le, le_rfl⟩
  have hT : ∀ {u v : Pt m}, u ∈ p.slab.set → v ∈ p.slab.set →
      X.passTime ω u v ≤ X.slabTime b p.slab ω u v := fun hu hv => by
    have h := X.passTime_le_setTime hb (Infra.Slab.isClosed_slab_set _)
      (Infra.Slab.convex_slab_set _) ω hu hv
    rwa [X.setTime_slab _ hw] at h
  have hT1 := hT hmemτ hmemτ'
  have hT0 := hT hmem0 hmem0'
  have hF1 := slabTime_le_F hb hM hs hτlon r ω
  have hF0 := slabTime_le_F hb hM hs (Pt.lon_zero (m := m)) r ω
  rw [zero_add] at hF0 ⊢
  change |_ - X.passTime ω 0 (ℓ • e₁)| ≤ _
  rw [abs_le] at hmod ⊢
  constructor <;> linarith only [hmod.1, hmod.2, hT1, hT0, hF1, hF0]

/-- The second moment of a nonnegative `O_1(θ)` variable is at most `6 θ²`. -/
theorem lintegral_sq_le_of_isOs_one {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    {θ : ℝ} (hθ : 0 < θ) (hY0 : ∀ ω, 0 ≤ Y ω) (hY : Cited.IsOs P 1 θ Y) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P ≤ ENNReal.ofReal (6 * θ ^ 2) := by
  have hmom := osMomentStatement_holds hY one_pos hθ (by norm_num : (0 : ℝ) ≤ 2)
  have hceil : Nat.ceil ((2 : ℝ) / 1) = 2 := by norm_num
  rw [hceil] at hmom
  have e1 : ∀ ω, ENNReal.ofReal (max (Y ω) 0 ^ (2 : ℝ)) = ENNReal.ofReal (Y ω ^ 2) := by
    intro ω
    rw [max_eq_left (hY0 ω), Real.rpow_two]
  simp_rw [e1] at hmom
  refine hmom.trans (le_of_eq ?_)
  rw [Real.rpow_two]
  norm_num [Nat.factorial]

/-- If `|Z| ≤ Y + Y₀ + D` with `Y, Y₀ ≥ 0` of size `O_1(θ)` and `‖D‖_p ≤ c`, `p ≥ 2`, then
`E Z² ≤ 36 θ² + 3 c²`. -/
theorem lintegral_sq_le_of_abs_le_add {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z Y Y₀ D : Ω → ℝ} (hZ : ∀ ω, |Z ω| ≤ Y ω + Y₀ ω + D ω) {θ : ℝ}
    (hθ : 0 < θ) (hY0 : ∀ ω, 0 ≤ Y ω) (hY₀0 : ∀ ω, 0 ≤ Y₀ ω) (hY : Cited.IsOs P 1 θ Y)
    (hY₀ : Cited.IsOs P 1 θ Y₀) {p : ℝ≥0∞} (hp : 2 ≤ p) {c : ℝ} (hc : 0 ≤ c)
    (hD : eLpNorm D p P ≤ ENNReal.ofReal c) :
    ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂P ≤ ENNReal.ofReal (36 * θ ^ 2 + 3 * c ^ 2) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hpt : ∀ ω, ENNReal.ofReal (Z ω ^ 2) ≤ ENNReal.ofReal 3 * ENNReal.ofReal (Y ω ^ 2) +
      (ENNReal.ofReal 3 * ENNReal.ofReal (Y₀ ω ^ 2) +
        ENNReal.ofReal 3 * ENNReal.ofReal (D ω ^ 2)) := by
    intro ω
    rw [← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_mul h3,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hZ ω
    have hs0 : 0 ≤ Y ω + Y₀ ω + D ω := (abs_nonneg _).trans h
    calc Z ω ^ 2 = |Z ω| ^ 2 := (sq_abs _).symm
      _ ≤ (Y ω + Y₀ ω + D ω) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ ≤ 3 * Y ω ^ 2 + (3 * Y₀ ω ^ 2 + 3 * D ω ^ 2) := by
          nlinarith only [sq_nonneg (Y ω - Y₀ ω), sq_nonneg (Y ω - D ω), sq_nonneg (Y₀ ω - D ω)]
  have hA1 : AEMeasurable (fun ω => ENNReal.ofReal 3 * ENNReal.ofReal (Y ω ^ 2)) P :=
    ((hY.1.pow_const 2).ennreal_ofReal).const_mul _
  have hA2 : AEMeasurable (fun ω => ENNReal.ofReal 3 * ENNReal.ofReal (Y₀ ω ^ 2)) P :=
    ((hY₀.1.pow_const 2).ennreal_ofReal).const_mul _
  have h1 := lintegral_sq_le_of_isOs_one hθ hY0 hY
  have h2 := lintegral_sq_le_of_isOs_one hθ hY₀0 hY₀
  have h4 := lintegral_ofReal_sq_le_of_eLpNorm_le hp hc hD
  calc ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal 3 * ENNReal.ofReal (Y ω ^ 2) +
          (ENNReal.ofReal 3 * ENNReal.ofReal (Y₀ ω ^ 2) +
            ENNReal.ofReal 3 * ENNReal.ofReal (D ω ^ 2))) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal 3 * ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P +
          (ENNReal.ofReal 3 * ∫⁻ ω, ENNReal.ofReal (Y₀ ω ^ 2) ∂P +
            ENNReal.ofReal 3 * ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂P) := by
        rw [lintegral_add_left' hA1, lintegral_add_left' hA2,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal (6 * θ ^ 2) +
          (ENNReal.ofReal 3 * ENNReal.ofReal (6 * θ ^ 2) +
            ENNReal.ofReal 3 * ENNReal.ofReal (c ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (36 * θ ^ 2 + 3 * c ^ 2) := by
        rw [← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_mul h3,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The comparison of `F̄` with `T_{Kn}`** (proof of Proposition `prop:gain`): if the
translations `j L W_n`, `j < ⌈K^{2/3}⌉`, are at most `r ≤ ρ`, the bound of Lemma `lem:slab` on
`F_τ − T(τ, τ + Kn e₁)` is `O_1(θ)`, and the modulus quantity of equation `eq:modulus` for `T_S`
at the mesh `ρ` has `L^{8d}` norm at most `c`, then Jensen's inequality over the translates gives
`E (F̄ − T_{Kn})² ≤ 36 θ² + 3 c²`. -/
theorem lintegral_sq_averagedMin_sub_le {b : ℝ} (hb : X.IsUpperBound b) {K L : ℕ} (hK : 1 ≤ K)
    {n Wn ℓ r ρ θ c : ℝ} (hn : 0 < n) (hℓ : (K : ℝ) * n = ℓ) (hrρ : r ≤ ρ) (hθ : 0 < θ) (hc : 0 ≤ c)
    (htrans : ∀ j < colCount K, 0 ≤ (j : ℝ) * L * Wn ∧ (j : ℝ) * L * Wn ≤ r)
    (hY : ∀ τ : Pt m, (∀ ω, 0 ≤ X.F b K n τ ω - X.passTime ω τ (τ + ℓ • e₁)) ∧
      Cited.IsOs X.P 1 θ fun ω => X.F b K n τ ω - X.passTime ω τ (τ + ℓ • e₁))
    (hmod : eLpNorm (fun ω => modulusSup (X.slabTime b (centeredPair ℓ r).slab ω)
      (centeredPair ℓ r).first (centeredPair ℓ r).second ρ) (8 * (m + 1) : ℝ≥0∞) X.P ≤
        ENNReal.ofReal c) :
    ∫⁻ ω, ENNReal.ofReal ((averagedMin X b K n Wn L ω - X.TRV ℓ ω) ^ 2) ∂X.P ≤
      ENNReal.ofReal (36 * θ ^ 2 + 3 * c ^ 2) := by
  set M := colCount K with hMdef
  have hM0 : (0 : ℝ) < M := colCount_pos hK
  have hM : 1 ≤ M := by exact_mod_cast hM0
  have hM0' : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast hM0.ne'
  set Δ : ℕ → X.Ω → ℝ := fun j ω => X.F b K n (((j : ℝ) * L * Wn) • e₂ m) ω - X.TRV ℓ ω with hΔ
  have hτ : ∀ j : ℕ, Pt.lon (((j : ℝ) * L * Wn) • e₂ m) = 0 := fun j => by
    rw [Pt.lon_smul, lon_e₂, mul_zero]
  have hΔm : ∀ j, AEMeasurable (Δ j) X.P := fun j =>
    (aemeasurable_F X hb K hn.le (hτ j)).sub (Profiles.aemeasurable_passTime (X := X) 0 (ℓ • e₁))
  have e : ∀ ω, averagedMin X b K n Wn L ω - X.TRV ℓ ω =
      (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, Δ j ω := fun ω => by
    simp only [hΔ]
    rw [averagedMin, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hM0.ne', one_mul]
  simp_rw [e]
  refine (lintegral_sq_average_le hM Δ hΔm).trans ?_
  have hp2 : (2 : ℝ≥0∞) ≤ 8 * (m + 1) := by
    calc (2 : ℝ≥0∞) ≤ 8 * 1 := by norm_num
      _ ≤ 8 * ((m : ℝ≥0∞) + 1) := by gcongr; exact le_add_self
  have hj : ∀ j ∈ Finset.range M, ∫⁻ ω, ENNReal.ofReal (Δ j ω ^ 2) ∂X.P ≤
      ENNReal.ofReal (36 * θ ^ 2 + 3 * c ^ 2) := fun j hj => by
    obtain ⟨h0, hr⟩ := htrans j (Finset.mem_range.1 hj)
    exact lintegral_sq_le_of_abs_le_add
      (fun ω => abs_F_sub_TRV_le hb hK hn hℓ h0 hr hrρ ω) hθ (hY _).1 (hY 0).1 (hY _).2 (hY 0).2
      hp2 hc hmod
  calc (M : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range M, ∫⁻ ω, ENNReal.ofReal (Δ j ω ^ 2) ∂X.P
      ≤ (M : ℝ≥0∞)⁻¹ * ∑ _j ∈ Finset.range M, ENNReal.ofReal (36 * θ ^ 2 + 3 * c ^ 2) := by
        gcongr with j hj'
        exact hj j hj'
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel hM0' (ENNReal.natCast_ne_top M), one_mul]

end Comparison

end IsotropicVariance.Paper.Proofs.Gain
