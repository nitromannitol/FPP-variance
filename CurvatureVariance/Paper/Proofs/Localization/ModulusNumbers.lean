/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusSupport
public import CurvatureVariance.Paper.Proofs.Localization.ModulusNumeric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Lemma `lem:modulus`: the numbers

The numbers of the proof of Lemma `lem:modulus`:

* `Q_le_rpow_third`: `Q_{⌈gℓ⌉} ≤ g^{1/3} Q_ℓ` for `g ≤ 1/128`, from `⌈gℓ⌉ ≤ 2gℓ` and
  `2g ≤ g^{6/7}`;
* `log_pairs_le`: the `C(b) g^{−C}` pairs of cubes cost `C(b) log(2/g)` in the union bound;
* `exists_scale_le`: `g ∈ (0, 1/128)` with `C(b)(g + g^{1/3} log(2/g)) ≤ η`, for every `C(b)`.
-/

@[expose] public section

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-! ## The scale `Q` -/

/-- `2g ≤ g^{6/7}` for `0 < g ≤ 1/128`. -/
theorem two_mul_le_rpow {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1 / 128) :
    2 * g ≤ g ^ ((6 : ℝ) / 7) := by
  have h1 : g ^ ((1 : ℝ) / 7) ≤ 1 / 2 := by
    calc g ^ ((1 : ℝ) / 7) ≤ (((1 : ℝ) / 2) ^ (7 : ℕ)) ^ ((1 : ℝ) / 7) :=
          Real.rpow_le_rpow hg.le (hg1.trans_eq (by norm_num)) (by norm_num)
      _ = 1 / 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
  have h2 : g = g ^ ((1 : ℝ) / 7) * g ^ ((6 : ℝ) / 7) := by
    rw [← Real.rpow_add hg]; norm_num
  have h3 : 0 ≤ g ^ ((6 : ℝ) / 7) := Real.rpow_nonneg hg.le _
  calc 2 * g = 2 * (g ^ ((1 : ℝ) / 7) * g ^ ((6 : ℝ) / 7)) := by rw [← h2]
    _ ≤ 2 * (1 / 2 * g ^ ((6 : ℝ) / 7)) := by
        gcongr
    _ = g ^ ((6 : ℝ) / 7) := by ring

/-- **`Q_{⌈gℓ⌉} ≤ g^{1/3} Q_ℓ`** (the proof of Lemma `lem:modulus`, which has the exponent `2/5`),
for a length `0 < s ≤ 2gℓ` and `g ≤ 1/128`, where `⌈gℓ⌉ ≤ 2gℓ`. The exponent `1/2 − δ/K` is at least
`7/18`. -/
theorem Q_le_rpow_third (M : Model m) (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 0 ≤ A) {s ℓ g : ℝ} (hs : 0 < s) (hg : 0 < g) (hℓ : 0 < ℓ) (hg1 : g ≤ 1 / 128)
    (hsg : s ≤ 2 * g * ℓ) : Q M K A s ≤ g ^ ((1 : ℝ) / 3) * Q M K A ℓ := by
  have he := exponent_bounds M hM hK
  set e : ℝ := 1 / 2 - M.δ / K with hedef
  have hδ10 : M.δ / 10 ^ 4 ≤ 1 / 10 ^ 4 :=
    div_le_div_of_nonneg_right hM.delta_le_one (by norm_num)
  have he718 : (7 : ℝ) / 18 ≤ e := by
    rw [hedef]; linarith only [he.2.2, hδ10]
  have he0 : 0 ≤ e := by linarith only [he718]
  have h1 : s ^ e ≤ (2 * g) ^ e * ℓ ^ e := by
    rw [← Real.mul_rpow (by positivity) hℓ.le]
    exact Real.rpow_le_rpow hs.le hsg he0
  have h2 : (2 * g) ^ e ≤ g ^ ((1 : ℝ) / 3) := by
    calc (2 * g) ^ e ≤ (g ^ ((6 : ℝ) / 7)) ^ e :=
          Real.rpow_le_rpow (by positivity) (two_mul_le_rpow hg hg1) he0
      _ = g ^ ((6 : ℝ) / 7 * e) := (Real.rpow_mul hg.le _ _).symm
      _ ≤ g ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_exponent_ge hg (by linarith only [hg1]) (by linarith only [he718])
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hℓ.le e)
  unfold Q
  rw [← hedef]
  calc A * s ^ e ≤ A * (g ^ ((1 : ℝ) / 3) * ℓ ^ e) :=
        mul_le_mul_of_nonneg_left (h1.trans h3) hA
    _ = g ^ ((1 : ℝ) / 3) * (A * ℓ ^ e) := by ring

/-! ## The number of pairs of cubes -/

/-- The constant of `log_pairs_le`. -/
noncomputable def logConst (m : ℕ) (T b : ℝ) : ℝ :=
  (2 * m + 1) * (Real.log (11 * T * (b + 3)) / Real.log 2 + 2)

theorem logConst_nonneg (m : ℕ) {T b : ℝ} (hT : 1 ≤ T) (hb : 1 ≤ b) : 0 ≤ logConst m T b := by
  unfold logConst
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log (11 * T * (b + 3)) := Real.log_nonneg (by nlinarith only [hb, hT])
  positivity

/-- `2 gridSize + 3 ≤ 11 T (b + 3) / g²`. -/
theorem two_mul_gridSize_add_three_le {T b g : ℝ} (hT : 1 ≤ T) (hb : 1 ≤ b) (hg : 0 < g)
    (hg1 : g ≤ 1) : (2 * gridSize T b g + 3 : ℝ) ≤ 11 * T * (b + 3) * g⁻¹ ^ 2 := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hn' : (gridSize T b g : ℝ) ≤ T * (2 / g + b + 1) * (2 / g) + 2 := by
    unfold gridSize; push_cast
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ T * (2 / g + b + 1) * (2 / g))
    linarith only [this]
  have hginv : 1 ≤ g⁻¹ := one_le_inv_iff₀.mpr ⟨hg, hg1⟩
  have hA : 2 / g + b + 1 ≤ (b + 3) * g⁻¹ := by
    rw [div_eq_mul_inv]; nlinarith only [hginv, hb]
  have k1 : (2 / g + b + 1) * (2 / g) ≤ (b + 3) * g⁻¹ * (2 * g⁻¹) := by
    rw [show 2 / g = 2 * g⁻¹ by rw [div_eq_mul_inv]]
    exact mul_le_mul_of_nonneg_right (by rwa [← div_eq_mul_inv]) (by positivity)
  have k1' : T * (2 / g + b + 1) * (2 / g) ≤ T * ((b + 3) * g⁻¹ * (2 * g⁻¹)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left k1 hT0
  have k2 : (1 : ℝ) ≤ g⁻¹ ^ 2 := one_le_pow₀ hginv
  have k3 : (b + 3) * g⁻¹ ^ 2 ≤ T * ((b + 3) * g⁻¹ ^ 2) := by
    have : 0 ≤ (b + 3) * g⁻¹ ^ 2 := by positivity
    nlinarith only [this, hT]
  nlinarith only [hn', k1', k2, hb, k3]

/-- **The cost of the union bound**: the `2 ((2n + 1)^m)²` pairs of cubes, at most `C(b) g^{−C}` in
number (the proof of Lemma `lem:modulus`), cost `log(2 + #pairs) ≤ C(b) log(2/g)`. -/
theorem log_pairs_le (m : ℕ) {T b g : ℝ} (hT : 1 ≤ T) (hb : 1 ≤ b) (hg : 0 < g) (hg1 : g ≤ 1) :
    Real.log (2 + ((2 * ((2 * gridSize T b g + 1) ^ m) ^ 2 : ℕ) : ℝ)) ≤
      logConst m T b * Real.log (2 / g) := by
  set n := gridSize T b g with hn
  have hn1 : 1 ≤ n := by rw [hn]; unfold gridSize; omega
  -- `2 + 2 (2n+1)^{2m} ≤ (2n+3)^{2m+1}`
  have hnat : 2 + 2 * ((2 * n + 1) ^ m) ^ 2 ≤ (2 * n + 3) ^ (2 * m + 1) := by
    set X := ((2 * n + 1) ^ m) ^ 2 with hX
    have h1 : 1 ≤ X := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by omega))
    have h2 : X ≤ (2 * n + 3) ^ (2 * m) := by
      rw [hX, ← pow_mul, mul_comm m 2]; exact Nat.pow_le_pow_left (by omega) _
    have h3 : (2 * n + 3) ^ (2 * m + 1) = (2 * n + 3) ^ (2 * m) * (2 * n + 3) := pow_succ _ _
    have h4 : X * 5 ≤ (2 * n + 3) ^ (2 * m) * (2 * n + 3) :=
      (Nat.mul_le_mul_left X (by omega : 5 ≤ 2 * n + 3)).trans (Nat.mul_le_mul_right _ h2)
    rw [h3]
    omega
  have hlog1 : Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ)) ≤
      (2 * m + 1) * Real.log (2 * n + 3) := by
    have : (2 : ℝ) + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ) ≤
        ((2 * n + 3 : ℕ) : ℝ) ^ (2 * m + 1) := by
      exact_mod_cast hnat
    calc Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ))
        ≤ Real.log (((2 * n + 3 : ℕ) : ℝ) ^ (2 * m + 1)) :=
          Real.log_le_log (by positivity) this
      _ = (2 * m + 1) * Real.log (2 * n + 3) := by
          rw [Real.log_pow]; push_cast; ring
  have h23 := two_mul_gridSize_add_three_le hT hb hg hg1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ Real.log (11 * T * (b + 3)) := Real.log_nonneg (by nlinarith only [hb, hT])
  have hg2 : Real.log 2 ≤ Real.log (2 / g) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hg]; nlinarith only [hg, hg1])
  have hginv : Real.log g⁻¹ ≤ Real.log (2 / g) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_eq_mul_inv]
    have := inv_pos.mpr hg
    linarith only [this]
  have hlog2 : Real.log (2 * n + 3) ≤
      (Real.log (11 * T * (b + 3)) / Real.log 2 + 2) * Real.log (2 / g) := by
    have e1 : Real.log (11 * T * (b + 3)) ≤
        Real.log (11 * T * (b + 3)) / Real.log 2 * Real.log (2 / g) := by
      calc Real.log (11 * T * (b + 3))
          = Real.log (11 * T * (b + 3)) / Real.log 2 * Real.log 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hg2 (by positivity)
    calc Real.log (2 * n + 3) ≤ Real.log (11 * T * (b + 3) * g⁻¹ ^ 2) :=
          Real.log_le_log (by positivity) h23
      _ = Real.log (11 * T * (b + 3)) + 2 * Real.log g⁻¹ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by rw [add_mul]; linarith only [e1, hginv]
  have hm : (0 : ℝ) ≤ 2 * m + 1 := by positivity
  calc Real.log (2 + ((2 * ((2 * n + 1) ^ m) ^ 2 : ℕ) : ℝ))
      ≤ (2 * m + 1) * ((Real.log (11 * T * (b + 3)) / Real.log 2 + 2) * Real.log (2 / g)) :=
        hlog1.trans (mul_le_mul_of_nonneg_left hlog2 hm)
    _ = logConst m T b * Real.log (2 / g) := by unfold logConst; ring

/-! ## The length `s = ⌈gℓ⌉` and the margin -/

/-- `s = ⌈gℓ⌉` for `gℓ ≥ 1`: `gℓ ≤ s ≤ 2gℓ`. -/
theorem ceil_facts {x : ℝ} (hx : 1 ≤ x) : 0 < ⌈x⌉₊ ∧ x ≤ ⌈x⌉₊ ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have h1 : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  have h2 := Nat.ceil_lt_add_one (by linarith only [hx] : 0 ≤ x)
  have h3 : (0 : ℝ) < ⌈x⌉₊ := by linarith only [hx, h1]
  exact ⟨by exact_mod_cast h3, h1, by linarith only [h2, hx]⟩

/-- `c (x / (c + 1)) ≤ x` for `c, x ≥ 0`. -/
theorem mul_div_add_one_le {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) : c * (x / (c + 1)) ≤ x := by
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith only [hc, hx]

/-! ## The choice of `g` -/

/-- **The closing line of the proof**: for every constant `K₀ = C(b)` there is `g ∈ (0, 1/128)` with
`K₀ (g + g^{1/3} log(2/g)) ≤ η`. -/
theorem exists_scale_le {K₀ η : ℝ} (hK₀ : 0 < K₀) (hη : 0 < η) :
    ∃ g : ℝ, 0 < g ∧ g < 1 / 128 ∧
      K₀ * (g + g ^ ((1 : ℝ) / 3) * Real.log (2 / g)) ≤ η := by
  set g : ℝ := min (1 / 256) ((η / (13 * K₀)) ^ 6) with hgdef
  have hg : 0 < g := lt_min (by norm_num) (by positivity)
  have hg1 : g ≤ 1 / 256 := min_le_left _ _
  have hg6 : g ^ ((1 : ℝ) / 6) ≤ η / (13 * K₀) := by
    have h1 : g ≤ (η / (13 * K₀)) ^ 6 := min_le_right _ _
    calc g ^ ((1 : ℝ) / 6) ≤ ((η / (13 * K₀)) ^ (6 : ℕ)) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow hg.le h1 (by norm_num)
      _ = η / (13 * K₀) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
  have hgle : g ≤ g ^ ((1 : ℝ) / 6) := by
    calc g = g ^ (1 : ℝ) := (Real.rpow_one g).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hg (by linarith only [hg1]) (by norm_num)
  -- `log(2/g) ≤ 6 (2/g)^{1/6} ≤ 12 g^{−1/6}`
  have hlog : Real.log (2 / g) ≤ 12 * g⁻¹ ^ ((1 : ℝ) / 6) := by
    have h1 := log_inv_le (g := g / 2) (by positivity)
    have e : (g / 2)⁻¹ = 2 / g := by field_simp
    rw [e] at h1
    have h2 : (2 / g) ^ ((1 : ℝ) / 6) ≤ 2 * g⁻¹ ^ ((1 : ℝ) / 6) := by
      rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (2 : ℝ) ^ ((1 : ℝ) / 6) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    linarith only [h1, h2]
  have hpow1 : g ^ ((1 : ℝ) / 3) * g⁻¹ ^ ((1 : ℝ) / 6) = g ^ ((1 : ℝ) / 6) := by
    rw [Real.inv_rpow hg.le, ← Real.rpow_neg hg.le, ← Real.rpow_add hg]; norm_num
  have hg3 : 0 ≤ g ^ ((1 : ℝ) / 3) := by positivity
  have hL : g ^ ((1 : ℝ) / 3) * Real.log (2 / g) ≤ 12 * g ^ ((1 : ℝ) / 6) := by
    calc g ^ ((1 : ℝ) / 3) * Real.log (2 / g)
        ≤ g ^ ((1 : ℝ) / 3) * (12 * g⁻¹ ^ ((1 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left hlog hg3
      _ = 12 * (g ^ ((1 : ℝ) / 3) * g⁻¹ ^ ((1 : ℝ) / 6)) := by ring
      _ = 12 * g ^ ((1 : ℝ) / 6) := by rw [hpow1]
  refine ⟨g, hg, by linarith only [hg1], ?_⟩
  calc K₀ * (g + g ^ ((1 : ℝ) / 3) * Real.log (2 / g)) ≤ K₀ * (13 * (η / (13 * K₀))) :=
        mul_le_mul_of_nonneg_left (by linarith only [hgle, hL, hg6]) hK₀.le
    _ = η := by field_simp

/-- The sum of the three pieces of the proof is at most `(a + b + c)(g + L) Q`, for `L` the term
`g^{1/3} log(2/g)`. -/
theorem sum_le_rate {g L Q a b c x y z : ℝ} (hg : 0 ≤ g) (hL : 0 ≤ L) (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : x ≤ a * L * Q) (hy : y ≤ b * g * Q) (hz : z ≤ c * g * Q) :
    x + y + z ≤ (a + b + c) * (g + L) * Q := by
  have h1 : 0 ≤ a * g * Q := mul_nonneg (mul_nonneg ha hg) hQ
  have h2 : 0 ≤ b * L * Q := mul_nonneg (mul_nonneg hb hL) hQ
  have h3 : 0 ≤ c * L * Q := mul_nonneg (mul_nonneg hc hL) hQ
  have e : (a + b + c) * (g + L) * Q =
      a * L * Q + b * g * Q + c * g * Q + a * g * Q + b * L * Q + c * L * Q := by ring
  rw [e]
  linarith only [hx, hy, hz, h1, h2, h3]

end CurvatureVariance.Paper.Localization.Modulus
