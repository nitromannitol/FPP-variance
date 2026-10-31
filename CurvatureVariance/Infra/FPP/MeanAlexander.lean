/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MeanDefs
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Alexander's theorem: convex-hull approximation implies general approximation

A deterministic statement used for the mean rate of [ADH, Thm 3.33]. If a subadditive,
linearly bounded `h` on the lattice dominates a seminorm `μ` and satisfies the convex-hull
approximation property `ConvexHullApprox`, then `h x ≤ μ x + C' φ(|x|)` for all `|x| ≥ 1`
(`le_add_meanRate_of_convexHullApprox`). The proof is Alexander's iteration: one Carathéodory
step halves the norm at the cost `k C φ(|x|)`, and the geometric decay of `φ` sums the errors.

We also record elementary facts about `meanRate`.
-/

@[expose] public section

open Filter

namespace CurvatureVariance.Infra.FPP


variable {m : ℕ}

/-! ### Facts about `meanRate` -/

theorem meanRate_nonneg (r : ℝ) : 0 ≤ meanRate r := Real.sqrt_nonneg _

theorem meanRate_mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) : meanRate r ≤ meanRate s := by
  unfold meanRate
  apply Real.sqrt_le_sqrt
  have h2 : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  exact mul_le_mul hrs (Real.log_le_log (by linarith) (by linarith)) h2 (hr.trans hrs)

theorem meanRate_half_le {r : ℝ} (hr : 0 ≤ r) : meanRate (r / 2) ≤ 3 / 4 * meanRate r := by
  unfold meanRate
  have ha : 0 ≤ r * Real.log (2 + r) :=
    mul_nonneg hr (Real.log_nonneg (by linarith))
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt ha]
  have hl : Real.log (2 + r / 2) ≤ Real.log (2 + r) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl0 : 0 ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have h1 : r / 2 * Real.log (2 + r / 2) ≤ r / 2 * Real.log (2 + r) :=
    mul_le_mul_of_nonneg_left hl (by linarith)
  linarith only [h1, ha, mul_nonneg hr hl0]

theorem one_le_meanRate {r : ℝ} (hr : 1 ≤ r) : 1 ≤ meanRate r := by
  unfold meanRate
  have h3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hl : Real.log 3 ≤ Real.log (2 + r) := Real.log_le_log (by norm_num) (by linarith)
  rw [Real.one_le_sqrt]
  nlinarith

theorem eventually_meanRate_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, meanRate r ≤ ε * r := by
  have hδ : 0 < ε ^ 2 / 4 := by positivity
  have h1 := Real.isLittleO_log_id_atTop.bound hδ
  filter_upwards [h1, eventually_ge_atTop (max 2 (4 / ε ^ 2))] with r hr hr2
  have hr2' : 2 ≤ r := (le_max_left _ _).trans hr2
  have hr4 : 4 / ε ^ 2 ≤ r := (le_max_right _ _).trans hr2
  have hr0 : 0 < r := by linarith
  have hlog : Real.log r ≤ ε ^ 2 / 4 * r := by
    have := hr
    simp only [id, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans_eq (by rw [abs_of_pos hr0]))
  have h1' : 1 ≤ ε ^ 2 / 4 * r := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 2)).1 hr4
    linarith
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have h2r : Real.log (2 + r) ≤ Real.log (r * 2) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul hr0.ne' (by norm_num)] at h2r
  have hlog' : Real.log (2 + r) ≤ ε ^ 2 / 2 * r := by linarith
  unfold meanRate
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc r * Real.log (2 + r) ≤ r * (ε ^ 2 / 2 * r) := mul_le_mul_of_nonneg_left hlog' hr0.le
    _ ≤ (ε * r) ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg ε) (mul_pos hr0 hr0).le]

/-! ### Lattice points -/


section Subadditive

variable {h : Vertex m → ℝ}

theorem le_nsmul_of_subadditive (hsub : ∀ x y, h (x + y) ≤ h x + h y) (h0 : h 0 = 0)
    (n : ℕ) (y : Vertex m) : h (n • y) ≤ n * h y := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [succ_nsmul]
    have := hsub (n • y) y
    push_cast
    linarith only [this, ih]

theorem le_sum_of_subadditive (hsub : ∀ x y, h (x + y) ≤ h x + h y) (h0 : h 0 = 0)
    {ι : Type*} (s : Finset ι) (g : ι → Vertex m) :
    h (∑ i ∈ s, g i) ≤ ∑ i ∈ s, h (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    linarith only [hsub (g a) (∑ i ∈ s, g i), ih]

end Subadditive

theorem seminorm_sum_le {E : Type*} [AddCommGroup E] [Module ℝ E] (μ : Seminorm ℝ E)
    {ι : Type*} (s : Finset ι) (g : ι → E) : μ (∑ i ∈ s, g i) ≤ ∑ i ∈ s, μ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add μ _ _).trans (by linarith only [ih])

/-! ### One Alexander step: the decomposition -/

/-- The integer/fractional decomposition: writing `x/k = ∑ w_j y_j` with `w_j ≥ 0`, there is a
lattice point `z` with `point z = ∑ f_j y_j`, `f_j ∈ [0,1]`, and
`h x ≤ k ∑ w_j h(y_j) + (h z - μ z)`. -/
theorem exists_step_decomp {h : Vertex m → ℝ} {μ : Seminorm ℝ (Pt m)}
    (hsub : ∀ x y, h (x + y) ≤ h x + h y) (h0 : h 0 = 0) (hge : ∀ x, μ (point x) ≤ h x)
    {ι : Type*} [Fintype ι] (x : Vertex m) {k : ℕ} (hk : 0 < k) (w : ι → ℝ)
    (hw : ∀ j, 0 ≤ w j) (y : ι → Vertex m)
    (hξ : ∑ j, w j • point (y j) = (k : ℝ)⁻¹ • point x) :
    ∃ (z : Vertex m) (f : ι → ℝ), (∀ j, 0 ≤ f j ∧ f j ≤ 1) ∧
      point z = ∑ j, f j • point (y j) ∧
      h x ≤ k * ∑ j, w j * h (y j) + (h z - μ (point z)) := by
  classical
  set n : ι → ℕ := fun j => ⌊(k : ℝ) * w j⌋₊ with hn
  set f : ι → ℝ := fun j => (k : ℝ) * w j - n j with hf
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hf0 : ∀ j, 0 ≤ f j := fun j => by
    simp only [hf, hn, sub_nonneg]; exact Nat.floor_le (mul_nonneg hkpos.le (hw j))
  have hf1 : ∀ j, f j ≤ 1 := fun j => by
    have := Nat.lt_floor_add_one ((k : ℝ) * w j)
    simp only [hf, hn]; linarith only [this]
  refine ⟨x - ∑ j, n j • y j, f, fun j => ⟨hf0 j, hf1 j⟩, ?_, ?_⟩
  · have hx : point x = ∑ j, ((k : ℝ) * w j) • point (y j) := by
      have : point x = (k : ℝ) • ((k : ℝ)⁻¹ • point x) := by
        rw [smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
      rw [this, ← hξ, Finset.smul_sum]
      simp only [smul_smul]
    rw [point_sub, point_sum, hx]
    simp only [point_nsmul, hf, sub_smul, Finset.sum_sub_distrib]
  · set z := x - ∑ j, n j • y j with hz
    have hxz : x = ∑ j, n j • y j + z := by rw [hz]; abel
    have h1 : h x ≤ ∑ j, (n j : ℝ) * h (y j) + h z := by
      calc h x = h (∑ j, n j • y j + z) := by rw [← hxz]
        _ ≤ h (∑ j, n j • y j) + h z := hsub _ _
        _ ≤ ∑ j, h (n j • y j) + h z := by
            gcongr; exact le_sum_of_subadditive hsub h0 _ _
        _ ≤ ∑ j, (n j : ℝ) * h (y j) + h z := by
            gcongr with j; exact le_nsmul_of_subadditive hsub h0 _ _
    have hz' : point z = ∑ j, f j • point (y j) := by
      have hx : point x = ∑ j, ((k : ℝ) * w j) • point (y j) := by
        have : point x = (k : ℝ) • ((k : ℝ)⁻¹ • point x) := by
          rw [smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
        rw [this, ← hξ, Finset.smul_sum]
        simp only [smul_smul]
      rw [hz, point_sub, point_sum, hx]
      simp only [point_nsmul, hf, sub_smul, Finset.sum_sub_distrib]
    have h2 : μ (point z) ≤ ∑ j, f j * h (y j) := by
      rw [hz']
      refine (seminorm_sum_le μ _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (hf0 j)]
      exact mul_le_mul_of_nonneg_left (hge _) (hf0 j)
    have h3 : ∑ j, (n j : ℝ) * h (y j) + ∑ j, f j * h (y j) = k * ∑ j, w j * h (y j) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hf]; ring
    linarith only [h1, h2, h3]

/-! ### One Alexander step -/

theorem finrank_lift : Module.finrank ℝ (Pt m × ℝ) = m + 2 := by
  have h1 : Module.finrank ℝ (Pt m) = m + 1 := by
    have := (WithLp.linearEquiv 2 ℝ (ℝ × EuclideanSpace ℝ (Fin m))).finrank_eq
    rw [this, Module.finrank_prod]
    simp
    omega
  rw [Module.finrank_prod, h1]; simp

theorem exists_step {h : Vertex m → ℝ} {μ : Seminorm ℝ (Pt m)} {M C r₀ : ℝ}
    (hsub : ∀ x y, h (x + y) ≤ h x + h y) (h0 : h 0 = 0) (hge : ∀ x, μ (point x) ≤ h x)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hchap : ConvexHullApprox h μ M C r₀)
    {k : ℕ} (hk : 0 < k) (hkM : 2 * ((m : ℝ) + 3) * M ≤ k)
    (x : Vertex m) (hx : k * r₀ ≤ ‖point x‖) :
    ∃ z : Vertex m, ‖point z‖ ≤ ‖point x‖ / 2 ∧
      h x - μ (point x) ≤ (k * C) * meanRate ‖point x‖ + (h z - μ (point z)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set ξ : Pt m := (k : ℝ)⁻¹ • point x with hξdef
  have hnξ : ‖ξ‖ = ‖point x‖ / k := by
    rw [hξdef, norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  have hr₀ : r₀ ≤ ‖ξ‖ := by
    rw [hnξ, le_div_iff₀ hkpos]; linarith only [hx]
  obtain ⟨v, hv, hmem⟩ := hchap x k hk hr₀
  obtain ⟨ι, _, p, w, hrange, hai, hwpos, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hmem
  have hex : ∀ j, ∃ y : Vertex m, ‖point y‖ ≤ M * ‖ξ‖ ∧ p j = (point y, h y) := fun j => by
    obtain ⟨y, hy, hpy⟩ := hrange ⟨j, rfl⟩
    exact ⟨y, hy, hpy.symm⟩
  choose y hy hpy using hex
  have hcard : Fintype.card ι ≤ m + 3 := by
    have h1 := hai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range p)) ≤ m + 2 :=
      finrank_lift (m := m) ▸ Submodule.finrank_le _
    omega
  have hs1 : ∑ j, w j • point (y j) = ξ := by
    have := congrArg Prod.fst hsum
    simpa [hpy, Prod.fst_sum] using this
  have hs2 : ∑ j, w j * h (y j) = v := by
    have := congrArg Prod.snd hsum
    simpa [hpy, Prod.snd_sum] using this
  obtain ⟨z, f, hf, hz, hxz⟩ := exists_step_decomp hsub h0 hge x hk w (fun j => (hwpos j).le) y hs1
  have hMξ : 0 ≤ M * ‖ξ‖ := mul_nonneg hM (norm_nonneg _)
  have hzn : ‖point z‖ ≤ ‖point x‖ / 2 := by
    rw [hz]
    calc ‖∑ j, f j • point (y j)‖ ≤ ∑ j, ‖f j • point (y j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : ι, M * ‖ξ‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf j).1]
          calc f j * ‖point (y j)‖ ≤ 1 * (M * ‖ξ‖) :=
                mul_le_mul (hf j).2 (hy j) (norm_nonneg _) zero_le_one
            _ = M * ‖ξ‖ := one_mul _
      _ = Fintype.card ι * (M * ‖ξ‖) := by simp
      _ ≤ ((m : ℝ) + 3) * (M * ‖ξ‖) := by
          gcongr; exact_mod_cast hcard
      _ = (((m : ℝ) + 3) * M) * (‖point x‖ / k) := by rw [hnξ]; ring
      _ ≤ (k / 2) * (‖point x‖ / k) := by
          gcongr; linarith only [hkM]
      _ = ‖point x‖ / 2 := by field_simp
  refine ⟨z, hzn, ?_⟩
  have hμ : (k : ℝ) * μ ξ = μ (point x) := by
    have : point x = (k : ℝ) • ξ := by
      rw [hξdef, smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
    have h2 : μ ((k : ℝ) • ξ) = k * μ ξ := by rw [map_smul_eq_mul, Real.norm_natCast]
    rw [← h2, ← this]
  have hφ : meanRate ‖ξ‖ ≤ meanRate ‖point x‖ :=
    meanRate_mono (norm_nonneg _) (by
      rw [hnξ]; exact div_le_self (norm_nonneg _) (by exact_mod_cast hk))
  have hkv : (k : ℝ) * v ≤ k * (μ ξ + C * meanRate ‖point x‖) := by
    apply mul_le_mul_of_nonneg_left _ hkpos.le
    have := mul_le_mul_of_nonneg_left hφ hC
    linarith only [hv, this]
  rw [hs2] at hxz
  nlinarith only [hxz, hkv, hμ]

/-! ### The iteration -/

theorem bound_of_pow {h : Vertex m → ℝ} {μ : Seminorm ℝ (Pt m)} {A M C r₀ : ℝ}
    (hsub : ∀ x y, h (x + y) ≤ h x + h y) (h0 : h 0 = 0)
    (hlin : ∀ x, h x ≤ A * ‖point x‖) (hge : ∀ x, μ (point x) ≤ h x)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hchap : ConvexHullApprox h μ M C r₀) {k : ℕ} (hk : 0 < k)
    (hkM : 2 * ((m : ℝ) + 3) * M ≤ k) (n : ℕ) :
    ∀ x : Vertex m, ‖point x‖ ≤ (k * r₀) * 2 ^ n →
      h x - μ (point x) ≤ A * (k * r₀) + 4 * (k * C) * meanRate ‖point x‖ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hB : 0 ≤ (k : ℝ) * C := mul_nonneg hkpos.le hC
  have small : ∀ x : Vertex m, ‖point x‖ ≤ k * r₀ →
      h x - μ (point x) ≤ A * (k * r₀) + 4 * (k * C) * meanRate ‖point x‖ := by
    intro x hx
    have h1 : 0 ≤ μ (point x) := apply_nonneg _ _
    have h2 : h x ≤ A * (k * r₀) := (hlin x).trans (mul_le_mul_of_nonneg_left hx hA)
    have h3 : 0 ≤ 4 * (k * C) * meanRate ‖point x‖ :=
      mul_nonneg (by linarith only [hB]) (meanRate_nonneg _)
    linarith only [h1, h2, h3]
  induction n with
  | zero => intro x hx; exact small x (by simpa using hx)
  | succ n ih =>
    intro x hx
    by_cases hs : ‖point x‖ ≤ k * r₀
    · exact small x hs
    · obtain ⟨z, hz, hstep⟩ := exists_step hsub h0 hge hM hC hchap hk hkM x (not_le.1 hs).le
      have hz' : ‖point z‖ ≤ (k * r₀) * 2 ^ n := by
        have : ‖point x‖ / 2 ≤ (k * r₀) * 2 ^ n := by
          rw [pow_succ] at hx; linarith only [hx]
        exact hz.trans this
      have h1 := ih z hz'
      have hr : 0 ≤ ‖point x‖ := norm_nonneg _
      have h2 : meanRate ‖point z‖ ≤ 3 / 4 * meanRate ‖point x‖ :=
        (meanRate_mono (norm_nonneg _) hz).trans (meanRate_half_le hr)
      have h3 := mul_le_mul_of_nonneg_left h2 (by linarith only [hB] : 0 ≤ 4 * ((k : ℝ) * C))
      linarith only [hstep, h1, h3]

/-- **Alexander's theorem**: a convex-hull approximation of a subadditive, linearly bounded `h`
dominating a seminorm `μ` yields the general approximation `h x ≤ μ x + C' φ(|x|)` for `|x| ≥ 1`. -/
theorem le_add_meanRate_of_convexHullApprox {h : Vertex m → ℝ} {μ : Seminorm ℝ (Pt m)}
    {A M C r₀ : ℝ} (hsub : ∀ x y, h (x + y) ≤ h x + h y) (h0 : h 0 = 0)
    (hlin : ∀ x, h x ≤ A * ‖point x‖) (hge : ∀ x, μ (point x) ≤ h x)
    (hA : 0 ≤ A) (hM : 0 < M) (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hchap : ConvexHullApprox h μ M C r₀) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ x : Vertex m, 1 ≤ ‖point x‖ →
      h x ≤ μ (point x) + C' * meanRate ‖point x‖ := by
  set k : ℕ := ⌈2 * ((m : ℝ) + 3) * M⌉₊ + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos _
  have hkM : 2 * ((m : ℝ) + 3) * M ≤ k := by
    rw [hkdef]; push_cast; linarith only [Nat.le_ceil (2 * ((m : ℝ) + 3) * M)]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hR : 0 < (k : ℝ) * r₀ := mul_pos hkpos hr₀
  have h1 : 1 ≤ meanRate 1 := one_le_meanRate le_rfl
  refine ⟨A * (k * r₀) + 4 * (k * C) + 1, by positivity, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖point x‖ / (k * r₀)) (by norm_num : (1 : ℝ) < 2)
  have hx' : ‖point x‖ ≤ (k * r₀) * 2 ^ n := by
    rw [div_lt_iff₀ hR] at hn; linarith only [hn]
  have hmain := bound_of_pow hsub h0 hlin hge hA hM.le hC hchap hk hkM n x hx'
  have hφ : 1 ≤ meanRate ‖point x‖ := one_le_meanRate hx
  have hAR : 0 ≤ A * (k * r₀) := mul_nonneg hA hR.le
  have hB : 0 ≤ 4 * ((k : ℝ) * C) := by positivity
  have h2 : A * (k * r₀) ≤ A * (k * r₀) * meanRate ‖point x‖ := by
    simpa using mul_le_mul_of_nonneg_left hφ hAR
  have hφ0 := meanRate_nonneg ‖point x‖
  have : (A * (k * r₀) + 4 * (k * C) + 1) * meanRate ‖point x‖ =
      A * (k * r₀) * meanRate ‖point x‖ + 4 * (k * C) * meanRate ‖point x‖ + meanRate ‖point x‖ :=
    by ring
  linarith only [hmain, h2, this, hφ0]

end CurvatureVariance.Infra.FPP
