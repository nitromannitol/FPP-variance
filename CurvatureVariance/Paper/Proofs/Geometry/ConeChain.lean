/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.TurningChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# The proof of Lemma `lem:cone`: no return, and the chain of last exits

The proof of Lemma `lem:cone`, for a sequence of points `f` with the inequality `(*)` of its proof
(`IsExcessPath`), from `f 0` to `f n = f 0 + ℓ (1, t)`.

* `IsExcessPath.add_le`: the inequality `(*)`, in the paper's form, in this order
  or in the reverse order.
* `IsExcessPath.no_return`: the no-return property of the proof: for `R ≥ C S²` the path has no
  vertices `x, x', x''`, in this order or in the reverse order, with `μ(x' − x) ≥ R` and
  `μ(x'' − x) ≤ R/2`.
* `exitIdx`: the indices of the points `z_j` of the proof: `z₀ = u` and, for `j ≥ 1`,
  the last vertex with `μ(v − z_j) ≥ R_j = 2^{−j} μ(v − u)`.
* `endDist_le_of_exitIdx_le`, `le_endDist_of_le_exitIdx`: the range of `μ(v − z)` between `z_j` and
  `z_{j+1}`, including the case `j = 0` (the no-return property at `v, z, u`).
* `angle_exit_link`: one step, the unnumbered display of the proof with the potential
  of the sentence after it.
* `angle_exit_chain`: equation `eq:conestep`, by induction on `j`.
* `angle_end_exit`: equation `eq:cone` at every vertex, the last paragraph of the
  proof except its last sentences.

The constants are those of `ChainConstants`, the potential is that of `chain_link_conditions`, and
one step is `angle_link_le` and `potential_step`. In `ChainConstants` the lower bound of `μ` is
taken as `μlo`, and the proofs here use `2 μlo |z| ≤ μ(z)`: the range
`R_j/4 ≤ μ(v − z) ≤ 2R_j + μ^*` is wider by a bounded factor than that of first entries.

The paper's `C₃ S² ≤ R_j` is here `M S² ≤ R_{j+1}`, that is `C₃ = 2 M`.
-/

@[expose] public section

open InnerProductGeometry

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper

variable {m : ℕ} {μ : Seminorm ℝ (Pt m)} {f : ℕ → Pt m} {n : ℕ} {b S μlo μhi : ℝ}

/-! ### The inequality `(*)`, in both orders -/

/-- **The inequality of the proof of Lemma `lem:cone`**:
`μ(x' − x) + μ(x'' − x') ≤ μ(x'' − x) + C S R^{1/2}` for three points of
the sequence, in this order or in the reverse order, with `|x' − x|, |x'' − x'| ≤ R`, `R ≥ S²`. The
constant is `C = 2 b`. The reverse order is `μ(−z) = μ(z)`. -/
theorem IsExcessPath.add_le (hf : IsExcessPath μ b S f) (hb : 0 ≤ b) (hS : 0 ≤ S) {i j k : ℕ}
    (hord : (i ≤ j ∧ j ≤ k) ∨ (k ≤ j ∧ j ≤ i)) {R : ℝ} (hR : S ^ 2 ≤ R) (h1 : ‖f j - f i‖ ≤ R)
    (h2 : ‖f k - f j‖ ≤ R) :
    μ (f j - f i) + μ (f k - f j) ≤ μ (f k - f i) + 2 * b * S * Real.sqrt R := by
  have hR0 : 0 ≤ R := (sq_nonneg S).trans hR
  have hD : S ^ 2 ≤ 2 * R := by linarith only [hR, hR0]
  have h3 : ‖f k - f i‖ ≤ 2 * R := by
    have e : f k - f i = (f k - f j) + (f j - f i) := by abel
    rw [e]
    linarith only [norm_add_le (f k - f j) (f j - f i), h1, h2]
  have h1' : ‖f j - f i‖ ≤ 2 * R := by linarith only [h1, hR0]
  have h2' : ‖f k - f j‖ ≤ 2 * R := by linarith only [h2, hR0]
  have hsqrt : b * S * Real.sqrt (2 * R) ≤ 2 * b * S * Real.sqrt R := by
    have e : Real.sqrt (2 * R) = Real.sqrt 2 * Real.sqrt R := Real.sqrt_mul (by norm_num) R
    have h2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    rw [e]
    have hs := Real.sqrt_nonneg R
    calc b * S * (Real.sqrt 2 * Real.sqrt R) ≤ b * S * (2 * Real.sqrt R) := by gcongr
      _ = 2 * b * S * Real.sqrt R := by ring
  rcases hord with ⟨hij, hjk⟩ | ⟨hkj, hji⟩
  · have := hf.excess_le i j k hij hjk (2 * R) hD h1' h2' h3
    linarith only [this, hsqrt]
  · have h1'' : ‖f i - f j‖ ≤ 2 * R := by rw [norm_sub_rev]; exact h1'
    have h2'' : ‖f j - f k‖ ≤ 2 * R := by rw [norm_sub_rev]; exact h2'
    have h3'' : ‖f i - f k‖ ≤ 2 * R := by rw [norm_sub_rev]; exact h3
    have := hf.excess_le k j i hkj hji (2 * R) hD h2'' h1'' h3''
    rw [map_sub_rev μ (f j) (f k), map_sub_rev μ (f i) (f j), map_sub_rev μ (f i) (f k)] at this
    linarith only [this, hsqrt]

/-! ### The no-return property -/

/-- The constant `C` of the no-return property: the property holds for `R ≥ C S²`. -/
noncomputable def noReturnConst (μlo μhi b : ℝ) : ℝ :=
  8 * b ^ 2 / μlo + 1 + 2 * μhi + μlo

/-- The no-return property for three points in the order of the sequence. See
`IsExcessPath.no_return`. -/
theorem IsExcessPath.no_return_forward (hf : IsExcessPath μ b S f) (hb : 0 ≤ b) (hμlo : 0 < μlo)
    (hμhi : 0 ≤ μhi) (hlo : ∀ z, μlo * ‖z‖ ≤ μ z) (hhi : ∀ z, μ z ≤ μhi * ‖z‖) (hS : 1 ≤ S) {R : ℝ}
    (hR : noReturnConst μlo μhi b * S ^ 2 ≤ R) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (h1 : R ≤ μ (f j - f i)) (h2 : μ (f k - f i) ≤ R / 2) : False := by
  have hS0 : 0 ≤ S := by linarith only [hS]
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hX : 0 ≤ 8 * b ^ 2 / μlo := by positivity
  have hsum : noReturnConst μlo μhi b * S ^ 2 =
      8 * b ^ 2 / μlo * S ^ 2 + S ^ 2 + 2 * μhi * S ^ 2 + μlo * S ^ 2 := by
    unfold noReturnConst; ring
  have e1 : 0 ≤ 8 * b ^ 2 / μlo * S ^ 2 := by positivity
  have e2 : 2 * μhi ≤ 2 * μhi * S ^ 2 := le_mul_of_one_le_right (by positivity) hS2
  have e3 : 0 ≤ μlo * S ^ 2 := by positivity
  have hR1 : 2 * μhi ≤ R := by linarith only [hR, hsum, e1, e2, e3, hS2]
  have hR2 : μlo * S ^ 2 ≤ R := by linarith only [hR, hsum, e1, e2, hS2, hμhi]
  have hR3 : 8 * b ^ 2 / μlo * S ^ 2 < R := by
    have : 0 ≤ 2 * μhi * S ^ 2 := by positivity
    linarith only [hR, hsum, this, e3, hS2]
  have hR0 : 0 < R := by linarith only [hR2, e3, hR3, e1]
  -- the first vertex after `x` with `μ(x̃ − x) ≥ R`
  have hex : ∃ l, i ≤ l ∧ R ≤ μ (f l - f i) := ⟨j, hij, h1⟩
  classical
  obtain ⟨hil, hlR⟩ := Nat.find_spec hex
  have hlj : Nat.find hex ≤ j := Nat.find_min' hex ⟨hij, h1⟩
  have hne : Nat.find hex ≠ i := by
    intro h
    rw [h, sub_self, map_zero] at hlR
    linarith only [hlR, hR0]
  obtain ⟨l', hl'⟩ : ∃ l', Nat.find hex = l' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by omega)
  have hil' : i ≤ l' := by omega
  have hmin : μ (f l' - f i) < R := by
    by_contra h
    exact Nat.find_min hex (show l' < Nat.find hex by omega) ⟨hil', not_lt.1 h⟩
  rw [hl'] at hlR hlj hil
  -- `μ(x̃ − x) ≤ R + μ^*`
  have hup : μ (f (l' + 1) - f i) ≤ R + μhi := by
    have e : f (l' + 1) - f i = (f (l' + 1) - f l') + (f l' - f i) := by abel
    have h3 := map_add_le_add μ (f (l' + 1) - f l') (f l' - f i)
    rw [← e] at h3
    have h4 : μ (f (l' + 1) - f l') ≤ μhi * 1 :=
      (hhi _).trans (mul_le_mul_of_nonneg_left (hf.norm_succ_sub_le l') hμhi)
    linarith only [h3, h4, hmin]
  -- so `|x̃ − x|, |x'' − x̃| ≤ 2R / μ_*`
  have hnorm : ∀ z : Pt m, ‖z‖ ≤ μ z / μlo := fun z => by
    rw [le_div_iff₀ hμlo, mul_comm]; exact hlo z
  have d1 : ‖f (l' + 1) - f i‖ ≤ 2 * R / μlo :=
    (hnorm _).trans (div_le_div_of_nonneg_right (by linarith only [hup, hR1, hR0]) hμlo.le)
  have hsplit : μ (f k - f (l' + 1)) ≤ μ (f k - f i) + μ (f (l' + 1) - f i) := by
    have e : f k - f (l' + 1) = (f k - f i) - (f (l' + 1) - f i) := by abel
    rw [e]
    exact map_sub_le_add μ _ _
  have d2 : ‖f k - f (l' + 1)‖ ≤ 2 * R / μlo :=
    (hnorm _).trans (div_le_div_of_nonneg_right (by linarith only [hsplit, h2, hup, hR1, hR0])
      hμlo.le)
  have hSD : S ^ 2 ≤ 2 * R / μlo := by
    rw [le_div_iff₀ hμlo]
    linarith only [hR2, hR0, mul_comm (S ^ 2) μlo]
  have hadd := hf.add_le hb hS0 (Or.inl ⟨hil, hlj.trans hjk⟩) hSD d1 d2
  -- the inequality for `x, x̃, x''` gives `3R/2 ≤ R/2 + C S R^{1/2}`
  have hlow : μ (f (l' + 1) - f i) - μ (f k - f i) ≤ μ (f k - f (l' + 1)) := by
    have e : f (l' + 1) - f i = (f k - f i) - (f k - f (l' + 1)) := by abel
    have h3 := map_sub_le_add μ (f k - f i) (f k - f (l' + 1))
    rw [← e] at h3
    linarith only [h3]
  have hkey : R ≤ 2 * b * S * Real.sqrt (2 * R / μlo) := by
    linarith only [hadd, hlow, hlR, h2]
  -- which is false
  have hD0 : 0 ≤ 2 * R / μlo := by positivity
  have hsq : R ^ 2 ≤ (2 * b * S) ^ 2 * (2 * R / μlo) := by
    have := pow_le_pow_left₀ hR0.le hkey 2
    rwa [mul_pow, Real.sq_sqrt hD0] at this
  have e4 : (2 * b * S) ^ 2 * (2 * R / μlo) = R * (8 * b ^ 2 / μlo * S ^ 2) := by
    field_simp
    ring
  rw [e4, sq] at hsq
  have := le_of_mul_le_mul_left hsq hR0
  linarith only [this, hR3]

/-- **The no-return property** (the proof of Lemma `lem:cone`): for
`R ≥ C S²`, the path has no vertices `x, x', x''`, in this order or in the reverse order, with
`μ(x' − x) ≥ R` and `μ(x'' − x) ≤ R/2`. The proof is the paper's, through the first vertex `x̃`
after `x`, in the order of the triple, with `μ(x̃ − x) ≥ R`. Passing to the sequence
`i ↦ −f (i₀ − i)` turns the reverse order into the order of the sequence, which is "in the order of
the triple". -/
theorem IsExcessPath.no_return (hf : IsExcessPath μ b S f) (hb : 0 ≤ b) (hμlo : 0 < μlo)
    (hμhi : 0 ≤ μhi) (hlo : ∀ z, μlo * ‖z‖ ≤ μ z) (hhi : ∀ z, μ z ≤ μhi * ‖z‖) (hS : 1 ≤ S) {R : ℝ}
    (hR : noReturnConst μlo μhi b * S ^ 2 ≤ R) {i j k : ℕ}
    (hord : (i ≤ j ∧ j ≤ k) ∨ (k ≤ j ∧ j ≤ i)) (h1 : R ≤ μ (f j - f i))
    (h2 : μ (f k - f i) ≤ R / 2) : False := by
  rcases hord with ⟨hij, hjk⟩ | ⟨hkj, hji⟩
  · exact hf.no_return_forward hb hμlo hμhi hlo hhi hS hR hij hjk h1 h2
  · have e0 : i - (i - i) = i := by omega
    have e1 : i - (i - j) = j := by omega
    have e2 : i - (i - k) = k := by omega
    refine (hf.reverse i).no_return_forward hb hμlo hμhi hlo hhi hS hR (i := i - i) (j := i - j)
      (k := i - k) (by omega) (by omega) ?_ ?_
    · simp only [e0, e1, neg_sub_neg]
      rw [map_sub_rev]
      exact h1
    · simp only [e0, e2, neg_sub_neg]
      rw [map_sub_rev]
      exact h2

/-! ### Last exits -/

open Classical in
/-- The last index at most `n` at norm distance at least `R` from the final point `f n`. -/
noncomputable def lastExit (μ : Seminorm ℝ (Pt m)) (f : ℕ → Pt m) (n : ℕ) (R : ℝ) : ℕ :=
  Nat.findGreatest (fun i => R ≤ endDist μ f n i) n

theorem le_endDist_lastExit {R : ℝ} (hR : R ≤ endDist μ f n 0) :
    R ≤ endDist μ f n (lastExit μ f n R) := by
  classical
  exact Nat.findGreatest_spec (P := fun i => R ≤ endDist μ f n i) (Nat.zero_le n) hR

theorem lastExit_le_length (R : ℝ) : lastExit μ f n R ≤ n :=
  Nat.findGreatest_le n

theorem endDist_lt_of_lastExit_lt {R : ℝ} {i : ℕ} (hi : lastExit μ f n R < i) (hin : i ≤ n) :
    endDist μ f n i < R := by
  classical
  exact not_le.1 (Nat.findGreatest_is_greatest hi hin)

/-- Last exits increase as the radius decreases. -/
theorem lastExit_anti {R R' : ℝ} (hRR' : R' ≤ R) (hR : R ≤ endDist μ f n 0) :
    lastExit μ f n R ≤ lastExit μ f n R' := by
  classical
  exact Nat.le_findGreatest (lastExit_le_length R) (hRR'.trans (le_endDist_lastExit hR))

/-- At a positive radius at most the norm distance of the initial point, the last exit is at norm
distance at most `R + μ^*`: the paper's `R_j ≤ μ(v − z_j) ≤ R_j + μ^*` for `j ≥ 1`. -/
theorem endDist_lastExit_le (hstep : ∀ i, ‖f (i + 1) - f i‖ ≤ 1) (hhi : ∀ z, μ z ≤ μhi * ‖z‖)
    (hμhi : 0 ≤ μhi) {R : ℝ} (hR0 : 0 < R) (hR : R ≤ endDist μ f n 0) :
    endDist μ f n (lastExit μ f n R) ≤ R + μhi := by
  set k := lastExit μ f n R with hk
  have hkn : k ≤ n := lastExit_le_length R
  have hkR : R ≤ endDist μ f n k := le_endDist_lastExit hR
  have hne : k ≠ n := by
    intro h
    rw [h, endDist_self] at hkR
    linarith only [hkR, hR0]
  have hlt : endDist μ f n (k + 1) < R := endDist_lt_of_lastExit_lt (by omega) (by omega)
  have h2 : endDist μ f n k ≤ endDist μ f n (k + 1) + μhi := by
    unfold endDist
    have e : f n - f k = (f n - f (k + 1)) + (f (k + 1) - f k) := by abel
    rw [e]
    refine (map_add_le_add μ _ _).trans (add_le_add le_rfl ?_)
    calc _ ≤ μhi * ‖f (k + 1) - f k‖ := hhi _
      _ ≤ μhi * 1 := mul_le_mul_of_nonneg_left (hstep k) hμhi
      _ = μhi := mul_one _
  linarith only [hlt, h2]

/-- The indices of the points `z_j` of the proof of Lemma `lem:cone`:
`z₀ = u` and, for `j ≥ 1`, `z_j` is the last vertex with `μ(v − z_j) ≥ R_j`, with
`R_j = 2^{−j} μ(v − u)`. -/
noncomputable def exitIdx (μ : Seminorm ℝ (Pt m)) (f : ℕ → Pt m) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => lastExit μ f n (endDist μ f n 0 / 2 ^ (j + 1))

theorem exitIdx_le_length (j : ℕ) : exitIdx μ f n j ≤ n := by
  cases j with
  | zero => exact Nat.zero_le n
  | succ j => exact lastExit_le_length _

/-- The chain points come in order along the path. -/
theorem exitIdx_le_succ (j : ℕ) : exitIdx μ f n j ≤ exitIdx μ f n (j + 1) := by
  cases j with
  | zero => exact Nat.zero_le _
  | succ j =>
    have hR₀ : 0 ≤ endDist μ f n 0 := apply_nonneg μ _
    have h1 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ one_le_two
    refine lastExit_anti ?_ (div_le_self hR₀ h1)
    exact div_le_div_of_nonneg_left hR₀ (by positivity)
      (pow_le_pow_right₀ one_le_two (Nat.le_succ _))

/-- Every vertex up to `z_{J+1}` lies between two consecutive chain points, up to the index `J`. -/
theorem exists_exitIdx_between {k : ℕ} (J : ℕ) (hk : k ≤ exitIdx μ f n (J + 1)) :
    ∃ j ≤ J, exitIdx μ f n j ≤ k ∧ k ≤ exitIdx μ f n (j + 1) := by
  induction J with
  | zero => exact ⟨0, le_rfl, Nat.zero_le k, hk⟩
  | succ J ih =>
    by_cases h : k ≤ exitIdx μ f n (J + 1)
    · obtain ⟨j, hj, h1, h2⟩ := ih h
      exact ⟨j, by omega, h1, h2⟩
    · exact ⟨J + 1, le_rfl, by omega, hk⟩

/-- `a ≤ R₀ / 2^J` and `R₀ / 2^(J+1) < a` for one `J`: the largest `j` with `R_j ≥ a`. -/
theorem exists_largest_dyadic {R₀ a : ℝ} (ha : 0 < a) (haR : a ≤ R₀) :
    ∃ J : ℕ, a ≤ R₀ / 2 ^ J ∧ R₀ / 2 ^ (J + 1) < a := by
  classical
  have hex : ∃ j : ℕ, R₀ / 2 ^ j < a := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R₀ / a) one_lt_two
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ ha] at hk
    linarith only [hk]
  have hne : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_zero, div_one] at this
    linarith only [this, haR]
  obtain ⟨J, hJ⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨J, not_lt.1 (Nat.find_min hex (by omega)), ?_⟩
  have := Nat.find_spec hex
  rwa [hJ] at this

/-! ### The range of `μ(v − z)` between two chain points -/

variable {δ c C r₁ T Kc P Q η ε₁ M ε₀ : ℝ} {t₀ : EuclideanSpace ℝ (Fin m)}

/-- **The upper bound of the range**: a vertex `z` from `z_j` on has `μ(v − z) ≤ 2 R_j + μ^*`.

This is the bound of the proof of Lemma `lem:cone`. At `j = 0` the point
`z₀ = u` is not a last exit, since a path may first move away from `v`, and, as in the paper, the
no-return property at `v, z, u`, in the reverse order, gives `μ(v − z) < 2 R₀`; for `j ≥ 1` the
stronger bound `μ(v − z) ≤ R_j + μ^*` holds. Every later use needs only `|v − z| ≤ C R_j`. -/
theorem endDist_le_of_exitIdx_le (hf : IsExcessPath μ b S f) (hb : 0 ≤ b) (hμlo : 0 < μlo)
    (hμhi : 0 ≤ μhi) (hlo : ∀ z, μlo * ‖z‖ ≤ μ z) (hhi : ∀ z, μ z ≤ μhi * ‖z‖) (hS : 1 ≤ S)
    (hR₀ : noReturnConst μlo μhi b * S ^ 2 ≤ 2 * endDist μ f n 0) (hR₀0 : 0 < endDist μ f n 0)
    {j k : ℕ} (hjk : exitIdx μ f n j ≤ k) (hkn : k ≤ n) :
    endDist μ f n k ≤ 2 * (endDist μ f n 0 / 2 ^ j) + μhi := by
  cases j with
  | zero =>
    have hnot : ¬ 2 * endDist μ f n 0 ≤ endDist μ f n k := fun h => by
      refine hf.no_return hb hμlo hμhi hlo hhi hS hR₀ (i := n) (j := k) (k := 0)
        (Or.inr ⟨Nat.zero_le k, hkn⟩) ?_ ?_
      · rw [map_sub_rev]; exact h
      · rw [map_sub_rev]
        show endDist μ f n 0 ≤ 2 * endDist μ f n 0 / 2
        linarith only [hR₀0]
    simp only [pow_zero, div_one]
    linarith only [not_le.1 hnot, hμhi]
  | succ j =>
    set R := endDist μ f n 0 / 2 ^ (j + 1) with hRdef
    have h1 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ one_le_two
    have hR0 : 0 < R := by positivity
    have hR : R ≤ endDist μ f n 0 := div_le_self hR₀0.le h1
    have hle : exitIdx μ f n (j + 1) = lastExit μ f n R := rfl
    rw [hle] at hjk
    rcases hjk.lt_or_eq with h | h
    · have := endDist_lt_of_lastExit_lt h hkn
      linarith only [this, hR0, hμhi]
    · rw [← h]
      have := endDist_lastExit_le hf.norm_succ_sub_le hhi hμhi hR0 hR
      linarith only [this, hR0]

/-- **The lower bound of the range**: a vertex `z` up to `z_{j+1}` has
`μ(v − z) ≥ R_{j+1}/2 = R_j/4`, by the no-return property at `v, z_{j+1}, z`, in the reverse
order. -/
theorem le_endDist_of_le_exitIdx (hf : IsExcessPath μ b S f) (hb : 0 ≤ b) (hμlo : 0 < μlo)
    (hμhi : 0 ≤ μhi) (hlo : ∀ z, μlo * ‖z‖ ≤ μ z) (hhi : ∀ z, μ z ≤ μhi * ‖z‖) (hS : 1 ≤ S)
    {j k : ℕ} (hR : noReturnConst μlo μhi b * S ^ 2 ≤ endDist μ f n 0 / 2 ^ (j + 1))
    (hR₀0 : 0 ≤ endDist μ f n 0) (hk : k ≤ exitIdx μ f n (j + 1)) :
    endDist μ f n 0 / 2 ^ (j + 1) / 2 ≤ endDist μ f n k := by
  by_contra hcon
  have hle : exitIdx μ f n (j + 1) = lastExit μ f n (endDist μ f n 0 / 2 ^ (j + 1)) := rfl
  have h1 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ one_le_two
  have hmem : exitIdx μ f n (j + 1) ≤ n := exitIdx_le_length (j + 1)
  refine hf.no_return hb hμlo hμhi hlo hhi hS hR (i := n) (j := exitIdx μ f n (j + 1)) (k := k)
    (Or.inr ⟨hk, hmem⟩) ?_ ?_
  · rw [map_sub_rev, hle]
    exact le_endDist_lastExit (div_le_self hR₀0 h1)
  · rw [map_sub_rev]
    exact (not_le.1 hcon).le

/-! ### One step -/

/-- `ChainConstants` is monotone in the lowest radius. -/
theorem ChainConstants.mono_M (hK : ChainConstants μlo μhi δ c C r₁ b T Kc P Q η ε₁ M ε₀) {M' : ℝ}
    (hM : M ≤ M') : ChainConstants μlo μhi δ c C r₁ b T Kc P Q η ε₁ M' ε₀ :=
  { hK with
    one_le_M := hK.one_le_M.trans hM
    two_mul_le_M := hK.two_mul_le_M.trans hM
    fluct_le := fun S R hS hR hMR =>
      hK.fluct_le S R hS hR ((mul_le_mul_of_nonneg_right hM (sq_nonneg S)).trans hMR) }

/-- **One step of the chain** (the proof of Lemma `lem:cone`): suppose that
equation `eq:conestep` holds at `j` and that `R_{j+1} ≥ M S²`. For every vertex `z` between `z_j`
and `z_{j+1}`,

`∠(v − z, (1, t)) ≤ P S^{1/2} R_{j+1}^{−1/4} + Q (j + 1) |t − t₀|^{1+δ/2}`.

The range of `μ(v − z)` gives `|v − z_j|, |v − z| ≤ C R_{j+1}` and `R_{j+1} ≤ C |v − z|`;
`angle_link_le` is the unnumbered display of the paper's proof, through a subgradient at the
slope `t_j'` of `v − z_j`, and `potential_step` is the computation of its last two sentences. -/
theorem angle_exit_link (hK : ChainConstants μlo μhi δ c C r₁ b T Kc P Q η ε₁ M ε₀)
    (hlo₂ : ∀ z, 2 * μlo * ‖z‖ ≤ μ z) (hhi : ∀ z, μ z ≤ μhi * ‖z‖)
    (hM : noReturnConst μlo μhi b ≤ M) (hsupp : AngularSupport μ t₀ δ c C r₁)
    (hf : IsExcessPath μ b S f) (hS : 1 ≤ S) {t : EuclideanSpace ℝ (Fin m)} {L : ℝ}
    (htT : ‖t‖ ≤ T) (ht : ‖t - t₀‖ ≤ ε₀) (htL : ‖t - t₀‖ ^ (δ / 2) * L ≤ ε₀)
    (hlen : ‖f n - f 0‖ ≤ S ^ 2 * Real.exp L) {j k : ℕ}
    (hj1 : M * S ^ 2 ≤ endDist μ f n 0 / 2 ^ (j + 1))
    (hΦ : angle (f n - f (exitIdx μ f n j)) (slopeVec t) ≤
      P * turnErr S (endDist μ f n 0 / 2 ^ j) + Q * j * ‖t - t₀‖ ^ (1 + δ / 2))
    (hk : exitIdx μ f n j ≤ k) (hk' : k ≤ exitIdx μ f n (j + 1)) :
    angle (f n - f k) (slopeVec t) ≤
      P * turnErr S (endDist μ f n 0 / 2 ^ (j + 1)) +
        Q * (j + 1) * ‖t - t₀‖ ^ (1 + δ / 2) := by
  have hμlo := hK.μlo_pos
  have hμhi : 0 < μhi := hμlo.trans_le hK.μlo_le_μhi
  have hb := hK.b_nonneg
  have hlo : ∀ z, μlo * ‖z‖ ≤ μ z := fun z =>
    (mul_le_mul_of_nonneg_right (by linarith only [hμlo]) (norm_nonneg z)).trans (hlo₂ z)
  have hS0 : 0 ≤ S := by linarith only [hS]
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hKc : 0 < Kc := lt_of_lt_of_le one_pos hK.one_le_Kc
  have hA₁ := stepConst_nonneg Kc b c
  have hA₂ := Real.sqrt_nonneg (C / c)
  have hkn : k ≤ n := hk'.trans (exitIdx_le_length _)
  have hiKn : exitIdx μ f n j ≤ n := exitIdx_le_length _
  have hRj : endDist μ f n 0 / 2 ^ j = 2 * (endDist μ f n 0 / 2 ^ (j + 1)) := by
    rw [pow_succ]; field_simp
  set R' := endDist μ f n 0 / 2 ^ (j + 1) with hR'def
  have hMS : M ≤ M * S ^ 2 := le_mul_of_one_le_right (zero_le_one.trans hK.one_le_M) hS2
  have hRμ : 2 * μhi ≤ R' := by linarith only [hK.two_mul_le_M, hMS, hj1]
  have hR' : 0 < R' := by linarith only [hRμ, hμhi]
  have hR₀0 : 0 < endDist μ f n 0 := by
    by_contra h
    have h1 : endDist μ f n 0 / 2 ^ (j + 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (not_lt.1 h) (by positivity)
    linarith only [h1, hR', hR'def]
  have hj : M * S ^ 2 ≤ endDist μ f n 0 / 2 ^ j := by rw [hRj]; linarith only [hj1, hR']
  have hjL := chain_index_le hK hhi hS hlen hj
  obtain ⟨hX, hY, hβ4, hβr⟩ :=
    chain_link_conditions hK hS0 ht htL (by positivity) hj hjL
  -- the range of `μ(v − z)`, at `j = 0` by the no-return property at `v, z, u`
  have hret : noReturnConst μlo μhi b * S ^ 2 ≤ 2 * endDist μ f n 0 := by
    have h1 : noReturnConst μlo μhi b * S ^ 2 ≤ R' :=
      (mul_le_mul_of_nonneg_right hM (by positivity)).trans hj1
    have h2 : R' ≤ endDist μ f n 0 := div_le_self hR₀0.le (one_le_pow₀ one_le_two)
    linarith only [h1, h2, hR₀0]
  have hret' : noReturnConst μlo μhi b * S ^ 2 ≤ R' :=
    (mul_le_mul_of_nonneg_right hM (by positivity)).trans hj1
  have hup := endDist_le_of_exitIdx_le hf hb hμlo hμhi.le hlo hhi hS hret hR₀0 hk hkn
  have hupi := endDist_le_of_exitIdx_le hf hb hμlo hμhi.le hlo hhi hS hret hR₀0 le_rfl hiKn
  have hlow := le_endDist_of_le_exitIdx hf hb hμlo hμhi.le hlo hhi hS hret' hR₀0.le hk'
  rw [hRj] at hup hupi
  rw [← hR'def] at hlow
  -- the comparisons with `R_{j+1}`
  have hKμ : 4 ≤ Kc * μlo := by rw [← div_le_iff₀ hμlo]; exact hK.four_div_le_Kc
  have hKμR : R' * 4 ≤ R' * (Kc * μlo) := mul_le_mul_of_nonneg_left hKμ hR'.le
  have hnorm : ∀ a : ℕ, endDist μ f n a ≤ 2 * (2 * R') + μhi → ‖f n - f a‖ ≤ Kc * R' := by
    intro a ha
    have e1 : 2 * μlo * ‖f n - f a‖ ≤ endDist μ f n a := hlo₂ _
    have e2 : 2 * μlo * ‖f n - f a‖ ≤ 2 * μlo * (Kc * R') := by
      have e3 : 2 * μlo * (Kc * R') = 2 * (R' * (Kc * μlo)) := by ring
      linarith only [e1, ha, hRμ, hKμR, e3, hR']
    exact le_of_mul_le_mul_left e2 (by positivity)
  have h₁ := hnorm _ hupi
  have h₂ := hnorm _ hup
  have h₃ : R' ≤ Kc * ‖f n - f k‖ := by
    have e1 : endDist μ f n k ≤ μhi * ‖f n - f k‖ := hhi _
    have e2 : 2 * μhi * ‖f n - f k‖ ≤ Kc * ‖f n - f k‖ :=
      mul_le_mul_of_nonneg_right hK.two_mul_le_Kc (norm_nonneg _)
    have e3 : 2 * (μhi * ‖f n - f k‖) = 2 * μhi * ‖f n - f k‖ := by ring
    linarith only [hlow, e1, e2, e3]
  have hSR : S ^ 2 ≤ 2 * Kc * R' := by
    have e1 : S ^ 2 ≤ M * S ^ 2 := le_mul_of_one_le_left (sq_nonneg S) hK.one_le_M
    have e2 : R' ≤ 2 * Kc * R' := by
      have := mul_le_mul_of_nonneg_right hK.one_le_Kc hR'.le
      linarith only [this, hR']
    linarith only [e1, e2, hj1]
  -- the display of the paper's proof
  have hlink := angle_link_le hsupp hK.c_pos hK.C_nonneg hf hK.b_nonneg hS0 htT hk hkn hΦ
    hβ4 hβr hKc hR' hSR h₁ h₂ h₃ hK.δ_pos.le
  rw [hRj] at hlink hX
  exact potential_step hR' hK.δ_pos hK.δ_le_one (slopeFactor_pos hK.T_nonneg) hA₁ hA₂
    hK.P_ge hK.Q_ge hK.η_le hK.rpow_ε₁_le (norm_nonneg (t - t₀)) (Nat.cast_nonneg j) hX hY hlink

/-- **Equation `eq:conestep`**, by induction on `j`: with
`R₀ = μ(v − u)` and `R_j = R₀ / 2 ^ j`, the chain point `z_j` is at angle at most
`P S^{1/2} R_j^{−1/4} + Q j |t − t₀|^{1+δ/2}` from `(1, t)`, for every `j` with `R_j ≥ M S²`. -/
theorem angle_exit_chain (hK : ChainConstants μlo μhi δ c C r₁ b T Kc P Q η ε₁ M ε₀)
    (hlo₂ : ∀ z, 2 * μlo * ‖z‖ ≤ μ z) (hhi : ∀ z, μ z ≤ μhi * ‖z‖)
    (hM : noReturnConst μlo μhi b ≤ M) (hsupp : AngularSupport μ t₀ δ c C r₁)
    (hf : IsExcessPath μ b S f) (hS : 1 ≤ S) {t : EuclideanSpace ℝ (Fin m)} {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hend : f n - f 0 = ℓ • slopeVec t) (htT : ‖t‖ ≤ T) (ht : ‖t - t₀‖ ≤ ε₀)
    (htL : ‖t - t₀‖ ^ (δ / 2) * L ≤ ε₀) (hlen : ‖f n - f 0‖ ≤ S ^ 2 * Real.exp L) :
    ∀ j : ℕ, M * S ^ 2 ≤ endDist μ f n 0 / 2 ^ j →
      angle (f n - f (exitIdx μ f n j)) (slopeVec t) ≤
        P * turnErr S (endDist μ f n 0 / 2 ^ j) + Q * j * ‖t - t₀‖ ^ (1 + δ / 2) := by
  have hμlo := hK.μlo_pos
  have hP0 : 0 ≤ P := le_trans (by have := stepConst_nonneg Kc b c; positivity) hK.P_ge
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : exitIdx μ f n 0 = 0 := rfl
    rw [h0, hend, angle_smul_slopeVec_self hℓ]
    have := turnErr_nonneg S (endDist μ f n 0 / 2 ^ 0)
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    positivity
  | succ j ih =>
    intro hj1
    have hR₀ : 0 ≤ endDist μ f n 0 := apply_nonneg μ _
    have hj : M * S ^ 2 ≤ endDist μ f n 0 / 2 ^ j := hj1.trans
      (div_le_div_of_nonneg_left hR₀ (by positivity)
        (pow_le_pow_right₀ one_le_two (Nat.le_succ _)))
    have := angle_exit_link hK hlo₂ hhi hM hsupp hf hS htT ht htL hlen hj1 (ih hj)
      (exitIdx_le_succ j) le_rfl
    push_cast
    exact this

/-- **Equation `eq:cone`**, for a sequence (the end of the proof of Lemma `lem:cone`). For an excess
path `f` with `f n − f 0 = ℓ (1, t)`, `‖f n − f 0‖ ≤ S² e^L`, `‖t‖ ≤ T`, `‖t − t₀‖ ≤ ε₀` and
`‖t − t₀‖^{δ/2} L ≤ ε₀`, every index `k ≤ n` with `‖f n − f k‖ ≥ K S²` has
`∠(f n − f k, (1, t)) ≤ K (S^{1/2} ‖f n − f k‖^{−1/4} + ‖t − t₀‖^{1+δ/2} L)`.

As in the paper, if `R₀ < C₃ S²` the no-return property at `v, z, u`, in the reverse order, bounds
`μ(v − z)` by a multiple of `S²`, so there is nothing to prove; here `C₃ = 2 M`, and the multiple is
`4 M`. Otherwise let `J` be the largest `j` with `R_j ≥ C₃ S²`. The vertices after `z_{J+1}` have
`μ(v − z) < R_{J+1} < C₃ S²`, and again there is nothing to prove. Every other vertex lies between
`z_j` and `z_{j+1}` for some `j ≤ J`, and `angle_exit_link` applies. -/
theorem angle_end_exit (hK : ChainConstants μlo μhi δ c C r₁ b T Kc P Q η ε₁ M ε₀)
    (hlo₂ : ∀ z, 2 * μlo * ‖z‖ ≤ μ z) (hhi : ∀ z, μ z ≤ μhi * ‖z‖)
    (hM : noReturnConst μlo μhi b ≤ M) (hsupp : AngularSupport μ t₀ δ c C r₁)
    (hf : IsExcessPath μ b S f) (hS : 1 ≤ S) {t : EuclideanSpace ℝ (Fin m)} {ℓ L : ℝ} (hL : 1 ≤ L)
    (hℓ : 0 < ℓ) (hend : f n - f 0 = ℓ • slopeVec t) (htT : ‖t‖ ≤ T) (ht : ‖t - t₀‖ ≤ ε₀)
    (htL : ‖t - t₀‖ ^ (δ / 2) * L ≤ ε₀) (hlen : ‖f n - f 0‖ ≤ S ^ 2 * Real.exp L) {K : ℝ}
    (hK1 : 8 * M / μlo ≤ K) (hK3 : P * (min (μlo / 4) 1)⁻¹ ≤ K) (hK4 : 3 * Q ≤ K)
    (hK5 : 1 ≤ K) {k : ℕ} (hk : k ≤ n) (hRk : K * S ^ 2 ≤ ‖f n - f k‖) :
    angle (f n - f k) (slopeVec t) ≤
      K * (S ^ ((1 : ℝ) / 2) * ‖f n - f k‖ ^ (-(1 : ℝ) / 4) + ‖t - t₀‖ ^ (1 + δ / 2) * L) := by
  set RE := ‖f n - f k‖ with hREdef
  have hμlo := hK.μlo_pos
  have hμhi : 0 < μhi := hμlo.trans_le hK.μlo_le_μhi
  have hb := hK.b_nonneg
  have hlo : ∀ z, μlo * ‖z‖ ≤ μ z := fun z =>
    (mul_le_mul_of_nonneg_right (by linarith only [hμlo]) (norm_nonneg z)).trans (hlo₂ z)
  have hS0 : 0 ≤ S := by linarith only [hS]
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hS2' : 0 < S ^ 2 := by positivity
  have hKc : 0 < Kc := lt_of_lt_of_le one_pos hK.one_le_Kc
  have hA₁ := stepConst_nonneg Kc b c
  have hA₂ := Real.sqrt_nonneg (C / c)
  have hP0 : 0 ≤ P := le_trans (by positivity) hK.P_ge
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hK.Q_ge
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hK.one_le_M
  have hRE0 : 0 < RE := lt_of_lt_of_le (by positivity) hRk
  have hρlo : 2 * μlo * RE ≤ endDist μ f n k := hlo₂ _
  -- `ρ = μ(v − z)` is at least `16 M S²`
  have hρK : 16 * M * S ^ 2 ≤ endDist μ f n k := by
    have e1 : 8 * M ≤ μlo * K := by rw [← div_le_iff₀' hμlo]; exact hK1
    have e2 : 8 * M * S ^ 2 ≤ μlo * K * S ^ 2 := mul_le_mul_of_nonneg_right e1 hS2'.le
    have e3 : 2 * μlo * (K * S ^ 2) ≤ 2 * μlo * RE :=
      mul_le_mul_of_nonneg_left hRk (by positivity)
    linarith only [e2, e3, hρlo]
  have hret : noReturnConst μlo μhi b * S ^ 2 ≤ M * S ^ 2 :=
    mul_le_mul_of_nonneg_right hM hS2'.le
  have hMS0 : 0 < M * S ^ 2 := by positivity
  -- if `R₀ < C₃ S²`, then no return bounds `μ(v − z)`
  have hR₀ : 2 * M * S ^ 2 ≤ endDist μ f n 0 := by
    by_contra h
    push Not at h
    refine hf.no_return hb hμlo hμhi.le hlo hhi hS (R := 4 * (M * S ^ 2))
      (by linarith only [hret, hMS0]) (i := n) (j := k) (k := 0)
      (Or.inr ⟨Nat.zero_le k, hk⟩) ?_ ?_
    · rw [map_sub_rev]
      show 4 * (M * S ^ 2) ≤ endDist μ f n k
      linarith only [hρK, hMS0]
    · rw [map_sub_rev]
      show endDist μ f n 0 ≤ 4 * (M * S ^ 2) / 2
      linarith only [h]
  -- `J`, the largest `j` with `R_j ≥ C₃ S²`
  have hC₃ : 0 < 2 * M * S ^ 2 := by positivity
  obtain ⟨J, hJ1, hJ2⟩ := exists_largest_dyadic hC₃ hR₀
  have hR₀0 : 0 < endDist μ f n 0 := by linarith only [hR₀, hC₃]
  -- the vertices after `z_{J+1}` have `μ(v − z) < C₃ S²`
  have hkJ : k ≤ exitIdx μ f n (J + 1) := by
    by_contra h
    have h1 : lastExit μ f n (endDist μ f n 0 / 2 ^ (J + 1)) < k := not_le.1 h
    have h2 := endDist_lt_of_lastExit_lt h1 hk
    linarith only [h2, hJ2, hρK, hMS0]
  obtain ⟨j, hjJ, hj1, hj2⟩ := exists_exitIdx_between J hkJ
  set R₀ := endDist μ f n 0 with hR₀def
  have hRj : R₀ / 2 ^ j = 2 * (R₀ / 2 ^ (j + 1)) := by rw [pow_succ]; field_simp
  have hRjJ : R₀ / 2 ^ J ≤ R₀ / 2 ^ j :=
    div_le_div_of_nonneg_left hR₀0.le (by positivity) (pow_le_pow_right₀ one_le_two hjJ)
  set R' := R₀ / 2 ^ (j + 1) with hR'def
  have hR'M : M * S ^ 2 ≤ R' := by linarith only [hJ1, hRjJ, hRj]
  have hR' : 0 < R' := by linarith only [hR'M, hMS0]
  have hjM : M * S ^ 2 ≤ R₀ / 2 ^ j := by linarith only [hR'M, hRj, hR']
  have hchain := angle_exit_chain hK hlo₂ hhi hM hsupp hf hS hℓ hend htT ht htL hlen j hjM
  rw [← hR₀def] at hchain
  have hpot := angle_exit_link hK hlo₂ hhi hM hsupp hf hS htT ht htL hlen (j := j) (k := k)
    (by rw [← hR₀def]; exact hR'M) hchain hj1 hj2
  rw [← hR₀def, ← hR'def] at hpot
  have hjL := chain_index_le hK hhi hS hlen hjM
  -- `|v − z| ≤ C R_{j+1}`
  have hMS : M ≤ M * S ^ 2 := le_mul_of_one_le_right hM0.le hS2
  have hRμ : 2 * μhi ≤ R' := by linarith only [hK.two_mul_le_M, hMS, hR'M]
  have hret2 : noReturnConst μlo μhi b * S ^ 2 ≤ 2 * R₀ := by linarith only [hret, hR₀, hMS0]
  have hup := endDist_le_of_exitIdx_le hf hb hμlo hμhi.le hlo hhi hS hret2 hR₀0 hj1 hk
  rw [hRj] at hup
  -- conversion to the Euclidean distance `RE`
  set κ := min (μlo / 4) 1 with hκdef
  have hκ0 : 0 < κ := lt_min (by positivity) one_pos
  have hκ1 : κ ≤ 1 := min_le_right _ _
  have hκRE : κ * RE ≤ R' := by
    have e1 : κ * RE ≤ μlo / 4 * RE := mul_le_mul_of_nonneg_right (min_le_left _ _) hRE0.le
    have e2 : μlo / 4 * RE = 2 * μlo * RE / 8 := by ring
    linarith only [e1, e2, hρlo, hup, hRμ, hR']
  have he : turnErr S R' ≤ κ⁻¹ * turnErr S RE :=
    (turnErr_anti hS0 (by positivity) hκRE).trans (turnErr_mul_le_inv S hRE0 hκ0 hκ1)
  have hτ0 : 0 ≤ ‖t - t₀‖ ^ (1 + δ / 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hj3L : (j : ℝ) + 1 ≤ 3 * L := by linarith only [hjL, hL]
  have e1 : P * turnErr S R' ≤ K * turnErr S RE := by
    calc P * turnErr S R' ≤ P * (κ⁻¹ * turnErr S RE) :=
          mul_le_mul_of_nonneg_left he hP0
      _ = P * κ⁻¹ * turnErr S RE := by ring
      _ ≤ K * turnErr S RE := mul_le_mul_of_nonneg_right hK3 (turnErr_nonneg S RE)
  have e2 : Q * ((j : ℝ) + 1) * ‖t - t₀‖ ^ (1 + δ / 2) ≤ K * (‖t - t₀‖ ^ (1 + δ / 2) * L) := by
    have : Q * ((j : ℝ) + 1) ≤ K * L := by
      calc Q * ((j : ℝ) + 1) ≤ Q * (3 * L) := mul_le_mul_of_nonneg_left hj3L hQ0
        _ = 3 * Q * L := by ring
        _ ≤ K * L := mul_le_mul_of_nonneg_right hK4 (by linarith only [hL])
    calc Q * ((j : ℝ) + 1) * ‖t - t₀‖ ^ (1 + δ / 2) ≤ K * L * ‖t - t₀‖ ^ (1 + δ / 2) :=
          mul_le_mul_of_nonneg_right this hτ0
      _ = K * (‖t - t₀‖ ^ (1 + δ / 2) * L) := by ring
  rw [← turnErr_eq_rpow hS0 hRE0]
  linarith only [hpot, e1, e2]

end CurvatureVariance.Paper.Proofs.Geometry
