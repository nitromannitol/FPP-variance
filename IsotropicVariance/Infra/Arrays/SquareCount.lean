/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Arrays.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Fin.Tuple.Basic
import IsotropicVariance.Infra.Arrays.Estimates
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The counting step of Lemma `lem:polynomialarray`

The sentences of the paper's proof on the sets of triples. For a set of `a` indices, the
triples `(i, k_{i-1}, k_i)` of a sequence at these indices are determined by the indices, the
displacements of the sequence between them and its increments at them. The total length of these
vectors is at most `∑_i |k_i - k_{i-1}| ≤ 2^{r/2} M` when `∑_i |k_i - k_{i-1}|² ≤ 2^r M`, and this
leaves at most `[C 2^{rd} (M/a)^{2d}]^a` sets of triples, `d = m + 1`.

* `pairLength`: the total length of a list of `a` pairs `(k_{i-1}, k_i)`, measured from the last
  point of the list before it. The list of a sequence along increasing indices is `pairList`.
* `pairLength_pairList_le`, `sq_sum_l1Length_le`: the total length of the list of a sequence.
* `tsum_exp_pairLength_le`, `pairCount_le`: the lattice points of the `ℓ¹` ball, by exponential
  weights.
* `choose_mul_pairCount_le`: the count `[C 2^{rd} (M/a)^{2d}]^a`.

Lengths are measured in the norm `ℓ¹` of `ℤ^m`, which is at most `m^{1/2}` times the Euclidean
norm, so the bound on the total length carries this factor. The sets of triples are counted through
their parameters: the set of indices (`M.choose a` choices) and the list of pairs.
-/

@[expose] public section

open scoped ENNReal

namespace IsotropicVariance.Infra.Arrays

variable {m M : ℕ}

/-- The `ℓ¹` norm `∑_j |x_j|` of a lattice vector. -/
noncomputable def l1Length (x : Fin m → ℤ) : ℝ := ∑ j, |(x j : ℝ)|

lemma l1Length_nonneg (x : Fin m → ℤ) : 0 ≤ l1Length x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma l1Length_add_le (x y : Fin m → ℤ) : l1Length (x + y) ≤ l1Length x + l1Length y := by
  unfold l1Length
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simpa only [Pi.add_apply, Int.cast_add] using abs_add_le (x j : ℝ) (y j : ℝ)

/-- The `ℓ¹` norm against the Euclidean norm: `|x|₁² ≤ m |x|²`. -/
lemma l1Length_sq_le (x : Fin m → ℤ) : l1Length x ^ 2 ≤ m * (sqNorm x : ℝ) := by
  have h : (∑ j : Fin m, |(x j : ℝ)|) ^ 2 ≤
      (Finset.univ : Finset (Fin m)).card * ∑ j, |(x j : ℝ)| ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
  simp only [l1Length, sqNorm, Int.cast_sum, Int.cast_pow]
  exact h

section Sums

/-- The sum of `e^{-θ|n|}` over `n ∈ ℤ`. -/
theorem tsum_int_ofReal_exp_neg_abs_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) :
    ∑' n : ℤ, ENNReal.ofReal (Real.exp (-θ * |(n : ℝ)|)) ≤ ENNReal.ofReal (16 / θ) := by
  have hnat : ∑' n : ℕ, ENNReal.ofReal (Real.exp (-θ * n)) ≤ ENNReal.ofReal (8 / θ) := by
    have h := tsum_rpow_mul_exp_neg_le (α := 0) le_rfl h0 h1
    have h8 : tiltConst 0 * θ ^ (-(1 + (0 : ℝ))) = 8 / θ := by
      have hc : tiltConst 0 = 8 := by
        simp only [tiltConst, expPowConst, Real.rpow_zero, Nat.ceil_zero, Nat.factorial_zero]
        norm_num
      rw [hc, add_zero, Real.rpow_neg_one, div_eq_mul_inv]
    rw [h8] at h
    simpa only [Real.rpow_zero, one_mul] using h
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have hpos : ∑' n : ℕ, ENNReal.ofReal (Real.exp (-θ * |(((n : ℤ) : ℝ))|)) ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-θ * n)) :=
    ENNReal.tsum_le_tsum fun n => by
      simp only [Int.cast_natCast, Nat.abs_cast, le_refl]
  have hneg : ∑' n : ℕ, ENNReal.ofReal (Real.exp (-θ * |(((-((n : ℤ) + 1) : ℤ) : ℝ))|)) ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-θ * n)) :=
    ENNReal.tsum_le_tsum fun n => by
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have habs : |(((-((n : ℤ) + 1) : ℤ) : ℝ))| = n + 1 := by
        push_cast
        rw [abs_neg, abs_of_nonneg (by linarith only [hn])]
      rw [habs]
      nlinarith only [h0]
  calc _ ≤ ENNReal.ofReal (8 / θ) + ENNReal.ofReal (8 / θ) :=
        add_le_add (hpos.trans hnat) (hneg.trans hnat)
    _ = ENNReal.ofReal (16 / θ) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The sum of `e^{-θ|x|₁}` over `x ∈ ℤ^m`. -/
theorem tsum_ofReal_exp_neg_l1Length_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) (m : ℕ) :
    ∑' x : Fin m → ℤ, ENNReal.ofReal (Real.exp (-θ * l1Length x)) ≤
      ENNReal.ofReal ((16 / θ) ^ m) := by
  induction m with
  | zero => simp [l1Length]
  | succ m ih =>
    rw [← (Fin.consEquiv (fun _ => ℤ)).tsum_eq, ENNReal.tsum_prod']
    have h16 : 0 ≤ 16 / θ := by positivity
    have key : ∀ (a : ℤ) (y : Fin m → ℤ),
        ENNReal.ofReal (Real.exp (-θ * l1Length ((Fin.consEquiv (fun _ => ℤ)) (a, y))))
          = ENNReal.ofReal (Real.exp (-θ * |(a : ℝ)|)) *
            ENNReal.ofReal (Real.exp (-θ * l1Length y)) := by
      intro a y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      simp only [l1Length, Fin.sum_univ_succ]
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      ring
    simp_rw [key]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, pow_succ, mul_comm ((16 / θ) ^ m), ENNReal.ofReal_mul h16]
    exact mul_le_mul' (tsum_int_ofReal_exp_neg_abs_le h0 h1) ih

/-- The sum of `e^{-θ|x - s|₁}` over `x` does not depend on `s`. -/
lemma tsum_ofReal_exp_neg_l1Length_sub (θ : ℝ) (s : Fin m → ℤ) :
    ∑' x : Fin m → ℤ, ENNReal.ofReal (Real.exp (-θ * l1Length (x - s))) =
      ∑' x : Fin m → ℤ, ENNReal.ofReal (Real.exp (-θ * l1Length x)) :=
  (Equiv.subRight s).tsum_eq fun x => ENNReal.ofReal (Real.exp (-θ * l1Length x))

end Sums

section Lists

/-- A pair `(k_{i-1}, k_i)` of indices of an array. -/
abbrev IdxPair (m : ℕ) : Type := (Fin m → ℤ) × (Fin m → ℤ)

/-- The total length of a list of pairs entered from `s`: the displacement from the last point
before each pair to its first point, and the increment inside each pair. -/
noncomputable def pairLength : (a : ℕ) → (Fin m → ℤ) → (Fin a → IdxPair m) → ℝ
  | 0, _, _ => 0
  | a + 1, s, L =>
      l1Length ((L 0).1 - s) + l1Length ((L 0).2 - (L 0).1) + pairLength a (L 0).2 (Fin.tail L)

lemma pairLength_cons (a : ℕ) (s : Fin m → ℤ) (y : IdxPair m) (L : Fin a → IdxPair m) :
    pairLength (a + 1) s (Fin.cons y L) =
      l1Length (y.1 - s) + l1Length (y.2 - y.1) + pairLength a y.2 L := by
  simp only [pairLength, Fin.cons_zero, Fin.tail_cons]

/-- Exponential weights of the lists of pairs: the sum of `e^{-θ L}` over the lists of `a` pairs of
total length `L`, for any entering point, is at most `(16/θ)^{2ma}`. -/
theorem tsum_exp_pairLength_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) :
    ∀ (a : ℕ) (s : Fin m → ℤ),
      ∑' L : Fin a → IdxPair m, ENNReal.ofReal (Real.exp (-θ * pairLength a s L)) ≤
        ENNReal.ofReal ((16 / θ) ^ (2 * m * a))
  | 0, s => by
    rw [tsum_eq_single (Fin.elim0 : Fin 0 → IdxPair m)
      (fun b hb => (hb (Subsingleton.elim _ _)).elim)]
    simp [pairLength]
  | a + 1, s => by
    have h16 : 0 ≤ 16 / θ := by positivity
    set B : ℝ≥0∞ := ENNReal.ofReal ((16 / θ) ^ (2 * m * a)) with hB
    set G : ℝ≥0∞ := ENNReal.ofReal ((16 / θ) ^ m) with hG
    have hgauss : ∀ s : Fin m → ℤ,
        ∑' x : Fin m → ℤ, ENNReal.ofReal (Real.exp (-θ * l1Length (x - s))) ≤ G := fun s => by
      rw [tsum_ofReal_exp_neg_l1Length_sub]
      exact tsum_ofReal_exp_neg_l1Length_le h0 h1 m
    have hsplit : ∀ (y : IdxPair m) (L : Fin a → IdxPair m),
        ENNReal.ofReal (Real.exp (-θ * pairLength (a + 1) s (Fin.cons y L))) =
          (ENNReal.ofReal (Real.exp (-θ * l1Length (y.1 - s))) *
            ENNReal.ofReal (Real.exp (-θ * l1Length (y.2 - y.1)))) *
            ENNReal.ofReal (Real.exp (-θ * pairLength a y.2 L)) := by
      intro y L
      rw [pairLength_cons, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    calc ∑' L : Fin (a + 1) → IdxPair m,
          ENNReal.ofReal (Real.exp (-θ * pairLength (a + 1) s L))
        = ∑' y : IdxPair m, ∑' L : Fin a → IdxPair m,
            (ENNReal.ofReal (Real.exp (-θ * l1Length (y.1 - s))) *
              ENNReal.ofReal (Real.exp (-θ * l1Length (y.2 - y.1)))) *
              ENNReal.ofReal (Real.exp (-θ * pairLength a y.2 L)) := by
          rw [← (Fin.consEquiv fun _ : Fin (a + 1) => IdxPair m).tsum_eq, ENNReal.tsum_prod']
          exact tsum_congr fun y => tsum_congr fun L => hsplit y L
      _ = ∑' y : IdxPair m,
            (ENNReal.ofReal (Real.exp (-θ * l1Length (y.1 - s))) *
              ENNReal.ofReal (Real.exp (-θ * l1Length (y.2 - y.1)))) *
              ∑' L : Fin a → IdxPair m, ENNReal.ofReal (Real.exp (-θ * pairLength a y.2 L)) :=
          tsum_congr fun y => ENNReal.tsum_mul_left
      _ ≤ ∑' y : IdxPair m,
            (ENNReal.ofReal (Real.exp (-θ * l1Length (y.1 - s))) *
              ENNReal.ofReal (Real.exp (-θ * l1Length (y.2 - y.1)))) * B :=
          ENNReal.tsum_le_tsum fun y =>
            mul_le_mul' le_rfl (tsum_exp_pairLength_le h0 h1 a y.2)
      _ = (∑' x : Fin m → ℤ, ENNReal.ofReal (Real.exp (-θ * l1Length (x - s))) *
            ∑' z : Fin m → ℤ, ENNReal.ofReal (Real.exp (-θ * l1Length (z - x)))) * B := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod']
          refine congrArg (· * B) (tsum_congr fun x => ?_)
          exact ENNReal.tsum_mul_left (a := ENNReal.ofReal (Real.exp (-θ * l1Length (x - s))))
            (f := fun z => ENNReal.ofReal (Real.exp (-θ * l1Length (z - x))))
      _ ≤ (∑' x : Fin m → ℤ, ENNReal.ofReal (Real.exp (-θ * l1Length (x - s))) * G) * B :=
          mul_le_mul' (ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (hgauss x)) le_rfl
      _ ≤ G * G * B := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_mul' (mul_le_mul' (hgauss s) le_rfl) le_rfl
      _ = ENNReal.ofReal ((16 / θ) ^ (2 * m * (a + 1))) := by
          rw [hG, hB, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← pow_add, ← pow_add]
          congr 2
          ring

/-- The number of lists of `a` pairs with total length at most `R`, entered from `0`. -/
noncomputable def pairCount (m a : ℕ) (R : ℝ) : ℝ≥0∞ :=
  ∑' L : Fin a → IdxPair m, if pairLength a 0 L ≤ R then 1 else 0

/-- The lattice points of the `ℓ¹` ball of radius `R`: at most `e^{θR} (16/θ)^{2ma}`. -/
theorem pairCount_le {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) (a : ℕ) (R : ℝ) :
    pairCount m a R ≤ ENNReal.ofReal (Real.exp (θ * R) * (16 / θ) ^ (2 * m * a)) := by
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc pairCount m a R
      ≤ ∑' L : Fin a → IdxPair m, ENNReal.ofReal (Real.exp (θ * R)) *
          ENNReal.ofReal (Real.exp (-θ * pairLength a 0 L)) := by
        refine ENNReal.tsum_le_tsum fun L => ?_
        split_ifs with h
        · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          refine ENNReal.one_le_ofReal.mpr (Real.one_le_exp ?_)
          have := mul_nonneg h0.le (sub_nonneg.2 h)
          linarith only [this]
        · exact zero_le
    _ = ENNReal.ofReal (Real.exp (θ * R)) *
          ∑' L : Fin a → IdxPair m, ENNReal.ofReal (Real.exp (-θ * pairLength a 0 L)) :=
        ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (tsum_exp_pairLength_le h0 h1 a 0)

/-- The choices of `a` indices among `M`: `binom(M, a) ≤ (e M/a)^a`. -/
theorem choose_le_exp_mul_pow (M : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    (M.choose a : ℝ) ≤ (Real.exp 1 * ((M : ℝ) / a)) ^ a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hf : (0 : ℝ) < a.factorial := by exact_mod_cast a.factorial_pos
  have h1 : (M.choose a : ℝ) ≤ (M : ℝ) ^ a / a.factorial := Nat.choose_le_pow_div a M
  have h2 : (a : ℝ) ^ a / a.factorial ≤ Real.exp 1 ^ a := by
    rw [Real.exp_one_pow]
    exact Real.pow_div_factorial_le_exp a ha0.le a
  have hM : (0 : ℝ) ≤ (M : ℝ) ^ a / (a : ℝ) ^ a := by positivity
  calc (M.choose a : ℝ) ≤ (M : ℝ) ^ a / a.factorial := h1
    _ = (a : ℝ) ^ a / a.factorial * ((M : ℝ) ^ a / (a : ℝ) ^ a) := by
        field_simp
    _ ≤ Real.exp 1 ^ a * ((M : ℝ) ^ a / (a : ℝ) ^ a) := mul_le_mul_of_nonneg_right h2 hM
    _ = (Real.exp 1 * ((M : ℝ) / a)) ^ a := by rw [mul_pow, div_pow]

/-- The constant `C` of the count of the sets of triples. -/
noncomputable def tripleCountConst (m : ℕ) : ℝ := Real.exp (1 + Real.sqrt m) * 16 ^ (2 * m)

lemma tripleCountConst_pos (m : ℕ) : 0 < tripleCountConst m := by
  unfold tripleCountConst
  positivity

/-- The real inequality behind `choose_mul_pairCount_le`, in `w = 2^{r/2}` and `q = M/a`. -/
lemma count_real_le {w q : ℝ} (hw : 1 ≤ w) (hq : 1 ≤ q) (a r : ℕ) (hwr : w ^ 2 = 2 ^ r) :
    (Real.exp 1 * q) ^ a * (Real.exp (a * Real.sqrt m) * (16 * w * q) ^ (2 * m * a)) ≤
      (tripleCountConst m * 2 ^ (r * (m + 1)) * q ^ (2 * (m + 1))) ^ a := by
  have hw0 : 0 < w := by linarith only [hw]
  have hq0 : 0 < q := by linarith only [hq]
  have h2 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hbase : Real.exp 1 * q * (Real.exp (Real.sqrt m) * (16 * w * q) ^ (2 * m)) ≤
      tripleCountConst m * 2 ^ (r * (m + 1)) * q ^ (2 * (m + 1)) := by
    have e1 : (16 * w * q) ^ (2 * m) = 16 ^ (2 * m) * (2 ^ r) ^ m * q ^ (2 * m) := by
      rw [mul_pow, mul_pow, pow_mul w, hwr]
    have e2 : Real.exp 1 * q * (Real.exp (Real.sqrt m) * (16 * w * q) ^ (2 * m)) =
        tripleCountConst m * ((2 ^ r) ^ m * q ^ (2 * m + 1)) := by
      rw [e1, tripleCountConst, Real.exp_add, pow_succ q]
      ring
    have e3 : tripleCountConst m * 2 ^ (r * (m + 1)) * q ^ (2 * (m + 1)) =
        tripleCountConst m * ((2 ^ r) ^ (m + 1) * q ^ (2 * (m + 1))) := by
      rw [pow_mul 2 r]
      ring
    rw [e2, e3]
    have hc := tripleCountConst_pos m
    have h3 : ((2 : ℝ) ^ r) ^ m ≤ (2 ^ r) ^ (m + 1) := pow_le_pow_right₀ h2 (by omega)
    have h4 : q ^ (2 * m + 1) ≤ q ^ (2 * (m + 1)) := pow_le_pow_right₀ hq (by omega)
    gcongr
  have hexp : Real.exp (a * Real.sqrt m) = Real.exp (Real.sqrt m) ^ a := by
    rw [← Real.exp_nat_mul]
  have e : (Real.exp 1 * q) ^ a * (Real.exp (a * Real.sqrt m) * (16 * w * q) ^ (2 * m * a)) =
      (Real.exp 1 * q * (Real.exp (Real.sqrt m) * (16 * w * q) ^ (2 * m))) ^ a := by
    rw [hexp, pow_mul (16 * w * q) (2 * m) a, ← mul_pow, ← mul_pow]
  rw [e]
  exact pow_le_pow_left₀ (by positivity) hbase a

/-- **The count of the sets of triples** (proof of Lemma `lem:polynomialarray`): the number of sets
of `a` indices times the number of lists of pairs of total length at most `m^{1/2} 2^{r/2} M` is
at most `[C 2^{rd} (M/a)^{2d}]^a`, `d = m + 1`. -/
theorem choose_mul_pairCount_le {a : ℕ} (ha : 1 ≤ a) (haM : a ≤ M) (r : ℕ) :
    (M.choose a : ℝ≥0∞) * pairCount m a (Real.sqrt m * 2 ^ ((r : ℝ) / 2) * M) ≤
      ENNReal.ofReal
        ((tripleCountConst m * 2 ^ (r * (m + 1)) * ((M : ℝ) / a) ^ (2 * (m + 1))) ^ a) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set w : ℝ := (2 : ℝ) ^ ((r : ℝ) / 2) with hw
  set q : ℝ := (M : ℝ) / a with hq
  have hw1 : 1 ≤ w := Real.one_le_rpow (by norm_num) (by positivity)
  have hw2 : w ^ 2 = 2 ^ r := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (r : ℝ) / 2 * ((2 : ℕ) : ℝ) = r := by push_cast; ring
    rw [this, Real.rpow_natCast]
  have hq1 : 1 ≤ q := (one_le_div ha0).2 (by exact_mod_cast haM)
  have hw0 : 0 < w := by linarith only [hw1]
  have hq0 : 0 < q := by linarith only [hq1]
  have hwq : 1 ≤ w * q := by nlinarith only [hw1, hq1]
  set θ : ℝ := 1 / (w * q) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := (div_le_one (by positivity)).2 hwq
  have hθR : θ * (Real.sqrt m * w * M) = a * Real.sqrt m := by
    have hMq : (M : ℝ) = q * a := by rw [hq]; field_simp
    rw [hθ, hMq]
    field_simp
  have hinv : 16 / θ = 16 * w * q := by
    rw [hθ]
    field_simp
  have hcount := pairCount_le (m := m) hθ0 hθ1 a (Real.sqrt m * w * M)
  rw [hθR, hinv] at hcount
  have hchoose : (M.choose a : ℝ≥0∞) ≤ ENNReal.ofReal ((Real.exp 1 * q) ^ a) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (choose_le_exp_mul_pow M ha)
  calc (M.choose a : ℝ≥0∞) * pairCount m a (Real.sqrt m * w * M)
      ≤ ENNReal.ofReal ((Real.exp 1 * q) ^ a) *
          ENNReal.ofReal (Real.exp (a * Real.sqrt m) * (16 * w * q) ^ (2 * m * a)) :=
        mul_le_mul' hchoose hcount
    _ = ENNReal.ofReal ((Real.exp 1 * q) ^ a *
          (Real.exp (a * Real.sqrt m) * (16 * w * q) ^ (2 * m * a))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (count_real_le hw1 hq1 a r hw2)

end Lists

section Paths

/-- The `ℓ¹` displacement of a path over `[a, b]` against the sum of its increments. -/
lemma l1Length_sub_le_sum (P : ℕ → Fin m → ℤ) {a b : ℕ} (hab : a ≤ b) :
    l1Length (P b - P a) ≤ ∑ j ∈ Finset.Ico a b, l1Length (P (j + 1) - P j) := by
  induction b, hab using Nat.le_induction with
  | base => simp [l1Length]
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    have e : P (b + 1) - P a = (P b - P a) + (P (b + 1) - P b) := by abel
    rw [e]
    exact (l1Length_add_le _ _).trans (add_le_add_left ih _)

/-- The pairs `(k_{i-1}, k_i)` of a path `P` at the indices `e h`. -/
def pairList (P : ℕ → Fin m → ℤ) {a : ℕ} (e : Fin a → Fin M) : Fin a → IdxPair m :=
  fun h => (P (e h), P ((e h : ℕ) + 1))

/-- The total length of the pairs of a path, along strictly increasing indices at least `q`, is at
most the sum of the `ℓ¹` lengths of its increments after `q`: in the proof of
Lemma `lem:polynomialarray`, the total length is at most `∑_i |k_i - k_{i-1}|`. -/
theorem pairLength_pairList_le (P : ℕ → Fin m → ℤ) :
    ∀ (a q : ℕ) (e : Fin a → Fin M), StrictMono e → (∀ h, q ≤ (e h : ℕ)) →
      pairLength a (P q) (pairList P e) ≤ ∑ j ∈ Finset.Ico q M, l1Length (P (j + 1) - P j)
  | 0, _, _, _, _ => by
    simp only [pairLength]
    exact Finset.sum_nonneg fun j _ => l1Length_nonneg _
  | a + 1, q, e, he, hq => by
    have IH := pairLength_pairList_le P a ((e 0 : ℕ) + 1) (e ∘ Fin.succ)
      (he.comp Fin.strictMono_succ) fun h => Fin.lt_def.mp (he (Fin.succ_pos h))
    set i₀ : ℕ := (e 0 : ℕ) with hi₀
    have hq0 : q ≤ i₀ := hq 0
    have hi₀M : i₀ < M := (e 0).isLt
    set f : ℕ → ℝ := fun j => l1Length (P (j + 1) - P j) with hf
    have hsplit : ∑ j ∈ Finset.Ico q M, f j =
        ∑ j ∈ Finset.Ico q i₀, f j + (f i₀ + ∑ j ∈ Finset.Ico (i₀ + 1) M, f j) := by
      rw [← Finset.sum_Ico_consecutive f hq0 hi₀M.le, Finset.sum_eq_sum_Ico_succ_bot hi₀M]
    have hgap := l1Length_sub_le_sum P hq0
    change l1Length (P i₀ - P q) + l1Length (P (i₀ + 1) - P i₀) +
        pairLength a (P (i₀ + 1)) (pairList P (e ∘ Fin.succ)) ≤ ∑ j ∈ Finset.Ico q M, f j
    rw [hsplit]
    linarith only [hgap, IH]

/-- Cauchy–Schwarz on the increments: `(∑_i |k_i - k_{i-1}|₁)² ≤ m M ∑_i |k_i - k_{i-1}|²`, the
step `∑_i |k_i - k_{i-1}| ≤ 2^{r/2} M` of the proof of Lemma `lem:polynomialarray` (with the factor
`m^{1/2}` of the norm `ℓ¹`). -/
theorem sq_sum_l1Length_le (P : ℕ → Fin m → ℤ) (M : ℕ) :
    (∑ j ∈ Finset.Ico 0 M, l1Length (P (j + 1) - P j)) ^ 2 ≤
      m * M * ∑ j ∈ Finset.Ico 0 M, (sqNorm (P (j + 1) - P j) : ℝ) := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.Ico 0 M)
    (f := fun j => l1Length (P (j + 1) - P j))
  rw [Nat.card_Ico, Nat.sub_zero] at h
  calc _ ≤ (M : ℝ) * ∑ j ∈ Finset.Ico 0 M, l1Length (P (j + 1) - P j) ^ 2 := h
    _ ≤ (M : ℝ) * ∑ j ∈ Finset.Ico 0 M, (m * (sqNorm (P (j + 1) - P j) : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => l1Length_sq_le _)
          (Nat.cast_nonneg M)
    _ = _ := by rw [← Finset.mul_sum]; ring

end Paths

end IsotropicVariance.Infra.Arrays
