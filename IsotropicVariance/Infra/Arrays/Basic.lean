/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Penalized sums of independent arrays: definitions

The objects of the bound behind Lemma `lem:polynomialarray`. For a starting index `k₀ ∈ ℤ^m` and
free indices `k : Fin M → ℤ^m` (the paper's `k_1, …, k_M`), the lattice path visits `k₀` at time `0`
and `k j` at time `j + 1`. Its energy is `E(k) = ∑_{i=1}^M |k_i - k_{i-1}|²` (Euclidean). Columns
are indexed by `Fin M`, so the paper's array `Z_i` is `Z (i - 1)`.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace IsotropicVariance.Infra.Arrays

variable {Ω : Type*} {m M : ℕ}

/-- The squared Euclidean norm `|x|² = ∑_j x_j²` of a lattice vector. -/
def sqNorm (x : Fin m → ℤ) : ℤ := ∑ j, x j ^ 2

lemma sqNorm_nonneg (x : Fin m → ℤ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun j _ => sq_nonneg (x j)

/-- The lattice path through the starting index `k₀` and the free indices `k`: time `0` is
`k₀`, time `j + 1 ≤ M` is `k j`; times after `M` are set to `k₀` and never used. -/
def pathPt (k₀ : Fin m → ℤ) (k : Fin M → Fin m → ℤ) : ℕ → Fin m → ℤ
  | 0 => k₀
  | j + 1 => if h : j < M then k ⟨j, h⟩ else k₀

@[simp] lemma pathPt_zero (k₀ : Fin m → ℤ) (k : Fin M → Fin m → ℤ) : pathPt k₀ k 0 = k₀ := rfl

lemma pathPt_succ (k₀ : Fin m → ℤ) (k : Fin M → Fin m → ℤ) (i : Fin M) :
    pathPt k₀ k ((i : ℕ) + 1) = k i := by
  simp [pathPt]

/-- The energy `E(k) = ∑_{i=1}^M |k_i - k_{i-1}|²` of the path through `k₀` and `k`. -/
def energy (k₀ : Fin m → ℤ) (k : Fin M → Fin m → ℤ) : ℝ :=
  ∑ i : Fin M, (sqNorm (pathPt k₀ k ((i : ℕ) + 1) - pathPt k₀ k (i : ℕ)) : ℝ)

lemma energy_nonneg (k₀ : Fin m → ℤ) (k : Fin M → Fin m → ℤ) : 0 ≤ energy k₀ k :=
  Finset.sum_nonneg fun _ _ => by exact_mod_cast sqNorm_nonneg _

/-- The energy as a sum over times `j < M`. -/
lemma energy_eq_sum_range (k₀ : Fin m → ℤ) (k : Fin M → Fin m → ℤ) :
    energy k₀ k = ∑ j ∈ Finset.range M, (sqNorm (pathPt k₀ k (j + 1) - pathPt k₀ k j) : ℝ) :=
  Fin.sum_univ_eq_sum_range (fun j => (sqNorm (pathPt k₀ k (j + 1) - pathPt k₀ k j) : ℝ)) M

end IsotropicVariance.Infra.Arrays
