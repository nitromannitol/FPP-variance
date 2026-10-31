/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Space.TransversePoint
public import Mathlib.Probability.Independence.Basic

/-!
# Contract: penalized sums over independent arrays, [AB26, Lemma 2.4]

* `ArraysStatement` — [AB26, Lemma 2.4], with `C(d)` before the number `M` of arrays and the
  probability space. The lattice paper cites it in equation `eq:chainsum` and in the proof of
  Lemma `lem:smallmean`. It is a result of the companion paper, not of the literature, so this
  library proves it (`Proofs.Arrays.arraysStatement_holds`), by the proof of the continuum
  library.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CurvatureVariance.Paper.Contracts

universe u

/-- **[AB26, Lemma 2.4]** (cited before equation `eq:chainsum` and in the proof of Lemma
`lem:smallmean`), with `d = m + 1`: there is `C(d)` such that, for every integer `M ≥ 1` and all
independent arrays `Z_1, …, Z_M` of nonnegative random variables `Z_i(j,k)`, `j, k ∈ ℤ^{d−1}`, with
`E[Z_i(j,k)^{4d}] ≤ 1`,
`E[sup_{k₀ = 0, k₁, …, k_M} {∑ᵢ Z_i(k_{i−1}, k_i) − ∑ᵢ |k_i − k_{i−1}|²}] ≤ C(d) M`.

Readings. The supremum is over all sequences with `k₀ = 0`. Its positive part is the supremum
itself, since the constant sequence `0` gives a nonnegative value, so the expectation is an integral
in `[0, ∞]`, and no finiteness of the supremum is assumed. That the entries are random variables is
the hypothesis of measurability. The moment hypothesis is an integral in `[0, ∞]`: it contains the
integrability in the paper's `E[Z_i(j,k)^{4d}] ≤ 1`. The model of this statement is the continuum
library's `IsotropicVariance.Paper.Contracts.PenalizedArraysStatement`. -/
def ArraysStatement (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin M → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ),
    (∀ i j k, Measurable fun ω => Z i ω j k) → (∀ i ω j k, 0 ≤ Z i ω j k) → iIndepFun Z P →
    (∀ i j k, ∫⁻ ω, ENNReal.ofReal (Z i ω j k ^ (4 * (m + 1))) ∂P ≤ 1) →
    ∫⁻ ω, ⨆ (k : Fin (M + 1) → Fin m → ℤ) (_ : k 0 = 0),
        ENNReal.ofReal ((∑ i : Fin M, Z i ω (k i.castSucc) (k i.succ)) -
          ∑ i : Fin M, ‖transversePoint (k i.succ - k i.castSucc)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (C * M)

end CurvatureVariance.Paper.Contracts
