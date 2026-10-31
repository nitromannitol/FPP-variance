/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Targets

/-!
# Contracts of Section `sec:mean` and of the induction step

The statements of Sections `sec:mean` and `sec:induction` of the lattice paper. Variances are
extended variances (`evariance`), so that no junk value enters a hypothesis or a bound. The domains
`𝒟(s)` and the condition on `y₀` are centred at `s t₀`, with `t₀` the slope of the direction.

* `SmallMeanStatement` — Lemma `lem:smallmean`.
* `ClassicalRangeStatement` — the case `Q_N ≥ 2C(N log(2+N))^{1/2}` of the induction step (the text
  before equation `eq:regime`).
* `ImprovementStatement` — Proposition `prop:induction`, as stated in the paper.
* `ImprovementAllKStatement` — the same for every large `K`, an internal statement that says why it
  exists in its docstring.

Every statement is uniform in the direction: its constants and thresholds come after a `Bounds`
record and before the models that fit it (`Model.Fits`), so they depend only on the law and the
bounds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper

/-- **Lemma `lem:smallmean`**: if `N` is large, depending only on `K`, then, for every integer
`s ∈ [N/8, N/4]` such that `sup_{y ∈ 𝒟(s)} Var[T(0,(s,y))/Q_s]` is at most `c`, and every
`y₀ ∈ ℤ^{d−1}` with `|y₀ − st₀| ≤ s N^{δ/100−1/4}`, `E[T(0,(s,y₀))] − μ(s,y₀) ≤ Q_s/100`.

Readings. `c` comes before `K`, as the convention of Section `ssec:notation` asks. The supremum is
at most `c` if and only if every term is. The standing hypotheses `eq:premise` and `eq:regime` of
Section `sec:induction` are explicit. -/
def SmallMeanStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ c : ℝ, 0 < c ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ s : ℕ, (N : ℝ) / 8 ≤ s → (s : ℝ) ≤ N / 4 →
    (∀ y ∈ premiseDomain M s,
      evariance (fun ω => passageTimeReal ω 0 ((s : ℤ), y) / Q M K A s) M.P ≤
        ENNReal.ofReal c) →
    ∀ y₀ : Fin m → ℤ, ‖transversePoint y₀ - (s : ℝ) • M.t₀‖ ≤ s * (N : ℝ) ^ (M.δ / 100 - 1 / 4) →
      (∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀) ∂M.P) - M.μ.1 (point ((s : ℤ), y₀)) ≤
        Q M K A s / 100

/-- **The classical range** (the text before equation `eq:regime`): there is `C_*` such that, for
every `K ≥ 10⁴`, for `N` large, every `A ≥ 1` with `Q_N ≥ C_* (N log(2+N))^{1/2}` (the complement of
equation `eq:regime`) and every `y ∈ 𝒟(N)`: `|T(0,(N,y)) − μ(N,y)| ≤ O₁(Q_N/2)`, by equation
`eq:classical`. This is equation `eq:improvement` in that case, the reason why the rest of the paper
may assume equation `eq:regime`. -/
def ClassicalRangeStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ Cstar : ℝ, 0 < Cstar ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  ¬ RangeA M K A N Cstar → ∀ y ∈ premiseDomain M N,
    IsAbsOs M.P 1 (Q M K A N / 2)
      (fun ω => passageTimeReal ω 0 ((N : ℤ), y) - M.μ.1 (point ((N : ℤ), y)))

/-- **Proposition `prop:induction`**: there are an integer `K ≥ 10⁴` and `N₁` such that equation
`eq:premise` implies equation `eq:improvement` for every `A ≥ 1` and every integer `N ≥ N₁`.

Readings. The paper's `N₀ ≥ 2` is `N₁`: `max N₁ 2` serves. Equation `eq:regime` is not a hypothesis:
the classical range is covered (`ClassicalRangeStatement`). -/
def ImprovementStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ K : ℕ, 10 ^ 4 ≤ K ∧ ∃ N₁ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₁ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → ∀ y ∈ premiseDomain M N,
    IsAbsOs M.P 1 (Q M K A N / 2)
      (fun ω => passageTimeReal ω 0 ((N : ℤ), y) - M.μ.1 (point ((N : ℤ), y)))

/-- **Proposition `prop:induction` for every large `K`**: there is `K₀` such that, for every
`K ≥ K₀` with `K ≥ 10⁴`, there is `N₁` such that equation `eq:premise` implies equation
`eq:improvement` for every `A ≥ 1` and every integer `N ≥ N₁`.

This statement is internal, and it is not in the paper. It exists because of the Lean's `Bounds`
record. The paper chooses one `K` depending on `d`, `ν` and the constants of (Curv), since
permutations and sign changes of the coordinates preserve the law (the start of Section
`sec:prelim`). A `Bounds` record contains the law of a model, with its time constant, and the chosen
coordinates give `2d` laws, one for each coordinate and sign (`ReductionUniformStatement`). So the
paper's one `K` is a common `K` for `2d` records. The paper's form gives one `K` for each record,
and this form gives a common `K` at once. It is a convenience, not a new fact: the paper's proof
fixes `K` by `ω_K` being small, which holds for all `K` large, and a common `K` can also be had
after the induction, since `Q_s` increases with `K` for `s ≥ 1`. `improvementStatement_of_allK`
gives the paper's form. -/
def ImprovementAllKStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → 10 ^ 4 ≤ K → ∃ N₁ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₁ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → ∀ y ∈ premiseDomain M N,
    IsAbsOs M.P 1 (Q M K A N / 2)
      (fun ω => passageTimeReal ω 0 ((N : ℤ), y) - M.μ.1 (point ((N : ℤ), y)))

/-- The internal form gives Proposition `prop:induction`, at `K = max K₀ 10⁴`. -/
theorem improvementStatement_of_allK {m : ℕ} (h : ImprovementAllKStatement m) :
    ImprovementStatement m := by
  intro bd hbd
  obtain ⟨K₀, hK⟩ := h bd hbd
  have hK₁ : K₀ ≤ max K₀ (10 ^ 4) := le_max_left _ _
  have hK₂ : 10 ^ 4 ≤ max K₀ (10 ^ 4) := le_max_right _ _
  exact ⟨max K₀ (10 ^ 4), hK₂, hK _ hK₁ hK₂⟩

end CurvatureVariance.Paper.Contracts
