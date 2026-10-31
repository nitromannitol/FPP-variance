/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.Model
public import CurvatureVariance.Infra.Percolation.Lattice

/-!
# Kesten's estimate as a hypothesis, and cheap paths from every vertex

Kesten's estimate, in the form of [ADH, Theorem 4.6, in its proof, p. 77], is
`CurvatureVariance.Infra.Kesten.measure_exists_isPath_walkCost_lt_le`. The theorems of this folder
take its conclusion as the hypothesis `KestenEstimate m F`, whose body is verbatim the conclusion
of that statement; `kestenEstimate` (`CurvatureVariance.Infra.FPP.Statements`) discharges it from
`F(0) < p_c`.

From it, by translation invariance, the cheap-path estimate holds from every vertex
(`CheapPaths`): some self-avoiding path of `k` edges from `u` costs at most `a k` with probability
at most `e^{-ck}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- **Kesten's estimate**, the conclusion of the statement `measure_exists_isPath_walkCost_lt_le`
([Kes86, Proposition 5.8], whose full reference is in `CurvatureVariance.Infra.Kesten.Estimate`,
in the form of [ADH, Theorem 4.6, in its proof, p. 77]): there are `a, C₉ > 0` such that for
every law `P` of independent weights with law `F` and all `n ≥ 1`, `P(∃` a self-avoiding path from
`0` with at least `n` edges and passage time below `a n) ≤ e^{−C₉ n}`. A hypothesis of the theorems
of this folder; `kestenEstimate` discharges it. -/
def KestenEstimate (m : ℕ) (F : Measure ℝ≥0) : Prop :=
  ∃ a C₉ : ℝ, 0 < a ∧ 0 < C₉ ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
    IsIIDWeights P F → ∀ n : ℕ, 1 ≤ n →
      P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v),
          γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < a * n} ≤
        ENNReal.ofReal (Real.exp (-(C₉ * n)))

/-- **The cheap-path estimate** at rate `a` with decay `c`: some self-avoiding path of length `k`
from `u` costs at most `a k` with probability at most `e^{-ck}`. -/
def CheapPaths (P : Measure (Config m)) (a c : ℝ) : Prop :=
  ∀ (u : Vertex m) (k : ℕ),
    P {ω | ∃ (v : Vertex m) (p : (latticeGraph m).Walk u v), p.IsPath ∧ p.length = k ∧
      (walkCost ω p : ℝ) ≤ a * k} ≤ ENNReal.ofReal (Real.exp (-(c * k)))

/-! ### Events of paths from a vertex -/

/-- The event that some self-avoiding path from `b` has a length and a cost satisfying `Q`. -/
def pathEvent (b : Vertex m) (Q : ℕ → ℝ → Prop) : Set (Config m) :=
  {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk b v), γ.IsPath ∧ Q γ.length (walkCost ω γ)}

/-- A path from `b` in the translated configuration `θ_a ω` is a path from `b + a` in `ω`. -/
theorem preimage_translate_pathEvent_subset (a b : Vertex m) (Q : ℕ → ℝ → Prop) :
    translate a ⁻¹' pathEvent b Q ⊆ pathEvent (b + a) Q := by
  rintro ω ⟨v, γ, hγ, hQ⟩
  refine ⟨v + a, γ.map (Percolation.latticeShift a).toHom,
    hγ.map (f := (Percolation.latticeShift a).toHom) (Percolation.latticeShift a).injective, ?_⟩
  convert hQ using 2
  · exact SimpleGraph.Walk.length_map _ _
  · exact walkCost_map_latticeShift a ω γ

/-- Path events are measurable when `Q` is measurable in the cost. -/
theorem measurableSet_pathEvent (b : Vertex m) {Q : ℕ → ℝ → Prop}
    (hQ : ∀ k, MeasurableSet {x : ℝ | Q k x}) : MeasurableSet (pathEvent b Q) := by
  classical
  have : pathEvent b Q = ⋃ v : Vertex m, ⋃ γ : (latticeGraph m).Walk b v,
      {ω | γ.IsPath ∧ Q γ.length (walkCost ω γ)} := by
    ext ω; simp [pathEvent]
  rw [this]
  refine MeasurableSet.iUnion fun v => MeasurableSet.iUnion fun γ => ?_
  by_cases hγ : γ.IsPath
  · simpa [hγ] using (measurable_walkCost_real γ) (hQ γ.length)
  · simp [hγ]

/-- Under a translation-invariant law, path events from any vertex have the probability of those
from the origin. -/
theorem measure_pathEvent_le {P : Measure (Config m)}
    (hP : ∀ a : Vertex m, MeasurePreserving (translate a) P P) (u : Vertex m)
    {Q : ℕ → ℝ → Prop} (hQ : ∀ k, MeasurableSet {x : ℝ | Q k x}) :
    P (pathEvent u Q) ≤ P (pathEvent 0 Q) := by
  rw [← (hP (-u)).measure_preimage (measurableSet_pathEvent u hQ).nullMeasurableSet]
  refine measure_mono ((preimage_translate_pathEvent_subset (-u) u Q).trans ?_)
  rw [add_neg_cancel]

/-- **Cheap paths from Kesten's estimate**: with `a` the rate of Kesten's estimate, paths of `k`
edges from any vertex cost at most `(a/2) k` with probability at most `e^{-C₉ k}`. -/
theorem KestenEstimate.exists_cheapPaths {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    (hK : KestenEstimate m F) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → CheapPaths P a c := by
  obtain ⟨a, C₉, ha, hC, h⟩ := hK
  refine ⟨a / 2, C₉, half_pos ha, hC, fun P _ hP u k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using prob_le_one
  have hsub : {ω | ∃ (v : Vertex m) (p : (latticeGraph m).Walk u v), p.IsPath ∧ p.length = k ∧
      (walkCost ω p : ℝ) ≤ a / 2 * k} ⊆
        pathEvent u fun l x => k ≤ l ∧ x < a * k := by
    rintro ω ⟨v, p, hp, hl, hc⟩
    refine ⟨v, p, hp, hl.ge, hc.trans_lt ?_⟩
    have : (0 : ℝ) < k := by exact_mod_cast hk
    nlinarith
  have hQ : ∀ l, MeasurableSet {x : ℝ | k ≤ l ∧ x < a * k} := fun l => by
    by_cases hl : k ≤ l
    · have : {x : ℝ | k ≤ l ∧ x < a * k} = Iio (a * k) := by ext x; simp [hl]
      rw [this]; exact measurableSet_Iio
    · simp [hl]
  refine (measure_mono hsub).trans ((measure_pathEvent_le
    (IsIIDWeights.measurePreserving_translate hP) u hQ).trans ?_)
  exact h P hP k hk

end CurvatureVariance.Infra.FPP
