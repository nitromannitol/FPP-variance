/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Lattice.PassageTime
public import CurvatureVariance.Infra.Kesten.Estimate
import CurvatureVariance.Statements.Inputs.MeasureExistsIsPathWalkCostLtLe
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import CurvatureVariance.Infra.FPP.Walks

/-!
# Geodesics exist almost surely

Under independent weights with law `F` (zero weights allowed), Kesten's estimate
[ADH, Proposition 4.4] — a self-avoiding path from the origin with at least `n` edges costs at
least `a n`, except on an event of probability at most `e^{-C₉ n}` — implies that almost surely
every passage time `T(u, v)` is attained by a self-avoiding path
(`ae_exists_isPath_walkCost_eq_passageTime_of_kesten`). Kesten's estimate enters as the
hypothesis `hK`, with exactly the conclusion of the statement
`measure_exists_isPath_walkCost_lt_le`.

* `walkCost_bypass_le`: loop erasure does not increase the cost (by
  `Kesten.walkCost_le_of_darts_sublist`).
* `mapWeights g`: the weights transported by a lattice automorphism; it preserves the product law
  (`measurePreserving_mapWeights`) and the costs of transported walks
  (`walkCost_map_mapWeights`), so the cheap-path event at `u` is no more likely than at the origin
  (`measure_exists_isPath_le_of_isIIDWeights`).
* `ae_eventually_le_walkCost_of_kesten`: Borel–Cantelli; almost surely, from every vertex,
  eventually in `n` every self-avoiding path with at least `n` edges costs at least `a n`.
* `exists_isPath_walkCost_eq_passageTime`: deterministically, under this conclusion the infimum
  defining `T(u, v)` is attained among the finitely many short self-avoiding paths.
* `ae_exists_isPath_walkCost_eq_passageTime`: **[ADH, Proposition 4.4]** in the combined form of
  its parts 1 and 2, from Kesten's estimate `Kesten.measure_exists_isPath_walkCost_lt_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter SimpleGraph
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.Geodesics

open CurvatureVariance.Infra.Percolation CurvatureVariance.Infra.Kesten

variable {m : ℕ}

/-! ### Costs of walks -/

/-- **Loop erasure does not increase cost** (zero weights allowed). -/
theorem walkCost_bypass_le [DecidableEq (Vertex m)] (ω : Config m) {u v : Vertex m}
    (p : (latticeGraph m).Walk u v) : walkCost ω p.bypass ≤ walkCost ω p :=
  Kesten.walkCost_le_of_darts_sublist ω _ _ p.darts_bypass_sublist_darts

/-- Changing the endpoint proofs of a walk does not change its cost. -/
@[simp] theorem walkCost_copy (ω : Config m) {u v u' v' : Vertex m}
    (p : (latticeGraph m).Walk u v) (hu : u = u') (hv : v = v') :
    walkCost ω (p.copy hu hv) = walkCost ω p := by
  subst hu hv
  rfl

/-! ### Transport of weights by automorphisms -/

/-- The weights transported by an automorphism `g` of the lattice: the edge `g e` carries the
weight of `e`. -/
def mapWeights (g : latticeGraph m ≃g latticeGraph m) (ω : Config m) : Config m :=
  fun e => ω (g.symm.mapEdgeSet e)

/-- Transport of weights is the reindexing of coordinates by the edge map of `g`. -/
theorem mapWeights_eq_piCongrLeft (g : latticeGraph m ≃g latticeGraph m) :
    (mapWeights g : Config m → Config m) =
      MeasurableEquiv.piCongrLeft (fun _ : Edge m => ℝ≥0) g.mapEdgeSet := by
  funext ω e
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp only [mapWeights, cast_eq]
  rfl

/-- **Automorphisms preserve the law of independent weights.** -/
theorem measurePreserving_mapWeights (g : latticeGraph m ≃g latticeGraph m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] :
    MeasurePreserving (mapWeights g) (Measure.infinitePi fun _ : Edge m => F)
      (Measure.infinitePi fun _ : Edge m => F) := by
  rw [mapWeights_eq_piCongrLeft]
  exact ⟨MeasurableEquiv.measurable _,
    Measure.infinitePi_map_piCongrLeft (μ := fun _ : Edge m => F) g.mapEdgeSet⟩

/-- Transporting a walk and the weights by the same automorphism does not change the cost. -/
theorem walkCost_map_mapWeights (g : latticeGraph m ≃g latticeGraph m) (ω : Config m)
    {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    walkCost (mapWeights g ω) (p.map g.toHom) = walkCost ω p := by
  unfold walkCost
  rw [Walk.darts_map, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  exact congrArg ω (symm_mapEdgeSet_map g ⟨t.edge, t.edge_mem⟩)

/-- **Translation invariance of cheap paths**: under independent weights, the probability that
some self-avoiding path from `u` with at least `n` edges costs less than `c` is at most the same
probability at the origin (outer measures; no measurability is needed). -/
theorem measure_exists_isPath_le_of_isIIDWeights {P : Measure (Config m)}
    [IsProbabilityMeasure P] {F : Measure ℝ≥0} [IsProbabilityMeasure F] (hP : IsIIDWeights P F)
    (u : Vertex m) (n : ℕ) (c : ℝ) :
    P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk u v),
        γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < c} ≤
      P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v),
        γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < c} := by
  set g := Percolation.latticeShift (m := m) (-u)
  have hmp := measurePreserving_mapWeights g F
  rw [← eq_infinitePi_of_isIIDWeights hP] at hmp
  refine le_trans (measure_mono fun ω hω => ?_)
    ((Measure.le_map_apply hmp.measurable.aemeasurable _).trans_eq (by rw [hmp.map_eq]))
  obtain ⟨v, γ, hγ, hn, hc⟩ := hω
  have hu : g.toHom u = 0 := add_neg_cancel u
  refine ⟨g.toHom v, (γ.map g.toHom).copy hu rfl, ?_, ?_, ?_⟩
  · exact (Walk.isPath_copy _ _ _).2 (hγ.map g.injective)
  · simpa using hn
  · rwa [walkCost_copy, walkCost_map_mapWeights]

/-! ### Borel–Cantelli -/

/-- **No long cheap paths, almost surely**: under Kesten's estimate `hK` with `C₉ > 0`, almost
surely, from every vertex `u`, eventually in `n` every self-avoiding path from `u` with at least
`n` edges costs at least `a n`. -/
theorem ae_eventually_le_walkCost_of_kesten {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {a C₉ : ℝ} (hC₉ : 0 < C₉)
    (hK : ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
      ∀ n : ℕ, 1 ≤ n →
        P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v),
            γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < a * n} ≤
          ENNReal.ofReal (Real.exp (-(C₉ * n))))
    (P : Measure (Config m)) [IsProbabilityMeasure P] (hP : IsIIDWeights P F) :
    ∀ᵐ ω ∂P, ∀ u : Vertex m, ∀ᶠ n in atTop, ∀ (v : Vertex m) (γ : (latticeGraph m).Walk u v),
      γ.IsPath → n ≤ γ.length → a * n ≤ walkCost ω γ := by
  rw [ae_all_iff]
  intro u
  set s : ℕ → Set (Config m) := fun n => {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk u v),
    γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < a * n}
  have hle : ∀ n : ℕ, P (s n) ≤ ENNReal.ofReal (Real.exp (-(C₉ * n))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using prob_le_one
    · exact (measure_exists_isPath_le_of_isIIDWeights hP u n _).trans (hK P hP n hn)
  have hsum : ∑' n, P (s n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    have hexp : (fun n : ℕ => Real.exp (-(C₉ * n))) = fun n => Real.exp (-C₉) ^ n := by
      funext n
      rw [← Real.exp_nat_mul]
      ring_nf
    have hs : Summable fun n : ℕ => Real.exp (-(C₉ * n)) := by
      rw [hexp]
      exact summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by linarith))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn v γ hγ hl
  by_contra hlt
  exact hn ⟨v, γ, hγ, hl, not_le.1 hlt⟩

/-! ### Existence of geodesics -/

/-- **Existence of geodesics, deterministically**: if, from `u`, eventually in `n` every
self-avoiding path with at least `n` edges costs at least `a n` (`a > 0`), then for every `v`
the passage time `T(u, v)` is attained by a self-avoiding path. -/
theorem exists_isPath_walkCost_eq_passageTime {ω : Config m} {a : ℝ} (ha : 0 < a)
    {u : Vertex m}
    (hω : ∀ᶠ n in atTop, ∀ (v : Vertex m) (γ : (latticeGraph m).Walk u v),
      γ.IsPath → n ≤ γ.length → a * n ≤ walkCost ω γ) (v : Vertex m) :
    ∃ γ : (latticeGraph m).Walk u v, γ.IsPath ∧ walkCost ω γ = passageTime ω u v := by
  classical
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hω
  obtain ⟨q⟩ := (latticeGraph_connected m).preconnected u v
  set n : ℕ := max n₀ (⌈(walkCost ω q : ℝ) / a⌉₊ + 1)
  have hqn : (walkCost ω q : ℝ) < a * n := by
    have h1 : (walkCost ω q : ℝ) / a < n :=
      calc (walkCost ω q : ℝ) / a ≤ ⌈(walkCost ω q : ℝ) / a⌉₊ := Nat.le_ceil _
        _ < ⌈(walkCost ω q : ℝ) / a⌉₊ + 1 := lt_add_one _
        _ ≤ n := by exact_mod_cast le_max_right _ _
    rwa [div_lt_iff₀ ha, mul_comm] at h1
  have hlong := hn₀ n (le_max_left _ _) v
  -- the finite set of candidates: the self-avoiding paths with fewer than `n` edges
  set S := ((latticeGraph m).finsetWalkLengthLT n u v).filter (·.IsPath)
  have hred : ∀ r : (latticeGraph m).Walk u v,
      r.bypass ∈ S ∨ (walkCost ω q : ℝ) < walkCost ω r := by
    intro r
    by_cases hl : r.bypass.length < n
    · exact Or.inl (Finset.mem_filter.2
        ⟨(mem_finsetWalkLengthLT_iff).2 hl, r.bypass_isPath⟩)
    · refine Or.inr (hqn.trans_le ((hlong _ r.bypass_isPath (not_lt.1 hl)).trans ?_))
      exact_mod_cast walkCost_bypass_le ω r
  have hqS : q.bypass ∈ S := (hred q).resolve_right (lt_irrefl _)
  obtain ⟨p, hpS, hmin⟩ := S.exists_min_image (fun r => walkCost ω r) ⟨_, hqS⟩
  have hp : ∀ r : (latticeGraph m).Walk u v, walkCost ω p ≤ walkCost ω r := by
    intro r
    rcases hred r with h | h
    · exact (hmin _ h).trans (walkCost_bypass_le ω r)
    · refine ((hmin _ hqS).trans (walkCost_bypass_le ω q)).trans ?_
      exact_mod_cast h.le
  have : Nonempty ((latticeGraph m).Walk u v) := ⟨q⟩
  exact ⟨p, (Finset.mem_filter.1 hpS).2,
    le_antisymm (le_ciInf hp) (FPP.passageTime_le_walkCost ω p)⟩

/-- **Geodesics exist almost surely**: under independent weights with law `F` (zero weights
allowed), Kesten's estimate `hK` (the conclusion of `measure_exists_isPath_walkCost_lt_le`)
implies that almost surely, for all vertices `u` and `v`, the passage time `T(u, v)` is the cost
of a self-avoiding path from `u` to `v`. -/
theorem ae_exists_isPath_walkCost_eq_passageTime_of_kesten {m : ℕ} {F : Measure ℝ≥0}
    [IsProbabilityMeasure F] {a C₉ : ℝ} (ha : 0 < a) (hC₉ : 0 < C₉)
    (hK : ∀ (P : Measure (Config m)) [IsProbabilityMeasure P], IsIIDWeights P F →
      ∀ n : ℕ, 1 ≤ n →
        P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v),
            γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < a * n} ≤
          ENNReal.ofReal (Real.exp (-(C₉ * n))))
    (P : Measure (Config m)) [IsProbabilityMeasure P] (hP : IsIIDWeights P F) :
    ∀ᵐ ω ∂P, ∀ u v : Vertex m, ∃ γ : (latticeGraph m).Walk u v,
      γ.IsPath ∧ walkCost ω γ = passageTime ω u v := by
  filter_upwards [ae_eventually_le_walkCost_of_kesten hC₉ hK P hP] with ω hω u v
  exact exists_isPath_walkCost_eq_passageTime ha (hω u) v

/-- **[ADH, Proposition 4.4]** (cited in Section `sec:prelim`), in the combined form of parts 1
and 2: if `F(0) < p_c`, then almost surely, for all `u, v ∈ ℤ^d`, a geodesic from `u` to `v`
exists, a simple path whose passage time is `T(u, v)` (the definition of a geodesic at the
beginning of Section `sec:prelim`). Zero weights are allowed. Exactly the statement
`CurvatureVariance.ae_exists_isPath_walkCost_eq_passageTime`. -/
theorem ae_exists_isPath_walkCost_eq_passageTime {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (h0 : F {0} < ENNReal.ofReal (bondCriticalProb m))
    (P : Measure (Config m)) [IsProbabilityMeasure P] (hP : IsIIDWeights P F) :
    ∀ᵐ ω ∂P, ∀ u v : Vertex m, ∃ γ : (latticeGraph m).Walk u v,
      γ.IsPath ∧ walkCost ω γ = passageTime ω u v := by
  obtain ⟨a, C₉, ha, hC₉, hK⟩ := CurvatureVariance.measure_exists_isPath_walkCost_lt_le hm F h0
  exact ae_exists_isPath_walkCost_eq_passageTime_of_kesten ha hC₉ hK P hP

end CurvatureVariance.Infra.Geodesics
