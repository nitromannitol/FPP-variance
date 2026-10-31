/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.MinCost
public import CurvatureVariance.Infra.FPP.CheapPaths

/-!
# The restricted passage time

The restricted passage time `T_R` of `u` and `v` is the minimum `minCost (pathFamily u v R)` of the
costs of the self-avoiding paths from `u` to `v` with at most `R` edges, as the sum of the weights
over the edge set of the path. It dominates the passage time `T`, and equals it outside the event
that either a coordinate path from `u` to `v` costs more than `a R`, or some self-avoiding path from
`u` with more than `R` edges is `a`-cheap. With the cheap-path estimate `CheapPaths P a c` and the
Chernoff bound for the coordinate path, that event has probability at most
`e^{-c(R+1)}/(1 - e^{-c}) + e^{-θ a R} M(θ)^{|v - u|₁}`, `M(θ) = E e^{θ τ}`, for a general law
of the weights.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The edges of a walk, as a finset of lattice edges. -/
noncomputable def walkEdgeFinset {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    Finset (Edge m) :=
  (p.darts.map fun d => (⟨d.edge, d.edge_mem⟩ : Edge m)).toFinset

theorem card_walkEdgeFinset_le {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    (walkEdgeFinset p).card ≤ p.length := by
  unfold walkEdgeFinset
  refine (List.toFinset_card_le _).trans ?_
  simp

/-- The cost of a self-avoiding path is the sum of the weights of its edge set. -/
theorem walkCost_eq_sum_walkEdgeFinset (ω : Config m) {u v : Vertex m}
    (p : (latticeGraph m).Walk u v) (hp : p.IsPath) :
    (walkCost ω p : ℝ) = ∑ e ∈ walkEdgeFinset p, (ω e : ℝ) := by
  have hnd : (p.darts.map fun d => (⟨d.edge, d.edge_mem⟩ : Edge m)).Nodup := by
    refine List.Nodup.of_map Subtype.val ?_
    have := hp.isTrail.edges_nodup
    simpa [SimpleGraph.Walk.edges, Function.comp_def] using this
  unfold walkEdgeFinset
  rw [List.sum_toFinset _ hnd]
  unfold walkCost
  rw [NNReal.coe_list_sum]
  simp [Function.comp_def]

/-- The edge sets of the self-avoiding paths from `u` to `v` with at most `R` edges. -/
noncomputable def pathFamily (u v : Vertex m) (R : ℕ) : Finset (Finset (Edge m)) := by
  classical exact (Finset.range (R + 1)).biUnion fun k =>
    (((latticeGraph m).finsetWalkLength k u v).filter fun p => p.IsPath).image walkEdgeFinset

theorem mem_pathFamily {u v : Vertex m} {R : ℕ} {F : Finset (Edge m)} :
    F ∈ pathFamily u v R ↔
      ∃ p : (latticeGraph m).Walk u v, p.IsPath ∧ p.length ≤ R ∧ walkEdgeFinset p = F := by
  classical
  unfold pathFamily
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_filter,
    SimpleGraph.mem_finsetWalkLength_iff]
  constructor
  · rintro ⟨k, hk, p, ⟨hl, hp⟩, rfl⟩
    exact ⟨p, hp, by omega, rfl⟩
  · rintro ⟨p, hp, hl, rfl⟩
    exact ⟨p.length, by omega, p, ⟨rfl, hp⟩, rfl⟩

theorem pathFamily_nonempty {u v : Vertex m} {R : ℕ} (h : l1Dist u v ≤ R) :
    (pathFamily u v R).Nonempty := by
  obtain ⟨p, hp, hl⟩ := exists_isPath_length_eq_l1Dist u v
  exact ⟨_, mem_pathFamily.2 ⟨p, hp, hl ▸ h, rfl⟩⟩

theorem card_le_of_mem_pathFamily {u v : Vertex m} {R : ℕ} {F : Finset (Edge m)}
    (hF : F ∈ pathFamily u v R) : F.card ≤ R := by
  obtain ⟨p, -, hl, rfl⟩ := mem_pathFamily.1 hF
  exact (card_walkEdgeFinset_le p).trans hl

/-- `T ≤ T_R`. -/
theorem passageTime_le_minCost_pathFamily {u v : Vertex m} {R : ℕ} (h : l1Dist u v ≤ R)
    (ω : Config m) :
    (passageTime ω u v : ℝ) ≤ minCost (pathFamily u v R) (pathFamily_nonempty h) ω := by
  obtain ⟨F, hF, heq⟩ := exists_minCost_eq (h𝓕 := pathFamily_nonempty h) ω
  obtain ⟨p, hp, -, rfl⟩ := mem_pathFamily.1 hF
  rw [heq, ← walkCost_eq_sum_walkEdgeFinset ω p hp]
  exact NNReal.coe_le_coe.2 (passageTime_le_walkCost ω p)

/-- `T_R` is at most the cost of every self-avoiding path with at most `R` edges. -/
theorem minCost_pathFamily_le_walkCost {u v : Vertex m} {R : ℕ} (h : l1Dist u v ≤ R)
    (ω : Config m) (p : (latticeGraph m).Walk u v) (hp : p.IsPath) (hl : p.length ≤ R) :
    minCost (pathFamily u v R) (pathFamily_nonempty h) ω ≤ walkCost ω p := by
  rw [walkCost_eq_sum_walkEdgeFinset ω p hp]
  exact minCost_le (mem_pathFamily.2 ⟨p, hp, hl, rfl⟩)

/-- `T_R = T` when a self-avoiding path with at most `R` edges costs at most `a R` and no
self-avoiding path from `u` with more than `R` edges is `a`-cheap. -/
theorem minCost_pathFamily_eq_passageTime {u v : Vertex m} {R : ℕ} (h : l1Dist u v ≤ R)
    (ω : Config m) {a : ℝ} (p : (latticeGraph m).Walk u v) (hp : p.IsPath) (hl : p.length ≤ R)
    (hΓ : (walkCost ω p : ℝ) ≤ a * R)
    (hcheap : ∀ k : ℕ, R < k → ∀ (w : Vertex m) (q : (latticeGraph m).Walk u w), q.IsPath →
      q.length = k → a * k < walkCost ω q) :
    minCost (pathFamily u v R) (pathFamily_nonempty h) ω = passageTime ω u v := by
  have hq : ∀ q : (latticeGraph m).Walk u v,
      minCost (pathFamily u v R) (pathFamily_nonempty h) ω ≤ walkCost ω q := by
    intro q
    set q' : (latticeGraph m).Walk u v := (q.toPath : (latticeGraph m).Walk u v) with hq'
    have hq'p : q'.IsPath := q.toPath.2
    have hle : (walkCost ω q' : ℝ) ≤ walkCost ω q :=
      NNReal.coe_le_coe.2 (walkCost_toPath_le ω q)
    by_cases hlen : q'.length ≤ R
    · exact (minCost_pathFamily_le_walkCost h ω q' hq'p hlen).trans hle
    · have hk := hcheap q'.length (by omega) v q' hq'p rfl
      have hRk : (R : ℝ) ≤ q'.length := by exact_mod_cast (by omega : R ≤ q'.length)
      have h0 := (minCost_pathFamily_le_walkCost h ω p hp hl)
      have h1 : (0 : ℝ) ≤ walkCost ω q' := NNReal.coe_nonneg _
      by_cases ha : 0 ≤ a
      · have hak : a * R ≤ a * q'.length := mul_le_mul_of_nonneg_left hRk ha
        linarith
      · have : a * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
        linarith
  refine le_antisymm ?_ (passageTime_le_minCost_pathFamily h ω)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨q, hq1⟩ := exists_walkCost_lt (ω := ω) u v (ε := ε.toNNReal) (by simpa using hε)
  have := NNReal.coe_lt_coe.2 hq1
  push_cast at this
  rw [Real.coe_toNNReal _ hε.le] at this
  linarith [hq q]

/-- `T_R = T` except with probability at most `e^{-c(R+1)}/(1 - e^{-c}) + e^{-θ a R} M(θ)^{|v-u|₁}`,
for independent weights with law `F`, the cheap-path estimate at rate `a` with decay `c`, and a rate
`θ ≥ 0` with `M(θ) = E e^{θ τ} < ∞`. -/
theorem measure_minCost_pathFamily_ne_le {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} (hP : IsIIDWeights P F) {a c : ℝ} (hc : 0 < c)
    (hcheap : CheapPaths P a c) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : Integrable (fun x : ℝ≥0 => Real.exp (θ * x)) F) {u v : Vertex m} {R : ℕ}
    (h : l1Dist u v ≤ R) :
    P {ω | minCost (pathFamily u v R) (pathFamily_nonempty h) ω ≠ passageTime ω u v} ≤
      ENNReal.ofReal (Real.exp (-(c * (R + 1))) / (1 - Real.exp (-c))) +
        ENNReal.ofReal (Real.exp (-θ * (a * R)) * (∫ x, Real.exp (θ * x) ∂F) ^ l1Dist u v) := by
  have := IsIIDWeights.isProbabilityMeasure hP
  obtain ⟨p, hp, hpl⟩ := exists_isPath_length_eq_l1Dist u v
  set A : Set (Config m) := {ω | a * R ≤ (walkCost ω p : ℝ)}
  set B : ℕ → Set (Config m) := fun j => {ω | ∃ (w : Vertex m) (q : (latticeGraph m).Walk u w),
    q.IsPath ∧ q.length = R + 1 + j ∧ (walkCost ω q : ℝ) ≤ a * ((R + 1 + j : ℕ) : ℝ)}
  have hsub : {ω | minCost (pathFamily u v R) (pathFamily_nonempty h) ω ≠ passageTime ω u v}
      ⊆ A ∪ ⋃ j, B j := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hn
    obtain ⟨hA, hB⟩ := hn
    refine hω (minCost_pathFamily_eq_passageTime h ω (a := a) p hp (hpl ▸ h)
      (le_of_lt (not_le.1 hA)) ?_)
    intro k hk w q hq hql
    by_contra hcon
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
    exact hB j ⟨w, q, hq, by omega, by
      have e : R + j + 1 = R + 1 + j := by omega
      rw [e] at hcon
      exact not_lt.1 hcon⟩
  have hA : P A ≤
      ENNReal.ofReal (Real.exp (-θ * (a * R)) * (∫ x, Real.exp (θ * x) ∂F) ^ l1Dist u v) := by
    have := IsIIDWeights.measure_le_walkCost_le hP p hp.isTrail.edges_nodup hθ0 hθ (a * R)
    rwa [hpl] at this
  have hq : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hB : P (⋃ j, B j) ≤ ENNReal.ofReal (Real.exp (-(c * (R + 1))) / (1 - Real.exp (-c))) := by
    refine (measure_iUnion_le _).trans ?_
    have hj : ∀ j, P (B j) ≤
        ENNReal.ofReal (Real.exp (-(c * (R + 1))) * Real.exp (-c) ^ j) := fun j => by
      refine (hcheap u (R + 1 + j)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    refine (ENNReal.tsum_le_tsum hj).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      ((summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left _),
      tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hq, div_eq_mul_inv]
  calc _ ≤ P (A ∪ ⋃ j, B j) := measure_mono hsub
    _ ≤ P A + P (⋃ j, B j) := measure_union_le _ _
    _ ≤ _ := by rw [add_comm]; exact add_le_add hB hA

end CurvatureVariance.Infra.FPP
