/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Weights.IsIIDWeights
public import CurvatureVariance.Statements.Percolation.OpenGraph
public import CurvatureVariance.Infra.Percolation.Transitive
public import CurvatureVariance.Infra.Percolation.Lattice
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Small weights are Bernoulli percolation

The coupling of first-passage percolation with Bernoulli bond percolation used by the block
argument for Kesten's estimate: under independent weights with law `F`, the edges of weight at
most `ε` are open independently with probability `F([0, ε])`.

* `eq_infinitePi_of_isIIDWeights`: the law of independent weights with law `F` is the product law.
* `openConfig ε ω`: the configuration of `ε`-open edges, `e` open when `ω e ≤ ε`;
  `map_openConfig_of_isIIDWeights`: its law is `percolation (latticeGraph m) (smallWeightProb F ε)`.
* `percolation_arm_le`: the one-arm bound at the origin (the form
  `Infra.Percolation.measure_reachable_sphere_le` of [Duminil-Copin and Tassion, Theorem 1.1(1)])
  transported to every vertex by translation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.Kesten

open CurvatureVariance.Infra.Percolation

variable {m : ℕ}

/-- **The law of independent weights is the product law.** -/
theorem eq_infinitePi_of_isIIDWeights {P : Measure (Config m)} [IsProbabilityMeasure P]
    {F : Measure ℝ≥0} [IsProbabilityMeasure F] (hP : IsIIDWeights P F) :
    P = Measure.infinitePi fun _ : Edge m => F := by
  have h := hP.1.map_fun_eq_infinitePi_map (fun e => measurable_pi_apply e)
  have hF : ∀ e : Edge m, P.map (fun ω : Config m => ω e) = F := fun e => (hP.2 e).map_eq
  simp only [hF] at h
  rw [← h]
  exact (Measure.map_id' (μ := P)).symm

/-- The configuration of `ε`-open edges: an edge is open when its weight is at most `ε`. -/
noncomputable def openConfig (ε : ℝ≥0) (ω : Config m) : Edge m → Bool :=
  fun e => decide (ω e ≤ ε)

/-- The indicator of a small weight is measurable. -/
theorem measurable_decide_le (ε : ℝ≥0) : Measurable fun x : ℝ≥0 => decide (x ≤ ε) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · have : (fun x : ℝ≥0 => decide (x ≤ ε)) ⁻¹' {false} = (Set.Iic ε)ᶜ := by
      ext x; simp
    rw [this]; exact measurableSet_Iic.compl
  · have : (fun x : ℝ≥0 => decide (x ≤ ε)) ⁻¹' {true} = Set.Iic ε := by
      ext x; simp
    rw [this]; exact measurableSet_Iic

/-- The configuration of `ε`-open edges is a measurable function of the weights. -/
theorem measurable_openConfig (ε : ℝ≥0) : Measurable (openConfig (m := m) ε) :=
  measurable_pi_iff.2 fun e => (measurable_decide_le ε).comp (measurable_pi_apply e)

/-- The probability `F([0, ε])` that a weight is at most `ε`, as a parameter in `[0, 1]`. -/
noncomputable def smallWeightProb (F : Measure ℝ≥0) [IsProbabilityMeasure F] (ε : ℝ≥0) : I :=
  ⟨F.real (Set.Iic ε), measureReal_nonneg, measureReal_le_one⟩

/-- A weight with law `F` is at most `ε` with probability `F([0, ε])`: the law of the indicator
is Bernoulli. -/
theorem map_decide_le_eq_bernoulliMeasure (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (ε : ℝ≥0) :
    F.map (fun x : ℝ≥0 => decide (x ≤ ε)) = bernoulliMeasure true false (smallWeightProb F ε) := by
  have hm := measurable_decide_le ε
  have hpre : (fun x : ℝ≥0 => decide (x ≤ ε)) ⁻¹' {true} = Set.Iic ε := by ext x; simp
  have hpre' : (fun x : ℝ≥0 => decide (x ≤ ε)) ⁻¹' {false} = (Set.Iic ε)ᶜ := by ext x; simp
  have hT : F.map (fun x : ℝ≥0 => decide (x ≤ ε)) {true} =
      ENNReal.ofReal (smallWeightProb F ε) := by
    rw [Measure.map_apply hm (measurableSet_singleton _), hpre]
    simp [smallWeightProb, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hF : F.map (fun x : ℝ≥0 => decide (x ≤ ε)) {false} =
      ENNReal.ofReal (1 - smallWeightProb F ε) := by
    rw [Measure.map_apply hm (measurableSet_singleton _), hpre',
      measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
    simp only [smallWeightProb, measureReal_def]
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine Measure.ext_iff_singleton.2 fun b => ?_
  cases b
  · rw [hF, bernoulliMeasure_false]
  · rw [hT, bernoulliMeasure_true]

/-- **Small weights are Bernoulli percolation**: under independent weights with law `F`, the
`ε`-open edges are open independently, each with probability `F([0, ε])`. -/
theorem map_openConfig_of_isIIDWeights {P : Measure (Config m)} [IsProbabilityMeasure P]
    {F : Measure ℝ≥0} [IsProbabilityMeasure F] (hP : IsIIDWeights P F) (ε : ℝ≥0) :
    P.map (openConfig ε) = percolation (latticeGraph m) (smallWeightProb F ε) := by
  rw [eq_infinitePi_of_isIIDWeights hP]
  have h := Measure.infinitePi_map_pi (fun _ : Edge m => F)
    (f := fun _ (x : ℝ≥0) => decide (x ≤ ε)) (fun _ => measurable_decide_le ε)
  change (Measure.infinitePi fun _ : Edge m => F).map (fun ω e => decide (ω e ≤ ε)) = _
  rw [h, percolation, bernoulliProduct]
  congr 1
  funext e
  exact map_decide_le_eq_bernoulliMeasure F ε

/-- **The one-arm bound at every vertex**: if `P_p[0 ↔ ∂Λ_n] ≤ e^{-cn}` for `n ≥ 1` (in the
form with Mathlib's `setBernoulli` and the open graph), then for every vertex `x` and
`L ≥ 1`, the probability that `x` is connected by an open walk to a vertex at `ℓ^∞` distance `L`
is at most `e^{-cL}` (translation invariance). -/
theorem percolation_arm_le {p : I} {c : ℝ}
    (hc : ∀ n : ℕ, 1 ≤ n →
      setBernoulli (Set.univ : Set (Edge m)) p
          {S | ∃ x : Vertex m, latticeSupNorm x = n ∧
            (CurvatureVariance.openGraph m S).Reachable 0 x} ≤
        ENNReal.ofReal (Real.exp (-(c * n))))
    (x : Vertex m) {L : ℕ} (hL : 1 ≤ L) :
    percolation (latticeGraph m) p
        {η | ∃ y ∈ {y | latticeSupNorm (y - x) = L},
          OpenConnected (latticeGraph m) η Set.univ x y} ≤
      ENNReal.ofReal (Real.exp (-(c * L))) := by
  set g := Percolation.latticeShift (m := m) x
  set Ex := {η : Edge m → Bool | ∃ y ∈ {y | latticeSupNorm (y - x) = L},
    OpenConnected (latticeGraph m) η Set.univ x y}
  set E0 := {η : Edge m → Bool | ∃ y ∈ {y : Vertex m | latticeSupNorm y = L},
    OpenConnected (latticeGraph m) η Set.univ 0 y}
  have hpre : E0 = mapConfig g ⁻¹' Ex := by
    ext η
    simp only [E0, Ex, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, hc⟩
      refine ⟨g y, by simpa [g] using hy, ?_⟩
      have := (openConnected_mapConfig_iff g η Set.univ 0 y).2 hc
      rw [image_univ_map] at this
      simpa [g] using this
    · rintro ⟨y, hy, hc⟩
      refine ⟨y - x, hy, ?_⟩
      have h' : OpenConnected (latticeGraph m) (mapConfig g η) (Sym2.map g '' Set.univ)
          (g 0) (g (y - x)) := by
        rw [image_univ_map]; simpa [g] using hc
      exact (openConnected_mapConfig_iff g η Set.univ 0 (y - x)).1 h'
  have hEx : percolation (latticeGraph m) p Ex = percolation (latticeGraph m) p E0 := by
    rw [hpre]
    exact ((measurePreserving_mapConfig g p).measure_preimage
      (measurableSet_exists_openConnected _ _ _).nullMeasurableSet).symm
  rw [hEx]
  refine le_trans ?_ (hc L hL)
  have hset : E0 ⊆ openSet ⁻¹' {S | ∃ x : Vertex m, latticeSupNorm x = L ∧
      (CurvatureVariance.openGraph m S).Reachable 0 x} := by
    rintro η ⟨y, hy, hc⟩
    exact ⟨y, hy, (reachable_openGraph_openSet_iff η 0 y).2 hc⟩
  refine (measure_mono hset).trans ?_
  rw [setBernoulli_univ_eq_map]
  exact Measure.le_map_apply measurable_openSet.aemeasurable _

end CurvatureVariance.Infra.Kesten
