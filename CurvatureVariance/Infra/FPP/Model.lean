/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.Translation
public import CurvatureVariance.Statements.Weights.IsIIDWeights
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecialFunctions.Exp
public import CurvatureVariance.Infra.Percolation.Lattice

/-!
# The model of independent, identically distributed weights

For the predicate `IsIIDWeights P F` (the weights `ω e` are independent under `P`, each with
law `F` on `[0, ∞)`):

* the law of the configuration is the product `Measure.infinitePi (fun _ => F)`, it exists, and it
  is invariant under the translations of `ℤ^d`;
* the cost of a walk is a sum over its darts; with an integrable weight it is integrable with mean
  `length · E τ`, and the cost of a walk with distinct edges (a path) has the moment generating
  function `M(θ)^length`, `M(θ) = E e^{θ τ}`, which gives a Chernoff bound for its upper tail;
* with an integrable weight the passage time is integrable, with `E T(u, v) ≤ |u - v|₁ E τ`;
* exponential moments of `F` below a rate with a finite exponential moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

open CurvatureVariance.Infra.Percolation (latticeShift)

variable {m : ℕ} {F : Measure ℝ≥0} {P : Measure (Config m)}

/-! ### The law -/

/-- The product of `F` over the edges satisfies `IsIIDWeights`. -/
theorem isIIDWeights_infinitePi (F : Measure ℝ≥0) [IsProbabilityMeasure F] :
    IsIIDWeights (Measure.infinitePi (fun _ : Edge m => F)) F := by
  refine ⟨iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id), fun e => ?_⟩
  exact ⟨(measurable_pi_apply e).aemeasurable, Measure.infinitePi_map_eval _ e⟩

/-- `IsIIDWeights` determines the law: it is the product of `F` over the edges. -/
theorem IsIIDWeights.eq_infinitePi [IsProbabilityMeasure F] (hP : IsIIDWeights P F) :
    P = Measure.infinitePi (fun _ : Edge m => F) := by
  have h := hP.1.map_fun_eq_infinitePi_map (fun e => measurable_pi_apply e)
  simp only [(hP.2 _).map_eq] at h
  simpa using h

/-- A law of independent weights with a probability law is a probability measure. -/
theorem IsIIDWeights.isProbabilityMeasure [IsProbabilityMeasure F] (hP : IsIIDWeights P F) :
    IsProbabilityMeasure P := by
  rw [(IsIIDWeights.eq_infinitePi hP)]; infer_instance

/-- **Translation invariance** of the law of independent identically distributed weights:
translation permutes the edges, and the law is a product of identical laws. -/
theorem IsIIDWeights.measurePreserving_translate [IsProbabilityMeasure F] (hP : IsIIDWeights P F)
    (a : Vertex m) : MeasurePreserving (translate a) P P := by
  rw [(IsIIDWeights.eq_infinitePi hP)]
  have heq : (translate a : Config m → Config m) =
      MeasurableEquiv.piCongrLeft (fun _ : Edge m => ℝ≥0) ((latticeShift a).mapEdgeSet.symm) := by
    funext ω e
    rw [translate_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp
  refine ⟨measurable_translate a, ?_⟩
  rw [heq]
  exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : Edge m => F)
    ((latticeShift a).mapEdgeSet.symm)

/-- The real weights are independent. -/
theorem IsIIDWeights.iIndepFun_real (hP : IsIIDWeights P F) :
    iIndepFun (fun (e : Edge m) (ω : Config m) => (ω e : ℝ)) P :=
  hP.1.comp (fun _ x => (x : ℝ)) fun _ => measurable_coe_nnreal_real

/-- Each real weight has law `F` pushed to `ℝ`. -/
theorem IsIIDWeights.hasLaw_real (hP : IsIIDWeights P F) (e : Edge m) :
    HasLaw (fun ω : Config m => (ω e : ℝ)) (F.map ((↑) : ℝ≥0 → ℝ)) P :=
  ⟨measurable_coe_nnreal_real.comp_aemeasurable (hP.2 e).aemeasurable, by
    rw [← (hP.2 e).map_eq, Measure.map_map measurable_coe_nnreal_real (measurable_pi_apply e)]
    rfl⟩

/-- Each real weight has the law of the identity under `F`, as an `IdentDistrib`. -/
theorem IsIIDWeights.identDistrib (hP : IsIIDWeights P F) (e : Edge m) :
    IdentDistrib (fun ω : Config m => (ω e : ℝ)) (fun x : ℝ≥0 => (x : ℝ)) P F :=
  ⟨((IsIIDWeights.hasLaw_real hP) e).aemeasurable, measurable_coe_nnreal_real.aemeasurable, by
    rw [((IsIIDWeights.hasLaw_real hP) e).map_eq]⟩

/-! ### Walk costs as sums over darts -/

/-- The edge traversed by the `i`-th dart of a walk. -/
def dartEdge {u v : Vertex m} (p : (latticeGraph m).Walk u v) (i : Fin p.darts.length) : Edge m :=
  ⟨p.darts[i].edge, p.darts[i].edge_mem⟩

/-- The cost of a walk as a sum over the positions of its darts. -/
theorem coe_walkCost_eq_sum {u v : Vertex m} (p : (latticeGraph m).Walk u v) (ω : Config m) :
    (walkCost ω p : ℝ) = ∑ i : Fin p.darts.length, (ω (dartEdge p i) : ℝ) := by
  have h : walkCost ω p = ∑ i : Fin p.darts.length, ω (dartEdge p i) := by
    change (p.darts.map fun t => ω ⟨t.edge, t.edge_mem⟩).sum = _
    rw [← Fin.sum_univ_getElem]
    exact Fintype.sum_equiv (finCongr (List.length_map ..)) _ _ (fun i => by simp [dartEdge])
  rw [h, NNReal.coe_sum]

theorem walkCost_eq_sum_fun {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    (fun ω : Config m => (walkCost ω p : ℝ)) =
      ∑ i ∈ Finset.univ, fun ω : Config m => (ω (dartEdge p i) : ℝ) := by
  funext ω
  rw [Finset.sum_apply, coe_walkCost_eq_sum]

/-- On a walk with distinct edges, the dart positions name distinct edges. -/
theorem injective_dartEdge {u v : Vertex m} (p : (latticeGraph m).Walk u v)
    (hnodup : p.edges.Nodup) : Function.Injective (dartEdge p) := by
  intro i j hij
  have h : (dartEdge p i).1 = (dartEdge p j).1 := congrArg Subtype.val hij
  have hl : p.edges.length = p.darts.length := by simp
  have h2 : p.edges[i.1]'(by rw [hl]; exact i.2) = p.edges[j.1]'(by rw [hl]; exact j.2) := by
    simpa [dartEdge, SimpleGraph.Walk.edges] using h
  exact Fin.ext ((hnodup.getElem_inj_iff).1 h2)

/-- The real cost of a fixed walk is measurable in the configuration. -/
theorem measurable_walkCost_real {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    Measurable fun ω : Config m => (walkCost ω p : ℝ) :=
  (measurable_walkCost p).coe_nnreal_real

/-! ### Moments of walk costs -/

section Moments

variable (hP : IsIIDWeights P F) {u v : Vertex m} (p : (latticeGraph m).Walk u v)
include hP

/-- With an integrable weight, the cost of a walk is integrable. -/
theorem IsIIDWeights.integrable_walkCost (hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) F) :
    Integrable (fun ω => (walkCost ω p : ℝ)) P := by
  rw [walkCost_eq_sum_fun]
  exact integrable_finsetSum' _ fun i _ =>
    ((IsIIDWeights.identDistrib hP) (dartEdge p i)).integrable_iff.2 hF

/-- With an integrable weight, a walk costs `length · E τ` on average (repeated edges counted with
multiplicity; no independence is needed). -/
theorem IsIIDWeights.integral_walkCost (hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) F) :
    ∫ ω, (walkCost ω p : ℝ) ∂P = p.length * ∫ x, (x : ℝ) ∂F := by
  simp_rw [coe_walkCost_eq_sum]
  rw [integral_finsetSum _ fun i _ =>
    ((IsIIDWeights.identDistrib hP) (dartEdge p i)).integrable_iff.2 hF]
  simp_rw [((IsIIDWeights.identDistrib hP) _).integral_eq]
  simp

variable (hnodup : p.edges.Nodup)
include hnodup

/-- The moment generating function of the cost of a walk with distinct edges is `M(θ)^length`. -/
theorem IsIIDWeights.mgf_walkCost (θ : ℝ) :
    mgf (fun ω => (walkCost ω p : ℝ)) P θ = (mgf (fun x : ℝ≥0 => (x : ℝ)) F θ) ^ p.length := by
  have hI : iIndepFun (fun (i : Fin p.darts.length) (ω : Config m) => (ω (dartEdge p i) : ℝ)) P :=
    (IsIIDWeights.iIndepFun_real hP).precomp (injective_dartEdge p hnodup)
  rw [walkCost_eq_sum_fun,
    hI.mgf_sum₀ (fun i => ((IsIIDWeights.identDistrib hP) (dartEdge p i)).aemeasurable_fst)]
  rw [Finset.prod_eq_pow_card fun i _ =>
    mgf_congr_of_identDistrib _ _ ((IsIIDWeights.identDistrib hP) _) θ]
  simp

/-- The cost of a walk with distinct edges has the exponential moments of its weights. -/
theorem IsIIDWeights.integrable_exp_mul_walkCost [IsProbabilityMeasure F] {θ : ℝ}
    (hθ : Integrable (fun x : ℝ≥0 => Real.exp (θ * x)) F) :
    Integrable (fun ω => Real.exp (θ * (walkCost ω p : ℝ))) P := by
  have := (IsIIDWeights.isProbabilityMeasure hP)
  have hI : iIndepFun (fun (i : Fin p.darts.length) (ω : Config m) => (ω (dartEdge p i) : ℝ)) P :=
    (IsIIDWeights.iIndepFun_real hP).precomp (injective_dartEdge p hnodup)
  simp_rw [coe_walkCost_eq_sum]
  have := hI.integrable_exp_mul_sum (fun i => (measurable_pi_apply (dartEdge p i)).coe_nnreal_real)
    (s := Finset.univ) (t := θ) (fun i _ =>
      (((IsIIDWeights.identDistrib hP) (dartEdge p i)).comp
        (measurable_id.const_mul θ).exp).integrable_iff.2 hθ)
  simpa using this

/-- **Chernoff bound for the cost of a path**: for `θ ≥ 0` with `M(θ) = E e^{θ τ} < ∞`,
`P(walkCost ≥ s) ≤ e^{-θ s} M(θ)^length` for a walk with distinct edges. -/
theorem IsIIDWeights.measure_le_walkCost_le [IsProbabilityMeasure F] {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : Integrable (fun x : ℝ≥0 => Real.exp (θ * x)) F) (s : ℝ) :
    P {ω | s ≤ (walkCost ω p : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-θ * s) * (∫ x, Real.exp (θ * x) ∂F) ^ p.length) := by
  have := (IsIIDWeights.isProbabilityMeasure hP)
  have h := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω => (walkCost ω p : ℝ)) s hθ0
    ((IsIIDWeights.integrable_exp_mul_walkCost hP) p hnodup hθ)
  rw [(IsIIDWeights.mgf_walkCost hP) p hnodup θ] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal h

end Moments

/-! ### The passage time -/

section PassageTime

variable (hP : IsIIDWeights P F) (hF : Integrable (fun x : ℝ≥0 => (x : ℝ)) F)
include hP hF

/-- With an integrable weight, the passage time is integrable (it is at most the cost of a
coordinate path). -/
theorem IsIIDWeights.integrable_passageTime [IsProbabilityMeasure F] (u v : Vertex m) :
    Integrable (fun ω => (passageTime ω u v : ℝ)) P := by
  have := (IsIIDWeights.isProbabilityMeasure hP)
  obtain ⟨p, -, -⟩ := exists_isPath_length_eq_l1Dist u v
  refine ((IsIIDWeights.integrable_walkCost hP) p hF).mono'
    (measurable_passageTime_real u v).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact NNReal.coe_le_coe.2 (passageTime_le_walkCost ω p)

/-- `E T(u, v) ≤ |u - v|₁ E τ`. -/
theorem IsIIDWeights.integral_passageTime_le [IsProbabilityMeasure F] (u v : Vertex m) :
    ∫ ω, (passageTime ω u v : ℝ) ∂P ≤ l1Dist u v * ∫ x, (x : ℝ) ∂F := by
  obtain ⟨p, -, hl⟩ := exists_isPath_length_eq_l1Dist u v
  rw [← hl, ← (IsIIDWeights.integral_walkCost hP) p hF]
  exact integral_mono ((IsIIDWeights.integrable_passageTime hP) hF u v)
    ((IsIIDWeights.integrable_walkCost hP) p hF)
    fun ω => NNReal.coe_le_coe.2 (passageTime_le_walkCost ω p)

end PassageTime

/-! ### Exponential moments of the weight law -/

/-- A finite exponential moment at rate `α` gives one at every rate `θ ≤ α`. -/
theorem integrable_exp_mul_of_le [IsFiniteMeasure F] {α θ : ℝ} (hθα : θ ≤ α)
    (hα : Integrable (fun x : ℝ≥0 => Real.exp (α * x)) F) :
    Integrable (fun x : ℝ≥0 => Real.exp (θ * x)) F := by
  refine ((hα.add (integrable_const 1))).mono'
    (measurable_coe_nnreal_real.const_mul θ).exp.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  show Real.exp (θ * x) ≤ Real.exp (α * x) + 1
  rcases le_total θ 0 with h | h
  · have : Real.exp (θ * x) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg h (NNReal.coe_nonneg x))
    linarith [Real.exp_pos (α * x)]
  · have : Real.exp (θ * x) ≤ Real.exp (α * x) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hθα (NNReal.coe_nonneg x))
    linarith

/-- A finite exponential moment at a positive rate makes the weight integrable. -/
theorem integrable_coe_of_exp [IsFiniteMeasure F] {α : ℝ} (hα0 : 0 < α)
    (hα : Integrable (fun x : ℝ≥0 => Real.exp (α * x)) F) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) F := by
  refine (hα.const_mul α⁻¹).mono' measurable_coe_nnreal_real.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg x)]
  have h := Real.add_one_le_exp (α * x)
  rw [le_inv_mul_iff₀ hα0]
  nlinarith [NNReal.coe_nonneg x]

end CurvatureVariance.Infra.FPP
