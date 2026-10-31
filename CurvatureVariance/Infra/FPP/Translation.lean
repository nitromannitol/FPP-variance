/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.Walks
public import Mathlib.Probability.IdentDistrib
public import CurvatureVariance.Infra.Percolation.Lattice

/-!
# Translations of `ℤ^d` and of weight configurations

The translation `latticeShift a : x ↦ x + a` (`CurvatureVariance.Infra.Percolation.latticeShift`)
is an automorphism of the lattice graph, and `translate a ω` is the configuration
`e ↦ ω (e + a)`. Walks map along `latticeShift a`, so
`T_{translate a ω}(u, v) = T_ω(u + a, v + a)`. Under a law invariant under `translate a`, every
measurable observable of the translated configuration has the law of the observable; in particular
`E T(u + a, v + a) = E T(u, v)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

open CurvatureVariance.Infra.Percolation (latticeShift)

variable {m : ℕ}

/-- A translation maps an edge `{x, y}` to `{x + a, y + a}`. -/
@[simp] theorem coe_latticeShift_mapEdgeSet (a : Vertex m) (e : Edge m) :
    (((latticeShift a).mapEdgeSet e : Edge m) : Sym2 (Vertex m)) = Sym2.map (· + a) e.1 := rfl

/-- The translate `θ_a ω` of a configuration, `(θ_a ω)(e) = ω(e + a)`. -/
def translate (a : Vertex m) (ω : Config m) : Config m :=
  fun e => ω ((latticeShift a).mapEdgeSet e)

/-- The convention of `translate`: `(translate a ω) e = ω (e + a)`. -/
theorem translate_apply (a : Vertex m) (ω : Config m) (e : Edge m) :
    translate a ω e = ω ((latticeShift a).mapEdgeSet e) := rfl

/-- Translation by zero is the identity. -/
@[simp] theorem translate_zero (ω : Config m) : translate 0 ω = ω := by
  funext e
  rw [translate_apply]
  congr 1
  apply Subtype.ext
  show Sym2.map (fun x : Vertex m => x + 0) e.1 = e.1
  simp only [add_zero, Sym2.map_id', id]

/-- Translations compose: `θ_a θ_b = θ_{a + b}`. -/
theorem translate_translate (a b : Vertex m) (ω : Config m) :
    translate a (translate b ω) = translate (a + b) ω := by
  funext e
  simp only [translate_apply]
  congr 1
  apply Subtype.ext
  simp only [coe_latticeShift_mapEdgeSet, Sym2.map_map]
  congr 1
  funext x
  simp [add_assoc]

/-- Translations are measurable for the product σ-algebra on configurations. -/
theorem measurable_translate (a : Vertex m) : Measurable (translate (m := m) a) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-! ### Walks along a translation -/

/-- Mapping a walk along a translation pulls the weights back. -/
theorem walkCost_map_latticeShift (a : Vertex m) (ω : Config m) {u v : Vertex m}
    (p : (latticeGraph m).Walk u v) :
    walkCost ω (p.map (latticeShift a).toHom) = walkCost (translate a ω) p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [SimpleGraph.Walk.map_cons, walkCost_cons, ih]
    rfl

/-- The walk map induced by a translation is a bijection with fixed endpoints. -/
def walkShiftEquiv (a : Vertex m) (u v : Vertex m) :
    (latticeGraph m).Walk u v ≃ (latticeGraph m).Walk (latticeShift a u) (latticeShift a v) where
  toFun := SimpleGraph.Walk.map (latticeShift a).toHom
  invFun := fun p => (p.map (latticeShift a).symm.toHom).copy
    ((latticeShift a).symm_apply_apply u) ((latticeShift a).symm_apply_apply v)
  left_inv := by
    intro p
    dsimp only
    rw [SimpleGraph.Walk.map_map]
    rw [p.map_eq_of_eq SimpleGraph.Hom.id (SimpleGraph.Iso.symm_toHom_comp_toHom (latticeShift a))]
    simp only [SimpleGraph.Walk.map_id]
    exact (p.copy_copy _ _ _ _).trans p.copy_rfl_rfl
  right_inv := by
    intro p
    rw [SimpleGraph.Walk.map_copy, SimpleGraph.Walk.map_map]
    rw [p.map_eq_of_eq SimpleGraph.Hom.id (SimpleGraph.Iso.toHom_comp_symm_toHom (latticeShift a))]
    simp only [SimpleGraph.Walk.map_id]
    exact (p.copy_copy _ _ _ _).trans p.copy_rfl_rfl

/-- `T_{θ_a ω}(u, v) = T_ω(u + a, v + a)`. -/
theorem passageTime_translate (a : Vertex m) (ω : Config m) (u v : Vertex m) :
    passageTime (translate a ω) u v = passageTime ω (u + a) (v + a) := by
  change sInf (Set.range _) = sInf (Set.range fun p : (latticeGraph m).Walk (latticeShift a u)
    (latticeShift a v) => walkCost ω p)
  congr 1
  rw [← (walkShiftEquiv a u v).surjective.range_comp (walkCost ω)]
  congr 1
  funext p
  exact (walkCost_map_latticeShift a ω p).symm

/-! ### Stationarity -/

variable {P : Measure (Config m)} {a : Vertex m}

/-- Under a law invariant under `translate a`, every measurable observable of the translated
configuration has the law of the observable. -/
theorem identDistrib_comp_translate (h : MeasurePreserving (translate a) P P) {β : Type*}
    [MeasurableSpace β] {F : Config m → β} (hF : Measurable F) :
    IdentDistrib (fun ω => F (translate a ω)) F P P where
  aemeasurable_fst := (hF.comp (measurable_translate a)).aemeasurable
  aemeasurable_snd := hF.aemeasurable
  map_eq := by
    change Measure.map (F ∘ translate a) P = Measure.map F P
    rw [← Measure.map_map hF (measurable_translate a), h.map_eq]

/-- The passage time between translated endpoints has the law of the passage time. -/
theorem identDistrib_passageTime_add (h : MeasurePreserving (translate a) P P) (u v : Vertex m) :
    IdentDistrib (fun ω => passageTime ω (u + a) (v + a)) (fun ω => passageTime ω u v) P P := by
  have := identDistrib_comp_translate h (measurable_passageTime u v)
  simpa only [passageTime_translate] using this

/-- `E T(u + a, v + a) = E T(u, v)` under a law invariant under `translate a`. -/
theorem integral_passageTime_add (h : MeasurePreserving (translate a) P P) (u v : Vertex m) :
    ∫ ω, (passageTime ω (u + a) (v + a) : ℝ) ∂P = ∫ ω, (passageTime ω u v : ℝ) ∂P :=
  ((identDistrib_passageTime_add h u v).comp measurable_coe_nnreal_real).integral_eq

end CurvatureVariance.Infra.FPP
