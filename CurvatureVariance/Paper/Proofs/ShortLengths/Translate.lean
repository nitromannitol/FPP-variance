/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Slabs
public import CurvatureVariance.Infra.FPP.Translation
public import CurvatureVariance.Infra.Os.Basic
public import CurvatureVariance.Infra.Percolation.Lattice

/-!
# Translations of slab passage times and of `O_s` bounds

* `slabTime_translate`: `D_{p,q}(u, v)` for the translated configuration `θ_a ω` is
  `D_{p+a₁,q+a₁}(u + a, v + a)` for `ω`: the translation maps the edges of the slab `[p, q]` onto
  those of `[p + a₁, q + a₁]` (`map_mem_slabEdges`);
* `IsOs.comp_measurePreserving`: an `O_s` bound is preserved by composing with a
  measure-preserving map, such as a translation of the weights.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Infra.Percolation (latticeShift)

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP CurvatureVariance.Infra.Os

variable {m : ℕ}

/-- A translation maps the edges of the slab `[p, q]` to those of `[p + a₁, q + a₁]`. -/
theorem map_mem_slabEdges (a : Vertex m) {p q : ℤ} {e : Sym2 (Vertex m)}
    (he : e ∈ slabEdges p q) : Sym2.map (· + a) e ∈ slabEdges (p + a.1) (q + a.1) := by
  obtain ⟨x, h⟩ := he
  rcases h with ⟨rfl, h1, h2⟩ | ⟨j, rfl, h1, h2⟩
  · refine ⟨x + a, Or.inl ⟨?_, by simp only [Prod.fst_add]; omega,
      by simp only [Prod.fst_add]; omega⟩⟩
    rw [Sym2.map_mk]
    rw [add_right_comm]
  · refine ⟨x + a, Or.inr ⟨j, ?_, by simp only [Prod.fst_add]; omega,
      by simp only [Prod.fst_add]; omega⟩⟩
    rw [Sym2.map_mk]
    rw [add_right_comm]

theorem map_mem_slabEdges_iff (a : Vertex m) {p q : ℤ} (e : Sym2 (Vertex m)) :
    Sym2.map (· + a) e ∈ slabEdges (p + a.1) (q + a.1) ↔ e ∈ slabEdges p q := by
  refine ⟨fun h => ?_, map_mem_slabEdges a⟩
  have h' := map_mem_slabEdges (-a) h
  simp only [Sym2.map_map, Prod.fst_neg, add_neg_cancel_right] at h'
  have : ((fun x : Vertex m => x + -a) ∘ fun x => x + a) = id := by
    funext x; simp
  rwa [this, Sym2.map_id, id] at h'

/-- **Slab passage times are translation covariant**:
`D_{p,q}(u, v; θ_a ω) = D_{p+a₁,q+a₁}(u + a, v + a; ω)`. -/
theorem slabTime_translate (a : Vertex m) (ω : Config m) (p q : ℤ) (u v : Vertex m) :
    slabTime (translate a ω) p q u v = slabTime ω (p + a.1) (q + a.1) (u + a) (v + a) := by
  unfold slabTime restrictedTime
  symm
  have h := (walkShiftEquiv a u v).iInf_comp
    (g := fun γ' : (latticeGraph m).Walk (latticeShift a u) (latticeShift a v) =>
      ⨅ (_ : ∀ e ∈ γ'.edges, e ∈ slabEdges (p + a.1) (q + a.1)), (walkCost ω γ' : ℝ≥0∞))
  refine h.symm.trans (iInf_congr fun γ => ?_)
  change ⨅ (_ : ∀ e ∈ (γ.map (latticeShift a).toHom).edges,
    e ∈ slabEdges (p + a.1) (q + a.1)), (walkCost ω (γ.map (latticeShift a).toHom) : ℝ≥0∞) = _
  rw [walkCost_map_latticeShift]
  refine iInf_congr_Prop ?_ fun _ => rfl
  rw [SimpleGraph.Walk.edges_map]
  constructor
  · intro h e he
    exact (map_mem_slabEdges_iff a e).1 (h _ (List.mem_map_of_mem he))
  · intro h e he
    rw [List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact map_mem_slabEdges a (h e' he')

/-- An `O_s` bound survives composition with a measure-preserving map. -/
theorem IsOs.comp_measurePreserving {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {s θ : ℝ} {X : Ω → ℝ} (h : IsOs P s θ X) {f : Ω → Ω} (hf : MeasurePreserving f P P) :
    IsOs P s θ (X ∘ f) := by
  refine ⟨h.1.comp_quasiMeasurePreserving hf.quasiMeasurePreserving, ?_⟩
  have hg := aemeasurable_exp_pos_rpow h.1 s θ
  have key : (∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X (f ω)) 0 / θ) ^ s)) ∂P) =
      ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂P := by
    have h1 := lintegral_map' (μ := P) (g := f)
      (f := fun ω => ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)))
      (by rw [hf.map_eq]; exact hg) hf.aemeasurable
    rw [hf.map_eq] at h1
    exact h1.symm
  exact key.le.trans h.2

end CurvatureVariance.Paper.Proofs.ShortLengths
