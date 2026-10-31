/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
public import CurvatureVariance.Infra.FPP.Translation
public import CurvatureVariance.Infra.FPP.Model
public import CurvatureVariance.Paper.Proofs.Responses.Basic
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.InnerProductSpace.Dual
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Module
import CurvatureVariance.Paper.Proofs.ShortLengths.Translate

/-!
# Common facts for Section `sec:gain`: translations, blocks and subgradients

Facts used by several proofs of Section `sec:gain`:

* **Translation equivariance** (the translation property of Lemma `lem:labels`, the minima `F_m`,
  and the comparison of `F̄` with the passage time): for the translate `θ_a ω`
  (`Infra.FPP.translate`, `(θ_a ω)(e) = ω(e + a)`), restricted passage times, slab passage times,
  tuple costs and the slab minimum `F` of equation `eq:F` at `θ_a ω` are those at `ω` with all
  points translated by `a` (`Proofs.ShortLengths.slabTime_translate`, `slabMin_translate`). In
  particular the translated minimum `F_τ` of Section `sec:gain` is `F` at the translate by `(0, τ)`
  (`translatedMin_eq_targetMin`).
* **Blocks shift to blocks** (the minima `F_m`): translating an edge by `(0, w L g')` maps the block
  `g` of a slab onto the block `g + g'` with the same offset (`map_add_mem_block_iff`); in
  particular the common translations by `v L w e₂` of the minima `F_m` permute the blocks of each
  slab.
* Measurability of `translatedMin` and `averagedMin`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Translation of restricted passage times -/

/-- Translating an edge by `a` maps the edges of the slab `[p, q]` onto those of the slab
`[p + a₁, q + a₁]`. -/
theorem map_add_mem_slabEdges_of_mem {p q : ℤ} (a : Vertex m) {e : Sym2 (Vertex m)}
    (he : e ∈ slabEdges p q) : Sym2.map (· + a) e ∈ slabEdges (p + a.1) (q + a.1) := by
  obtain ⟨x, hx⟩ := he
  refine ⟨x + a, ?_⟩
  rcases hx with ⟨rfl, h1, h2⟩ | ⟨j, rfl, h1, h2⟩
  · refine Or.inl ⟨?_, by simpa using h1, by simpa using h2⟩
    rw [Sym2.map_mk, add_right_comm]
  · refine Or.inr ⟨j, ?_, by simpa using h1, by simpa using h2⟩
    rw [Sym2.map_mk, add_right_comm]

/-- Membership in a slab is translation invariant. -/
theorem map_add_mem_slabEdges_iff {p q : ℤ} (a : Vertex m) (e : Sym2 (Vertex m)) :
    Sym2.map (· + a) e ∈ slabEdges (p + a.1) (q + a.1) ↔ e ∈ slabEdges p q := by
  refine ⟨fun h => ?_, map_add_mem_slabEdges_of_mem a⟩
  have h' := map_add_mem_slabEdges_of_mem (-a) h
  rw [Sym2.map_map] at h'
  have hid : ((fun x : Vertex m => x + -a) ∘ fun x => x + a) = id := by
    funext x
    simp
  rw [hid, Sym2.map_id, id] at h'
  simpa using h'

/-- The real slab passage time is translation equivariant. -/
theorem slabTimeReal_translate (a : Vertex m) (ω : Config m) (p q : ℤ) (u v : Vertex m) :
    slabTimeReal (translate a ω) p q u v = slabTimeReal ω (p + a.1) (q + a.1) (u + a) (v + a) := by
  simp only [slabTimeReal, Proofs.ShortLengths.slabTime_translate]

/-! ### Translation of the slab minimum -/

/-- The tuple translated by the transverse part of `a`. -/
theorem tuplePoint_add (u a : Vertex m) (n : ℕ) {K : ℕ} (y : Fin (K + 1) → Fin m → ℤ)
    (i : Fin (K + 1)) :
    tuplePoint (u + a) n (fun j => y j + a.2) i = tuplePoint u n y i + a := by
  simp only [tuplePoint, Prod.fst_add]
  congr 1
  ring

/-- Tuple costs are translation equivariant. -/
theorem tupleCost_translate (a : Vertex m) (ω : Config m) (u : Vertex m) (n : ℕ) {K : ℕ}
    (y : Fin (K + 1) → Fin m → ℤ) :
    tupleCost (translate a ω) u n y = tupleCost ω (u + a) n (fun j => y j + a.2) := by
  unfold tupleCost
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Proofs.ShortLengths.slabTime_translate, tuplePoint_add, tuplePoint_add]
  congr 1 <;> simp only [Prod.fst_add] <;> ring

/-- Admissibility of tuples is translation invariant. -/
theorem isAdmissibleTuple_add_iff (M : Model m) (n K : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (u v a : Vertex m) (y : Fin (K + 1) → Fin m → ℤ) :
    IsAdmissibleTuple M n K t (u + a) (v + a) (fun j => y j + a.2) ↔
      IsAdmissibleTuple M n K t u v y := by
  simp only [IsAdmissibleTuple, Prod.snd_add, add_left_inj, add_sub_add_right_eq_sub]

/-- **The slab minimum is translation equivariant**: `F(θ_a ω)` from `u` to `v` is `F(ω)` from
`u + a` to `v + a`. -/
theorem slabMin_translate (M : Model m) (a : Vertex m) (ω : Config m) (n K : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m) :
    slabMin M (translate a ω) n K t u v = slabMin M ω n K t (u + a) (v + a) := by
  unfold slabMin
  let e : (Fin (K + 1) → Fin m → ℤ) ≃ (Fin (K + 1) → Fin m → ℤ) :=
    Equiv.addRight (fun _ => a.2)
  refine Eq.trans ?_ (e.iInf_comp (g := fun y =>
    ⨅ (_ : IsAdmissibleTuple M n K t (u + a) (v + a) y), tupleCost ω (u + a) n y))
  refine iInf_congr fun y => ?_
  have hy : e y = fun j => y j + a.2 := rfl
  rw [hy, tupleCost_translate]
  exact iInf_congr_Prop (isAdmissibleTuple_add_iff M n K t u v a y).symm fun _ => rfl

/-- **The translated minimum `F_τ` is `F` at the translate by `(0, τ)`** (the minima `F_m` of the
text before Lemma `lem:residual`). -/
theorem translatedMin_eq_targetMin (M : Model m) (ω : Config m) (n K ℓ : ℕ)
    (y τ : Fin m → ℤ) :
    translatedMin M ω n K ℓ y τ = targetMin M (translate ((0 : ℤ), τ) ω) n K ℓ y := by
  rw [targetMin, slabMin_translate, translatedMin, zero_add, Prod.mk_add_mk, add_zero]

/-! ### Measurability and laws -/

/-- The translated minimum is measurable. -/
theorem measurable_translatedMin (M : Model m) (n K ℓ : ℕ) (y τ : Fin m → ℤ) :
    Measurable fun ω => translatedMin M ω n K ℓ y τ :=
  (Responses.measurable_slabMin M n K _ _ _).ennreal_toReal

/-- The averaged minimum `F̄` is measurable. -/
theorem measurable_averagedMin (M : Model m) (K : ℕ) (A : ℝ) (L n ℓ : ℕ) (y : Fin m → ℤ) :
    Measurable fun ω => averagedMin M K A L ω n ℓ y := by
  unfold averagedMin
  exact measurable_const.mul
    (Finset.measurable_sum _ fun v _ => measurable_translatedMin M n K ℓ y _)

/-! ### Blocks under transverse translations by multiples of `w L` -/

/-- The midpoint of a translated edge is the translated midpoint. -/
theorem edgeMid_map_add (a : Vertex m) (e : Sym2 (Vertex m)) :
    edgeMid (Sym2.map (· + a) e) = edgeMid e + point a := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Sym2.map_mk, edgeMid, Sym2.lift_mk, point_add]
    module

/-- Translating a point of `ℝ^d` by the vertex `(0, w g')` shifts its fine-cube index by `g'`. -/
theorem fineIndex_add_point {w : ℕ} (hw : 0 < w) (t : EuclideanSpace ℝ (Fin m)) (x : Pt m)
    (g' : Fin m → ℤ) :
    fineIndex w t (x + point ((0 : ℤ), fun k => (w : ℤ) * g' k)) = fineIndex w t x + g' := by
  funext k
  have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  simp only [fineIndex, point, transversePoint, WithLp.ofLp_add, Prod.fst_add, Prod.snd_add,
    Pi.add_apply, Int.cast_zero, add_zero, Int.cast_mul, Int.cast_natCast]
  rw [show x.ofLp.2 k + (w : ℝ) * g' k - x.ofLp.1 * t k =
      (x.ofLp.2 k - x.ofLp.1 * t k) + (g' k : ℝ) * w by ring, add_div,
    mul_div_cancel_right₀ _ hw', Int.floor_add_intCast]

/-- **Blocks shift to blocks**: translating an edge by `(0, w L g')` maps the block `g` of a slab
onto the block `g + g'`, with the same offset. -/
theorem map_add_mem_block_iff {n w L : ℕ} (hw : 0 < w) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ)
    (o g g' : Fin m → ℤ) (e : Sym2 (Vertex m)) :
    Sym2.map (· + ((0 : ℤ), fun k => (w : ℤ) * ((L : ℤ) * g' k))) e ∈ block n w L t i o (g + g') ↔
      e ∈ block n w L t i o g := by
  have hslab := map_add_mem_slabEdges_iff (p := ((i : ℤ) - 1) * n) (q := (i : ℤ) * n)
    ((0 : ℤ), fun k => (w : ℤ) * ((L : ℤ) * g' k)) e
  simp only [add_zero] at hslab
  simp only [block, mem_ofPred_eq, hslab, edgeMid_map_add, fineIndex_add_point hw, Pi.add_apply]
  refine and_congr_right fun _ => forall_congr' fun k => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end CurvatureVariance.Paper.Gain
