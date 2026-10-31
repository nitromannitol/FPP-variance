/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
public import Mathlib.Probability.ProductMeasure
import CurvatureVariance.Paper.Proofs.Responses.Slabs

/-!
# The configuration as a product over the blocks

In the proofs of Lemmas `lem:residual` and `lem:fewtranslates` and of Proposition `prop:gain`, the
weights of the `K` slabs are viewed as countably many independent blocks of weights. This file makes
that precise.

* `fiberEquiv b`: for any map `b : Edge m → ι`, the measurable equivalence between the
  configurations and the families, indexed by `c : ι`, of weights of the edges of the fiber
  `b⁻¹{c}` (`fiberEquiv_apply`, `fiberEquiv_symm_apply`). It maps the product of `F` over the
  edges to the product over `c` of the products of `F` over the fibers (`map_fiberEquiv`), and
  replacing the coordinate `c` by that of `ω'` is resampling the fiber (`fiberEquiv_symm_update`).
* `blockCell`: the blocks `block n w L t (i + 1) (o (i + 1)) g` of the slabs `1 ≤ i + 1 ≤ K`
  with the offsets `o`, indexed by `some (i, g)`, and the edges outside all of them, indexed by
  `none`. They partition the edges (`eq_of_mem_block_of_mem_block`, `cellOf_eq_iff`), and every
  edge of slab `i` lies in a block of it (`exists_mem_block`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain.LabelResidual

open CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Configurations as products over the fibers of a map -/

section Fibers

variable {E ι : Type*} (b : E → ι)

/-- A family of weights indexed by `E`, as the family, indexed by `c : ι`, of its restrictions to
the fibers `b⁻¹{c}`. For `E` the edges, the configuration on the fibers. -/
noncomputable def fiberEquiv : (E → ℝ≥0) ≃ᵐ ∀ c : ι, ({e : E // b e = c} → ℝ≥0) :=
  (MeasurableEquiv.piCongrLeft (fun _ : E => ℝ≥0) (Equiv.sigmaFiberEquiv b)).symm.trans
    (MeasurableEquiv.piCurry fun (c : ι) (_ : {e : E // b e = c}) => ℝ≥0)

@[simp] theorem fiberEquiv_apply (ω : E → ℝ≥0) (c : ι) (e : {e : E // b e = c}) :
    fiberEquiv b ω c e = ω e.1 := rfl

@[simp] theorem fiberEquiv_symm_apply (x : ∀ c : ι, ({e : E // b e = c} → ℝ≥0)) (e : E) :
    (fiberEquiv b).symm x e = x (b e) ⟨e, rfl⟩ := rfl

/-- The product of `F` over `E` is carried to the product over the fibers of the products of `F`
over each fiber. -/
theorem map_fiberEquiv (F : Measure ℝ≥0) [IsProbabilityMeasure F] :
    (Measure.infinitePi fun _ : E => F).map (fiberEquiv b) =
      Measure.infinitePi fun c : ι => Measure.infinitePi fun _ : {e : E // b e = c} => F := by
  have h1 : (Measure.infinitePi fun _ : E => F).map
      (MeasurableEquiv.piCongrLeft (fun _ : E => ℝ≥0) (Equiv.sigmaFiberEquiv b)).symm =
      Measure.infinitePi fun _ : (c : ι) × {e : E // b e = c} => F := by
    rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, MeasurableEquiv.symm_symm]
    exact (Measure.infinitePi_map_piCongrLeft (fun _ : E => F)
      (Equiv.sigmaFiberEquiv b)).symm
  rw [fiberEquiv, MeasurableEquiv.coe_trans, ← Measure.map_map (MeasurableEquiv.measurable _)
    (MeasurableEquiv.measurable _), h1]
  exact Measure.infinitePi_map_piCurry (fun (c : ι) (_ : {e : E // b e = c}) => F)

/-- Replacing the coordinate `c` by that of `ω'` resamples the fiber `b⁻¹{c}`. -/
theorem fiberEquiv_symm_update [DecidableEq ι] (b : Edge m → ι) (c : ι) (ω ω' : Config m)
    {G : Set (Sym2 (Vertex m))} (hG : ∀ e : Edge m, e.1 ∈ G ↔ b e = c) :
    (fiberEquiv b).symm (Function.update (fiberEquiv b ω) c (fiberEquiv b ω' c)) =
      resample G ω ω' := by
  classical
  funext e
  rw [fiberEquiv_symm_apply]
  by_cases he : b e = c
  · subst he
    have hm : e.1 ∈ G := (hG e).2 rfl
    simp [resample, hm]
  · have hm : e.1 ∉ G := fun h => he ((hG e).1 h)
    rw [Function.update_of_ne he, fiberEquiv_apply]
    simp [resample, hm]

end Fibers

/-! ### The blocks of the `K` slabs -/

section Blocks

variable (n w L K : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o : ℕ → Fin m → ℤ)

/-- The blocks of the `K` slabs and the rest: for `c = some (i, g)` the block
`block n w L t (i + 1) (o (i + 1)) g` of slab `i + 1`, and for `c = none` the edges outside all
of these blocks. -/
def blockCell : Option (Fin K × (Fin m → ℤ)) → Set (Sym2 (Vertex m))
  | some c => block n w L t ((c.1 : ℕ) + 1) (o ((c.1 : ℕ) + 1)) c.2
  | none => {e | ∀ c : Fin K × (Fin m → ℤ),
      e ∉ block n w L t ((c.1 : ℕ) + 1) (o ((c.1 : ℕ) + 1)) c.2}

variable {n w L K t o}

/-- Two blocks of slabs `i + 1`, `i' + 1` with a common edge are the same block. -/
theorem eq_of_mem_block_of_mem_block {i i' : ℕ} {g g' : Fin m → ℤ} {e : Sym2 (Vertex m)}
    (h : e ∈ block n w L t (i + 1) (o (i + 1)) g)
    (h' : e ∈ block n w L t (i' + 1) (o (i' + 1)) g') : i = i' ∧ g = g' := by
  have hii : i = i' := by
    by_contra hne
    have hd := Responses.pairwise_disjoint_slabEdges (m := m) 0 n hne
    have hs : e ∈ slabEdges ((((i + 1 : ℕ) : ℤ) - 1) * n) (((i + 1 : ℕ) : ℤ) * n) := h.1
    have hs' : e ∈ slabEdges ((((i' + 1 : ℕ) : ℤ) - 1) * n) (((i' + 1 : ℕ) : ℤ) * n) := h'.1
    push_cast at hs hs'
    simp only [zero_add, add_sub_cancel_right] at hd hs hs'
    exact Set.disjoint_left.mp hd hs hs'
  subst hii
  refine ⟨rfl, funext fun k => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 k
  obtain ⟨h1', h2'⟩ := h'.2 k
  have hL : (0 : ℤ) ≤ L := Int.natCast_nonneg L
  have a1 : (L : ℤ) * (g k - g' k) < L * 1 := by linarith
  have a2 : (L : ℤ) * (g' k - g k) < L * 1 := by linarith
  have b1 := lt_of_mul_lt_mul_left a1 hL
  have b2 := lt_of_mul_lt_mul_left a2 hL
  omega

/-- Every edge of slab `i` lies in a block of it, for `L ≥ 1`. -/
theorem exists_mem_block (hL : 1 ≤ L) {i : ℕ} (o' : Fin m → ℤ) {e : Sym2 (Vertex m)}
    (he : e ∈ slabEdges (((i : ℤ) - 1) * n) ((i : ℤ) * n)) :
    ∃ g : Fin m → ℤ, e ∈ block n w L t i o' g := by
  refine ⟨fun k => (fineIndex w t (edgeMid e) k - o' k) / L, he, fun k => ?_⟩
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have h1 := Int.mul_ediv_add_emod (fineIndex w t (edgeMid e) k - o' k) L
  have h2 := Int.emod_nonneg (fineIndex w t (edgeMid e) k - o' k) hL'.ne'
  have h3 := Int.emod_lt_of_pos (fineIndex w t (edgeMid e) k - o' k) hL'
  constructor <;> linarith

open Classical in
/-- The block index of an edge: `some (i, g)` if it lies in the block `g` of slab `i + 1`,
`i < K`, and `none` if it lies in no such block. -/
noncomputable def cellOf (e : Edge m) : Option (Fin K × (Fin m → ℤ)) :=
  if h : ∃ c : Fin K × (Fin m → ℤ), e.1 ∈ blockCell n w L K t o (some c) then some h.choose
  else none

variable (n w L K t o) in
/-- The block index of an edge is `c` exactly when the edge lies in the cell `c`. -/
theorem cellOf_eq_iff (e : Edge m) (c : Option (Fin K × (Fin m → ℤ))) :
    cellOf (n := n) (w := w) (L := L) (K := K) (t := t) (o := o) e = c ↔
      e.1 ∈ blockCell n w L K t o c := by
  classical
  unfold cellOf
  split_ifs with h
  · have hc := h.choose_spec
    rcases c with _ | c
    · simp only [reduceCtorEq, false_iff]
      intro hn
      exact hn _ hc
    · simp only [Option.some.injEq]
      constructor
      · rintro rfl; exact hc
      · intro hc'
        obtain ⟨h1, h2⟩ := eq_of_mem_block_of_mem_block hc hc'
        exact Prod.ext (Fin.ext h1) h2
  · push Not at h
    rcases c with _ | c
    · simp only [true_iff]
      exact fun c => h c
    · simp only [reduceCtorEq, false_iff]
      exact h c

end Blocks

end CurvatureVariance.Paper.Gain.LabelResidual
