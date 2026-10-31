/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Labels
public import CurvatureVariance.Paper.Proofs.Gain.FAGeometry
public import CurvatureVariance.Paper.Proofs.Gain.Common
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Linarith

/-!
# The translated mesh of Lemma `lem:labels`

Step 2 of the proof of [AB26, Lemma 6.2], as the proof of Lemma `lem:labels` changes it: "let
`(u_g, v_g)` be a point of a mesh of `Γ_G` of spacing `g(nQ_n)^{1/2}` with
`|u − u_g|, |v − v_g| ≤ g(nQ_n)^{1/2}`, chosen so that translating `G`, `u` and `v` by a vector of
`{0} × wLℤ^{d−1}` translates `(u_g, v_g)` by the same vector".

The mesh is built on the reference block `g = 0` and translated, so that the translation holds
exactly:

* `blockCoord_add_blockShift`, `meshIndex_add_blockShift`: the coordinates relative to a block, and
  the mesh index of `FAGeometry`, do not change when the block and the point move by
  `z = (0, wLm')`.
* `add_blockShift_mem_subcubeFace_iff`, `add_blockShift_mem_blockFacePairs_iff`: the faces of `G + z`
  are the translates of those of `G`, so `Γ_{G+z} = Γ_G + z`.
* `map_add_blockShift_mem_block_iff`: the block `(o, g + m')` is the translate of the block `(o, g)`.
* `blockRep`: the representative of a mesh cell, the representative `meshRep` of the reference block
  translated to the block `g`; `blockRep_add` is the clause of the paper. `blockRep_mem` and
  `norm_sub_blockRep_le`: it is a point of the face, at distance at most `m w τ` from the point.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### The vector `z = (0, wLm')` -/

@[simp] theorem blockShift_fst (w L : ℕ) (m' : Fin m → ℤ) : (blockShift w L m').1 = 0 := rfl

theorem blockShift_snd_apply (w L : ℕ) (m' : Fin m → ℤ) (k : Fin m) :
    (blockShift w L m').2 k = (w : ℤ) * (L : ℤ) * m' k := by
  simp only [blockShift, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem blockShift_add (w L : ℕ) (a b : Fin m → ℤ) :
    blockShift w L (a + b) = blockShift w L a + blockShift w L b := by
  refine Prod.ext (by simp) ?_
  funext k
  simp only [Prod.snd_add, Pi.add_apply, blockShift_snd_apply]
  ring

/-- `z = (0, wLm')` in the form of `map_add_mem_block_iff`. -/
theorem blockShift_eq (w L : ℕ) (m' : Fin m → ℤ) :
    blockShift w L m' = ((0 : ℤ), fun k => (w : ℤ) * ((L : ℤ) * m' k)) := by
  refine Prod.ext rfl ?_
  funext k
  rw [blockShift_snd_apply, mul_assoc]

/-- **Blocks are translates of each other**: the vector `z = (0, wLm')` moves the block `(o, g)` of
a slab onto the block `(o, g + m')`. -/
theorem map_add_blockShift_mem_block_iff {n w L : ℕ} (hw : 0 < w) (t : EuclideanSpace ℝ (Fin m))
    (i : ℕ) (o g m' : Fin m → ℤ) (e : Sym2 (Vertex m)) :
    Sym2.map (· + blockShift w L m') e ∈ block n w L t i o (g + m') ↔ e ∈ block n w L t i o g := by
  rw [blockShift_eq]
  exact map_add_mem_block_iff hw t i o g m' e

/-! ### Coordinates relative to a block -/

theorem blockCoord_add_blockShift (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g m' : Fin m → ℤ)
    (x : Vertex m) (k : Fin m) :
    blockCoord w L t o (g + m') (x + blockShift w L m') k = blockCoord w L t o g x k := by
  simp only [blockCoord, Prod.fst_add, blockShift_fst, add_zero, Prod.snd_add, Pi.add_apply,
    blockShift_snd_apply]
  push_cast
  ring

theorem meshIndex_add_blockShift (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g m' : Fin m → ℤ)
    (τ : ℝ) (x : Vertex m) :
    meshIndex w L t o (g + m') τ (x + blockShift w L m') = meshIndex w L t o g τ x := by
  funext k
  simp only [meshIndex, blockCoord_add_blockShift]

/-- **The faces of `G + z` are the translates of those of `G`.** -/
theorem add_blockShift_mem_subcubeFace_iff {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {o g m' : Fin m → ℤ} {h : ℤ} {x : Vertex m} :
    x + blockShift w L m' ∈ subcubeFace w L t o (g + m') h ↔ x ∈ subcubeFace w L t o g h := by
  rw [mem_subcubeFace_iff, mem_subcubeFace_iff]
  simp only [Prod.fst_add, blockShift_fst, add_zero, blockCoord_add_blockShift]

/-- **`Γ_{G+z} = Γ_G + z`.** -/
theorem add_blockShift_mem_blockFacePairs_iff {n w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {i : ℕ}
    {o g m' : Fin m → ℤ} {u v : Vertex m} :
    (u + blockShift w L m', v + blockShift w L m') ∈ blockFacePairs n w L t i o (g + m') ↔
      (u, v) ∈ blockFacePairs n w L t i o g := by
  simp only [blockFacePairs, mem_prod, add_blockShift_mem_subcubeFace_iff]

/-! ### The translated mesh -/

/-- The representative of the mesh cell `a` in the face at height `h` of the block `g`: the
representative of the reference block `g = 0`, translated to the block `g`. -/
noncomputable def blockRep (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ) (τ : ℝ)
    (h : ℤ) (a : Fin m → ℤ) : Vertex m :=
  meshRep w L t o 0 τ h a + blockShift w L g

/-- **The mesh moves with the block** (the proof of Lemma `lem:labels`). -/
theorem blockRep_add (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g m' : Fin m → ℤ) (τ : ℝ)
    (h : ℤ) (a : Fin m → ℤ) :
    blockRep w L t o (g + m') τ h a = blockRep w L t o g τ h a + blockShift w L m' := by
  simp only [blockRep, blockShift_add, add_assoc]

/-- A point of a face of the block `g`, moved to the reference block. -/
theorem sub_blockShift_mem_subcubeFace {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ}
    {h : ℤ} {x : Vertex m} (hx : x ∈ subcubeFace w L t o g h) :
    x - blockShift w L g ∈ subcubeFace w L t o 0 h := by
  have hx' : (x - blockShift w L g) + blockShift w L g ∈ subcubeFace w L t o (0 + g) h := by
    rwa [sub_add_cancel, zero_add]
  exact add_blockShift_mem_subcubeFace_iff.mp hx'

/-- The mesh index of a point of the block `g`, on the reference block. -/
theorem meshIndex_sub_blockShift (w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o g : Fin m → ℤ)
    (τ : ℝ) (x : Vertex m) :
    meshIndex w L t o 0 τ (x - blockShift w L g) = meshIndex w L t o g τ x := by
  have h := meshIndex_add_blockShift w L t o 0 g τ (x - blockShift w L g)
  rw [sub_add_cancel, zero_add] at h
  exact h.symm

/-- The representative of the cell of a face point is a face point. -/
theorem blockRep_mem {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ} {τ : ℝ} {h : ℤ}
    {x : Vertex m} (hx : x ∈ subcubeFace w L t o g h) :
    blockRep w L t o g τ h (meshIndex w L t o g τ x) ∈ subcubeFace w L t o g h := by
  have hx₀ := sub_blockShift_mem_subcubeFace hx
  have hs := (meshRep_spec (τ := τ) hx₀).1
  rw [meshIndex_sub_blockShift] at hs
  have h' := add_blockShift_mem_subcubeFace_iff (m' := g).mpr hs
  rwa [zero_add] at h'

/-- **Face points are close to their representatives**: `|x − rep(x)| ≤ m w τ`. -/
theorem norm_sub_blockRep_le {w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ} {τ : ℝ}
    {h : ℤ} (hw : 0 < w) (hτ : 0 < τ) {x : Vertex m} (hx : x ∈ subcubeFace w L t o g h) :
    ‖point x - point (blockRep w L t o g τ h (meshIndex w L t o g τ x))‖ ≤ m * (w * τ) := by
  have hx₀ := sub_blockShift_mem_subcubeFace hx
  have hb := norm_sub_meshRep_le (τ := τ) hw hτ hx₀
  rw [meshIndex_sub_blockShift] at hb
  have e : point x - point (blockRep w L t o g τ h (meshIndex w L t o g τ x)) =
      point (x - blockShift w L g) - point (meshRep w L t o 0 τ h (meshIndex w L t o g τ x)) := by
    have h1 := point_add (meshRep w L t o 0 τ h (meshIndex w L t o g τ x)) (blockShift w L g)
    have h2 := point_add (x - blockShift w L g) (blockShift w L g)
    rw [sub_add_cancel] at h2
    rw [blockRep, h1, h2]
    abel
  rw [e]
  exact hb

end CurvatureVariance.Paper.Gain
