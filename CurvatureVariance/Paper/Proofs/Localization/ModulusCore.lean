/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusSupport
public import CurvatureVariance.Paper.Proofs.Localization.ModulusMeasure
public import CurvatureVariance.Paper.Contracts.Moments
import CurvatureVariance.Infra.FPP.Walks
import CurvatureVariance.Infra.Os.Maximum
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp

/-!
# The combination steps of the continuity estimate (Lemma `lem:modulus`)

For the proof of Lemma `lem:modulus`, equation `eq:modulus`:

* the grid pairs of cubes covering two transverse boxes satisfy `IsCubePair`
  (`isCubePair_grid`);
* vertices of geodesics between the cubes on `{R ≤ 1/g}` lie in the transverse boxes
  (`abs_offset_le_of_locRadius_le`);
* the crude bound `|T(u,v) − T(u₂,v₂) − P·(v − u − v₂ + u₂)| ≤ 2X + F` from `|T − μ| ≤ X` and
  `0 ≤ f ≤ F` on the pair of cubes (`abs_modulus_le_of_abs_le`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-! ## Finite maxima of pair bounds -/

/-- The grid pairs of cubes covering two transverse boxes at distance `L` (centres differing by
`L t`) are cube pairs with slope `t + (s₀/L)(k' − k)`. -/
theorem isCubePair_grid (M : Model m) {K : ℕ} {A : ℝ} {L : ℕ} (hL : 0 < L) {s₀ : ℝ}
    (hs₀ : 0 ≤ s₀) (hs₀W : s₀ ≤ W M K A L) (p : ℤ) (z t : EuclideanSpace ℝ (Fin m))
    (k k' : Fin m → ℤ) :
    IsCubePair M K A L 1 (t + (s₀ / L) • (transversePoint k' - transversePoint k))
      (transverseCube p (z + s₀ • transversePoint k) s₀)
      (transverseCube (p + L) (z + (L : ℝ) • t + s₀ • transversePoint k') s₀) := by
  refine ⟨p, z + s₀ • transversePoint k, z + (L : ℝ) • t + s₀ • transversePoint k', s₀, s₀,
    rfl, rfl, hs₀, by rwa [one_mul], hs₀, by rwa [one_mul], ?_⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have : z + (L : ℝ) • t + s₀ • transversePoint k' - (z + s₀ • transversePoint k) -
      (L : ℝ) • (t + (s₀ / L) • (transversePoint k' - transversePoint k)) = 0 := by
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hL', smul_sub]
    abel
  rw [this, norm_zero]
  positivity

/-! ## Vertices of geodesics on `{R ≤ 1/g}` -/

/-- On `{R ≤ r}`, a vertex `x` of a geodesic from `u ∈ transverseCube p c a` to
`v ∈ transverseCube (p + ℓ) c' a'` with `x₁ = p + L` has transverse coordinates within
`(1 + T) r W + max a a'/2 + 2√d` of the line of slope `t` through `c`, if `‖t‖ ≤ T`. -/
theorem abs_offset_le_of_locRadius_le {ω : Config m} {p : ℤ} {ℓ L : ℤ}
    {c c' t : EuclideanSpace ℝ (Fin m)} {a a' Wl r T : ℝ} (hW : 0 < Wl) (hr : 0 ≤ r)
    (hcc : ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1)) (ht : ‖t‖ ≤ T)
    (hR : locRadius ω (transverseCube p c a) (transverseCube (p + ℓ) c' a') Wl ≤
      ENNReal.ofReal r)
    {u v : Vertex m} (hu : u ∈ transverseCube p c a) (hv : v ∈ transverseCube (p + ℓ) c' a')
    {γ : (latticeGraph m).Walk u v} (hγ : IsGeodesic ω γ) {x : Vertex m} (hx : x ∈ γ.support)
    (hx1 : x.1 = p + L) (j : Fin m) :
    |(x.2 j : ℝ) - (c j + (L : ℝ) * t j)| ≤
      (1 + T) * (r * Wl) + max a a' / 2 + 2 * Real.sqrt ((m : ℝ) + 1) := by
  have hd := infDist_le_of_locRadius_le hW hr hR hu hv hγ hx
  have hcomp : IsCompact (segment ℝ (point u) (point v)) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨y, hy, hyd⟩ := hcomp.exists_infDist_eq_dist
    ⟨point u, left_mem_segment ℝ _ _⟩ (point x)
  rw [hyd, dist_eq_norm] at hd
  exact abs_offset_le hu hv hcc ht hx1 hy hd j

/-! ## The deterministic comparison -/

/-- The crude bound: if `|T − μ| ≤ X` on `I × I'` and `0 ≤ f ≤ F` there, then
`|T(u,v) − T(u₂,v₂) − P·(v − u − v₂ + u₂)| ≤ 2X + F`. -/
theorem abs_modulus_le_of_abs_le {T : Vertex m → Vertex m → ℝ} (μ : PtNorm m) (P : Pt m)
    {I I' : Set (Vertex m)} {X F : ℝ}
    (hX : ∀ u ∈ I, ∀ v ∈ I', |T u v - μ.1 (point v - point u)| ≤ X)
    (hF : ∀ u ∈ I, ∀ v ∈ I', 0 ≤ supportExcess μ P (point v - point u) ∧
      supportExcess μ P (point v - point u) ≤ F)
    {u u₂ v v₂ : Vertex m} (hu : u ∈ I) (hu₂ : u₂ ∈ I) (hv : v ∈ I') (hv₂ : v₂ ∈ I') :
    |T u v - T u₂ v₂ - inner ℝ P (point v - point u - point v₂ + point u₂)| ≤ 2 * X + F := by
  have hP : inner ℝ P (point v - point u - point v₂ + point u₂) =
      inner ℝ P (point v - point u) - inner ℝ P (point v₂ - point u₂) := by
    rw [← inner_sub_right]; congr 1; abel
  have a1 := abs_le.mp (hX u hu v hv)
  have a2 := abs_le.mp (hX u₂ hu₂ v₂ hv₂)
  have f1 := hF u hu v hv
  have f2 := hF u₂ hu₂ v₂ hv₂
  unfold supportExcess at f1 f2
  rw [hP, abs_le]
  constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, f1.1, f1.2, f2.1, f2.2]

end CurvatureVariance.Paper.Localization.Modulus
