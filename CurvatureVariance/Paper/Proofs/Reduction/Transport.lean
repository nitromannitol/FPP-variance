/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.Symmetry
public import CurvatureVariance.Statements.Curvature.AssumptionCAt
public import CurvatureVariance.Statements.Curvature.AssumptionCWith
public import CurvatureVariance.Statements.Space.FloorVertex
public import Mathlib.Probability.Moments.Variance
import CurvatureVariance.Infra.FPP.Walks

/-!
# Transport along an automorphism of the lattice

The change of coordinates at the beginning of Section `sec:prelim`, in general form. An automorphism
`Φ` of the lattice graph that fixes the origin, is additive, and acts on points by a linear isometry
`A` (`point (Φ z) = A (point z)`) transports the objects of the main theorem:

* `transportNorm μ A`: the norm `μ ∘ A⁻¹` in the new coordinates;
* `isTimeConstant_transportNorm`: it is a time constant of the same i.i.d. law. The proof
  transports the weights along `Φ`, which preserves their law; no invariance of `μ` is used;
* `isCompl_map`, `assumptionCAt_transportNorm`: transversality and `AssumptionCAt` at `ξ` and `H`
  give the same at `A ξ` and `A H`, with `ℓ ∘ A⁻¹` and `q ∘ A⁻¹`;
* `assumptionCWith_transportNorm`: Assumption (Curv) with the constants `δ, r, M, c` at `ξ` on
  `ξ^⊥`
  gives the same at `A ξ` on `(A ξ)^⊥ = A(ξ^⊥)`, with the same constants;
* `evariance_map_eq`, `evariance_passageTime_apply`: `Var T(0, x) = Var T(0, Φ x)`;
* `norm_point_floorVertex_sub_le`: `|⌊x⌋ − x| ≤ √d`.

The signed permutations of the coordinates (`Infra.FPP.signedPermIso`, `Infra.FPP.signedPermPt`)
are such automorphisms: `signedPermIsometry` and `point_signedPermIso`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Reduction

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ## Coordinates and norms -/

/-- The squared norm of a point is the sum of the squares of its coordinates. -/
theorem norm_sq_eq_sum_ptCoord (x : Pt m) : ‖x‖ ^ 2 = ∑ k, ptCoord x k ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, Fintype.sum_option, Real.norm_eq_abs, sq_abs,
    EuclideanSpace.real_norm_sq_eq]
  rfl

/-- The floor of a point is within `√d` of it: `|⌊x⌋ − x| ≤ √(m + 1)`. -/
theorem norm_point_floorVertex_sub_le (x : Pt m) :
    ‖point (floorVertex x) - x‖ ≤ Real.sqrt ((m : ℝ) + 1) := by
  have hc : ptCoord (point (floorVertex x) - x) = fun k => (⌊ptCoord x k⌋ : ℝ) - ptCoord x k := by
    funext k
    cases k <;> rfl
  have hsq : ‖point (floorVertex x) - x‖ ^ 2 ≤ (m : ℝ) + 1 := by
    rw [norm_sq_eq_sum_ptCoord, hc]
    calc ∑ k, ((⌊ptCoord x k⌋ : ℝ) - ptCoord x k) ^ 2 ≤ ∑ _k : Option (Fin m), (1 : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have h1 := Int.floor_le (ptCoord x k)
          have h2 := Int.lt_floor_add_one (ptCoord x k)
          nlinarith
      _ = (m : ℝ) + 1 := by simp
  simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt hsq

/-! ## Signed permutations of the coordinates -/

section Signs

variable {σ : Equiv.Perm (Option (Fin m))} {ε : Option (Fin m) → ℝ}

theorem ptCoord_signedPermPt (σ : Equiv.Perm (Option (Fin m))) (ε : Option (Fin m) → ℝ)
    (x : Pt m) : ptCoord (signedPermPt σ ε x) = fun k => ε k * ptCoord x (σ k) := by
  simp only [signedPermPt, LinearMap.coe_mk, AddHom.coe_mk, ptCoord_ptOfCoord]

theorem signedPermPt_symm_apply (hε : ∀ k, ε k * ε k = 1) (x : Pt m) :
    signedPermPt σ.symm (fun j => ε (σ.symm j)) (signedPermPt σ ε x) = x := by
  apply ptCoord_injective
  funext j
  simp [ptCoord_signedPermPt, ← mul_assoc, hε]

theorem signedPermPt_apply_symm (hε : ∀ k, ε k * ε k = 1) (x : Pt m) :
    signedPermPt σ ε (signedPermPt σ.symm (fun j => ε (σ.symm j)) x) = x := by
  apply ptCoord_injective
  funext k
  simp [ptCoord_signedPermPt, ← mul_assoc, hε]

/-- A signed permutation of the coordinates preserves the Euclidean norm. -/
theorem norm_signedPermPt (hε : ∀ k, ε k * ε k = 1) (x : Pt m) :
    ‖signedPermPt σ ε x‖ = ‖x‖ := by
  have hε2 : ∀ k, ε k ^ 2 = 1 := fun k => by rw [sq, hε]
  have hsq : ‖signedPermPt σ ε x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_sum_ptCoord, norm_sq_eq_sum_ptCoord, ptCoord_signedPermPt]
    simp only [mul_pow, hε2, one_mul]
    exact Equiv.sum_comp σ (fun k => ptCoord x k ^ 2)
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- The signed permutation `x ↦ (ε_k x_{σ k})_k` of `ℝ^d` with signs `ε_k = ±1`, as a linear
isometry equivalence. -/
noncomputable def signedPermIsometry (σ : Equiv.Perm (Option (Fin m))) (ε : Option (Fin m) → ℝ)
    (hε : ∀ k, ε k * ε k = 1) : Pt m ≃ₗᵢ[ℝ] Pt m where
  toLinearEquiv := LinearEquiv.ofLinearMap (signedPermPt σ ε)
    (signedPermPt σ.symm fun j => ε (σ.symm j))
    (LinearMap.ext fun x => signedPermPt_apply_symm hε x)
    (LinearMap.ext fun x => signedPermPt_symm_apply hε x)
  norm_map' := norm_signedPermPt hε

/-- The lattice automorphism `signedPermIso` acts on points by `signedPermPt`. -/
theorem point_signedPermIso {s : Option (Fin m) → ℤ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (z : Vertex m) :
    point (signedPermIso (σ := σ) hs z) = signedPermPt σ (fun k => (s k : ℝ)) (point z) := by
  apply ptCoord_injective
  funext k
  show ptCoord (point (signedPerm σ s z)) k = _
  simp [ptCoord_point, vertexCoord_signedPerm, ptCoord_signedPermPt]

theorem signedPermIso_zero {s : Option (Fin m) → ℤ} (hs : ∀ k, s k = 1 ∨ s k = -1) :
    signedPermIso (σ := σ) hs 0 = 0 :=
  signedPerm_zero σ s

theorem signedPermIso_add {s : Option (Fin m) → ℤ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (z w : Vertex m) :
    signedPermIso (σ := σ) hs (z + w) =
      signedPermIso (σ := σ) hs z + signedPermIso (σ := σ) hs w :=
  signedPerm_add σ s z w

end Signs

/-! ## Transport of the time constant, of the curvature hypotheses and of the variance -/

/-- The variance of `X` under an image measure. -/
theorem evariance_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {f : Ω → Ω'} (hf : Measurable f) {X : Ω' → ℝ} (hX : Measurable X) :
    evariance X (P.map f) = evariance (X ∘ f) P := by
  rw [evariance, evariance, integral_map hf.aemeasurable hX.aestronglyMeasurable,
    lintegral_map ((hX.sub_const _).enorm.pow_const _) hf]
  rfl

/-- The norm `μ ∘ A⁻¹`: the norm `μ` in the coordinates given by `A`. -/
noncomputable def transportNorm (μ : PtNorm m) (A : Pt m ≃ₗᵢ[ℝ] Pt m) : PtNorm m :=
  ⟨μ.1.comp A.symm.toLinearEquiv.toLinearMap, fun y hy =>
    A.symm.map_eq_zero_iff.1 (μ.2 (A.symm y) hy)⟩

theorem transportNorm_apply (μ : PtNorm m) (A : Pt m ≃ₗᵢ[ℝ] Pt m) (x : Pt m) :
    (transportNorm μ A).1 x = μ.1 (A.symm x) :=
  rfl

/-- An additive automorphism commutes with the multiples. -/
theorem apply_nsmul (Φ : latticeGraph m ≃g latticeGraph m) (hΦ0 : Φ 0 = 0)
    (hΦadd : ∀ z w, Φ (z + w) = Φ z + Φ w) (n : ℕ) (w : Vertex m) : Φ (n • w) = n • Φ w := by
  induction n with
  | zero => simp [hΦ0]
  | succ n ih => rw [succ_nsmul, succ_nsmul, hΦadd, ih]

/-- **The time constant in the new coordinates**: if `Φ` acts on points by `A`, then `μ ∘ A⁻¹` is
a time constant of the same law. The weights are transported along `Φ`, which preserves their law
(`IsIIDWeights.measurePreserving_transport`), and `T_{transport Φ ω}(0, n Φ⁻¹ z) = T_ω(0, n z)`.
-/
theorem isTimeConstant_transportNorm {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} (hP : IsIIDWeights P F) {μ : PtNorm m} (hμ : IsTimeConstant P μ)
    (Φ : latticeGraph m ≃g latticeGraph m) (hΦ0 : Φ 0 = 0)
    (hΦadd : ∀ z w, Φ (z + w) = Φ z + Φ w) (A : Pt m ≃ₗᵢ[ℝ] Pt m) (hA : ∀ z, point (Φ z) = A (point z)) :
    IsTimeConstant P (transportNorm μ A) := by
  have hA' : ∀ z, point (Φ.symm z) = A.symm (point z) := fun z => by
    rw [← A.symm_apply_apply (point (Φ.symm z)), ← hA, RelIso.apply_symm_apply]
  intro z
  have hΨ := (IsIIDWeights.measurePreserving_transport hP Φ).quasiMeasurePreserving.ae
    (hμ (Φ.symm z))
  filter_upwards [hΨ] with ω hω
  have e : (fun n : ℕ => (passageTime (transport Φ ω) 0 (n • Φ.symm z) : ℝ) / n) =
      fun n : ℕ => (passageTime ω 0 (n • z) : ℝ) / n := by
    funext n
    rw [passageTime_transport, hΦ0, apply_nsmul Φ hΦ0 hΦadd, RelIso.apply_symm_apply]
  rw [e, hA'] at hω
  exact hω

/-- **The variance in the new coordinates**: `Var T(0, x) = Var T(0, Φ x)`, since transporting the
weights along `Φ⁻¹` preserves their law and `T_{transport Φ⁻¹ ω}(0, Φ x) = T_ω(0, x)`. -/
theorem evariance_passageTime_apply {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} (hP : IsIIDWeights P F) (Φ : latticeGraph m ≃g latticeGraph m)
    (hΦ0 : Φ 0 = 0) (x : Vertex m) :
    evariance (fun ω => (passageTime ω 0 x : ℝ)) P =
      evariance (fun ω => (passageTime ω 0 (Φ x) : ℝ)) P := by
  have hΦ0' : Φ.symm 0 = 0 := by rw [RelIso.symm_apply_eq, hΦ0]
  have hg := IsIIDWeights.measurePreserving_transport hP Φ.symm
  have hX := measurable_passageTime_real (0 : Vertex m) (Φ x)
  have e : (fun ω => (passageTime ω 0 x : ℝ)) =
      (fun ω => (passageTime ω 0 (Φ x) : ℝ)) ∘ transport Φ.symm := by
    funext ω
    simp only [Function.comp_apply, passageTime_transport, hΦ0', RelIso.symm_apply_apply]
  rw [e, ← evariance_map_eq hg.measurable hX, hg.map_eq]

/-- Transversality transports along a linear isometry: `IsCompl (span {ξ}) H` gives
`IsCompl (span {A ξ}) (A H)`. -/
theorem isCompl_map {ξ : Pt m} {H : Submodule ℝ (Pt m)}
    (hH : IsCompl (Submodule.span ℝ {ξ}) H) (A : Pt m ≃ₗᵢ[ℝ] Pt m) :
    IsCompl (Submodule.span ℝ {A ξ}) (H.map (A.toLinearEquiv : Pt m →ₗ[ℝ] Pt m)) := by
  have h := (Submodule.orderIsoMapComap A.toLinearEquiv).isCompl hH
  rw [Submodule.orderIsoMapComap_apply, Submodule.orderIsoMapComap_apply, Submodule.map_span,
    Set.image_singleton] at h
  exact h

/-- **`AssumptionCAt` in the new coordinates**: the expansion of `μ` at `ξ` along `H` gives that of
`μ ∘ A⁻¹` at `A ξ` and `A H`, with the same exponent, radius and constant, and with `ℓ ∘ A⁻¹`
and `q ∘ A⁻¹`. -/
theorem assumptionCAt_transportNorm {μ : PtNorm m} {ξ : Pt m} {H : Submodule ℝ (Pt m)}
    (hC : AssumptionCAt μ ξ H) (A : Pt m ≃ₗᵢ[ℝ] Pt m) :
    AssumptionCAt (transportNorm μ A) (A ξ) (H.map (A.toLinearEquiv : Pt m →ₗ[ℝ] Pt m)) := by
  obtain ⟨δ, hδ0, hδ1, r, hr, M, hM, ℓ, q, hq, hbd⟩ := hC
  set e := (A.toLinearEquiv.submoduleMap H).symm with hedef
  have he : ∀ h, ((e h : H) : Pt m) = A.symm h := fun h => by
    have h1 := congrArg Subtype.val ((A.toLinearEquiv.submoduleMap H).apply_symm_apply h)
    rw [LinearEquiv.submoduleMap_apply] at h1
    rw [← hedef] at h1
    rw [← h1]
    exact (A.symm_apply_apply _).symm
  have hn : ∀ h, ‖e h‖ = ‖h‖ := fun h => by
    show ‖((e h : H) : Pt m)‖ = ‖(h : Pt m)‖
    rw [he, LinearIsometryEquiv.norm_map]
  refine ⟨δ, hδ0, hδ1, r, hr, M, hM, ℓ.comp e.toLinearMap, q.comp e.toLinearMap, ?_, ?_⟩
  · intro h hh
    exact hq (e h) ((LinearEquiv.map_ne_zero_iff e).2 hh)
  · intro h hh
    have hb := hbd (e h) ((hn h).trans_le hh)
    rw [hn, he] at hb
    have h1 : (transportNorm μ A).1 (A ξ + h) = μ.1 (ξ + A.symm h) := by
      rw [transportNorm_apply, map_add, A.symm_apply_apply]
    have h2 : (transportNorm μ A).1 (A ξ) = μ.1 ξ := by
      rw [transportNorm_apply, A.symm_apply_apply]
    rw [h1, h2]
    exact hb

/-- **Assumption (Curv) with constants in the new coordinates**: (Curv) for `μ` at `ξ` on `ξ^⊥` with
the constants `δ, r, M, c` gives (Curv) for `μ ∘ A⁻¹` at `A ξ` on `(A ξ)^⊥` with the same constants,
and with `ℓ ∘ A⁻¹` and `q ∘ A⁻¹`: `A` maps `ξ^⊥` onto `(A ξ)^⊥` isometrically. -/
theorem assumptionCWith_transportNorm {μ : PtNorm m} {ξ : Pt m} {δ r M c : ℝ}
    (hC : AssumptionCWith μ ξ δ r M c) (A : Pt m ≃ₗᵢ[ℝ] Pt m) :
    AssumptionCWith (transportNorm μ A) (A ξ) δ r M c := by
  obtain ⟨ℓ, q, hq, hbd⟩ := hC
  have hmap : (Submodule.span ℝ {ξ})ᗮ.map (A.toLinearEquiv : Pt m →ₗ[ℝ] Pt m) =
      (Submodule.span ℝ {A ξ})ᗮ := by
    rw [Submodule.map_orthogonal_equiv, Submodule.map_span, Set.image_singleton]
    rfl
  set e := (A.toLinearEquiv.ofSubmodules _ _ hmap).symm with hedef
  have he : ∀ h, ((e h : (Submodule.span ℝ {ξ})ᗮ) : Pt m) = A.symm h := fun h => rfl
  have hn : ∀ h, ‖e h‖ = ‖h‖ := fun h => by
    show ‖((e h : (Submodule.span ℝ {ξ})ᗮ) : Pt m)‖ = ‖(h : Pt m)‖
    rw [he, LinearIsometryEquiv.norm_map]
  refine ⟨ℓ.comp e.toLinearMap, q.comp e.toLinearMap, fun h => ?_, fun h hh => ?_⟩
  · have hc := hq (e h)
    rw [hn] at hc
    exact hc
  · have hb := hbd (e h) ((hn h).trans_le hh)
    rw [hn, he] at hb
    have h1 : (transportNorm μ A).1 (A ξ + h) = μ.1 (ξ + A.symm h) := by
      rw [transportNorm_apply, map_add, A.symm_apply_apply]
    have h2 : (transportNorm μ A).1 (A ξ) = μ.1 ξ := by
      rw [transportNorm_apply, A.symm_apply_apply]
    rw [h1, h2]
    exact hb

end CurvatureVariance.Paper.Proofs.Reduction
