/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Inputs.IsLatticeSymmetric
public import CurvatureVariance.Statements.Space.EOne
public import CurvatureVariance.Infra.FPP.TimeConstant

/-!
# Lattice symmetries of the time constant

The symmetries of `ℤ^d` that fix the origin are the signed permutations of the coordinates. With
the coordinates of `ℝ^d` indexed by `Option (Fin m)` (`none` longitudinal, `some j` transverse):

* the coordinates `ptCoord`, `ptOfCoord` and the predicate `IsLatticeSymmetric` are the
  definitions `CurvatureVariance.ptCoord`, `CurvatureVariance.ptOfCoord` and
  `CurvatureVariance.IsLatticeSymmetric`;
* `pos_iff_forall_pos_of_isLatticeSymmetric` ([ADH, Theorem 2.6]): a subadditive, absolutely
  homogeneous, lattice-symmetric `μ` is positive at `e₁` iff it is positive off the origin. If
  `x_k ≠ 0`, the reflection `x'` of `x` in all coordinates but `k` has `μ(x') = μ(x)` and
  `x + x' = 2 x_k e_k`, so `2 |x_k| μ(e₁) = μ(2 x_k e_k) ≤ 2 μ(x)`;
* the signed permutations `signedPerm` of `ℤ^d`, which are automorphisms of the lattice graph
  (`signedPermIso`), and the transport of the weights along a graph automorphism (`transport`),
  which preserves passage times and the law of independent identically distributed weights
  (`passageTime_transport`, `IsIIDWeights.measurePreserving_transport`), and the signed
  permutations `signedPermPt` of `ℝ^d`.

The transport of weights along a graph automorphism follows the translations of
`CurvatureVariance.Infra.FPP.Translation` and `IsIIDWeights.measurePreserving_translate` of
`CurvatureVariance.Infra.FPP.Model`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Coordinates of `ℝ^d` -/

@[simp] theorem ptCoord_ptOfCoord (c : Option (Fin m) → ℝ) : ptCoord (ptOfCoord c) = c := by
  funext k; cases k <;> rfl

@[simp] theorem ptOfCoord_ptCoord (x : Pt m) : ptOfCoord (ptCoord x) = x := rfl

theorem ptCoord_injective : Function.Injective (ptCoord (m := m)) := fun x y h => by
  rw [← ptOfCoord_ptCoord x, h, ptOfCoord_ptCoord]

@[simp] theorem ptCoord_add (x y : Pt m) : ptCoord (x + y) = ptCoord x + ptCoord y := by
  funext k; cases k <;> simp [ptCoord]

@[simp] theorem ptCoord_smul (c : ℝ) (x : Pt m) : ptCoord (c • x) = c • ptCoord x := by
  funext k; cases k <;> simp [ptCoord]

@[simp] theorem ptCoord_zero : ptCoord (0 : Pt m) = 0 := by
  funext k; cases k <;> simp [ptCoord]

/-- The coordinates of `e₁`. -/
theorem ptCoord_e₁ : ptCoord (e₁ : Pt m) = Pi.single none 1 := by
  funext k; cases k <;> simp [ptCoord, e₁]

theorem e₁_ne_zero : (e₁ : Pt m) ≠ 0 := fun h => by
  have := congrFun (congrArg ptCoord h) none
  simp [ptCoord_e₁] at this

/-! ### Positivity -/

/-- **[ADH, Theorem 2.6]**: for a function `μ` on `ℝ^d` that is subadditive, satisfies
`μ(cx) = |c| μ(x)`, and is invariant under the symmetries of `ℤ^d` that fix the origin,
`μ(e₁) > 0` if and only if `μ(x) > 0` for all `x ≠ 0` (continuity is not needed). -/
theorem pos_iff_forall_pos_of_isLatticeSymmetric {m : ℕ} (μ : Pt m → ℝ)
    (hsub : ∀ x y, μ (x + y) ≤ μ x + μ y) (hhom : ∀ (c : ℝ) x, μ (c • x) = |c| * μ x)
    (hsym : IsLatticeSymmetric μ) (_hcont : Continuous μ) :
    0 < μ e₁ ↔ ∀ x, x ≠ 0 → 0 < μ x := by
  classical
  refine ⟨fun h1 x hx => ?_, fun h => h _ e₁_ne_zero⟩
  obtain ⟨k, hk⟩ : ∃ k, ptCoord x k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (ptCoord_injective (by funext k; simp [hcon k]))
  -- the unit vector `e_k` has the value `μ(e₁)`
  have hek : μ (ptOfCoord (Pi.single k 1)) = μ e₁ := by
    have h := hsym (Equiv.swap k none) (fun _ => 1) (fun _ => Or.inl rfl) e₁
    have e : (ptOfCoord fun j => (fun _ => (1 : ℝ)) j * ptCoord e₁ (Equiv.swap k none j)) =
        ptOfCoord (Pi.single k 1) := by
      congr 1
      funext j
      by_cases hj : j = k
      · subst hj; simp [ptCoord_e₁]
      · have : Equiv.swap k none j ≠ none := fun h' => hj (by
          simpa using congrArg (Equiv.swap k none) h')
        simp [ptCoord_e₁, hj, this]
    rw [← e, h]
  -- the reflection of `x` in all coordinates but `k`
  set ε : Option (Fin m) → ℝ := fun j => if j = k then 1 else -1 with hεdef
  have hε : ∀ j, ε j = 1 ∨ ε j = -1 := fun j => by
    by_cases h : j = k
    · exact Or.inl (by simp [hεdef, h])
    · exact Or.inr (by simp [hεdef, h])
  have hx' := hsym (Equiv.refl _) ε hε x
  have hsum : x + ptOfCoord (fun j => ε j * ptCoord x (Equiv.refl _ j)) =
      (2 * ptCoord x k) • ptOfCoord (Pi.single k 1) := by
    apply ptCoord_injective
    funext j
    by_cases h : j = k
    · subst h; simp [hεdef]; ring
    · simp [hεdef, h]
  have h2 := hsub x (ptOfCoord fun j => ε j * ptCoord x (Equiv.refl _ j))
  rw [hsum, hhom, hek, hx'] at h2
  have h3 : 0 < |2 * ptCoord x k| := abs_pos.2 (mul_ne_zero two_ne_zero hk)
  have h4 := mul_pos h3 h1
  linarith only [h2, h4]

/-! ### Signed permutations of `ℤ^d` -/

/-- The coordinates of a vertex, indexed by `Option (Fin m)`. -/
def vertexCoord (z : Vertex m) : Option (Fin m) → ℤ := fun k => k.elim z.1 z.2

/-- The vertex with the given coordinates. -/
def vertexOfCoord (c : Option (Fin m) → ℤ) : Vertex m := (c none, fun j => c (some j))

@[simp] theorem vertexCoord_vertexOfCoord (c : Option (Fin m) → ℤ) :
    vertexCoord (vertexOfCoord c) = c := by
  funext k; cases k <;> rfl

@[simp] theorem vertexOfCoord_vertexCoord (z : Vertex m) : vertexOfCoord (vertexCoord z) = z := rfl

theorem vertexCoord_injective : Function.Injective (vertexCoord (m := m)) := fun x y h => by
  rw [← vertexOfCoord_vertexCoord x, h, vertexOfCoord_vertexCoord]

@[simp] theorem vertexCoord_zero : vertexCoord (0 : Vertex m) = 0 := by
  funext k; cases k <;> rfl

@[simp] theorem vertexCoord_add (z w : Vertex m) :
    vertexCoord (z + w) = vertexCoord z + vertexCoord w := by
  funext k; cases k <;> rfl

/-- The coordinates of the point of a vertex. -/
theorem ptCoord_point (z : Vertex m) : ptCoord (point z) = fun k => (vertexCoord z k : ℝ) := by
  funext k; cases k <;> rfl

/-- Two vertices are adjacent iff their difference has one coordinate `±1` and the others `0`. -/
theorem latticeGraph_adj_iff_vertexCoord {x y : Vertex m} :
    (latticeGraph m).Adj x y ↔
      ∃ k t, (t = 1 ∨ t = -1) ∧ vertexCoord (y - x) = Pi.single k t := by
  classical
  rw [latticeGraph_adj_iff_sub]
  constructor
  · rintro (h | h | ⟨j, h | h⟩) <;> rw [h]
    · exact ⟨none, 1, Or.inl rfl, by funext k; cases k <;> simp [vertexCoord]⟩
    · exact ⟨none, -1, Or.inr rfl, by funext k; cases k <;> simp [vertexCoord]⟩
    · exact ⟨some j, 1, Or.inl rfl, by
        funext k; cases k <;> simp [vertexCoord, Pi.single_apply]⟩
    · exact ⟨some j, -1, Or.inr rfl, by
        funext k; cases k <;> simp [vertexCoord, Pi.single_apply]; split_ifs <;> simp⟩
  · rintro ⟨k, t, ht, h⟩
    have hw : y - x = vertexOfCoord (Pi.single k t) := by rw [← h, vertexOfCoord_vertexCoord]
    rw [hw]
    rcases k with _ | j <;> rcases ht with rfl | rfl
    · exact Or.inl (Prod.ext (by simp [vertexOfCoord]) (by funext i; simp [vertexOfCoord]))
    · exact Or.inr (Or.inl (Prod.ext (by simp [vertexOfCoord])
        (by funext i; simp [vertexOfCoord])))
    · exact Or.inr (Or.inr ⟨j, Or.inl (Prod.ext (by simp [vertexOfCoord])
        (by funext i; simp [vertexOfCoord, Pi.single_apply]))⟩)
    · exact Or.inr (Or.inr ⟨j, Or.inr (Prod.ext (by simp [vertexOfCoord])
        (by funext i; simp [vertexOfCoord, Pi.single_apply]; split_ifs <;> simp))⟩)

/-- The signed permutation `z ↦ (s_k z_{σ k})_k` of `ℤ^d`. -/
def signedPerm (σ : Equiv.Perm (Option (Fin m))) (s : Option (Fin m) → ℤ) (z : Vertex m) :
    Vertex m :=
  vertexOfCoord fun k => s k * vertexCoord z (σ k)

theorem vertexCoord_signedPerm (σ : Equiv.Perm (Option (Fin m))) (s : Option (Fin m) → ℤ)
    (z : Vertex m) : vertexCoord (signedPerm σ s z) = fun k => s k * vertexCoord z (σ k) :=
  vertexCoord_vertexOfCoord _

@[simp] theorem signedPerm_zero (σ : Equiv.Perm (Option (Fin m))) (s : Option (Fin m) → ℤ) :
    signedPerm σ s 0 = 0 := by
  apply vertexCoord_injective
  funext k
  simp [vertexCoord_signedPerm]

theorem signedPerm_add (σ : Equiv.Perm (Option (Fin m))) (s : Option (Fin m) → ℤ)
    (z w : Vertex m) : signedPerm σ s (z + w) = signedPerm σ s z + signedPerm σ s w := by
  apply vertexCoord_injective
  funext k
  simp [vertexCoord_signedPerm, mul_add]

section Signs

variable {σ : Equiv.Perm (Option (Fin m))} {s : Option (Fin m) → ℤ}

theorem signedPerm_symm_signedPerm (hs : ∀ k, s k * s k = 1) (z : Vertex m) :
    signedPerm σ.symm (fun j => s (σ.symm j)) (signedPerm σ s z) = z := by
  apply vertexCoord_injective
  funext j
  simp [vertexCoord_signedPerm, ← mul_assoc, hs]

theorem signedPerm_signedPerm_symm (hs : ∀ k, s k * s k = 1) (z : Vertex m) :
    signedPerm σ s (signedPerm σ.symm (fun j => s (σ.symm j)) z) = z := by
  apply vertexCoord_injective
  funext k
  simp [vertexCoord_signedPerm, ← mul_assoc, hs]

/-- A signed permutation of the coordinates, as an additive automorphism of `ℤ^d`. -/
def signedPermEquiv (hs : ∀ k, s k * s k = 1) : Vertex m ≃+ Vertex m where
  toFun := signedPerm σ s
  invFun := signedPerm σ.symm fun j => s (σ.symm j)
  left_inv := signedPerm_symm_signedPerm hs
  right_inv := signedPerm_signedPerm_symm hs
  map_add' := signedPerm_add σ s

/-- A signed permutation maps the unit steps `±e_k` onto themselves. -/
theorem exists_single_iff_of_sign (hs : ∀ k, s k = 1 ∨ s k = -1) (c : Option (Fin m) → ℤ) :
    (∃ k t, (t = 1 ∨ t = -1) ∧ (fun k => s k * c (σ k)) = Pi.single k t) ↔
      ∃ k t, (t = 1 ∨ t = -1) ∧ c = Pi.single k t := by
  classical
  have hss : ∀ k, s k * s k = 1 := fun k => by rcases hs k with h | h <;> rw [h] <;> norm_num
  have hst : ∀ k (t : ℤ), (t = 1 ∨ t = -1) → (s k * t = 1 ∨ s k * t = -1) := fun k t ht => by
    rcases hs k with h | h <;> rcases ht with rfl | rfl <;> rw [h] <;> norm_num
  constructor
  · rintro ⟨k₁, t, ht, h⟩
    refine ⟨σ k₁, s k₁ * t, hst k₁ t ht, funext fun j => ?_⟩
    have hj := congrFun h (σ.symm j)
    simp only [Equiv.apply_symm_apply] at hj
    have hc : c j = s (σ.symm j) * (Pi.single k₁ t : Option (Fin m) → ℤ) (σ.symm j) := by
      rw [← hj, ← mul_assoc, hss, one_mul]
    rw [hc]
    by_cases hjk : j = σ k₁
    · subst hjk; simp
    · have : σ.symm j ≠ k₁ := fun h' => hjk (by rw [← h', Equiv.apply_symm_apply])
      simp [hjk, this]
  · rintro ⟨k₀, t, ht, rfl⟩
    refine ⟨σ.symm k₀, s (σ.symm k₀) * t, hst _ t ht, funext fun k => ?_⟩
    by_cases hk : k = σ.symm k₀
    · subst hk; simp
    · have : σ k ≠ k₀ := fun h' => hk (by rw [← h', Equiv.symm_apply_apply])
      simp [hk, this]

/-- A signed permutation of the coordinates, as an automorphism of the lattice graph. -/
def signedPermIso (hs : ∀ k, s k = 1 ∨ s k = -1) : latticeGraph m ≃g latticeGraph m where
  toEquiv := (signedPermEquiv (σ := σ) (s := s)
    fun k => by rcases hs k with h | h <;> rw [h] <;> norm_num).toEquiv
  map_rel_iff' := by
    intro x y
    show (latticeGraph m).Adj (signedPerm σ s x) (signedPerm σ s y) ↔ (latticeGraph m).Adj x y
    rw [latticeGraph_adj_iff_vertexCoord, latticeGraph_adj_iff_vertexCoord]
    have e : signedPerm σ s y - signedPerm σ s x = signedPerm σ s (y - x) := by
      rw [sub_eq_iff_eq_add, ← signedPerm_add, sub_add_cancel]
    rw [e, vertexCoord_signedPerm]
    exact exists_single_iff_of_sign hs _

end Signs

/-! ### Transport of weights along a graph automorphism -/

/-- The weights transported along an automorphism `Φ` of the lattice graph:
`(transport Φ ω)(e) = ω(Φ e)`. -/
def transport (Φ : latticeGraph m ≃g latticeGraph m) (ω : Config m) : Config m :=
  fun e => ω (Φ.mapEdgeSet e)

/-- Mapping a walk along a graph automorphism pulls the weights back. -/
theorem walkCost_map_iso (Φ : latticeGraph m ≃g latticeGraph m) (ω : Config m)
    {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    walkCost ω (p.map Φ.toHom) = walkCost (transport Φ ω) p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [SimpleGraph.Walk.map_cons, walkCost_cons, ih]
    rfl

/-- The walk map induced by a graph automorphism is a bijection. -/
def walkIsoEquiv (Φ : latticeGraph m ≃g latticeGraph m) (u v : Vertex m) :
    (latticeGraph m).Walk u v ≃ (latticeGraph m).Walk (Φ u) (Φ v) where
  toFun := SimpleGraph.Walk.map Φ.toHom
  invFun := fun p => (p.map Φ.symm.toHom).copy (Φ.symm_apply_apply u) (Φ.symm_apply_apply v)
  left_inv := by
    intro p
    dsimp only
    rw [SimpleGraph.Walk.map_map]
    rw [p.map_eq_of_eq SimpleGraph.Hom.id (SimpleGraph.Iso.symm_toHom_comp_toHom Φ)]
    simp only [SimpleGraph.Walk.map_id]
    exact (p.copy_copy _ _ _ _).trans p.copy_rfl_rfl
  right_inv := by
    intro p
    rw [SimpleGraph.Walk.map_copy, SimpleGraph.Walk.map_map]
    rw [p.map_eq_of_eq SimpleGraph.Hom.id (SimpleGraph.Iso.toHom_comp_symm_toHom Φ)]
    simp only [SimpleGraph.Walk.map_id]
    exact (p.copy_copy _ _ _ _).trans p.copy_rfl_rfl

/-- `T_{transport Φ ω}(u, v) = T_ω(Φ u, Φ v)`. -/
theorem passageTime_transport (Φ : latticeGraph m ≃g latticeGraph m) (ω : Config m)
    (u v : Vertex m) : passageTime (transport Φ ω) u v = passageTime ω (Φ u) (Φ v) := by
  change sInf (Set.range _) = sInf (Set.range fun p : (latticeGraph m).Walk (Φ u) (Φ v) =>
    walkCost ω p)
  congr 1
  rw [← (walkIsoEquiv Φ u v).surjective.range_comp (walkCost ω)]
  congr 1
  funext p
  exact (walkCost_map_iso Φ ω p).symm

theorem measurable_transport (Φ : latticeGraph m ≃g latticeGraph m) :
    Measurable (transport Φ) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- The law of independent identically distributed weights is invariant under the transport
along every automorphism of the lattice graph, which permutes the edges. -/
theorem IsIIDWeights.measurePreserving_transport {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} (hP : IsIIDWeights P F) (Φ : latticeGraph m ≃g latticeGraph m) :
    MeasurePreserving (transport Φ) P P := by
  rw [IsIIDWeights.eq_infinitePi hP]
  have heq : (transport Φ : Config m → Config m) =
      MeasurableEquiv.piCongrLeft (fun _ : Edge m => ℝ≥0) Φ.mapEdgeSet.symm := by
    funext ω e
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    simp [transport]
  refine ⟨measurable_transport Φ, ?_⟩
  rw [heq]
  exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : Edge m => F) Φ.mapEdgeSet.symm

/-! ### Signed permutations of `ℝ^d` -/

/-- The signed permutation `x ↦ (ε_k x_{σ k})_k` of `ℝ^d`, as a linear map. -/
def signedPermPt (σ : Equiv.Perm (Option (Fin m))) (ε : Option (Fin m) → ℝ) :
    Pt m →ₗ[ℝ] Pt m where
  toFun x := ptOfCoord fun k => ε k * ptCoord x (σ k)
  map_add' x y := ptCoord_injective (by funext k; simp [mul_add])
  map_smul' c x := ptCoord_injective (by funext k; simp; ring)

end CurvatureVariance.Infra.FPP
