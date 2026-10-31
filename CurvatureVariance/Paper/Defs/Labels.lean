/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
public import CurvatureVariance.Infra.FPP.Translation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# Labels of blocks, resampling given a label, and the conditional expectations of Section `sec:gain`

The objects of Lemmas `lem:labels`, `lem:residual` and `lem:fewtranslates` of the lattice paper.

* `labelES P X G lam`: `E[(X^G − X)²]` for the resampling of `G` with `σ_G = λ`
  (the resampling of [AB26], defined before [AB26, Lemma 6.1], which the text before Lemma
  `lem:blocks` uses for the weights).
* `IsBlockLabel`: a label of one block, with equation `eq:labelprofile` at an error `ε`.
* `offsetOf`, `offsetAverage`: the vectors `a = (a_1, …, a_K)` and the average
  `L^{−K(d−1)} Σ_a` of equation `eq:residual`.
* `blockFacePairs`: the set `Γ_G` (the text before Lemma `lem:labels`).
* `blockShift`: the vector `z = (0, wLm)` of the translation property of Lemma `lem:labels`.
* `IsLabelFamily`: the conclusion of Lemma `lem:labels`, for one family `lam i o g` indexed by the
  slab, the offset and the block.
* `blockEnergy`: `Σ_G E[(X^G − X)²]` with `σ_G = λ_G`, for the blocks of all `K` slabs.
* `IsLabelOf`, `IsOffsetLabels`: a label of an edge set and a family of labels at fixed offsets.
* `blockLabelSigma`, `labelMean`, `integrateLabel`, `meanConditionalVariance`: the `σ`-algebras of
  the labels, `f = E[F̄ | (X_G)_G]`, `E_G[f]` and `E[Var[F̄ | (X_G)_G]]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-! ### Resampling a set of edges given a label -/

/-- `E (X − X^{G,λ})²`: the mean square change of `X` when the weights of `G` are resampled
conditionally on the value of the label `λ` (the resampling of [AB26] with `σ_G = λ`),
`∫ω ∫ω' (X ω − X (resample G ω ω'))² dP[|λ⁻¹{λ ω}](ω') dP(ω)`. -/
noncomputable def labelES (P : Measure (Config m)) (X : Config m → ℝ)
    (G : Set (Sym2 (Vertex m))) {β : Type*} (lam : Config m → β) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal ((X ω - X (resample G ω ω')) ^ 2) ∂(P[|lam ⁻¹' {lam ω}]) ∂P

/-- `labelES` depends on the label only through its level sets. -/
theorem labelES_congr_level (P : Measure (Config m)) (X : Config m → ℝ)
    (G : Set (Sym2 (Vertex m))) {β γ : Type*} {lam : Config m → β} {lam' : Config m → γ}
    (h : ∀ ω ω', lam ω' = lam ω ↔ lam' ω' = lam' ω) :
    labelES P X G lam = labelES P X G lam' := by
  unfold labelES
  congr 1
  funext ω
  have hset : lam ⁻¹' {lam ω} = lam' ⁻¹' {lam' ω} := by
    ext ω'
    simp only [mem_preimage, mem_singleton_iff]
    exact h ω ω'
  rw [hset]

/-! ### Block labels -/

/-- **A label of the block `(i, o, g)` at error `ε`** (equation `eq:labelprofile`): `λ` is
a function of the weights of the block `block n w L t i o g`
(`w = ⌈(nQ_n)^{1/2}⌉`) with finitely many values and measurable level sets, and
`‖sup_{(u,v) ∈ Γ_G} |(T^{(i)}(u,v) − P·(v−u))/Q_n − λ(u,v)|‖_{8d} ≤ ε`, the supremum over the points
of the subcube of the block on the two faces of slab `i`. -/
structure IsBlockLabel (M : Model m) (K : ℕ) (A : ℝ) (L n : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (P : Pt m) (i : ℕ) (o g : Fin m → ℤ) (ε : ℝ) (lam : Config m → Vertex m → Vertex m → ℝ) :
    Prop where
  /-- `λ` is a function of the weights of the block. -/
  dep : ∀ ω ω' : Config m,
    (∀ e : Edge m, e.1 ∈ block n (wInt M K A n) L t i o g → ω e = ω' e) → lam ω = lam ω'
  /-- `λ` has finitely many values. -/
  finite : (Set.range lam).Finite
  /-- The level sets of `λ` are measurable. -/
  measurableSet : ∀ ω, MeasurableSet (lam ⁻¹' {lam ω})
  /-- The approximation of equation `eq:labelprofile` at error `ε`. -/
  approx : ∃ X : Config m → ℝ, eLpNorm X (8 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal ε ∧
    ∀ᵐ ω ∂M.P,
      ∀ u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n),
      ∀ v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n),
        |normSlabTime M K A ω n P i u v - lam ω u v| ≤ X ω

/-! ### Offsets -/

/-- The offsets `o i = σ (i − 1)` of the slabs `1 ≤ i ≤ K`, and `0` for the other `i`, of a family
`σ : Fin K → Fin m → Fin L`. -/
def offsetOf {K L : ℕ} (σ : Fin K → Fin m → Fin L) : ℕ → Fin m → ℤ :=
  fun i k => if h : 1 ≤ i ∧ i ≤ K then ((σ ⟨i - 1, by omega⟩ k : ℕ) : ℤ) else 0

/-- The offsets of a family lie in `{0, …, L − 1}`. -/
theorem offsetOf_mem {K L : ℕ} (hL : 1 ≤ L) (σ : Fin K → Fin m → Fin L) (i : ℕ) (k : Fin m) :
    0 ≤ offsetOf σ i k ∧ offsetOf σ i k < L := by
  unfold offsetOf
  split_ifs with h
  · exact ⟨Int.natCast_nonneg _, by exact_mod_cast (σ ⟨i - 1, by omega⟩ k).isLt⟩
  · exact ⟨le_rfl, by exact_mod_cast hL⟩

/-- The offsets of a family at the slab `i + 1`, `i < K`. -/
theorem offsetOf_succ {K L : ℕ} (σ : Fin K → Fin m → Fin L) (i : Fin K) :
    offsetOf σ ((i : ℕ) + 1) = fun k => ((σ i k : ℕ) : ℤ) := by
  funext k
  unfold offsetOf
  split_ifs with h
  · simp
  · exact absurd ⟨by omega, by omega⟩ h

/-- The average `L^{-mK} ∑_σ E(offsetOf σ)` over the offset families
`σ : Fin K → Fin m → Fin L`: the expectation over independent uniform offsets. -/
noncomputable def offsetAverage (K L : ℕ) (E : (ℕ → Fin m → ℤ) → ℝ≥0∞) : ℝ≥0∞ :=
  ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ σ : Fin K → Fin m → Fin L, E (offsetOf σ)

/-- The average over offsets is monotone. -/
theorem offsetAverage_mono {K L : ℕ} {E E' : (ℕ → Fin m → ℤ) → ℝ≥0∞}
    (h : ∀ σ : Fin K → Fin m → Fin L, E (offsetOf σ) ≤ E' (offsetOf σ)) :
    offsetAverage K L E ≤ offsetAverage K L E' := by
  unfold offsetAverage
  gcongr with σ
  exact h σ

/-! ### The conclusion of Lemma `lem:labels` -/

/-- **The set `Γ_G`** (the text before Lemma `lem:labels`) of the block `block n w L t i o g`: the
pairs `(u, v)` of lattice points of the faces `{x·e₁ = (i−1)n}` and `{x·e₁ = in}` of slab `i` whose
coordinates `(q, h)` satisfy `h − qt ∈ w(z + [0,1)^{d−1})` for some
`z ∈ j + {⌈L^{1/2}⌉, …, L − 1 − ⌈L^{1/2}⌉}^{d−1}`, where `j = Lg + o` is the corner of the block.
The union of the cells `w(z + [0,1)^{d−1})` over these `z` is, coordinate by coordinate, the range
of `Paper.subcubeFace`. -/
def blockFacePairs (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (o g : Fin m → ℤ) :
    Set (Vertex m × Vertex m) :=
  subcubeFace w L t o g (((i : ℤ) - 1) * n) ×ˢ subcubeFace w L t o g ((i : ℤ) * n)

/-- The vector `z = (0, wLm)` of the translation property of Lemma `lem:labels`, for
`m' ∈ ℤ^{d−1}`. -/
def blockShift (w L : ℕ) (m' : Fin m → ℤ) : Vertex m :=
  (0, ((w * L : ℕ) : ℤ) • m')

/-- **The conclusion of Lemma `lem:labels`**, at the atom bound `α` and the error `ε`, for one
family `lam i o g` of labels: for every slab `i ∈ {1, …, K}`, every offset `o ∈ {0, …, L−1}^{d−1}`
and every `g ∈ ℤ^{d−1}`, the label `X_G = lam i o g` of the block `G = block n w L t i o g`
(`w = ⌈(nQ_n)^{1/2}⌉`)

* is determined by `τ|_G`, takes finitely many values, has measurable level sets, and satisfies
  equation `eq:labelprofile` at the error `ε` (`IsBlockLabel`);
* has every value of probability at least `α`;
* is a bounded function on `Γ_G` (`blockFacePairs`);
* has the translation property, at every `ω`: for `z = (0, wLm')`, `m' ∈ ℤ^{d−1}`, and every
  pair `(u, v)`, the value `X_{G+z}(u+z, v+z)` computed from the weights `(τ_{e−z})_e` equals
  `X_G(u, v)` computed from `(τ_e)_e`.

Readings. A block of slab `i` is the pair `(o, g)`: for `o ∈ {0, …, L−1}^{d−1}` this is one-to-one,
`j = Lg + o`, and `G + z` is the block `(o, g + m')`, since `z` moves each cell index by `Lm'`. So
`X_G` depends only on the block `G`, not on the offsets of the other slabs, as in the paper; the
proof of Lemma `lem:residual` needs it, since it takes the `a_i` random and independent. The weights
`(τ_{e−z})_e` are `Infra.FPP.translate (-z) τ`, since `translate a τ e = τ (e + a)`. In the paper,
`X_G` is a function on `Γ_G`. A value of the Lean's label is a function on all pairs of vertices,
and `labelES` and `blockLabelSigma` read the partition of the configurations by the whole function.
So the translation property is stated on all pairs, which contains the paper's clause on `Γ_G`: the
proof of Lemma `lem:residual` needs the partitions of `G` and `G + z` to be translates of each other
(the third paragraph of the proof of [AB26, Lemma 6.3]), and the extension by `0` off `Γ_G` of a
label with the paper's clause has this form, since `Γ_G + z` is `Γ_{G+z}`. Since `Γ_G` is finite,
the bound on the values follows from the finiteness of the values; it is stated since the paper
states it. -/
structure IsLabelFamily (M : Model m) (K : ℕ) (A : ℝ) (L n : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (P : Pt m) (α ε : ℝ)
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ) : Prop where
  /-- Each label is determined by its block, has finitely many values, and satisfies equation
  `eq:labelprofile` at the error `ε`. -/
  isBlockLabel : ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ o g : Fin m → ℤ, (∀ k, 0 ≤ o k ∧ o k < L) →
    IsBlockLabel M K A L n t P i o g ε (lam i o g)
  /-- Every value of a label has probability at least `α`. -/
  le_measure : ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ o g : Fin m → ℤ, (∀ k, 0 ≤ o k ∧ o k < L) →
    ∀ ω : Config m, ENNReal.ofReal α ≤ M.P (lam i o g ⁻¹' {lam i o g ω})
  /-- The values of a label are bounded functions on `Γ_G`. -/
  bounded : ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ o g : Fin m → ℤ, (∀ k, 0 ≤ o k ∧ o k < L) →
    ∃ B : ℝ, ∀ (ω : Config m), ∀ p ∈ blockFacePairs n (wInt M K A n) L t i o g,
      |lam i o g ω p.1 p.2| ≤ B
  /-- The translation property, at every `ω`. -/
  translate_eq : ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ o g : Fin m → ℤ, (∀ k, 0 ≤ o k ∧ o k < L) →
    ∀ (m' : Fin m → ℤ) (ω : Config m) (u v : Vertex m),
      lam i o (g + m') (Infra.FPP.translate (-blockShift (wInt M K A n) L m') ω)
          (u + blockShift (wInt M K A n) L m') (v + blockShift (wInt M K A n) L m') =
        lam i o g ω u v

/-! ### The sum over the blocks -/

/-- `Σ_G E[(X^G − X)²]` over the blocks `G = block n w L t (i + 1) (o (i + 1)) g`, `i < K`,
`g ∈ ℤ^{d−1}`, of the `K` slabs with the offsets `o`, for the resampling of each `G` with
`σ_G = lam (i + 1) (o (i + 1)) g`: the left side of the first bound of equation `eq:residual`,
for one choice of the offsets. -/
noncomputable def blockEnergy (P : Measure (Config m)) (X : Config m → ℝ) (n w L K : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) {β : Type*}
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β) (o : ℕ → Fin m → ℤ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
    labelES P X (block n w L t (i + 1) (o (i + 1)) g) (lam (i + 1) (o (i + 1)) g)

/-! ### The labels at fixed offsets and the conditional expectations -/

/-- **`λ` is a label of the edge set `G`**: a function of the weights of `G` with finitely many
values and measurable level sets. -/
structure IsLabelOf (G : Set (Sym2 (Vertex m))) {β : Type*} (lam : Config m → β) : Prop where
  /-- `λ` is a function of the weights of `G`. -/
  dep : ∀ ω ω' : Config m, (∀ e : Edge m, e.1 ∈ G → ω e = ω' e) → lam ω = lam ω'
  /-- `λ` has finitely many values. -/
  finite : (Set.range lam).Finite
  /-- The level sets of `λ` are measurable. -/
  measurableSet : ∀ ω, MeasurableSet (lam ⁻¹' {lam ω})

/-- A label of a block at an error `ε` is a label of this block. -/
theorem IsBlockLabel.isLabelOf {M : Model m} {K : ℕ} {A : ℝ} {L n : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {P : Pt m} {i : ℕ} {o g : Fin m → ℤ} {ε : ℝ}
    {lam : Config m → Vertex m → Vertex m → ℝ} (h : IsBlockLabel M K A L n t P i o g ε lam) :
    IsLabelOf (block n (wInt M K A n) L t i o g) lam :=
  ⟨h.dep, h.finite, h.measurableSet⟩

/-- The `σ`-algebra `σ(λ)` of a label is below the `σ`-algebra of the configurations. -/
theorem IsLabelOf.comap_le {G : Set (Sym2 (Vertex m))} {β : Type*} {lam : Config m → β}
    (h : IsLabelOf G lam) :
    MeasurableSpace.comap lam ⊤ ≤ (inferInstance : MeasurableSpace (Config m)) := by
  classical
  rintro s ⟨S, -, rfl⟩
  have hs : lam ⁻¹' S = ⋃ c ∈ (h.finite.toFinset.filter (· ∈ S) : Finset β), lam ⁻¹' {c} := by
    ext ω
    simp [Set.Finite.mem_toFinset]
  rw [hs]
  refine Finset.measurableSet_biUnion _ fun c hc => ?_
  obtain ⟨ω, rfl⟩ := (Set.Finite.mem_toFinset h.finite).1 (Finset.mem_filter.1 hc).1
  exact h.measurableSet ω

/-- **A family of labels at the offsets `o`**: `lam (i + 1) (o (i + 1)) g` is a label of the block
of slab `i + 1` with index `g`, for `i < K` and `g ∈ ℤ^{d−1}`. This is what Lemma
`lem:fewtranslates` needs of its labels. -/
def IsOffsetLabels (n w L K : ℕ) (t : EuclideanSpace ℝ (Fin m)) (o : ℕ → Fin m → ℤ) {β : Type*}
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β) : Prop :=
  ∀ i < K, ∀ g : Fin m → ℤ,
    IsLabelOf (block n w L t (i + 1) (o (i + 1)) g) (lam (i + 1) (o (i + 1)) g)

/-- The conclusion of Lemma `lem:labels` gives a family of labels at all offsets. -/
theorem IsLabelFamily.isOffsetLabels {M : Model m} {K : ℕ} {A : ℝ} {L n : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {P : Pt m} {α ε : ℝ}
    {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ}
    (h : IsLabelFamily M K A L n t P α ε lam) {o : ℕ → Fin m → ℤ}
    (ho : ∀ i k, 0 ≤ o i k ∧ o i k < L) : IsOffsetLabels n (wInt M K A n) L K t o lam :=
  fun i hi g => (h.isBlockLabel (i + 1) (by omega) hi (o (i + 1)) g (ho (i + 1))).isLabelOf

/-- The `σ`-algebra generated by the labels of the blocks `(i, g) ∈ S`, `i < K`, of the `K` slabs at
the offsets `o`. -/
@[instance_reducible]
def blockLabelSigma (K : ℕ) (o : ℕ → Fin m → ℤ) {β : Type*}
    (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β) (S : Set (ℕ × (Fin m → ℤ))) :
    MeasurableSpace (Config m) :=
  ⨆ (p : ℕ × (Fin m → ℤ)) (_ : p.1 < K ∧ p ∈ S),
    MeasurableSpace.comap (lam (p.1 + 1) (o (p.1 + 1)) p.2) ⊤

/-- The `σ`-algebras of the labels of a family are below the `σ`-algebra of the configurations, so
that `labelMean` and `integrateLabel` are conditional expectations for a sub-`σ`-algebra. -/
theorem IsOffsetLabels.blockLabelSigma_le {n w L K : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {o : ℕ → Fin m → ℤ} {β : Type*} {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β}
    (h : IsOffsetLabels n w L K t o lam) (S : Set (ℕ × (Fin m → ℤ))) :
    blockLabelSigma K o lam S ≤ (inferInstance : MeasurableSpace (Config m)) :=
  iSup₂_le fun p hp => (h p.1 hp.1 p.2).comap_le

/-- `f = E[X | (X_G)_G]` (as in [AB26], after [AB26, Lemma 6.2]; the text after Lemma `lem:labels`):
the conditional expectation of `X` given the `σ`-algebra of all the labels of the blocks of the `K`
slabs at the offsets `o`. -/
noncomputable def labelMean (P : Measure (Config m)) (X : Config m → ℝ) (K : ℕ)
    (o : ℕ → Fin m → ℤ) {β : Type*} (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β) :
    Config m → ℝ :=
  P[X | blockLabelSigma K o lam Set.univ]

/-- `E_G[Y]`, for `G = (i, g)` the block of slab `i + 1` and index `g` (as in [AB26], before
[AB26, Lemma 6.3]; the text after Lemma `lem:labels`): the conditional expectation of `Y` given the
`σ`-algebra of the labels of the other blocks. The labels are independent, since each is a function
of the weights of its block and the blocks are disjoint, so for a function `Y` of the labels this
integrates `X_G` alone. -/
noncomputable def integrateLabel (P : Measure (Config m)) (Y : Config m → ℝ) (K : ℕ)
    (o : ℕ → Fin m → ℤ) {β : Type*} (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β)
    (i : ℕ) (g : Fin m → ℤ) : Config m → ℝ :=
  P[Y | blockLabelSigma K o lam {(i, g)}ᶜ]

/-- `E[Var[X | (X_G)_G]]` (the second bound of equation `eq:residual`): the mean square of
`X − E[X | (X_G)_G]`, in `[0, ∞]`. For `X ∈ L²` this is the mean of the conditional variance. -/
noncomputable def meanConditionalVariance (P : Measure (Config m)) (X : Config m → ℝ) (K : ℕ)
    (o : ℕ → Fin m → ℤ) {β : Type*} (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → β) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((X ω - labelMean P X K o lam ω) ^ 2) ∂P

end CurvatureVariance.Paper.Gain
