/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import IsotropicVariance.Infra.Measurability.MinimizerMeasurable

/-!
# Section `sec:gain`: geometry of the blocks

The geometric input of the block coordinates: the blocks `[in, (i+1)n] × W(z + [0, L)^m)` of the
`K` slabs with offsets `o` are the regions of independent block coordinates of the noise.

* Hyperplanes `{x · e₁ = a}` and `{x · e_{k+2} = a}` are Lebesgue-null (`volume_lon_eq`,
  `volume_tr_eq`); the frontier of a block lies in finitely many of them
  (`volume_frontier_block`).
* Two different blocks meet in a null set (`volume_blockOf_inter`), so their interiors are
  disjoint.
* The pieces `piece`, the blocks without their upper face (except in the last slab), are
  pairwise disjoint (`pairwise_disjoint_piece`) and cover the closed strip `[0, Kn] × ℝ^m`
  (`exists_mem_piece`).
-/

@[expose] public section

open MeasureTheory Set

open IsotropicVariance.Infra.Slab (continuous_tr_apply)
namespace IsotropicVariance.Paper.Proofs.Gain.Bridge

open IsotropicVariance.Paper

variable {m : ℕ}

/-! ### Hyperplanes -/

section Hyperplanes

/-- The longitudinal coordinate as an affine map. -/
noncomputable def lonAffine : Pt m →ᵃ[ℝ] ℝ :=
  (WithLp.fstₗ 2 ℝ ℝ (EuclideanSpace ℝ (Fin m))).toAffineMap

/-- A transverse coordinate as an affine map. -/
noncomputable def trAffine (k : Fin m) : Pt m →ᵃ[ℝ] ℝ :=
  ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).toLinearMap.comp
    (WithLp.sndₗ 2 ℝ ℝ (EuclideanSpace ℝ (Fin m)))).toAffineMap

/-- A level set of a nonconstant affine function is Lebesgue-null. -/
theorem volume_preimage_affine (f : Pt m →ᵃ[ℝ] ℝ) {x y : Pt m} (hxy : f x ≠ f y) (a : ℝ) :
    volume (f ⁻¹' {a}) = 0 := by
  have hset : f ⁻¹' {a} =
      ((({a} : AffineSubspace ℝ ℝ).comap f : AffineSubspace ℝ (Pt m)) : Set (Pt m)) := by
    rw [AffineSubspace.coe_comap]
    simp
  rw [hset]
  refine Measure.addHaar_affineSubspace _ _ fun htop => ?_
  have hx : x ∈ ((({a} : AffineSubspace ℝ ℝ).comap f : AffineSubspace ℝ (Pt m)) :
      Set (Pt m)) := by
    rw [htop]
    exact mem_univ _
  have hy : y ∈ ((({a} : AffineSubspace ℝ ℝ).comap f : AffineSubspace ℝ (Pt m)) :
      Set (Pt m)) := by
    rw [htop]
    exact mem_univ _
  rw [← hset] at hx hy
  exact hxy (hx.trans hy.symm)

/-- A hyperplane `{x · e₁ = a}` is Lebesgue-null. -/
theorem volume_lon_eq (a : ℝ) : volume {x : Pt m | Pt.lon x = a} = 0 :=
  volume_preimage_affine lonAffine (x := WithLp.toLp 2 (0, 0)) (y := WithLp.toLp 2 (1, 0))
    (by simp [lonAffine]) a

/-- A hyperplane `{x · e_{k+2} = a}` is Lebesgue-null. -/
theorem volume_tr_eq (k : Fin m) (a : ℝ) : volume {x : Pt m | Pt.tr x k = a} = 0 :=
  volume_preimage_affine (trAffine k) (x := WithLp.toLp 2 (0, 0))
    (y := WithLp.toLp 2 (0, EuclideanSpace.single k 1)) (by simp [trAffine]) a

end Hyperplanes

/-! ### Frontiers and interiors -/

section Frontier

variable {α : Type*} [TopologicalSpace α]

/-- The frontier of an intersection lies in the union of the frontiers. -/
theorem frontier_inter_subset_union (s t : Set α) :
    frontier (s ∩ t) ⊆ frontier s ∪ frontier t :=
  (frontier_inter_subset s t).trans
    (union_subset_union inter_subset_left inter_subset_right)

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α}

/-- An intersection of sets with null frontiers has a null frontier. -/
theorem null_frontier_inter (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s ∩ t)) = 0 :=
  measure_mono_null (frontier_inter_subset_union s t) (measure_union_null hs ht)

/-- A difference of sets with null frontiers has a null frontier. -/
theorem null_frontier_diff (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s \ t)) = 0 := by
  rw [sdiff_eq]
  exact null_frontier_inter hs (by rwa [frontier_compl])

/-- Two sets meeting in a null set have disjoint interiors, for a measure positive on open sets.
-/
theorem disjoint_interior_of_null_inter [μ.IsOpenPosMeasure] (h : μ (s ∩ t) = 0) :
    Disjoint (interior s) (interior t) := by
  rw [disjoint_iff_inter_eq_empty, ← interior_inter]
  exact Measure.interior_eq_empty_of_null h

end Frontier

/-! ### Blocks -/

section Blocks

/-- The closed box containing a block. -/
def closedBlock (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) : Set (Pt m) :=
  {x | (i : ℝ) * n ≤ Pt.lon x ∧ Pt.lon x ≤ ((i : ℝ) + 1) * n ∧
    ∀ k, W * z k ≤ Pt.tr x k ∧ Pt.tr x k ≤ W * (z k + L)}

/-- The open box contained in a block. -/
def openBlock (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) : Set (Pt m) :=
  {x | (i : ℝ) * n < Pt.lon x ∧ Pt.lon x < ((i : ℝ) + 1) * n ∧
    ∀ k, W * z k < Pt.tr x k ∧ Pt.tr x k < W * (z k + L)}

/-- The faces of the boxes of a block. -/
def blockFaces (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) : Set (Pt m) :=
  {x | Pt.lon x = (i : ℝ) * n} ∪ {x | Pt.lon x = ((i : ℝ) + 1) * n} ∪
    ⋃ k, ({x | Pt.tr x k = W * z k} ∪ {x | Pt.tr x k = W * (z k + L)})

/-- The closed box of a block is closed. -/
theorem isClosed_closedBlock (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    IsClosed (closedBlock n W L i z) := by
  simp only [closedBlock, ofPred_and, ofPred_forall]
  exact (isClosed_le continuous_const Pt.continuous_lon).inter
    ((isClosed_le Pt.continuous_lon continuous_const).inter
      (isClosed_iInter fun k => (isClosed_le continuous_const (continuous_tr_apply k)).inter
        (isClosed_le (continuous_tr_apply k) continuous_const)))

/-- The open box of a block is open. -/
theorem isOpen_openBlock (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    IsOpen (openBlock n W L i z) := by
  simp only [openBlock, ofPred_and, ofPred_forall]
  exact (isOpen_lt continuous_const Pt.continuous_lon).inter
    ((isOpen_lt Pt.continuous_lon continuous_const).inter
      (isOpen_iInter_of_finite fun k => (isOpen_lt continuous_const (continuous_tr_apply k)).inter
        (isOpen_lt (continuous_tr_apply k) continuous_const)))

/-- A block is Borel. -/
theorem measurableSet_block (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    MeasurableSet (block n W L i z) := by
  simp only [block, ofPred_and, ofPred_forall]
  exact (measurableSet_le measurable_const Pt.continuous_lon.measurable).inter
    ((measurableSet_le Pt.continuous_lon.measurable measurable_const).inter
      (MeasurableSet.iInter fun k =>
        (measurableSet_le measurable_const (continuous_tr_apply k).measurable).inter
        (measurableSet_lt (continuous_tr_apply k).measurable measurable_const)))

/-- The frontier of a block lies in the faces of its boxes. -/
theorem frontier_block_subset (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    frontier (block n W L i z) ⊆ blockFaces n W L i z := by
  have hcl : closure (block n W L i z) ⊆ closedBlock n W L i z :=
    closure_minimal (fun x hx => ⟨hx.1, hx.2.1, fun k => ⟨(hx.2.2 k).1, (hx.2.2 k).2.le⟩⟩)
      (isClosed_closedBlock n W L i z)
  have hint : openBlock n W L i z ⊆ interior (block n W L i z) :=
    interior_maximal (fun x hx => ⟨hx.1.le, hx.2.1.le, fun k => ⟨(hx.2.2 k).1.le, (hx.2.2 k).2⟩⟩)
      (isOpen_openBlock n W L i z)
  intro x hx
  have hxc := hcl hx.1
  have hxo : x ∉ openBlock n W L i z := fun h => hx.2 (hint h)
  by_contra hH
  simp only [blockFaces, mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists] at hH
  exact hxo ⟨lt_of_le_of_ne hxc.1 (Ne.symm hH.1.1), lt_of_le_of_ne hxc.2.1 hH.1.2,
    fun k => ⟨lt_of_le_of_ne (hxc.2.2 k).1 (Ne.symm (hH.2 k).1),
      lt_of_le_of_ne (hxc.2.2 k).2 (hH.2 k).2⟩⟩

/-- The faces of the boxes of a block are Lebesgue-null. -/
theorem volume_blockFaces (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    volume (blockFaces n W L i z) = 0 :=
  measure_union_null (measure_union_null (volume_lon_eq _) (volume_lon_eq _))
    (measure_iUnion_null fun k => measure_union_null (volume_tr_eq k _) (volume_tr_eq k _))

/-- The frontier of a block is Lebesgue-null. -/
theorem volume_frontier_block (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    volume (frontier (block n W L i z)) = 0 :=
  measure_mono_null (frontier_block_subset n W L i z) (volume_blockFaces n W L i z)

/-- Two blocks of the same slab with different indices `z ≡ z' (mod L)` are disjoint. -/
theorem disjoint_block_of_ne {n W : ℝ} (hW : 0 < W) {L i : ℕ} {o : Fin m → Fin L}
    {z z' : Fin m → ℤ} (hz : IsBlockIndex L o z) (hz' : IsBlockIndex L o z') (hne : z ≠ z') :
    Disjoint (block n W L i z) (block n W L i z') := by
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ z' k := by
    by_contra h
    exact hne (funext fun k => not_not.1 (not_exists.1 h k))
  have hdvd : (L : ℤ) ∣ z k - z' k := by
    have := dvd_sub (hz k) (hz' k)
    rwa [sub_sub_sub_cancel_right] at this
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hx'⟩
  have h1 := hx.2.2 k
  have h2 := hx'.2.2 k
  rcases lt_or_gt_of_ne hk with hlt | hlt
  · have hL : (L : ℤ) ≤ z' k - z k :=
      Int.le_of_dvd (sub_pos.2 hlt) (by rw [← neg_sub]; exact (dvd_neg).2 hdvd)
    have hL' : ((z k : ℝ) + L) ≤ z' k := by exact_mod_cast (by linarith : z k + (L : ℤ) ≤ z' k)
    have := mul_le_mul_of_nonneg_left hL' hW.le
    linarith [h1.2, h2.1]
  · have hL : (L : ℤ) ≤ z k - z' k := Int.le_of_dvd (sub_pos.2 hlt) hdvd
    have hL' : ((z' k : ℝ) + L) ≤ z k := by exact_mod_cast (by linarith : z' k + (L : ℤ) ≤ z k)
    have := mul_le_mul_of_nonneg_left hL' hW.le
    linarith [h1.1, h2.2]

/-- Blocks of two slabs `i < i'` meet at most in the upper face of the slab `i`. -/
theorem block_inter_block_subset {n W : ℝ} (hn : 0 ≤ n) {L i i' : ℕ} (hii : i < i')
    (z z' : Fin m → ℤ) :
    block n W L i z ∩ block n W L i' z' ⊆ {x | Pt.lon x = ((i : ℝ) + 1) * n} := by
  rintro x ⟨hx, hx'⟩
  have hi : ((i : ℝ) + 1) ≤ i' := by exact_mod_cast hii
  have := mul_le_mul_of_nonneg_right hi hn
  exact le_antisymm hx.2.1 (this.trans hx'.1)

/-- The index set of the blocks of the `K` slabs with offsets `o`: a slab `i < K` and a block
index `z ≡ o i (mod L)`. -/
abbrev BlockIdx (L K : ℕ) (o : Fin K → Fin m → Fin L) : Type :=
  Σ i : Fin K, {z : Fin m → ℤ | IsBlockIndex L (o i) z}

/-- A sum over the blocks of the strip is a sum over the slabs of sums over their blocks. -/
theorem tsum_blockIdx {L K : ℕ} {o : Fin K → Fin m → Fin L} (f : BlockIdx L K o → ENNReal) :
    ∑' c, f c = ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z}, f ⟨i, z⟩ := by
  rw [ENNReal.tsum_sigma', tsum_fintype]

/-- A block of the slab `i` lies in the slab. -/
theorem block_subset_chainSlab (s W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    block s W L i z ⊆ (chainSlab s 0 i).set := by
  intro x hx
  rw [mem_chainSlab_set]
  simp only [Pt.lon_zero, zero_add]
  exact ⟨hx.1, by linarith [hx.2.1]⟩

/-- The block of an index. -/
def blockOf (n W : ℝ) {L K : ℕ} {o : Fin K → Fin m → Fin L} (c : BlockIdx L K o) :
    Set (Pt m) :=
  block n W L c.1 c.2

/-- Two different blocks of the strip meet in a null set. -/
theorem volume_blockOf_inter {n W : ℝ} (hn : 0 ≤ n) (hW : 0 < W) {L K : ℕ}
    {o : Fin K → Fin m → Fin L} {c c' : BlockIdx L K o} (hcc : c ≠ c') :
    volume (blockOf n W c ∩ blockOf n W c') = 0 := by
  obtain ⟨i, z, hz⟩ := c
  obtain ⟨i', z', hz'⟩ := c'
  rcases lt_trichotomy (i : ℕ) i' with hlt | heq | hgt
  · exact measure_mono_null (block_inter_block_subset hn hlt z z') (volume_lon_eq _)
  · have hii : i = i' := Fin.ext heq
    subst hii
    have hzz : z ≠ z' := fun h => hcc (by subst h; rfl)
    rw [blockOf, blockOf, (disjoint_block_of_ne hW hz hz' hzz).inter_eq]
    exact measure_empty
  · rw [inter_comm]
    exact measure_mono_null (block_inter_block_subset hn hgt z' z) (volume_lon_eq _)

/-- Two different blocks of the strip have disjoint interiors. -/
theorem disjoint_interior_blockOf {n W : ℝ} (hn : 0 ≤ n) (hW : 0 < W) {L K : ℕ}
    {o : Fin K → Fin m → Fin L} :
    Pairwise (Function.onFun Disjoint fun c : BlockIdx L K o => interior (blockOf n W c)) :=
  fun _ _ hcc => disjoint_interior_of_null_inter (volume_blockOf_inter hn hW hcc)

end Blocks

/-! ### Pieces of the strip -/

section Pieces

variable {L K : ℕ} {o : Fin K → Fin m → Fin L}

/-- The block of an index without its upper face, except in the last slab: these pieces
partition the closed strip `[0, Kn] × ℝ^m`. -/
def piece (n W : ℝ) (c : BlockIdx L K o) : Set (Pt m) :=
  blockOf n W c \ {x | Pt.lon x = ((c.1 : ℝ) + 1) * n ∧ (c.1 : ℕ) + 1 < K}

/-- A piece lies in its block. -/
theorem piece_subset (n W : ℝ) (c : BlockIdx L K o) : piece n W c ⊆ blockOf n W c :=
  sdiff_subset

/-- A piece is Borel. -/
theorem measurableSet_piece (n W : ℝ) (c : BlockIdx L K o) : MeasurableSet (piece n W c) :=
  (measurableSet_block _ _ _ _ _).diff
    ((measurableSet_eq_fun Pt.continuous_lon.measurable measurable_const).inter
      (MeasurableSet.const _))

/-- A piece has a null frontier. -/
theorem volume_frontier_piece (n W : ℝ) (c : BlockIdx L K o) :
    volume (frontier (piece n W c)) = 0 := by
  refine null_frontier_diff (volume_frontier_block _ _ _ _ _) ?_
  have hsub : frontier {x : Pt m | Pt.lon x = ((c.1 : ℝ) + 1) * n ∧ (c.1 : ℕ) + 1 < K} ⊆
      {x | Pt.lon x = ((c.1 : ℝ) + 1) * n} := by
    refine (frontier_subset_closure).trans (closure_minimal (fun x hx => hx.1) ?_)
    exact isClosed_eq Pt.continuous_lon continuous_const
  exact measure_mono_null hsub (volume_lon_eq _)

/-- Different pieces are disjoint. -/
theorem pairwise_disjoint_piece {n W : ℝ} (hn : 0 ≤ n) (hW : 0 < W) :
    Pairwise (Function.onFun Disjoint (piece (o := o) n W)) := by
  intro c c' hcc
  obtain ⟨i, z, hz⟩ := c
  obtain ⟨i', z', hz'⟩ := c'
  have key : ∀ {i i' : Fin K} (z z' : Fin m → ℤ), (i : ℕ) < i' →
      Disjoint (block n W L i z \ {x | Pt.lon x = ((i : ℝ) + 1) * n ∧ (i : ℕ) + 1 < K})
        (block n W L i' z') := by
    intro i i' z z' hlt
    rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    rintro x ⟨⟨hx, hxf⟩, hx'⟩
    have hface := block_inter_block_subset hn hlt z z' ⟨hx, hx'⟩
    exact hxf ⟨hface, lt_of_le_of_lt (Nat.succ_le_of_lt hlt) i'.2⟩
  rcases lt_trichotomy (i : ℕ) i' with hlt | heq | hgt
  · exact (key z z' hlt).mono_right (piece_subset n W _)
  · have hii : i = i' := Fin.ext heq
    subst hii
    have hzz : z ≠ z' := fun h => hcc (by subst h; rfl)
    exact (disjoint_block_of_ne hW hz hz' hzz).mono (piece_subset n W _) (piece_subset n W _)
  · exact ((key z' z hgt).mono_right (piece_subset n W _)).symm

/-- A transverse block index containing a given transverse coordinate. -/
theorem exists_blockIndex_coord {W : ℝ} (hW : 0 < W) (hL : 1 ≤ L) (r : ℕ) (a : ℝ) :
    ∃ zk : ℤ, (L : ℤ) ∣ zk - r ∧ W * zk ≤ a ∧ a < W * (zk + L) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  set q : ℤ := ⌊(a / W - r) / L⌋ with hq
  refine ⟨r + L * q, ⟨q, by ring⟩, ?_, ?_⟩
  · have h1 : (q : ℝ) ≤ (a / W - r) / L := Int.floor_le _
    have h2 : (L : ℝ) * q ≤ a / W - r := by
      rw [le_div_iff₀ hL0] at h1
      linarith
    have h3 : ((r : ℝ) + L * q) ≤ a / W := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hW.le
    rw [mul_div_cancel₀ a hW.ne'] at h4
    push_cast
    linarith
  · have h1 : (a / W - r) / L < q + 1 := Int.lt_floor_add_one _
    have h2 : a / W - r < L * (q + 1) := by
      rw [div_lt_iff₀ hL0] at h1
      linarith
    have h3 : a / W < (r : ℝ) + L * q + L := by linarith
    have h4 := mul_lt_mul_of_pos_left h3 hW
    rw [mul_div_cancel₀ a hW.ne'] at h4
    push_cast
    linarith

/-- The pieces cover the closed strip `[0, Kn] × ℝ^m`. -/
theorem exists_mem_piece {n W : ℝ} (hn : 0 < n) (hW : 0 < W) (hL : 1 ≤ L) (hK : 1 ≤ K)
    {x : Pt m} (hx₀ : 0 ≤ Pt.lon x) (hx₁ : Pt.lon x ≤ K * n) :
    ∃ c : BlockIdx L K o, x ∈ piece n W c := by
  set t := Pt.lon x / n with ht
  have ht0 : 0 ≤ t := div_nonneg hx₀ hn.le
  have htK : t ≤ K := by rw [ht, div_le_iff₀ hn]; exact hx₁
  set i : ℕ := min ⌊t⌋₊ (K - 1) with hi
  have hiK : i < K := lt_of_le_of_lt (min_le_right _ _) (by omega)
  -- the transverse index
  have hz : ∀ k, ∃ zk : ℤ, (L : ℤ) ∣ zk - (o ⟨i, hiK⟩ k : ℕ) ∧
      W * zk ≤ Pt.tr x k ∧ Pt.tr x k < W * (zk + L) :=
    fun k => exists_blockIndex_coord hW hL _ _
  choose z hzdvd hz using hz
  refine ⟨⟨⟨i, hiK⟩, ⟨z, hzdvd⟩⟩, ⟨⟨?_, ?_, fun k => hz k⟩, ?_⟩⟩
  · -- `i n ≤ lon x`
    have : (i : ℝ) ≤ t := by
      calc (i : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast min_le_left _ _
        _ ≤ t := Nat.floor_le ht0
    have := mul_le_mul_of_nonneg_right this hn.le
    rwa [ht, div_mul_cancel₀ _ hn.ne'] at this
  · -- `lon x ≤ (i + 1) n`
    have : t ≤ (i : ℝ) + 1 := by
      rcases le_total ⌊t⌋₊ (K - 1) with h | h
      · rw [hi, min_eq_left h]
        exact (Nat.lt_floor_add_one t).le
      · rw [hi, min_eq_right h]
        have : ((K - 1 : ℕ) : ℝ) + 1 = K := by
          rw [Nat.cast_sub hK]
          ring
        rw [this]
        exact htK
    have := mul_le_mul_of_nonneg_right this hn.le
    rwa [ht, div_mul_cancel₀ _ hn.ne'] at this
  · -- not on a removed upper face
    rintro ⟨hface, hlast⟩
    have htface : t = (i : ℝ) + 1 := by
      rw [ht, hface]
      field_simp
    rcases le_total ⌊t⌋₊ (K - 1) with h | h
    · have hfl : ⌊t⌋₊ = i := by rw [hi, min_eq_left h]
      have := Nat.lt_floor_add_one t
      rw [hfl, htface] at this
      exact absurd this (lt_irrefl _)
    · have hiK1 : i = K - 1 := by rw [hi, min_eq_right h]
      simp only at hlast
      omega

end Pieces

end IsotropicVariance.Paper.Proofs.Gain.Bridge
