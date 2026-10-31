/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Kesten.Blocks
public import CurvatureVariance.Infra.Kesten.Coupling
public import CurvatureVariance.Infra.Kesten.Walks
public import CurvatureVariance.Infra.EfronStein.Coordinates

/-!
# Bad blocks in Bernoulli percolation

The probabilistic half of the block argument for Kesten's estimate, in Bernoulli bond
percolation on `ℤ^d`, `d = m + 1`, with blocks `B(z) = Lz + [0, L)^d`
(`CurvatureVariance.Infra.Kesten.Blocks`).

* `localArm L x`: `x` is joined by an open walk, every edge of which has an endpoint at `ℓ^∞`
  distance less than `L` from `x`, to a vertex at `ℓ^∞` distance exactly `L`.
* `badBlock L z`: some vertex of `B(z)` has a local arm. It depends only on the edges near the
  block (`dependsOn_badBlock`), and has probability at most `L^d e^{-cL}` under the one-arm bound
  (`percolation_badBlock_le`).
* `percolation_iInter_badBlock_eq_prod`: bad events of blocks at pairwise `ℓ^∞` distance at least
  `4` are independent.
* `percolation_badHalf_le`: if every block is bad with probability at most `θ^{10·7^d}`,
  `2θ ≤ 1`, then at least half of the blocks of a finite set `Z` are bad with probability at most
  `θ^{4|Z|}` (a union over the bad subsets, a `4`-separated subfamily, and independence).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.Kesten

open CurvatureVariance.Infra.Percolation

variable {m : ℕ}

/-! ### Local arms and bad blocks -/

/-- The edges with an endpoint at `ℓ^∞` distance less than `L` from `x`. -/
def ballEdges (L : ℕ) (x : Vertex m) : Set (Sym2 (Vertex m)) :=
  {e | ∃ u ∈ e, latticeSupNorm (u - x) < L}

/-- **A local arm at `x`**: `x` is joined, by an open walk whose edges all have an endpoint at
`ℓ^∞` distance less than `L` from `x`, to a vertex at `ℓ^∞` distance exactly `L`. -/
def localArm (L : ℕ) (x : Vertex m) : Set (Edge m → Bool) :=
  {η | ∃ y ∈ {y | latticeSupNorm (y - x) = L},
    OpenConnected (latticeGraph m) η (ballEdges L x) x y}

/-- **A bad block**: some vertex of the block `B(z)` has a local arm. -/
def badBlock (L : ℕ) (z : Vertex m) : Set (Edge m → Bool) :=
  ⋃ x ∈ blockFinset L z, localArm L x

/-- Local arms are measurable events. -/
theorem measurableSet_localArm (L : ℕ) (x : Vertex m) : MeasurableSet (localArm L x) :=
  measurableSet_exists_openConnected _ _ _

/-- Bad blocks are measurable events. -/
theorem measurableSet_badBlock (L : ℕ) (z : Vertex m) : MeasurableSet (badBlock L z) :=
  Finset.measurableSet_biUnion _ fun x _ => measurableSet_localArm L x

/-- The edges near the local arms of the vertices of a block are edges near the block. -/
theorem ballEdges_subset_blockEdges {L : ℕ} (hL : 0 < L) {x z : Vertex m}
    (hx : x ∈ blockFinset L z) :
    {e : Edge m | (e : Sym2 (Vertex m)) ∈ ballEdges L x} ⊆ blockEdges L z := by
  rintro e ⟨u, hu, hux⟩
  refine ⟨u, hu, ?_⟩
  rw [← (mem_blockFinset hL).1 hx]
  exact latticeSupNorm_block_sub_le_one hL hux.le

/-- **Locality of bad blocks**: whether `B(z)` is bad depends only on the edges with an endpoint
in the tripled block. -/
theorem dependsOn_badBlock {L : ℕ} (hL : 0 < L) (z : Vertex m) :
    DependsOn (· ∈ badBlock L z) (blockEdges L z) := by
  intro η η' h
  have hx : ∀ x ∈ blockFinset L z, (η ∈ localArm L x) = (η' ∈ localArm L x) := fun x hx =>
    (dependsOn_exists_openConnected (G := latticeGraph m) (ballEdges L x) x
      {y | latticeSupNorm (y - x) = L}).mono (ballEdges_subset_blockEdges hL hx)
      fun e he => h e he
  simp only [badBlock, Set.mem_iUnion, eq_iff_iff]
  exact ⟨fun ⟨x, hxz, hη⟩ => ⟨x, hxz, (hx x hxz) ▸ hη⟩,
    fun ⟨x, hxz, hη⟩ => ⟨x, hxz, (hx x hxz).symm ▸ hη⟩⟩

/-- **A block is bad with probability at most `L^d e^{-cL}`** under the one-arm bound
`P_p[0 ↔ ∂Λ_n] ≤ e^{-cn}`, `n ≥ 1`. -/
theorem percolation_badBlock_le {p : I} {c : ℝ}
    (hc : ∀ n : ℕ, 1 ≤ n →
      setBernoulli (Set.univ : Set (Edge m)) p
          {S | ∃ x : Vertex m, latticeSupNorm x = n ∧
            (CurvatureVariance.openGraph m S).Reachable 0 x} ≤
        ENNReal.ofReal (Real.exp (-(c * n))))
    {L : ℕ} (hL : 1 ≤ L) (z : Vertex m) :
    percolation (latticeGraph m) p (badBlock L z) ≤
      (L ^ (m + 1) : ℕ) * ENNReal.ofReal (Real.exp (-(c * L))) := by
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ x ∈ blockFinset L z, percolation (latticeGraph m) p (localArm L x)
      ≤ ∑ _x ∈ blockFinset L z, ENNReal.ofReal (Real.exp (-(c * L))) := by
        refine Finset.sum_le_sum fun x _ => (measure_mono ?_).trans (percolation_arm_le hc x hL)
        rintro η ⟨y, hy, hη⟩
        exact ⟨y, hy, hη.mono_edges (Set.subset_univ _)⟩
    _ = ((blockFinset L z).card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(c * L))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L ^ (m + 1) : ℕ) * ENNReal.ofReal (Real.exp (-(c * L))) := by
        gcongr
        exact_mod_cast card_blockFinset_le L z

/-! ### Independence of separated bad blocks -/

/-- An event of a product of Boolean coordinates that depends only on the coordinates in `D` is
measurable for the σ-algebra of those coordinates. -/
theorem measurableSet_coordinateSigma_of_dependsOn {ι : Type*} {A : Set (ι → Bool)} {D : Set ι}
    (hA : MeasurableSet A) (h : DependsOn (· ∈ A) D) :
    MeasurableSet[Infra.EfronStein.coordinateSigma (fun _ : ι => Bool) D] A :=
  ⟨extendFalse D ⁻¹' A, measurable_extendFalse D hA, (eq_preimage_restrict_of_dependsOn h).symm⟩

/-- **Bad events of blocks at pairwise `ℓ^∞` distance at least `4` are independent.** -/
theorem percolation_iInter_badBlock_eq_prod {L : ℕ} (hL : 0 < L) (p : I)
    (B : Finset (Vertex m)) (hB : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → 4 ≤ latticeSupNorm (a - b)) :
    percolation (latticeGraph m) p (⋂ z ∈ B, badBlock L z) =
      ∏ z ∈ B, percolation (latticeGraph m) p (badBlock L z) := by
  classical
  let S : Vertex m → Set (Edge m) := fun z => if z ∈ B then blockEdges L z else ∅
  have hS : Pairwise fun a b => Disjoint (S a) (S b) := by
    intro a b hab
    by_cases ha : a ∈ B
    · by_cases hb : b ∈ B
      · simp only [S, ha, hb, ite_true]
        exact disjoint_blockEdges hL (hB a ha b hb hab)
      · simp [S, hb]
    · simp [S, ha]
  have hind := Infra.EfronStein.iIndep_coordinateSigma (X := fun _ : Edge m => Bool)
    (fun _ => bernoulliMeasure true false p) S hS
  have hmeas : ∀ z ∈ B, MeasurableSet[Infra.EfronStein.coordinateSigma
      (fun _ : Edge m => Bool) (S z)] (badBlock L z) := by
    intro z hz
    have hSz : S z = blockEdges L z := by simp [S, hz]
    rw [hSz]
    exact measurableSet_coordinateSigma_of_dependsOn (measurableSet_badBlock L z)
      (dependsOn_badBlock hL z)
  exact (iIndep_iff _ _).1 hind B hmeas

open Classical in
/-- **At least half of the blocks of `Z` are bad with probability at most `θ^{4|Z|}`**, if every
block is bad with probability at most `θ^{10·7^d}` and `2θ ≤ 1`. -/
theorem percolation_badHalf_le {L : ℕ} (hL : 0 < L) (p : I) {θ : ℝ≥0∞} (hθ : 2 * θ ≤ 1)
    (hbad : ∀ z : Vertex m, percolation (latticeGraph m) p (badBlock L z) ≤
      θ ^ (10 * 7 ^ (m + 1)))
    (Z : Finset (Vertex m)) :
    percolation (latticeGraph m) p
        {η | Z.card ≤ 2 * (Z.filter fun z => η ∈ badBlock L z).card} ≤ θ ^ (4 * Z.card) := by
  classical
  have hθ1 : θ ≤ 1 := le_trans (by
    calc θ = 1 * θ := (one_mul θ).symm
      _ ≤ 2 * θ := by gcongr; norm_num) hθ
  set 𝓑 := Z.powerset.filter fun B => Z.card ≤ 2 * B.card
  have hsub : {η | Z.card ≤ 2 * (Z.filter fun z => η ∈ badBlock L z).card} ⊆
      ⋃ B ∈ 𝓑, ⋂ z ∈ B, badBlock L z := by
    intro η hη
    simp only [Set.mem_iUnion, Set.mem_iInter]
    refine ⟨Z.filter fun z => η ∈ badBlock L z, ?_, fun z hz => (Finset.mem_filter.1 hz).2⟩
    simp only [𝓑, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, hη⟩
  -- each bad subset with at least half of the blocks
  have hB : ∀ B ∈ 𝓑, percolation (latticeGraph m) p (⋂ z ∈ B, badBlock L z) ≤
      θ ^ (5 * Z.card) := by
    intro B hB
    simp only [𝓑, Finset.mem_filter, Finset.mem_powerset] at hB
    obtain ⟨B', hB'B, hsep, hcard⟩ := exists_subset_pairwise_not_card_le
      (fun a b : Vertex m => latticeSupNorm (b - a) ≤ 3) (fun a => by simp [latticeSupNorm_zero])
      (fun a b h => by rwa [latticeSupNorm_sub_comm]) B (7 ^ (m + 1))
      (fun a _ => card_filter_latticeSupNorm_sub_le B a 3)
    have hsep' : ∀ a ∈ B', ∀ b ∈ B', a ≠ b → 4 ≤ latticeSupNorm (a - b) := by
      intro a ha b hb hab
      have := hsep a ha b hb hab
      rw [latticeSupNorm_sub_comm] at this
      omega
    calc percolation (latticeGraph m) p (⋂ z ∈ B, badBlock L z)
        ≤ percolation (latticeGraph m) p (⋂ z ∈ B', badBlock L z) :=
          measure_mono (Set.biInter_subset_biInter_left fun z hz => hB'B hz)
      _ = ∏ z ∈ B', percolation (latticeGraph m) p (badBlock L z) :=
          percolation_iInter_badBlock_eq_prod hL p B' hsep'
      _ ≤ ∏ _z ∈ B', θ ^ (10 * 7 ^ (m + 1)) := Finset.prod_le_prod fun z _ => hbad z
      _ = θ ^ (10 * 7 ^ (m + 1) * B'.card) := by rw [Finset.prod_const, ← pow_mul]
      _ ≤ θ ^ (5 * Z.card) := pow_le_pow_right_of_le_one' hθ1 (by nlinarith)
  calc percolation (latticeGraph m) p
        {η | Z.card ≤ 2 * (Z.filter fun z => η ∈ badBlock L z).card}
      ≤ ∑ B ∈ 𝓑, percolation (latticeGraph m) p (⋂ z ∈ B, badBlock L z) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _B ∈ 𝓑, θ ^ (5 * Z.card) := Finset.sum_le_sum hB
    _ ≤ (2 ^ Z.card : ℕ) * θ ^ (5 * Z.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        rw [← Finset.card_powerset]
        exact_mod_cast Finset.card_filter_le _ _
    _ = (2 * θ) ^ Z.card * θ ^ (4 * Z.card) := by
        push_cast
        rw [mul_pow, mul_assoc, ← pow_add]
        congr 2
        ring
    _ ≤ 1 * θ ^ (4 * Z.card) := by gcongr; exact pow_le_one₀ bot_le hθ
    _ = θ ^ (4 * Z.card) := one_mul _

end CurvatureVariance.Infra.Kesten
