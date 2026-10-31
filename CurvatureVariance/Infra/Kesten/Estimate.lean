/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Kesten.Deterministic
public import CurvatureVariance.Infra.Percolation.LatticeSharpness
import CurvatureVariance.Statements.Inputs.MeasureReachableSphereLe
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kesten's estimate

**Kesten's estimate** in the form of [ADH, Theorem 4.6, in its proof, p. 77], cited in Section
`sec:prelim`: if `F(0) < p_c(d)`, there are `a, C₉ > 0` such that, for every law `P` of independent
weights with law `F` and every `n ≥ 1`, the probability that some self-avoiding path from the origin
with at least `n` edges has passage time below `an` is at most `e^{-C₉ n}`.

This is [Kes86, Proposition 5.8], p. 182, of H. Kesten, "Aspects of first passage percolation",
École d'Été de Probabilités de Saint-Flour XIV, Lecture Notes in Mathematics 1180, Springer (1986),
under `F(0) < p_c`: the proposition assumes `F(0) < p_T`, and `p_T = p_c` by [DCT, Theorem 1.1].
These notes are not the [Kes93] of the papers.

The proof avoids the van den Berg–Kesten inequality:

1. choose `ε > 0` with `p = F([0, ε]) < p_c` (`exists_smallWeightProb_lt`); the `ε`-open edges are
   Bernoulli(`p`) percolation (`CurvatureVariance.Infra.Kesten.Coupling`);
2. one-arm decay below `p_c` ([Duminil-Copin and Tassion, Thm 1.1(1)] on `ℤ^d`,
   `Infra.Percolation.measure_reachable_sphere_le`) makes a block of side `L` bad
   with probability at most `L^d e^{-cL}`, as small as needed (`exists_block_side`);
3. a self-avoiding path with `n ≥ (3L)^d` edges and passage time below `an`,
   `a = ε / (4·3^d L^d)`, visits a connected set of at least `n/L^d` blocks, at least half of them
   bad (`CurvatureVariance.Infra.Kesten.Deterministic`); the visited blocks are the support of a
   walk of length at most twice their number (`exists_walk_support_eq_image`), and a union bound
   over such walks with the independence of separated blocks
   (`CurvatureVariance.Infra.Kesten.BadBlocks`) gives `e^{-cn}` (`measure_cheapPath_le_of_large`);
4. small `n` (`measure_cheapPath_le_of_small`): with `a ≤ ε/(3L)^d`, the event forces an
   `ε`-open edge at the origin, whose probability is `1 - (1-p)^{2d} < 1`.

`measure_exists_isPath_walkCost_lt_le` has exactly the statement of
`CurvatureVariance.measure_exists_isPath_walkCost_lt_le`, which then follows by `exact`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.Kesten

open CurvatureVariance.Infra.Percolation

variable {m : ℕ}

/-! ### The parameters -/

/-- **A level below the critical probability**: if `F({0}) < p_c`, there is `ε > 0` with
`F([0, ε]) < p_c` (continuity of `F` from above). -/
theorem exists_smallWeightProb_lt (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (h0 : F {0} < ENNReal.ofReal (bondCriticalProb m)) :
    ∃ ε : ℝ≥0, 0 < ε ∧ (smallWeightProb F ε : ℝ) < bondCriticalProb m := by
  set s : ℕ → Set ℝ≥0 := fun k => Set.Iic (1 / ((k : ℝ≥0) + 1))
  have hanti : Antitone s := by
    intro i j hij
    refine Set.Iic_subset_Iic.2 ?_
    gcongr
  have hinter : (⋂ k, s k) = {0} := by
    ext x
    simp only [s, Set.mem_iInter, Set.mem_Iic, Set.mem_singleton_iff]
    refine ⟨fun h => ?_, fun h k => by simp [h]⟩
    by_contra hx
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (pos_iff_ne_zero.2 hx)
    exact absurd (h k) (not_le.2 hk)
  have ht := tendsto_measure_iInter_atTop (μ := F) (fun k => measurableSet_Iic.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds h0)).exists
  refine ⟨1 / ((k : ℝ≥0) + 1), by positivity, ?_⟩
  exact ENNReal.toReal_lt_of_lt_ofReal hk

/-- **A block side**: for `c > 0` and `t > 0` there is `L ≥ 1` with `L^d e^{-cL} ≤ t`. -/
theorem exists_block_side {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) (d : ℕ) :
    ∃ L : ℕ, 1 ≤ L ∧ (L : ℝ) ^ d * Real.exp (-(c * L)) ≤ t := by
  have h1 : Tendsto (fun L : ℕ => (c * L) ^ d * Real.exp (-(c * L))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have h2 : ∀ᶠ L : ℕ in atTop, (c * L) ^ d * Real.exp (-(c * L)) < t * c ^ d :=
    h1.eventually (gt_mem_nhds (by positivity))
  obtain ⟨L, hL, hL1⟩ := (h2.and (eventually_ge_atTop 1)).exists
  refine ⟨L, hL1, ?_⟩
  have hcd : 0 < c ^ d := pow_pos hc d
  rw [mul_pow] at hL
  have : (L : ℝ) ^ d * Real.exp (-(c * L)) * c ^ d < t * c ^ d := by linarith
  exact (lt_of_mul_lt_mul_right this hcd.le).le

/-! ### Long paths -/

open Classical in
/-- At least half of the blocks of `Z` are bad. -/
def badHalf (L : ℕ) (Z : Finset (Vertex m)) : Set (Edge m → Bool) :=
  {η | Z.card ≤ 2 * (Z.filter fun z => η ∈ badBlock L z).card}

/-- The walks `Γ` of blocks from the origin of length `ℓ ≤ 2n` whose support `Z` has at least
`(n + 1)/L^d` blocks and at least `(ℓ + 2)/2` blocks, at least half of them bad. -/
noncomputable def animalEvent (L n : ℕ) : Set (Edge m → Bool) :=
  ⋃ ℓ ∈ Finset.range (2 * n + 1), ⋃ w ∈ cubeFinset (0 : Vertex m) ℓ,
    ⋃ Γ ∈ (latticeGraph m).finsetWalkLength ℓ 0 w,
      {η | n + 1 ≤ Γ.support.toFinset.card * L ^ (m + 1) ∧ ℓ + 2 ≤ 2 * Γ.support.toFinset.card ∧
        η ∈ badHalf L Γ.support.toFinset}

/-- The origin lies in the block of index `0`. -/
theorem block_zero (L : ℕ) : block L (0 : Vertex m) = 0 := by
  ext <;> simp [block]

/-- A walk is at least as costly as each of its prefixes. -/
theorem walkCost_take_le (ω : Config m) {u v : Vertex m} (γ : (latticeGraph m).Walk u v) (n : ℕ) :
    walkCost ω (γ.take n) ≤ walkCost ω γ :=
  walkCost_le_of_darts_sublist ω _ _
    (by rw [SimpleGraph.Walk.darts_take]; exact List.take_sublist _ _)

/-- **The animal inclusion**: a self-avoiding path from the origin with at least `n ≥ (3L)^d`
edges and passage time below `an`, `a = ε/(4·3^d L^d)`, produces a walk of blocks in
`animalEvent L n` for the `ε`-open edges. -/
theorem cheapPath_subset_animalEvent {L : ℕ} (hL : 1 ≤ L) {ε : ℝ≥0} (hε : 0 < ε) {n : ℕ}
    (hn : (3 * L) ^ (m + 1) ≤ n) :
    {ω : Config m | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v), γ.IsPath ∧ n ≤ γ.length ∧
        (walkCost ω γ : ℝ) < (ε : ℝ) / (4 * 3 ^ (m + 1) * L ^ (m + 1)) * n} ⊆
      openConfig ε ⁻¹' animalEvent L n := by
  classical
  rintro ω ⟨v, γ, hγ, hnγ, hcost⟩
  have hL0 : 0 < L := hL
  -- truncate to exactly `n` edges
  set γ' := γ.take n
  have hγ' : γ'.IsPath := hγ.take n
  have hlen : γ'.length = n := by
    rw [SimpleGraph.Walk.take_length]; exact min_eq_left hnγ
  have hcost' : (walkCost ω γ' : ℝ) < (ε : ℝ) / (4 * 3 ^ (m + 1) * L ^ (m + 1)) * n :=
    lt_of_le_of_lt (by exact_mod_cast walkCost_take_le ω γ n) hcost
  obtain ⟨hhalf, hn1⟩ := card_le_two_mul_card_bad hL ω hε hγ' hn hlen.ge hcost'
  obtain ⟨w, Γ, hΓ, hΓlen⟩ := exists_walk_support_eq_image (block L)
    (fun x y h => block_eq_or_adj hL0 h) γ'
  set Γ' := Γ.copy (block_zero L) rfl
  have hΓ' : Γ'.support.toFinset = γ'.support.toFinset.image (block L) := by
    simp [Γ', hΓ]
  have hZle : (γ'.support.toFinset.image (block L)).card ≤ n + 1 := by
    refine Finset.card_image_le.trans ((List.toFinset_card_le _).trans ?_)
    rw [SimpleGraph.Walk.length_support, hlen]
  have hΓ'len : Γ'.length + 2 ≤ 2 * Γ'.support.toFinset.card := by
    simpa [Γ', hΓ] using hΓlen
  simp only [Set.mem_preimage, animalEvent, Set.mem_iUnion]
  refine ⟨Γ'.length, Finset.mem_range.2 (by rw [hΓ'] at hΓ'len; omega), w, ?_,
    Γ', SimpleGraph.mem_finsetWalkLength_iff.2 rfl, ?_⟩
  · refine mem_cubeFinset ?_
    simpa using latticeSupNorm_sub_le_length Γ'
  · refine ⟨by rw [hΓ']; exact hn1, hΓ'len, ?_⟩
    rw [hΓ']
    exact hhalf

open Classical in
/-- **The union bound over walks of blocks.** If every block is bad with probability at most
`θ^{10·7^d}` and `2d θ ≤ 1/2`, then `animalEvent L n` has probability at most `2 θ^{2K}`,
`K = ⌊n/L^d⌋`. -/
theorem percolation_animalEvent_le {L : ℕ} (hL : 1 ≤ L) (p : I) {θ : ℝ≥0∞}
    (hθ : (2 * (m + 1) : ℝ≥0∞) * θ ≤ 2⁻¹)
    (hbad : ∀ z : Vertex m, percolation (latticeGraph m) p (badBlock L z) ≤
      θ ^ (10 * 7 ^ (m + 1)))
    (n : ℕ) :
    percolation (latticeGraph m) p (animalEvent L n) ≤ 2 * θ ^ (2 * (n / L ^ (m + 1))) := by
  have hL0 : 0 < L := hL
  have hLd : 0 < L ^ (m + 1) := pow_pos hL _
  have hθ2 : 2 * θ ≤ 1 := by
    calc 2 * θ ≤ (2 * (m + 1) : ℝ≥0∞) * θ := by
          gcongr
          calc (2 : ℝ≥0∞) = 2 * 1 := (mul_one 2).symm
            _ ≤ 2 * ((m : ℝ≥0∞) + 1) := by gcongr; exact le_add_self
      _ ≤ 2⁻¹ := hθ
      _ ≤ 1 := ENNReal.inv_le_one.2 (by norm_num)
  have hθ1 : θ ≤ 1 := le_trans (le_mul_of_one_le_left bot_le (by norm_num)) hθ2
  set K := n / L ^ (m + 1)
  -- one walk of blocks
  have hone : ∀ ℓ (w : Vertex m) (Γ : (latticeGraph m).Walk 0 w), Γ.length = ℓ →
      percolation (latticeGraph m) p
          {η | n + 1 ≤ Γ.support.toFinset.card * L ^ (m + 1) ∧
            ℓ + 2 ≤ 2 * Γ.support.toFinset.card ∧ η ∈ badHalf L Γ.support.toFinset} ≤
        θ ^ ℓ * θ ^ (2 * K) := by
    intro ℓ w Γ _
    by_cases hc : n + 1 ≤ Γ.support.toFinset.card * L ^ (m + 1) ∧
        ℓ + 2 ≤ 2 * Γ.support.toFinset.card
    · refine (measure_mono fun η hη => hη.2.2).trans ?_
      refine (percolation_badHalf_le hL0 p hθ2 hbad _).trans ?_
      rw [← pow_add]
      refine pow_le_pow_right_of_le_one' hθ1 ?_
      have hK : K * L ^ (m + 1) ≤ n := Nat.div_mul_le_self n _
      have hKZ : K ≤ Γ.support.toFinset.card := by
        by_contra hcon
        have : Γ.support.toFinset.card * L ^ (m + 1) < K * L ^ (m + 1) :=
          Nat.mul_lt_mul_of_pos_right (not_le.1 hcon) hLd
        omega
      omega
    · refine le_trans (measure_mono (t := (∅ : Set (Edge m → Bool)))
        fun η hη => absurd ⟨hη.1, hη.2.1⟩ hc) ?_
      simp
  calc percolation (latticeGraph m) p (animalEvent L n)
      ≤ ∑ ℓ ∈ Finset.range (2 * n + 1), ∑ w ∈ cubeFinset (0 : Vertex m) ℓ,
          ∑ Γ ∈ (latticeGraph m).finsetWalkLength ℓ 0 w, θ ^ ℓ * θ ^ (2 * K) := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun Γ hΓ => ?_)
        exact hone ℓ w Γ (SimpleGraph.mem_finsetWalkLength_iff.1 hΓ)
    _ = ∑ ℓ ∈ Finset.range (2 * n + 1),
          ((∑ w ∈ cubeFinset (0 : Vertex m) ℓ,
            ((latticeGraph m).finsetWalkLength ℓ 0 w).card : ℕ) : ℝ≥0∞) *
            (θ ^ ℓ * θ ^ (2 * K)) := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ ℓ ∈ Finset.range (2 * n + 1), ((2 * (m + 1)) ^ ℓ : ℕ) * (θ ^ ℓ * θ ^ (2 * K)) := by
        refine Finset.sum_le_sum fun ℓ _ => ?_
        gcongr
        exact sum_card_finsetWalkLength_le (fun v => (degree_latticeGraph v).le) ℓ 0 _
    _ = (∑ ℓ ∈ Finset.range (2 * n + 1), ((2 * (m + 1) : ℝ≥0∞) * θ) ^ ℓ) * θ ^ (2 * K) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        have hD : (((2 * (m + 1)) ^ ℓ : ℕ) : ℝ≥0∞) = (2 * ((m : ℝ≥0∞) + 1)) ^ ℓ := by
          push_cast; rfl
        rw [hD, mul_pow (2 * ((m : ℝ≥0∞) + 1)) θ ℓ, mul_assoc]
    _ ≤ (∑ ℓ ∈ Finset.range (2 * n + 1), (2⁻¹ : ℝ≥0∞) ^ ℓ) * θ ^ (2 * K) := by
        gcongr
    _ ≤ 2 * θ ^ (2 * K) := by
        gcongr
        calc ∑ ℓ ∈ Finset.range (2 * n + 1), (2⁻¹ : ℝ≥0∞) ^ ℓ
            ≤ ∑' ℓ, (2⁻¹ : ℝ≥0∞) ^ ℓ := ENNReal.sum_le_tsum _
          _ = 2 := by rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

/-- **Kesten's estimate for long paths.** With `θ = (4(m+1))⁻¹`, if every block of side `L` is
bad with probability at most `θ^{10·7^d}` for the `ε`-open edges, then for `n ≥ (3L)^d` the
probability that a self-avoiding path from the origin with at least `n` edges costs less than
`an`, `a = ε/(4·3^d L^d)`, is at most `θ^{⌊n/L^d⌋}`. -/
theorem measure_cheapPath_le_of_large {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} [IsProbabilityMeasure P] (hP : IsIIDWeights P F) {ε : ℝ≥0}
    (hε : 0 < ε) {L : ℕ} (hL : 1 ≤ L)
    (hbad : ∀ z : Vertex m, percolation (latticeGraph m) (smallWeightProb F ε) (badBlock L z) ≤
      ENNReal.ofReal (4 * ((m : ℝ) + 1))⁻¹ ^ (10 * 7 ^ (m + 1)))
    {n : ℕ} (hn : (3 * L) ^ (m + 1) ≤ n) :
    P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v), γ.IsPath ∧ n ≤ γ.length ∧
        (walkCost ω γ : ℝ) < (ε : ℝ) / (4 * 3 ^ (m + 1) * L ^ (m + 1)) * n} ≤
      ENNReal.ofReal (4 * ((m : ℝ) + 1))⁻¹ ^ (n / L ^ (m + 1)) := by
  set θ := ENNReal.ofReal (4 * ((m : ℝ) + 1))⁻¹ with hθdef
  have hθ : (2 * (m + 1) : ℝ≥0∞) * θ ≤ 2⁻¹ := by
    have h : (2 * (m + 1) : ℝ≥0∞) = ENNReal.ofReal (2 * ((m : ℝ) + 1)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by norm_num)]
      simp
    rw [h, hθdef, ← ENNReal.ofReal_mul (by positivity)]
    have : 2 * ((m : ℝ) + 1) * (4 * ((m : ℝ) + 1))⁻¹ = 2⁻¹ := by
      field_simp; ring
    rw [this, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  have hLd : 0 < L ^ (m + 1) := pow_pos hL _
  have hK : 1 ≤ n / L ^ (m + 1) := by
    rw [Nat.one_le_div_iff hLd]
    refine le_trans ?_ hn
    rw [mul_pow]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)
  have hθ1 : 2 * θ ≤ 1 := by
    calc 2 * θ ≤ (2 * (m + 1) : ℝ≥0∞) * θ := by
          gcongr
          calc (2 : ℝ≥0∞) = 2 * 1 := (mul_one 2).symm
            _ ≤ 2 * ((m : ℝ≥0∞) + 1) := by gcongr; exact le_add_self
      _ ≤ 2⁻¹ := hθ
      _ ≤ 1 := ENNReal.inv_le_one.2 (by norm_num)
  calc P _ ≤ P (openConfig ε ⁻¹' animalEvent L n) :=
        measure_mono (cheapPath_subset_animalEvent hL hε hn)
    _ ≤ (P.map (openConfig ε)) (animalEvent L n) :=
        Measure.le_map_apply (measurable_openConfig ε).aemeasurable _
    _ = percolation (latticeGraph m) (smallWeightProb F ε) (animalEvent L n) := by
        rw [map_openConfig_of_isIIDWeights hP]
    _ ≤ 2 * θ ^ (2 * (n / L ^ (m + 1))) := percolation_animalEvent_le hL _ hθ hbad n
    _ = 2 * θ ^ (n / L ^ (m + 1)) * θ ^ (n / L ^ (m + 1)) := by
        rw [two_mul (n / _), pow_add, mul_assoc]
    _ ≤ 2 * θ * θ ^ (n / L ^ (m + 1)) := by
        gcongr
        exact pow_le_of_le_one bot_le (le_trans (le_mul_of_one_le_left bot_le (by norm_num)) hθ1)
          (by omega)
    _ ≤ 1 * θ ^ (n / L ^ (m + 1)) := by gcongr
    _ = θ ^ (n / L ^ (m + 1)) := one_mul _

/-! ### Short paths -/

/-- The edges at the origin. -/
noncomputable def originEdges (m : ℕ) : Finset (Edge m) :=
  ((latticeGraph m).neighborFinset 0).attach.image fun y =>
    ⟨s((0 : Vertex m), y.1), (SimpleGraph.mem_neighborFinset _ _ _).1 y.2⟩

/-- With probability at most `1 - (1-p)^{2d}`, some edge at the origin is open. -/
theorem percolation_exists_open_origin_le (p : I) :
    percolation (latticeGraph m) p
        {η | ∃ y, ∃ h : (latticeGraph m).Adj 0 y, η ⟨s(0, y), h⟩ = true} ≤
      1 - ENNReal.ofReal ((1 - p) ^ (originEdges m).card) := by
  set A : Set (Edge m → Bool) := Set.pi (originEdges m : Set (Edge m)) fun _ => {false}
  have hA : MeasurableSet A :=
    MeasurableSet.pi (Finset.countable_toSet _) fun _ _ => measurableSet_singleton _
  have hsub : {η : Edge m → Bool | ∃ y, ∃ h : (latticeGraph m).Adj 0 y, η ⟨s(0, y), h⟩ = true} ⊆
      Aᶜ := by
    rintro η ⟨y, h, hη⟩ hηA
    have hmem : (⟨s(0, y), h⟩ : Edge m) ∈ originEdges m := by
      refine Finset.mem_image.2 ⟨⟨y, (SimpleGraph.mem_neighborFinset _ _ _).2 h⟩,
        Finset.mem_attach _ _, rfl⟩
    have := hηA _ (Finset.mem_coe.2 hmem)
    simp only [Set.mem_singleton_iff] at this
    rw [this] at hη
    exact Bool.false_ne_true hη
  have hpi : percolation (latticeGraph m) p A =
      ENNReal.ofReal ((1 - p) ^ (originEdges m).card) := by
    rw [percolation, bernoulliProduct, Measure.infinitePi_pi _ fun _ _ => measurableSet_singleton _]
    simp only [bernoulliMeasure_false, Finset.prod_const]
    rw [ENNReal.ofReal_pow (by have := p.2.2; linarith)]
  refine (measure_mono hsub).trans ?_
  rw [prob_compl_eq_one_sub hA, hpi]

/-- **Kesten's estimate for short paths**: if `a n ≤ ε`, a self-avoiding path from the origin
with at least `n ≥ 1` edges and passage time below `a n` starts with an `ε`-open edge, so the
probability is at most `1 - (1 - F([0, ε]))^{2d}`. -/
theorem measure_cheapPath_le_of_small {F : Measure ℝ≥0} [IsProbabilityMeasure F]
    {P : Measure (Config m)} [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (ε : ℝ≥0)
    {a : ℝ} {n : ℕ} (hn : 1 ≤ n) (han : a * n ≤ ε) :
    P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v), γ.IsPath ∧ n ≤ γ.length ∧
        (walkCost ω γ : ℝ) < a * n} ≤
      1 - ENNReal.ofReal ((1 - smallWeightProb F ε) ^ (originEdges m).card) := by
  have hsub : {ω : Config m | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v), γ.IsPath ∧
      n ≤ γ.length ∧ (walkCost ω γ : ℝ) < a * n} ⊆
      openConfig ε ⁻¹' {η | ∃ y, ∃ h : (latticeGraph m).Adj 0 y, η ⟨s(0, y), h⟩ = true} := by
    rintro ω ⟨v, γ, -, hlen, hcost⟩
    cases γ with
    | nil => simp at hlen; omega
    | @cons _ y _ h q =>
      refine ⟨y, h, ?_⟩
      have h1 : (ω ⟨s(0, y), h⟩ : ℝ) ≤ walkCost ω (SimpleGraph.Walk.cons h q) := by
        have : ω ⟨s(0, y), h⟩ ≤ walkCost ω (SimpleGraph.Walk.cons h q) := by
          simp only [walkCost, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
          exact le_self_add
        exact_mod_cast this
      have h2 : (ω ⟨s(0, y), h⟩ : ℝ) ≤ ε := by linarith
      simpa [openConfig] using h2
  calc P _ ≤ P (openConfig ε ⁻¹' _) := measure_mono hsub
    _ ≤ (P.map (openConfig ε)) _ := Measure.le_map_apply (measurable_openConfig ε).aemeasurable _
    _ = percolation (latticeGraph m) (smallWeightProb F ε) _ := by
        rw [map_openConfig_of_isIIDWeights hP]
    _ ≤ _ := percolation_exists_open_origin_le _

/-! ### Kesten's estimate -/

/-- **Kesten's estimate**, [Kes86, Proposition 5.8] (cited in Section `sec:prelim`), in the form of
[ADH, Theorem 4.6, in its proof, p. 77]: if `F(0) < p_c`, there are `a, C₉ > 0` such that for all
`n ≥ 1`,
`P(∃ self-avoiding γ starting at 0 with #γ ≥ n but with T(γ) < an) ≤ e^{−C₉ n}`. The constants
depend only on `d` and the law `F`. Exactly the statement
`CurvatureVariance.measure_exists_isPath_walkCost_lt_le`. -/
theorem measure_exists_isPath_walkCost_lt_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (h0 : F {0} < ENNReal.ofReal (bondCriticalProb m)) :
    ∃ a C₉ : ℝ, 0 < a ∧ 0 < C₉ ∧ ∀ (P : Measure (Config m)) [IsProbabilityMeasure P],
      IsIIDWeights P F → ∀ n : ℕ, 1 ≤ n →
        P {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v),
            γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < a * n} ≤
          ENNReal.ofReal (Real.exp (-(C₉ * n))) := by
  -- the level `ε` and the one-arm decay at `p = F([0, ε])`
  obtain ⟨ε, hε, hp⟩ := exists_smallWeightProb_lt F h0
  set p := smallWeightProb F ε with hpdef
  obtain ⟨c, hc, hdecay⟩ := CurvatureVariance.measure_reachable_sphere_le hm p hp
  have hp1 : (p : ℝ) < 1 := hp.trans_le (bondCriticalProb_bounds m).2
  -- the block side
  set θ₀ : ℝ := (4 * ((m : ℝ) + 1))⁻¹ with hθ₀def
  have hθ₀ : 0 < θ₀ := by positivity
  obtain ⟨L, hL, hLc⟩ := exists_block_side hc (pow_pos hθ₀ (10 * 7 ^ (m + 1))) (m + 1)
  have hbad : ∀ z : Vertex m, percolation (latticeGraph m) p (badBlock L z) ≤
      ENNReal.ofReal θ₀ ^ (10 * 7 ^ (m + 1)) := by
    intro z
    refine (percolation_badBlock_le hdecay hL z).trans ?_
    rw [← ENNReal.ofReal_pow hθ₀.le, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact hLc)
  -- the constants
  set n₁ : ℕ := (3 * L) ^ (m + 1) with hn₁def
  have hn₁ : 1 ≤ n₁ := Nat.one_le_pow _ _ (by omega)
  have hLd : 0 < L ^ (m + 1) := pow_pos hL _
  set a₀ : ℝ := (ε : ℝ) / (4 * 3 ^ (m + 1) * L ^ (m + 1)) with ha₀def
  set a₁ : ℝ := (ε : ℝ) / n₁ with ha₁def
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have ha₀ : 0 < a₀ := by positivity
  have ha₁ : 0 < a₁ := by
    have : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
    positivity
  set q : ℝ := 1 - (1 - (p : ℝ)) ^ (originEdges m).card with hqdef
  have hq1 : q < 1 := by
    have : 0 < (1 - (p : ℝ)) ^ (originEdges m).card := pow_pos (by linarith) _
    linarith
  have hq0 : 0 ≤ (1 - (p : ℝ)) ^ (originEdges m).card := pow_nonneg (by linarith) _
  have hmax0 : 0 < max q 2⁻¹ := lt_max_of_lt_right (by norm_num)
  have hmax1 : max q 2⁻¹ < 1 := max_lt hq1 (by norm_num)
  set Cs : ℝ := -Real.log (max q 2⁻¹) / n₁ with hCsdef
  have hCs : 0 < Cs := by
    have : Real.log (max q 2⁻¹) < 0 := Real.log_neg hmax0 hmax1
    have : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
    exact div_pos (by linarith) this
  set lam : ℝ := Real.log (4 * ((m : ℝ) + 1)) with hlamdef
  have hlam : 0 < lam := Real.log_pos (by have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith)
  set Cl : ℝ := lam / (2 * L ^ (m + 1)) with hCldef
  have hCl : 0 < Cl := by positivity
  refine ⟨min a₀ a₁, min Cl Cs, lt_min ha₀ ha₁, lt_min hCl hCs, ?_⟩
  intro P _ hP n hn
  by_cases hlarge : n₁ ≤ n
  · -- long paths
    have hsub : {ω : Config m | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v),
        γ.IsPath ∧ n ≤ γ.length ∧ (walkCost ω γ : ℝ) < min a₀ a₁ * n} ⊆
        {ω | ∃ (v : Vertex m) (γ : (latticeGraph m).Walk 0 v), γ.IsPath ∧ n ≤ γ.length ∧
          (walkCost ω γ : ℝ) < (ε : ℝ) / (4 * 3 ^ (m + 1) * L ^ (m + 1)) * n} := by
      rintro ω ⟨v, γ, hγ, hlen, hcost⟩
      exact ⟨v, γ, hγ, hlen, hcost.trans_le
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))⟩
    refine (measure_mono hsub).trans ((measure_cheapPath_le_of_large hP hε hL hbad hlarge).trans ?_)
    set K := n / L ^ (m + 1)
    have hK1 : 1 ≤ K := by
      rw [Nat.one_le_div_iff hLd]
      refine le_trans ?_ hlarge
      rw [hn₁def, mul_pow]
      exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)
    have hnK : n ≤ 2 * L ^ (m + 1) * K := by
      have h1 : L ^ (m + 1) * K + n % L ^ (m + 1) = n := Nat.div_add_mod n _
      have h2 := Nat.mod_lt n hLd
      have h3 : L ^ (m + 1) * 1 ≤ L ^ (m + 1) * K := Nat.mul_le_mul_left _ hK1
      have h4 : 2 * L ^ (m + 1) * K = L ^ (m + 1) * K + L ^ (m + 1) * K := by ring
      rw [h4]
      omega
    have hθexp : θ₀ = Real.exp (-lam) := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
    rw [← ENNReal.ofReal_pow hθ₀.le, hθexp, ← Real.exp_nat_mul]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hnK' : (n : ℝ) ≤ 2 * L ^ (m + 1) * K := by exact_mod_cast hnK
    have hC : min Cl Cs * n ≤ Cl * n :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)
    have hCl' : Cl * n ≤ lam * K := by
      rw [hCldef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  · -- short paths
    push Not at hlarge
    have han : min a₀ a₁ * n ≤ ε := by
      calc min a₀ a₁ * n ≤ a₁ * n :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n)
        _ ≤ a₁ * n₁ := mul_le_mul_of_nonneg_left (by exact_mod_cast hlarge.le) ha₁.le
        _ = ε := by
            rw [ha₁def, div_mul_cancel₀]
            exact_mod_cast (show n₁ ≠ 0 by omega)
    refine (measure_cheapPath_le_of_small hP ε hn han).trans ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 - (1 - (smallWeightProb F ε : ℝ)) ^ (originEdges m).card ≤ max q 2⁻¹ :=
      le_max_left _ _
    have h2 : max q 2⁻¹ = Real.exp (-(Cs * n₁)) := by
      rw [hCsdef, div_mul_cancel₀ _ (by exact_mod_cast (show n₁ ≠ 0 by omega)), neg_neg,
        Real.exp_log hmax0]
    refine h1.trans (h2 ▸ Real.exp_le_exp.2 ?_)
    have h3 : min Cl Cs * n ≤ Cs * n :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n)
    have h4 : Cs * n ≤ Cs * n₁ :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hlarge.le) hCs.le
    linarith

end CurvatureVariance.Infra.Kesten
