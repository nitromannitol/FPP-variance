/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.Slabs

/-!
# Lemma `lem:good`: the events `𝒢_N(S)`

`goodStatement_holds`: the contract `GoodStatement`, Lemma `lem:good` and its proof.

The union bound is `exists_goodEvent_bound` (`Proofs.Geometry.SlabsProb`), which is the paper's: the
Gaussian tails of [ADH, Theorem 3.13], the Chernoff bound, the mean bound of equation `eq:classical`
through its law-level form `classical_of_law`, and Kesten's bound, for the events `GoodEvent` of the
box `[−2N², 2N²]^d`.

* `slabTime_anti`: `T_P(x, y)` does not increase when `[p, q]` is enlarged, the paper's reduction of
  (2) to slabs with `min{x₁, y₁} − 2 ≤ p` and `q ≤ max{x₁, y₁} + 2`.
* `slabTime_le_of_mem_goodEvent`: (2) for every slab. A path in such a slab, of at most
  `|y − x|₁ + 2` edges, is one of the three coordinate paths through the levels
  `x₁ − 1, x₁, x₁ + 1`, which are those of the union bound.
* `isGood_of_mem_goodEvent`: on `GoodEvent`, the properties (1)–(3).

Readings. The union bound runs over these three paths for each pair `x, y`, where the paper's runs
over the pairs `p, q`. The paper's event is the one on which (1)–(3) hold, and `GoodEvent` is
contained in it: the events here are those of the union bound itself, which is all that
`GoodStatement` asks.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- A smaller slab has fewer edges. -/
theorem slabEdges_subset {p p' q q' : ℤ} (hp : p ≤ p') (hq : q' ≤ q) :
    slabEdges (m := m) p' q' ⊆ slabEdges p q := by
  rintro e ⟨x, ⟨he, h1, h2⟩ | ⟨j, he, h1, h2⟩⟩
  · exact ⟨x, Or.inl ⟨he, by omega, by omega⟩⟩
  · exact ⟨x, Or.inr ⟨j, he, by omega, by omega⟩⟩

/-- **`T_P` does not increase when `[p, q]` is enlarged** (the proof of Lemma `lem:good`). -/
theorem slabTime_anti {p p' q q' : ℤ} (hp : p ≤ p') (hq : q' ≤ q) (ω : Config m)
    (x y : Vertex m) : slabTime ω p q x y ≤ slabTime ω p' q' x y :=
  le_iInf₂ fun γ hγ => iInf₂_le_of_le γ (fun e he => slabEdges_subset hp hq (hγ e he)) le_rfl

/-- The level `c` of a coordinate path, next to `x₁`, as an index of the three paths of the event
`GoodEvent`. -/
theorem exists_fin_three_level {a c : ℤ} (h : c = a - 1 ∨ c = a ∨ c = a + 1) :
    ∃ i : Fin 3, a + ((i : ℕ) : ℤ) - 1 = c := by
  rcases h with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨2, by simp; omega⟩

/-- **Property (2) of Lemma `lem:good`** on the events, for every slab, in the paper's two steps:
by `slabTime_anti` we may take `min{x₁, y₁} − 2 ≤ p` and `q ≤ max{x₁, y₁} + 2`, and then a
coordinate path within the slab, of at most `|y − x|₁ + 2` edges, costs at most
`A(|y − x|₁ + S²)`. -/
theorem slabTime_le_of_mem_goodEvent {μ : Seminorm ℝ (Pt m)} {A a : ℝ} {R : ℕ} {S : ℝ}
    {ω : Config m} (hω : ω ∈ GoodEvent μ A a R S) {x y : Vertex m} (hx : x ∈ boxFinset R)
    (hy : y ∈ boxFinset R) {p q : ℤ} (hpq : p + 2 ≤ q) (hpx : p ≤ x.1) (hxq : x.1 ≤ q)
    (hpy : p ≤ y.1) (hyq : y.1 ≤ q) :
    slabTime ω p q x y ≤ ENNReal.ofReal (A * (oneNorm (y - x) + S ^ 2)) := by
  set p' := max p (min x.1 y.1 - 2) with hp'
  set q' := min q (max x.1 y.1 + 2) with hq'
  have hpp' : p ≤ p' := le_max_left _ _
  have hq'q : q' ≤ q := min_le_left _ _
  have hpq' : p' + 2 ≤ q' := by
    simp only [hp', hq']
    omega
  have hpx' : p' ≤ x.1 := by
    simp only [hp']
    omega
  have hxq' : x.1 ≤ q' := by
    simp only [hq']
    omega
  have hpy' : p' ≤ y.1 := by
    simp only [hp']
    omega
  have hyq' : y.1 ≤ q' := by
    simp only [hq']
    omega
  obtain ⟨h1, h2⟩ := slabLevel_bounds hpq' hpx' hxq'
  obtain ⟨i, hi⟩ := exists_fin_three_level (slabLevel_mem p' q' x)
  have hcost := hω.2.1 x hx y hy i
  rw [hi] at hcost
  refine (slabTime_anti hpp' hq'q ω x y).trans ?_
  calc slabTime ω p' q' x y ≤ (walkCost ω (slabPath x y (slabLevel p' q' x)) : ℝ≥0∞) :=
        iInf₂_le _ (slabPath_edges_mem hpx' hxq' hpy' hyq' h1 h2)
    _ = ENNReal.ofReal (walkCost ω (slabPath x y (slabLevel p' q' x)) : ℝ) :=
        (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hcost

/-- **The properties (1)–(3) of Lemma `lem:good`** on the events. The constant `C` is at least
`A d`, since (2) has the Euclidean norm where the event has `|·|₁`. -/
theorem isGood_of_mem_goodEvent {M : Model m} {A a C : ℝ} (hA : 0 ≤ A)
    (hC : A * ((m : ℝ) + 1) ≤ C) {N : ℕ} {S : ℝ} {ω : Config m} (hS : 0 ≤ S)
    (hω : ω ∈ GoodEvent M.μ.1 A a (2 * N ^ 2) S) : IsGood M C a N S ω := by
  have hbox : ∀ x : Vertex m, InBox (2 * (N : ℝ) ^ 2) x → x ∈ boxFinset (2 * N ^ 2) := by
    intro x hx
    rw [mem_boxFinset_iff]
    push_cast
    exact hx
  have hAC : A ≤ C := by
    have : A * 1 ≤ A * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only [Nat.cast_nonneg (α := ℝ) m]) hA
    linarith only [this, hC]
  refine ⟨fun x y hx hy => ?_, fun x y hx hy p q hpq hpx hxq hpy hyq => ?_,
    fun x hx y γ hγ hlen => ?_⟩
  · refine (hω.1 x (hbox x hx) y (hbox y hy)).trans
      (mul_le_mul_of_nonneg_right hAC (by positivity))
  · refine (slabTime_le_of_mem_goodEvent hω (hbox x hx) (hbox y hy) hpq hpx hxq hpy hyq).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [oneNorm_sub_eq_l1Dist]
    have h1 := l1Dist_le_mul_norm x y
    have hd : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) m]
    calc A * ((l1Dist x y : ℝ) + S ^ 2)
        ≤ A * (((m : ℝ) + 1) * ‖point y - point x‖ + ((m : ℝ) + 1) * S ^ 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add h1 (le_mul_of_one_le_left (sq_nonneg S) hd)) hA
      _ = A * ((m : ℝ) + 1) * (‖point y - point x‖ + S ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)
  · have hnot := hω.2.2 x (hbox x hx) γ.length
      ((mul_le_mul_of_nonneg_right hAC (sq_nonneg S)).trans hlen)
    by_contra hcon
    exact hnot ⟨y, γ, hγ, rfl, (not_le.1 hcon).le⟩

/-- **Lemma `lem:good`**, with its proof. The events are those of
`slabsStatement_holds`: `𝒢_N(S) = GoodEvent μ A a (2N²) (max S 1)`, increasing in `S`, with
`P(𝒢_N(S)ᶜ) ≤ e^{−cS²/2}` for `S ≥ log N` and `N` large. -/
theorem goodStatement_holds (m : ℕ) : GoodStatement m := by
  intro bd hbd
  obtain ⟨A, a, K, c, hA, ha, hK, hc, hbound⟩ := exists_goodEvent_bound bd hbd
  set C := max (A * ((m : ℝ) + 1)) (Real.sqrt (2 / c) + 1) with hCdef
  have hC1 : A * ((m : ℝ) + 1) ≤ C := le_max_left _ _
  have hC3 : Real.sqrt (2 / c) + 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by
    have := Real.sqrt_nonneg (2 / c)
    linarith only [this, hC3]
  obtain ⟨N₄, hsmall⟩ := exists_nat_goodEvent_small (m := m) hK hc
  refine ⟨a, C, ha, hC0, N₄, fun M hM hfit N hN => ?_⟩
  have := hM.probP
  set G : ℝ → Set (Config m) := fun S => GoodEvent M.μ.1 A a (2 * N ^ 2) (max S 1) with hG
  have hGS : ∀ S : ℝ, Real.log N ≤ S → G S = GoodEvent M.μ.1 A a (2 * N ^ 2) S := by
    intro S hS
    have := (hsmall N hN S hS).1
    simp only [hG, max_eq_left this]
  refine ⟨G, fun S S' hSS' => goodEvent_mono hA.le (le_max_of_le_right zero_le_one)
    (max_le_max_right 1 hSS'), fun S hS => ?_, fun S hS ω hω => ?_⟩
  · -- the indicator bound
    obtain ⟨hS1, hlog, hK2⟩ := hsmall N hN S hS
    rw [hGS S hS]
    have hS0 : 0 < S := by linarith only [hS1]
    refine isOs_two_indicator_compl (measurableSet_goodEvent _ _ _ _ _) ?_
    refine (hbound M hM hfit _ S hS1 hlog).trans (ENNReal.ofReal_le_ofReal (hK2.trans ?_))
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    -- `S²/C² ≤ cS²/2` since `C² ≥ 2/c`
    have hCsq : 2 / c ≤ C ^ 2 := by
      have h1 : Real.sqrt (2 / c) ≤ C := by linarith only [hC3]
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rwa [Real.sq_sqrt (by positivity)] at h2
    rw [div_pow, one_div_div]
    rw [div_le_iff₀ (by positivity)]
    have : 2 ≤ c * C ^ 2 := by
      rw [div_le_iff₀ hc] at hCsq
      linarith only [hCsq]
    nlinarith only [this, sq_nonneg S, hc]
  · -- the properties (1)–(3)
    rw [hGS S hS] at hω
    exact isGood_of_mem_goodEvent hA.le hC1 (by linarith only [(hsmall N hN S hS).1]) hω

end CurvatureVariance.Paper.Proofs.Geometry
