/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.KestenVar
public import CurvatureVariance.Paper.Proofs.Geometry.SlabPaths
public import CurvatureVariance.Paper.Proofs.Geometry.Basic

/-!
# The events `𝒢_N(S)` of Lemma `lem:good`

The proof of Lemma `lem:good`: the Gaussian bounds of [ADH, Theorem 3.13],
the Chernoff bound for coordinate paths and Kesten's estimate, with union bounds over a box, give
events on which

* (H1) `|T(x,y) − μ(y − x)| ≤ A(S|y − x|^{1/2} + S²)` for `x, y` in the box;
* (H2) the coordinate paths within slabs from `x` to `y` (`slabPath`) cost at most
  `A(|y − x|₁ + S²)`;
* (H3) simple paths from the box with at least `AS²` edges cost more than `a` per edge.

`GoodEvent μ A a R S` is the event of (H1)–(H3) on the box `[−R, R]^d`; it is measurable and
increasing in `S ≥ 0`. `isOs_two_indicator_compl` turns `P(𝒢ᶜ) ≤ e^{-1/θ²}` into
`1_{𝒢ᶜ} ≤ O₂(θ)`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP CurvatureVariance.Infra.Os

variable {m : ℕ}

/-! ### Boxes -/

/-- The vertices of the box `[−R, R]^d`. -/
def boxFinset (R : ℕ) : Finset (Vertex m) :=
  Finset.Icc (-(R : ℤ)) R ×ˢ Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

theorem mem_boxFinset_iff {R : ℕ} {x : Vertex m} : x ∈ boxFinset R ↔ InBox (R : ℝ) x := by
  simp only [boxFinset, Finset.mem_product, Finset.mem_Icc, Fintype.mem_piFinset, InBox, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, fun j => ?_⟩
    exact ⟨by exact_mod_cast (h3 j).1, by exact_mod_cast (h3 j).2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, fun j => ?_⟩
    exact ⟨by exact_mod_cast (h3 j).1, by exact_mod_cast (h3 j).2⟩

theorem card_boxFinset (R : ℕ) :
    (boxFinset R : Finset (Vertex m)).card = (2 * R + 1) ^ (m + 1) := by
  simp only [boxFinset, Finset.card_product, Fintype.card_piFinset, Int.card_Icc,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : (R : ℤ) + 1 - -(R : ℤ) = ((2 * R + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast, pow_succ']

/-! ### The events -/

/-- The event of (H1)–(H3) at scale `S` on the box `[−R, R]^d`, with constant `A` and cheap rate
`a`. -/
def GoodEvent (μ : Seminorm ℝ (Pt m)) (A a : ℝ) (R : ℕ) (S : ℝ) : Set (Config m) :=
  {ω | (∀ x ∈ boxFinset R, ∀ y ∈ boxFinset R,
      |passageTimeReal ω x y - μ (point y - point x)| ≤
        A * (S * Real.sqrt ‖point y - point x‖ + S ^ 2)) ∧
    (∀ x ∈ boxFinset R, ∀ y ∈ boxFinset R, ∀ i : Fin 3,
      (walkCost ω (slabPath x y (x.1 + (i : ℕ) - 1)) : ℝ) ≤ A * (oneNorm (y - x) + S ^ 2)) ∧
    (∀ x ∈ boxFinset R, ∀ k : ℕ, A * S ^ 2 ≤ k → ω ∉ cheapEvent a x k)}

theorem measurableSet_goodEvent (μ : Seminorm ℝ (Pt m)) (A a : ℝ) (R : ℕ) (S : ℝ) :
    MeasurableSet (GoodEvent μ A a R S) := by
  have h1 : MeasurableSet {ω : Config m | ∀ x ∈ boxFinset R, ∀ y ∈ boxFinset R,
      |passageTimeReal ω x y - μ (point y - point x)| ≤
        A * (S * Real.sqrt ‖point y - point x‖ + S ^ 2)} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le
      (continuous_abs.measurable.comp ((measurable_passageTime_real x y).sub measurable_const))
      measurable_const
  have h2 : MeasurableSet {ω : Config m | ∀ x ∈ boxFinset R, ∀ y ∈ boxFinset R, ∀ i : Fin 3,
      (walkCost ω (slabPath x y (x.1 + (i : ℕ) - 1)) : ℝ) ≤ A * (oneNorm (y - x) + S ^ 2)} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun i => ?_
    exact measurableSet_le (measurable_walkCost_real _) measurable_const
  have h3 : MeasurableSet {ω : Config m | ∀ x ∈ boxFinset R, ∀ k : ℕ, A * S ^ 2 ≤ k →
      ω ∉ cheapEvent a x k} := by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_
    exact (measurableSet_cheapEvent a x k).compl
  exact (h1.inter (h2.inter h3))

/-- The events increase with the scale. -/
theorem goodEvent_mono {μ : Seminorm ℝ (Pt m)} {A a : ℝ} (hA : 0 ≤ A) {R : ℕ} {S S' : ℝ}
    (hS : 0 ≤ S) (hSS' : S ≤ S') : GoodEvent μ A a R S ⊆ GoodEvent μ A a R S' := by
  have hsq : S ^ 2 ≤ S' ^ 2 := pow_le_pow_left₀ hS hSS' 2
  rintro ω ⟨h1, h2, h3⟩
  refine ⟨fun x hx y hy => (h1 x hx y hy).trans ?_, fun x hx y hy i => (h2 x hx y hy i).trans ?_,
    fun x hx k hk => h3 x hx k ((mul_le_mul_of_nonneg_left hsq hA).trans hk)⟩
  · have := Real.sqrt_nonneg ‖point y - point x‖
    have := mul_le_mul_of_nonneg_right hSS' this
    exact mul_le_mul_of_nonneg_left (by linarith) hA
  · exact mul_le_mul_of_nonneg_left (by linarith) hA

/-! ### `O₂` bounds for indicators -/

/-- **An indicator with a Gaussian-small complement is `O₂`**: if `P(Gᶜ) ≤ e^{-1/θ²}`, then
`1_{Gᶜ} ≤ O₂(θ)`. -/
theorem isOs_two_indicator_compl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G : Set Ω} (hG : MeasurableSet G) {θ : ℝ}
    (h : P Gᶜ ≤ ENNReal.ofReal (Real.exp (-(1 / θ ^ 2)))) :
    IsOs P 2 θ (Gᶜ.indicator fun _ => (1 : ℝ)) := by
  refine ⟨(measurable_const.indicator hG.compl).aemeasurable, ?_⟩
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp ((max (Gᶜ.indicator (fun _ => (1 : ℝ)) ω) 0 / θ) ^
      (2 : ℝ))) = Gᶜ.indicator (fun _ => ENNReal.ofReal (Real.exp (1 / θ ^ 2))) ω +
        G.indicator (fun _ => 1) ω := by
    intro ω
    by_cases hω : ω ∈ G
    · have : ω ∉ Gᶜ := fun h => h hω
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem this, Set.indicator_of_mem hω]
      simp [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
    · have : ω ∈ Gᶜ := hω
      rw [Set.indicator_of_mem this, Set.indicator_of_mem this, Set.indicator_of_notMem hω,
        add_zero, max_eq_left zero_le_one, Real.rpow_two, div_pow, one_pow]
  simp_rw [hpt]
  rw [lintegral_add_left ((measurable_const.indicator hG.compl)), lintegral_indicator hG.compl,
    lintegral_indicator hG, setLIntegral_const, setLIntegral_const, one_mul]
  calc ENNReal.ofReal (Real.exp (1 / θ ^ 2)) * P Gᶜ + P G
      ≤ ENNReal.ofReal (Real.exp (1 / θ ^ 2)) * ENNReal.ofReal (Real.exp (-(1 / θ ^ 2))) + 1 :=
        add_le_add (mul_le_mul_right h _) prob_le_one
    _ = 2 := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one, one_add_one_eq_two]

end CurvatureVariance.Paper.Proofs.Geometry
