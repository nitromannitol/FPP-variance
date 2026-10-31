/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Infra.Os.Power
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import IsotropicVariance.Paper.Proofs.SmallMean.MeanTools

/-!
# Tools for the fluctuation bound in the proof of Lemma `lem:smallmean`

* **Dense sequences.** A nonempty set of a separable metric space has a sequence in it whose
  closure contains it (`exists_dense_seq_in`). A continuous function, bounded on the set, is
  bounded there by its supremum along the sequence (`le_iSup_of_denseSeq`).
* **Moments of arbitrary functions.**
  - Jensen's inequality `∫⁻ f ≤ (∫⁻ f^q)^{1/q}` holds for every function on a probability space
    (`lintegral_le_lintegral_rpow`), through a measurable minorant with the same integral.
  - `∫(Y + Mo + c)^p ≤ 3^{p−1}(∫Y^p + ∫Mo^p + c^p)` needs only `Y` measurable
    (`lintegral_pow_le_of_le_add`).
  The modulus quantity of equation `eq:modulus` and the supremum in equation `eq:profiles` are
  suprema over uncountable families, whose measurability is not needed.
* **Nets of the unit cube** (`exists_unitCube_net`): finite, with a cardinality that depends only
  on the radius and the dimension.
* **Suprema.** The suprema in equations `eq:modulus` and `eq:profiles` dominate each of their
  terms (`le_modulusSup`, `le_iSup_pair`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace IsotropicVariance.Paper.Proofs.SmallMean

/-! ### Dense sequences -/

/-- A nonempty subset of a separable metric space contains a sequence whose closure contains
it. -/
theorem exists_dense_seq_in {α : Type*} [PseudoMetricSpace α] [SeparableSpace α] {S : Set α}
    (hS : S.Nonempty) : ∃ q : ℕ → α, (∀ n, q n ∈ S) ∧ S ⊆ closure (range q) := by
  have : Nonempty S := hS.to_subtype
  have : SeparableSpace S := inferInstance
  obtain ⟨q, hq⟩ := exists_dense_seq S
  refine ⟨fun n => q n, fun n => (q n).2, fun x hx => ?_⟩
  have hx' : (⟨x, hx⟩ : S) ∈ closure (range q) := hq ⟨x, hx⟩
  have hcont : Continuous (Subtype.val : S → α) := continuous_subtype_val
  exact map_mem_closure hcont hx' (t := range fun n => (q n : α)) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩)

/-- A continuous function bounded above along a sequence is bounded by its supremum along the
sequence at every point of the closure of the sequence. -/
theorem le_iSup_of_denseSeq {α : Type*} [TopologicalSpace α] {q : ℕ → α} {f : α → ℝ}
    (hf : Continuous f) (hb : BddAbove (range fun n => f (q n))) {x : α}
    (hx : x ∈ closure (range q)) : f x ≤ ⨆ n, f (q n) := by
  have hcl : IsClosed {y | f y ≤ ⨆ n, f (q n)} := isClosed_le hf continuous_const
  have hsub : range q ⊆ {y | f y ≤ ⨆ n, f (q n)} := by
    rintro _ ⟨n, rfl⟩
    exact le_ciSup hb n
  exact hcl.closure_subset_iff.mpr hsub hx

/-! ### Moments of arbitrary functions -/

/-- **Jensen's inequality for an arbitrary function**: `∫⁻ f ≤ (∫⁻ f^q)^{1/q}` for `q ≥ 1` on a
probability space, with no measurability. -/
theorem lintegral_le_lintegral_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (f : Ω → ℝ≥0∞) {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ ω, f ω ∂P ≤ (∫⁻ ω, f ω ^ q ∂P) ^ (1 / q) := by
  obtain ⟨g, hgm, hgf, hg⟩ := exists_measurable_le_lintegral_eq P f
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have h1 : ∫⁻ ω, g ω ∂P ≤ (∫⁻ ω, g ω ^ q ∂P) ^ (1 / q) := by
    have := Infra.Os.lintegral_rpow_le (P := P) (f := fun ω => g ω ^ q)
      (hgm.pow_const q).aemeasurable (a := 1 / q) (by positivity)
      ((div_le_one hq0).2 hq)
    simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] using this
  rw [hg]
  refine h1.trans (ENNReal.rpow_le_rpow (lintegral_mono fun ω => ?_) (by positivity))
  exact ENNReal.rpow_le_rpow (hgf ω) hq0.le

/-- **The power of a sum of three terms**, only the first measurable:
`∫(F)^p ≤ 3^{p−1}(∫Y^p + ∫Mo^p + c^p)` when `0 ≤ F ≤ Y + Mo + c` almost everywhere. -/
theorem lintegral_pow_le_of_le_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F Y Mo : Ω → ℝ} {c : ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hMo0 : ∀ ω, 0 ≤ Mo ω) (hc0 : 0 ≤ c) (hF0 : ∀ ω, 0 ≤ F ω)
    (hF : ∀ᵐ ω ∂P, F ω ≤ Y ω + Mo ω + c) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (F ω ^ p) ∂P ≤ ENNReal.ofReal (3 ^ (p - 1)) *
      (∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂P + ∫⁻ ω, ENNReal.ofReal (Mo ω ^ p) ∂P +
        ENNReal.ofReal (c ^ p)) := by
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (F ω ^ p) ≤ ENNReal.ofReal (3 ^ (p - 1)) *
      (ENNReal.ofReal (Y ω ^ p) + (ENNReal.ofReal (Mo ω ^ p) + ENNReal.ofReal (c ^ p))) := by
    filter_upwards [hF] with ω hω
    rw [← ENNReal.ofReal_add (pow_nonneg (hMo0 ω) p) (pow_nonneg hc0 p),
      ← ENNReal.ofReal_add (pow_nonneg (hY0 ω) p)
        (add_nonneg (pow_nonneg (hMo0 ω) p) (pow_nonneg hc0 p)),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hconv : (Y ω + Mo ω + c) ^ p ≤ 3 ^ (p - 1) * (Y ω ^ p + Mo ω ^ p + c ^ p) :=
      add_three_pow_le (hY0 ω) (hMo0 ω) hc0 hp
    calc F ω ^ p ≤ (Y ω + Mo ω + c) ^ p := pow_le_pow_left₀ (hF0 ω) hω p
      _ ≤ 3 ^ (p - 1) * (Y ω ^ p + Mo ω ^ p + c ^ p) := hconv
      _ = 3 ^ (p - 1) * (Y ω ^ p + (Mo ω ^ p + c ^ p)) := by ring
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left ((hY.pow_const p).ennreal_ofReal),
    lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, add_assoc]

/-! ### Nets of the unit cube -/

/-- The unit cube `[0, 1]^m` of `EuclideanSpace ℝ (Fin m)`. -/
def unitCube (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) := {y | ∀ l, 0 ≤ y l ∧ y l ≤ 1}

theorem isCompact_unitCube (m : ℕ) : IsCompact (unitCube m) := by
  have hb : Bornology.IsBounded (unitCube m) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨Real.sqrt m, fun y hy => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ l, ‖y l‖ ^ 2 ≤ ∑ _l : Fin m, (1 : ℝ) := Finset.sum_le_sum fun l _ => by
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith [(hy l).1, (hy l).2]
      _ = m := by simp
  have hc : IsClosed (unitCube m) := by
    simp only [unitCube, Set.ofPred_forall]
    exact isClosed_iInter fun l => (isClosed_le continuous_const
      ((EuclideanSpace.proj l).continuous)).inter
      (isClosed_le ((EuclideanSpace.proj l).continuous) continuous_const)
  exact Metric.isCompact_of_isClosed_isBounded hc hb

/-- **A finite net of the unit cube**: for every radius there are finitely many points of the
cube within that radius of every point of the cube. -/
theorem exists_unitCube_net (m : ℕ) {h : ℝ} (hh : 0 < h) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin m)), (∀ t ∈ T, t ∈ unitCube m) ∧
      ∀ y ∈ unitCube m, ∃ t ∈ T, dist y t ≤ h := by
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_unitCube m) hh
  refine ⟨htf.toFinset, fun x hx => hts (htf.mem_toFinset.1 hx), fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcov hy)
  exact ⟨x, htf.mem_toFinset.2 hx, (mem_ball.1 hyx).le⟩

/-! ### The suprema of equations `eq:modulus` and `eq:profiles` dominate their terms -/

/-- A term of the modulus quantity of equation `eq:modulus` is at most the quantity, when the
family is bounded. -/
theorem le_modulusSup {m : ℕ} {D : Pt m → Pt m → ℝ} {I I' : Set (Pt m)} {r B : ℝ}
    (hB : ∀ u ∈ I, ∀ u₁ ∈ I, ∀ v ∈ I', ∀ v₁ ∈ I',
      |D u v - D u₁ v₁ - dist u v + dist u₁ v₁| ≤ B)
    {u u₁ v v₁ : Pt m} (hu : u ∈ I) (hu₁ : u₁ ∈ I) (hv : v ∈ I') (hv₁ : v₁ ∈ I')
    (hr : dist u u₁ ≤ r ∧ dist v v₁ ≤ r) :
    |D u v - D u₁ v₁ - dist u v + dist u₁ v₁| ≤ Contracts.modulusSup D I I' r := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB u hu u₁ hu₁ v hv v₁ hv₁)
  -- the innermost supremum over the condition
  have h4 : ∀ (a : I) (a₁ : I) (c : I') (c₁ : I'),
      (⨆ (_ : dist (a : Pt m) a₁ ≤ r ∧ dist (c : Pt m) c₁ ≤ r),
        |D a c - D a₁ c₁ - dist (a : Pt m) c + dist (a₁ : Pt m) c₁|) ≤ B := by
    intro a a₁ c c₁
    by_cases hcond : dist (a : Pt m) a₁ ≤ r ∧ dist (c : Pt m) c₁ ≤ r
    · rw [ciSup_pos hcond]
      exact hB a a.2 a₁ a₁.2 c c.2 c₁ c₁.2
    · simp [hcond, hB0]
  have h3 : ∀ (a : I) (a₁ : I) (c : I'), (⨆ (c₁ : I') (_ : dist (a : Pt m) a₁ ≤ r ∧
      dist (c : Pt m) c₁ ≤ r), |D a c - D a₁ c₁ - dist (a : Pt m) c + dist (a₁ : Pt m) c₁|) ≤
      B := fun a a₁ c => by
    rcases isEmpty_or_nonempty I' with h | h
    · simp [hB0]
    · exact ciSup_le fun c₁ => h4 a a₁ c c₁
  have h2 : ∀ (a : I) (a₁ : I), (⨆ (c : I') (c₁ : I') (_ : dist (a : Pt m) a₁ ≤ r ∧
      dist (c : Pt m) c₁ ≤ r), |D a c - D a₁ c₁ - dist (a : Pt m) c + dist (a₁ : Pt m) c₁|) ≤
      B := fun a a₁ => by
    rcases isEmpty_or_nonempty I' with h | h
    · simp [hB0]
    · exact ciSup_le fun c => h3 a a₁ c
  have h1 : ∀ (a : I), (⨆ (a₁ : I) (c : I') (c₁ : I') (_ : dist (a : Pt m) a₁ ≤ r ∧
      dist (c : Pt m) c₁ ≤ r), |D a c - D a₁ c₁ - dist (a : Pt m) c + dist (a₁ : Pt m) c₁|) ≤
      B := fun a => by
    have : Nonempty I := ⟨a⟩
    exact ciSup_le fun a₁ => h2 a a₁
  unfold Contracts.modulusSup
  refine le_trans ?_ (le_ciSup ⟨B, ?_⟩ (⟨u, hu⟩ : I))
  · refine le_trans ?_ (le_ciSup ⟨B, ?_⟩ (⟨u₁, hu₁⟩ : I))
    · refine le_trans ?_ (le_ciSup ⟨B, ?_⟩ (⟨v, hv⟩ : I'))
      · refine le_trans ?_ (le_ciSup ⟨B, ?_⟩ (⟨v₁, hv₁⟩ : I'))
        · rw [ciSup_pos hr]
        · rintro _ ⟨c₁, rfl⟩
          exact h4 _ _ _ c₁
      · rintro _ ⟨c, rfl⟩
        exact h3 _ _ c
    · rintro _ ⟨a₁, rfl⟩
      exact h2 _ a₁
  · rintro _ ⟨a, rfl⟩
    exact h1 a

/-- The modulus quantity of equation `eq:modulus` is at most a bound of its terms. -/
theorem modulusSup_le {m : ℕ} {D : Pt m → Pt m → ℝ} {I I' : Set (Pt m)} {r B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ u ∈ I, ∀ u₁ ∈ I, ∀ v ∈ I', ∀ v₁ ∈ I',
      |D u v - D u₁ v₁ - dist u v + dist u₁ v₁| ≤ B) :
    Contracts.modulusSup D I I' r ≤ B := by
  unfold Contracts.modulusSup
  rcases isEmpty_or_nonempty I with hI | hI
  · simp [hB0]
  refine ciSup_le fun a => ?_
  refine ciSup_le fun a₁ => ?_
  rcases isEmpty_or_nonempty I' with hI' | hI'
  · simp [hB0]
  refine ciSup_le fun c => ciSup_le fun c₁ => ?_
  by_cases hcond : dist (a : Pt m) a₁ ≤ r ∧ dist (c : Pt m) c₁ ≤ r
  · rw [ciSup_pos hcond]
    exact hB a a.2 a₁ a₁.2 c c.2 c₁ c₁.2
  · simp [hcond, hB0]

/-- A term of the supremum in equation `eq:profiles` is at most the supremum, when the family is
bounded. -/
theorem le_iSup_pair {m : ℕ} {f : Pt m → Pt m → ℝ} {I I' : Set (Pt m)} {B : ℝ}
    (hB : ∀ u ∈ I, ∀ v ∈ I', f u v ≤ B) {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I') :
    f u v ≤ ⨆ (a : I) (c : I'), f a c := by
  have hne : Nonempty I' := ⟨⟨v, hv⟩⟩
  have h1 : ∀ a : I, (⨆ c : I', f a c) ≤ B := fun a => ciSup_le fun c => hB a a.2 c c.2
  refine le_trans ?_ (le_ciSup ⟨B, ?_⟩ (⟨u, hu⟩ : I))
  · exact le_ciSup ⟨B, by rintro _ ⟨c, rfl⟩; exact hB u hu c c.2⟩ (⟨v, hv⟩ : I')
  · rintro _ ⟨a, rfl⟩
    exact h1 a

end IsotropicVariance.Paper.Proofs.SmallMean
