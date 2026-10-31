/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.Basic
import Mathlib.Tactic.Linarith

/-!
# Chaining (the proof of Lemma `lem:tree`)

The abstract form of the dyadic chaining of equation `eq:tree`. A base point
`a` is joined to every point `u` of a finite set `U` through chain points
`φ 0 u = a, φ 1 u, …, φ J u`, then directly to `u`.
By the triangle inequality and telescoping of the linear terms,
`T(a, u) − P·(u − a) ≤ ∑ⱼ (linkError + linkCost) + (T(φ J u, u) − P·(u − φ J u))`
(`chain_le`). If the link errors of generation `j` are `O₁(θⱼ)` and take at most `Bⱼ` distinct
values, the deterministic costs sum to at most `D`, and the final steps are `O₁(θ_f)`, then one
variable `X ≤ O₁(∑ⱼ log₂(2Bⱼ) θⱼ + log₂(2|U|) θ_f + 2D)` bounds `T(a,u) − P·(u − a)` for all
`u ∈ U` at once ([AKM, Lemmas A.1 and A.4]; `exists_isOs_chain`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

/-- The link error `T(x, y) − μ(y − x)`. -/
noncomputable def linkError (M : Model m) (ω : Config m) (x y : Vertex m) : ℝ :=
  passageTimeReal ω x y - M.μ.1 (point y - point x)

/-- The deterministic link cost `μ(y − x) − P·(y − x)`, nonnegative when `P` is a subgradient. -/
noncomputable def linkCost (M : Model m) (P : Pt m) (x y : Vertex m) : ℝ :=
  M.μ.1 (point y - point x) - inner ℝ P (point y - point x)

/-- **The chain inequality**: the triangle inequality along `φ 0, …, φ J, u`, with the linear
terms telescoping. -/
theorem chain_le (M : Model m) (P : Pt m) (ω : Config m) (φ : ℕ → Vertex m) (u : Vertex m)
    (J : ℕ) :
    passageTimeReal ω (φ 0) u - inner ℝ P (point u - point (φ 0)) ≤
      ∑ j ∈ Finset.range J, (linkError M ω (φ j) (φ (j + 1)) + linkCost M P (φ j) (φ (j + 1))) +
        (passageTimeReal ω (φ J) u - inner ℝ P (point u - point (φ J))) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have htri := passageTimeReal_triangle ω (φ J) (φ (J + 1)) u
    have hlin : inner ℝ P (point u - point (φ J)) =
        inner ℝ P (point (φ (J + 1)) - point (φ J)) + inner ℝ P (point u - point (φ (J + 1))) := by
      rw [← inner_add_right]; congr 1; abel
    have hterm : linkError M ω (φ J) (φ (J + 1)) + linkCost M P (φ J) (φ (J + 1)) =
        passageTimeReal ω (φ J) (φ (J + 1)) - inner ℝ P (point (φ (J + 1)) - point (φ J)) := by
      unfold linkError linkCost; ring
    linarith only [ih, htri, hlin, hterm]

/-- An `O₁` bound for a finite sum plus one more term, allowing an empty sum. -/
theorem isOs_one_finset_sum_add {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (T : Finset ι) (θ : ι → ℝ) (hθ : ∀ i ∈ T, 0 < θ i)
    (X : ι → Ω → ℝ) (hX : ∀ i ∈ T, IsOs P 1 (θ i) (X i)) {θ' : ℝ} (hθ' : 0 < θ') {Y : Ω → ℝ}
    (hY : IsOs P 1 θ' Y) :
    IsOs P 1 (∑ i ∈ T, θ i + θ') (fun ω => ∑ i ∈ T, X i ω + Y ω) := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simpa using hY
  · exact isOs_add (isOs_one_finset_sum T hT θ hθ X hX) hY (Finset.sum_pos hθ hT) hθ'

/-- **Chaining** (the proof of Lemma `lem:tree`, [AKM, Lemmas A.1 and A.4]). -/
theorem exists_isOs_chain {M : Model m} (hM : M.Standing) (P : Pt m) (a : Vertex m)
    (U : Finset (Vertex m)) (hU : U.Nonempty) (J : ℕ) (φ : ℕ → Vertex m → Vertex m)
    (hφ0 : ∀ u ∈ U, φ 0 u = a) (θ : ℕ → ℝ) (hθ : ∀ j, 0 < θ j) (B : ℕ → ℝ)
    (hlink : ∀ j < J, ∀ u ∈ U, IsOs M.P 1 (θ j) (fun ω => linkError M ω (φ j u) (φ (j + 1) u)))
    (hcard : ∀ j < J, ((U.image fun u => (φ j u, φ (j + 1) u)).card : ℝ) ≤ B j)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ u ∈ U, ∑ j ∈ Finset.range J, linkCost M P (φ j u) (φ (j + 1) u) ≤ D)
    (θf : ℝ) (hθf : 0 < θf)
    (hfin : ∀ u ∈ U, IsOs M.P 1 θf
      (fun ω => passageTimeReal ω (φ J u) u - inner ℝ P (point u - point (φ J u)))) :
    ∃ X : Config m → ℝ, IsOs M.P 1
        (∑ j ∈ Finset.range J, Real.log (2 * B j) / Real.log 2 * θ j +
          Real.log (2 * U.card) / Real.log 2 * θf + 2 * D) X ∧
      ∀ ω, ∀ u ∈ U, passageTimeReal ω a u - inner ℝ P (point u - point a) ≤ X ω := by
  have := hM.probP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the links of generation `j` and their maximum
  let L : ℕ → Finset (Vertex m × Vertex m) := fun j => U.image fun u => (φ j u, φ (j + 1) u)
  have hL : ∀ j, (L j).Nonempty := fun j => hU.image _
  let E : Vertex m × Vertex m → Config m → ℝ := fun pr ω => linkError M ω pr.1 pr.2
  let Y : ℕ → Config m → ℝ := fun j => (L j).sup' (hL j) E
  have hcard1 : ∀ j, (1 : ℝ) ≤ (L j).card := fun j => by exact_mod_cast (hL j).card_pos
  have hscale : ∀ j, 0 < Real.log (2 * (L j).card) / Real.log 2 * θ j := fun j =>
    mul_pos (div_pos (Real.log_pos (by linarith only [hcard1 j])) hlog2) (hθ j)
  have hY : ∀ j ∈ Finset.range J, IsOs M.P 1 (Real.log (2 * B j) / Real.log 2 * θ j) (Y j) := by
    intro j hj
    have hjJ := Finset.mem_range.mp hj
    have h := isOs_finset_sup' (P := M.P) one_pos (hθ j) (L j) (hL j) E (by
      intro pr hpr
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hpr
      exact hlink j hjJ u hu)
    simp only [div_one] at h
    refine h.mono_scale zero_le_one (by simpa using hscale j) ?_
    rw [Real.rpow_one]
    apply mul_le_mul_of_nonneg_right _ (hθ j).le
    apply div_le_div_of_nonneg_right _ hlog2.le
    exact Real.log_le_log (by linarith only [hcard1 j]) (by linarith only [hcard j hjJ])
  -- the final steps and their maximum
  let Fv : Vertex m → Config m → ℝ :=
    fun u ω => passageTimeReal ω (φ J u) u - inner ℝ P (point u - point (φ J u))
  let Yf : Config m → ℝ := U.sup' hU Fv
  have hU1 : (1 : ℝ) ≤ U.card := by exact_mod_cast hU.card_pos
  have hYf : IsOs M.P 1 (Real.log (2 * U.card) / Real.log 2 * θf) Yf := by
    have h := isOs_finset_sup' (P := M.P) one_pos hθf U hU Fv hfin
    simpa only [div_one, Real.rpow_one] using h
  have hfpos : 0 < Real.log (2 * U.card) / Real.log 2 * θf :=
    mul_pos (div_pos (Real.log_pos (by linarith only [hU1])) hlog2) hθf
  have hsum := isOs_one_finset_sum_add (P := M.P) (Finset.range J) _ (fun j hj => by
      have hjJ := Finset.mem_range.mp hj
      refine mul_pos (div_pos (Real.log_pos ?_) hlog2) (hθ j)
      linarith only [hcard1 j, hcard j hjJ]) Y hY hfpos hYf
  have h0 : 0 ≤ ∑ j ∈ Finset.range J, Real.log (2 * B j) / Real.log 2 * θ j := by
    refine Finset.sum_nonneg fun j hj => ?_
    have hjJ := Finset.mem_range.mp hj
    have hB : (1 : ℝ) ≤ 2 * B j := by linarith only [hcard1 j, hcard j hjJ]
    exact mul_nonneg (div_nonneg (Real.log_nonneg hB) hlog2.le) (hθ j).le
  have hX := isOs_add_const hsum (by linarith only [h0, hfpos]) hD0
  refine ⟨fun ω => (∑ j ∈ Finset.range J, Y j ω + Yf ω) + D, hX, fun ω u hu => ?_⟩
  have hchain := chain_le M P ω (fun j => φ j u) u J
  simp only [hφ0 u hu] at hchain
  have hE : ∀ j ∈ Finset.range J, linkError M ω (φ j u) (φ (j + 1) u) ≤ Y j ω := by
    intro j _
    have hmem : (φ j u, φ (j + 1) u) ∈ L j := Finset.mem_image_of_mem _ hu
    change E (φ j u, φ (j + 1) u) ω ≤ (L j).sup' (hL j) E ω
    rw [Finset.sup'_apply]
    exact Finset.le_sup' (fun pr => E pr ω) hmem
  have hF : Fv u ω ≤ Yf ω := by
    change Fv u ω ≤ U.sup' hU Fv ω
    rw [Finset.sup'_apply]
    exact Finset.le_sup' (fun v => Fv v ω) hu
  rw [Finset.sum_add_distrib] at hchain
  have h1 := Finset.sum_le_sum hE
  have h2 := hD u hu
  have hF' : passageTimeReal ω (φ J u) u - inner ℝ P (point u - point (φ J u)) ≤ Yf ω := hF
  show _ ≤ (∑ j ∈ Finset.range J, Y j ω + Yf ω) + D
  linarith only [hchain, h1, h2, hF']

end CurvatureVariance.Paper.Moments
