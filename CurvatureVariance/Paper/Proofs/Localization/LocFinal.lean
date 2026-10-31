/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocGood
public import CurvatureVariance.Paper.Proofs.Localization.LocMoments
public import CurvatureVariance.Paper.Proofs.Localization.LocTranslate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Basic

/-!
# Lemma `lem:localization`: the last step

* `isOs_two_const`, `isOs_radiusGood`: `R 1_𝒢 ≤ O₂(C(b))`, from `Ψ ≤ O₁(C(b))`.
* `exists_length_sup`: off the good event, the bound on the number of edges of geodesics in
  Section `sec:prelim`, and the union bound, equation `eq:union`, over the pairs `u ∈ I`, `v ∈ I'`
  (the proof of Lemma `lem:localization`).
* `deviation_le_of_length`: a vertex of a path is within its length of `[u, v]`.
* `moment_of_bounds`: the moment bound for one family of paths.
* `Loc.cubeFinset`: the lattice points of a transverse cube.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.Os Radius

variable {m : ℕ}

/-! ## The lattice points of a transverse cube -/

/-- The lattice points of a transverse cube, as a finset. -/
noncomputable def cubeFinset (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) (a : ℝ) : Finset (Vertex m) :=
  {p} ×ˢ Fintype.piFinset fun i => Finset.Icc ⌈c i - a / 2⌉ ⌊c i + a / 2⌋

theorem mem_cubeFinset {p : ℤ} {c : EuclideanSpace ℝ (Fin m)} {a : ℝ} {x : Vertex m} :
    x ∈ cubeFinset p c a ↔ x ∈ transverseCube p c a := by
  simp only [cubeFinset, Finset.mem_product, Finset.mem_singleton, Fintype.mem_piFinset,
    Finset.mem_Icc, transverseCube, Set.mem_ofPred_eq, abs_le, Int.ceil_le, Int.le_floor]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩

theorem card_cubeFinset_le {p : ℤ} {c : EuclideanSpace ℝ (Fin m)} {a : ℝ} (ha : 0 ≤ a) :
    ((cubeFinset p c a).card : ℝ) ≤ (a + 1) ^ m := by
  simp only [cubeFinset, Finset.card_product, Finset.card_singleton, one_mul,
    Fintype.card_piFinset, Nat.cast_prod]
  calc ∏ i, ((Finset.Icc ⌈c i - a / 2⌉ ⌊c i + a / 2⌋).card : ℝ) ≤ ∏ _i : Fin m, (a + 1) := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro i _
        rw [Int.card_Icc]
        have h1 := Int.le_ceil (c i - a / 2)
        have h2 := Int.floor_le (c i + a / 2)
        by_cases hle : ⌈c i - a / 2⌉ ≤ ⌊c i + a / 2⌋ + 1
        · have h0 : 0 ≤ ⌊c i + a / 2⌋ + 1 - ⌈c i - a / 2⌉ := by omega
          have h5 := Int.toNat_of_nonneg h0
          have : (((⌊c i + a / 2⌋ + 1 - ⌈c i - a / 2⌉).toNat : ℕ) : ℝ) =
              ((⌊c i + a / 2⌋ + 1 - ⌈c i - a / 2⌉ : ℤ) : ℝ) := by exact_mod_cast h5
          rw [this]; push_cast; linarith
        · push Not at hle
          rw [Int.toNat_of_nonpos (by omega)]; simp only [Nat.cast_zero]; linarith
    _ = (a + 1) ^ m := by simp

/-- A positive constant is `O₂(2c)`. -/
theorem isOs_two_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {c : ℝ} (hc : 0 < c) : CurvatureVariance.IsOs P 2 (2 * c) (fun _ => c) := by
  refine ⟨aemeasurable_const, ?_⟩
  rw [lintegral_const, measure_univ, mul_one]
  have h : max c 0 / (2 * c) = 1 / 2 := by
    rw [max_eq_left hc.le]; field_simp
  rw [h, Real.rpow_two]
  have h1 : Real.exp ((1 / 2 : ℝ) ^ 2) ≤ 2 :=
    (Real.exp_le_exp.2 (by norm_num)).trans Moments.exp_half_le_two
  calc ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) ^ 2)) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal h1
    _ = 2 := ENNReal.ofReal_ofNat 2

/-- **`R 1_𝒢 ≤ O₂(C(b))`**: the bound on the good event is `O₂`, for `Ψ ≤ O₁(τ)`. -/
theorem isOs_radiusGood (hSum : SignedOsSumStatement.{0, 0}) {P : Measure (Config m)}
    [IsProbabilityMeasure P] {Ψ : Config m → ℝ} {τ A₀ A₁ : ℝ} (hτ : 0 < τ) (hA₀ : 0 < A₀)
    (hA₁ : 0 < A₁) (hΨ : CurvatureVariance.IsOs P 1 τ Ψ) :
    CurvatureVariance.IsOs P 2 (2 * A₀ + A₁ * Real.sqrt τ) (fun ω => A₀ + A₁ * Real.sqrt (max (Ψ ω) 0)) := by
  have h1 := isOs_sqrt hτ hΨ
  have h2 := (isOs_mul_iff (P := P) (s := 2) (θ := Real.sqrt τ) hA₁).2 h1
  have h3 := isOs_two_const (P := P) hA₀
  have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have h4 := isOs_add_of hSum (s := 2) one_le_two h3 h2 (by positivity) (by positivity)
  exact h4

/-- A vertex of a path from `u` is within the length of the path of `[u, v]`. -/
theorem deviation_le_of_length {geo : ∀ {u v : Vertex m}, (latticeGraph m).Walk u v → Prop}
    {I I' : Set (Vertex m)} {B : ℝ}
    (hlen : ∀ u ∈ I, ∀ v ∈ I', ∀ γ : (latticeGraph m).Walk u v, geo γ → (γ.length : ℝ) ≤ B) :
    deviation geo I I' ≤ ENNReal.ofReal B := by
  simp only [deviation]
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv =>
    iSup_le fun γ => iSup_le fun hγ => iSup_le fun x => iSup_le fun hx => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : Metric.infDist (point x) (segment ℝ (point u) (point v)) ≤ ‖point x - point u‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (left_mem_segment ℝ _ _)
  have h2 := Infra.FPP.norm_point_sub_le_length_of_mem γ hx
  linarith only [h1, h2, hlen u hu v hv γ hγ]

/-- The constant of the union bound, equation `eq:union`, at `s = 1`. -/
noncomputable def unionConst (hUnion : OsUnionStatement.{0, 0}) : ℝ :=
  Classical.choose (hUnion 1 one_pos)

theorem unionConst_pos (hUnion : OsUnionStatement.{0, 0}) : 0 < unionConst hUnion :=
  (Classical.choose_spec (hUnion 1 one_pos)).1

/-- **The length off the good event**: one `O₁(C log(2 + J))` variable, by the union bound,
equation `eq:union`, dominates the variables of the edge count over `J` pairs. -/
theorem exists_length_sup (hUnion : OsUnionStatement.{0, 0}) {P : Measure (Config m)}
    [IsProbabilityMeasure P] {C : ℝ} (hC : 0 < C) (T₀ : Finset (Vertex m × Vertex m))
    (hT : T₀.Nonempty) {Q : Vertex m × Vertex m → Config m → ℝ → Prop}
    (hlen : ∀ uv : Vertex m × Vertex m, ∃ X : Config m → ℝ, CurvatureVariance.IsOs P 1 C X ∧
      ∀ᵐ ω ∂P, Q uv ω (X ω))
    (hmono : ∀ uv ω x y, x ≤ y → Q uv ω x → Q uv ω y) :
    ∃ Λ : Config m → ℝ, CurvatureVariance.IsOs P 1 (unionConst hUnion * C * Real.log (2 + T₀.card)) Λ ∧
      ∀ᵐ ω ∂P, ∀ uv ∈ T₀, Q uv ω (Λ ω) := by
  obtain ⟨-, hU⟩ := Classical.choose_spec (hUnion 1 one_pos)
  choose X hX hXae using hlen
  have h := hU P T₀ hT C hC X (fun uv _ => hX uv)
  have e : Real.log (2 + T₀.card) ^ (1 / (1 : ℝ)) = Real.log (2 + T₀.card) := by
    rw [div_self one_ne_zero, Real.rpow_one]
  rw [e] at h
  refine ⟨T₀.sup' hT X, h, ?_⟩
  have hae : ∀ᵐ ω ∂P, ∀ uv ∈ T₀, Q uv ω (X uv ω) :=
    (Filter.eventually_all_finset T₀).mpr fun uv _ => hXae uv
  filter_upwards [hae] with ω hω uv huv
  refine hmono uv ω _ _ ?_ (hω uv huv)
  rw [Finset.sup'_apply]
  exact Finset.le_sup' (fun uv => X uv ω) huv

/-- **The moment bound for one family of paths**: if the deviation is at most `W (A₀ + A₁ √Ψ₊)` on
`G`, and at most `W (L + Λ₊)` almost surely, then, by `lintegral_rpow_of_good_bad`,
`E[R^p] ≤ 2^p (2(1 + ⌈p/2⌉!) θ^p + 1)`, with `θ = 2(1 + A₀) + A₁√τ`. -/
theorem moment_of_bounds (hSum : SignedOsSumStatement.{0, 0}) {P : Measure (Config m)}
    [IsProbabilityMeasure P] {dev : Config m → ℝ≥0∞} {G : Set (Config m)}
    {Ψ Λ : Config m → ℝ} {W τ η τG A₀ A₁ L p : ℝ} (hW : 1 ≤ W) (hτ : 0 < τ) (hη : 0 < η)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 < A₁) (hL : 0 ≤ L) (hp : 1 ≤ p) (hΨ : CurvatureVariance.IsOs P 1 τ Ψ)
    (hΛ : CurvatureVariance.IsOs P 1 η Λ) (hG : CurvatureVariance.IsOs P 2 τG (Gᶜ.indicator fun _ => (1 : ℝ)))
    (hgood : ∀ᵐ ω ∂P, ω ∈ G → dev ω ≤ ENNReal.ofReal (W * (A₀ + A₁ * Real.sqrt (max (Ψ ω) 0))))
    (hall : ∀ᵐ ω ∂P, dev ω ≤ ENNReal.ofReal (W * (L + max (Λ ω) 0)))
    (hnum : 2 ^ (2 * p) * ((1 + L) ^ (2 * p) +
        2 * (1 + ((Nat.ceil (2 * p / 1)).factorial : ℝ)) * η ^ (2 * p)) *
        (2 * Real.exp (-(1 / τG) ^ 2)) ≤ 1) :
    ∫⁻ ω, (1 + dev ω / ENNReal.ofReal W) ^ p ∂P ≤
      ENNReal.ofReal (2 ^ p * (2 * (1 + ((Nat.ceil (p / 2)).factorial : ℝ)) *
        (2 * (1 + A₀) + A₁ * Real.sqrt τ) ^ p + 1)) := by
  have hW0 : 0 < W := by linarith only [hW]
  have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hΦ := isOs_radiusGood hSum (A₀ := 1 + A₀) hτ (by linarith only [hA₀]) hA₁ hΨ
  have hθ : 0 < 2 * (1 + A₀) + A₁ * Real.sqrt τ := by positivity
  refine lintegral_rpow_of_good_bad (Φ := fun ω => 1 + A₀ + A₁ * Real.sqrt (max (Ψ ω) 0))
    (Λ := Λ) (L := 1 + L) hθ hη (by linarith only [hL]) hp hΦ hΛ hG ?_ ?_ hnum
  · filter_upwards [hgood] with ω hω hmem
    have := radius_le_of_deviation_le (by positivity) (hω hmem)
    refine this.trans (le_of_eq ?_)
    congr 1
    ring
  · filter_upwards [hall] with ω hω
    have h1 : 0 ≤ L + max (Λ ω) 0 := by positivity
    have := radius_le_of_deviation_le h1 hω
    refine this.trans (le_of_eq ?_)
    congr 1
    ring

end CurvatureVariance.Paper.Localization.Loc
