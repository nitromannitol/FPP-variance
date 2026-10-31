/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
import CurvatureVariance.Infra.FPP.Walks
import CurvatureVariance.Paper.Closing.Induction
import CurvatureVariance.Paper.Proofs.Reduction.FinalTarget
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds

/-!
# The closing: Theorem `thm:main`

The last sentences of the proof of Theorem `thm:main`, given equation `eq:premise` at every
length. Let `ε = 2δ/K`, so that `Q_s = A s^{(1−ε)/2}`.

* `exists_nat_of_near_ray`: the geometry. If `x = (s, y)` lies within `|x|^{3/4}` of `βa (1, t)` and
  `|x|` is large, then `s ≥ a|x|/2`, `|y − st| ≤ (1 + |t|)|x|^{3/4}`, and so `y ∈ 𝒟(s)`. The
  thresholds are `|x| ≥ 16(1 + √d)⁴` and `|x| ≥ 2√d · B^{100/δ}`, with `B = (1 + T) 2√d`. They
  depend on `ξ` only through `a ≥ d^{−1/2}` and `|t₀| ≤ T`. For these `x`, the coordinate `s` is
  positive.
* `lintegral_exp_le_of_map_eq`: the passage from a model to the original coordinates. An
  exponential bound depends only on the law of `T(0, x)`, and the time constant agrees at `x` and
  `Φ x`.
* `mainExpStatement`: the contract `Contracts.MainExpStatement`. There is one `K` for the
  finitely many laws of the choice of coordinates, the maximum of the `K₀` of the laws. The other
  `x` lie in a box of vertices, and for them the base case gives the bound. `C` is a sum over the
  finitely many laws and the points of the box, so it does not depend on `ξ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Closing

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

variable {m : ℕ}

/-! ## Vertices -/

/-- The first coordinate of a vertex is at most its norm. -/
theorem abs_fst_le_norm_point (x : Vertex m) : |(x.1 : ℝ)| ≤ ‖point x‖ := by
  have h := Proofs.Reduction.abs_fst_sub_le_of_norm_le (z := x) (b := 0) (C := ‖point x‖)
    (t := 0) (by simp)
  simpa using h

/-- The transverse part of a vertex is at most its norm. -/
theorem norm_transversePoint_le_norm_point (x : Vertex m) :
    ‖transversePoint x.2‖ ≤ ‖point x‖ := by
  have h := Proofs.Reduction.norm_snd_sub_le_of_norm_le (z := x) (b := 0) (C := ‖point x‖)
    (t := 0) (by simp)
  simpa using h

/-- A nonzero vertex has norm at least `1`. -/
theorem one_le_norm_point {x : Vertex m} (hx : x ≠ 0) : 1 ≤ ‖point x‖ := by
  by_cases h1 : x.1 = 0
  · have h2 : x.2 ≠ 0 := fun h2 => hx (Prod.ext h1 h2)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h2
    have h : (1 : ℝ) ≤ |(x.2 j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
    exact h.trans ((Responses.abs_coord_le_norm_transversePoint x.2 j).trans
      (norm_transversePoint_le_norm_point x))
  · have h : (1 : ℝ) ≤ |(x.1 : ℝ)| := by exact_mod_cast Int.one_le_abs h1
    exact h.trans (abs_fst_le_norm_point x)

/-- The box `[−R, R]^d` of vertices. -/
def vertexBox (m : ℕ) (R : ℤ) : Finset (Vertex m) :=
  Finset.Icc (-R) R ×ˢ Fintype.piFinset fun _ => Finset.Icc (-R) R

/-- A vertex of norm at most `R` lies in the box of side `⌈R⌉`. -/
theorem mem_vertexBox_of_norm_le {x : Vertex m} {R : ℝ} (hx : ‖point x‖ ≤ R) :
    x ∈ vertexBox m ⌈R⌉ := by
  have hc : ∀ {u : ℤ}, |(u : ℝ)| ≤ R → u ∈ Finset.Icc (-⌈R⌉) ⌈R⌉ := fun {u} hu => by
    have h := abs_le.1 hu
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩
    · have h' : ((-⌈R⌉ : ℤ) : ℝ) ≤ u := by
        push_cast
        linarith only [h.1, Int.le_ceil R]
      exact_mod_cast h'
    · have h' : (u : ℝ) ≤ (⌈R⌉ : ℤ) := h.2.trans (Int.le_ceil R)
      exact_mod_cast h'
  refine Finset.mem_product.2 ⟨hc ((abs_fst_le_norm_point x).trans hx), ?_⟩
  exact Fintype.mem_piFinset.2 fun j =>
    hc ((Responses.abs_coord_le_norm_transversePoint x.2 j).trans
      ((norm_transversePoint_le_norm_point x).trans hx))

/-! ## The geometry -/

/-- `R ≥ 16 (1 + S)⁴` gives `2 (1 + S) R^{3/4} ≤ R`. -/
theorem two_mul_mul_rpow_le {S R : ℝ} (hS : 0 ≤ S) (hR : 16 * (1 + S) ^ 4 ≤ R) :
    2 * (1 + S) * R ^ ((3 : ℝ) / 4) ≤ R := by
  have hc : 0 ≤ 2 * (1 + S) := by positivity
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hq : 2 * (1 + S) ≤ R ^ ((1 : ℝ) / 4) := by
    have e : 16 * (1 + S) ^ 4 = (2 * (1 + S)) ^ 4 := by ring
    rw [e] at hR
    have h1 := Real.rpow_le_rpow (by positivity) hR (show (0 : ℝ) ≤ (1 : ℝ) / 4 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hc, show (((4 : ℕ) : ℝ) * (1 / 4)) = 1 by norm_num,
      Real.rpow_one] at h1
  have hsplit : R ^ ((1 : ℝ) / 4) * R ^ ((3 : ℝ) / 4) = R := by
    rw [← Real.rpow_add hR0, show (1 : ℝ) / 4 + 3 / 4 = 1 by norm_num, Real.rpow_one]
  calc 2 * (1 + S) * R ^ ((3 : ℝ) / 4)
      ≤ R ^ ((1 : ℝ) / 4) * R ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hR0.le _)
    _ = R := hsplit

/-- `R^{3/4} ≤ 2 S s^{3/4}` for `R ≤ 2 S s` and `2 S ≥ 1`. -/
theorem rpow_le_mul_rpow {S R s : ℝ} (hS : 1 ≤ 2 * S) (hR : 0 ≤ R) (hs : 0 ≤ s)
    (hRs : R ≤ 2 * S * s) : R ^ ((3 : ℝ) / 4) ≤ 2 * S * s ^ ((3 : ℝ) / 4) := by
  have hS0 : 0 ≤ 2 * S := by linarith only [hS]
  calc R ^ ((3 : ℝ) / 4) ≤ (2 * S * s) ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow hR hRs (by norm_num)
    _ = (2 * S) ^ ((3 : ℝ) / 4) * s ^ ((3 : ℝ) / 4) := Real.mul_rpow hS0 hs
    _ ≤ 2 * S * s ^ ((3 : ℝ) / 4) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs _)
        exact Real.rpow_le_self_of_one_le hS (by norm_num)

/-- `|y − st| ≤ (1 + T) D` if `y` is within `D` of `bt`, and `|b − s| ≤ D`, `|t| ≤ T`. -/
theorem norm_sub_smul_le {y t : EuclideanSpace ℝ (Fin m)} {b s D T : ℝ}
    (hy : ‖y - b • t‖ ≤ D) (hs : |b - s| ≤ D) (ht : ‖t‖ ≤ T) : ‖y - s • t‖ ≤ (1 + T) * D := by
  have e : y - s • t = (y - b • t) + (b - s) • t := by
    rw [sub_smul]; abel
  have hD : 0 ≤ D := (abs_nonneg _).trans hs
  have h1 : |b - s| * ‖t‖ ≤ T * D := by
    rw [mul_comm T]
    exact mul_le_mul hs ht (norm_nonneg _) hD
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]
  linarith only [hy, h1]

/-- **The geometry of the proof of Theorem `thm:main`**: if the vertex
`z = (s, y)` of norm `R` lies within `R^{3/4}` of `b (1, t)`, with `b ≥ a(R − R^{3/4})` and
`a ≥ 1/S`, and `R` is large, then `s ≥ aR/2 > 0`, `s ≤ R` and `y ∈ 𝒟(s)`. -/
theorem exists_nat_of_near_ray {z : Vertex m} {t : EuclideanSpace ℝ (Fin m)} {a b S T γ R : ℝ}
    (hS : 1 ≤ S) (hT : ‖t‖ ≤ T) (haS : 1 ≤ a * S) (hγ : 0 < γ)
    (hRz : ‖point z‖ = R) (hb : a * (R - R ^ ((3 : ℝ) / 4)) ≤ b)
    (hnear : ‖point z - b • slopeVec t‖ ≤ R ^ ((3 : ℝ) / 4))
    (hR₀ : 16 * (1 + S) ^ 4 ≤ R) (hR₁ : 2 * S * ((1 + T) * (2 * S)) ^ (1 / γ) ≤ R) :
    ∃ s : ℕ, 1 ≤ s ∧ (s : ℝ) ≤ R ∧ z.1 = s ∧
      ‖transversePoint z.2 - (s : ℝ) • t‖ ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + γ) := by
  have hT0 : 0 ≤ T := (norm_nonneg t).trans hT
  have hS0 : 0 < S := by linarith only [hS]
  have ha : 0 < a := by
    by_contra h
    have h' : a * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hS0.le
    linarith only [h', haS]
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR₀
  set D := R ^ ((3 : ℝ) / 4) with hD
  have hD0 : 0 ≤ D := Real.rpow_nonneg hR0.le _
  have h1 := Proofs.Reduction.abs_fst_sub_le_of_norm_le hnear
  have h2 := Proofs.Reduction.norm_snd_sub_le_of_norm_le hnear
  have h1' := abs_le.1 h1
  -- `s ≥ a R / 2`
  have hRD : 2 * (1 + S) * D ≤ R := two_mul_mul_rpow_le hS0.le hR₀
  have hs : a * R / 2 ≤ z.1 := by
    have h3 : D ≤ a * S * D := le_mul_of_one_le_left hD0 haS
    have h4 := mul_le_mul_of_nonneg_left hRD (show 0 ≤ a / 2 by positivity)
    linarith only [h1'.1, hb, h3, h4]
  -- `R ≤ 2 S s`
  have hRs : R ≤ 2 * S * z.1 := by
    have h3 : R ≤ a * S * R := le_mul_of_one_le_left hR0.le haS
    have h4 := mul_le_mul_of_nonneg_left hs hS0.le
    linarith only [h3, h4]
  -- `s ≥ B^{1/γ} ≥ 1`
  set B := (1 + T) * (2 * S) with hBdef
  have hB1 : 1 ≤ B := by
    have h3 : (1 : ℝ) ≤ 2 * S := by linarith only [hS]
    have h4 : (1 : ℝ) ≤ 1 + T := by linarith only [hT0]
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (1 + T) * (2 * S) := mul_le_mul h4 h3 zero_le_one (by linarith only [hT0])
  have hB0 : 0 < B := by linarith only [hB1]
  have hsB : B ^ (1 / γ) ≤ z.1 :=
    le_of_mul_le_mul_left (hR₁.trans hRs) (by positivity)
  have hz1 : (1 : ℝ) ≤ z.1 := (Real.one_le_rpow hB1 (by positivity)).trans hsB
  have hz0 : 0 ≤ z.1 := by exact_mod_cast zero_le_one.trans hz1
  set s := z.1.toNat with hsdef
  have hsz : (s : ℤ) = z.1 := Int.toNat_of_nonneg hz0
  have hsR : (s : ℝ) = (z.1 : ℝ) := by rw [← hsz, Int.cast_natCast]
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  refine ⟨s, ?_, ?_, hsz.symm, ?_⟩
  · have h : (1 : ℝ) ≤ s := hsR ▸ hz1
    exact_mod_cast h
  · rw [hsR, ← hRz]
    exact (le_abs_self _).trans (abs_fst_le_norm_point z)
  -- `|y − s t| ≤ (1 + T) R^{3/4} ≤ B s^{3/4} ≤ s^{3/4 + γ}`
  have hsb : |b - (s : ℝ)| ≤ D := by rw [hsR, abs_sub_comm]; exact h1
  have hdist := norm_sub_smul_le h2 hsb hT
  have hDs : D ≤ 2 * S * (s : ℝ) ^ ((3 : ℝ) / 4) :=
    rpow_le_mul_rpow (by linarith only [hS]) hR0.le hs0 (by rw [hsR]; exact hRs)
  have hBs : B ≤ (s : ℝ) ^ γ := by
    have h3 : (B ^ (1 / γ)) ^ γ = B := by
      rw [← Real.rpow_mul hB0.le, show 1 / γ * γ = 1 by field_simp, Real.rpow_one]
    calc B = (B ^ (1 / γ)) ^ γ := h3.symm
      _ ≤ (s : ℝ) ^ γ := Real.rpow_le_rpow (Real.rpow_nonneg hB0.le _) (hsR ▸ hsB) hγ.le
  have hp : 0 ≤ (s : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hs0 _
  have hs1 : (0 : ℝ) < s := by rw [hsR]; linarith only [hz1]
  calc ‖transversePoint z.2 - (s : ℝ) • t‖ ≤ (1 + T) * D := hdist
    _ ≤ (1 + T) * (2 * S * (s : ℝ) ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hDs (by linarith only [hT0])
    _ = B * (s : ℝ) ^ ((3 : ℝ) / 4) := by rw [hBdef]; ring
    _ ≤ (s : ℝ) ^ γ * (s : ℝ) ^ ((3 : ℝ) / 4) := mul_le_mul_of_nonneg_right hBs hp
    _ = (s : ℝ) ^ ((3 : ℝ) / 4 + γ) := by rw [← Real.rpow_add hs1, add_comm]

/-! ## The passage to the original coordinates -/

/-- `|X| ≤ O₁(θ)` is the exponential bound of Theorem `thm:main` on any larger scale. -/
theorem lintegral_exp_le_of_isAbsOs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ S : ℝ} (hθ : 0 < θ) (hθS : θ ≤ S) (h : IsAbsOs P 1 θ X) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / S)) ∂P ≤ 2 := by
  have h' := (IsAbsOs.mono_scale h zero_le_one hθ hθS).2.2
  refine le_of_eq_of_le (lintegral_congr fun ω => ?_) h'
  rw [max_eq_left (abs_nonneg _), Real.rpow_one]

/-- The exponential bound depends only on the law: if `X` under `P` has the law of `Y` under `Q`
and `|Y − c| ≤ O₁(θ)`, then `E[exp(|X − c| / S)] ≤ 2` for `S ≥ θ`. -/
theorem lintegral_exp_le_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : AEMeasurable X P)
    (hY : AEMeasurable Y Q) (hmap : Measure.map X P = Measure.map Y Q) {c θ S : ℝ}
    (hθ : 0 < θ) (hθS : θ ≤ S) (h : IsAbsOs Q 1 θ (fun ω => Y ω - c)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - c| / S)) ∂P ≤ 2 := by
  have hg : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (|t - c| / S)) := by fun_prop
  have e : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω - c| / S)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (|Y ω - c| / S)) ∂Q := by
    rw [← lintegral_map' hg.aemeasurable hX, hmap, lintegral_map' hg.aemeasurable hY]
  rw [e]
  exact lintegral_exp_le_of_isAbsOs hθ hθS h

/-! ## Theorem `thm:main` -/

/-- The bound in a model, at a large vertex: in the bounds of the chosen coordinates, equation
`eq:premise` at every length gives `|T(0, z) − μ(z)| ≤ O₁(Q_s)`, with `Q_s ≤ A R^{(1−ε)/2}`. -/
theorem exists_isAbsOs_of_near_ray {Md : Model m} {K : ℕ} {A a b S T R ε : ℝ} {z : Vertex m}
    (hprem : ∀ N, Premise Md K A N) (hA : 1 ≤ A) (hexp : (1 / 2 - Md.δ / K : ℝ) = (1 - ε) / 2)
    (hexp0 : 0 < (1 - ε) / 2) (hδ : 0 < Md.δ)
    (hS : 1 ≤ S) (hT : ‖Md.t₀‖ ≤ T) (haS : 1 ≤ a * S)
    (hRz : ‖point z‖ = R) (hb : a * (R - R ^ ((3 : ℝ) / 4)) ≤ b)
    (hnear : ‖point z - b • slopeVec Md.t₀‖ ≤ R ^ ((3 : ℝ) / 4))
    (hR₀ : 16 * (1 + S) ^ 4 ≤ R)
    (hR₁ : 2 * S * ((1 + T) * (2 * S)) ^ (1 / (Md.δ / 100)) ≤ R) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ A * R ^ ((1 - ε) / 2) ∧
      IsAbsOs Md.P 1 θ (fun ω => passageTimeReal ω 0 z - Md.μ.1 (point z)) := by
  obtain ⟨s, hs1, hsR, hz1, hz2⟩ :=
    exists_nat_of_near_ray hS hT haS (by positivity) hRz hb hnear hR₀ hR₁
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hz : z = ((s : ℤ), z.2) := Prod.ext hz1 rfl
  have hle : (s : ℝ) ≤ 2 * ((2 * s : ℕ) : ℝ) / 3 := by
    push_cast
    linarith only [hs0]
  refine ⟨Q Md K A s, Q_pos Md K hA hs0, ?_, ?_⟩
  · refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hA])
    rw [hexp]
    exact Real.rpow_le_rpow hs0.le hsR hexp0.le
  · have h := hprem (2 * s) s hs1 hle z.2 hz2
    rw [← hz] at h
    exact h

/-- **Theorem `thm:main`, given equation `eq:premise` at every length** (the proof of Theorem
`thm:main`): one `K` for the laws of the coordinates, `ε = 2δ/K`, the bound at `x`
near the ray, and the base case for the other `x`. -/
theorem mainExpStatement {m : ℕ} (hD : DomainExpStatement m)
    (hR : ReductionUniformStatement m) (hB : BaseCaseStatement m) : MainExpStatement m := by
  intro hm F _ hW P _ hP μ hμ δ r M c hδ hδ₁ hr hM hc
  obtain ⟨hi, hhi, -, hred⟩ := hR hm F hW P hP μ hμ
  obtain ⟨law, hlaw, hred⟩ := hred δ r M c hδ hδ₁ hr hM hc
  set bd : Option (Fin m) × Bool → Bounds m := fun j => chartBounds (law j) hi r M c with hbddef
  have hbd : ∀ j, (bd j).Valid := fun j => chartBounds_valid (hlaw j).1 hhi hr hM hc
  -- one `K` for the laws of the coordinates
  choose K₀ hK₀ using fun j => hD (bd j) (hbd j)
  set K : ℕ := max (Finset.univ.sup K₀) (10 ^ 4) with hKdef
  have hKj : ∀ j, K₀ j ≤ K := fun j =>
    (Finset.le_sup (f := K₀) (Finset.mem_univ j)).trans (le_max_left _ _)
  have hK : 10 ^ 4 ≤ K := le_max_right _ _
  choose A hA hprem using fun j => hK₀ j K (hKj j) hK
  -- `ε = 2δ/K`
  have hK4 : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hK4
  set ε : ℝ := 2 * δ / K with hεdef
  have hε : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    rw [hεdef, div_lt_one hK0]
    linarith only [hδ₁, hK4]
  have hexp0 : 0 < (1 - ε) / 2 := by linarith only [hε1]
  -- the thresholds, and the box of the other points
  set S := Real.sqrt ((m : ℝ) + 1) with hSdef
  have hS : 1 ≤ S := by
    rw [hSdef, Real.one_le_sqrt]
    linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set T := Real.sqrt m with hTdef
  set R₀ : ℝ := max (16 * (1 + S) ^ 4) (2 * S * ((1 + T) * (2 * S)) ^ (1 / (δ / 100))) with hR₀def
  choose θ hθ0 hθ using fun j x => hB (bd j) (hbd j) x
  set box := vertexBox m ⌈R₀⌉ with hboxdef
  -- `C` is a sum, over the laws and the box
  set C : ℝ := ∑ j, (A j + ∑ x ∈ box, θ j x) with hCdef
  have hsum0 : ∀ j, 0 ≤ ∑ x ∈ box, θ j x := fun j =>
    Finset.sum_nonneg fun x _ => (hθ0 j x).le
  have hterm0 : ∀ j ∈ (Finset.univ : Finset (Option (Fin m) × Bool)),
      0 ≤ A j + ∑ x ∈ box, θ j x := fun j _ =>
    add_nonneg (zero_le_one.trans (hA j)) (hsum0 j)
  have hjC : ∀ j, A j + ∑ x ∈ box, θ j x ≤ C := fun j =>
    Finset.single_le_sum hterm0 (Finset.mem_univ j)
  have hAC : ∀ j, A j ≤ C := fun j => by linarith only [hjC j, hsum0 j]
  have hθC : ∀ j, ∀ x ∈ box, θ j x ≤ C := fun j x hx => by
    have h1 : θ j x ≤ ∑ x ∈ box, θ j x :=
      Finset.single_le_sum (f := θ j) (fun x _ => (hθ0 j x).le) hx
    linarith only [hjC j, hA j, h1]
  have hC : 0 < C := by linarith only [hAC (none, true), hA (none, true)]
  refine ⟨ε, hε, C, hC, fun ξ hξ hCξ x hx hnear => ?_⟩
  obtain ⟨β, hβ0, hβ⟩ := hnear
  obtain ⟨j, Md, Φ, a, hMs, hfit, ha0, -, hlawx, hμx, hdist⟩ := hred ξ hξ hCξ
  have hnorm : ‖point (Φ x)‖ = ‖point x‖ := by simpa using hdist x 0
  set R := ‖point x‖ with hRdef
  have hR1 : 1 ≤ R := one_le_norm_point hx
  have hpow1 : 1 ≤ R ^ ((1 - ε) / 2) := Real.one_le_rpow hR1 hexp0.le
  have hMδ : Md.δ = δ := hfit.δ_eq.trans (hlaw j).2
  have hCR : C ≤ C * R ^ ((1 - ε) / 2) := le_mul_of_one_le_right hC.le hpow1
  -- the bound in the model, at the transported vertex
  have key : ∃ θ' : ℝ, 0 < θ' ∧ θ' ≤ C * R ^ ((1 - ε) / 2) ∧
      IsAbsOs Md.P 1 θ' (fun ω => passageTimeReal ω 0 (Φ x) - Md.μ.1 (point (Φ x))) := by
    by_cases hlarge : R₀ ≤ R
    · have hS0 : 0 < S := by linarith only [hS]
      have haS : 1 ≤ a * S := by
        have h := mul_le_mul_of_nonneg_right ha0 hS0.le
        rwa [div_mul_cancel₀ _ hS0.ne'] at h
      have hexp : (1 / 2 - Md.δ / K : ℝ) = (1 - ε) / 2 := by
        rw [hMδ, hεdef]
        ring
      have hRβ : R - R ^ ((3 : ℝ) / 4) ≤ β := by
        have h1 : R ≤ ‖point x - β • ξ‖ + ‖β • ξ‖ := norm_le_norm_sub_add _ _
        rw [norm_smul, hξ, mul_one, Real.norm_of_nonneg hβ0] at h1
        linarith only [h1, hβ]
      have hb : a * (R - R ^ ((3 : ℝ) / 4)) ≤ β * a := by
        have ha : 0 ≤ a := (by positivity : (0 : ℝ) ≤ 1 / S).trans ha0
        rw [mul_comm β]
        exact mul_le_mul_of_nonneg_left hRβ ha
      obtain ⟨θ', h0, hle, hos⟩ := exists_isAbsOs_of_near_ray (hprem j Md hMs hfit) (hA j) hexp
        hexp0 (hMδ ▸ hδ) hS hfit.t₀_le haS hnorm hb ((hdist x β).trans_le hβ)
        ((le_max_left _ _).trans hlarge)
        (by rw [hMδ]; exact (le_max_right _ _).trans hlarge)
      exact ⟨θ', h0, hle.trans (mul_le_mul_of_nonneg_right (hAC j) (by positivity)), hos⟩
    · have hmem : Φ x ∈ box :=
        mem_vertexBox_of_norm_le (by rw [hnorm]; exact (not_le.1 hlarge).le)
      exact ⟨θ j (Φ x), hθ0 j _, (hθC j _ hmem).trans hCR, hθ j (Φ x) Md hMs hfit⟩
  obtain ⟨θ', hθ'0, hθ'le, hos⟩ := key
  rw [hμx x] at hos
  exact ⟨(Infra.FPP.measurable_passageTime_real 0 x).aemeasurable,
    lintegral_exp_le_of_map_eq (X := fun ω => passageTimeReal ω 0 x)
      (Y := fun ω => passageTimeReal ω 0 (Φ x))
      (Infra.FPP.measurable_passageTime_real 0 x).aemeasurable
      (Infra.FPP.measurable_passageTime_real 0 (Φ x)).aemeasurable (hlawx x) hθ'0 hθ'le hos⟩

end CurvatureVariance.Paper.Closing
