/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.WhiteNoise.Coordinates
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# A smooth partition of squares

`sqBump` is a smooth function on `ℝ`, supported in `[-1/4, 5/4]`, whose integer translates have
squares summing to one. The cube bumps `cubeBump z x = ∏ᵢ sqBump (2 coord x i - zᵢ)` on a
finite-dimensional inner product space then satisfy `∑_z (cubeBump z x)² = 1`, are smooth and
compactly supported, and only finitely many meet a bounded set.
-/

@[expose] public section

open scoped ContDiff

namespace IsotropicVariance.Infra.WhiteNoise

/-- The smooth step `0` on `(-∞, -1/4]` and `1` on `[1/4, ∞)`. -/
noncomputable def sqStep (t : ℝ) : ℝ := Real.smoothTransition (2 * t + 1 / 2)

theorem sqStep_eq_zero {t : ℝ} (ht : t ≤ -1 / 4) : sqStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem sqStep_eq_one {t : ℝ} (ht : 1 / 4 ≤ t) : sqStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem contDiff_sqStep : ContDiff ℝ ∞ sqStep :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- A smooth bump on `ℝ`, supported in `[-1/4, 5/4]`, whose integer translates have squares summing
to one. -/
noncomputable def sqBump (s : ℝ) : ℝ :=
  if s ≤ 1 / 2 then Real.sin (Real.pi / 2 * sqStep s) else Real.cos (Real.pi / 2 * sqStep (s - 1))

theorem sqBump_of_le {s : ℝ} (hs : s ≤ 1 / 2) : sqBump s = Real.sin (Real.pi / 2 * sqStep s) :=
  by simp only [sqBump, hs, ↓reduceIte]

theorem sqBump_of_gt {s : ℝ} (hs : 1 / 2 < s) :
    sqBump s = Real.cos (Real.pi / 2 * sqStep (s - 1)) :=
  by simp only [sqBump, not_le.2 hs, ↓reduceIte]

theorem sqBump_eq_sin {s : ℝ} (hs : s < 3 / 4) : sqBump s = Real.sin (Real.pi / 2 * sqStep s) := by
  by_cases h : s ≤ 1 / 2
  · exact sqBump_of_le h
  · rw [sqBump_of_gt (not_le.1 h), sqStep_eq_zero (t := s - 1) (by linarith),
      sqStep_eq_one (t := s) (by linarith)]
    simp

theorem sqBump_eq_cos {s : ℝ} (hs : 1 / 4 < s) :
    sqBump s = Real.cos (Real.pi / 2 * sqStep (s - 1)) := by
  by_cases h : s ≤ 1 / 2
  · rw [sqBump_of_le h, sqStep_eq_one (t := s) (by linarith),
      sqStep_eq_zero (t := s - 1) (by linarith)]
    simp
  · exact sqBump_of_gt (not_le.1 h)

theorem sqBump_eq_one {s : ℝ} (h1 : 1 / 4 ≤ s) (h2 : s ≤ 3 / 4) : sqBump s = 1 := by
  rcases lt_or_ge s (3 / 4) with h | h
  · rw [sqBump_eq_sin h, sqStep_eq_one h1]; simp
  · rw [sqBump_eq_cos (by linarith), sqStep_eq_zero (by linarith)]; simp

theorem contDiff_sqBump : ContDiff ℝ ∞ sqBump := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s < 3 / 4
  · have h : ContDiffAt ℝ ∞ (fun v : ℝ => Real.sin (Real.pi / 2 * sqStep v)) s :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_sqStep)).contDiffAt
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hs] with v hv using sqBump_eq_sin hv
  · have h : ContDiffAt ℝ ∞ (fun v : ℝ => Real.cos (Real.pi / 2 * sqStep (v - 1))) s :=
      (Real.contDiff_cos.comp
        (contDiff_const.mul (contDiff_sqStep.comp (contDiff_id.sub contDiff_const)))).contDiffAt
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (1 / 4 : ℝ) < s by linarith)] with v hv
    using sqBump_eq_cos hv

theorem sqBump_eq_zero_of_le {s : ℝ} (hs : s ≤ -1 / 4) : sqBump s = 0 := by
  rw [sqBump_of_le (by linarith), sqStep_eq_zero hs]; simp

theorem sqBump_eq_zero_of_ge {s : ℝ} (hs : 5 / 4 ≤ s) : sqBump s = 0 := by
  rw [sqBump_of_gt (by linarith), sqStep_eq_one (by linarith)]; simp

theorem abs_sqBump_le_one (s : ℝ) : |sqBump s| ≤ 1 := by
  unfold sqBump
  split_ifs
  · exact Real.abs_sin_le_one _
  · exact Real.abs_cos_le_one _

/-- A finite set of translates carrying all of the mass. -/
theorem exists_finset_sqBump_sq (s : ℝ) :
    ∃ F : Finset ℤ, (∀ j ∉ F, sqBump (s - j) = 0) ∧ ∑ j ∈ F, sqBump (s - j) ^ 2 = 1 := by
  set n : ℤ := ⌊s⌋ with hn
  set u : ℝ := s - n with hu
  have hu0 : 0 ≤ u := by rw [hu]; exact sub_nonneg.2 (Int.floor_le s)
  have hu1 : u < 1 := by rw [hu]; linarith [Int.lt_floor_add_one s]
  refine ⟨{n - 1, n, n + 1}, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨h1, h2, h3⟩ := hj
    rcases lt_or_gt_of_ne h2 with h | h
    · have : j ≤ n - 2 := by omega
      have : (j : ℝ) ≤ n - 2 := by exact_mod_cast this
      exact sqBump_eq_zero_of_ge (by linarith)
    · have : n + 2 ≤ j := by omega
      have : (n : ℝ) + 2 ≤ j := by exact_mod_cast this
      exact sqBump_eq_zero_of_le (by linarith)
  · rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
    have e0 : s - ((n - 1 : ℤ) : ℝ) = u + 1 := by push_cast; rw [hu]; ring
    have e1 : s - (n : ℝ) = u := hu.symm
    have e2 : s - ((n + 1 : ℤ) : ℝ) = u - 1 := by push_cast; rw [hu]; ring
    rw [e0, e1, e2]
    rcases lt_or_ge u (1 / 4) with h | h
    · rw [sqBump_eq_zero_of_le (show u - 1 ≤ -1 / 4 by linarith),
        sqBump_of_gt (show 1 / 2 < u + 1 by linarith), sqBump_of_le (by linarith),
        show u + 1 - 1 = u by ring]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 2 * sqStep u)]
    rcases le_or_gt u (3 / 4) with h' | h'
    · rw [sqBump_eq_zero_of_le (show u - 1 ≤ -1 / 4 by linarith),
        sqBump_eq_zero_of_ge (show 5 / 4 ≤ u + 1 by linarith), sqBump_eq_one h h']
      norm_num
    · rw [sqBump_eq_zero_of_ge (show 5 / 4 ≤ u + 1 by linarith),
        sqBump_of_gt (show 1 / 2 < u by linarith), sqBump_of_le (by linarith)]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 2 * sqStep (u - 1))]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The bump of index `z ∈ ℤ^n`: `χ_z(x) = ∏ᵢ θ(2 coord x i − zᵢ)`. -/
noncomputable def cubeBump (z : Coord E → ℤ) (x : E) : ℝ :=
  ∏ i, sqBump (2 * coord x i - z i)

theorem contDiff_cubeBump (z : Coord E → ℤ) : ContDiff ℝ ∞ (cubeBump (E := E) z) := by
  unfold cubeBump
  exact contDiff_prod fun i _ =>
    contDiff_sqBump.comp (((contDiff_const.mul (contDiff_coord i))).sub contDiff_const)

theorem abs_cubeBump_le_one (z : Coord E → ℤ) (x : E) : |cubeBump z x| ≤ 1 := by
  unfold cubeBump
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => abs_sqBump_le_one _

theorem cubeBump_eq_zero {z : Coord E → ℤ} {x : E}
    (h : ∃ i, coord x i ∉ Set.Icc ((z i : ℝ) / 2 - 1 / 8) ((z i : ℝ) / 2 + 5 / 8)) :
    cubeBump z x = 0 := by
  obtain ⟨i, hi⟩ := h
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
  rcases hi with h | h
  · exact sqBump_eq_zero_of_le (by linarith)
  · exact sqBump_eq_zero_of_ge (by linarith)

theorem cubeBump_ne_zero_bounds {z : Coord E → ℤ} {x : E} (h : cubeBump z x ≠ 0) (i : Coord E) :
    (z i : ℝ) / 2 - 1 / 8 ≤ coord x i ∧ coord x i ≤ (z i : ℝ) / 2 + 5 / 8 := by
  by_contra hc
  exact h (cubeBump_eq_zero ⟨i, hc⟩)

theorem norm_le_sum_abs_coord (x : E) : ‖x‖ ≤ ∑ i, |coord x i| := by
  conv_lhs => rw [← (coordBasis E).sum_repr' x]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_smul, (coordBasis E).orthonormal.1 i, mul_one, Real.norm_eq_abs, coord_apply]

theorem hasCompactSupport_cubeBump (z : Coord E → ℤ) : HasCompactSupport (cubeBump (E := E) z) := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E)
    (∑ i : Coord E, (|(z i : ℝ)| / 2 + 1)) ) fun x hx => ?_
  by_contra hne
  apply hx
  rw [mem_closedBall_zero_iff]
  refine (norm_le_sum_abs_coord x).trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨h1, h2⟩ := cubeBump_ne_zero_bounds hne i
  rw [abs_le]
  have := le_abs_self (z i : ℝ)
  have := neg_abs_le (z i : ℝ)
  constructor <;> linarith

/-- **The squares of the cube bumps sum to one.** -/
theorem hasSum_cubeBump_sq (x : E) : HasSum (fun z : Coord E → ℤ => cubeBump z x ^ 2) 1 := by
  choose t ht hsum using fun i : Coord E => exists_finset_sqBump_sq (2 * coord x i)
  have key : ∀ z : Coord E → ℤ, cubeBump z x ^ 2 =
      ∏ i, sqBump (2 * coord x i - z i) ^ 2 := fun z => by
    unfold cubeBump; rw [Finset.prod_pow]
  have h1 : ∀ z ∉ Fintype.piFinset t, cubeBump z x ^ 2 = 0 := by
    intro z hz
    rw [Fintype.mem_piFinset, not_forall] at hz
    obtain ⟨i, hi⟩ := hz
    rw [key]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [ht i _ hi]; simp)
  have h2 : HasSum (fun z : Coord E → ℤ => cubeBump z x ^ 2)
      (∑ z ∈ Fintype.piFinset t, cubeBump z x ^ 2) := hasSum_sum_of_ne_finset_zero h1
  convert h2 using 1
  simp_rw [key]
  rw [← Finset.prod_univ_sum (fun i => t i) (fun i j => sqBump (2 * coord x i - j) ^ 2)]
  simp [hsum]

/-- Only finitely many cube bumps meet a bounded set. -/
theorem finite_setOf_cubeBump_ne_zero {K : Set E} (hK : Bornology.IsBounded K) :
    {z : Coord E → ℤ | ∃ x ∈ K, cubeBump z x ≠ 0}.Finite := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hK
  refine (Set.Finite.pi (t := fun _ : Coord E => Set.Icc (-⌈2 * R + 2⌉) ⌈2 * R + 2⌉)
    fun _ => Set.finite_Icc _ _).subset ?_
  rintro z ⟨x, hxK, hx⟩ i -
  obtain ⟨h1, h2⟩ := cubeBump_ne_zero_bounds hx i
  have hc := (abs_le.1 ((abs_coord_le x i).trans (hR x hxK)))
  have hceil := Int.le_ceil (2 * R + 2)
  have hR0 : 0 ≤ R := (norm_nonneg x).trans (hR x hxK)
  constructor
  · have : (-(⌈2 * R + 2⌉ : ℤ) : ℝ) ≤ z i := by linarith [hc.1]
    exact_mod_cast this
  · have : (z i : ℝ) ≤ (⌈2 * R + 2⌉ : ℤ) := by linarith [hc.2]
    exact_mod_cast this

end IsotropicVariance.Infra.WhiteNoise
