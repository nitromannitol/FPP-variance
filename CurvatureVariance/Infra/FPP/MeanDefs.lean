/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.FPP.Hypotheses
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Shared definitions of the mean-rate chain

The objects shared by the files of the mean-rate chain (the mean rate `E T(0,x) ≤ μ(x) + C φ(|x|)`
of [ADH, Thm 3.33], by Alexander's convex-hull method):

* `meanTime P x = E T(0, x)` and the rate `meanRate r = (r log(2 + r))^{1/2}`;
* `liftedPoints` and the convex-hull approximation property `ConvexHullApprox` of Alexander;
* finite sets of lattice points and edges: `latticeBall`, `edgesNear`, `walkEdges`;
* skeletons of walks: `skelVert`, `skeletonFamily`, `skeletonBad`, `skeletonBadUnion`.

The two probabilistic inputs (the cheap-path estimate `CheapPaths` and the Gaussian lower tail of
least costs `MinCostLowerTail`) are those of `CurvatureVariance.Infra.FPP.CheapPaths` and
`CurvatureVariance.Infra.FPP.Hypotheses`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- The mean passage time `E T(0, x)`. -/
noncomputable def meanTime (P : Measure (Config m)) (x : Vertex m) : ℝ :=
  ∫ ω, (passageTime ω 0 x : ℝ) ∂P

/-- The fluctuation rate `φ(r) = (r log(2 + r))^{1/2}` of the mean bound. -/
noncomputable def meanRate (r : ℝ) : ℝ :=
  Real.sqrt (r * Real.log (2 + r))

/-- The lifted lattice points `(y, h(y)) ∈ ℝ^d × ℝ` with `|y| ≤ R`. -/
def liftedPoints (h : Vertex m → ℝ) (R : ℝ) : Set (Pt m × ℝ) :=
  (fun y : Vertex m => (point y, h y)) '' {y | ‖point y‖ ≤ R}

/-- **Alexander's convex-hull approximation property** (averaged form) of `h` relative to the
seminorm `μ`, with constants `M, C, r₀`: every rational point `x = z/k` with `|x| ≥ r₀` lies, at a
height at most `μ(x) + C φ(|x|)`, in the convex hull of the lifted lattice points `(y, h(y))` with
`|y| ≤ M|x|`. -/
def ConvexHullApprox (h : Vertex m → ℝ) (μ : Seminorm ℝ (Pt m)) (M C r₀ : ℝ) : Prop :=
  ∀ (z : Vertex m) (k : ℕ), 0 < k → r₀ ≤ ‖(k : ℝ)⁻¹ • point z‖ →
    ∃ v : ℝ, v ≤ μ ((k : ℝ)⁻¹ • point z) + C * meanRate ‖(k : ℝ)⁻¹ • point z‖ ∧
      ((k : ℝ)⁻¹ • point z, v) ∈
        convexHull ℝ (liftedPoints h (M * ‖(k : ℝ)⁻¹ • point z‖))

/-- The lattice points in the closed ball of radius `R` about the origin. -/
noncomputable def latticeBall (m : ℕ) (R : ℝ) : Finset (Vertex m) := by
  classical
  exact (Finset.Icc (-(⌊R⌋₊ : ℤ)) ⌊R⌋₊ ×ˢ
    Fintype.piFinset fun _ : Fin m => Finset.Icc (-(⌊R⌋₊ : ℤ)) ⌊R⌋₊).filter
      fun y => ‖point y‖ ≤ R

/-- The lattice edges both of whose endpoints lie in the closed ball of radius `R`. -/
noncomputable def edgesNear (m : ℕ) (R : ℝ) : Finset (Edge m) := by
  classical
  exact ((latticeBall m R ×ˢ latticeBall m R).image fun p => s(p.1, p.2)).subtype
    (· ∈ (latticeGraph m).edgeSet)

/-- The edges of a walk, as a finite set of lattice edges. -/
noncomputable def walkEdges {u v : Vertex m} (p : (latticeGraph m).Walk u v) :
    Finset (Edge m) := by
  classical
  exact p.edges.toFinset.subtype (· ∈ (latticeGraph m).edgeSet)

/-- The skeleton vertices `v_i = d_0 + ⋯ + d_{i-1}` of the increments `d` (`v_0 = 0`). -/
def skelVert {q : ℕ} (d : Fin q → Vertex m) (i : ℕ) : Vertex m :=
  ∑ j ∈ Finset.range i, if h : j < q then d ⟨j, h⟩ else 0

/-- The family of a skeleton `v_0, …, v_q`: the sets of at most `K` edges near the origin whose
total weight dominates `∑_{i<q} T(v_i, v_{i+1})` in every configuration. -/
noncomputable def skeletonFamily (v : ℕ → Vertex m) (q K : ℕ) : Finset (Finset (Edge m)) := by
  classical
  exact (edgesNear m K).powerset.filter fun F => F.card ≤ K ∧
    ∀ ω : Config m, ∑ i ∈ Finset.range q, (passageTime ω (v i) (v (i + 1)) : ℝ) ≤
      ∑ e ∈ F, (ω e : ℝ)

/-- The deficit event of a skeleton: some edge set of its family weighs less than
`∑_{i<q} E T(v_i, v_{i+1}) - Δ`. -/
def skeletonBad (P : Measure (Config m)) (v : ℕ → Vertex m) (q K : ℕ) (Δ : ℝ) :
    Set (Config m) :=
  {ω | ∃ F ∈ skeletonFamily v q K, ∑ e ∈ F, (ω e : ℝ) <
    ∑ i ∈ Finset.range q, meanTime P (v (i + 1) - v i) - Δ}

/-- The union of the deficit events, at deficit `q D`, of all skeletons from the origin to `X`
with `q ≤ K` steps in the ball of radius `R`. -/
noncomputable def skeletonBadUnion (P : Measure (Config m)) (X : Vertex m) (R : ℝ) (K : ℕ)
    (D : ℝ) : Set (Config m) := by
  classical
  exact ⋃ q ∈ Finset.range (K + 1),
    ⋃ d ∈ (Fintype.piFinset fun _ : Fin q => latticeBall m R).filter (fun d => ∑ j, d j = X),
      skeletonBad P (skelVert d) q K (q * D)

/-- The point of a natural multiple of a vertex. -/
theorem point_nsmul (n : ℕ) (z : Vertex m) : point (n • z) = (n : ℝ) • point z := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, point_add, ih]; push_cast; rw [add_smul, one_smul]

/-- The point of a finite sum of vertices. -/
theorem point_sum {ι : Type*} (s : Finset ι) (g : ι → Vertex m) :
    point (∑ i ∈ s, g i) = ∑ i ∈ s, point (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, point_add, ih]

theorem mem_latticeBall {R : ℝ} {y : Vertex m} : y ∈ latticeBall m R ↔ ‖point y‖ ≤ R := by
  classical
  unfold latticeBall
  simp only [Finset.mem_filter, and_iff_right_iff_imp]
  intro hy
  have hR : 0 ≤ R := (norm_nonneg _).trans hy
  have hc : ∀ t : ℤ, |(t : ℝ)| ≤ R → t ∈ Finset.Icc (-(⌊R⌋₊ : ℤ)) ⌊R⌋₊ := by
    intro t ht
    have h1 : |t| ≤ (⌊R⌋₊ : ℤ) := by
      have : (|t| : ℝ) ≤ R := by exact_mod_cast ht
      have h2 : (|t|).toNat ≤ ⌊R⌋₊ := Nat.le_floor (by
        rw [show (((|t|).toNat : ℕ) : ℝ) = ((|t| : ℤ) : ℝ) by
          exact_mod_cast Int.toNat_of_nonneg (abs_nonneg t)]
        exact_mod_cast this)
      omega
    rw [Finset.mem_Icc]
    exact ⟨by linarith [neg_abs_le t], le_trans (le_abs_self t) h1⟩
  have hfst : |(y.1 : ℝ)| ≤ R := by
    have := (WithLp.norm_fst_le ℝ (point y)).trans hy
    simpa [Real.norm_eq_abs] using this
  refine Finset.mem_product.2 ⟨hc _ hfst, Fintype.mem_piFinset.2 fun j => hc _ ?_⟩
  have h1 : ‖(point y).snd‖ ≤ ‖point y‖ := WithLp.norm_snd_le ℝ _
  have h2 : |((point y).snd j : ℝ)| ≤ ‖(point y).snd‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (point y).snd j
  simpa [point_snd, transversePoint] using h2.trans (h1.trans hy)

theorem mem_edgesNear {R : ℝ} {e : Edge m} :
    e ∈ edgesNear m R ↔ ∀ x ∈ (e : Sym2 (Vertex m)), ‖point x‖ ≤ R := by
  classical
  unfold edgesNear
  rw [Finset.mem_subtype, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩ x hx
    rw [← he, Sym2.mem_iff] at hx
    rw [Finset.mem_product] at hab
    rcases hx with rfl | rfl
    · exact mem_latticeBall.1 hab.1
    · exact mem_latticeBall.1 hab.2
  · intro h
    induction e using Subtype.rec with
    | _ e he' =>
    induction e using Sym2.ind with
    | _ a b =>
    exact ⟨(a, b), Finset.mem_product.2
      ⟨mem_latticeBall.2 (h a (Sym2.mem_mk_left a b)),
        mem_latticeBall.2 (h b (Sym2.mem_mk_right a b))⟩, rfl⟩

theorem mem_walkEdges {u v : Vertex m} {p : (latticeGraph m).Walk u v} {e : Edge m} :
    e ∈ walkEdges p ↔ (e : Sym2 (Vertex m)) ∈ p.edges := by
  classical
  unfold walkEdges
  rw [Finset.mem_subtype, List.mem_toFinset]

@[simp] theorem skelVert_zero {q : ℕ} (d : Fin q → Vertex m) : skelVert d 0 = 0 := by
  simp [skelVert]

theorem skelVert_succ_sub {q : ℕ} (d : Fin q → Vertex m) {i : ℕ} (hi : i < q) :
    skelVert d (i + 1) - skelVert d i = d ⟨i, hi⟩ := by
  simp [skelVert, Finset.sum_range_succ, hi]

theorem sum_range_skelVert_sub {β : Type*} [AddCommMonoid β] {q : ℕ} (d : Fin q → Vertex m)
    (f : Vertex m → β) :
    ∑ i ∈ Finset.range q, f (skelVert d (i + 1) - skelVert d i) = ∑ j, f (d j) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (skelVert d (i + 1) - skelVert d i))]
  exact Finset.sum_congr rfl fun j _ => by rw [skelVert_succ_sub d j.2]

theorem skelVert_self {q : ℕ} (d : Fin q → Vertex m) : skelVert d q = ∑ j, d j := by
  have h := Finset.sum_range_sub (skelVert d) q
  rw [skelVert_zero, sub_zero] at h
  exact h.symm.trans (sum_range_skelVert_sub d id)

end CurvatureVariance.Infra.FPP
