/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.SlabVersion
import IsotropicVariance.Infra.Selection.Subtype
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.Linarith

/-!
# The slab minimum `F` and the indices `J` are random variables

For the slab minimum `F` of equation `eq:F` and the lexicographically least minimizing points
(the proof of Lemma `lem:rowenergy`; `IsotropicVariance.Paper.Defs.Minimum`):

* the slabs of the chain have pairwise disjoint interiors
  (`pairwise_disjoint_interior_chainSlab`);
* `lexMinimizer` is the lexicographically least minimizer for the density of every outcome
  (`isLexLeastMinimizer_lexMinimizer`, a corollary of `Paper.isLexLeastMinimizer_lexMinimizer`);
* `F` and the indices `J_i` are almost everywhere measurable (`aemeasurable_F`,
  `aemeasurable_J`).

The existence and uniqueness of the minimizing points are in
`IsotropicVariance.Paper.Defs.Minimum`; the order of `lexKey` is the lexicographic order of the
flattened coordinates `flatCoords`. For measurability, the compact lexicographic selection of
`IsotropicVariance.Infra.Selection` is applied, on the flattened admissible set, to the slab sum
of jointly measurable, continuous versions of the slab passage times
(`Infra.Slab.exists_slabTime_version`). These agree with the slab passage times at all admissible
points on one full-measure event; there the selected points are the lexicographically least
minimizer (`isLexLeastMinimizer_of_select`), hence `lexMinimizer`, by
uniqueness (`Paper.lexMinimizer_eq_iff`).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace IsotropicVariance.Infra.Slab

open IsotropicVariance.Paper

variable {m : ℕ}

/-! ## Coordinates -/

/-- The point with given coordinates `(x · e₁, …, x · e_d)`. -/
noncomputable def ofCoords (c : Fin (m + 1) → ℝ) : Pt m :=
  Pt.mk (c 0) (WithLp.toLp 2 fun k => c k.succ)

lemma ofCoords_coords (x : Pt m) : ofCoords (Pt.coords x) = x := by
  simp [ofCoords, Pt.coords, Pt.mk, Pt.lon, Pt.tr]
  rfl

lemma continuous_tr_apply (k : Fin m) : Continuous fun x : Pt m => Pt.tr x k := by
  unfold Pt.tr
  fun_prop

lemma continuous_ofCoords : Continuous (ofCoords : (Fin (m + 1) → ℝ) → Pt m) := by
  unfold ofCoords Pt.mk
  fun_prop

/-! ## Flattening lists of points -/

/-- The list of points with given flattened coordinates (the inverse of `flatCoords`). -/
noncomputable def unflatten {M : ℕ} (z : Fin ((M + 1) * (m + 1)) → ℝ) : Fin (M + 1) → Pt m :=
  fun i => ofCoords fun k => z (finProdFinEquiv (i, k))

lemma flatCoords_apply {M : ℕ} (x : Fin (M + 1) → Pt m) (i : Fin (M + 1)) (k : Fin (m + 1)) :
    flatCoords x (finProdFinEquiv (i, k)) = Pt.coords (x i) k := by
  simp [flatCoords]

lemma unflatten_flatCoords {M : ℕ} (x : Fin (M + 1) → Pt m) : unflatten (flatCoords x) = x := by
  funext i
  simp only [unflatten, flatCoords_apply]
  exact ofCoords_coords _

lemma continuous_unflatten {M : ℕ} :
    Continuous (unflatten : (Fin ((M + 1) * (m + 1)) → ℝ) → Fin (M + 1) → Pt m) :=
  continuous_pi fun _ => continuous_ofCoords.comp (continuous_pi fun _ => continuous_apply _)

/-! ## Chain slabs and admissible points -/

lemma slabCoord_chainSlab (s : ℝ) (τ : Pt m) (i : ℕ) (x : Pt m) :
    slabCoord (chainSlab s τ i) x = Pt.lon x - (Pt.lon τ + i * s) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = (chainSlab s τ i).motion y :=
    ⟨_, (AffineIsometryEquiv.apply_symm_apply _ x).symm⟩
  rw [slabCoord, AffineIsometryEquiv.symm_apply_apply]
  simp only [chainSlab, e1Slab, AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, Pt.lon_add,
    Pt.lon_smul, Pt.lon_e₁]
  ring

/-- The interior of a slab lies strictly between its faces. -/
lemma interior_slab_subset (sl : Slab m) :
    interior sl.set ⊆ slabCoord sl ⁻¹' Ioo 0 sl.width := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  set z := sl.motion.symm x
  have hmem (c : ℝ) (hc : |c| < ε) : slabCoord sl x + c ∈ Icc 0 sl.width := by
    have hy : sl.motion (z + c • e₁) ∈ ball x ε := by
      rw [mem_ball, ← sl.motion.apply_symm_apply x, sl.motion.dist_map, dist_eq_norm,
        add_sub_cancel_left, norm_smul, norm_e₁, mul_one, Real.norm_eq_abs]
      exact hc
    have h := (mem_slab_set_iff sl).mp (hball hy)
    simpa [slabCoord, Pt.lon_add, Pt.lon_smul, Pt.lon_e₁, z] using h
  have h1 := hmem (ε / 2) (by rw [abs_of_pos (half_pos hε)]; linarith)
  have h2 := hmem (-(ε / 2)) (by rw [abs_neg, abs_of_pos (half_pos hε)]; linarith)
  exact ⟨by linarith [h2.1], by linarith [h1.2]⟩

/-- **The slabs of the chain have pairwise disjoint interiors.** -/
theorem pairwise_disjoint_interior_chainSlab {s : ℝ} (hs : 0 < s) (τ : Pt m) (M : ℕ) :
    Pairwise (Function.onFun Disjoint fun i : Fin M => interior (chainSlab s τ i).set) := by
  have key : ∀ i j : Fin M, i < j →
      Disjoint (interior (chainSlab s τ i).set) (interior (chainSlab s τ j).set) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    have hi := interior_slab_subset _ hxi
    have hj := interior_slab_subset _ hxj
    have hwi : (chainSlab s τ (i : ℕ)).width = s := rfl
    have hwj : (chainSlab s τ (j : ℕ)).width = s := rfl
    simp only [mem_preimage, slabCoord_chainSlab, mem_Ioo, hwi, hwj] at hi hj
    have hij' : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
    nlinarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

variable {b s : ℝ} {τ : Pt m} {M : ℕ}

/-- The flattened admissible set. -/
def flatSet (M : ℕ) (s : ℝ) (τ : Pt m) : Set (Fin ((M + 1) * (m + 1)) → ℝ) :=
  flatCoords '' {x | IsAdmissible M s τ x}

lemma isCompact_flatSet (hs : 0 ≤ s) : IsCompact (flatSet M s τ) :=
  (isCompact_admissible M hs τ).image continuous_flatCoords

lemma nonempty_flatSet (hs : 0 ≤ s) : (flatSet M s τ).Nonempty := by
  have h : (fun i : Fin (M + 1) => τ + (((i : ℕ) : ℝ) * s) • (e₁ : Pt m)) ∈
      {x | IsAdmissible M s τ x} := isAdmissible_straight M s hs τ
  exact ⟨_, mem_image_of_mem _ h⟩

lemma unflatten_mem (z : flatSet M s τ) : IsAdmissible M s τ (unflatten z.1) := by
  obtain ⟨x, hx, hz⟩ := z.2
  rw [← hz, unflatten_flatCoords]
  exact hx

lemma flatCoords_unflatten (z : flatSet M s τ) : flatCoords (unflatten z.1) = z.1 := by
  obtain ⟨x, _, hz⟩ := z.2
  rw [← hz, unflatten_flatCoords]

/-! ## The lexicographically least minimizer -/

/-- **From the flattened selection to the lexicographically least minimizer.** If `f` agrees
with the slab sum on admissible points, a flattened admissible point minimizing `f` and least in
the first-differing-coordinate order among the minimizers is the lexicographically least
minimizer of equation `eq:F`. -/
theorem isLexLeastMinimizer_of_select {σ : Pt m → ℝ} (f : (Fin (M + 1) → Pt m) → ℝ)
    (hf : ∀ x, IsAdmissible M s τ x → f x = slabSum b σ M s τ x) (z : flatSet M s τ)
    (hmin : ∀ y : flatSet M s τ, f (unflatten z.1) ≤ f (unflatten y.1))
    (hlex : ∀ y : flatSet M s τ, f (unflatten y.1) = f (unflatten z.1) →
      ∀ p, (∀ j < p, y.1 j = z.1 j) → z.1 p ≤ y.1 p) :
    IsLexLeastMinimizer b σ M s τ (unflatten z.1) := by
  set x₀ := unflatten z.1 with hx₀def
  have hx₀ : IsAdmissible M s τ x₀ := unflatten_mem z
  let toFlat (y : Fin (M + 1) → Pt m) (hy : IsAdmissible M s τ y) : flatSet M s τ :=
    ⟨flatCoords y, mem_image_of_mem _ hy⟩
  have hun (y : Fin (M + 1) → Pt m) (hy : IsAdmissible M s τ y) :
      unflatten (toFlat y hy).1 = y := unflatten_flatCoords y
  have hmin' (y : Fin (M + 1) → Pt m) (hy : IsAdmissible M s τ y) :
      slabSum b σ M s τ x₀ ≤ slabSum b σ M s τ y := by
    have := hmin (toFlat y hy)
    rwa [hun, hf _ hx₀, hf _ hy] at this
  have hF : slabSum b σ M s τ x₀ = slabMinimum b σ M s τ := by
    have : Nonempty {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x} := ⟨⟨x₀, hx₀⟩⟩
    refine le_antisymm (le_ciInf fun y => hmin' y.1 y.2) (ciInf_le ⟨slabSum b σ M s τ x₀, ?_⟩
      (⟨x₀, hx₀⟩ : {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x}))
    rintro _ ⟨y, rfl⟩
    exact hmin' y.1 y.2
  refine ⟨hx₀, hF, fun x' hx' hx'F => ?_⟩
  have hcost : f (unflatten (toFlat x' hx').1) = f (unflatten z.1) := by
    rw [hun x' hx', hf _ hx', hf _ hx₀, hx'F, hF]
  have hz : z.1 = flatCoords x₀ := (flatCoords_unflatten z).symm
  have H := hlex (toFlat x' hx') hcost
  rw [hz] at H
  exact toLex_le_of_forall H

variable (X : Setting m)

/-! ## Measurability -/

/-- On one full-measure event, the lexicographically least minimizer and the slab minimum are
measurable functions of the outcome. -/
theorem exists_measurable_lexMinimizer_ae (hb : X.IsUpperBound b) (hs : 0 < s) (τ : Pt m)
    (M : ℕ) :
    ∃ g : X.Ω → Fin (M + 1) → Pt m, Measurable g ∧ ∃ Fv : X.Ω → ℝ, Measurable Fv ∧
      ∀ᵐ ω ∂X.P, lexMinimizer b (X.ρ ω) M s τ = g ω ∧ X.F b M s τ ω = Fv ω := by
  choose V hVm hVc _ hVae using fun i : Fin M => exists_slabTime_version X hb (chainSlab s τ i)
  let SV : X.Ω → (Fin (M + 1) → Pt m) → ℝ := fun ω x =>
    ∑ i : Fin M, V i ω (x i.castSucc, x i.succ)
  have hSVc (ω : X.Ω) : Continuous (SV ω) :=
    continuous_finsetSum _ fun i _ =>
      (hVc i ω).comp ((continuous_apply i.castSucc).prodMk (continuous_apply i.succ))
  have hSVm {h : X.Ω → Fin (M + 1) → Pt m} (hh : Measurable h) :
      Measurable fun ω => SV ω (h ω) :=
    Finset.measurable_sum _ fun i _ => (hVm i).comp (measurable_id.prodMk
      (((measurable_pi_apply i.castSucc).comp hh).prodMk ((measurable_pi_apply i.succ).comp hh)))
  let G : X.Ω → flatSet M s τ → ℝ := fun ω y => SV ω (unflatten y.1)
  have hGc (ω : X.Ω) : Continuous (G ω) :=
    (hSVc ω).comp (continuous_unflatten.comp continuous_subtype_val)
  have hGm (y : flatSet M s τ) : Measurable fun ω => G ω y := hSVm measurable_const
  obtain ⟨sel, hselm, hsel⟩ := Infra.Selection.exists_measurable_lexMinimizer (flatSet M s τ)
    (isCompact_flatSet hs.le) (nonempty_flatSet hs.le) G hGc hGm
  have hg : Measurable fun ω => unflatten (sel ω).1 :=
    continuous_unflatten.measurable.comp (measurable_subtype_coe.comp hselm)
  refine ⟨fun ω => unflatten (sel ω).1, hg, fun ω => SV ω (unflatten (sel ω).1), hSVm hg, ?_⟩
  filter_upwards [ae_all_iff.mpr hVae] with ω hω
  have hf : ∀ x, IsAdmissible M s τ x → SV ω x = slabSum b (X.ρ ω) M s τ x := by
    intro x hx
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := admissible_mem_chainSlab hs.le hx i
    exact hω i _ h.1 _ h.2
  have hsel' := isLexLeastMinimizer_of_select (SV ω) hf (sel ω) (hsel ω).1 (hsel ω).2
  refine ⟨(lexMinimizer_eq_iff b (X.isValidChain ω hs.le) M τ).mpr hsel', ?_⟩
  change slabMinimum b (X.ρ ω) M s τ = _
  rw [← hsel'.2.1, hf _ hsel'.1]

/-- **The slab minimum `F` is a random variable.** -/
theorem aemeasurable_F (hb : X.IsUpperBound b) (hs : 0 < s) (τ : Pt m) (M : ℕ) :
    AEMeasurable (fun ω => X.F b M s τ ω) X.P := by
  obtain ⟨_, _, Fv, hFv, hae⟩ := exists_measurable_lexMinimizer_ae X hb hs τ M
  exact ⟨Fv, hFv, hae.mono fun _ h => h.2⟩

/-- **The indices `J_i` are random variables.** -/
theorem aemeasurable_J (hb : X.IsUpperBound b) (hs : 0 < s) (τ : Pt m) (M : ℕ) (W : ℝ)
    (i : Fin (M + 1)) : AEMeasurable (fun ω => X.J b M s W τ ω i) X.P := by
  obtain ⟨g, hg, _, _, hae⟩ := exists_measurable_lexMinimizer_ae X hb hs τ M
  refine ⟨fun ω k => if 0 < W then ⌊Pt.tr (g ω i - τ) k / W⌋ else 0, ?_,
    hae.mono fun ω h => ?_⟩
  · refine Measurable.of_eval fun k => ?_
    by_cases hW : 0 < W
    · simp only [hW, ↓reduceIte]
      refine Measurable.floor ?_
      have hc : Continuous fun x : Pt m => Pt.tr (x - τ) k / W :=
        ((continuous_tr_apply k).comp (continuous_id.sub continuous_const)).div_const W
      exact hc.measurable.comp ((measurable_pi_apply i).comp hg)
    · simp only [hW, ↓reduceIte]
      exact measurable_const
  · change (fun k => if 0 < W then ⌊Pt.tr (lexMinimizer b (X.ρ ω) M s τ i - τ) k / W⌋
      else 0) = _
    rw [h.1]

end IsotropicVariance.Infra.Slab
