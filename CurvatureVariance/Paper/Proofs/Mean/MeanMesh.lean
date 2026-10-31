/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Cubes
import Mathlib.Data.Finset.Lattice.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Pi.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import CurvatureVariance.Infra.FPP.Lattice

/-!
# Finite meshes for the centered slab profiles

A mesh of a bounded set of lattice points has a cardinality bounded in terms of the
radius divided by its spacing, uniformly in the scale.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace CurvatureVariance.Paper.Mean

section Mesh

variable {m : ℕ}

/-- The grid meshCell (side `s`) of a point `y`. -/
noncomputable def meshCell (s : ℝ) (y : Pt m) : ℤ × (Fin m → ℤ) :=
  (⌊y.fst / s⌋, fun i => ⌊y.snd i / s⌋)

theorem norm_le_of_meshCell_eq {s : ℝ} (hs : 0 < s) {y z : Pt m}
    (h : meshCell s y = meshCell s z) : ‖y - z‖ ≤ ((m : ℝ) + 1) * s := by
  have key : ∀ a b : ℝ, ⌊a / s⌋ = ⌊b / s⌋ → |a - b| < s := by
    intro a b hab
    have := Int.abs_sub_lt_one_of_floor_eq_floor hab
    rw [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs] at this
    exact this
  have h1 : |y.fst - z.fst| < s := key _ _ (congrArg Prod.fst h)
  have h2 : ∀ i, |y.snd i - z.snd i| < s := fun i => key _ _ (congrFun (congrArg Prod.snd h) i)
  have hsq : ‖y - z‖ ^ 2 ≤ ((m : ℝ) + 1) * s ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
    have e1 : ‖(y - z).fst‖ ^ 2 ≤ s ^ 2 := by
      have : ‖(y - z).fst‖ = |y.fst - z.fst| := by simp [Real.norm_eq_abs]
      rw [this]; exact sq_le_sq' (by linarith [abs_nonneg (y.fst - z.fst)]) h1.le
    have e2 : ∑ i, ‖(y - z).snd i‖ ^ 2 ≤ ∑ _i : Fin m, s ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have : ‖(y - z).snd i‖ = |y.snd i - z.snd i| := by simp [Real.norm_eq_abs]
      rw [this]; exact sq_le_sq' (by linarith [abs_nonneg (y.snd i - z.snd i), h2 i]) (h2 i).le
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e2
    linarith
  have hnn : 0 ≤ ((m : ℝ) + 1) * s := by positivity
  refine abs_le_of_sq_le_sq' ?_ hnn |>.2
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  nlinarith [sq_nonneg s, mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ)) (sq_nonneg s),
    Nat.cast_nonneg (α := ℝ) m]

theorem meshCell_mem_box {s R : ℝ} (hs : 0 < s) {y : Pt m} (hy : ‖y‖ ≤ R) :
    meshCell s y ∈ Finset.Icc ⌊-R / s⌋ ⌊R / s⌋ ×ˢ
      Fintype.piFinset (fun _ : Fin m => Finset.Icc ⌊-R / s⌋ ⌊R / s⌋) := by
  have hb : ∀ x : ℝ, |x| ≤ R → ⌊x / s⌋ ∈ Finset.Icc ⌊-R / s⌋ ⌊R / s⌋ := by
    intro x hx
    rw [abs_le] at hx
    simp only [Finset.mem_Icc]
    exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right hx.1 hs.le),
      Int.floor_le_floor (div_le_div_of_nonneg_right hx.2 hs.le)⟩
  have hsq := WithLp.prod_norm_sq_eq_of_L2 y
  have hR0 : 0 ≤ R := (norm_nonneg y).trans hy
  have h1 : |y.fst| ≤ R := by
    refine abs_le_of_sq_le_sq' ?_ hR0 |> fun h => abs_le.2 h
    have : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
    have h3 : ‖y.fst‖ ^ 2 = y.fst ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg ‖y.snd‖]
  have h2 : ∀ i, |y.snd i| ≤ R := fun i => by
    have h := PiLp.norm_apply_le y.snd i
    rw [Real.norm_eq_abs] at h
    have : ‖y.snd‖ ≤ R := by
      have h4 : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
      exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖y.fst‖, norm_nonneg y.snd]) hR0 |>.2
    linarith
  simp only [Finset.mem_product, Fintype.mem_piFinset, meshCell]
  exact ⟨hb _ h1, fun i => hb _ (h2 i)⟩

/-- **Mesh of a bounded set of lattice points**: a finite set `U` of lattice points in the ball of
radius `R` about `c` contains a subset `G` of at most `(4 (m+1) (R/ρ + 1))^(m+1)` points such that
every point of `U` is within `ρ` of `G`. -/
theorem exists_mesh (U : Finset (Vertex m)) (c : Pt m) {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hU : ∀ u ∈ U, ‖point u - c‖ ≤ R) :
    ∃ G : Finset (Vertex m), G ⊆ U ∧
      (G.card : ℝ) ≤ (4 * ((m : ℝ) + 1) * (R / ρ + 1)) ^ (m + 1) ∧
      ∀ u ∈ U, ∃ p ∈ G, ‖point u - point p‖ ≤ ρ := by
  classical
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set s : ℝ := ρ / ((m : ℝ) + 1) with hs_def
  have hs : 0 < s := by positivity
  set idx : Vertex m → ℤ × (Fin m → ℤ) := fun u => meshCell s (point u - c)
    with hidx
  obtain ⟨G, hGU, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f := idx)
    (U : Set _) (U.image idx) (by intro k hk; simpa using hk)
  refine ⟨G, fun x hx => by simpa using hGU hx, ?_, ?_⟩
  · have hcard : G.card = (U.image idx).card := by
      rw [← himg, Finset.card_image_of_injOn hinj]
    set a : ℤ := ⌊-R / s⌋
    set b : ℤ := ⌊R / s⌋
    have hsub : U.image idx ⊆ Finset.Icc a b ×ˢ Fintype.piFinset (fun _ : Fin m => Finset.Icc a b) := by
      intro k hk
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hk
      exact meshCell_mem_box hs (hU u hu)
    have hn : ((Finset.Icc a b).card : ℝ) ≤ 4 * ((m : ℝ) + 1) * (R / ρ + 1) := by
      rw [Int.card_Icc]
      have hRs : R / s = ((m : ℝ) + 1) * (R / ρ) := by
        rw [hs_def]; field_simp
      have ha : (a : ℝ) ≥ -R / s - 1 := (Int.sub_one_lt_floor _).le
      have hb : (b : ℝ) ≤ R / s := Int.floor_le _
      have hba : 0 ≤ b + 1 - a := by
        have h0 : 0 ≤ b := Int.floor_nonneg.2 (by positivity)
        have h1 : a ≤ 0 := Int.floor_nonpos (by
          have : 0 ≤ R / s := by positivity
          rw [neg_div]; linarith)
        omega
      have : (((b + 1 - a).toNat : ℕ) : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hba]
      rw [this]
      push_cast
      have hq : 0 ≤ R / ρ := by positivity
      rw [neg_div] at ha
      nlinarith [mul_nonneg hm1.le hq]
    have hbox : ((Finset.Icc a b ×ˢ Fintype.piFinset
        (fun _ : Fin m => Finset.Icc a b)).card : ℝ) ≤ (4 * ((m : ℝ) + 1) * (R / ρ + 1)) ^ (m + 1) := by
      rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, pow_succ']
      push_cast
      exact mul_le_mul hn (pow_le_pow_left₀ (Nat.cast_nonneg _) hn m) (by positivity)
        (by positivity)
    rw [hcard]
    exact (Nat.cast_le.2 (Finset.card_le_card hsub)).trans hbox
  · intro u hu
    have hk : idx u ∈ G.image idx := by rw [himg]; exact Finset.mem_image_of_mem _ hu
    obtain ⟨p, hp, hpk⟩ := Finset.mem_image.1 hk
    refine ⟨p, hp, ?_⟩
    have := norm_le_of_meshCell_eq hs hpk.symm
    have e : point u - point p =
        (point u - c) - (point p - c) := by abel
    rw [e]
    calc _ ≤ ((m : ℝ) + 1) * s := this
      _ = ρ := by rw [hs_def]; field_simp

end Mesh

/-- A transverse lattice cube contains finitely many vertices. -/
theorem finite_transverseCube {m : ℕ} (p : ℤ) (c : EuclideanSpace ℝ (Fin m)) (a : ℝ) :
    (transverseCube p c a).Finite := by
  classical
  let lo : Vertex m := (p, fun j => ⌈c j - a / 2⌉)
  let hi : Vertex m := (p, fun j => ⌊c j + a / 2⌋)
  apply (Finset.finite_toSet (Finset.Icc lo hi)).subset
  intro u hu
  rw [Finset.mem_coe, Finset.mem_Icc]
  refine ⟨⟨by exact hu.1.ge, ?_⟩, ⟨by exact hu.1.le, ?_⟩⟩
  · intro j
    apply Int.ceil_le.mpr
    have hh := (abs_le.mp (hu.2 j)).1
    linarith only [hh]
  · intro j
    apply Int.le_floor.mpr
    have hh := (abs_le.mp (hu.2 j)).2
    linarith only [hh]

/-- A dimension-dependent radius for a cube, sufficient for the scale-independent mesh count. -/
theorem norm_cube_point_sub_center_le {m : ℕ} {p : ℤ}
    {c : EuclideanSpace ℝ (Fin m)} {a : ℝ} (ha : 0 ≤ a)
    {u : Vertex m} (hu : u ∈ transverseCube p c a) :
    ‖point u - WithLp.toLp 2 ((p : ℝ), c)‖ ≤ ((m : ℝ) + 1) * a := by
  let x : Pt m := point u - WithLp.toLp 2 ((p : ℝ), c)
  have hfst : x.fst = 0 := by
    change (u.1 : ℝ) - (p : ℝ) = 0
    rw [hu.1, sub_self]
  have hcoord (j : Fin m) : ‖x.snd j‖ ≤ a := by
    change |(u.2 j : ℝ) - c j| ≤ a
    exact (hu.2 j).trans (by linarith only [ha])
  have hsq : ‖x‖ ^ 2 ≤ (m : ℝ) * a ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, hfst, norm_zero, zero_pow two_ne_zero,
      zero_add, EuclideanSpace.norm_sq_eq]
    calc
      ∑ j : Fin m, ‖x.snd j‖ ^ 2 ≤ ∑ _j : Fin m, a ^ 2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord j) 2)
      _ = (m : ℝ) * a ^ 2 := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
  have hb : (m : ℝ) * a ^ 2 ≤ (((m : ℝ) + 1) * a) ^ 2 := by
    nlinarith only [sq_nonneg ((m : ℝ) * a), sq_nonneg a,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sq_nonneg a)]
  exact (abs_le_of_sq_le_sq' (hsq.trans hb) (by positivity)).2

end CurvatureVariance.Paper.Mean
