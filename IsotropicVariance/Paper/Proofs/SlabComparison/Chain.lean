/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.SlabBounds
public import IsotropicVariance.Paper.Defs.Minimum
public import IsotropicVariance.Infra.TimeConstant.Mean
import Mathlib.Tactic.Module

/-! # Straight admissible chains and the deterministic chain lower bound -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {m : ℕ}

/-- The straight sequence of interface points in the slab chain. -/
noncomputable def straightPoints (M : ℕ) (s : ℝ) (τ : Pt m) (i : Fin (M + 1)) : Pt m :=
  τ + ((i : ℝ) * s) • e₁

lemma straightPoints_increment (M : ℕ) (s : ℝ) (τ : Pt m) (i : Fin M) :
    straightPoints M s τ i.succ - straightPoints M s τ i.castSucc = s • e₁ := by
  simp only [straightPoints, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  module

lemma straightPoints_admissible (M : ℕ) {s : ℝ} (hs : 0 ≤ s) (τ : Pt m) :
    IsAdmissible M s τ (straightPoints M s τ) := by
  refine ⟨by simp [straightPoints], by simp [straightPoints], ?_, ?_⟩
  · intro i
    simp [straightPoints, Pt.lon, e₁]
  · intro i
    rw [straightPoints_increment]
    simp only [sub_self, norm_zero]
    positivity

/-- The triangle inequality sums along any finite chain. -/
lemma passage_le_sum_chain (X : Setting m) (ω : X.Ω) (M : ℕ)
    (x : Fin (M + 1) → Pt m) :
    X.passTime ω (x 0) (x (Fin.last M)) ≤
      ∑ i : Fin M, X.passTime ω (x i.castSucc) (x i.succ) := by
  induction M with
  | zero =>
    obtain ⟨a, b, ha, hab⟩ := Infra.TimeConstant.setting_passTime_bounds X
    simpa using (hab ω (x 0) (x 0)).2
  | succ M ih =>
    rw [Fin.sum_univ_castSucc]
    have h := Infra.TimeConstant.setting_passTime_triangle X ω (x 0)
      (x (Fin.last M).castSucc) (x (Fin.last (M + 1)))
    have h' := ih (fun i => x i.castSucc)
    exact h.trans (add_le_add h' le_rfl)

lemma mem_e1Slab_face₀ (a s : ℝ) (x : Pt m) (hx : Pt.lon x = a) :
    x ∈ (e1Slab a s).face₀ := by
  refine ⟨x - a • e₁, ?_, ?_⟩
  · change Pt.lon (x - a • e₁) = 0
    simpa [Pt.lon, e₁] using sub_eq_zero.mpr hx
  · change a • e₁ + (x - a • e₁) = x
    abel

lemma mem_e1Slab_face₁ (a s : ℝ) (x : Pt m) (hx : Pt.lon x = a + s) :
    x ∈ (e1Slab a s).face₁ := by
  refine ⟨x - a • e₁, ?_, ?_⟩
  · change Pt.lon (x - a • e₁) = s
    have H : Pt.lon (x - a • e₁) = Pt.lon x - a := by simp [Pt.lon, e₁]
    rw [H, hx]
    ring
  · change a • e₁ + (x - a • e₁) = x
    abel

lemma admissible_face₀ {M : ℕ} {s : ℝ} {τ : Pt m} {x : Fin (M + 1) → Pt m}
    (hx : IsAdmissible M s τ x) (i : Fin M) :
    x i.castSucc ∈ (chainSlab s τ i).face₀ := by
  apply mem_e1Slab_face₀
  have h := hx.2.2.1 i.castSucc
  simpa [Pt.lon, sub_eq_iff_eq_add, add_comm] using h

lemma admissible_face₁ {M : ℕ} {s : ℝ} {τ : Pt m} {x : Fin (M + 1) → Pt m}
    (hx : IsAdmissible M s τ x) (i : Fin M) :
    x i.succ ∈ (chainSlab s τ i).face₁ := by
  apply mem_e1Slab_face₁
  have h := hx.2.2.1 i.succ
  simp only [Pt.lon, WithLp.ofLp_sub, Prod.fst_sub, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h ⊢
  linarith

/-- Every admissible slab chain costs at least the unrestricted endpoint passage time. -/
lemma passTime_le_slabSum (X : Setting m) (ω : X.Ω) {M : ℕ} {s : ℝ} (hs : 0 ≤ s)
    {τ : Pt m} {x : Fin (M + 1) → Pt m} (hx : IsAdmissible M s τ x)
    {b : ℝ} (hb : X.IsUpperBound b) :
    X.passTime ω τ (τ + ((M : ℝ) * s) • e₁) ≤ slabSum b (X.ρ ω) M s τ x := by
  have h := passage_le_sum_chain X ω M x
  rw [hx.1, hx.2.1] at h
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  exact passageTime_le_slabTime (chainSlab s τ i) hs (X.ρ ω) (hb ω)
    (admissible_face₀ hx i) (admissible_face₁ hx i)

/-- In particular the unrestricted passage time is below the slab minimum `F`. -/
theorem passTime_le_slabMinimum (X : Setting m) (ω : X.Ω) (M : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (τ : Pt m) {b : ℝ} (hb : X.IsUpperBound b) :
    X.passTime ω τ (τ + ((M : ℝ) * s) • e₁) ≤ X.F b M s τ ω := by
  let : Nonempty {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x} :=
    ⟨straightPoints M s τ, straightPoints_admissible M hs τ⟩
  apply le_ciInf
  intro x
  exact passTime_le_slabSum X ω hs x.2 hb

lemma straightPoints_dist (M : ℕ) {s : ℝ} (hs : 0 ≤ s) (τ : Pt m) (i : Fin M) :
    dist (straightPoints M s τ i.castSucc) (straightPoints M s τ i.succ) = s := by
  rw [dist_eq_norm', straightPoints_increment, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hs, Paper.norm_e₁, mul_one]

lemma slabSum_straight_le (X : Setting m) (ω : X.Ω) (M : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (τ : Pt m) {b : ℝ} (hb : X.IsUpperBound b) (hb0 : 0 ≤ b) :
    slabSum b (X.ρ ω) M s τ (straightPoints M s τ) ≤ b * M * s := by
  have hadm := straightPoints_admissible M hs τ
  calc
    _ ≤ ∑ _i : Fin M, b * s := by
      apply Finset.sum_le_sum
      intro i _
      have h := slabTime_le_mul_dist (chainSlab s τ i) hs (X.ρ ω) (hb ω) hb0
        (admissible_face₀ hadm i) (admissible_face₁ hadm i)
      rwa [straightPoints_dist M hs τ i] at h
    _ = _ := by simp; ring

/-- The straight chain supplies the deterministic upper bound for the slab minimum. -/
theorem slabMinimum_le_straight (X : Setting m) (ω : X.Ω) (M : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (τ : Pt m) {b : ℝ} (hb : X.IsUpperBound b) (hb0 : 0 ≤ b) :
    X.F b M s τ ω ≤ b * M * s := by
  let f : {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x} → ℝ :=
    fun x => slabSum b (X.ρ ω) M s τ x
  have hbounded : BddBelow (range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact slabSum_nonneg b (X.ρ ω) M s τ x
  have h := ciInf_le (f := f) hbounded
    (⟨straightPoints M s τ, straightPoints_admissible M hs τ⟩ :
      {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x})
  exact h.trans (slabSum_straight_le X ω M hs τ hb hb0)

/-- The deterministic chain comparison; the proof of Lemma `lem:slab` uses this when `s < C S²`. -/
theorem chain_comparison_small_width (X : Setting m) (ω : X.Ω) (M : ℕ) {s : ℝ}
    (hs : 0 ≤ s) (τ : Pt m) {b : ℝ} (hb : X.IsUpperBound b) (hb0 : 0 ≤ b) :
    0 ≤ X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁) ∧
      X.F b M s τ ω - X.passTime ω τ (τ + ((M : ℝ) * s) • e₁) ≤ b * M * s := by
  refine ⟨sub_nonneg.mpr (passTime_le_slabMinimum X ω M hs τ hb), ?_⟩
  have h0 : 0 ≤ X.passTime ω τ (τ + ((M : ℝ) * s) • e₁) := ENNReal.toReal_nonneg
  linarith [slabMinimum_le_straight X ω M hs τ hb hb0]

end IsotropicVariance.Paper.Proofs.SlabComparison
