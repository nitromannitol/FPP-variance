/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.CurveDirections

/-! # Ordered crossings of equally spaced hyperplanes -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- A curve between the terminal faces has ordered hits of all intermediate hyperplanes.
After the final hit the sequence is capped at the terminal parameter. -/
theorem exists_ordered_hyperplane_hits (M : ℕ) (hM : 1 ≤ M) {s : ℝ} (hs : 0 < s)
    (τ : Pt m) (γ : Infra.Curves.LipCurve (Pt m) τ (τ + ((M : ℝ) * s) • e₁)) :
    ∃ t : ℕ → ℝ, t 0 = 0 ∧ t M = 1 ∧ Monotone t ∧
      ∀ n : ℕ, t n ∈ Icc (0 : ℝ) 1 ∧
        Pt.lon (γ.toFun (t n)) = Pt.lon τ + ((min n M : ℕ) : ℝ) * s := by
  classical
  have hend : Pt.lon (γ.toFun 1) = Pt.lon τ + (M : ℝ) * s := by
    rw [γ.map_one]
    simp [Pt.lon, e₁]
  have hcont : ContinuousOn (fun t => Pt.lon (γ.toFun t)) (Icc (0 : ℝ) 1) := by
    have hlon : LipschitzWith 1 (Pt.lon (m := m)) := LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, NNReal.coe_one, one_mul]
      exact Infra.Slab.abs_lon_sub_le x y
    exact hlon.continuous.comp_continuousOn γ.toRectifiable.continuousOn
  let A (n : ℕ) := {t : ℝ // t ∈ Icc (0 : ℝ) 1 ∧
    Pt.lon (γ.toFun t) = Pt.lon τ + ((min n M : ℕ) : ℝ) * s ∧ (M ≤ n → t = 1)}
  have hnext (n : ℕ) (a : A n) : ∃ b : A (n + 1), (a : ℝ) ≤ b := by
    by_cases hcap : M ≤ n + 1
    · refine ⟨⟨1, ⟨zero_le_one, le_rfl⟩, ?_, fun _ => rfl⟩, a.property.1.2⟩
      simpa only [min_eq_right hcap] using hend
    · have hlow : Pt.lon (γ.toFun a) ≤ Pt.lon τ + ((min (n + 1) M : ℕ) : ℝ) * s := by
        rw [a.property.2.1]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (min_le_min_right M (Nat.le_succ n))) hs.le)
      have hhigh : Pt.lon τ + ((min (n + 1) M : ℕ) : ℝ) * s ≤ Pt.lon (γ.toFun 1) := by
        rw [hend]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_right _ _)) hs.le)
      obtain ⟨b, hb, hlevel⟩ := intermediate_value_Icc a.property.1.2
        (hcont.mono (Icc_subset_Icc a.property.1.1 le_rfl)) ⟨hlow, hhigh⟩
      exact ⟨⟨b, ⟨a.property.1.1.trans hb.1, hb.2⟩, hlevel, fun h => (hcap h).elim⟩, hb.1⟩
  let first : A 0 := ⟨0, ⟨le_rfl, zero_le_one⟩,
    by simp only [γ.map_zero, min_eq_left (Nat.zero_le M), Nat.cast_zero, zero_mul, add_zero],
    fun h => by omega⟩
  let next (n : ℕ) (a : A n) : A (n + 1) := Classical.choose (hnext n a)
  let F : (n : ℕ) → A n := Nat.rec first next
  let t (n : ℕ) : ℝ := (F n).val
  have ht0 : t 0 = 0 := rfl
  have htM : t M = 1 := (F M).property.2.2 le_rfl
  have hmono : Monotone t := monotone_nat_of_le_succ fun n =>
    Classical.choose_spec (hnext n (F n))
  exact ⟨t, ht0, htM, hmono, fun n => ⟨(F n).property.1, (F n).property.2.1⟩⟩

end IsotropicVariance.Paper.Proofs.SlabComparison
