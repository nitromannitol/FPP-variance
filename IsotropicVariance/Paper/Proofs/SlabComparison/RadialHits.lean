/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.NearOptimal
import Mathlib.Topology.Order.IntermediateValue

/-! # Ordered radial hits of continuous rectifiable curves -/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
variable {E : Type*} [PseudoMetricSpace E]

/-- Every intermediate radius is hit between the supplied parameters. No choice of a
geodesic or differentiability of its parametrization is needed. -/
lemma exists_radius_hit_between (γ : IsotropicVariance.RectifiableCurve E) (p : E)
    {a b r : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hra : dist p (γ.toFun a) ≤ r) (hrb : r ≤ dist p (γ.toFun b)) :
    ∃ t ∈ Icc a b, dist p (γ.toFun t) = r := by
  have hc : ContinuousOn (fun t => dist p (γ.toFun t)) (Icc a b) :=
    by
      intro t ht
      exact continuousWithinAt_const.dist
        ((γ.continuousOn.mono (Icc_subset_Icc ha hb)) t ht)
  exact intermediate_value_Icc hab hc ⟨hra, hrb⟩

/-- A monotone sequence of radial hits, doubling the radius until the terminal radius is
reached. At and after that scale the parameter is exactly the terminal parameter. -/
theorem exists_dyadic_radial_hits (γ : IsotropicVariance.RectifiableCurve E) (p : E)
    {b c R D : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (hc : c ≤ 1)
    (hR : 0 < R) (hRD : R < D)
    (hstart : dist p (γ.toFun b) = R) (hend : dist p (γ.toFun c) = D) :
    ∃ t : ℕ → ℝ, t 0 = b ∧ Monotone t ∧ ∀ n,
      t n ∈ Icc b c ∧ dist p (γ.toFun (t n)) = min (R * 2 ^ n) D ∧
        (D ≤ R * 2 ^ n → t n = c) := by
  classical
  let r : ℕ → ℝ := fun n => min (R * 2 ^ n) D
  have hr0 : r 0 = R := by simp only [r, pow_zero, mul_one, min_eq_left hRD.le]
  have hrmono (n : ℕ) : r n ≤ r (n + 1) := by
    apply min_le_min _ le_rfl
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ n)) hR.le
  let A (n : ℕ) := {t : ℝ // t ∈ Icc b c ∧ dist p (γ.toFun t) = r n ∧ (r n = D → t = c)}
  have H (n : ℕ) (t : A n) : ∃ q : A (n + 1), t.1 ≤ q.1 := by
    by_cases hcap : r (n + 1) = D
    · refine ⟨⟨c, ⟨hbc, le_rfl⟩, hend.trans hcap.symm, fun _ => rfl⟩, t.2.1.2⟩
    · obtain ⟨q, hq, hqr⟩ := exists_radius_hit_between γ p
        (hb.trans t.2.1.1) t.2.1.2 hc
        (t.2.2.1.trans_le (hrmono n)) (by rw [hend]; exact min_le_right _ _)
      exact ⟨⟨q, ⟨t.2.1.1.trans hq.1, hq.2⟩, hqr, fun h => (hcap h).elim⟩, hq.1⟩
  choose step hstep using H
  let initial : A 0 := ⟨b, ⟨le_rfl, hbc⟩, hstart.trans hr0.symm, fun h =>
    ((hRD.ne (hr0.symm.trans h))).elim⟩
  let q : (n : ℕ) → A n := fun n => Nat.rec initial (fun n t => step n t) n
  refine ⟨fun n => (q n).1, rfl, monotone_nat_of_le_succ (fun n => hstep n (q n)), ?_⟩
  intro n
  refine ⟨(q n).2.1, (q n).2.2.1, ?_⟩
  intro hn
  exact (q n).2.2.2 (min_eq_right hn)

end IsotropicVariance.Paper.Proofs.SlabComparison
