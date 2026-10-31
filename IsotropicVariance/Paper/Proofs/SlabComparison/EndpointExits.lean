/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SlabComparison.CurveDirections

/-! # The two end pieces of a near-geodesic

The proof of equation `eq:slab` replaces the two end pieces of a near-geodesic by
segments, and uses that the points of the middle piece are at distance at least `R` from both
endpoints. The cuts are the last exit from the ball of radius `R` around the first endpoint and the
first entry after it into the ball around the second endpoint.
-/

@[expose] public section
open Set
namespace IsotropicVariance.Paper.Proofs.SlabComparison
open Paper
variable {m : ℕ}

/-- The last time a continuous function is at most `r`, between a point where it is at most `r` and
a point where it is at least `r`: from then on it is at least `r`. -/
lemma exists_last_hit {f : ℝ → ℝ} {α β r : ℝ} (hαβ : α ≤ β) (hf : ContinuousOn f (Icc α β))
    (hα : f α ≤ r) (hβ : r ≤ f β) :
    ∃ a ∈ Icc α β, f a = r ∧ ∀ t ∈ Icc a β, r ≤ f t := by
  let S := Icc α β ∩ f ⁻¹' Iic r
  have hclosed : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  have hne : S.Nonempty := ⟨α, ⟨le_rfl, hαβ⟩, hα⟩
  have hmem := hcompact.sSup_mem hne
  set a := sSup S
  have hle : ∀ t ∈ S, t ≤ a := fun t ht => le_csSup hcompact.bddAbove ht
  have haβ : a ≤ β := hmem.1.2
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc haβ (hf.mono (Icc_subset_Icc hmem.1.1 le_rfl))
    ⟨hmem.2, hβ⟩
  have hta : t = a :=
    le_antisymm (hle t ⟨⟨hmem.1.1.trans ht.1, ht.2⟩, hft.le⟩) ht.1
  refine ⟨a, hmem.1, hta ▸ hft, fun u hu => ?_⟩
  by_contra hlt
  have hua : u = a :=
    le_antisymm (hle u ⟨⟨hmem.1.1.trans hu.1, hu.2⟩, (not_le.mp hlt).le⟩) hu.1
  rw [hua, ← hta, hft] at hlt
  exact hlt le_rfl

/-- The first time a continuous function is at most `r`, after a point where it is at least `r`:
until then it is at least `r`. -/
lemma exists_first_hit {f : ℝ → ℝ} {α β r : ℝ} (hαβ : α ≤ β) (hf : ContinuousOn f (Icc α β))
    (hα : r ≤ f α) (hβ : f β ≤ r) :
    ∃ c ∈ Icc α β, f c = r ∧ ∀ t ∈ Icc α c, r ≤ f t := by
  have hmaps : MapsTo (fun t => α + β - t) (Icc α β) (Icc α β) :=
    fun t ht => ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
  have hg : ContinuousOn (fun t => f (α + β - t)) (Icc α β) :=
    hf.comp (by fun_prop) hmaps
  obtain ⟨a, ha, hfa, hafter⟩ := exists_last_hit hαβ hg
    (by simpa only [add_sub_cancel_left] using hβ)
    (by simpa only [add_sub_cancel_right] using hα)
  refine ⟨α + β - a, hmaps ha, hfa, fun t ht => ?_⟩
  have hh := hafter (α + β - t) ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
  simpa only [sub_sub_cancel] using hh

/-- **The end pieces of a curve** (proof of equation `eq:slab`): the parameters `a ≤ c` at which
the curve is at distance `r` from its endpoints, such that between them it is at distance at least
`r` from both. -/
theorem exists_endpoint_exits {u v : Pt m} (γ : Infra.Curves.LipCurve (Pt m) u v)
    {r : ℝ} (hr : 0 ≤ r) (hD : 2 * r ≤ dist u v) :
    ∃ a c : ℝ, 0 ≤ a ∧ a ≤ c ∧ c ≤ 1 ∧ dist u (γ.toFun a) = r ∧ dist v (γ.toFun c) = r ∧
      ∀ t ∈ Icc a c, r ≤ dist u (γ.toFun t) ∧ r ≤ dist v (γ.toFun t) := by
  have hcont : ContinuousOn γ.toFun (Icc (0 : ℝ) 1) := γ.toRectifiable.continuousOn
  have hdist (p : Pt m) : ContinuousOn (fun t => dist p (γ.toFun t)) (Icc (0 : ℝ) 1) :=
    fun t ht => continuousWithinAt_const.dist (hcont t ht)
  obtain ⟨a, ha, hfa, hafter⟩ := exists_last_hit (f := fun t => dist u (γ.toFun t)) zero_le_one
    (hdist u) (by simpa only [γ.map_zero, dist_self] using hr)
    (by simpa only [γ.map_one] using (by linarith only [hr, hD] : r ≤ dist u v))
  have hstart : r ≤ dist v (γ.toFun a) := by
    have htri := dist_triangle u (γ.toFun a) v
    rw [dist_comm (γ.toFun a) v] at htri
    linarith only [htri, hfa, hD]
  obtain ⟨c, hc, hgc, hbefore⟩ := exists_first_hit (f := fun t => dist v (γ.toFun t)) ha.2
    ((hdist v).mono (Icc_subset_Icc ha.1 le_rfl)) hstart
    (by simpa only [γ.map_one, dist_self] using hr)
  exact ⟨a, c, ha.1, hc.1, hc.2, hfa, hgc, fun t ht =>
    ⟨hafter t ⟨ht.1, ht.2.trans hc.2⟩, hbefore t ht⟩⟩

end IsotropicVariance.Paper.Proofs.SlabComparison
