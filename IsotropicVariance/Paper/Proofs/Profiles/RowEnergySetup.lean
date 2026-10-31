/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry
public import IsotropicVariance.Paper.Proofs.Profiles.PenalizedExp
public import IsotropicVariance.Paper.Proofs.Profiles.ProfileBounds
public import IsotropicVariance.Infra.Measurability.MinimizerMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# The proof of Lemma `lem:rowenergy`: the profile functional of a slab

For a pair of transverse cubes `p` and a function `f` of the endpoints (a version of the slab
passage time), `profileFun p f` is the supremum of `|f(u, v) − |v − u||` over a fixed countable
dense subset of `I × I'`. It is a measurable function of `f` (for the product σ-algebra on
functions), and for `f` continuous it is the supremum over all of `I × I'`. This makes the
summands of the exponential union bound of the proof of Lemma `lem:rowenergy` functions of the
independent versions of the slab passage times (`Infra.Slab.exists_iIndep_slabTime_versions`).
-/

@[expose] public section

open MeasureTheory Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

open Infra.Os Infra.Slab

variable {m : ℕ}

lemma isCompact_stdBox (r₀ : ℝ) (r : Fin m → ℝ) : IsCompact (stdBox r₀ r) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h : stdBox r₀ r = {x : Pt m | |Pt.lon x| ≤ r₀} ∩ ⋂ k, {x : Pt m | |Pt.tr x k| ≤ r k} := by
      ext x; simp [stdBox]
    rw [h]
    exact (isClosed_le Pt.continuous_lon.abs continuous_const).inter
      (isClosed_iInter fun k => isClosed_le (Infra.Slab.continuous_tr_apply k).abs continuous_const)
  · set ρ : ℝ := ∑ k, |r k| with hρ
    have hρ0 : 0 ≤ ρ := Finset.sum_nonneg fun k _ => abs_nonneg _
    refine (Metric.isBounded_closedBall (x := (0 : Pt m)) (r := |r₀| + Real.sqrt m * ρ)).subset
      fun x hx => ?_
    rw [mem_closedBall, dist_zero_right]
    have htr : ‖Pt.tr x‖ ≤ Real.sqrt m * ρ := norm_le_of_abs_le hρ0 fun k =>
      (hx.2 k).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |r k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ k)))
    have hlon : |Pt.lon x| ≤ |r₀| := hx.1.trans (le_abs_self _)
    have h1 := norm_sq_eq_lon_tr x
    have h2 : ‖x‖ ^ 2 ≤ (|r₀| + Real.sqrt m * ρ) ^ 2 := by
      rw [h1, ← sq_abs (Pt.lon x)]
      nlinarith [abs_nonneg (Pt.lon x), norm_nonneg (Pt.tr x)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

lemma isCompact_of_isRectBox {B : Set (Pt m)} {c : Pt m} (h : IsRectBox B c) : IsCompact B := by
  obtain ⟨g, r₀, r, -, -, -, rfl⟩ := h
  exact (isCompact_stdBox r₀ r).image g.continuous

/-- A countable dense subset of `I × I'`. -/
noncomputable def pairDense (p : CubePair m) : Set (p.first × p.second) :=
  (exists_countable_dense (p.first × p.second)).choose

lemma pairDense_countable (p : CubePair m) : (pairDense p).Countable :=
  (exists_countable_dense (p.first × p.second)).choose_spec.1

lemma pairDense_dense (p : CubePair m) : Dense (pairDense p) :=
  (exists_countable_dense (p.first × p.second)).choose_spec.2

/-- The profile functional: `sup |f(u, v) − |v − u||` over the countable dense subset of
`I × I'`. -/
noncomputable def profileFun (p : CubePair m) (f : Pt m × Pt m → ℝ) : ℝ :=
  ⨆ d : pairDense p, |f (((d : p.first × p.second).1 : Pt m), ((d : p.first × p.second).2 : Pt m)) -
    dist ((d : p.first × p.second).1 : Pt m) ((d : p.first × p.second).2 : Pt m)|

lemma measurable_profileFun (p : CubePair m) : Measurable (profileFun p) := by
  have : Countable (pairDense p) := (pairDense_countable p).to_subtype
  exact Measurable.iSup fun d => continuous_abs.measurable.comp
    ((measurable_pi_apply _).sub_const _)

lemma profileFun_spec (p : CubePair m) (h1 : 0 ≤ p.side₁) (h2 : 0 ≤ p.side₂)
    {f : Pt m × Pt m → ℝ} (hf : Continuous f) :
    BddAbove (range fun q : p.first × p.second => |f ((q.1 : Pt m), (q.2 : Pt m)) -
      dist (q.1 : Pt m) q.2|) ∧
    ⨆ q : p.first × p.second, |f ((q.1 : Pt m), (q.2 : Pt m)) - dist (q.1 : Pt m) q.2| =
      profileFun p f := by
  have : CompactSpace p.first :=
    isCompact_iff_compactSpace.mp (isCompact_of_isRectBox (cubePair_isRectBox_first p h1))
  have : CompactSpace p.second :=
    isCompact_iff_compactSpace.mp (isCompact_of_isRectBox (cubePair_isRectBox_second p h2))
  have : Nonempty (p.first × p.second) :=
    ⟨(⟨_, cubePair_center₁_mem p h1⟩, ⟨_, cubePair_center₂_mem p h2⟩)⟩
  have hc : Continuous fun q : p.first × p.second => |f ((q.1 : Pt m), (q.2 : Pt m)) -
      dist (q.1 : Pt m) q.2| := by
    have h : Continuous fun q : p.first × p.second => ((q.1 : Pt m), (q.2 : Pt m)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact ((hf.comp h).sub (continuous_dist.comp h)).abs
  have hb := (isCompact_range hc).bddAbove
  exact ⟨hb, iSup_eq_iSup_dense (pairDense_dense p) hc hb⟩

/-- For continuous `f`, the profile functional bounds `|f(u, v) − |v − u||` on `I × I'`. -/
lemma le_profileFun (p : CubePair m) (h1 : 0 ≤ p.side₁) (h2 : 0 ≤ p.side₂)
    {f : Pt m × Pt m → ℝ} (hf : Continuous f) {u v : Pt m} (hu : u ∈ p.first)
    (hv : v ∈ p.second) : |f (u, v) - dist u v| ≤ profileFun p f := by
  obtain ⟨hb, heq⟩ := profileFun_spec p h1 h2 hf
  rw [← heq]
  exact le_ciSup hb (⟨u, hu⟩, ⟨v, hv⟩)

/-- For continuous `f`, the profile functional is the supremum over `I × I'`. -/
lemma profileFun_eq_iSup (p : CubePair m) (h1 : 0 ≤ p.side₁) (h2 : 0 ≤ p.side₂)
    {f : Pt m × Pt m → ℝ} (hf : Continuous f) :
    profileFun p f = ⨆ (u : p.first) (v : p.second), |f ((u : Pt m), (v : Pt m)) - dist (u : Pt m) v| := by
  obtain ⟨hb, heq⟩ := profileFun_spec p h1 h2 hf
  rw [← heq, iSup_iSup_eq_iSup_prod hb]

end IsotropicVariance.Paper.Proofs.Profiles
