/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.LocalBoxes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry

/-!
# The cube pair of Lemma `lem:localization` and the hypotheses of the tree bound

For an admissible pair of transverse cubes at distance `n` (sides at most `4W`, slope of the
centers at most `κ`): the points of the cubes lie within `ε = 2√m W` of the centers, the
centers are at distance `r ∈ [n, (1 + κ)n]`, the cubes lie in the faces of the slab of the pair, and
the cubes and the boxes of the proof of Lemma `lem:localization` are rectangular boxes centered on
the lines of the tree bound (equation `eq:tree`; the proof of Lemma `lem:localization`).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

open IsotropicVariance.Paper.Proofs.Profiles (abs_lon_le_norm)
open IsotropicVariance.Paper.Proofs.Responses (transverseIntegerPoint)
namespace IsotropicVariance.Paper.Proofs.Localization

variable {m : ℕ}

/-! ## The cube pair -/

namespace CubePairFacts

variable {p : CubePair m} {n W κ : ℝ}

lemma dist_first_le (hp : p.IsAdmissible n W κ) {u : Pt m} (hu : u ∈ p.first) :
    dist u p.center₁ ≤ 2 * Real.sqrt m * W := by
  obtain ⟨x, ⟨hx0, hx⟩, rfl⟩ := hu
  rw [CubePair.center₁, p.motion.dist_map, dist_zero_right]
  have h := Pt.lon_tr_norm_le x
  rw [hx0, abs_zero, zero_add] at h
  have hW : 0 ≤ W := by linarith [hp.2.1, hp.2.2.1]
  have := Profiles.norm_le_of_abs_le (y := Pt.tr x) (ρ := 2 * W) (by positivity) fun k =>
    (hx k).trans (by linarith [hp.2.2.1])
  linarith

lemma dist_second_le (hp : p.IsAdmissible n W κ) {v : Pt m} (hv : v ∈ p.second) :
    dist v p.center₂ ≤ 2 * Real.sqrt m * W := by
  obtain ⟨x, ⟨hx0, hx⟩, rfl⟩ := hv
  rw [CubePair.center₂, p.motion.dist_map, dist_eq_norm]
  have h := Pt.lon_tr_norm_le (x - Pt.mk p.dist p.offset)
  rw [Pt.lon_sub, hx0, Pt.lon_mk, sub_self, abs_zero, zero_add, Pt.tr_sub,
    Pt.tr_mk] at h
  have hW : 0 ≤ W := by linarith [hp.2.2.2.1, hp.2.2.2.2.1]
  have := Profiles.norm_le_of_abs_le (y := Pt.tr x - p.offset) (ρ := 2 * W) (by positivity)
    fun k => by
      simp only [PiLp.sub_apply]
      exact (hx k).trans (by linarith [hp.2.2.2.2.1])
  linarith

lemma dist_centers (hp : p.IsAdmissible n W κ) (hn : 0 < n) :
    n ≤ dist p.center₁ p.center₂ ∧ dist p.center₁ p.center₂ ≤ (1 + κ) * n := by
  rw [CubePair.center₁, CubePair.center₂, p.motion.dist_map, dist_zero_left]
  have hd : p.dist = n := hp.1
  set y : Pt m := Pt.mk p.dist p.offset
  have hoff : ‖p.offset‖ ≤ κ * n := by
    have h := hp.2.2.2.2.2
    rwa [CubePair.centerSlope, hd, div_le_iff₀ hn] at h
  constructor
  · have h1 := abs_lon_le_norm y
    have h2 : Pt.lon y = n := by simp [y, hd]
    rw [h2, abs_of_pos hn] at h1
    exact h1
  · have h1 := Pt.lon_tr_norm_le y
    have h2 : Pt.lon y = n := by simp [y, hd]
    have h3 : Pt.tr y = p.offset := by simp [y]
    rw [h2, h3, abs_of_pos hn] at h1
    linarith

lemma first_subset_slab (hp : p.IsAdmissible n W κ) (hn : 0 ≤ n) :
    p.first ⊆ p.slab.set := by
  rintro _ ⟨x, ⟨hx0, -⟩, rfl⟩
  refine ⟨x, ⟨by rw [hx0], ?_⟩, rfl⟩
  change Pt.lon x ≤ p.dist
  rw [hx0, hp.1]; exact hn

lemma second_subset_slab (hp : p.IsAdmissible n W κ) (hn : 0 ≤ n) :
    p.second ⊆ p.slab.set := by
  rintro _ ⟨x, ⟨hx0, -⟩, rfl⟩
  refine ⟨x, ⟨?_, ?_⟩, rfl⟩
  · rw [hx0, hp.1]; exact hn
  · change Pt.lon x ≤ p.dist
    rw [hx0]

lemma isRectBox_first (hp : p.IsAdmissible n W κ) : IsRectBox p.first p.center₁ := by
  refine ⟨p.motion, 0, fun _ => p.side₁ / 2, le_rfl, fun _ => by linarith [hp.2.1], rfl, ?_⟩
  unfold CubePair.first
  congr 1
  ext x
  simp only [mem_ofPred_eq, abs_nonpos_iff]

lemma isRectBox_second (hp : p.IsAdmissible n W κ) : IsRectBox p.second p.center₂ := by
  refine ⟨(AffineIsometryEquiv.constVAdd ℝ (Pt m) (Pt.mk p.dist p.offset)).trans p.motion, 0,
    fun _ => p.side₂ / 2, le_rfl, fun _ => by linarith [hp.2.2.2.1], by simp [CubePair.center₂],
    ?_⟩
  have hS : {x : Pt m | Pt.lon x = p.dist ∧ ∀ k, |Pt.tr x k - p.offset k| ≤ p.side₂ / 2} =
      (fun y => Pt.mk p.dist p.offset + y) ''
        {x : Pt m | |Pt.lon x| ≤ 0 ∧ ∀ k, |Pt.tr x k| ≤ p.side₂ / 2} := by
    ext x
    constructor
    · rintro ⟨hx0, hx⟩
      refine ⟨x - Pt.mk p.dist p.offset, ⟨?_, fun k => ?_⟩, by abel_nf⟩
      · rw [abs_nonpos_iff, Pt.lon_sub, hx0, Pt.lon_mk, sub_self]
      · rw [Pt.tr_sub, Pt.tr_mk]; exact hx k
    · rintro ⟨y, ⟨hy0, hy⟩, rfl⟩
      refine ⟨?_, fun k => ?_⟩
      · rw [abs_nonpos_iff] at hy0
        rw [Pt.lon_add, hy0, Pt.lon_mk, add_zero]
      · rw [Pt.tr_add, Pt.tr_mk]
        simp only [PiLp.add_apply, add_sub_cancel_left]
        exact hy k
  unfold CubePair.second
  rw [hS, image_image]
  rfl

lemma isCompact_first : IsCompact p.first := by
  refine IsCompact.image ?_ p.motion.continuous
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_eq Pt.continuous_lon continuous_const).inter (isClosed_iInter fun k => ?_)
    exact isClosed_le (by unfold Pt.tr; fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Pt m)) (r := Real.sqrt m * |p.side₁ / 2|)).subset
      fun x ⟨hx0, hx⟩ => ?_
    rw [mem_closedBall, dist_zero_right]
    have h := Pt.lon_tr_norm_le x
    rw [hx0, abs_zero, zero_add] at h
    exact h.trans (Profiles.norm_le_of_abs_le (abs_nonneg _) fun k => (hx k).trans (le_abs_self _))

lemma isCompact_second : IsCompact p.second := by
  refine IsCompact.image ?_ p.motion.continuous
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [Set.ofPred_and, Set.ofPred_forall]
    refine (isClosed_eq Pt.continuous_lon continuous_const).inter (isClosed_iInter fun k => ?_)
    exact isClosed_le (by unfold Pt.tr; fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (Pt.mk p.dist p.offset : Pt m))
      (r := Real.sqrt m * |p.side₂ / 2|)).subset fun x ⟨hx0, hx⟩ => ?_
    rw [mem_closedBall, dist_eq_norm]
    have h := Pt.lon_tr_norm_le (x - Pt.mk p.dist p.offset)
    rw [Pt.lon_sub, hx0, Pt.lon_mk, sub_self, abs_zero, zero_add, Pt.tr_sub,
      Pt.tr_mk] at h
    refine h.trans (Profiles.norm_le_of_abs_le (abs_nonneg _) fun k => ?_)
    simp only [PiLp.sub_apply]
    exact (hx k).trans (le_abs_self _)

end CubePairFacts

/-! ## The boxes as rectangular boxes -/

lemma isRectBox_box (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n W C₀ : ℝ} (hn : 0 ≤ n) (hW : 0 ≤ W)
    (jk : ℕ × (Fin m → ℤ)) :
    IsRectBox (g '' boxSet n W C₀ jk.1 jk.2) (g (boxCtr n W C₀ jk.1 jk.2)) := by
  refine ⟨(AffineIsometryEquiv.constVAdd ℝ (Pt m) (boxCtr n W C₀ jk.1 jk.2)).trans g, n / 1000,
    fun _ => W, by positivity, fun _ => hW, by simp, ?_⟩
  have hS : boxSet n W C₀ jk.1 jk.2 = (fun y => boxCtr n W C₀ jk.1 jk.2 + y) ''
      {x : Pt m | |Pt.lon x| ≤ n / 1000 ∧ ∀ k, |Pt.tr x k| ≤ W} := by
    ext x
    constructor
    · rintro ⟨hx0, hx⟩
      refine ⟨x - boxCtr n W C₀ jk.1 jk.2, ⟨?_, fun k => ?_⟩, by abel_nf⟩
      · rw [Pt.lon_sub]; simpa [boxCtr] using hx0
      · rw [Pt.tr_sub]; simpa [boxCtr, transverseIntegerPoint] using hx k
    · rintro ⟨y, ⟨hy0, hy⟩, rfl⟩
      refine ⟨?_, fun k => ?_⟩
      · simpa [boxCtr] using hy0
      · simpa [boxCtr, transverseIntegerPoint] using hy k
  rw [hS, image_image]
  rfl

lemma plusPt_add (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (n W C₀ : ℝ) (jk : ℕ × (Fin m → ℤ)) :
    plusPt g n W C₀ jk.1 jk.2 + (n / 16) • -frameDir g = g (boxCtr n W C₀ jk.1 jk.2) := by
  rw [plusPt, frame_add, frameDir, map_smul, smul_neg]; abel

lemma minusPt_add (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (n W C₀ : ℝ) (jk : ℕ × (Fin m → ℤ)) :
    minusPt g n W C₀ jk.1 jk.2 + (n / 16) • frameDir g = g (boxCtr n W C₀ jk.1 jk.2) := by
  rw [minusPt, sub_eq_add_neg, frame_add, frameDir, map_neg, map_smul]; abel

/-- The points of the box `(j, k)` are within `√m W` of the line through `x₊` along `e`. -/
lemma infDist_line_plus_le (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n W C₀ : ℝ} (hW : 0 ≤ W)
    (jk : ℕ × (Fin m → ℤ)) {z : Pt m} (hz : z ∈ g '' boxSet n W C₀ jk.1 jk.2) :
    infDist z (range fun s : ℝ => plusPt g n W C₀ jk.1 jk.2 + s • -frameDir g) ≤
      Real.sqrt m * W := by
  obtain ⟨ζ, hζ, rfl⟩ := hz
  set s₀ := boxLon n C₀ jk.1 + n / 16 - Pt.lon ζ
  have hpt : plusPt g n W C₀ jk.1 jk.2 + s₀ • -frameDir g =
      g (Pt.mk (Pt.lon ζ) (W • transverseIntegerPoint jk.2)) := by
    rw [plusPt, frameDir, smul_neg, ← map_smul, ← map_neg, ← frame_add]
    congr 1
    refine Profiles.pt_ext ?_ ?_
    · simp [boxCtr, s₀]
    · simp [boxCtr]
  refine (infDist_le_dist_of_mem (mem_range_self (f := fun s : ℝ =>
    plusPt g n W C₀ jk.1 jk.2 + s • -frameDir g) s₀)).trans ?_
  rw [hpt, dist_frame]
  have : ζ - Pt.mk (Pt.lon ζ) (W • transverseIntegerPoint jk.2) =
      Pt.mk 0 (Pt.tr ζ - W • transverseIntegerPoint jk.2) :=
    Profiles.pt_ext (by simp) (by simp)
  rw [this]
  have h := Pt.lon_tr_norm_le (Pt.mk 0 (Pt.tr ζ - W • transverseIntegerPoint jk.2) : Pt m)
  rw [Pt.lon_mk, Pt.tr_mk, abs_zero, zero_add] at h
  exact h.trans (norm_tr_sub_kvec_le hW hζ)

/-- The points of the box `(j, k)` are within `√m W` of the line through `x₋` along `e`. -/
lemma infDist_line_minus_le (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n W C₀ : ℝ} (hW : 0 ≤ W)
    (jk : ℕ × (Fin m → ℤ)) {z : Pt m} (hz : z ∈ g '' boxSet n W C₀ jk.1 jk.2) :
    infDist z (range fun s : ℝ => minusPt g n W C₀ jk.1 jk.2 + s • frameDir g) ≤
      Real.sqrt m * W := by
  obtain ⟨ζ, hζ, rfl⟩ := hz
  set s₀ := Pt.lon ζ - boxLon n C₀ jk.1 + n / 16
  have hpt : minusPt g n W C₀ jk.1 jk.2 + s₀ • frameDir g =
      g (Pt.mk (Pt.lon ζ) (W • transverseIntegerPoint jk.2)) := by
    rw [minusPt, frameDir, ← map_smul, ← frame_add]
    congr 1
    refine Profiles.pt_ext ?_ ?_
    · simp [boxCtr, s₀]
    · simp [boxCtr]
  refine (infDist_le_dist_of_mem (mem_range_self (f := fun s : ℝ =>
    minusPt g n W C₀ jk.1 jk.2 + s • frameDir g) s₀)).trans ?_
  rw [hpt, dist_frame]
  have : ζ - Pt.mk (Pt.lon ζ) (W • transverseIntegerPoint jk.2) =
      Pt.mk 0 (Pt.tr ζ - W • transverseIntegerPoint jk.2) :=
    Profiles.pt_ext (by simp) (by simp)
  rw [this]
  have h := Pt.lon_tr_norm_le (Pt.mk 0 (Pt.tr ζ - W • transverseIntegerPoint jk.2) : Pt m)
  rw [Pt.lon_mk, Pt.tr_mk, abs_zero, zero_add] at h
  exact h.trans (norm_tr_sub_kvec_le hW hζ)

end IsotropicVariance.Paper.Proofs.Localization
