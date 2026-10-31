/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.Tubes.Geometry
import CurvatureVariance.Paper.Proofs.Responses.WidthBridge
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The deterministic tube property

This proves the tube property of Section `sec:gain` for every configuration: the fine cubes
within `R_i(j,k)` of the segment `[j,k]` contain those within distance two of every geodesic. A
geodesic vertex contributes to the supremum defining the localization radius; its edge midpoint
is within one half of that vertex. The normalized shear and row/fine rounding bounds then place
every fine index within distance two of the edge's fine index inside the index tube. No
probabilistic estimate is used.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Tubes

variable {m : ℕ}

/-- A nearest-neighbor edge midpoint lies one half from either endpoint. -/
theorem norm_edgeMid_sub_left {a b : Vertex m} (hab : (latticeGraph m).Adj a b) :
    ‖edgeMid s(a, b) - point a‖ = (1 / 2 : ℝ) := by
  have hid : edgeMid s(a, b) - point a = (1 / 2 : ℝ) • (point b - point a) := by
    change (1 / 2 : ℝ) • (point a + point b) - point a = _
    module
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    Infra.FPP.norm_point_sub_point_of_adj hab.symm, mul_one]

/-- Nearby indices of any edge of a walk obey the chord-distance bound at an endpoint. -/
theorem infDist_near_edge_le (n : ℕ) {w : ℕ} (hw : 1 ≤ w)
    {t : EuclideanSpace ℝ (Fin m)} {T : ℝ} (ht : ‖t‖ ≤ T) (i i' : ℤ) (j k : Fin m → ℤ)
    {u v : Vertex m} (hu : u ∈ rowCube n w t i j) (hv : v ∈ rowCube n w t i' k)
    (γ : (latticeGraph m).Walk u v) {a b : Vertex m} (he : s(a, b) ∈ γ.edges)
    (j' : Fin m → ℤ) (hnear : ‖transversePoint (j' - fineIndex w t (edgeMid s(a, b)))‖ ≤ 2) :
    Metric.infDist (transversePoint j') (segment ℝ (transversePoint j) (transversePoint k)) ≤
      (2 * Real.sqrt m + 3 + T) +
        (1 + T) * (Metric.infDist (point a) (segment ℝ (point u) (point v)) / w) := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hdist : dist (transversePoint j') (transversePoint (fineIndex w t (edgeMid s(a, b)))) ≤ 2 := by
    simpa only [Infra.FPP.transversePoint_sub, dist_eq_norm] using hnear
  have hmid : dist (edgeMid s(a, b)) (point a) = (1 / 2 : ℝ) := by
    rw [dist_eq_norm, norm_edgeMid_sub_left (γ.adj_of_mem_edges he)]
  have hm := Metric.infDist_le_infDist_add_dist (x := edgeMid s(a, b)) (y := point a)
    (s := segment ℝ (point u) (point v))
  rw [hmid] at hm
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ (1 + T) / (w : ℝ) by positivity)
  have hf := infDist_index_le n hw ht i i' j k hu hv (edgeMid s(a, b))
  have hj := Metric.infDist_le_infDist_add_dist (x := transversePoint j')
    (y := transversePoint (fineIndex w t (edgeMid s(a, b))))
    (s := segment ℝ (transversePoint j) (transversePoint k))
  have hiw : (1 : ℝ) / w ≤ 1 := (div_le_one hw0).2 hw1
  have hid : ((1 + T) / (w : ℝ)) *
      (Metric.infDist (point a) (segment ℝ (point u) (point v)) + 1 / 2) =
      (1 + T) * (Metric.infDist (point a) (segment ℝ (point u) (point v)) / w) + ((1 + T) / 2) * (1 / w) := by ring
  rw [hid] at hm'
  have hiw' := mul_le_mul_of_nonneg_left hiw (show 0 ≤ (1 + T) / 2 by positivity)
  linarith only [hdist, hm', hf, hj, hiw', hT]

end CurvatureVariance.Paper.Tubes

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper.Tubes

/-- The tube property of Section `sec:gain`, with constant `2√m + 3 + T` for slopes
of norm at most `T`.
It holds deterministically for every configuration, without any statement of Sections `sec:cubes`
and `sec:localization`. -/
theorem tubeStatement_holds (m : ℕ) : TubeStatement m := by
  intro T hT
  refine ⟨2 * Real.sqrt m + 3 + T, by positivity, ?_⟩
  intro M K A hA ω n hn t ht i _ j k u hu v hv γ hγ e
  refine Sym2.inductionOn e ?_
  intro a b he j' hnear
  have hw := Responses.one_le_wInt (M := M) (K := K) hA hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hQ : 0 < Q M K A n := mul_pos (lt_of_lt_of_le zero_lt_one hA)
    (Real.rpow_pos_of_pos hn0 _)
  have hW : 0 < W M K A n := Real.sqrt_pos.2 (mul_pos hn0 hQ)
  have hWw : W M K A n ≤ (wInt M K A n : ℝ) := Nat.le_ceil _
  let D : ℝ := Metric.infDist (point a) (segment ℝ (point u) (point v))
  have hD : 0 ≤ D := Metric.infDist_nonneg
  have hdiv : D / (wInt M K A n : ℝ) ≤ D / W M K A n :=
    div_le_div_of_nonneg_left hD hW hWw
  have hreal := infDist_near_edge_le n hw ht ((i : ℤ) - 1) i j k hu hv γ he j' hnear
  have hdev : ENNReal.ofReal D ≤ deviation
      (fun γ => IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ)
      (rowCube n (wInt M K A n) t ((i : ℤ) - 1) j)
      (rowCube n (wInt M K A n) t i k) := by
    apply le_iSup_of_le u
    apply le_iSup_of_le hu
    apply le_iSup_of_le v
    apply le_iSup_of_le hv
    apply le_iSup_of_le γ
    apply le_iSup_of_le hγ
    apply le_iSup_of_le a
    apply le_iSup_of_le (γ.fst_mem_support_of_mem_edges he)
    exact le_rfl
  change ENNReal.ofReal (Metric.infDist (transversePoint j')
    (segment ℝ (transversePoint j) (transversePoint k))) ≤ _
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.sqrt m + 3 + T) + (1 + T) * (D / W M K A n)) :=
      ENNReal.ofReal_le_ofReal (by nlinarith only [hreal, hdiv, hT])
    _ = ENNReal.ofReal (2 * Real.sqrt m + 3 + T) +
        ENNReal.ofReal (1 + T) * (ENNReal.ofReal D / ENNReal.ofReal (W M K A n)) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 + T),
        ENNReal.ofReal_div_of_pos hW]
    _ ≤ slabRadius M K A (2 * Real.sqrt m + 3 + T) ω n t i j k := by
      unfold slabRadius locRadiusSlab
      have hCd : ENNReal.ofReal (1 + T) ≤ ENNReal.ofReal (2 * Real.sqrt m + 3 + T) :=
        ENNReal.ofReal_le_ofReal (by nlinarith only [Real.sqrt_nonneg (m : ℝ)])
      calc
        _ ≤ ENNReal.ofReal (2 * Real.sqrt m + 3 + T) +
            ENNReal.ofReal (2 * Real.sqrt m + 3 + T) * (_ / ENNReal.ofReal (W M K A n)) :=
          add_le_add le_rfl (mul_le_mul' hCd (ENNReal.div_le_div_right hdev _))
        _ = ENNReal.ofReal (2 * Real.sqrt m + 3 + T) * (1 +
            _ / ENNReal.ofReal (W M K A n)) := by rw [mul_add, mul_one]
        _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_left bot_le)

end CurvatureVariance.Paper.Contracts
