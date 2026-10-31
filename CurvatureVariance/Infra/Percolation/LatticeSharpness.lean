/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Lattice
public import CurvatureVariance.Infra.Percolation.Sharpness
public import CurvatureVariance.Statements.Percolation.BondCriticalProb

/-!
# Sharpness of the phase transition on `ℤ^d`

The general theorems of `CurvatureVariance.Infra.Percolation.Sharpness` applied to
`latticeGraph m` (locally finite, connected, vertex-transitive by translations, of degree
`2d = 2(m + 1)`; `CurvatureVariance.Infra.Percolation.Lattice`), with the root `0`. They prove the
percolation statements in the namespace `CurvatureVariance` with exactly their types, so that
those statements follow by `exact`:

* `bondCriticalProb_bounds`: `1/(2d) ≤ p_c(d) ≤ 1` (`CurvatureVariance.bondCriticalProb_bounds`);
* `measure_reachable_sphere_le`: **[Duminil-Copin and Tassion, Theorem 1.1(1)] on `ℤ^d`**, for
  `p < p_c`, `P_p[0 ↔ ∂Λ_n] ≤ e^{-cn}` for every `n ≥ 1`, with `∂Λ_n = {x : ‖x‖_∞ = n}`
  (`CurvatureVariance.measure_reachable_sphere_le`);
* `bondCriticalProb_pos`: `0 < p_c(d)` (`CurvatureVariance.bondCriticalProb_pos`).

`latticeSupNorm` (in `CurvatureVariance.Infra.Percolation.Lattice`) has verbatim the body of the
definition `CurvatureVariance.supNorm`, so the statements below are definitionally those in
`CurvatureVariance`. The graph distance of the general theorem is converted to the `ℓ^∞` norm by
`latticeSupNorm_le_dist`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

/-! ### The cited statements -/

/-- **Bounds on `p_c(d)`** (`CurvatureVariance.bondCriticalProb_bounds`): `1/(2d) ≤ p_c(d) ≤ 1`,
from `φ_p({0}) = 2dp` ([Duminil-Copin and Tassion, Remark 4]) and `p̃_c = p_c`. -/
theorem bondCriticalProb_bounds (m : ℕ) :
    (2 * ((m : ℝ) + 1))⁻¹ ≤ bondCriticalProb m ∧ bondCriticalProb m ≤ 1 := by
  have h := inv_degree_le_criticalProb (G := latticeGraph m) (o := 0) exists_latticeShift_eq
    (latticeGraph_connected m)
  rw [degree_latticeGraph] at h
  have hcast : ((2 * (m + 1) : ℕ) : ℝ) = 2 * ((m : ℝ) + 1) := by push_cast; ring
  rw [hcast] at h
  exact ⟨h, (criticalProb_mem_Icc (latticeGraph m) 0).2⟩

/-- **`p_c(d) > 0`** (`CurvatureVariance.bondCriticalProb_pos`). -/
theorem bondCriticalProb_pos {m : ℕ} (_hm : 1 ≤ m) : 0 < bondCriticalProb m :=
  lt_of_lt_of_le (by positivity) (bondCriticalProb_bounds m).1

/-- **[Duminil-Copin and Tassion, Theorem 1.1(1)] on `ℤ^d`**
(`CurvatureVariance.measure_reachable_sphere_le`): for `p < p_c`, there is `c > 0` such that
`P_p[0 ↔ ∂Λ_n] ≤ e^{-cn}` for every `n ≥ 1`, where `∂Λ_n = {x : ‖x‖_∞ = n}`. -/
theorem measure_reachable_sphere_le {m : ℕ} (_hm : 1 ≤ m) (p : unitInterval)
    (hp : (p : ℝ) < bondCriticalProb m) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      setBernoulli (Set.univ : Set (Edge m)) p
          {S | ∃ x : Vertex m, latticeSupNorm x = n ∧
            (CurvatureVariance.openGraph m S).Reachable 0 x} ≤
        ENNReal.ofReal (Real.exp (-(c * n))) := by
  obtain ⟨c, hc, h⟩ := exists_armProb_le_exp (G := latticeGraph m) (o := 0)
    exists_latticeShift_eq (latticeGraph_connected m) hp
  refine ⟨c, hc, fun n hn => (measure_mono ?_).trans (h n hn)⟩
  rintro S ⟨x, hx, hr⟩
  exact ⟨x, hx ▸ latticeSupNorm_le_dist x, hr⟩

end CurvatureVariance.Infra.Percolation
