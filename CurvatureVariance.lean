/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

/-!
# CurvatureVariance

Lean formalization of "Curvature and variance in lattice first-passage percolation" (Armstrong and
Bou-Rabee).

The main theorem is `CurvatureVariance.lintegral_exp_passageTime_le`, Theorem `thm:main` of the
paper. In first-passage percolation on `ℤ^d`, `d ≥ 2`, let the edge weights be independent and
identically distributed, with a law that has an exponential moment and puts mass smaller than the
critical probability `p_c(d)` of bond percolation at zero (Assumption (W)), and let `μ` be the time
constant. A unit vector `ξ` satisfies the curvature assumption (Curv) with the constants
`δ ∈ (0, 1]`, `r > 0`, `M ≥ 0` and `c > 0` (the paper's `Λ` and `λ`) if, on the orthogonal
hyperplane `ξ^⊥`, `μ(ξ + h)` has an expansion with a linear term, a quadratic form at least `c |h|²`
and a remainder at most `M |h|^{2+δ}` for `|h| ≤ r` (`AssumptionCWith`). For all such constants
there are `ε > 0` and `C > 0` such that `E[exp(|T(0, x) - μ(x)| / (C |x|^{(1-ε)/2}))] ≤ 2` for every
unit vector `ξ` satisfying the assumption with these constants and every lattice point `x ≠ 0`
within distance `|x|^{3/4}` of the ray through `ξ`. The exponent and the constant depend only on
`d`, the law and the constants, not on the direction.

The library also proves the variance bound of the paper,
`CurvatureVariance.Paper.Closing.variance_passageTime_le`, and two bounds along a ray. The first,
`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`, is a corollary of the variance
bound: there are `ε > 0` and `n₀`, depending only on `d`, the law and the constants, such that
`Var T(0, ⌊nξ⌋) ≤ n^{1-ε}` for every unit vector `ξ` as above and every integer `n ≥ n₀`, where the
floor is taken coordinatewise in the original lattice coordinates. The second,
`CurvatureVariance.evariance_passageTime_floorVertex_le`, is at one direction and is not a
corollary: it is proved through the same induction. For a nonzero `ξ` and a linear hyperplane `H`
transverse to it, the assumption at `ξ` along `H` with constants that are not fixed in advance
(`AssumptionCAt`) gives the same bound for `n` large, with `ε` and the threshold depending on the
direction.

The library contains:

* the statements of `lintegral_exp_passageTime_le` and of the two bounds along a ray, the
  definitions they use (the lattice, the weights, passage times, the time constant, Assumption (W)
  and the curvature assumption), and the statements of the results that the paper cites from the
  literature, each proved here;
* `CurvatureVariance.Infra`, general infrastructure: the Efron–Stein inequality, entropy and the
  modified Poincaré inequality of Benaïm and Rossignol, the stochastic order `O_s`, penalized sums
  of independent arrays, sharpness of the phase transition in Bernoulli bond percolation, Kesten's
  estimate, and the first-passage results of Auffinger, Damron and Hanson on the time constant,
  concentration, the mean and geodesics;
* `CurvatureVariance.Paper`, the definitions, statements and proofs of the paper, section by
  section, and the assembly of the main theorem.
-/
