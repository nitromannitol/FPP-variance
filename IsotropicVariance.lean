/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

/-!
# IsotropicVariance

Lean formalization of the continuum paper of Armstrong and Bou-Rabee, "Fluctuation bounds for
rotationally invariant first-passage percolation". Take a density determined in each unit ball by
Gaussian white noise or a homogeneous Poisson process on `ℝ^d`, `d ≥ 2`, with values between two
positive constants and commuting with rigid motions. Then the time constant
`μ = lim_{t→∞} t⁻¹ E[T(0, t e₁)]` exists, and there are `ε > 0` and `C < ∞` such that
`E[exp(|T(0, x) − μ|x|| / (C |x|^{(1−ε)/2}))] ≤ 2` for every `|x| ≥ 1`. In particular
`Var T(0, x) ≤ |x|^{1-ε}` for `|x|` large, with a smaller `ε`.

## Main results

* `IsotropicVariance.lintegral_exp_passageTime_le`: the main theorem (Theorem `thm:main`), for the
  density `ψ(χ ∗ W)` of Gaussian white noise `W`, a smooth radial function `χ` supported in the
  closed unit ball and a continuous function `ψ` with values between two positive constants.
* `IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise` and
  `IsotropicVariance.lintegral_exp_passageTime_le_of_isPoissonProcess`: the theorem on local
  densities (Theorem `thm:general`), for every density satisfying Assumption `ass:local` over
  Gaussian white noise or over a homogeneous Poisson process.
* The variance bound that the paper derives after Theorem `thm:main`, for the same three sets of
  hypotheses: `Var T(0, t e₁) ≤ t^{1-ε}` for `t` large (`IsotropicVariance.variance_passageTime_le`,
  `…_of_isWhiteNoise`, `…_of_isPoissonProcess`), and `Var T(0, x) ≤ |x|^{1-ε}` for `|x|` large
  (`IsotropicVariance.variance_passageTime_le_norm`, `…_norm_of_isWhiteNoise`,
  `…_norm_of_isPoissonProcess`).

## Organization

* `IsotropicVariance.Statements`: the statements, one declaration per module. These are the definitions
  they use (points and rigid motions, rectifiable curves and the passage time, noise configurations,
  white noise and Poisson processes, local densities, the convolution density), the main theorems
  and the variance bounds, the results cited from the literature, and the existence of white noise
  and of Poisson processes.
* `IsotropicVariance.Providers`: one module for each theorem stated in `IsotropicVariance.Statements`,
  proving it with exactly its type.
* `IsotropicVariance.Paper.Defs`: the objects of the paper (the setting of a density over a noise,
  slabs and slab passage times, the slab minimum and its minimizing points, the scales `Q_s` and
  `W_s`, blocks, couplings and labels).
* `IsotropicVariance.Paper.Contracts`: the paper's intermediate results, stated as `Prop`s.
* `IsotropicVariance.Paper.Proofs`: their proofs, one directory for each result.
* `IsotropicVariance.Paper.Closing`: the assembly of the main theorems from these results.
* `IsotropicVariance.Infra`: general mathematics that the proofs use (white noise and Poisson
  processes and their information σ-algebras, rectifiable curves, concentration, entropy and
  Efron–Stein inequalities, the `O_s` calculus, measurable selection, subadditivity).
-/
