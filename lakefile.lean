/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
import Lake

open Lake DSL

package FPPVariance

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

-- Curvature and variance in lattice first-passage percolation.
@[default_target]
lean_lib CurvatureVariance where
  globs := #[.andSubmodules `CurvatureVariance]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Fluctuation bounds for rotationally invariant first-passage percolation.
@[default_target]
lean_lib IsotropicVariance where
  globs := #[.andSubmodules `IsotropicVariance]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- The Mathlib-only comparator challenges and their solutions, one directory per main theorem.
@[default_target]
lean_lib Audit where
  globs := #[.submodules `Audit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
