/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import IsotropicVariance.Infra.Subadditive.HN

/-!
# Proof of `IsotropicVariance.Cited.hn_lemma4_2`

Proves `IsotropicVariance.Providers.Cited.hn_lemma4_2`, [HN, Lemma 4.2, p. 611], with exactly
the type of the theorem `IsotropicVariance.Cited.hn_lemma4_2` stated in
`IsotropicVariance.Statements.Cited.HnLemma42`. The statement module proves its theorem from this one
and is not imported here.
-/

@[expose] public section

open Filter
open scoped Topology

namespace IsotropicVariance.Providers

/-- [HN, Lemma 4.2, p. 611], with `ψ` a number below `2` such that `g(2L) ≤ ψ g(L)` for all large
`L`, and the doubling inequality of `a` for all large `L`. -/
theorem Cited.hn_lemma4_2 (a g : ℝ → ℝ) (ν : ℝ) (hg : ∀ L, 0 < L → 0 ≤ g L)
    (ha : Tendsto (fun L => a L / L) atTop (𝓝 ν))
    (hgo : Tendsto (fun L => g L / L) atTop (𝓝 0))
    (hdouble : ∀ᶠ L in atTop, 2 * a L - g L ≤ a (2 * L))
    (ψ : ℝ) (hψ : ψ < 2) (hψg : ∀ᶠ L in atTop, g (2 * L) ≤ ψ * g L)
    (c : ℝ) (hc : 1 / (2 - ψ) < c) :
    ∀ᶠ L in atTop, a L ≤ ν * L + c * g L :=
  Infra.Subadditive.hn_lemma4_2 a g ν hg ha hgo hdouble ψ hψ hψg c hc

end IsotropicVariance.Providers
