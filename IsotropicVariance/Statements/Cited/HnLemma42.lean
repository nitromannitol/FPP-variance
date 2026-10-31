/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
import IsotropicVariance.Providers.CitedHnLemma42

/-!
# `IsotropicVariance.Cited.hn_lemma4_2`

One declaration of the statements of this formalization (`IsotropicVariance.Statements`): the
definitions, the results cited from the literature and the main theorems, one per file.

This file states a result from the literature, in the form the paper uses; its proof is
`IsotropicVariance.Providers.Cited.hn_lemma4_2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace IsotropicVariance
namespace Cited

/-- **[HN, Lemma 4.2]** (p. 611, used in the proof of Lemma `lem:classical`). Let `a : ℝ⁺ → ℝ` and
`g : ℝ⁺ → ℝ⁺` satisfy `a(L)/L → ν ∈ ℝ`, `g(L)/L → 0` as `L → ∞`, `a(2L) ≥ 2a(L) − g(L)` and
`ψ ≡ limsup_{L→∞} g(2L)/g(L) < 2`. Then, for any `c > 1/(2 − ψ)`, `a(L) ≤ νL + c g(L)` for all
large `L`.

HN's `ℝ⁺` contains `0` (p. 598). The argument is read as `0 < L`, which only weakens `hg`, and the
values of `g` as `0 ≤ g L`, so `g` may vanish. The hypothesis on `ψ` is read as a number `ψ < 2`
with `g(2L) ≤ ψ g(L)` for all large `L`, which needs no division by `g(L)`. It is implied by HN's
hypothesis: if `ψ₀` is HN's limsup and `c > 1/(2 − ψ₀)`, take `ψ` between `ψ₀` and `2` with
`c > 1/(2 − ψ)`. The doubling inequality is required only for large `L`, as [HN, Lemma 4.1]
gives it and HN's proof uses it. -/
theorem hn_lemma4_2 (a g : ℝ → ℝ) (ν : ℝ) (hg : ∀ L, 0 < L → 0 ≤ g L)
    (ha : Tendsto (fun L => a L / L) atTop (𝓝 ν))
    (hgo : Tendsto (fun L => g L / L) atTop (𝓝 0))
    (hdouble : ∀ᶠ L in atTop, 2 * a L - g L ≤ a (2 * L))
    (ψ : ℝ) (hψ : ψ < 2) (hψg : ∀ᶠ L in atTop, g (2 * L) ≤ ψ * g L)
    (c : ℝ) (hc : 1 / (2 - ψ) < c) :
    ∀ᶠ L in atTop, a L ≤ ν * L + c * g L :=
  by exact IsotropicVariance.Providers.Cited.hn_lemma4_2 a g ν hg ha hgo hdouble ψ hψ hψg c hc

end Cited
end IsotropicVariance
