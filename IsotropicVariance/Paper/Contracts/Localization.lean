/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum
public import IsotropicVariance.Paper.Contracts.Slab
import IsotropicVariance.Infra.Os.Basic

/-!
# Statements of Section `sec:localization`, part 1: transverse fluctuations and the modulus

* `LocalizationStatement`: Lemma `lem:localization`, equation `eq:localization`.
* `OverviewTransverseStatement`: display `eq:transverse` of the overview, the same bound for the
  cubes of Step 1 with `s = n`, that is, with `|y| ≤ n`.
* `ModulusStatement`: Lemma `lem:modulus`, equation `eq:modulus`.

The section's standing data (the start of Section `sec:localization`): `eq:premise` and
`eq:regime`, a length `n ∈ [β₁N, N]`, and cubes `I`, `I'` and a slab `S` as in equation
`eq:cubepair` with `s = n` and `|y| ≤ n/2`, which is `p.IsAdmissible n (W K A n) (1 / 2)`, with
`I = p.first`, `I' = p.second`, `S = p.slab`. The lower multiple is `c₁ ≤ 1`: for `c₁ > 1` the
range of `n` is empty.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Contracts

/-- The largest distance from `[u, v]`, over `u ∈ I`, `v ∈ I'`, of the points of the 1-optimal
curves for `(σ, S)` from `u` to `v` (equation `eq:localization`). -/
noncomputable def maxSegmentDeviation {m : ℕ} (σ : Pt m → ℝ) (S I I' : Set (Pt m)) : ℝ :=
  ⨆ (u : I) (v : I') (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal σ S u v γ})
    (t : Icc (0 : ℝ) 1), infDist (γ.1.toFun t) (segment ℝ (u : Pt m) (v : Pt m))

/-- **Lemma `lem:localization`, equation `eq:localization`**: if `N`
is large, depending only on `K` and the lower multiple `c₁`, then for every `c₁N ≤ n ≤ N` and all
cubes as in the section's standing data,
`(nQ_n)^{−1/2} sup_{u ∈ I, v ∈ I'} sup_{π ∈ Π_{T_S}(u, v)} sup_{x ∈ π} dist(x, [u, v]) ≤ O_2(C)`.
Here `(nQ_n)^{1/2}` is `W K A n`, and `Π_{T_S}(u, v)` is the set of the curves from `u` to `v` in
`S` that are 1-optimal for the density `ρ_S`, which is `p.slab.density b (X.ρ ω)`, with any
deterministic upper bound `b` in place of `sup ρ`. -/
def LocalizationStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 → ∀ K : ℕ,
      ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ n : ℝ, c₁ * N ≤ n → n ≤ N →
        ∀ p : CubePair m, p.IsAdmissible n (W K A n) (1 / 2) →
          Cited.IsOs X.P 2 C (fun ω => (W K A n)⁻¹ *
            maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first p.second)

/-- **Display `eq:transverse` of the overview** (Step 2 of Section `ssec:overview`, for the cubes
of its Step 1 with `s = n`): the statement of Lemma `lem:localization` for cubes whose centers
differ by `ne₁` plus a vector of length at most `n`, which is `p.IsAdmissible n (W K A n) 1`.
Section `sec:localization` has `|y| ≤ n/2`. Since `W² = nQ_n`, the bound
`W⁻¹ sup dist(x, [u, v]) ≤ O_2(C)` is `E[exp(sup dist(x, [u, v])²/(C²nQ_n))] ≤ 2`, the display
with `C²` for its constant. -/
def OverviewTransverseStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 → ∀ K : ℕ,
      ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ n : ℝ, c₁ * N ≤ n → n ≤ N →
        ∀ p : CubePair m, p.IsAdmissible n (W K A n) 1 →
          Cited.IsOs X.P 2 C (fun ω => (W K A n)⁻¹ *
            maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first p.second)

/-- The modulus quantity of equation `eq:modulus` for a passage time `D`: the supremum over
`u, u₁ ∈ I`, `v, v₁ ∈ I'` with `|u − u₁|, |v − v₁| ≤ hW` of
`|D(u, v) − D(u₁, v₁) − |v − u| + |v₁ − u₁||` (the paper writes `ũ`, `ṽ` for `u₁`, `v₁`). -/
noncomputable def modulusSup {m : ℕ} (D : Pt m → Pt m → ℝ) (I I' : Set (Pt m)) (r : ℝ) : ℝ :=
  ⨆ (u : I) (u₁ : I) (v : I') (v₁ : I') (_ : dist (u : Pt m) u₁ ≤ r ∧ dist (v : Pt m) v₁ ≤ r),
    |D u v - D u₁ v₁ - dist (u : Pt m) v + dist (u₁ : Pt m) v₁|

/-- **Lemma `lem:modulus`, equation `eq:modulus`**: for every `η > 0`
there is `h > 0`, depending only on `η`, the law of the density and `d`, such that, if `N` is large,
depending only on `K`, `η` and the lower multiple `c₁`, then for every `c₁N ≤ n ≤ N` and all cubes
as in the section's standing data,
`E[sup |T_S(u, v) − T_S(ũ, ṽ) − |v − u| + |ṽ − ũ||^{8d}]^{1/(8d)} ≤ ηQ_n`, the supremum over
`u, ũ ∈ I`, `v, ṽ ∈ I'` with `|u − ũ|, |v − ṽ| ≤ h(nQ_n)^{1/2}`. The order of the quantifiers
carries these dependences: `h` is chosen before `c₁` and `K`. The bound `b` is any deterministic
upper bound of the density. -/
def ModulusStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∀ η : ℝ, 0 < η →
      ∃ h : ℝ, 0 < h ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 → ∀ K : ℕ, ∃ N₀ : ℝ,
        ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ n : ℝ, c₁ * N ≤ n → n ≤ N →
          ∀ p : CubePair m, p.IsAdmissible n (W K A n) (1 / 2) →
            eLpNorm (fun ω => modulusSup (X.slabTime b p.slab ω) p.first p.second
                (h * W K A n)) (8 * (m + 1) : ℝ≥0∞) X.P ≤ ENNReal.ofReal (η * Q K A n)

end IsotropicVariance.Paper.Contracts
