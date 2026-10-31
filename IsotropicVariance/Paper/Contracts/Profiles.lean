/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Minimum

/-!
# Statements of Section `sec:exponential`

The order of the quantifiers makes explicit the dependences that the paper states in words: the
setting `X` (normalized, `μ = 1`), the slab upper bound `b`, the regime constant `C_*` and the upper
multiple are given first; then the constant `C` (depending on them, never on `K`, `A`, `N`); then
the lower multiple and `K`; then the threshold `N₀`; then every `A ≥ 1` and `N ≥ N₀` satisfying the
standing hypotheses `eq:premise` and `eq:regime` (`Standing`). The multiples `c₁`, `c₂` are the
numbers `β₁`, `β₂` of the start of Section `sec:exponential`. Since `N₀` is chosen after `c₁` and
`K`, a use may take `c₁` depending on `K`, as the paper does (in the proof of Lemma `lem:blocks`).
Lemma `lem:tree` assumes `eq:premise` alone, so it has neither `b`, nor `C_*`, nor a threshold.

* `TreeStatement`: Lemma `lem:tree`, equation `eq:tree`.
* `ProfilesStatement`: Proposition `prop:profiles`, equation `eq:profiles`.
* `ProfilesShortStatement`: the same for `s ≤ N/4`, the first part of the paper's proof.
* `RowEnergyStatement`: Lemma `lem:rowenergy`, equation `eq:rowenergy`.
* `ParentStatement`: Lemma `lem:parent`, equation `eq:parent`.
* `ChainSumStatement`: equation `eq:chainsum`, stated between `lem:rowenergy` and `lem:parent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology RealInnerProductSpace

universe u

namespace IsotropicVariance.Paper.Contracts

/-- **Lemma `lem:tree`, equation `eq:tree`**, in its translated and
rotated form, the second sentence of the lemma, which contains the first (`x = 0`, `e = e₁`):
assume `eq:premise` for an integer `K ≥ 10`, `A ≥ 1` and a length `N ≥ 2`. For `16 ≤ t ≤ N/2`,
every point `x`, unit vector `e`, and rectangular box `B` centered at `x + te`, of diameter at most
`t/8`, within distance `16(d tQ_t)^{1/2}` of the line `x + ℝe`,
`sup_{z ∈ B} {T(x, z) − (z − x) · e} ≤ O_1(C Q_t)`. "Within distance" means that every point of
`B` is within that distance of the line. The constant `C` depends on the setting only: neither on
`K`, `A` nor `N`. There is no threshold on `N` and no regime hypothesis. -/
def TreeStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∃ C : ℝ, 0 < C ∧
    ∀ (K : ℕ) (A N : ℝ), 10 ≤ K → 1 ≤ A → 2 ≤ N → Premise X K A N →
      ∀ t : ℝ, 16 ≤ t → t ≤ N / 2 →
        ∀ (x e : Pt m), ‖e‖ = 1 → ∀ B : Set (Pt m), IsRectBox B (x + t • e) →
          (∀ z ∈ B, ∀ z' ∈ B, dist z z' ≤ t / 8) →
          (∀ z ∈ B, infDist z (range fun r : ℝ => x + r • e) ≤
            16 * Real.sqrt (m + 1) * W K A t) →
            Cited.IsOs X.P 1 (C * Q K A t)
              (fun ω => ⨆ z : B, (X.passTime ω x z - ⟪(z : Pt m) - x, e⟫))

/-- **Proposition `prop:profiles`, equation `eq:profiles`**: if `N` is
large, depending only on `K` and `c₁ = β₁`, then for every `s ∈ [c₁N, N]` and all cubes `I`, `I'` as
in equation `eq:cubepair` (of sides at most `4W_s`) with `|y| ≤ s`,
`sup_{u ∈ I, v ∈ I'} |T_P(u, v) − |v − u|| ≤ O_1(C Q_s)`, both for `P = ℝ^d` and for `P = S`. -/
def ProfilesStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ s : ℝ, c₁ * N ≤ s → s ≤ N →
        ∀ p : CubePair m, p.IsAdmissible s (W K A s) 1 →
          Cited.IsOs X.P 1 (C * Q K A s) (fun ω =>
              ⨆ (u : p.first) (v : p.second),
                |X.passTime ω u v - dist (u : Pt m) (v : Pt m)|) ∧
            Cited.IsOs X.P 1 (C * Q K A s) (fun ω =>
              ⨆ (u : p.first) (v : p.second),
                |X.slabTime b p.slab ω u v - dist (u : Pt m) (v : Pt m)|)

/-- **The first part of the proof of Proposition `prop:profiles`**:
equation `eq:profiles` for `s ≤ N/4`. The paper proves Proposition `prop:profiles` for `s ≤ N/4`,
then Lemmas `lem:rowenergy` and `lem:parent` from that part, and then `N/4 < s ≤ N` (the second
part of the proof). This statement carries that order, and so breaks the cycle
`prop:profiles` → `lem:rowenergy` → `lem:parent` → `prop:profiles`. Internal: it is not a statement
of the paper, and it differs from `ProfilesStatement` only in the upper end of the range of `s`. -/
def ProfilesShortStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ s : ℝ, c₁ * N ≤ s → s ≤ N / 4 →
        ∀ p : CubePair m, p.IsAdmissible s (W K A s) 1 →
          Cited.IsOs X.P 1 (C * Q K A s) (fun ω =>
              ⨆ (u : p.first) (v : p.second),
                |X.passTime ω u v - dist (u : Pt m) (v : Pt m)|) ∧
            Cited.IsOs X.P 1 (C * Q K A s) (fun ω =>
              ⨆ (u : p.first) (v : p.second),
                |X.slabTime b p.slab ω u v - dist (u : Pt m) (v : Pt m)|)

/-- **Lemma `lem:rowenergy`, equation `eq:rowenergy`**: for every
positive integer `M` and every `c₁N ≤ s ≤ N/4`,
`|F − Ms| + s⁻¹ Σ_{i=1}^M |x_i − x_{i−1} − s e₁|² ≤ C M Q_s + O_1(C Q_s)`, where
`x_0, …, x_M` are the lexicographically least points attaining the minimum in equation `eq:F`
(`lexMinimizer`, the convention before Lemma `lem:rowenergy`), and `C` does not depend on `M`. One
constant for the two terms: the larger of two constants serves for both, so this is the same
statement. -/
def RowEnergyStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ (M : ℕ) (s : ℝ), 1 ≤ M →
        c₁ * N ≤ s → s ≤ N / 4 →
          Cited.IsOs X.P 1 (C * Q K A s) (fun ω =>
            |X.F b M s 0 ω - M * s| +
              s⁻¹ * ∑ i : Fin M,
                ‖lexMinimizer b (X.ρ ω) M s 0 i.succ - lexMinimizer b (X.ρ ω) M s 0 i.castSucc -
                  s • e₁‖ ^ 2 -
              C * M * Q K A s)

/-- **Lemma `lem:parent`, equation `eq:parent`**: for every
`t ∈ [c₁N, c₂N]`, `|T_t − t| ≤ C(β₂) Q_t + O_1(Q_t/100)`, the constant depending on the upper
multiple `c₂ = β₂`. The Lean variable is `ℓ`. -/
def ParentStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ Cstar : ℝ, 0 < Cstar →
    ∀ c₂ : ℝ, 0 < c₂ → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ ℓ : ℝ, c₁ * N ≤ ℓ → ℓ ≤ c₂ * N →
        Cited.IsOs X.P 1 (Q K A ℓ / 100) (fun ω => |X.TRV ℓ ω - ℓ| - C * Q K A ℓ)

/-- **Equation `eq:chainsum`**: for `s` and `N` as in Lemma
`lem:rowenergy`, that is, for every positive integer `M` and every `c₁N ≤ s ≤ N/4`, let
`Z_1, …, Z_M` be independent random arrays of nonnegative random variables with
`E[(Z_i(j, k) − |j − k|²)₊^{4d}] ≤ 1` for all `i, j, k`. With `k_i` the lexicographically greatest
index with `x_i ∈ I_i(k_i)`, `E[Σ_{i=1}^M Z_i(x_{i−1}, x_i)] ≤ CM`, with `C` independent of `M`.

Readings:
* `Z_i(x_{i−1}, x_i)` is `Z_i(k_{i−1}, k_i)`, and `k_i` is `X.J` (the floor is the
  lexicographically greatest index). Lean slabs are 0-based, so the term of the slab `i : Fin M` is
  `Z i ω (J i.castSucc) (J i.succ)`.
* The arrays may be read off a larger probability space: `(Ω', P')`, with a measure-preserving map
  `π : Ω' → X.Ω`, the chain being that of `π ω`. The reason is Lemma `lem:blocks`: its arrays `Y_i`
  live on the joint law `X.blockResampling` of the noise and of its resamplings, and the points
  `x_i` are those of the noise. Independence and the moment bound are under `P'`. The paper is the
  instance `π = id`.
* The arrays take values in `[0, ∞]`, so that the subtraction, truncated at zero, is the positive
  part, and the moment bound, the only integrability hypothesis, is an inequality in `[0, ∞]`. Two
  of the four uses have arrays in `[0, ∞]`: `Y_i` is a sum over infinitely many blocks, finite only
  almost surely (Lemmas `lem:blocks` and `lem:residual`). A real array `Z ≥ 0` is the instance
  `ENNReal.ofReal ∘ Z`, as in the other two uses, so this form contains the paper's, and the
  moment bound makes every entry finite almost surely. -/
def ChainSumStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → ∀ K : ℕ, ∃ N₀ : ℝ,
      ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ (M : ℕ) (s : ℝ), 1 ≤ M →
        c₁ * N ≤ s → s ≤ N / 4 →
          ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
            (π : Ω' → X.Ω), MeasurePreserving π P' X.P →
            ∀ Z : Fin M → Ω' → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞,
              (∀ i j k, Measurable fun ω => Z i ω j k) →
              iIndepFun Z P' →
              (∀ i j k, ∫⁻ ω, (Z i ω j k - ENNReal.ofReal (zNorm (j - k) ^ 2)) ^ (4 * (m + 1))
                ∂P' ≤ 1) →
              ∫⁻ ω, ∑ i : Fin M, Z i ω (X.J b M s (W K A s) 0 (π ω) i.castSucc)
                  (X.J b M s (W K A s) 0 (π ω) i.succ) ∂P' ≤
                ENNReal.ofReal (C * M)

end IsotropicVariance.Paper.Contracts
