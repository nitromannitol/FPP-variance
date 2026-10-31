/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Targets
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Probability.Independence.Basic

/-!
# Contracts of Sections `sec:induction`, `sec:cubes` and `sec:localization`

Scales, cubes, transverse fluctuations and continuity: the statements of Sections `sec:induction`,
`sec:cubes` and `sec:localization` of the lattice paper.

* `ScalesStatement` — equation `eq:scales`.
* `ProfileDifferenceStatement` — equation `eq:profiledifference`.
* `TreeStatement` — Lemma `lem:tree`, equation `eq:tree`.
* `ShortConclusion`, `ProfilesShortStatement`, `ProfilesStatement` — Proposition `prop:profiles`,
  equation `eq:profiles`.
* `ExpArrayStatement` — Lemma `lem:rowenergy`, equation `eq:rowenergy`.
* `ChainSumStatement` — equation `eq:chainsum`.
* `ParentStatement` — Lemma `lem:parent`, equation `eq:parent`.
* `LocalizationStatement` — Lemma `lem:localization`.
* `ModulusStatement` — Lemma `lem:modulus`, equation `eq:modulus`.

The standing hypotheses of these sections are the induction hypothesis, equation `eq:premise`
(`Paper.Premise`), and equation `eq:regime` (`Paper.RangeA`), made explicit hypotheses. The paper's
constant `2C` of `eq:regime` is `Cstar`, for every `Cstar`, which is stronger: the constants may
depend on `Cstar`, and the proof of Proposition `prop:induction` takes one that depends on the
bounds only. By the convention of Section `ssec:notation`, constants and thresholds come after a
`Bounds` record and before the models that fit it, thresholds are independent of `A`, and a
constant the paper makes depend on a parameter comes after exactly that parameter. Where the
paper's constants use `|t₀| ≤ (d−1)^{1/2}`, the Lean's depend on `Bounds.T`.

A bound `sup_{…} Z ≤ O₁(θ)` is written as the existence of one random variable `X ≤ O₁(θ)` with
`Z ≤ X` almost surely for all indices at once, which avoids measurability of the supremum and
implies the paper's bound, since the suprema are countable.

The Lean's cube `transverseCube p c a` is closed, with center `c`; the paper's cube of the same
center and side, half-open, lies in it, so a bound over Lean cubes implies the paper's bound. A
single lattice point is a Lean cube of side `0`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper

variable {m : ℕ}

universe u

/-- **Equation `eq:scales`**: for an integer `N ≥ 2` and `A ≥ 1` with equation `eq:regime`,
`s ≥ N^{1/2}/16` and `|t − t₀| ≤ 3s^{δ/100−1/4}`,
`(sQ_s)^{1/2} / s^{3/4+δ/100} ≤ C N^{−δ/250} (log(2+N))^{1/4}` and
`s |t − t₀|^{2+δ} / Q_s ≤ C s^{−δ/5}`.

Readings. By the convention of Section `ssec:notation`, `C` comes before `K`: it depends on `Cstar`
and the bounds only, and both exponents are bounded uniformly for `K ≥ 10⁴`. The paper has no
threshold: the integer `N ≥ 2` is that of the induction hypothesis, equation `eq:premise`. The
paper quantifies `s` and `t` together; here the first bound has no `t`, which is the same
statement. -/
def ScalesStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, 2 ≤ N → ∀ A : ℝ, 1 ≤ A → RangeA M K A N Cstar →
  ∀ s : ℝ, Real.sqrt N / 16 ≤ s →
    W M K A s / s ^ ((3 : ℝ) / 4 + M.δ / 100) ≤
        C * (N : ℝ) ^ (-M.δ / 250) * Real.log (2 + N) ^ ((1 : ℝ) / 4) ∧
      ∀ t : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ 3 * s ^ (M.δ / 100 - 1 / 4) →
        s * ‖t - M.t₀‖ ^ (2 + M.δ) / Q M K A s ≤ C * s ^ (-M.δ / 5)

/-- **Equation `eq:profiledifference`** (in the proof of Proposition `prop:profiles`): for a pair of
cubes `I, I'` with `P` the slab between their hyperplanes,
`0 ≤ sup_{u ∈ I, v ∈ I'} (T_P(u,v) − T(u,v)) ≤ C log²N + O₁(C)`.

Readings. The constant `C` comes before `b`, as in the paper, and the threshold after `K` and `b`.
The range `N^{1/2} ≤ s ≤ 2N`, `|t − t₀| ≤ (3/2) s^{δ/100−1/4}` contains both ranges of Proposition
`prop:profiles` for `N` large, so one contract covers them. The proof uses Lemma `lem:good`, Lemma
`lem:slabs` and equation `eq:regime`, so the induction hypothesis is not a hypothesis here, which is
stronger. One `X` serves all `u, v`. -/
def ProfileDifferenceStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 1 ≤ b →
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → RangeA M K A N Cstar →
  ∀ s : ℕ, Real.sqrt N ≤ s → (s : ℝ) ≤ 2 * N → ∀ (t : EuclideanSpace ℝ (Fin m))
    (I I' : Set (Vertex m)), IsCubePair M K A s b t I I' →
    ‖t - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
    ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 C X ∧ ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I',
      (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v ∧
      slabTimeReal ω u.1 v.1 u v - passageTimeReal ω u v ≤ C * Real.log N ^ 2 + X ω

/-- **Lemma `lem:tree`**, equation `eq:tree`: let `b ≥ 1`, `s ∈ [N^{1/2}/16, N/2]` real,
`|t − t₀| ≤ (4/5) s^{δ/100−1/4}`, `I` a cube of side at most `b(sQ_s)^{1/2}` with center `ū`, and
`a = ū − s(1,t)`, `a' = ū + s(1,t)`. If `N` is large, depending only on `K` and `b`, then for every
subgradient `ζ_t` of `μ` at `(1,t)`, `sup_{u ∈ I} (T(a,u) − ζ_t·(u−a)) ≤ O₁(C(b)Q_s)` and
`sup_{u ∈ I} (T(u,a') − ζ_t·(a'−u)) ≤ O₁(C(b)Q_s)`, and the same on the thickening of `I` by `s/64`
along `(1,t)`.

Readings. `s` is real, as in the paper. The paper's `a`, `a'` are real endpoints, replaced by a
nearest lattice point (the start of Section `sec:prelim`). Here they are every lattice
point within `√d` of the real points, which is stronger, and needs no fixed map. The set `thicken`
contains `I`, so one statement on the thickening gives both bounds of the paper, and one `X`
dominates both orientations. `C(b)` comes after `b` and before `K`. -/
def TreeStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∀ b : ℝ, 1 ≤ b → ∃ Cb : ℝ, 0 < Cb ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ s : ℝ, Real.sqrt N / 16 ≤ s → s ≤ N / 2 → ∀ (p : ℤ) (c t : EuclideanSpace ℝ (Fin m)) (a₀ : ℝ),
    0 ≤ a₀ → a₀ ≤ b * W M K A s → ‖t - M.t₀‖ ≤ 4 / 5 * s ^ (M.δ / 100 - 1 / 4) →
    ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P → ∀ a a' : Vertex m,
    ‖point a - (WithLp.toLp 2 ((p : ℝ), c) - s • slopeVec t)‖ ≤ Real.sqrt ((m : ℝ) + 1) →
    ‖point a' - (WithLp.toLp 2 ((p : ℝ), c) + s • slopeVec t)‖ ≤ Real.sqrt ((m : ℝ) + 1) →
    ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (Cb * Q M K A s) X ∧ ∀ᵐ ω ∂M.P,
      ∀ u ∈ thicken (transverseCube p c a₀) t (s / 64),
        passageTimeReal ω a u - inner ℝ P (point u - point a) ≤ X ω ∧
        passageTimeReal ω u a' - inner ℝ P (point a' - point u) ≤ X ω

/-- The conclusion of Proposition `prop:profiles` (equation `eq:profiles` and the two bounds after
it) at length `s` for a pair `I, I'` with slope `t`: for one `X ≤ O₁(C Q_s)`, almost
surely `|T(u,v) − μ(v − u)| ≤ X` for `u, v` in `I, I'` thickened by `s/1024`, and
`|T_P(u,v) − μ(v − u)| ≤ X` for `u ∈ I`, `v ∈ I'`, with `P` the slab between the hyperplanes of `I`
and `I'`. The thickenings contain the cubes, so this is the paper's three bounds. -/
def ShortConclusion (M : Model m) (K : ℕ) (A : ℝ) (s : ℕ) (C : ℝ)
    (t : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)) : Prop :=
  ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (C * Q M K A s) X ∧ ∀ᵐ ω ∂M.P,
    (∀ u ∈ thicken I t ((s : ℝ) / 1024), ∀ v ∈ thicken I' t ((s : ℝ) / 1024),
      |passageTimeReal ω u v - M.μ.1 (point v - point u)| ≤ X ω) ∧
    (∀ u ∈ I, ∀ v ∈ I', |slabTimeReal ω u.1 v.1 u v - M.μ.1 (point v - point u)| ≤ X ω)

/-- **Proposition `prop:profiles` for `s ≤ N/2`** (the first case of Proposition `prop:profiles`,
with its own proof, the proof for `s ≤ N/2`): for `b ≥ 1`, `N` large depending only on
`K` and `b`, an integer `N^{1/2} ≤ s ≤ N/2` and a pair of cubes of sides at most `b(sQ_s)^{1/2}`
with slope `|t − t₀| ≤ (4/5) s^{δ/100−1/4}`, the conclusion `ShortConclusion`.

This statement is internal and carries the paper's order of the proofs: this case is proved first,
then Lemma `lem:rowenergy` and Lemma `lem:parent` from it, then the second case (the proof for
`κN ≤ s ≤ 2N`, after Lemma `lem:parent`). So it breaks the cycle Proposition `prop:profiles` →
Lemma `lem:rowenergy` → Lemma `lem:parent` → Proposition `prop:profiles`, as the continuum
library's `IsotropicVariance.Paper.Contracts.ProfilesShortStatement` does. -/
def ProfilesShortStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∀ b : ℝ, 1 ≤ b → ∃ Cb : ℝ, 0 < Cb ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ s : ℕ, Real.sqrt N ≤ s → (s : ℝ) ≤ N / 2 → ∀ (t : EuclideanSpace ℝ (Fin m))
    (I I' : Set (Vertex m)), IsCubePair M K A s b t I I' →
    ‖t - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) → ShortConclusion M K A s Cb t I I'

/-- **Proposition `prop:profiles`**, equation `eq:profiles`: let `b ≥ 1`, `κ ∈ (0, 1]`, `s` an
integer, and `I, I'` a pair of cubes of sides at most `b(sQ_s)^{1/2}` with slope `t`, such that
either `N^{1/2} ≤ s ≤ N/2` and `|t − t₀| ≤ (4/5) s^{δ/100−1/4}`, or `κN ≤ s ≤ 2N` and
`|t − t₀| ≤ (3/2) s^{δ/100−1/4}`. If `N` is large, depending only on `K`, `b` and `κ`, then
`sup_{I×I'} |T_P − μ| ≤ O₁(C(b)Q_s)` for the slab `P` between the hyperplanes, the same for `T`,
and, for `T`, on the thickenings by `s/1024`.

Readings. Here `κ > 0`, which is stronger than the paper's statement and has no content: a larger
`κ` has a smaller range. `C(b)` comes before `κ` and `K`, and the threshold after them. -/
def ProfilesStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∀ b : ℝ, 1 ≤ b → ∃ Cb : ℝ, 0 < Cb ∧
  ∀ κ : ℝ, 0 < κ → ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (s : ℕ) (t : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
    IsCubePair M K A s b t I I' →
    ((Real.sqrt N ≤ s ∧ (s : ℝ) ≤ N / 2 ∧ ‖t - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4)) ∨
      (κ * N ≤ s ∧ (s : ℝ) ≤ 2 * N ∧ ‖t - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4))) →
    ShortConclusion M K A s Cb t I I'

/-- **Lemma `lem:rowenergy`**, equation `eq:rowenergy`: there are `c, C > 0`, independent of the
number `M` of slabs and of `K`, such that for `N` large depending only on `K`, `M ≥ 128`,
`s ≥ N^{1/2}` with `Ms ≤ 3N`, and `Mst ∈ ℤ^{d-1}` with `|t − t₀| ≤ 2(Ms)^{δ/100−1/4}`, with `F` the
minimum of equation `eq:F` from `0` to `(Ms, Mst)` over slabs of width `s`, and `J_i` the cube
indices of the cubes `I_i(j)` (the text before Lemma `lem:rowenergy`, `w = ⌈(sQ_s)^{1/2}⌉`) of a
minimizing chain: `|F − μ(Ms,Mst)| + c Q_s ∑ᵢ |J_i − J_{i−1}|² ≤ C M Q_s + X` for one
`X ≤ O₁(C Q_s)`.

Readings. The paper's `M` is `Ms` and its `Mst` is `z`. The bound holds for all minimizing tuples at
once, which is stronger than the paper's lexicographically least chain, and it contains that chain:
an `O₁` variable that dominates all of them dominates it. -/
def ExpArrayStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (Ms s : ℕ), 128 ≤ Ms → Real.sqrt N ≤ s → ((Ms * s : ℕ) : ℝ) ≤ 3 * N →
  ∀ z : Fin m → ℤ, ‖transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
    2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) →
    ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (C * Q M K A s) X ∧ ∀ᵐ ω ∂M.P,
      ∀ Y : Fin (Ms + 1) → Fin m → ℤ,
        IsMinTuple M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) Y →
        |(slabMin M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)).toReal -
            M.μ.1 (point (((Ms * s : ℕ) : ℤ), z))| +
          c * Q M K A s * ∑ i : Fin Ms,
            indexJumpSq s (wInt M K A s) (targetSlope (Ms * s) z) Y i ≤
          C * Ms * Q M K A s + X ω

/-- **Equation `eq:chainsum`** (as [AB26, (4.7)]): for `M`, `s`, `t` and `N` as in Lemma
`lem:rowenergy` and independent random arrays `Z_1, …, Z_M` of nonnegative random variables with
`E[(Z_i(j,k) − |j−k|²)₊^{4d}] ≤ 1` for all `i, j, k`, `E[∑_{i=1}^M Z_i(x_{i−1}, x_i)] ≤ CM`.

Readings, as in the model `IsotropicVariance.Paper.Contracts.ChainSumStatement`:
* `Z_i(x_{i−1}, x_i)` is `Z_i(J_{i−1}, J_i)`. Lean slabs are 0-based here: the term of the slab
  `i : Fin Ms` is `Z i ω (J i.castSucc) (J i.succ)`.
* The bound holds for the supremum over all minimizing tuples, which is stronger than the paper's
  lexicographically least chain, and is what the proof gives.
* The arrays may be read off a larger probability space: `(Ω, Pr)` with a measure-preserving map
  `π : Ω → Config m`, the chain being that of `π ω`. The arrays `Y_i` of Lemma `lem:blocks` live on
  the law of the weights and of their resamplings, and the chain is that of the weights. The
  paper's statement is the instance `π = id`.
* The arrays take values in `[0, ∞]`, so that the subtraction, truncated at zero, is the positive
  part. `Y_i` is a sum over infinitely many blocks, finite only almost surely. A real array `Z ≥ 0`
  is the instance `ENNReal.ofReal ∘ Z`, so this form contains the paper's form. -/
def ChainSumStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (Ms s : ℕ), 128 ≤ Ms → Real.sqrt N ≤ s → ((Ms * s : ℕ) : ℝ) ≤ 3 * N →
  ∀ z : Fin m → ℤ, ‖transversePoint z - ((Ms * s : ℕ) : ℝ) • M.t₀‖ ≤
    2 * ((Ms * s : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (π : Ω → Config m), MeasurePreserving π Pr M.P →
  ∀ Z : Fin Ms → Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞,
    (∀ i j k, Measurable fun ω => Z i ω j k) → iIndepFun Z Pr →
    (∀ i j k, ∫⁻ ω, (Z i ω j k - ENNReal.ofReal (‖transversePoint (j - k)‖ ^ 2)) ^ (4 * (m + 1))
      ∂Pr ≤ 1) →
    ∫⁻ ω, ⨆ (Y : Fin (Ms + 1) → Fin m → ℤ)
        (_ : IsMinTuple M (π ω) s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) Y),
        ∑ i : Fin Ms, Z i ω (tupleIndex s (wInt M K A s) (targetSlope (Ms * s) z) Y i.castSucc)
          (tupleIndex s (wInt M K A s) (targetSlope (Ms * s) z) Y i.succ) ∂Pr ≤
      ENNReal.ofReal (C * Ms)

/-- **Lemma `lem:parent`**, equation `eq:parent`: let `κ ∈ (0, 1]`. If `N` is large, depending only
on `K` and `κ`, then for every integer `ℓ ∈ [κN, 3N]` and every `y ∈ ℤ^{d-1}` with
`|y − ℓt₀| ≤ (7/4) ℓ^{3/4+δ/100}`, `|T(0,(ℓ,y)) − μ(ℓ,y)| ≤ C Q_ℓ + O₁(Q_ℓ/100)`.

Readings. `X ≤ Y + O₁(θ)` is `X − Y ≤ O₁(θ)` (Section `ssec:notation`). Here `κ > 0`, which is
stronger than the paper's statement and has no content: a larger `κ` has a smaller range. `C` does
not depend on `κ` or `K`, and the threshold does. The range `7/4` is the paper's: the paper's proof
takes `t = y/(Ms)` and needs it. -/
def ParentStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ →
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ ℓ : ℕ, κ * N ≤ ℓ → (ℓ : ℝ) ≤ 3 * N → ∀ y : Fin m → ℤ,
    ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤ 7 / 4 * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) →
    CurvatureVariance.IsOs M.P 1 (Q M K A ℓ / 100)
      (fun ω => |passageTimeReal ω 0 ((ℓ : ℤ), y) - M.μ.1 (point ((ℓ : ℤ), y))| - C * Q M K A ℓ)

/-- **Lemma `lem:localization`** (with the data fixed at the beginning of Section
`sec:localization`): fix `b ≥ 1`, `κ ∈ (0, 1]`, an integer `ℓ ∈ [κN, N]`, and a pair of cubes
`I, I'` with `s = ℓ`, of sides at most `b(ℓQ_ℓ)^{1/2}`, with a slope `|t − t₀| ≤ ℓ^{δ/100−1/4}`. Let
`p ≥ 1`, and let `R = 1 + (ℓQ_ℓ)^{−1/2} sup_{u ∈ I, v ∈ I'} sup_π sup_{x ∈ π} dist(x, [u,v])`, where
`x` ranges over the vertices of `π`, and `π` ranges either over the geodesics from `u` to `v` or
over the geodesics from `u` to `v` in the slab `P` between the hyperplanes. If `N` is large,
depending only on `K`, `b`, `κ` and `p`, then `E[R^p] ≤ C(b,p)` for both choices of `π`.

Readings. `p` is real, as in the paper. `R` is `Paper.locRadius` and `Paper.locRadiusSlab`, with
values in `[0, ∞]`. The paper's subgradient `ζ_t` of the fixed data enters no statement of
this lemma. `C(b,p)` comes after `b` and `p`, before `κ` and `K`. Here `κ > 0`, which is stronger
and has no content. The hyperplane of `I` is `q`: for an empty `I` the statement holds for every
`q`. -/
def LocalizationStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∀ b : ℝ, 1 ≤ b → ∀ p : ℝ, 1 ≤ p →
  ∃ Cb : ℝ, 0 < Cb ∧ ∀ κ : ℝ, 0 < κ → ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ ℓ : ℕ, κ * N ≤ ℓ → ℓ ≤ N → ∀ (t : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
    IsCubePair M K A ℓ b t I I' → ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) →
    (∫⁻ ω, locRadius ω I I' (W M K A ℓ) ^ p ∂M.P ≤ ENNReal.ofReal Cb) ∧
    ∀ q : ℤ, (∀ u ∈ I, u.1 = q) →
      ∫⁻ ω, locRadiusSlab ω q (q + ℓ) I I' (W M K A ℓ) ^ p ∂M.P ≤ ENNReal.ofReal Cb

/-- **Lemma `lem:modulus`** (with the data fixed at the beginning of Section `sec:localization`),
equation `eq:modulus`: for every `η > 0` there is `h > 0`, depending only on `b` and `η`, such that,
if `N` is large, depending only on `K`, `b`, `κ` and `η`, then
`E[sup |T(u,v) − T(ũ,ṽ) − ζ_t·(v − u − ṽ + ũ)|^{8d}]^{1/(8d)} ≤ η Q_ℓ`, the supremum over
`u, ũ ∈ I`, `v, ṽ ∈ I'` with `|u − ũ|, |v − ṽ| ≤ h(ℓQ_ℓ)^{1/2}`, for every subgradient `ζ_t`
of `μ` at `(1,t)`.

Readings. `ũ, ṽ` are `u₂, v₂`. The supremum is one variable `X` with the `L^{8d}` bound. One `h`,
chosen before `K` and `κ`, as in the paper. -/
def ModulusStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∀ b : ℝ, 1 ≤ b → ∀ η : ℝ, 0 < η →
  ∃ h : ℝ, 0 < h ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
  ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → RangeA M K A N Cstar →
  ∀ ℓ : ℕ, κ * N ≤ ℓ → ℓ ≤ N → ∀ (t : EuclideanSpace ℝ (Fin m))
    (I I' : Set (Vertex m)), IsCubePair M K A ℓ b t I I' →
    ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) → ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P →
    ∃ X : Config m → ℝ, eLpNorm X (8 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal (η * Q M K A ℓ) ∧
      ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ u₂ ∈ I, ∀ v ∈ I', ∀ v₂ ∈ I',
        ‖point u - point u₂‖ ≤ h * W M K A ℓ → ‖point v - point v₂‖ ≤ h * W M K A ℓ →
        |passageTimeReal ω u v - passageTimeReal ω u₂ v₂ -
          inner ℝ P (point v - point u - point v₂ + point u₂)| ≤ X ω

end CurvatureVariance.Paper.Contracts
