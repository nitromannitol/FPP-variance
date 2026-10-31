/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Labels

/-!
# Contracts of Section `sec:gain`: the blocks, the labels and the gain

The statements of Section `sec:gain` of the lattice paper.

* `RadiusEnergyStatement` — equation `eq:radiusenergy` of Lemma `lem:blocks`.
* `RewardMomentStatement`, `BlockReplacementStatement` — the two bounds of equation
  `eq:rewardmoment` of Lemma `lem:blocks`.
* `BlockSumStatement` — equation `eq:blocksum`, in the proof of Lemma `lem:blocks`.
* `LabelsStatement` — Lemma `lem:labels`, equation `eq:labelprofile`, the values of probability at
  least `α_L`, and the translation property.
* `ResidualStatement` — Lemma `lem:residual`, both bounds of equation `eq:residual`.
* `FewTranslatesStatement` — Lemma `lem:fewtranslates`.
* `GainStatement` — Proposition `prop:gain`.

The resampling of [AB26, Section 6] appears in two forms. For Lemma `lem:blocks` it is an abstract
exchangeable replacement of the blocks, independent over the slabs (`Paper.IsSlabReplacement`). This
is stronger than "every choice of the `σ_G`", since the paper's resampling is an instance. The
paper's instances are constant `σ_G` (`Paper.esTerm`) and finite labels (`Gain.labelES`).

The target is `IsTarget`: `ℓ = Kn ∈ [N/9, N]`, `y ∈ 𝒟(ℓ)`, `t = y/ℓ` (Section `sec:gain`). A block
of slab `i` with offset `a_i = o i` is `Paper.block n w L t i (o i) g`, with `w = ⌈(nQ_n)^{1/2}⌉`,
and the sum over its blocks is the sum over `g ∈ ℤ^{d−1}`, the cell `j = Lg + o i` being its corner.

The quantities `ω_K` and `ω_L` at the start of Section `sec:gain` are functions chosen
before `K`, `L`, `N`, `A` and the targets. A chain sum holds for the supremum over all minimizing
tuples where the bound is an upper bound of that sum. Every statement is uniform in the direction:
its constants and thresholds come after a `Bounds` record and before the models that fit it
(`Model.Fits`), so they depend only on the law and the bounds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Contracts

open CurvatureVariance.Paper

universe u

/-- **Lemma `lem:blocks`, equation `eq:radiusenergy`**: if `N` is large, depending only on `K`, then
`E[Σ_{i=1}^K R_i(x_{i−1}, x_i)²] ≤ CK`.

Readings. `R_i(j,k)` is `Paper.radiusArray` with the constant `C_d`: `C_d(1 + R)` on the retained
pairs `8w|k − j| ≤ n^{3/4+δ/100}` and `0` on the others, which is the paper's `CR` up to a factor
`2`, since `R ≥ 1` (the text before Lemma `lem:blocks`). The statement holds for every `C_d ≥ 0`,
with `C` after `C_d`; the paper's constant is the one of `TubeStatement`. It holds for the supremum
over all minimizing tuples, which is stronger than the paper's lexicographically least chain. -/
def RadiusEnergyStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar Cd : ℝ, 0 ≤ Cd → ∃ C : ℝ, 0 < C ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
    ∫⁻ ω, ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
        (_ : IsMinTuple M ω n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y),
        ∑ i : Fin K, radiusArray M K A Cd ω n (targetSlope ℓ y) ((i : ℕ) + 1)
          (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
          (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ) ^ 2 ∂M.P ≤
      ENNReal.ofReal (C * K)

/-- **Lemma `lem:blocks`, first bound of equation `eq:rewardmoment`**: if `N` is large, depending
only on `K`, then for every integer `L ≥ 1`, every choice of the vectors `a_i` and of the `σ_G`, and
all `i, j, k`, `E[Y_i(j,k)^{16d}]^{1/(16d)} ≤ C(1 + |j − k|)`, written here for the moment itself.

Readings. The threshold depends only on `K`, as in the paper, so `L` comes after it. `Y_i(j,k)` is
`Paper.reward`, which vanishes off the retained pairs. The choice of the `σ_G` is the exchangeable
replacement `IsSlabReplacement`, which is stronger. -/
def RewardMomentStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
  ∀ L : ℕ, 1 ≤ L → ∀ o : ℕ → Fin m → ℤ, (∀ i k, 0 ≤ o i k ∧ o i k < L) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (Pr : Measure Ω) (old : Ω → Config m)
    (new : ℕ → (Fin m → ℤ) → Ω → Config m),
    IsSlabReplacement M Pr n K (wInt M K A n) L (targetSlope ℓ y) o old new →
    ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ j k : Fin m → ℤ,
      ∫⁻ ω, reward M K A n (targetSlope ℓ y) old new i j k ω ^ (16 * (m + 1)) ∂Pr ≤
        ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (16 * (m + 1)))

/-- **Equation `eq:blocksum`** (in the proof of Lemma `lem:blocks`):
`Σ_G E[(F^G − F)²] ≤ 2 Q_n² E[Σ_{i=1}^K Y_i(x_{i−1}, x_i)]`, the sum over the blocks of all `K`
slabs, both sides in `[0, ∞]`.

Readings. The chain `x_i` is any almost sure selection `x` of a minimizing chain of the weights
`old`. The paper's lexicographically least chain is one. A selection, not a supremum, since the
right side here is an upper bound: a supremum over the minimizing tuples would be weaker than the
paper's statement. The paper's proof applies to every selection and needs no measurability of
it. -/
def BlockSumStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
  ∀ L : ℕ, 1 ≤ L → ∀ o : ℕ → Fin m → ℤ, (∀ i k, 0 ≤ o i k ∧ o i k < L) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (Pr : Measure Ω) (old : Ω → Config m)
    (new : ℕ → (Fin m → ℤ) → Ω → Config m),
    IsSlabReplacement M Pr n K (wInt M K A n) L (targetSlope ℓ y) o old new →
    ∀ x : Ω → Fin (K + 1) → Fin m → ℤ,
      (∀ᵐ ω ∂Pr, IsMinTuple M (old ω) n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) (x ω)) →
      ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
          ∫⁻ ω, ENNReal.ofReal ((targetMin M (new (i + 1) g ω) n K ℓ y -
            targetMin M (old ω) n K ℓ y) ^ 2) ∂Pr ≤
        ENNReal.ofReal (2 * Q M K A n ^ 2) *
          ∫⁻ ω, ∑ i : Fin K, reward M K A n (targetSlope ℓ y) old new ((i : ℕ) + 1)
            (tupleIndex n (wInt M K A n) (targetSlope ℓ y) (x ω) i.castSucc)
            (tupleIndex n (wInt M K A n) (targetSlope ℓ y) (x ω) i.succ) ω ∂Pr

/-- **Lemma `lem:blocks`, second bound of equation `eq:rewardmoment`**: if `N` is large, depending
only on `K`, then for every integer `L ≥ 1` and every choice of the vectors `a_i` and of the `σ_G`,
`Σ_G E[(F^G − F)²] ≤ C K Q_n²`, the sum over the blocks of all `K` slabs, in `[0, ∞]`. There is no
factor `½`, as in the paper. -/
def BlockReplacementStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
  ∀ L : ℕ, 1 ≤ L → ∀ o : ℕ → Fin m → ℤ, (∀ i k, 0 ≤ o i k ∧ o i k < L) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (Pr : Measure Ω) (old : Ω → Config m)
    (new : ℕ → (Fin m → ℤ) → Ω → Config m),
    IsSlabReplacement M Pr n K (wInt M K A n) L (targetSlope ℓ y) o old new →
    ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        ∫⁻ ω, ENNReal.ofReal ((targetMin M (new (i + 1) g ω) n K ℓ y -
          targetMin M (old ω) n K ℓ y) ^ 2) ∂Pr ≤
      ENNReal.ofReal (C * K * Q M K A n ^ 2)

/-- **Lemma `lem:labels`**: let `L ≥ 16` be an integer. There is `α_L > 0`, depending only on `L`,
such that, if `N` is large, depending only on `K` and `L`, then for every slab `i` and every block
`G` of it there is a random variable `X_G`, determined by `τ|_G`, taking finitely many values, each
a bounded function on `Γ_G` and each with probability at least `α_L`, such that equation
`eq:labelprofile` holds with `ω_L`, and the translation property of the last sentence of the lemma
holds.

Readings. The conclusion is `Gain.IsLabelFamily`, whose docstring reads it clause by clause: one
family `lam i o g` indexed by the slab, the offset and the block, so `X_G` depends only on `G`, as
in the paper; the translation property at every `ω`; every value of probability at least `α_L`,
not "`0` or at least `α_L`". The functions `α` and `ψ = ω_L` are chosen before `K` and `L`. The
subgradient `ζ_t = P` is fixed in the text before Lemma `lem:labels`, so the labels come
after it. -/
def LabelsStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ α ψ : ℕ → ℝ, (∀ L, 0 < α L) ∧
    Tendsto ψ atTop (𝓝 0) ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ L : ℕ, 16 ≤ L → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
  ∀ P : Pt m, IsSubgradient M.μ (slopeVec (targetSlope ℓ y)) P →
    ∃ lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ,
      Gain.IsLabelFamily M K A L n (targetSlope ℓ y) P (α L) (ψ L) lam

/-- **Lemma `lem:residual`**, equation `eq:residual`: let `L ≥ 16` be an integer, let `X_G` be as in
Lemma `lem:labels`, and let `τ^G` be the resampling of `G` with `σ_G = X_G`. If `N` is large,
depending only on `K` and `L`, then `L^{−K(d−1)} Σ_a Σ_G E[(F^G − F)²] ≤ ω_L K Q_n²` and
`L^{−K(d−1)} Σ_a E[Var[F̄ | (X_G)_G]] ≤ ω_L K Q_n²`, where `a = (a_1, …, a_K)` ranges over
`({0, …, L−1}^{d−1})^K`.

Readings. The statement is quantified over exactly what Lemma `lem:labels` delivers: for all
functions `α > 0` and `ε → 0`, every family with `Gain.IsLabelFamily` at `α L` and `ε L`. It holds
for each family, so it assumes nothing else; the paper's `X_G` is the instance `α, ψ` of
`LabelsStatement`, and the paper's `ω_L` is `ψ'` here, chosen after `α` and `ε`, and before `K`, `L`
and the family. The paper says "the blocks, the `X_G` and `τ^G` depend on `a`": here, as in Lemma
`lem:labels`, `X_G` depends on the slab, the offset and the block only. `F̄` is
`Paper.averagedMin`, with the endpoints of `F_m` shifted by `mLwe₂` (the text before Lemma
`lem:residual`). The first sum is `Gain.blockEnergy`, which has no factor `½`, as in the paper, and
the second is `Gain.meanConditionalVariance`. -/
def ResidualStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∀ α ε : ℕ → ℝ, (∀ L, 0 < α L) →
    Tendsto ε atTop (𝓝 0) → ∃ ψ' : ℕ → ℝ, Tendsto ψ' atTop (𝓝 0) ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ L : ℕ, 16 ≤ L → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
  ∀ P : Pt m, IsSubgradient M.μ (slopeVec (targetSlope ℓ y)) P →
  ∀ lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ,
    Gain.IsLabelFamily M K A L n (targetSlope ℓ y) P (α L) (ε L) lam →
    Gain.offsetAverage K L (Gain.blockEnergy M.P (fun ω => targetMin M ω n K ℓ y) n
        (wInt M K A n) L K (targetSlope ℓ y) lam) ≤
      ENNReal.ofReal (ψ' L * K * Q M K A n ^ 2) ∧
    Gain.offsetAverage K L (fun o => Gain.meanConditionalVariance M.P
        (fun ω => averagedMin M K A L ω n ℓ y) K o lam) ≤
      ENNReal.ofReal (ψ' L * K * Q M K A n ^ 2)

/-- **Lemma `lem:fewtranslates`**: let `L ≥ 16` be an integer. If `N` is large, depending only on
`K` and `L`, then for every choice of the vectors `a_i`, `Σ_G E[(f − E_G[f])²] ≤ C K Q_n²` and
`Σ_G E[|f − E_G[f]|]² ≤ C K^{−1/6} K Q_n²`, the sums over the blocks of all `K` slabs, in `[0, ∞]`,
written with the `L²` and `L¹` norms.

Readings. `f = E[F̄ | (X_G)_G]` is `Gain.labelMean`, and `E_G[f]`, the expectation of `f` with
respect to `X_G` alone (the text before [AB26, Lemma 6.3]), is `Gain.integrateLabel`, a conditional
expectation given the other labels, as in the continuum library's
`IsotropicVariance.Paper.Contracts.FewTranslatesStatement`. The paper fixes the `X_G` of Lemma
`lem:labels`; its proof uses only that they are determined by the weights in their blocks and have
finitely many values, so the statement is for every such family (`Gain.IsOffsetLabels`), which is
stronger, and contains the paper's statement by `Gain.IsLabelFamily.isOffsetLabels`. `C` comes
before `K` and `L`. -/
def FewTranslatesStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ L : ℕ, 16 ≤ L → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y →
  ∀ o : ℕ → Fin m → ℤ, (∀ i k, 0 ≤ o i k ∧ o i k < L) →
  ∀ lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ,
    Gain.IsOffsetLabels n (wInt M K A n) L K (targetSlope ℓ y) o lam →
    (∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        eLpNorm (Gain.labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam -
          Gain.integrateLabel M.P
            (Gain.labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam) K o lam i g)
          2 M.P ^ 2 ≤ ENNReal.ofReal (C * K * Q M K A n ^ 2)) ∧
    ∑ i ∈ Finset.range K, ∑' g : Fin m → ℤ,
        eLpNorm (Gain.labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam -
          Gain.integrateLabel M.P
            (Gain.labelMean M.P (fun ω => averagedMin M K A L ω n ℓ y) K o lam) K o lam i g)
          1 M.P ^ 2 ≤ ENNReal.ofReal (C * (K : ℝ) ^ (-(1 : ℝ) / 6) * (K * Q M K A n ^ 2))

/-- **Proposition `prop:gain`**: there is `ω_K`, tending to zero as `K → ∞`, such that, if `K` is
large and `N` is large depending on `K`, then `Var[T(0,(ℓ',y'))] ≤ ω_K Q_{ℓ'}²` for every integer
`ℓ' ∈ [N/8, N]` and every `y' ∈ 𝒟(ℓ')`.

Readings. `ω_K` is `φ K`, chosen before `K`. The threshold is independent of `A`. -/
def GainStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∃ φ : ℕ → ℝ, Tendsto φ atTop (𝓝 0) ∧
  ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ ℓ : ℕ, (N : ℝ) / 8 ≤ ℓ → ℓ ≤ N → ∀ y ∈ premiseDomain M ℓ,
    evariance (fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y)) M.P ≤
      ENNReal.ofReal (φ K * Q M K A ℓ ^ 2)

end CurvatureVariance.Paper.Contracts
