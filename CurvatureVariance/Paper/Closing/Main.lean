/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Arrays
public import CurvatureVariance.Paper.Contracts.Closing
public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Inputs
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Responses
import CurvatureVariance.Paper.Closing.BaseCase
import CurvatureVariance.Paper.Closing.DomainExp
import CurvatureVariance.Paper.Closing.Induction
import CurvatureVariance.Paper.Closing.MainExp
import CurvatureVariance.Paper.Closing.MainTheorems
import CurvatureVariance.Paper.Closing.OwnBounds
import CurvatureVariance.Paper.Closing.VarianceSentence
import CurvatureVariance.Paper.Proofs.Arrays
import CurvatureVariance.Paper.Proofs.Chart.ChartUniform
import CurvatureVariance.Paper.Proofs.Chart.Rounding
import CurvatureVariance.Paper.Proofs.Gain.FewTranslatesBound
import CurvatureVariance.Paper.Proofs.Gain.GainMain
import CurvatureVariance.Paper.Proofs.Gain.LabelsMain
import CurvatureVariance.Paper.Proofs.Geometry.Chains
import CurvatureVariance.Paper.Proofs.Geometry.Classical
import CurvatureVariance.Paper.Proofs.Geometry.GeodesicLength
import CurvatureVariance.Paper.Proofs.Geometry.Good
import CurvatureVariance.Paper.Proofs.Geometry.SlabsHits
import CurvatureVariance.Paper.Proofs.Geometry.Support
import CurvatureVariance.Paper.Proofs.Localization.LocMain
import CurvatureVariance.Paper.Proofs.Localization.ModulusMain
import CurvatureVariance.Paper.Proofs.Mean.Classical
import CurvatureVariance.Paper.Proofs.Mean.Improvement
import CurvatureVariance.Paper.Proofs.Mean.SmallMean
import CurvatureVariance.Paper.Proofs.Moments.ChainSum
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayRowEnergy
import CurvatureVariance.Paper.Proofs.Moments.ParentLemma
import CurvatureVariance.Paper.Proofs.Moments.Scales
import CurvatureVariance.Paper.Proofs.Moments.Tree
import CurvatureVariance.Paper.Proofs.Modified
import CurvatureVariance.Paper.Proofs.Reduction.Coordinates
import CurvatureVariance.Paper.Proofs.Reduction.EveryPoint
import CurvatureVariance.Paper.Proofs.Reduction.FinalTarget
import CurvatureVariance.Paper.Proofs.Residual.Main
import CurvatureVariance.Paper.Proofs.Responses.BlocksRadius
import CurvatureVariance.Paper.Proofs.Responses.BlocksReplacement
import CurvatureVariance.Paper.Proofs.Responses.BlocksReward
import CurvatureVariance.Paper.Proofs.Responses.BlocksSum
import CurvatureVariance.Paper.Proofs.Responses.FixedComparisonMain
import CurvatureVariance.Paper.Proofs.ShortLengths.ProfilesDifference
import CurvatureVariance.Paper.Proofs.ShortLengths.ProfilesFull
import CurvatureVariance.Paper.Proofs.Tubes.Tube

/-!
# The paper's proof graph, type-checked

The four roots have no hypothesis beyond the binders of their statements:

* `lintegral_exp_passageTime_le`: Theorem `thm:main`, with the statement of
  `CurvatureVariance.lintegral_exp_passageTime_le`;
* `variance_passageTime_le`: the same with the variance sentence after Theorem `thm:main`, for the
  same `ε` and `C`;
* `evariance_passageTime_floorVertex_le_uniform`: the statement of
  `CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`, a corollary of that sentence;
* `evariance_passageTime_floorVertex_le`: the statement of
  `CurvatureVariance.evariance_passageTime_floorVertex_le`, a theorem at one direction under
  `AssumptionCAt`, which is not in the paper. It is proved at the level of the model, and shares
  every edge up to `DomainExpStatement`.

Three further roots, reached by no other theorem, are statements of the paper themselves:

* `slabsBounds_holds`: Lemma `lem:slabs`, in the paper's form, without the chain of its proof;
* `improvementStatement_holds`: Proposition `prop:induction`, in the paper's form;
* `boundA_holds`: the bound (a) of Section `sec:induction`, for `ℓ ∈ [N/8, N]` and `y ∈ 𝒟(ℓ)`.

They are roots beside `variance_passageTime_le`.

The lists below are the record of the proof. An edge of the graph is an implication between
contracts, one for each proof of the paper, whose premises are the contracts that the proof uses,
read from the paper and, for a proof given as changes to a proof of [AB26], from that proof with
the changes. Each edge is a theorem, named last in its item, and every edge is proved; the theorems
below compose them.

The providers of `CurvatureVariance.lintegral_exp_passageTime_le`,
`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform` and
`CurvatureVariance.evariance_passageTime_floorVertex_le` apply the roots to their binders.

## Section `sec:prelim` and the introduction

* Equation `eq:union`: → `OsUnionStatement`, `Contracts.osUnionStatement_holds`.
* Equation `eq:sum`: → `SignedOsSumStatement`, `Contracts.signedOsSumStatement_holds`. For `s ≥ 1`
  it is [AKM, Lemma A.4], `CurvatureVariance.exists_isOs_integral`; the case `s < 1` is not in the
  paper.
* Equation `eq:sum` over `IsOs`: → `OsSumStatement`, `Contracts.osSumStatement_holds`; no edge uses
  it.
* Lemma `lem:chart`: → `ChartUniformStatement`, `Chart.chartUniformStatement_holds`.
* Lemma `lem:support`: → `SupportStatement`, `Geometry.supportStatement`.
* Equation `eq:rounding`: → `RoundingStatement`, `Chart.roundingStatement_holds`.
* Equation `eq:classical`: → `ClassicalStatement`, `Geometry.classicalStatement_holds`.
* The bound on the number of edges of geodesics, after equation `eq:classical`:
  → `GeodesicLengthStatement`, `Geometry.geodesicLengthStatement_holds`.
* Lemma `lem:good`: `Classical` → `GoodStatement`, `Geometry.goodStatement_holds`.
* Lemma `lem:cone`: `Support` → `ConeStatement`, `Geometry.coneStatement_of`.
* The existence of chains, after equation `eq:F`: → `ChainsExistStatement`,
  `Geometry.chainsExistStatement_holds`.
* Lemma `lem:slabs`: `Cone` → `SlabsStatement`, `Geometry.slabsStatement_of`.

## Sections `sec:induction` and `sec:cubes`

* Equation `eq:scales`: → `ScalesStatement`, `Moments.scalesStatement_holds`.
* Lemma `lem:tree`: `Scales`, `Support`, `OsUnion`, `SignedOsSum` → `TreeStatement`,
  `Moments.treeStatement`.
* Equation `eq:profiledifference`: `Good`, `Slabs`, `Scales` → `ProfileDifferenceStatement`,
  `ShortLengths.profileDifferenceStatement`.
* Proposition `prop:profiles`, first case: `Tree`, `ProfileDifference`, `Support`, `Scales`,
  `SignedOsSum` → `ProfilesShortStatement`, `ShortLengths.profilesShortStatement`.
* Lemma `lem:rowenergy`: `ProfilesShort`, `Support`, `Scales`, `ChainsExist` → `ExpArrayStatement`,
  `Moments.expArrayStatement`.
* [AB26, Lemma 2.4]: → `ArraysStatement`, `Arrays.arraysStatement_holds`.
* Equation `eq:chainsum`: `ExpArray`, `Arrays` → `ChainSumStatement`, `Moments.chainSumStatement`.
* Lemma `lem:parent`: `ExpArray`, `Good`, `Slabs`, `ChainsExist`, `Classical`, `SignedOsSum`
  → `ParentStatement`, `Moments.parentStatement`.
* Proposition `prop:profiles`, second case: `ProfilesShort`, `Parent`, `Tree`, `ProfileDifference`,
  `Support`, `Scales`, `SignedOsSum` → `ProfilesStatement`, `ShortLengths.profilesStatement`.

## Sections `sec:localization`, `sec:gain` and `sec:mean`

* Lemma `lem:localization`: `Tree`, `Profiles`, `Support`, `Scales`, `Good`, `Cone`, `Slabs`,
  `GeodesicLength`, `OsUnion`, `SignedOsSum` → `LocalizationStatement`,
  `Localization.localizationStatement_of`.
* Lemma `lem:modulus`: `Profiles`, `Localization`, `Support`, `Scales`, `OsUnion`
  → `ModulusStatement`, `Localization.modulusStatement`.
* Equation `eq:fixedcomparison`: `Good`, `Slabs`, `ChainsExist` → `FixedComparisonStatement`,
  `Contracts.fixedComparison`.
* The tube property, before Lemma `lem:blocks`: → `TubeStatement`, `Contracts.tubeStatement_holds`.
* Equation `eq:radiusenergy`: `Localization`, `ChainSum`, `Scales` → `RadiusEnergyStatement`,
  `Contracts.radiusEnergy`.
* Equation `eq:rewardmoment`, first bound: `Localization`, `Profiles`, `Tube`, `Scales`
  → `RewardMomentStatement`, `Contracts.rewardMoment`.
* Equation `eq:blocksum`: `Scales` → `BlockSumStatement`, `Contracts.blockSum`.
* Equation `eq:rewardmoment`, second bound: `RewardMoment`, `BlockSum`, `ChainSum`
  → `BlockReplacementStatement`, `Contracts.blockReplacement`.
* Lemma `lem:labels`: `Profiles`, `Localization`, `Modulus`, `ProfileDifference`, `Support`,
  `Scales`, `Tube` → `LabelsStatement`, `Gain.labelsStatement_of`.
* Lemma `lem:residual`: `RewardMoment`, `BlockSum`, `ChainSum`, `Localization`, `Scales`, `Tube`
  → `ResidualStatement`, `Residual.residualStatement_of`.
* Lemma `lem:fewtranslates`: `RewardMoment`, `BlockReplacement`, `ExpArray`, `RadiusEnergy`,
  `Scales`, `Tube` → `FewTranslatesStatement`, `Gain.fewTranslatesStatement_of`.
* [AB26, Proposition 1.3]: → `ModifiedPoincareStatement`,
  `Modified.modifiedPoincareStatement_holds`.
* Proposition `prop:gain`, with the reduction to lengths that are multiples of `K` at the beginning
  of Section `sec:gain`: `Labels`, `Residual`, `FewTranslates`, `ModifiedPoincare`, `Modulus`,
  `FixedComparison`, `Rounding` → `GainStatement`, `Gain.Printed.gainStatement`.
* Lemma `lem:smallmean`: `Support`, `Scales`, `Classical`, `Modulus`, `Parent`, `ProfileDifference`,
  `Arrays`, `Good`, `Slabs`, `ChainsExist` → `SmallMeanStatement`, `Mean.smallMeanStatement_of`.

## The induction and the theorems

* The reduction to equation `eq:regime`, after the proof of Theorem `thm:main`: `Classical`
  → `ClassicalRangeStatement`, `Mean.ClassicalRangeStatement_of`.
* Proposition `prop:induction`, from the bounds (a)–(c) of Section `sec:induction` and its proof at
  the end of Section `sec:mean`: `ClassicalRange`, `Classical`, `Parent`, `Gain`, `SmallMean`,
  `Rounding`, `SignedOsSum` → `ImprovementAllKStatement`, `Mean.improvementAllKStatement_of`.
* Proposition `prop:induction`, in the paper's form: `ImprovementAllK` → `ImprovementStatement`,
  `Contracts.improvementStatement_of_allK`.
* The base case, in the proof of Theorem `thm:main`: → `BaseCaseStatement`,
  `Closing.baseCaseStatement_holds`.
* The induction on `N`, in the proof of Theorem `thm:main`: `ImprovementAllK`, `BaseCase`
  → `DomainExpStatement`, `Closing.domainExpStatement`.
* The choice of coordinates, at the beginning of Section `sec:prelim`: `ChartUniform`
  → `ReductionUniformStatement`, `Reduction.reductionUniformStatement`.
* Theorem `thm:main`, in the proof given Proposition `prop:induction`: `DomainExp`,
  `ReductionUniform`, `BaseCase` → `MainExpStatement`, `Closing.mainExpStatement`.
* The variance sentence after Theorem `thm:main`: `MainExp` → `VarianceSentenceStatement`,
  `Closing.varianceSentenceStatement`.

## Notes on the edges

* Lemma `lem:rowenergy` is `Moments.expArrayStatement`, over `Moments.expArray_of`. Its premise
  `ChainsExist` is not used: the rounded chain is proved directly.
* Equations `eq:union` and `eq:sum` are proved unconditionally, and any proof may use them. They
  are listed as premises where they are a named step of a proof of the paper or of a cited proof,
  not at every use. Their universes are `0`.
* The cited inputs are not premises: they are statements of results from the literature, which the
  proofs use directly.

## Inputs that are not in the paper

* `MainUniformStatement`, from `VarianceSentence`: proved, `Closing.mainUniformStatement`. The
  paper has no bound at `⌊nξ⌋`.
* `MainTheoremStatement`, from `DomainExp`, `OwnBounds`, `Reduction`, `FinalTarget`: proved,
  `Closing.mainTheoremStatement`. It is not derived from Theorem `thm:main`: its hypothesis
  `AssumptionCAt` is on a transverse `H` at a direction that need not be a unit vector.
* `ReductionStatement` (`Reduction.reductionStatement_holds`), `FinalTargetStatement`
  (`Reduction.finalTargetStatement_holds`), `OwnBoundsStatement`
  (`Closing.ownBoundsStatement_holds`): proved, used only at one direction.
* `ReductionUniformStatement`: the formal transport to the chosen coordinates through `2d` laws,
  which the paper calls a choice of coordinates. Proved,
  `Reduction.reductionUniformStatement`.
* `ImprovementAllKStatement`, `DomainExpStatement`: one `K` for the `2d` laws.
* `ProfilesShortStatement`: the first case of a proposition of the paper, to break a cycle.
* `ChainsExistStatement`: a sentence of the paper, as a statement, since the tuple encoding needs
  it.
* `TubeStatement`: a sentence of the paper, in a stronger form.
* `Model`, `Bounds`, `Model.Fits`, `chartBounds`: the encoding of the convention of Section
  `ssec:notation` that constants and thresholds may depend on `d`, the law and the constants of
  (Curv), but not on `ξ`.
* The companion statements and the other inputs (existence and uniqueness of the weights and of
  the time constant, one-arm decay, bounds on `p_c`) are below the `Infra` layer and enter no edge
  here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Closing

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Paper.Proofs

/-! ### Section `sec:prelim` -/

/-- Lemma `lem:cone`. -/
theorem coneStatement_holds (m : ℕ) : ConeStatement m :=
  Geometry.coneStatement_of (Geometry.supportStatement m)

/-- Lemma `lem:slabs`. -/
theorem slabsStatement_holds (m : ℕ) : SlabsStatement m :=
  Geometry.slabsStatement_of (coneStatement_holds m)

/-- **Lemma `lem:slabs`**, as stated: on the good event, `0 ≤ T_P(u, v) - T(u, v) ≤ C S²` in (1),
and `0 ≤ F - T(u, v) ≤ C M S²` in (2). The proof of the lemma also shows that the first vertices of
a geodesic on the hyperplanes form a chain, and `SlabsStatement` states that too. A root: no other
theorem reaches it. -/
theorem slabsBounds_holds (m : ℕ) (bd : Bounds m) (hbd : bd.Valid) (Cg cg : ℝ) (hCg : 0 < Cg)
    (hcg : 0 < cg) : ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ S : ℝ, Real.log N ≤ S →
    ∀ ω : Config m, IsGood M Cg cg N S ω →
    ∀ (ℓ : ℕ) (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m),
      point v - point u = (ℓ : ℝ) • slopeVec t → 1 ≤ ℓ → (ℓ : ℝ) ≤ 3 * N →
      ‖t - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) →
      -- (1)
      (InBox ((N : ℝ) ^ 2) u → InBox ((N : ℝ) ^ 2) v → C * S ^ 2 ≤ ℓ →
        (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v ∧
          slabTime ω u.1 v.1 u v ≤ (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C * S ^ 2)) ∧
      -- (2)
      (∀ Ms n : ℕ, ℓ = Ms * n → 1 ≤ Ms → Real.sqrt N ≤ n →
        ‖t - M.t₀‖ ≤ 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) → S ≤ (N : ℝ) ^ (M.δ / 1000) →
        InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) u → InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) v →
        (passageTime ω u v : ℝ≥0∞) ≤ slabMin M ω n Ms t u v ∧
          slabMin M ω n Ms t u v ≤ (passageTime ω u v : ℝ≥0∞) +
            ENNReal.ofReal (C * Ms * S ^ 2)) := by
  obtain ⟨C, hC, N₀, h⟩ := slabsStatement_holds m bd hbd Cg cg hCg hcg
  refine ⟨C, hC, N₀, fun M hM hfit N hN S hS ω hω ℓ t u v huv hℓ hℓN ht => ?_⟩
  have h' := h M hM hfit N hN S hS ω hω ℓ t u v huv hℓ hℓN ht
  exact ⟨h'.1, fun Ms n hl hMs hn ht' hS' hu hv => (h'.2 Ms n hl hMs hn ht' hS' hu hv).2⟩

/-! ### Sections `sec:induction` and `sec:cubes` -/

/-- Lemma `lem:tree`. -/
theorem treeStatement (m : ℕ) : TreeStatement m :=
  Moments.treeStatement (Moments.scalesStatement_holds m) (Geometry.supportStatement m)
    osUnionStatement_holds signedOsSumStatement_holds

/-- Equation `eq:profiledifference`. -/
theorem profileDifferenceStatement (m : ℕ) : ProfileDifferenceStatement m :=
  ShortLengths.profileDifferenceStatement (Geometry.goodStatement_holds m)
    (slabsStatement_holds m) (Moments.scalesStatement_holds m)

/-- Proposition `prop:profiles`, first case. -/
theorem profilesShortStatement (m : ℕ) : ProfilesShortStatement m :=
  ShortLengths.profilesShortStatement (treeStatement m) (profileDifferenceStatement m)
    (Geometry.supportStatement m) (Moments.scalesStatement_holds m) signedOsSumStatement_holds

/-- Lemma `lem:rowenergy`. -/
theorem expArrayStatement (m : ℕ) : ExpArrayStatement m :=
  Moments.expArrayStatement (profilesShortStatement m) (Geometry.supportStatement m)
    (Moments.scalesStatement_holds m) (Geometry.chainsExistStatement_holds m)

/-- Equation `eq:chainsum`. -/
theorem chainSumStatement (m : ℕ) : ChainSumStatement.{0} m :=
  Moments.chainSumStatement (expArrayStatement m) (Proofs.Arrays.arraysStatement_holds m)

/-- Lemma `lem:parent`. -/
theorem parentStatement (m : ℕ) : ParentStatement m :=
  Moments.parentStatement (expArrayStatement m) (Geometry.goodStatement_holds m)
    (slabsStatement_holds m)
    (Geometry.chainsExistStatement_holds m) (Geometry.classicalStatement_holds m)
    signedOsSumStatement_holds

/-- Proposition `prop:profiles`. -/
theorem profilesStatement (m : ℕ) : ProfilesStatement m :=
  ShortLengths.profilesStatement (profilesShortStatement m) (parentStatement m)
    (treeStatement m)
    (profileDifferenceStatement m) (Geometry.supportStatement m)
    (Moments.scalesStatement_holds m)
    signedOsSumStatement_holds

/-! ### Section `sec:localization` -/

/-- Lemma `lem:localization`. -/
theorem localizationStatement (m : ℕ) : LocalizationStatement m :=
  Localization.localizationStatement_of (treeStatement m) (profilesStatement m)
    (Geometry.supportStatement m) (Moments.scalesStatement_holds m)
    (Geometry.goodStatement_holds m) (coneStatement_holds m) (slabsStatement_holds m)
    (Geometry.geodesicLengthStatement_holds m)
    osUnionStatement_holds signedOsSumStatement_holds

/-- Lemma `lem:modulus`. -/
theorem modulusStatement (m : ℕ) : ModulusStatement m :=
  Localization.modulusStatement (profilesStatement m) (localizationStatement m)
    (Geometry.supportStatement m) (Moments.scalesStatement_holds m) osUnionStatement_holds

/-! ### Section `sec:gain` -/

/-- Equation `eq:fixedcomparison`. -/
theorem fixedComparisonStatement (m : ℕ) : FixedComparisonStatement m :=
  fixedComparison (Geometry.goodStatement_holds m) (slabsStatement_holds m)
    (Geometry.chainsExistStatement_holds m)

/-- Equation `eq:radiusenergy`. -/
theorem radiusEnergyStatement (m : ℕ) : RadiusEnergyStatement m :=
  radiusEnergy (localizationStatement m) (chainSumStatement m)
    (Moments.scalesStatement_holds m)

/-- The first bound of equation `eq:rewardmoment`. -/
theorem rewardMomentStatement (m : ℕ) : RewardMomentStatement.{0} m :=
  rewardMoment (localizationStatement m) (profilesStatement m) (tubeStatement_holds m)
    (Moments.scalesStatement_holds m)

/-- Equation `eq:blocksum`. -/
theorem blockSumStatement (m : ℕ) : BlockSumStatement.{0} m :=
  blockSum (Moments.scalesStatement_holds m)

/-- The second bound of equation `eq:rewardmoment`. -/
theorem blockReplacementStatement (m : ℕ) : BlockReplacementStatement.{0} m :=
  blockReplacement (rewardMomentStatement m) (blockSumStatement m) (chainSumStatement m)

/-- Lemma `lem:labels`. -/
theorem labelsStatement (m : ℕ) : LabelsStatement m :=
  Gain.labelsStatement_of (profilesStatement m) (localizationStatement m) (modulusStatement m)
    (profileDifferenceStatement m) (Geometry.supportStatement m)
    (Moments.scalesStatement_holds m)
    (tubeStatement_holds m)

/-- Lemma `lem:residual`. -/
theorem residualStatement (m : ℕ) : ResidualStatement m :=
  Residual.residualStatement_of (rewardMomentStatement m) (blockSumStatement m)
    (chainSumStatement m)
    (localizationStatement m) (Moments.scalesStatement_holds m) (tubeStatement_holds m)

/-- Lemma `lem:fewtranslates`. -/
theorem fewTranslatesStatement (m : ℕ) : FewTranslatesStatement m :=
  Gain.fewTranslatesStatement_of (rewardMomentStatement m) (blockReplacementStatement m)
    (expArrayStatement m) (radiusEnergyStatement m) (Moments.scalesStatement_holds m)
    (tubeStatement_holds m)

/-- Proposition `prop:gain`. -/
theorem gainStatement (m : ℕ) : GainStatement m :=
  Gain.Printed.gainStatement (labelsStatement m) (residualStatement m)
    (fewTranslatesStatement m)
    Proofs.Modified.modifiedPoincareStatement_holds
    (modulusStatement m) (fixedComparisonStatement m) Chart.roundingStatement_holds

/-! ### Section `sec:mean` and the induction -/

/-- Lemma `lem:smallmean`. -/
theorem smallMeanStatement (m : ℕ) : SmallMeanStatement m :=
  Mean.smallMeanStatement_of (Geometry.supportStatement m) (Moments.scalesStatement_holds m)
    (Geometry.classicalStatement_holds m) (modulusStatement m) (parentStatement m)
    (profileDifferenceStatement m) (Proofs.Arrays.arraysStatement_holds m)
    (Geometry.goodStatement_holds m)
    (slabsStatement_holds m) (Geometry.chainsExistStatement_holds m)

/-- Proposition `prop:induction` for every large `K`. -/
theorem improvementAllKStatement (m : ℕ) : ImprovementAllKStatement m :=
  Mean.improvementAllKStatement_of
    (Mean.ClassicalRangeStatement_of (Geometry.classicalStatement_holds m))
    (Geometry.classicalStatement_holds m)
    (parentStatement m) (gainStatement m) (smallMeanStatement m) Chart.roundingStatement_holds
    signedOsSumStatement_holds

/-- **Proposition `prop:induction`**, in the paper's form: a root, with no hypothesis beyond the
binders of the statement. -/
theorem improvementStatement_holds (m : ℕ) : ImprovementStatement m :=
  improvementStatement_of_allK (improvementAllKStatement m)

/-- Equation `eq:premise` at every length. -/
theorem domainExpStatement_holds (m : ℕ) : DomainExpStatement m :=
  domainExpStatement (improvementAllKStatement m) (baseCaseStatement_holds m)

/-! ### The theorems -/

/-- The choice of coordinates. -/
theorem reductionUniformStatement_holds (m : ℕ) : ReductionUniformStatement m :=
  Reduction.reductionUniformStatement Chart.chartUniformStatement_holds

/-- Theorem `thm:main`. -/
theorem mainExpStatement_holds (m : ℕ) : MainExpStatement m :=
  mainExpStatement (domainExpStatement_holds m) (reductionUniformStatement_holds m)
    (baseCaseStatement_holds m)

/-- The sentence after Theorem `thm:main`. -/
theorem varianceSentenceStatement_holds (m : ℕ) : VarianceSentenceStatement m :=
  varianceSentenceStatement (mainExpStatement_holds m)

/-- The statement of
`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`. -/
theorem mainUniformStatement_holds (m : ℕ) : MainUniformStatement m :=
  mainUniformStatement (varianceSentenceStatement_holds m)

/-- The statement of `CurvatureVariance.evariance_passageTime_floorVertex_le`. -/
theorem mainTheoremStatement_holds (m : ℕ) : MainTheoremStatement m :=
  mainTheoremStatement (domainExpStatement_holds m) (ownBoundsStatement_holds m)
    (Reduction.reductionStatement_holds m) (Reduction.finalTargetStatement_holds m)

/-- **Theorem `thm:main`**, with the statement of
`CurvatureVariance.lintegral_exp_passageTime_le`. -/
theorem lintegral_exp_passageTime_le {m : ℕ} (hm : 1 ≤ m)
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - μ.1 (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 :=
  mainExpStatement_holds m hm F hW P hP μ hμ δ r M c hδ hδ₁ hr hM hc

/-- **The sentence after Theorem `thm:main`**: the bound of the theorem and
`Var[T(0,x)] ≤ 2C²|x|^{1−ε}`, for the same `ε` and `C`. -/
theorem variance_passageTime_le {m : ℕ} (hm : 1 ≤ m)
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - μ.1 (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 ∧
            evariance (fun ω => (passageTime ω 0 x : ℝ)) P ≤
              ENNReal.ofReal (2 * C ^ 2 * ‖point x‖ ^ (1 - ε)) :=
  varianceSentenceStatement_holds m hm F hW P hP μ hμ δ r M c hδ hδ₁ hr hM hc

/-- **The bound at `⌊nξ⌋`, uniform in the direction**, with the statement of
`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`: a corollary of the variance
sentence after Theorem `thm:main`. -/
theorem evariance_passageTime_floorVertex_le_uniform {m : ℕ}
    (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hW : AssumptionW m F)
    (P : Measure (Config m)) [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m)
    (hμ : IsTimeConstant P μ) (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hM : 0 ≤ M)
    (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ n : ℕ, n₀ ≤ n →
        evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P ≤
          ENNReal.ofReal ((n : ℝ) ^ (1 - ε)) :=
  mainUniformStatement_holds m hm F hW P hP μ hμ δ r M c hδ hδ₁ hr hM hc

/-- **The bound at `⌊nξ⌋` at one direction**, with the statement of
`CurvatureVariance.evariance_passageTime_floorVertex_le`: a theorem under `AssumptionCAt`, which is
not in the paper. -/
theorem evariance_passageTime_floorVertex_le {m : ℕ}
    (hm : 1 ≤ m) (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hW : AssumptionW m F)
    (P : Measure (Config m)) [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m)
    (hμ : IsTimeConstant P μ) (ξ : Pt m) (hξ : ξ ≠ 0) (H : Submodule ℝ (Pt m))
    (hH : IsCompl (Submodule.span ℝ {ξ}) H) (hC : AssumptionCAt μ ξ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P ≤
        ENNReal.ofReal ((n : ℝ) ^ (1 - ε)) :=
  mainTheoremStatement_holds m hm F hW P hP μ hμ ξ hξ H hH hC

/-- **The bound (a)** of Section `sec:induction`, in the paper's form: there is `C` such that, for
every `K ≥ 10⁴`, there is `N₀` such that, for every model that fits `bd`, every `N ≥ N₀`, every
`A ≥ 1` with equation `eq:premise` at `N` and the range (`RangeA`), every `ℓ ∈ [N/8, N]` and every
`y ∈ 𝒟(ℓ)`, `E[exp(8 |T − E T| / Q_ℓ)] ≤ C`. A root: no other theorem reaches it. It follows from
Lemma `lem:parent` at `ℓ ≥ N/8` and the integrability of `T`, the first clause of
`ClassicalStatement`. -/
theorem boundA_holds (m : ℕ) (bd : Bounds m) (hbd : bd.Valid) (Cstar : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
    ∀ M : Model m, M.Standing → M.Fits bd → ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
    Premise M K A N → RangeA M K A N Cstar →
    ∀ ℓ : ℕ, (N : ℝ) / 8 ≤ ℓ → ℓ ≤ N → ∀ y ∈ premiseDomain M ℓ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (8 * |passageTimeReal ω 0 ((ℓ : ℤ), y) -
        ∫ ω', passageTimeReal ω' 0 ((ℓ : ℤ), y) ∂M.P| / Q M K A ℓ)) ∂M.P ≤ ENNReal.ofReal C := by
  obtain ⟨Cp, hCp, hP⟩ := parentStatement m bd hbd Cstar
  obtain ⟨Ccl, -, hCl⟩ := Geometry.classicalStatement_holds m bd hbd
  refine ⟨2 * Real.exp (16 * Cp + 1), by positivity, fun K hK => ?_⟩
  obtain ⟨N₀, hP⟩ := hP (1 / 8) (by norm_num) K hK
  refine ⟨max N₀ 8, fun M hM hfit N hN A hA hp hr ℓ hℓ8 hℓN y hy => ?_⟩
  have := hM.probP
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hℓ1 : (1 : ℝ) ≤ ℓ := by linarith only [hℓ8, hN8]
  have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hℓ1]
  have hℓpos : 0 < ℓ := by exact_mod_cast hℓ0
  have hx : ((ℓ : ℤ), y) ≠ (0 : Vertex m) := by
    intro h
    have h₁ := congrArg Prod.fst h
    simp only [Prod.fst_zero] at h₁
    omega
  have hint := (hCl M hM hfit _ hx).1
  have hQ : 0 < Q M K A ℓ := Q_pos M K hA hℓ0
  have hNr : (ℓ : ℝ) ≤ 3 * N := by
    have : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓN
    linarith only [this, hN8]
  have hdom : ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤
      7 / 4 * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
    have h0 : 0 ≤ (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by positivity
    have h1 : ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤ (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := hy
    linarith only [h0, h1]
  have hpar := hP M hM hfit N ((le_max_left _ _).trans hN) A hA hp hr ℓ
    (by linarith only [hℓ8]) hNr y hdom
  exact Mean.lintegral_exp_abs_sub_integral_le hint hQ hCp.le hpar

end CurvatureVariance.Paper.Closing
