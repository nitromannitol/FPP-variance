/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Averaged
public import IsotropicVariance.Paper.Defs.Resampling

/-!
# Statements of Section `sec:gain`, part 2: the labels, the residual, the gain

Notation: `n = ℓ/K`, `(nQ_n)^{1/2}` is `W K A n`; `F̄` is `Proofs.Gain.averagedMin`, `f` is
`X.labelMean`, and `Λ` is a family of labels of all the blocks `(i, z)` (`X.LabelFamily`).
`Setting.blockResampling` is the joint law of the noise and of its resamplings. Lean slabs are
0-based: the faces of the block `(i, z)` are `{in}` and `{(i+1)n}`.

* `Proofs.Gain.IsCovariantAE`, `Proofs.Gain.LabelProfileBound`: one translated rule, and equation
  `eq:labelprofile` at an error `ε`, which the statements below share.
* `LabelsStatement`: Lemma `lem:labels`.
* `ResidualStatement`: Lemma `lem:residual`.
* `FewTranslatesStatement`: Lemma `lem:fewtranslates`.
* `GainStatement`: Proposition `prop:gain`.

Proposition `prop:gain` is proved by
`IsotropicVariance.Paper.Proofs.Gain.gainStatement_of_contracts`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

/-- **One translated rule, almost surely** (Lemma `lem:labels`: "for every block `G` of the `i`th
slab and every `τ` orthogonal to `e₁` such that `G+τ` is a block, `X_{G+τ}(u+τ, v+τ)`, computed with
`ω` translated by `τ`, equals `X_G(u, v)`"): for two blocks `(i, z)` and `(i, z')` of one slab and
one choice of the offset, so that `z' − z` is a multiple of `L` in each coordinate, moving the noise
by the translation between their corners moves the label of `(i, z)` to the label of `(i, z')`,
almost surely. The labels are random variables of the noise interface, chosen measurable for the
information of their blocks, so the equality holds up to null sets. -/
def IsCovariantAE {m : ℕ} {X : Setting.{u} m} (Λ : X.LabelFamily) (n W : ℝ) (L : ℕ) : Prop :=
  ∀ (i : ℕ) (z z' : Fin m → ℤ), (∀ k, (L : ℤ) ∣ z' k - z k) → ∀ᵐ ω ∂X.P,
    Λ.label i z' (X.act (AffineIsometryEquiv.constVAdd ℝ (Pt m)
      (blockCorner n W i z' - blockCorner n W i z)) ω) = Λ.label i z ω

/-- The bound `eq:labelprofile` at an error `ε` for the label family `Λ` of the blocks of side
`L W_n`, `n = ℓ/K`: for every slab `i < K` and block `z`,
`‖sup_{u, v} |(D_i(u, v) − n)/Q_n − X_G(u − corner, v − corner)|‖_{8d} ≤ ε`, the supremum over the
cores of the two faces taken in `[0, ∞]` (a real supremum is `0` for a family unbounded above;
`eLpNorm` of a non-measurable function is `∞`, so the bound also asserts measurability). -/
def LabelProfileBound {m : ℕ} (X : Setting.{u} m) (b : ℝ) (K : ℕ) (A ℓ : ℝ) (L : ℕ)
    (Λ : X.LabelFamily) (ε : ℝ) : Prop :=
  ∀ i : ℕ, i < K → ∀ z : Fin m → ℤ,
    eLpNorm (fun ω => ⨆ (u : coreFace (ℓ / K) (W K A (ℓ / K)) L i z)
        (v : coreFace (ℓ / K) (W K A (ℓ / K)) L (i + 1) z),
        ENNReal.ofReal |(X.slabTime b (chainSlab (ℓ / K) 0 i) ω u v - ℓ / K) / Q K A (ℓ / K) -
          Λ.value (Λ.label i z ω) ((u : Pt m) - blockCorner (ℓ / K) (W K A (ℓ / K)) i z)
            ((v : Pt m) - blockCorner (ℓ / K) (W K A (ℓ / K)) i z)|)
      (8 * (m + 1) : ℝ≥0∞) X.P ≤ ENNReal.ofReal ε

end IsotropicVariance.Paper.Proofs.Gain

namespace IsotropicVariance.Paper.Contracts

/-- **Lemma `lem:labels`, equation `eq:labelprofile`**: there are
`α_L > 0` and `δ_L → 0`, depending only on `L` and the setting, such that for `K ≥ 10`, `L ≥ 16` and
`N` large depending on `K` and `L`, every `ℓ = Kn ∈ [N/8, N]` has labels `X_G` of all the blocks of
side `L(nQ_n)^{1/2}`: each determined by the noise in its block, with values in a finite set of
bounded functions of the endpoints, each taken with probability zero or at least `α_L`, given by
one translated rule, with equation `eq:labelprofile` at the error `δ_L`.

Readings:
* one family `Λ` is indexed by all the blocks `(i, z)`, so it serves every choice of the offsets,
  and a value of `Λ` is a function of the endpoints relative to the corner of the block;
* the covariance is the paper's clause, for two blocks of one slab and one choice of the offset,
  and it holds almost surely (`Proofs.Gain.IsCovariantAE`). The noise interface only gives versions
  of the passage times measurable for the information of a block, so the labels, and the rule, are
  defined up to null sets;
* the independence of the labels of distinct blocks is not a clause: it follows from
  `Λ.IsDetermined` and `NoiseModel.iIndep_info`;
* `b` is any deterministic upper bound of the density. -/
def LabelsStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ α δ : ℕ → ℝ, (∀ L, 0 < α L) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ K : ℕ, 10 ≤ K → ∀ L : ℕ, 16 ≤ L → ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N →
        Standing X Cstar K A N → ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N →
          ∃ Λ : X.LabelFamily, Λ.IsDetermined (ℓ / K) (W K A (ℓ / K)) L ∧
            Λ.HasBoundedValues ∧ Λ.AtomsGe (α L) ∧
            Proofs.Gain.IsCovariantAE Λ (ℓ / K) (W K A (ℓ / K)) L ∧
            Proofs.Gain.LabelProfileBound X b K A ℓ L Λ (δ L)

/-- **Lemma `lem:residual`**: for `L ≥ 16`, `ω^G` the resampling
of `G` with `σ_G = X_G`, and `N` large depending on `K` and `L`, equation
`eq:residual`, `L^{−K(d−1)} Σ_a Σ_G E[(F^G − F)²] ≤ δ_L K Q_n²` and
`L^{−K(d−1)} Σ_a E[Var[F̄ | (X_G)_G]] ≤ δ_L K Q_n²`, where `a = (a_1, …, a_K)` ranges over
`({0, …, L − 1}^{d−1})^K`.

Here `E[Var[F̄ | (X_G)_G]]` is `E[(F̄ − E[F̄ | (X_G)_G])²]`, and the sums are in `[0, ∞]`.

Which labels: the paper fixes the `X_G` of Lemma `lem:labels`. The statement takes every label
family that is determined, satisfies equation `eq:labelprofile` at an error `ε`, and is given by one
translated rule, with `G ε L` small when `ε` is small and `L` is large. The paper's statement is
the instance `ε = δ_L` of `LabelsStatement` (made positive), and then `G (δ_L) L → 0` is the `δ_L`
of this lemma. This is stronger in the error, and it assumes only what the proof uses: the rule is
used for the second bound (proof of Lemma `lem:residual`, "the `X_G` of a block to that of the
translated block"), and neither the bound on the values nor the atoms are used. -/
def ResidualStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ G : ℝ → ℕ → ℝ,
      (∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₀ : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ L : ℕ, L₀ ≤ L → G ε L ≤ η) ∧
      ∀ K : ℕ, 10 ≤ K → ∀ L : ℕ, 16 ≤ L → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N →
        Standing X Cstar K A N → ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N →
          ∀ Λ : X.LabelFamily, Λ.IsDetermined (ℓ / K) (W K A (ℓ / K)) L →
            Proofs.Gain.IsCovariantAE Λ (ℓ / K) (W K A (ℓ / K)) L →
            Proofs.Gain.LabelProfileBound X b K A ℓ L Λ ε →
            ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o : Fin K → Fin m → Fin L,
                ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
                  ∫⁻ p, ENNReal.ofReal ((X.F b K (ℓ / K) 0 (p.2 ((i : ℕ), (z : Fin m → ℤ))) -
                      X.F b K (ℓ / K) 0 p.1) ^ 2)
                    ∂X.blockResampling (ℓ / K) (W K A (ℓ / K)) L (fun p => Λ.sigma p.1 p.2) ≤
              ENNReal.ofReal (G ε L * K * Q K A (ℓ / K) ^ 2) ∧
            ((L : ℝ≥0∞) ^ (m * K))⁻¹ * ∑ o : Fin K → Fin m → Fin L,
                ∫⁻ ω, ENNReal.ofReal
                  ((Proofs.Gain.averagedMin X b K (ℓ / K) (W K A (ℓ / K)) L ω -
                    X.P[Proofs.Gain.averagedMin X b K (ℓ / K) (W K A (ℓ / K)) L |
                      Λ.allSigma K o] ω) ^ 2) ∂X.P ≤
              ENNReal.ofReal (G ε L * K * Q K A (ℓ / K) ^ 2)

/-- **Lemma `lem:fewtranslates`**: there is `C`, independent of `K` and
`L`, such that for `K ≥ 10`, `L ≥ 16`, `N` large depending on `K` and `L`, every family of labels
determined by the noise in their blocks and all offsets `a_i`, for `f = E[F̄ | (X_G)_G]`,
`Σ_G E[(f − E_G[f])²] ≤ C K Q_n²` and `Σ_G E[|f − E_G[f]|]² ≤ C K^{−1/6} K Q_n²`, the sums over the
blocks of all `K` slabs, in `[0, ∞]`, written with the `L²` and `L¹` norms.

`E_G[f]` is the expectation of `f` with respect to `X_G` alone (the text before Lemma
`lem:residual`), which on the noise is `X.P[f | Λ.otherSigma K o i z]` (module
`IsotropicVariance.Paper.Defs.Averaged`). The paper fixes the `X_G` of Lemma `lem:labels`; its
proof uses only that they are determined by the noise in their blocks, so the statement is for
every such family, which is stronger. -/
def FewTranslatesStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
    ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 10 ≤ K → ∀ L : ℕ, 16 ≤ L →
      ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N →
        ∀ Λ : X.LabelFamily, Λ.IsDetermined (ℓ / K) (W K A (ℓ / K)) L →
          ∀ o : Fin K → Fin m → Fin L,
            ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
                eLpNorm (X.labelMean b K (ℓ / K) (W K A (ℓ / K)) Λ o -
                  X.P[X.labelMean b K (ℓ / K) (W K A (ℓ / K)) Λ o |
                    Λ.otherSigma K o i z]) 2 X.P ^ 2 ≤
              ENNReal.ofReal (C * K * Q K A (ℓ / K) ^ 2) ∧
            ∑ i : Fin K, ∑' z : {z : Fin m → ℤ | IsBlockIndex L (o i) z},
                eLpNorm (X.labelMean b K (ℓ / K) (W K A (ℓ / K)) Λ o -
                  X.P[X.labelMean b K (ℓ / K) (W K A (ℓ / K)) Λ o |
                    Λ.otherSigma K o i z]) 1 X.P ^ 2 ≤
              ENNReal.ofReal (C * (K : ℝ) ^ (-(1 : ℝ) / 6) * K * Q K A (ℓ / K) ^ 2)

/-- **Proposition `prop:gain`** (the gain): there are
`o(K) → 0` (depending on the setting only) and `K₀` such that for every `K ≥ K₀` and `N` large
depending on `K`, `Var T_ℓ ≤ o(K) Q_ℓ²` for every `ℓ ∈ [N/8, N]`, uniformly in `A ≥ 1`. The paper
states `Var[T_{Kn}] ≤ δ_K Q_{Kn}²` for every `n` with `Kn ∈ [N/8, N]`, which is this statement at
`ℓ = Kn`. The paper fixes `A` in the standing hypotheses; here the threshold for `N` is explicitly
independent of `A`, as the proof gives and the induction of Section `sec:completion` needs. -/
def GainStatement : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ Cstar : ℝ, 0 < Cstar →
    ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → 10 ≤ K →
      ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ ℓ : ℝ, N / 8 ≤ ℓ → ℓ ≤ N →
        evariance (X.TRV ℓ) X.P ≤ ENNReal.ofReal (o K * Q K A ℓ ^ 2)

end IsotropicVariance.Paper.Contracts
