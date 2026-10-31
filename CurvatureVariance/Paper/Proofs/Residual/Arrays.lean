/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.LabelResidual.Assembly
public import CurvatureVariance.Paper.Proofs.LabelResidual.Mixture
public import CurvatureVariance.Paper.Proofs.LabelResidual.MixtureArrays
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds

/-!
# Lemma `lem:residual`: the arrays `Y_i`, with the offsets random

The first bound of equation `eq:residual` is proved "with the `a_i` independent of the rest and
included in probabilities and expectations" (the first paragraph of the proof of
[AB26, Lemma 6.3]). In the Lean this is the mixture `offsetMixture Pr` of the laws `Pr σ` over the
offset families `σ`, on the space `(Fin K → Fin m → Fin L) × (Config m × Config m)`.

* `mixtureReward`: the array `Y_i(j,k)`, defined with the resampling at the offsets `a`.
* `iIndepFun_mixtureReward`: the arrays are independent over `i`. This needs that `X_G` depends only
  on `G`, as Lemma `lem:labels` states.
* `measurePreserving_old_offsetMixture`: the old weights have the law of the weights under the
  mixture, so the chain of equation `eq:chainsum` is read off them.
* `offsetAvg_iSup_reward_le`: equation `eq:chainsum`, applied to the arrays `Y_i/θ`, gives
  `E[Σ_i Y_i(x_{i−1}, x_i)] ≤ CθK` if `E[(Y_i(j,k) − θ|j − k|²)₊^{4d}] ≤ θ^{4d}` for all `i, j, k`.

The continuum Lean has the couplings of the blocks of each slab on their own spaces, so it takes the
conditional arrays given the noise in the slab, averaged over the offsets
(the modules `ConditionalRewards` and `AverageRewards` of
`IsotropicVariance.Paper.Proofs.LabelResidual`). Here `labelPairLaw` carries the resampling of all
the blocks at once, with independent slabs, so the arrays are the paper's: `Y_i` itself, with the
`a_i` random. The array step goes through `ChainSumStatement` (equation `eq:chainsum`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Residual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.Contracts
open CurvatureVariance.Paper.Gain.LabelResidual

variable {m : ℕ}

/-- The array `Y_i(j,k)` of slab `i + 1`, with the offsets included in the probability space: at
`(σ, x)`, the reward of the replacement at the offsets `offsetOf σ`. -/
noncomputable def mixtureReward (M : Model m) (K : ℕ) (A : ℝ) (n L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : Fin K) (j k : Fin m → ℤ)
    (z : (Fin K → Fin m → Fin L) × (Config m × Config m)) : ℝ≥0∞ :=
  reward M K A n t Prod.fst (pairNew n (wInt M K A n) L t (offsetOf z.1)) ((i : ℕ) + 1) j k z.2

/-- The array `Y_i(j,k)` is a function of the offset of slab `i + 1` and the pair of weights of
slab `i + 1`. -/
theorem mixtureReward_eq (M : Model m) (K : ℕ) (A : ℝ) (n L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : Fin K) (j k : Fin m → ℤ)
    (z : (Fin K → Fin m → Fin L) × (Config m × Config m)) :
    mixtureReward M K A n L t i j k z =
      rewardFactor M K A n L t ((i : ℕ) + 1) (fun c => ((z.1 i c : ℕ) : ℤ))
        (slabPair n ((i : ℕ) + 1) z.2) j k := by
  rw [mixtureReward, reward_pairNew_eq, offsetOf_succ z.1 i]

theorem measurable_mixtureReward (M : Model m) (K : ℕ) (A : ℝ) (n L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : Fin K) (j k : Fin m → ℤ) :
    Measurable (mixtureReward M K A n L t i j k) := by
  have h := measurable_rewardFactor M K A n L t ((i : ℕ) + 1) (S := Fin m → Fin L)
    (fun s c => ((s c : ℕ) : ℤ)) j k
  have hW : Measurable fun z : (Fin K → Fin m → Fin L) × (Config m × Config m) =>
      (z.1 i, slabPair (m := m) n ((i : ℕ) + 1) z.2) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_slabPair n _).comp measurable_snd)
  convert h.comp hW using 1
  funext z
  exact mixtureReward_eq M K A n L t i j k z

variable {M : Model m} {K : ℕ} {A : ℝ} {n L : ℕ} {t : EuclideanSpace ℝ (Fin m)}
  {Pr : (Fin K → Fin m → Fin L) → Measure (Config m × Config m)}

/-- **The arrays `Y_i` are independent over `i`**, with the offsets random, if the pairs of weights
of the slabs are independent under each `Pr σ` and the law of the pair of slab `i + 1` depends only
on the offset of that slab. -/
theorem iIndepFun_mixtureReward (hL : 1 ≤ L) [∀ σ, IsProbabilityMeasure (Pr σ)]
    (hind : ∀ σ, iIndepFun (fun (i : Fin K) x => slabPair (m := m) n ((i : ℕ) + 1) x) (Pr σ))
    (hloc : ∀ (i : Fin K) σ σ', σ i = σ' i →
      (Pr σ).map (slabPair n ((i : ℕ) + 1)) = (Pr σ').map (slabPair n ((i : ℕ) + 1))) :
    iIndepFun (fun (i : Fin K) z => fun j k => mixtureReward M K A n L t i j k z)
      (offsetMixture Pr) := by
  have hne : Nonempty (Fin m → Fin L) := ⟨fun _ => ⟨0, by omega⟩⟩
  have h := iIndepFun_offsetMixture (Pr := Pr) (U := fun (i : Fin K) x =>
    slabPair (m := m) n ((i : ℕ) + 1) x) (fun i => measurable_slabPair n _) hind hloc
  have hΦ : ∀ i : Fin K, Measurable fun (p : (Fin m → Fin L) ×
      ((slabEdgeSet m n ((i : ℕ) + 1) → ℝ≥0) × (slabEdgeSet m n ((i : ℕ) + 1) → ℝ≥0))) =>
      fun j k => rewardFactor M K A n L t ((i : ℕ) + 1) (fun c => ((p.1 c : ℕ) : ℤ)) p.2 j k :=
    fun i => measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k =>
      measurable_rewardFactor M K A n L t ((i : ℕ) + 1) (S := Fin m → Fin L)
        (fun s c => ((s c : ℕ) : ℤ)) j k
  convert h.comp _ hΦ using 1
  funext i z j k
  exact mixtureReward_eq M K A n L t i j k z

/-- **The old weights have the law of the weights under the mixture.** -/
theorem measurePreserving_old_offsetMixture (hL : 1 ≤ L) [∀ σ, IsProbabilityMeasure (Pr σ)]
    (hold : ∀ σ, (Pr σ).map Prod.fst = M.P) :
    MeasurePreserving (fun z : (Fin K → Fin m → Fin L) × (Config m × Config m) => z.2.1)
      (offsetMixture Pr) M.P := by
  have hne : Nonempty (Fin m → Fin L) := ⟨fun _ => ⟨0, by omega⟩⟩
  have : Nonempty (Fin K → Fin m → Fin L) := ⟨fun _ => hne.some⟩
  have hcard : (Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hπ : Measurable fun z : (Fin K → Fin m → Fin L) × (Config m × Config m) => z.2.1 :=
    measurable_fst.comp measurable_snd
  refine ⟨hπ, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hπ hs, offsetMixture_apply Pr (hπ hs)]
  have h : ∀ σ, Pr σ (Prod.mk σ ⁻¹' ((fun z : (Fin K → Fin m → Fin L) × (Config m × Config m) =>
      z.2.1) ⁻¹' s)) = M.P s := fun σ => by
    rw [← hold σ, Measure.map_apply measurable_fst hs]
    rfl
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  rw [ENNReal.inv_mul_cancel hcard (ENNReal.natCast_ne_top _), one_mul]

/-- **Equation `eq:chainsum`, applied to the arrays `Y_i/θ`** (the first paragraph of the proof of
[AB26, Lemma 6.3]): there is `C`, depending only on the bounds, such that for `N` large depending
only on `K`, every target, every `L ≥ 1` and all replacements `Pr σ` at the offsets `σ` of a
label-pair family, if `E[(Y_i(j,k) − θ|j − k|²)₊^{4d}] ≤ θ^{4d}` for all `i, j, k`, the offsets
being random, then `E[sup_x Σ_i Y_i(x_{i−1}, x_i)] ≤ CθK`, the supremum over the minimizing chains
of the old weights. -/
theorem offsetAvg_iSup_reward_le (hC : ChainSumStatement.{0} m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
    ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → Premise M K A N → RangeA M K A N Cstar →
    ∀ (n ℓ : ℕ) (y : Fin m → ℤ), IsTarget M K N n ℓ y → ∀ L : ℕ, 1 ≤ L →
    ∀ (Pr : (Fin K → Fin m → Fin L) → Measure (Config m × Config m))
      (lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ),
      IsLabelPairFamily M n (wInt M K A n) L K (targetSlope ℓ y) lam Pr →
    ∀ θ : ℝ, 0 < θ →
      (∀ (i : Fin K) (j k : Fin m → ℤ), offsetAvg (fun σ => ∫⁻ x,
          (reward M K A n (targetSlope ℓ y) Prod.fst
              (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1) j k x -
            ENNReal.ofReal (θ * ‖transversePoint (j - k)‖ ^ 2)) ^ (4 * (m + 1)) ∂Pr σ) ≤
        ENNReal.ofReal (θ ^ (4 * (m + 1)))) →
      offsetAvg (fun σ : Fin K → Fin m → Fin L => ∫⁻ x, ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
          (_ : IsMinTuple M x.1 n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y), ∑ i : Fin K,
            reward M K A n (targetSlope ℓ y) Prod.fst
              (pairNew n (wInt M K A n) L (targetSlope ℓ y) (offsetOf σ)) ((i : ℕ) + 1)
              (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.castSucc)
              (tupleIndex n (wInt M K A n) (targetSlope ℓ y) Y i.succ) x ∂Pr σ) ≤
        ENNReal.ofReal (θ * C * K) := by
  obtain ⟨C, hC0, hchain⟩ := hC bd hbd Cstar
  refine ⟨C, hC0, fun K hK => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hchain K hK
  refine ⟨max ((9 * K) ^ 2) N₁, ?_⟩
  intro M hM hfit N hN A hA hprem hrange n ℓ y htar L hL Pr lam hfam θ hθ hmom
  obtain ⟨-, hsqrt, -, -⟩ := Responses.target_size_bounds (by omega : 1 ≤ K)
    ((le_max_left _ _).trans hN) htar
  obtain ⟨hℓK, -, hℓN, hdom⟩ := htar
  subst hℓK
  have := hfam.prob
  have hne : Nonempty (Fin m → Fin L) := ⟨fun _ => ⟨0, by omega⟩⟩
  have : IsProbabilityMeasure (offsetMixture Pr) := isProbabilityMeasure_offsetMixture Pr
  set t := targetSlope (K * n) y with ht
  set p := 4 * (m + 1) with hp
  have hθi : ENNReal.ofReal θ⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hind := iIndepFun_mixtureReward (M := M) (K := K) (A := A) (n := n) (L := L) (t := t)
    (Pr := Pr) hL hfam.ind hfam.loc
  -- the arrays `Y_i/θ`
  set Z : Fin K → (Fin K → Fin m → Fin L) × (Config m × Config m) → (Fin m → ℤ) → (Fin m → ℤ) →
      ℝ≥0∞ := fun i z j k => ENNReal.ofReal θ⁻¹ * mixtureReward M K A n L t i j k z with hZ
  have hZm : ∀ i j k, Measurable fun z => Z i z j k := fun i j k =>
    (measurable_mixtureReward M K A n L t i j k).const_mul _
  have hZind : iIndepFun Z (offsetMixture Pr) := by
    have hev : ∀ j k, Measurable fun f : (Fin m → ℤ) → (Fin m → ℤ) → ℝ≥0∞ => f j k :=
      fun j k => (measurable_pi_apply k).comp (measurable_pi_apply j)
    exact hind.comp (fun _ f j k => ENNReal.ofReal θ⁻¹ * f j k) fun _ =>
      measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => (hev j k).const_mul _
  have hZmom : ∀ i j k, ∫⁻ z, (Z i z j k - ENNReal.ofReal (‖transversePoint (j - k)‖ ^ 2)) ^ p
      ∂offsetMixture Pr ≤ 1 := by
    intro i j k
    set a := ‖transversePoint (j - k)‖ ^ 2 with ha
    have ha0 : 0 ≤ a := by positivity
    have hpt : ∀ z, (Z i z j k - ENNReal.ofReal a) ^ p = ENNReal.ofReal θ⁻¹ ^ p *
        (mixtureReward M K A n L t i j k z - ENNReal.ofReal (θ * a)) ^ p := fun z => by
      rw [← mul_pow, ENNReal.mul_sub fun _ _ => hθi, ← ENNReal.ofReal_mul (by positivity),
        inv_mul_cancel_left₀ hθ.ne']
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hθi), lintegral_offsetMixture]
    have h := hmom i j k
    unfold offsetAvg at h
    calc ENNReal.ofReal θ⁻¹ ^ p * _ ≤ ENNReal.ofReal θ⁻¹ ^ p * ENNReal.ofReal (θ ^ p) :=
          mul_le_mul' le_rfl h
      _ = 1 := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
            inv_mul_cancel₀ hθ.ne', one_pow, ENNReal.ofReal_one]
  have hπ := measurePreserving_old_offsetMixture (M := M) (Pr := Pr) hL
    fun σ => (hfam.repl σ).law_old
  have hdom' : ‖transversePoint y - ((K * n : ℕ) : ℝ) • M.t₀‖ ≤
      2 * ((K * n : ℕ) : ℝ) ^ (1 + (M.δ / 100 - 1 / 4)) := by
    have hexp : 1 + (M.δ / 100 - 1 / 4) = (3 : ℝ) / 4 + M.δ / 100 := by ring
    rw [hexp]
    refine (show _ ≤ _ from hdom).trans ?_
    linarith only [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (K * n))
      ((3 : ℝ) / 4 + M.δ / 100)]
  have hmain := hN₁ M hM hfit N ((le_max_right _ _).trans hN) A hA hprem hrange K n (by omega) hsqrt
    (by
      have h : ((K * n : ℕ) : ℝ) ≤ N := by exact_mod_cast hℓN
      linarith only [h, Nat.cast_nonneg (α := ℝ) N]) y hdom'
    ((Fin K → Fin m → Fin L) × (Config m × Config m)) (offsetMixture Pr) (fun z => z.2.1) hπ Z hZm
    hZind hZmom
  -- the supremum of the arrays `Y_i`
  set G : (Fin K → Fin m → Fin L) × (Config m × Config m) → ℝ≥0∞ := fun z =>
    ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
      (_ : IsMinTuple M z.2.1 n K t 0 (((K * n : ℕ) : ℤ), y) Y), ∑ i : Fin K,
        mixtureReward M K A n L t i (tupleIndex n (wInt M K A n) t Y i.castSucc)
          (tupleIndex n (wInt M K A n) t Y i.succ) z with hG
  have hlhs : offsetAvg (fun σ : Fin K → Fin m → Fin L => ∫⁻ x, ⨆ (Y : Fin (K + 1) → Fin m → ℤ)
      (_ : IsMinTuple M x.1 n K t 0 (((K * n : ℕ) : ℤ), y) Y), ∑ i : Fin K,
        reward M K A n t Prod.fst
          (pairNew n (wInt M K A n) L t (offsetOf σ)) ((i : ℕ) + 1)
          (tupleIndex n (wInt M K A n) t Y i.castSucc)
          (tupleIndex n (wInt M K A n) t Y i.succ) x ∂Pr σ) =
      ∫⁻ z, G z ∂offsetMixture Pr := by
    rw [lintegral_offsetMixture]
    rfl
  have hZG : ∀ z, (⨆ (Y : Fin (K + 1) → Fin m → ℤ)
      (_ : IsMinTuple M z.2.1 n K t 0 (((K * n : ℕ) : ℤ), y) Y), ∑ i : Fin K,
        Z i z (tupleIndex n (wInt M K A n) t Y i.castSucc)
          (tupleIndex n (wInt M K A n) t Y i.succ)) = ENNReal.ofReal θ⁻¹ * G z := fun z => by
    simp only [hZ, hG, ← Finset.mul_sum, ENNReal.mul_iSup]
  have hmain' := (lintegral_congr hZG).symm.le.trans hmain
  rw [lintegral_const_mul' _ _ hθi] at hmain'
  rw [hlhs]
  have hθ1 : ENNReal.ofReal θ * ENNReal.ofReal θ⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hθ.le, mul_inv_cancel₀ hθ.ne', ENNReal.ofReal_one]
  calc ∫⁻ z, G z ∂offsetMixture Pr
      = ENNReal.ofReal θ * (ENNReal.ofReal θ⁻¹ * ∫⁻ z, G z ∂offsetMixture Pr) := by
        rw [← mul_assoc, hθ1, one_mul]
    _ ≤ ENNReal.ofReal θ * ENNReal.ofReal (C * K) := mul_le_mul' le_rfl hmain'
    _ = _ := by
        rw [← ENNReal.ofReal_mul hθ.le, mul_assoc]

end CurvatureVariance.Paper.Proofs.Residual
