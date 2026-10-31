/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Residual.Arrays
import CurvatureVariance.Paper.Proofs.LabelResidual.Small
import CurvatureVariance.Paper.Proofs.ReplacementResponses.Arrays
import CurvatureVariance.Paper.Proofs.Responses.RadiusArrays
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Lemma `lem:residual`: the event `E`

The proof of Lemma `lem:residual`: the event `E` of the proof of [AB26, Lemma 6.3] "becomes the
event that `R_i(j,k) > L^{1/2}` or that some `z ∈ ℤ^{d−1}` with
`|z − j| ≤ C(1 + |j − k| + L^{1/2})` lies outside `j_G + {⌈L^{1/2}⌉, …, L − 1 − ⌈L^{1/2}⌉}^{d−1}`,
where `G` is the block that contains the cell `j`" and "Lemma `lem:localization` and Markov's
inequality give `P[E] ≤ C(1 + |j − k| + L^{1/2})/L`".

"Off `E`, only `G` contributes to `Y_i(j,k)`, and the cubes `I_{i−1}(j)` and `I_i(k)` lie in the
region of equation `eq:labelprofile`" and the two terms of the display are bounded by equation
`eq:labelprofile` (the second paragraph of the proof of [AB26, Lemma 6.3]). "On `E`, we use
Hölder's inequality and equation `eq:rewardmoment`."

* The ball `{z : |z − j| ≤ r}` is `tubeIndices j j r` (`mem_tubeIndices_self_iff`). It contains the
  tube of radius `r₀` about `[j, k]` if `|j − k| + r₀ ≤ r` (`tubeIndices_subset_ball`).
* `residualEvent`: the event `E`, on the mixture of `Residual.Arrays`. Its second clause reads "the
  ball lies in the core of no block". This is the paper's clause, since a ball that lies in the core
  of a block `g` contains `j`, so `g` is the block of `j`.
* `lintegral_reward_pow_le_add_of_ball_subset`: at an offset for which the ball lies in the core of
  a block, `E[Y^{4d}] ≤ 2^{8d+1} ε^{8d} + E[Y^{4d}; R_i(j,k) > L^{1/2}]`, with the Hölder step
  taken on `E`.
* `offsetAvg_reward_pow_le`: `E[Y^{4d}] ≤ 2^{8d+1} ε^{8d} + (C(1 + |j − k|))^{4d} P[E]^{3/4}`, the
  offsets being random.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.Residual

open CurvatureVariance.Paper CurvatureVariance.Paper.Gain CurvatureVariance.Paper.Contracts
open CurvatureVariance.Paper.Gain.LabelResidual

variable {m : ℕ}

/-! ### The ball -/

/-- `tubeIndices j j r` is the ball `{z : |z − j| ≤ r}`. -/
theorem mem_tubeIndices_self_iff {j z : Fin m → ℤ} {r : ℝ} (hr : 0 ≤ r) :
    z ∈ tubeIndices j j (ENNReal.ofReal r) ↔ ‖transversePoint (z - j)‖ ≤ r := by
  change ENNReal.ofReal (Metric.infDist (transversePoint z)
    (segment ℝ (transversePoint j) (transversePoint j))) ≤ ENNReal.ofReal r ↔ _
  rw [segment_same, Metric.infDist_singleton, ENNReal.ofReal_le_ofReal_iff hr, dist_eq_norm,
    Infra.FPP.transversePoint_sub]

/-- The tube of radius `r₀` about `[j, k]` lies in the ball of radius `r ≥ |j − k| + r₀` about
`j`. -/
theorem tubeIndices_subset_ball {j k : Fin m → ℤ} {r₀ r : ℝ} (hr₀ : 0 ≤ r₀)
    (hr : ‖transversePoint (j - k)‖ + r₀ ≤ r) :
    tubeIndices j k (ENNReal.ofReal r₀) ⊆ tubeIndices j j (ENNReal.ofReal r) := by
  intro z hz
  have hd : Metric.infDist (transversePoint z)
      (segment ℝ (transversePoint j) (transversePoint k)) ≤ r₀ :=
    (ENNReal.ofReal_le_ofReal_iff hr₀).1 hz
  have hne : (segment ℝ (transversePoint j) (transversePoint k)).Nonempty :=
    ⟨_, left_mem_segment ℝ _ _⟩
  have ha0 := norm_nonneg (transversePoint (j - k))
  have hjk : dist (transversePoint j) (transversePoint k) = ‖transversePoint (j - k)‖ := by
    rw [dist_eq_norm, Infra.FPP.transversePoint_sub]
  have hlow : dist (transversePoint z) (transversePoint j) - ‖transversePoint (j - k)‖ ≤
      Metric.infDist (transversePoint z) (segment ℝ (transversePoint j) (transversePoint k)) := by
    refine (Metric.le_infDist hne).2 fun y hy => ?_
    have h1 := dist_add_dist_of_mem_segment hy
    have h2 := dist_triangle (transversePoint z) y (transversePoint j)
    have h3 := dist_nonneg (x := y) (y := transversePoint k)
    have h4 := dist_comm y (transversePoint j)
    linarith only [h1, h2, h3, h4, hjk]
  rw [mem_tubeIndices_self_iff (by linarith only [ha0, hr₀, hr])]
  rw [Infra.FPP.transversePoint_sub, ← dist_eq_norm]
  linarith only [hlow, hd, hr]

/-! ### One offset -/

/-- **Off `E`, at one offset** (the second paragraph of the proof of [AB26, Lemma 6.3]): for a
replacement whose new weights of the block `g₀` of slab `i` keep a label of the block at error `ε`,
if the ball of radius `r` about `j` lies in the core of `g₀`, with `|j − k| + L^{1/2} ≤ r` and
`|j − k| + m^{1/2} ≤ r`, then `E[Y^{4d}] ≤ 2^{8d+1} ε^{8d} + E[Y^{4d}; R_i(j,k) > L^{1/2}]`. -/
theorem lintegral_reward_pow_le_add_of_ball_subset {M : Model m} {K : ℕ} {A : ℝ} {n L : ℕ}
    (hL : 1 ≤ L) {t : EuclideanSpace ℝ (Fin m)} {P : Pt m} {o : ℕ → Fin m → ℤ} {Ω : Type*}
    [MeasurableSpace Ω] {Pr : Measure Ω} {old : Ω → Config m}
    {new : ℕ → (Fin m → ℤ) → Ω → Config m}
    (hR : IsSlabReplacement M Pr n K (wInt M K A n) L t o old new) (hQ : 0 < Q M K A n)
    (hw : 0 < wInt M K A n) {i : ℕ} {j k : Fin m → ℤ} {Cd : ℝ}
    (hgeo : ∀ᵐ ω ∂M.P, ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j,
      ∀ v ∈ rowCube n (wInt M K A n) t i k,
      (∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ) ∧
      ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
        ∀ e ∈ γ.edges, fineIndex (wInt M K A n) t (edgeMid e) ∈
          tubeIndices j k (slabRadius M K A Cd ω n t i j k))
    {r : ℝ} (hrL : ‖transversePoint (j - k)‖ + Real.sqrt L ≤ r)
    (hrm : ‖transversePoint (j - k)‖ + Real.sqrt m ≤ r) {g₀ : Fin m → ℤ}
    (hg₀ : tubeIndices j j (ENNReal.ofReal r) ⊆ subIndices L (o i) g₀)
    {ε : ℝ} {lam : Config m → Vertex m → Vertex m → ℝ}
    (hlab : IsBlockLabel M K A L n t P i (o i) g₀ ε lam)
    (hpres : ∀ᵐ x ∂Pr, lam (new i g₀ x) = lam (old x)) :
    ∫⁻ x, reward M K A n t old new i j k x ^ (4 * (m + 1)) ∂Pr ≤
      ENNReal.ofReal (2 ^ (8 * (m + 1) + 1) * ε ^ (8 * (m + 1))) +
        ∫⁻ x, {x | ENNReal.ofReal (Real.sqrt L) <
          slabRadius M K A Cd (old x) n t i j k}.indicator
            (fun x => reward M K A n t old new i j k x ^ (4 * (m + 1))) x ∂Pr := by
  have hPr : IsProbabilityMeasure Pr := hR.prob
  obtain ⟨X, hXp, hXae⟩ := hlab.approx
  set Y : Ω → ℝ≥0∞ := fun x => reward M K A n t old new i j k x with hYdef
  set B : Set Ω := {x | ENNReal.ofReal (Real.sqrt L) <
    slabRadius M K A Cd (old x) n t i j k} with hBdef
  have hBm : MeasurableSet B := measurableSet_lt measurable_const
    ((Responses.measurable_slabRadius M K A Cd n t i j k).comp hR.measurable_old)
  have hYm : Measurable Y :=
    ReplacementResponses.measurable_reward M K A n t hR.measurable_old hR.measurable_new i j k
  set a₁ : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (X (new i g₀ x)) with ha₁
  set a₂ : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (X (old x)) with ha₂
  have hsq0 := Real.sqrt_nonneg (m : ℝ)
  have hsL0 := Real.sqrt_nonneg (L : ℝ)
  have ha0 := norm_nonneg (transversePoint (j - k))
  have hr₁ : Real.sqrt m ≤ r := by linarith only [hrm, ha0]
  -- off the event
  have hgood : ∀ᵐ x ∂Pr, x ∉ B → Y x ≤ (a₁ x + a₂ x) ^ 2 := by
    filter_upwards [IsSlabReplacement.ae_old hR hgeo, IsSlabReplacement.ae_old hR hXae,
      IsSlabReplacement.ae_new hR hXae, hpres] with x h1 h2 h3 h4 hxB
    have hrad : slabRadius M K A Cd (old x) n t i j k ≤ ENNReal.ofReal (Real.sqrt L) :=
      not_lt.1 hxB
    refine (reward_le_rewardSum M K A n t old new i j k x).trans ?_
    exact rewardSum_le_of_subset_subIndices hL hQ hw (S := tubeIndices j j (ENNReal.ofReal r))
      (fun g e he => hR.agree i g x e he) (fun u hu v hv => (h1 u hu v hv).1)
      (fun u hu v hv γ hγ e he => tubeIndices_subset_ball hsL0 hrL
        (tubeIndices_mono j k hrad ((h1 u hu v hv).2 γ hγ e he)))
      (fun u hu => fineIndex_mem_tubeIndices_left hw hr₁ hu)
      (fun v hv => tubeIndices_subset_ball hsq0 hrm
        (fineIndex_mem_tubeIndices_right hw le_rfl hv)) hg₀ h2 (h3 i g₀) h4
  -- pointwise: off the event and on the event
  have hpt : ∀ᵐ x ∂Pr, Y x ^ (4 * (m + 1)) ≤
      (a₁ x + a₂ x) ^ (8 * (m + 1)) + B.indicator (fun x => Y x ^ (4 * (m + 1))) x := by
    filter_upwards [hgood] with x hx
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem hxB]
      exact le_add_self
    · rw [Set.indicator_of_notMem hxB, add_zero]
      calc Y x ^ (4 * (m + 1)) ≤ ((a₁ x + a₂ x) ^ 2) ^ (4 * (m + 1)) :=
            pow_le_pow_left₀ bot_le (hx hxB) _
        _ = (a₁ x + a₂ x) ^ (8 * (m + 1)) := by
            rw [← pow_mul]
            congr 1
            ring
  -- the two terms of the display, by equation `eq:labelprofile`
  have hN0 : 8 * (m + 1) ≠ 0 := by omega
  have hX1 : ∫⁻ x, a₁ x ^ (8 * (m + 1)) ∂Pr ≤ ENNReal.ofReal ε ^ (8 * (m + 1)) :=
    lintegral_ofReal_comp_pow_le (hR.measurable_new i g₀) (IsSlabReplacement.map_new hR i g₀)
      hN0 hXp
  have hX2 : ∫⁻ x, a₂ x ^ (8 * (m + 1)) ∂Pr ≤ ENNReal.ofReal ε ^ (8 * (m + 1)) :=
    lintegral_ofReal_comp_pow_le hR.measurable_old hR.law_old hN0 hXp
  have hXsm : AEStronglyMeasurable X M.P :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXp)
  have ha₁m : AEMeasurable a₁ Pr := by
    have hm : AEMeasurable (fun y => ENNReal.ofReal (X y)) (Pr.map (new i g₀)) := by
      rw [IsSlabReplacement.map_new hR i g₀]
      exact hXsm.aemeasurable.ennreal_ofReal
    exact hm.comp_aemeasurable (hR.measurable_new i g₀).aemeasurable
  have h2pow : ENNReal.ofReal ((2 : ℝ) ^ (8 * (m + 1) + 1)) = 2 ^ (8 * (m + 1) + 1) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hgoodint : ∫⁻ x, (a₁ x + a₂ x) ^ (8 * (m + 1)) ∂Pr ≤
      ENNReal.ofReal (2 ^ (8 * (m + 1) + 1) * ε ^ (8 * (m + 1))) := by
    calc ∫⁻ x, (a₁ x + a₂ x) ^ (8 * (m + 1)) ∂Pr
        ≤ ∫⁻ x, 2 ^ (8 * (m + 1)) * (a₁ x ^ (8 * (m + 1)) + a₂ x ^ (8 * (m + 1))) ∂Pr :=
          lintegral_mono fun x => add_pow_le_two_pow_mul _ _ _
      _ = 2 ^ (8 * (m + 1)) *
          (∫⁻ x, a₁ x ^ (8 * (m + 1)) ∂Pr + ∫⁻ x, a₂ x ^ (8 * (m + 1)) ∂Pr) := by
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
            lintegral_add_left' (ha₁m.pow_const _)]
      _ ≤ 2 ^ (8 * (m + 1)) *
          (ENNReal.ofReal (ε ^ (8 * (m + 1))) + ENNReal.ofReal (ε ^ (8 * (m + 1)))) := by
          gcongr
          · exact hX1.trans (ofReal_pow_le_ofReal_pow ε hN0)
          · exact hX2.trans (ofReal_pow_le_ofReal_pow ε hN0)
      _ = ENNReal.ofReal (2 ^ (8 * (m + 1) + 1) * ε ^ (8 * (m + 1))) := by
          rw [ENNReal.ofReal_mul (by positivity), h2pow, pow_succ, mul_assoc, two_mul]
  calc ∫⁻ x, reward M K A n t old new i j k x ^ (4 * (m + 1)) ∂Pr
      ≤ ∫⁻ x, ((a₁ x + a₂ x) ^ (8 * (m + 1)) +
          B.indicator (fun x => Y x ^ (4 * (m + 1))) x) ∂Pr :=
        lintegral_mono_ae hpt
    _ = ∫⁻ x, (a₁ x + a₂ x) ^ (8 * (m + 1)) ∂Pr +
          ∫⁻ x, B.indicator (fun x => Y x ^ (4 * (m + 1))) x ∂Pr :=
        lintegral_add_right' _ ((hYm.pow_const _).indicator hBm).aemeasurable
    _ ≤ _ := add_le_add hgoodint le_rfl

/-! ### The event, with the offsets random -/

/-- **The event `E`** of the proof of Lemma `lem:residual` for `Y_i(j,k)`, `i` the slab `i + 1`, on
the mixture over the offsets: `R_i(j,k) > L^{1/2}`, or the ball of radius `r` about `j` lies in the
core of no block. -/
def residualEvent (M : Model m) (K : ℕ) (A Cd : ℝ) (n L : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (i : Fin K) (j k : Fin m → ℤ) (r : ℝ) :
    Set ((Fin K → Fin m → Fin L) × (Config m × Config m)) :=
  {z | ENNReal.ofReal (Real.sqrt L) < slabRadius M K A Cd z.2.1 n t ((i : ℕ) + 1) j k ∨
    ¬∃ g, tubeIndices j j (ENNReal.ofReal r) ⊆ subIndices L (offsetOf z.1 ((i : ℕ) + 1)) g}

/-- The bound `m (⌈2r⌉ + 2⌈L^{1/2}⌉)/L` for the fraction of the offsets of one slab for which the
ball of radius `r` lies in the core of no block. -/
noncomputable def offsetFraction (m L : ℕ) (r : ℝ) : ℝ :=
  m * ((⌈2 * r⌉ : ℤ) + 2 * ⌈Real.sqrt L⌉₊) / L

variable {M : Model m} {K : ℕ} {A : ℝ} {n L : ℕ} {t : EuclideanSpace ℝ (Fin m)}
  {Pr : (Fin K → Fin m → Fin L) → Measure (Config m × Config m)}

theorem measurableSet_residualEvent (M : Model m) (K : ℕ) (A Cd : ℝ) (n L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : Fin K) (j k : Fin m → ℤ) (r : ℝ) :
    MeasurableSet (residualEvent M K A Cd n L t i j k r) := by
  have h1 : MeasurableSet {z : (Fin K → Fin m → Fin L) × (Config m × Config m) |
      ENNReal.ofReal (Real.sqrt L) < slabRadius M K A Cd z.2.1 n t ((i : ℕ) + 1) j k} :=
    measurableSet_lt measurable_const
      ((Responses.measurable_slabRadius M K A Cd n t _ j k).comp
        (measurable_fst.comp measurable_snd))
  have h2 : MeasurableSet {z : (Fin K → Fin m → Fin L) × (Config m × Config m) |
      ¬∃ g, tubeIndices j j (ENNReal.ofReal r) ⊆ subIndices L (offsetOf z.1 ((i : ℕ) + 1)) g} :=
    measurable_fst (show MeasurableSet {σ : Fin K → Fin m → Fin L |
      ¬∃ g, tubeIndices j j (ENNReal.ofReal r) ⊆ subIndices L (offsetOf σ ((i : ℕ) + 1)) g} from
      (Set.to_countable _).measurableSet)
  exact h1.union h2

/-- **The probability of `E`** (the proof of Lemma `lem:residual`): at most the tail of `R_i(j,k)`
at `L^{1/2}` plus the fraction of the offsets of slab `i` for which the ball lies in the core of no
block. -/
theorem measure_residualEvent_le (hL : 1 ≤ L) [∀ σ, IsProbabilityMeasure (Pr σ)]
    (hold : ∀ σ, (Pr σ).map Prod.fst = M.P) {Cd : ℝ} (i : Fin K) (j k : Fin m → ℤ) {r : ℝ}
    (hr : 0 ≤ r) :
    offsetMixture Pr (residualEvent M K A Cd n L t i j k r) ≤
      M.P {ω | ENNReal.ofReal (Real.sqrt L) < slabRadius M K A Cd ω n t ((i : ℕ) + 1) j k} +
        ENNReal.ofReal (offsetFraction m L r) := by
  classical
  have hπ := measurePreserving_old_offsetMixture (M := M) (Pr := Pr) hL hold
  have hS : MeasurableSet {ω : Config m | ENNReal.ofReal (Real.sqrt L) <
      slabRadius M K A Cd ω n t ((i : ℕ) + 1) j k} :=
    measurableSet_lt measurable_const (Responses.measurable_slabRadius M K A Cd n t _ j k)
  set E₂ : Set ((Fin K → Fin m → Fin L) × (Config m × Config m)) := {z |
      ¬∃ g, tubeIndices j j (ENNReal.ofReal r) ⊆ subIndices L (offsetOf z.1 ((i : ℕ) + 1)) g}
    with hE₂
  have hE₂m : MeasurableSet E₂ :=
    measurable_fst (show MeasurableSet {σ : Fin K → Fin m → Fin L |
      ¬∃ g, tubeIndices j j (ENNReal.ofReal r) ⊆ subIndices L (offsetOf σ ((i : ℕ) + 1)) g} from
      (Set.to_countable _).measurableSet)
  have hsub : residualEvent M K A Cd n L t i j k r ⊆
      (fun z : (Fin K → Fin m → Fin L) × (Config m × Config m) => z.2.1) ⁻¹'
        {ω | ENNReal.ofReal (Real.sqrt L) < slabRadius M K A Cd ω n t ((i : ℕ) + 1) j k} ∪ E₂ :=
    fun z hz => hz
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hπ.measure_preimage hS.nullMeasurableSet]
  refine add_le_add le_rfl ?_
  -- the offsets
  set bad : (Fin m → Fin L) → ℝ≥0∞ := fun s =>
    if ∃ g, tubeIndices j j (ENNReal.ofReal r) ⊆ subIndices L (fun c => ((s c : ℕ) : ℤ)) g
      then 0 else 1 with hbad
  have hsec : ∀ σ : Fin K → Fin m → Fin L, Pr σ (Prod.mk σ ⁻¹' E₂) = bad (σ i) := by
    intro σ
    by_cases h : ∃ g, tubeIndices j j (ENNReal.ofReal r) ⊆
        subIndices L (fun c => ((σ i c : ℕ) : ℤ)) g
    · have he : Prod.mk σ ⁻¹' E₂ = ∅ := by
        ext x
        simp only [mem_preimage, hE₂, mem_ofPred_eq, offsetOf_succ σ i, not_not,
          mem_empty_iff_false, iff_false]
        exact h
      rw [he, measure_empty, hbad]
      simp only [h, ite_true]
    · have he : Prod.mk σ ⁻¹' E₂ = univ := by
        ext x
        simp only [mem_preimage, hE₂, mem_ofPred_eq, offsetOf_succ σ i, mem_univ, iff_true]
        exact h
      rw [he, measure_univ, hbad]
      simp only [h, ite_false]
  rw [offsetMixture_apply Pr hE₂m]
  simp_rw [hsec]
  rw [avg_comp_eval hL i bad]
  have hcard : (Fintype.card (Fin m → Fin L) : ℝ≥0∞) = (L : ℝ≥0∞) ^ m := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [hcard]
  refine (avg_offsets_not_subset_tube_le hL j j hr (s := ⌈2 * r⌉) ?_).trans_eq ?_
  · rw [sub_self, show transversePoint (0 : Fin m → ℤ) = 0 by ext; simp [transversePoint],
      norm_zero, zero_add]
    exact Int.le_ceil _
  · rfl

/-- **The moment off and on `E`** (the second paragraph of the proof of [AB26, Lemma 6.3]): the
offsets being random,
`E[Y_i(j,k)^{4d}] ≤ 2^{8d+1} ε^{8d} + (C(1 + |j − k|))^{4d} P[E]^{3/4}`. Off `E` only the block of
`j` contributes, by the tube property, and equation `eq:labelprofile` bounds the two terms of the
display; on `E` this is Hölder's inequality with equation `eq:rewardmoment`. -/
theorem offsetAvg_reward_pow_le (hL : 1 ≤ L) {P : Pt m}
    {lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ}
    (hfam : IsLabelPairFamily M n (wInt M K A n) L K t lam Pr) (hQ : 0 < Q M K A n)
    (hw : 0 < wInt M K A n) {ε : ℝ}
    (hlab : ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ o g : Fin m → ℤ, (∀ k, 0 ≤ o k ∧ o k < L) →
      IsBlockLabel M K A L n t P i o g ε (lam i o g))
    (i : Fin K) {j k : Fin m → ℤ} {Cd : ℝ}
    (hgeo : ∀ᵐ ω ∂M.P, ∀ u ∈ rowCube n (wInt M K A n) t (((i : ℕ) + 1 : ℕ) - 1) j,
      ∀ v ∈ rowCube n (wInt M K A n) t ((i : ℕ) + 1 : ℕ) k,
      (∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω ((((i : ℕ) + 1 : ℕ) - 1) * n)
        (((i : ℕ) + 1 : ℕ) * n) γ) ∧
      ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω ((((i : ℕ) + 1 : ℕ) - 1) * n)
        (((i : ℕ) + 1 : ℕ) * n) γ →
        ∀ e ∈ γ.edges, fineIndex (wInt M K A n) t (edgeMid e) ∈
          tubeIndices j k (slabRadius M K A Cd ω n t ((i : ℕ) + 1) j k))
    {C : ℝ}
    (hmom : ∀ σ, ∫⁻ x, reward M K A n t Prod.fst (pairNew n (wInt M K A n) L t (offsetOf σ))
        ((i : ℕ) + 1) j k x ^ (16 * (m + 1)) ∂Pr σ ≤
      ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (16 * (m + 1))))
    {r : ℝ} (hrL : ‖transversePoint (j - k)‖ + Real.sqrt L ≤ r)
    (hrm : ‖transversePoint (j - k)‖ + Real.sqrt m ≤ r) :
    offsetAvg (fun σ => ∫⁻ x, reward M K A n t Prod.fst
        (pairNew n (wInt M K A n) L t (offsetOf σ)) ((i : ℕ) + 1) j k x ^ (4 * (m + 1)) ∂Pr σ) ≤
      ENNReal.ofReal (2 ^ (8 * (m + 1) + 1) * ε ^ (8 * (m + 1))) +
        ENNReal.ofReal ((C * (1 + ‖transversePoint (j - k)‖)) ^ (4 * (m + 1))) *
          offsetMixture Pr (residualEvent M K A Cd n L t i j k r) ^ ((3 : ℝ) / 4) := by
  classical
  have := hfam.prob
  have hne : Nonempty (Fin m → Fin L) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hne' : Nonempty (Fin K → Fin m → Fin L) := ⟨fun _ => hne.some⟩
  set p := 4 * (m + 1) with hp
  set T := mixtureReward M K A n L t i j k with hT
  have hTm : Measurable T := measurable_mixtureReward M K A n L t i j k
  set E := residualEvent M K A Cd n L t i j k r with hE
  have hEm : MeasurableSet E := measurableSet_residualEvent M K A Cd n L t i j k r
  set b : ℝ := (C * (1 + ‖transversePoint (j - k)‖)) ^ p with hb
  have hb0 : 0 ≤ b := Even.pow_nonneg ⟨2 * (m + 1), by rw [hp]; ring⟩ _
  set A₀ := ENNReal.ofReal (2 ^ (8 * (m + 1) + 1) * ε ^ (8 * (m + 1))) with hA₀
  -- Hölder's inequality on `E`
  have hT4 : ∫⁻ z, T z ^ (4 * p) ∂offsetMixture Pr ≤ ENNReal.ofReal (b ^ 4) := by
    rw [lintegral_offsetMixture]
    refine offsetAvg_le_const hL fun σ => ?_
    have e1 : 4 * p = 16 * (m + 1) := by rw [hp]; ring
    have e2 : b ^ 4 = (C * (1 + ‖transversePoint (j - k)‖)) ^ (16 * (m + 1)) := by
      rw [hb, ← pow_mul, hp]
      congr 1
      ring
    rw [e1, e2]
    exact hmom σ
  have hH := lintegral_indicator_pow_le hTm.aemeasurable hEm hb0 hT4
  -- each offset
  have hσ : ∀ σ : Fin K → Fin m → Fin L, ∫⁻ x, T (σ, x) ^ p ∂Pr σ ≤
      A₀ + ∫⁻ x, E.indicator (fun z => T z ^ p) (σ, x) ∂Pr σ := by
    intro σ
    by_cases hgood : ∃ g, tubeIndices j j (ENNReal.ofReal r) ⊆
        subIndices L (offsetOf σ ((i : ℕ) + 1)) g
    · obtain ⟨g₀, hg₀⟩ := hgood
      refine (lintegral_reward_pow_le_add_of_ball_subset hL (hfam.repl σ) hQ hw hgeo hrL hrm hg₀
        (hlab ((i : ℕ) + 1) (by omega) (by omega) _ g₀ (offsetOf_mem hL σ _))
        (hfam.lab σ ((i : ℕ) + 1) (by omega) (by omega) g₀)).trans
        (add_le_add le_rfl (lintegral_mono fun x => ?_))
      by_cases hx : ENNReal.ofReal (Real.sqrt L) <
          slabRadius M K A Cd x.1 n t ((i : ℕ) + 1) j k
      · rw [Set.indicator_of_mem (show x ∈ {x : Config m × Config m |
          ENNReal.ofReal (Real.sqrt L) < slabRadius M K A Cd x.1 n t ((i : ℕ) + 1) j k} from hx),
          Set.indicator_of_mem (show (σ, x) ∈ E from Or.inl hx)]
        exact le_rfl
      · rw [Set.indicator_of_notMem (show x ∉ {x : Config m × Config m |
          ENNReal.ofReal (Real.sqrt L) < slabRadius M K A Cd x.1 n t ((i : ℕ) + 1) j k} from hx)]
        exact bot_le
    · refine le_add_left (le_of_eq (lintegral_congr fun x => ?_))
      rw [Set.indicator_of_mem (show (σ, x) ∈ E from Or.inr hgood)]
  -- the average
  have hcard : (Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hconst : ((Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞))⁻¹ *
      ∑ _σ : Fin K → Fin m → Fin L, A₀ = A₀ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hcard (ENNReal.natCast_ne_top _), one_mul]
  calc offsetAvg (fun σ => ∫⁻ x, T (σ, x) ^ p ∂Pr σ)
      ≤ ((Fintype.card (Fin K → Fin m → Fin L) : ℝ≥0∞))⁻¹ * ∑ σ : Fin K → Fin m → Fin L,
          (A₀ + ∫⁻ x, E.indicator (fun z => T z ^ p) (σ, x) ∂Pr σ) := by
        unfold offsetAvg
        gcongr with σ
        exact hσ σ
    _ = A₀ + ∫⁻ z, E.indicator (fun z => T z ^ p) z ∂offsetMixture Pr := by
        rw [Finset.sum_add_distrib, mul_add, hconst, lintegral_offsetMixture]
    _ ≤ _ := add_le_add le_rfl hH

end CurvatureVariance.Paper.Proofs.Residual
