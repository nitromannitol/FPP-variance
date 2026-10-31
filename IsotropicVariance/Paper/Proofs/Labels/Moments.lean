/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Labels.Pointwise
public import IsotropicVariance.Paper.Proofs.Labels.TermNorms
import IsotropicVariance.Paper.Proofs.Labels.Region

/-!
# The bound of Lemma `lem:labels` for one block, in `L^{8d}`

The moments of the terms of the second display of Step 2 of the proof, and of Step 3.

* `aestronglyMeasurable_labelSup`: the supremum in equation `eq:labelprofile` is a random variable.
  On each pair of indices the value of a label is constant, and a version of `T^{(i)}` is continuous
  in the endpoints, so the supremum is a supremum over a countable set.
* `eLpNorm_modTerm_le`: the first term, by equation `eq:modulus` for each pair of cubes.
* `isOs_profSup`: the supremum of `|T^{(i)} − |v − u||` over the pairs of cubes, by equation
  `eq:profiles` and the union bound, equation `eq:union` (`Infra.Os.isOs_finset_sup'_log`).
* `eLpNorm_eventTerm_le`: the third term.
* `eLpNorm_mergeTerm_le`: the term of Step 3.
* `eLpNorm_labelSup_le_terms`: the bound for one block from the inputs.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper IsotropicVariance.Paper.Proofs.Labels

variable {m : ℕ}

/-! ### The exponent -/

theorem eight_mul_add_one_eq (m : ℕ) : (8 * (m + 1) : ℝ≥0∞) = ((8 * (m + 1) : ℕ) : ℝ≥0∞) := by
  push_cast
  ring

theorem toReal_eight_mul_add_one (m : ℕ) : (8 * (m + 1) : ℝ≥0∞).toReal = 8 * ((m : ℝ) + 1) := by
  rw [eight_mul_add_one_eq, ENNReal.toReal_natCast]
  push_cast
  ring

theorem one_le_eight_mul_add_one (m : ℕ) : (1 : ℝ≥0∞) ≤ 8 * (m + 1) := by
  rw [eight_mul_add_one_eq]
  exact_mod_cast (by omega : 1 ≤ 8 * (m + 1))

theorem eight_mul_add_one_ne_top (m : ℕ) : (8 * (m + 1) : ℝ≥0∞) ≠ ⊤ := by
  rw [eight_mul_add_one_eq]
  exact ENNReal.natCast_ne_top _

/-! ### The supremum is a random variable -/

/-- A supremum over `A` of a distance between a function continuous in the point and a function
that depends on the point through finitely many cells is measurable: on each cell it is a supremum
over a countable dense subset. -/
theorem measurable_iSup_ofReal_abs_sub {Ω E C : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [SecondCountableTopology E] [Finite C] {g : Ω → E → ℝ}
    (hgm : ∀ x, Measurable fun ω => g ω x) (hgc : ∀ ω, Continuous (g ω)) (A : Set E)
    (cell : E → C) {f : C → Ω → ℝ} (hf : ∀ c, Measurable (f c)) :
    Measurable fun ω => ⨆ x ∈ A, ENNReal.ofReal |g ω x - f (cell x) ω| := by
  have hD : ∀ c : C, ∃ D : Set E, D.Countable ∧ D ⊆ A ∩ cell ⁻¹' {c} ∧
      A ∩ cell ⁻¹' {c} ⊆ closure D := fun c => TopologicalSpace.exists_countable_dense_subset _
  choose D hDc hDA hAD using hD
  have hS : Measurable fun ω => ⨆ c : C, ⨆ x ∈ D c, ENNReal.ofReal |g ω x - f c ω| := by
    refine Measurable.iSup fun c => ?_
    have : Countable (D c) := (hDc c).to_subtype
    refine Measurable.biSup _ (hDc c) fun x _ => ?_
    exact (continuous_abs.measurable.comp ((hgm x).sub (hf c))).ennreal_ofReal
  suffices heq : (fun ω => ⨆ x ∈ A, ENNReal.ofReal |g ω x - f (cell x) ω|) =
      fun ω => ⨆ c : C, ⨆ x ∈ D c, ENNReal.ofReal |g ω x - f c ω| by
    rw [heq]
    exact hS
  funext ω
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨S, hS'⟩ : ∃ S, S = ⨆ c : C, ⨆ x ∈ D c, ENNReal.ofReal |g ω x - f c ω| := ⟨_, rfl⟩
    rw [← hS']
    have hψ : Continuous fun y => ENNReal.ofReal |g ω y - f (cell x) ω| :=
      ENNReal.continuous_ofReal.comp (continuous_abs.comp ((hgc ω).sub continuous_const))
    have hcl : IsClosed {y | ENNReal.ofReal |g ω y - f (cell x) ω| ≤ S} :=
      isClosed_le hψ continuous_const
    refine closure_minimal (fun y hy => ?_) hcl (hAD (cell x) ⟨hx, rfl⟩)
    rw [hS']
    have h1 : ENNReal.ofReal |g ω y - f (cell x) ω| ≤
        ⨆ x' ∈ D (cell x), ENNReal.ofReal |g ω x' - f (cell x) ω| :=
      le_iSup₂ (f := fun x' (_ : x' ∈ D (cell x)) => ENNReal.ofReal |g ω x' - f (cell x) ω|) y hy
    exact h1.trans (le_iSup (fun c => ⨆ x' ∈ D c, ENNReal.ofReal |g ω x' - f c ω|) (cell x))
  · refine iSup_le fun c => iSup₂_le fun x hx => ?_
    obtain ⟨hxA, hxc⟩ := hDA c hx
    have hxc' : cell x = c := hxc
    exact le_iSup₂_of_le x hxA (by rw [hxc'])

variable (X : Setting.{u} m)

/-- **The supremum in equation `eq:labelprofile` is a random variable.** -/
theorem aestronglyMeasurable_labelSup {b : ℝ} (hb : X.IsUpperBound b)
    {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W : ℝ} (hn : 0 ≤ n) (Q : ℝ) {L : ℕ}
    (κ M θ : ℝ) (hVm : ∀ i z, Measurable[X.info (block n W L i z)] (V i z)) (i : ℕ)
    (z : Fin m → ℤ) :
    AEStronglyMeasurable (fun ω => ⨆ (u : coreFace n W L i z) (v : coreFace n W L (i + 1) z),
      ENNReal.ofReal |(X.slabTime b (chainSlab n 0 i) ω u v - n) / Q -
        (tgFamily X V n W Q L κ M θ).value ((tgFamily X V n W Q L κ M θ).label i z ω)
          ((u : Pt m) - blockCorner n W i z) ((v : Pt m) - blockCorner n W i z)|) X.P := by
  obtain ⟨Vs, hVsm, hVsc, -, hVs⟩ := Infra.Slab.exists_slabTime_version X hb (chainSlab n 0 i)
  obtain ⟨c, hc⟩ : ∃ c, c = blockCorner n W i z := ⟨_, rfl⟩
  rw [← hc]
  obtain ⟨A, hA⟩ : ∃ A : Set (Pt m × Pt m),
    A = coreFace n W L i z ×ˢ coreFace n W L (i + 1) z := ⟨_, rfl⟩
  have hf : ∀ pq : GridPair m L κ,
      Measurable fun ω => dequantize M κ (lambdaCode X V n W Q L κ M θ i z ω pq) := fun pq => by
    have h1 : Measurable fun c : GridCode m L κ M => c pq := measurable_pi_apply pq
    have h2 : Measurable fun r : Fin (levelCount M κ) => dequantize M κ r := Measurable.of_discrete
    exact (h2.comp h1).comp (measurable_lambdaCode X Q κ M θ hVm i z)
  have hmeas := measurable_iSup_ofReal_abs_sub (g := fun ω x => (Vs ω x - n) / Q)
    (fun x => ((hVsm.comp (measurable_id.prodMk measurable_const)).sub_const n).div_const Q)
    (fun ω => ((hVsc ω).sub continuous_const).div_const Q) A
    (fun x : Pt m × Pt m => ((gridCell W L κ (x.1 - c), gridCell W L κ (x.2 - c)) :
      GridPair m L κ)) hf
  refine hmeas.aestronglyMeasurable.congr ?_
  filter_upwards [hVs] with ω hω
  have hval : ∀ u ∈ coreFace n W L i z, ∀ v ∈ coreFace n W L (i + 1) z,
      ENNReal.ofReal |(X.slabTime b (chainSlab n 0 i) ω u v - n) / Q -
        (tgFamily X V n W Q L κ M θ).value ((tgFamily X V n W Q L κ M θ).label i z ω)
          (u - c) (v - c)| =
      ENNReal.ofReal |(Vs ω (u, v) - n) / Q -
        dequantize M κ (lambdaCode X V n W Q L κ M θ i z ω
          (gridCell W L κ (u - c), gridCell W L κ (v - c)))| := by
    intro u hu v hv
    have hus : u ∈ (chainSlab n 0 i).set := by
      rw [Labels.mem_chainSlab_set, hu.1]
      exact ⟨le_rfl, by nlinarith only [hn]⟩
    have hvs : v ∈ (chainSlab n 0 i).set := by
      rw [Labels.mem_chainSlab_set, hv.1]
      push_cast
      exact ⟨by nlinarith only [hn], le_rfl⟩
    rw [hω u hus v hvs]
    rfl
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    have hx' : x.1 ∈ coreFace n W L i z ∧ x.2 ∈ coreFace n W L (i + 1) z := by
      rw [hA] at hx
      exact hx
    refine le_iSup₂_of_le (⟨x.1, hx'.1⟩ : coreFace n W L i z)
      (⟨x.2, hx'.2⟩ : coreFace n W L (i + 1) z) ?_
    exact (hval x.1 hx'.1 x.2 hx'.2).symm.le
  · refine iSup₂_le fun u v => ?_
    have hmem : ((u : Pt m), (v : Pt m)) ∈ A := by
      rw [hA]
      exact ⟨u.2, v.2⟩
    refine le_iSup₂_of_le ((u : Pt m), (v : Pt m)) hmem ?_
    exact (hval u u.2 v v.2).le

/-! ### The terms -/

/-- The modulus quantity is nonnegative. -/
theorem modulusSup_nonneg (D : Pt m → Pt m → ℝ) (I I' : Set (Pt m)) (r : ℝ) :
    0 ≤ Contracts.modulusSup D I I' r :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- **The first term**, by equation `eq:modulus` for each pair of cubes. -/
theorem eLpNorm_modTerm_le {b n W Q r η : ℝ} (hQ : 0 < Q) {L i : ℕ} {z : Fin m → ℤ} {p : ℝ≥0∞}
    (hp : 1 ≤ p)
    (h : ∀ ab : PairIdx m L, eLpNorm (fun ω => Contracts.modulusSup
      (X.slabTime b (pairOf n W i z ab).slab ω) (pairOf n W i z ab).first
        (pairOf n W i z ab).second r) p X.P ≤ ENNReal.ofReal (η * Q)) :
    eLpNorm (modTerm X b n W Q r L i z) p X.P ≤
      Fintype.card (PairIdx m L) * ENNReal.ofReal η := by
  have hsum : modTerm X b n W Q r L i z = ∑ ab : PairIdx m L, fun ω => ENNReal.ofReal
      (Contracts.modulusSup (X.slabTime b (pairOf n W i z ab).slab ω)
        (pairOf n W i z ab).first (pairOf n W i z ab).second r / Q) := by
    funext ω
    simp only [modTerm, Finset.sum_apply]
  rw [hsum]
  refine (eLpNorm_sum_le hp).trans ?_
  calc ∑ ab : PairIdx m L, eLpNorm (fun ω => ENNReal.ofReal
        (Contracts.modulusSup (X.slabTime b (pairOf n W i z ab).slab ω)
          (pairOf n W i z ab).first (pairOf n W i z ab).second r / Q)) p X.P
      ≤ ∑ _ab : PairIdx m L, ENNReal.ofReal η :=
        Finset.sum_le_sum fun ab _ =>
          eLpNorm_ofReal_div_le (fun ω => modulusSup_nonneg _ _ _ _) hQ (h ab)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The supremum over the pairs of cubes**, by equation `eq:profiles` and the union bound,
equation `eq:union`. -/
theorem isOs_profSup {b n W C Q : ℝ} (hC : 0 < C) (hQ : 0 < Q) {L i : ℕ} {z : Fin m → ℤ}
    (h : ∀ ab : PairIdx m L, Cited.IsOs X.P 1 (C * Q) (fun ω =>
      ⨆ (u : (pairOf n W i z ab).first) (v : (pairOf n W i z ab).second),
        |X.slabTime b (pairOf n W i z ab).slab ω u v - dist (u : Pt m) v|)) :
    Cited.IsOs X.P 1
      ((2 / Real.log 2 * C * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m))) * Q)
      (profSup X b n W L i z) := by
  have h0 := Infra.Os.isOs_finset_sup'_log (s := 1) one_pos (mul_pos hC hQ)
    (Finset.univ : Finset (PairIdx m L)) Finset.univ_nonempty _ (fun ab _ => h ab)
  rw [Finset.card_univ, card_pairIdx, one_div_one, Real.rpow_one, Real.rpow_one] at h0
  have e : 2 / Real.log 2 * C * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) * Q =
      2 / Real.log 2 * (C * Q) * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) := by ring
  rw [e]
  exact h0

/-- **The third term.** -/
theorem eLpNorm_eventTerm_le {b n W : ℝ} {L i : ℕ} {z : Fin m → ℤ} (M : ℝ) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {ε : ℝ≥0∞} (hε : X.P (stepOneEvent X b n W L i z) ≤ ε) :
    eLpNorm (eventTerm X b n W L i z M) p X.P ≤ ENNReal.ofReal (2 * M) * ε ^ (1 / p.toReal) :=
  eLpNorm_indicator_const_le (measurableSet_toMeasurable _ _) _ hp0 hpt
    (by rw [measure_toMeasurable]; exact hε)

/-- **The term of Step 3.** -/
theorem eLpNorm_mergeTerm_le {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W : ℝ} (Q : ℝ)
    {L : ℕ} (κ M θ : ℝ) (hVm : ∀ i z, Measurable[X.info (block n W L i z)] (V i z)) (i : ℕ)
    (z : Fin m → ℤ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (mergeTerm X V n W Q L κ M θ i z) p X.P ≤
      ENNReal.ofReal (2 * (M + κ)) *
        ENNReal.ofReal (Fintype.card (GridCode m L κ M) * θ) ^ (1 / p.toReal) := by
  have hB : MeasurableSet {ω | lambdaCode X V n W Q L κ M θ i z ω ≠
      psiCode X V n W Q L κ M i z ω} :=
    ((measurable_lambdaCode X Q κ M θ hVm i z).prodMk (measurable_psiCode X (hVm i z)))
      (Set.toFinite {q : GridCode m L κ M × GridCode m L κ M | q.1 ≠ q.2}).measurableSet
  exact eLpNorm_indicator_const_le hB _ hp0 hpt
    (measure_mergeRare_ne_le (c := psiCode X V n W Q L κ M i z) X.P θ)

/-! ### The sum -/

/-- The `L^p` norm of the supremum of equation `eq:labelprofile` is at most the sum of the `L^p`
norms of the terms of `ofReal_abs_sub_value_le`. -/
theorem eLpNorm_labelSup_le {b : ℝ} (hb : X.IsUpperBound b)
    {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W Q : ℝ} (hn : 0 < n) (hW : 0 < W)
    (hQ : 0 < Q) (hWQ : W ^ 2 = n * Q) {L : ℕ} (hL : 16 ≤ L) {κ M θ r : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hκW : Real.sqrt m * κ ≤ 1) (hκr : Real.sqrt m * κ * W ≤ r) (hM : 0 ≤ M)
    (hVm : ∀ i z, Measurable[X.info (block n W L i z)] (V i z)) (i : ℕ) (z : Fin m → ℤ)
    (hV : ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n W L i z), ∀ v ∈ closure (block n W L i z),
      V i z ω (u, v) = X.setTime b (closure (block n W L i z)) ω u v)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun ω => ⨆ (u : coreFace n W L i z) (v : coreFace n W L (i + 1) z),
        ENNReal.ofReal |(X.slabTime b (chainSlab n 0 i) ω u v - n) / Q -
          (tgFamily X V n W Q L κ M θ).value ((tgFamily X V n W Q L κ M θ).label i z ω)
            ((u : Pt m) - blockCorner n W i z) ((v : Pt m) - blockCorner n W i z)|) p X.P ≤
      eLpNorm (modTerm X b n W Q r L i z) p X.P + ENNReal.ofReal (2 * m * L * κ) +
        eLpNorm (fun ω => ENNReal.ofReal (profSup X b n W L i z ω / Q - M / 2)) p X.P +
        ENNReal.ofReal (m * L ^ 2 / 2 - M / 2) + eLpNorm (eventTerm X b n W L i z M) p X.P +
        ENNReal.ofReal κ + eLpNorm (mergeTerm X V n W Q L κ M θ i z) p X.P := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  refine (eLpNorm_mono_enorm_ae
    (g := modTerm X b n W Q r L i z + (fun _ => ENNReal.ofReal (2 * m * L * κ)) +
      (fun ω => ENNReal.ofReal (profSup X b n W L i z ω / Q - M / 2)) +
      (fun _ => ENNReal.ofReal (m * L ^ 2 / 2 - M / 2)) + eventTerm X b n W L i z M +
      (fun _ => ENNReal.ofReal κ) + mergeTerm X V n W Q L κ M θ i z)
    (aestronglyMeasurable_labelSup X hb hn.le Q κ M θ hVm i z) ?_).trans ?_
  · filter_upwards [hV] with ω hω
    simp only [enorm_eq_self, Pi.add_apply]
    exact iSup₂_le fun u v =>
      ofReal_abs_sub_value_le X hb V hn hW hQ hWQ hL hκ hκ1 hκW hκr hM i z ω hω u.2 v.2
  refine (eLpNorm_add_le hp).trans (add_le_add ?_ le_rfl)
  refine (eLpNorm_add_le hp).trans (add_le_add ?_ (eLpNorm_const_enn _ hp0).le)
  refine (eLpNorm_add_le hp).trans (add_le_add ?_ le_rfl)
  refine (eLpNorm_add_le hp).trans (add_le_add ?_ (eLpNorm_const_enn _ hp0).le)
  refine (eLpNorm_add_le hp).trans (add_le_add ?_ le_rfl)
  exact (eLpNorm_add_le hp).trans (add_le_add le_rfl (eLpNorm_const_enn _ hp0).le)

/-- **The bound of equation `eq:labelprofile` for one block from the inputs**: equation `eq:modulus`
on the pairs of cubes at the error `η` and the mesh `h`, equation `eq:profiles` with the constant
`C_p`, and equation `eq:localization` with the constant `C_l`. -/
theorem eLpNorm_labelSup_le_terms {b : ℝ} (hb : X.IsUpperBound b)
    {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W Q : ℝ} (hn : 0 < n) (hW : 4 ≤ W)
    (hQ : 0 < Q) (hWQ : W ^ 2 = n * Q) {L : ℕ} (hL : 16 ≤ L) {κ M θ h η Cp Cl : ℝ} (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hκW : Real.sqrt m * κ ≤ 1) (hκh : Real.sqrt m * κ ≤ h) (hM : 0 < M)
    (hCp : 0 < Cp) (hCl : 0 < Cl)
    (hVm : ∀ i z, Measurable[X.info (block n W L i z)] (V i z)) (i : ℕ) (z : Fin m → ℤ)
    (hV : ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n W L i z), ∀ v ∈ closure (block n W L i z),
      V i z ω (u, v) = X.setTime b (closure (block n W L i z)) ω u v)
    (hmodB : ∀ ab : PairIdx m L, eLpNorm (fun ω => Contracts.modulusSup
      (X.slabTime b (pairOf n W i z ab).slab ω) (pairOf n W i z ab).first
        (pairOf n W i z ab).second (h * W)) (8 * (m + 1) : ℝ≥0∞) X.P ≤ ENNReal.ofReal (η * Q))
    (hprofB : ∀ ab : PairIdx m L, Cited.IsOs X.P 1 (Cp * Q) (fun ω =>
      ⨆ (u : (pairOf n W i z ab).first) (v : (pairOf n W i z ab).second),
        |X.slabTime b (pairOf n W i z ab).slab ω u v - dist (u : Pt m) v|))
    (hlocB : ∀ ab : PairIdx m L, Cited.IsOs X.P 2 Cl (fun ω => W⁻¹ * Contracts.maxSegmentDeviation
      ((pairOf n W i z ab).slab.density b (X.ρ ω)) (pairOf n W i z ab).slab.set
      (pairOf n W i z ab).first (pairOf n W i z ab).second)) :
    eLpNorm (fun ω => ⨆ (u : coreFace n W L i z) (v : coreFace n W L (i + 1) z),
        ENNReal.ofReal |(X.slabTime b (chainSlab n 0 i) ω u v - n) / Q -
          (tgFamily X V n W Q L κ M θ).value ((tgFamily X V n W Q L κ M θ).label i z ω)
            ((u : Pt m) - blockCorner n W i z) ((v : Pt m) - blockCorner n W i z)|)
        (8 * (m + 1) : ℝ≥0∞) X.P ≤
      Fintype.card (PairIdx m L) * ENNReal.ofReal η + ENNReal.ofReal (2 * m * L * κ) +
        ENNReal.ofReal (momentConst (8 * ((m : ℝ) + 1)) ^ (1 / (8 * ((m : ℝ) + 1))) *
          (2 / Real.log 2 * Cp * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m))) ^ 2 / (M / 2)) +
        ENNReal.ofReal (m * L ^ 2 / 2 - M / 2) +
        ENNReal.ofReal (2 * M) * ENNReal.ofReal (Fintype.card (PairIdx m L) *
          (2 * Real.exp (-((Real.sqrt L - 1) / (2 * Cl)) ^ 2))) ^ (1 / (8 * ((m : ℝ) + 1))) +
        ENNReal.ofReal κ +
        ENNReal.ofReal (2 * (M + κ)) *
          ENNReal.ofReal (Fintype.card (GridCode m L κ M) * θ) ^ (1 / (8 * ((m : ℝ) + 1))) := by
  have hW0 : 0 < W := by linarith only [hW]
  have hp := one_le_eight_mul_add_one m
  have hpt := eight_mul_add_one_ne_top m
  have hp0 : (8 * (m + 1) : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hL1 : 1 ≤ L := by omega
  have hκr : Real.sqrt m * κ * W ≤ h * W := mul_le_mul_of_nonneg_right hκh hW0.le
  refine (eLpNorm_labelSup_le X hb hn hW0 hQ hWQ hL hκ hκ1 hκW hκr hM.le hVm i z hV hp).trans ?_
  have h1 := eLpNorm_modTerm_le X hQ hp hmodB
  have hG : 0 < 2 / Real.log 2 * Cp * Real.log (2 + ((L : ℝ) + 1) ^ (2 * m)) := by
    have h2 : (1 : ℝ) < 2 + ((L : ℝ) + 1) ^ (2 * m) := by
      have : (0 : ℝ) ≤ ((L : ℝ) + 1) ^ (2 * m) := by positivity
      linarith only [this]
    have h3 := Real.log_pos h2
    have h4 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  have h2 := eLpNorm_ofReal_div_sub_le (isOs_profSup X hCp hQ hprofB) hG hQ
    (half_pos hM) hp0 hpt
  have h3 := eLpNorm_eventTerm_le X M hp0 hpt (measure_stepOneEvent_le X hW hCl hL1 hlocB)
  have h4 := eLpNorm_mergeTerm_le X Q κ M θ hVm i z hp0 hpt
  rw [toReal_eight_mul_add_one] at h2 h3 h4
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 le_rfl) h2)
    le_rfl) h3) le_rfl) h4

end IsotropicVariance.Paper.Proofs.Labels
