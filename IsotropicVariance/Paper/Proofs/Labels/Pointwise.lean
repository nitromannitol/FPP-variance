/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Labels.Covariance
public import IsotropicVariance.Paper.Proofs.Labels.Extract
public import IsotropicVariance.Infra.Os.Maximum
public import IsotropicVariance.Infra.Os.Moments
import IsotropicVariance.Statements.Cited.IsOsMeasureGeLe
import IsotropicVariance.Paper.Proofs.Labels.Region
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bound of Lemma `lem:labels` for one block, pointwise

Steps 1 and 2 of the proof.

* `stepOneEvent`: the event `E`, that a curve in `Π_{T^{(i)}}(u, v)` strays from the segment
  `[u, v]` by more than `√L W/2 − 2`, for some pair of cubes covering the faces of `G`. Off `E`, the
  curves between points at distance at least `√L W/2` from the sides of `G` keep a margin, so
  `T_G = T^{(i)}` at these points (`setTime_eq_slabTime_of_notMem_stepOneEvent`).
* `measure_stepOneEvent_le`: `P[E] ≤ (L + 1)^{2m} · 2 e^{−((√L − 1)/(2C))²}`, by equation
  `eq:localization` for the pairs of cubes.
* `modTerm`, `profSup`, `eventTerm`, `mergeTerm`: the terms of the second display of Step 2 and of
  Step 3. `profSup` is the supremum of `|T^{(i)} − |v − u||` over the pairs of cubes.
* `ofReal_abs_sub_value_le`: the second display of Step 2, followed by the replacement of
  Step 3, for `X_G`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper IsotropicVariance.Paper.Proofs.Labels

variable {m : ℕ}

/-! ### The event of Step 1 -/

/-- The slab density of a pair of cubes of the cover is the density of the slab `i`. -/
theorem density_pairOf_slab (b n W : ℝ) {L : ℕ} (i : ℕ) (z : Fin m → ℤ) (ab : PairIdx m L)
    (σ : Pt m → ℝ) : (pairOf n W i z ab).slab.density b σ = (chainSlab n 0 i).density b σ := by
  funext x
  simp only [Slab.density, pairOf, coverPair_slab_faces]

variable (X : Setting.{u} m)

/-- **The event `E`** of Step 1 of the proof of Lemma `lem:labels`: for some pair of cubes, a curve
of `Π_{T^{(i)}}` strays from the segment by more than `√L W/2 − 2`. -/
def stepOneEvent (b n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) : Set X.Ω :=
  {ω | ∃ ab : PairIdx m L, Real.sqrt L * W / 2 - 2 < Contracts.maxSegmentDeviation
    ((pairOf n W i z ab).slab.density b (X.ρ ω)) (pairOf n W i z ab).slab.set
    (pairOf n W i z ab).first (pairOf n W i z ab).second}

/-- **Off `E`, `T_G = T^{(i)}`** at the points of the cubes at distance at least `√L W/2` from the
sides of the block (Step 1 of the proof of Lemma `lem:labels`). -/
theorem setTime_eq_slabTime_of_notMem_stepOneEvent {b : ℝ} (hb : X.IsUpperBound b) {n W : ℝ}
    (hn : 0 < n) {L i : ℕ} {z : Fin m → ℤ} {ω : X.Ω} (hω : ω ∉ stepOneEvent X b n W L i z)
    (ab : PairIdx m L) {u v : Pt m} (hu : u ∈ (pairOf n W i z ab).first)
    (hv : v ∈ (pairOf n W i z ab).second) (hub : InBox W L z (Real.sqrt L / 2) u)
    (hvb : InBox W L z (Real.sqrt L / 2) v) (huc : u ∈ closure (block n W L i z))
    (hvc : v ∈ closure (block n W L i z)) :
    X.setTime b (closure (block n W L i z)) ω u v = X.slabTime b (chainSlab n 0 i) ω u v := by
  refine setTime_closure_block_eq X hb hn ω huc hvc fun γ hγ t ht => ?_
  have hset : (pairOf n W i z ab).slab.set = (chainSlab n 0 i).set := coverPair_slab_set n W i z _ _
  have hγ' : IsOneOptimal ((pairOf n W i z ab).slab.density b (X.ρ ω))
      (pairOf n W i z ab).slab.set u v γ := by
    rw [density_pairOf_slab, hset]
    exact hγ
  have h1 := infDist_le_maxSegmentDeviation_slab X hb (pairOf n W i z ab) hn.le ω hu hv hγ' ht
  have h2 : Contracts.maxSegmentDeviation ((pairOf n W i z ab).slab.density b (X.ρ ω))
      (pairOf n W i z ab).slab.set (pairOf n W i z ab).first (pairOf n W i z ab).second ≤
      Real.sqrt L * W / 2 - 2 := not_lt.1 fun h => hω ⟨ab, h⟩
  exact hub.hasMargin_of_infDist_le hvb (h1.trans h2)

/-- **`P[E] ≤ C L^{2(d−1)} e^{−cL}`** (Step 1 of the proof of Lemma `lem:labels`), by equation
`eq:localization` with the constant `C`, for `W ≥ 4`. -/
theorem measure_stepOneEvent_le {b n W C : ℝ} (hW : 4 ≤ W) (hC : 0 < C) {L i : ℕ} (hL : 1 ≤ L)
    {z : Fin m → ℤ}
    (h : ∀ ab : PairIdx m L, Cited.IsOs X.P 2 C (fun ω => W⁻¹ * Contracts.maxSegmentDeviation
      ((pairOf n W i z ab).slab.density b (X.ρ ω)) (pairOf n W i z ab).slab.set
      (pairOf n W i z ab).first (pairOf n W i z ab).second)) :
    X.P (stepOneEvent X b n W L i z) ≤
      ENNReal.ofReal (Fintype.card (PairIdx m L) *
        (2 * Real.exp (-((Real.sqrt L - 1) / (2 * C)) ^ 2))) := by
  obtain ⟨t, htdef⟩ : ∃ t, t = (Real.sqrt L - 1) / (2 * C) := ⟨_, rfl⟩
  have hsL : (1 : ℝ) ≤ Real.sqrt L := Real.one_le_sqrt.2 (by exact_mod_cast hL)
  have ht : 0 ≤ t := by
    rw [htdef]
    exact div_nonneg (by linarith only [hsL]) (by positivity)
  have hCt : C * t = (Real.sqrt L - 1) / 2 := by
    rw [htdef]
    field_simp
  have hW0 : 0 < W := by linarith only [hW]
  have hsub : stepOneEvent X b n W L i z ⊆ ⋃ ab : PairIdx m L,
      {ω | C * t ≤ W⁻¹ * Contracts.maxSegmentDeviation
        ((pairOf n W i z ab).slab.density b (X.ρ ω)) (pairOf n W i z ab).slab.set
        (pairOf n W i z ab).first (pairOf n W i z ab).second} := by
    rintro ω ⟨ab, hab⟩
    refine mem_iUnion.2 ⟨ab, ?_⟩
    have h1 := mul_le_mul_of_nonneg_left hab.le (inv_nonneg.2 hW0.le)
    have h2 : W⁻¹ * (Real.sqrt L * W / 2 - 2) = Real.sqrt L / 2 - 2 / W := by
      field_simp
    have h3 : 2 / W ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hW0 two_pos]
      linarith only [hW]
    change C * t ≤ _
    rw [hCt]
    linarith only [h1, h2, h3]
  calc X.P (stepOneEvent X b n W L i z)
      ≤ X.P (⋃ ab : PairIdx m L,
          {ω | C * t ≤ W⁻¹ * Contracts.maxSegmentDeviation
            ((pairOf n W i z ab).slab.density b (X.ρ ω)) (pairOf n W i z ab).slab.set
            (pairOf n W i z ab).first (pairOf n W i z ab).second}) := measure_mono hsub
    _ ≤ ∑ ab : PairIdx m L, X.P {ω | C * t ≤ W⁻¹ * Contracts.maxSegmentDeviation
            ((pairOf n W i z ab).slab.density b (X.ρ ω)) (pairOf n W i z ab).slab.set
            (pairOf n W i z ab).first (pairOf n W i z ab).second} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ab : PairIdx m L, ENNReal.ofReal (2 * Real.exp (-t ^ 2)) :=
        Finset.sum_le_sum fun ab _ => by
          have := Cited.IsOs.measure_ge_le two_pos hC (h ab) _ ht
          rwa [Real.rpow_two] at this
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), htdef]

/-! ### The terms of the bound -/

/-- The first term: the moduli of equation `eq:modulus` at the scale `r` on the pairs of cubes,
divided by `Q`. -/
noncomputable def modTerm (b n W Q r : ℝ) (L i : ℕ) (z : Fin m → ℤ) (ω : X.Ω) : ℝ≥0∞ :=
  ∑ ab : PairIdx m L, ENNReal.ofReal (Contracts.modulusSup
    (X.slabTime b (pairOf n W i z ab).slab ω) (pairOf n W i z ab).first
      (pairOf n W i z ab).second r / Q)

/-- The supremum of `|T^{(i)}(u, v) − |v − u||` over the pairs of cubes. -/
noncomputable def profSup (b n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) : X.Ω → ℝ :=
  (Finset.univ : Finset (PairIdx m L)).sup' Finset.univ_nonempty fun ab ω =>
    ⨆ (u : (pairOf n W i z ab).first) (v : (pairOf n W i z ab).second),
      |X.slabTime b (pairOf n W i z ab).slab ω u v - dist (u : Pt m) v|

/-- The third term: `2M` on the event `E`, enlarged to a measurable set. -/
noncomputable def eventTerm (b n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) (M : ℝ) : X.Ω → ℝ≥0∞ :=
  (toMeasurable X.P (stepOneEvent X b n W L i z)).indicator fun _ => ENNReal.ofReal (2 * M)

/-- The term of Step 3: `2(M + κ)` where `X_G` differs from `Ψ_G`. -/
noncomputable def mergeTerm (V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ) (n W Q : ℝ) (L : ℕ)
    (κ M θ : ℝ) (i : ℕ) (z : Fin m → ℤ) : X.Ω → ℝ≥0∞ :=
  {ω | lambdaCode X V n W Q L κ M θ i z ω ≠ psiCode X V n W Q L κ M i z ω}.indicator
    fun _ => ENNReal.ofReal (2 * (M + κ))

/-! ### The real bound -/

/-- The second display of Step 2 of the proof of Lemma `lem:labels` in real numbers, for
`x = (T(u, v) − n)/Q`, `y = (T(u_κ, v_κ) − n)/Q` and `y' = (T_G(u_κ, v_κ) − n)/Q`. -/
theorem abs_sub_dequantize_quantize_le {M κ x y y' e : ℝ} (hM : 0 ≤ M) (hκ : 0 < κ)
    (he : |clampM M y - clampM M y'| ≤ e) :
    |x - dequantize M κ (quantize M κ y')| ≤ |x - y| + max (|y| - M) 0 + e + κ := by
  have h1 := abs_sub_clampM_le hM y
  have h2 := abs_clampM_sub_dequantize_le hM hκ y'
  have e1 : x - dequantize M κ (quantize M κ y') = (x - y) + (y - clampM M y) +
      (clampM M y - clampM M y') + (clampM M y' - dequantize M κ (quantize M κ y')) := by ring
  rw [e1]
  have h3 := abs_add_le ((x - y) + (y - clampM M y) + (clampM M y - clampM M y'))
    (clampM M y' - dequantize M κ (quantize M κ y'))
  have h4 := abs_add_le ((x - y) + (y - clampM M y)) (clampM M y - clampM M y')
  have h5 := abs_add_le (x - y) (y - clampM M y)
  linarith only [h1, h2, he, h3, h4, h5]

/-- Two clamped values differ by at most `2M`. -/
theorem abs_clampM_sub_clampM_le_two_mul {M : ℝ} (hM : 0 ≤ M) (y y' : ℝ) :
    |clampM M y - clampM M y'| ≤ 2 * M := by
  have h1 := abs_clampM_le hM y
  have h2 := abs_clampM_le hM y'
  have h3 := abs_sub (clampM M y) (clampM M y')
  linarith only [h1, h2, h3]

/-! ### The rounded points of a pair of cores -/

/-- The facts of Step 2 of the proof of Lemma `lem:labels` about two points of the cores of the
faces of a block and their rounded points: one pair of cubes contains all four, the rounded points
are at distance at least `√L W/2` from the sides, and the Euclidean estimates hold. -/
theorem exists_pair_round {n W Q κ : ℝ} (hn : 0 < n) (hW : 0 < W) (hWQ : W ^ 2 = n * Q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hκW : Real.sqrt m * κ ≤ 1) {L : ℕ} (hL : 16 ≤ L) {i : ℕ}
    {z : Fin m → ℤ} {u v : Pt m} (hu : u ∈ coreFace n W L i z)
    (hv : v ∈ coreFace n W L (i + 1) z) :
    ∃ ab : PairIdx m L,
      u ∈ (pairOf n W i z ab).first ∧ roundPt n W L κ i z 0 u ∈ (pairOf n W i z ab).first ∧
      v ∈ (pairOf n W i z ab).second ∧ roundPt n W L κ i z n v ∈ (pairOf n W i z ab).second ∧
      InBox W L z (Real.sqrt L / 2) (roundPt n W L κ i z 0 u) ∧
      InBox W L z (Real.sqrt L / 2) (roundPt n W L κ i z n v) ∧
      dist u (roundPt n W L κ i z 0 u) ≤ Real.sqrt m * κ * W ∧
      dist v (roundPt n W L κ i z n v) ≤ Real.sqrt m * κ * W ∧
      |dist u v - dist (roundPt n W L κ i z 0 u) (roundPt n W L κ i z n v)| ≤ 2 * m * L * κ * Q ∧
      n ≤ dist (roundPt n W L κ i z 0 u) (roundPt n W L κ i z n v) ∧
      dist (roundPt n W L κ i z 0 u) (roundPt n W L κ i z n v) - n ≤ m * L ^ 2 * Q / 2 := by
  have hL' : (16 : ℝ) ≤ L := by exact_mod_cast hL
  have hs4 : 4 ≤ Real.sqrt L := Real.le_sqrt_of_sq_le (by linarith only [hL'])
  have hsp : 0 < Real.sqrt L := by linarith only [hs4]
  obtain ⟨hlu, hbu⟩ := coreFace_iff.1 hu
  obtain ⟨hlv, hbv⟩ := coreFace_iff.1 hv
  have hlu' : Pt.lon u = (i : ℝ) * n + 0 := by rw [hlu, add_zero]
  have hlv' : Pt.lon v = (i : ℝ) * n + n := by
    rw [hlv]
    push_cast
    ring
  have hlur : Pt.lon (roundPt n W L κ i z 0 u) = (i : ℝ) * n := by
    rw [lon_roundPt, add_zero]
  have hlvr : Pt.lon (roundPt n W L κ i z n v) = ((i + 1 : ℕ) : ℝ) * n := by
    rw [lon_roundPt]
    push_cast
    ring
  have hdu : dist u (roundPt n W L κ i z 0 u) ≤ Real.sqrt m * κ * W :=
    dist_roundPt_le hW hκ hsp hlu' hbu
  have hdv : dist v (roundPt n W L κ i z n v) ≤ Real.sqrt m * κ * W :=
    dist_roundPt_le hW hκ hsp hlv' hbv
  have hrW : Real.sqrt m * κ * W ≤ W := mul_le_of_le_one_left hW.le hκW
  have hmono : Real.sqrt L / 2 ≤ Real.sqrt L - κ := by linarith only [hs4, hκ1]
  have hbu' : InBox W L z (Real.sqrt L / 2) (roundPt n W L κ i z 0 u) :=
    (hbu.roundPt hW hκ hsp).mono hW.le hmono
  have hbv' : InBox W L z (Real.sqrt L / 2) (roundPt n W L κ i z n v) :=
    (hbv.roundPt hW hκ hsp).mono hW.le hmono
  obtain ⟨ab, h1, h2⟩ := exists_pairOf (n := n) hW hu hv
  have hdist0 : ∀ x : Pt m, dist x x ≤ W := fun x => by
    rw [dist_self]
    exact hW.le
  have hlon1 : Pt.lon v - Pt.lon u = n := by
    rw [hlv', hlu']
    ring
  have hlon2 : Pt.lon (roundPt n W L κ i z n v) - Pt.lon (roundPt n W L κ i z 0 u) = n := by
    rw [lon_roundPt, lon_roundPt]
    ring
  have hR1 := hbu.norm_tr_sub_le hW.le hsp.le hbv
  have hR2 := hbu'.norm_tr_sub_le hW.le (by positivity) hbv'
  exact ⟨ab, h1 u hlu (hdist0 u), h1 _ hlur (hdu.trans hrW), h2 v hlv (hdist0 v),
    h2 _ hlvr (hdv.trans hrW), hbu', hbv', hdu, hdv,
    abs_dist_sub_dist_le_of_mesh hn hW.le hWQ hlon1 hlon2 hR1 hR2 hdu hdv,
    le_dist_of_lon_sub hn.le hlon2, dist_sub_le_of_tr hn hWQ hlon2 hR2⟩

/-! ### The bound for one block -/

/-- **The bound of equation `eq:labelprofile` for one block, pointwise** (Steps 2 and 3 of the proof
of Lemma `lem:labels`). Here `hω` is the event on which the version of `T_G` is equal to it, and `r`
is the scale of the modulus. -/
theorem ofReal_abs_sub_value_le {b : ℝ} (hb : X.IsUpperBound b)
    (V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ) {n W Q : ℝ} (hn : 0 < n) (hW : 0 < W) (hQ : 0 < Q)
    (hWQ : W ^ 2 = n * Q) {L : ℕ} (hL : 16 ≤ L) {κ M θ r : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hκW : Real.sqrt m * κ ≤ 1) (hκr : Real.sqrt m * κ * W ≤ r) (hM : 0 ≤ M) (i : ℕ)
    (z : Fin m → ℤ) (ω : X.Ω)
    (hω : ∀ u ∈ closure (block n W L i z), ∀ v ∈ closure (block n W L i z),
      V i z ω (u, v) = X.setTime b (closure (block n W L i z)) ω u v)
    {u v : Pt m} (hu : u ∈ coreFace n W L i z) (hv : v ∈ coreFace n W L (i + 1) z) :
    ENNReal.ofReal |(X.slabTime b (chainSlab n 0 i) ω u v - n) / Q -
        (tgFamily X V n W Q L κ M θ).value ((tgFamily X V n W Q L κ M θ).label i z ω)
          (u - blockCorner n W i z) (v - blockCorner n W i z)| ≤
      modTerm X b n W Q r L i z ω + ENNReal.ofReal (2 * m * L * κ) +
        ENNReal.ofReal (profSup X b n W L i z ω / Q - M / 2) +
        ENNReal.ofReal (m * L ^ 2 / 2 - M / 2) + eventTerm X b n W L i z M ω +
        ENNReal.ofReal κ + mergeTerm X V n W Q L κ M θ i z ω := by
  classical
  have hL1 : 1 ≤ L := by omega
  obtain ⟨ab, huf, hu'f, hvs, hv's, hbu', hbv', hdu, hdv, hgeo, hn', hup⟩ :=
    exists_pair_round hn hW hWQ hκ hκ1 hκW hL hu hv
  obtain ⟨pq, hpq⟩ : ∃ pq : GridPair m L κ, pq = (gridCell W L κ (u - blockCorner n W i z),
      gridCell W L κ (v - blockCorner n W i z)) := ⟨_, rfl⟩
  have hpts : pairPts n W L κ i z pq =
      (roundPt n W L κ i z 0 u, roundPt n W L κ i z n v) := by
    rw [hpq]
    rfl
  obtain ⟨u', hu'⟩ : ∃ u', u' = roundPt n W L κ i z 0 u := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v', v' = roundPt n W L κ i z n v := ⟨_, rfl⟩
  rw [← hu', ← hv'] at hpts hgeo hn' hup
  rw [← hu'] at hu'f hbu' hdu
  rw [← hv'] at hv's hbv' hdv
  obtain ⟨huc, hvc⟩ := pairPts_mem hn.le hW hκ hL1 i z pq
  rw [hpts] at huc hvc
  simp only at huc hvc
  obtain ⟨D, hD⟩ : ∃ D, D = X.slabTime b (chainSlab n 0 i) ω := ⟨_, rfl⟩
  have hDp : ∀ x y, X.slabTime b (pairOf n W i z ab).slab ω x y = D x y := fun x y => by
    rw [hD]
    exact congrFun (congrFun (slabTime_coverPair_slab X b n W i z _ _ ω) x) y
  -- the first term
  obtain ⟨modS, hmodS⟩ : ∃ modS, modS = Contracts.modulusSup
      (X.slabTime b (pairOf n W i z ab).slab ω) (pairOf n W i z ab).first
      (pairOf n W i z ab).second r := ⟨_, rfl⟩
  have h1 : |D u v - D u' v' - dist u v + dist u' v'| ≤ modS := by
    have := abs_slabTime_sub_sub_add_le_modulusSup X hb (pairOf n W i z ab) hn.le ω huf hu'f hvs
      hv's (hdu.trans hκr) (hdv.trans hκr)
    rwa [hDp u v, hDp u' v', ← hmodS] at this
  have hY1 : |(D u v - n) / Q - (D u' v' - n) / Q| ≤ modS / Q + 2 * m * L * κ := by
    have e1 : (D u v - n) / Q - (D u' v' - n) / Q =
        ((D u v - D u' v' - dist u v + dist u' v') + (dist u v - dist u' v')) / Q := by ring
    have e2 : (modS / Q + 2 * m * L * κ) * Q = modS + 2 * m * L * κ * Q := by field_simp
    rw [e1, abs_div, abs_of_pos hQ, div_le_iff₀ hQ, e2]
    have h3 := abs_add_le (D u v - D u' v' - dist u v + dist u' v') (dist u v - dist u' v')
    linarith only [h1, hgeo, h3]
  -- the second term
  obtain ⟨P, hP⟩ : ∃ P, P = profSup X b n W L i z ω := ⟨_, rfl⟩
  have h2 : |D u' v' - dist u' v'| ≤ P := by
    have h3 := abs_slabTime_sub_dist_le_iSup X hb (pairOf n W i z ab) hn.le ω hu'f hv's
    rw [hDp u' v'] at h3
    refine h3.trans ?_
    rw [hP]
    exact Finset.le_sup' (fun ab ω =>
      ⨆ (u : (pairOf n W i z ab).first) (v : (pairOf n W i z ab).second),
        |X.slabTime b (pairOf n W i z ab).slab ω u v - dist (u : Pt m) v|)
      (Finset.mem_univ ab) ω
  have hYabs : |(D u' v' - n) / Q| ≤ P / Q + m * L ^ 2 / 2 := by
    have e2 : (P / Q + m * L ^ 2 / 2) * Q = P + m * L ^ 2 * Q / 2 := by field_simp
    rw [abs_div, abs_of_pos hQ, div_le_iff₀ hQ, e2]
    have h3 := abs_add_le (D u' v' - dist u' v') (dist u' v' - n)
    rw [show D u' v' - dist u' v' + (dist u' v' - n) = D u' v' - n by ring,
      abs_of_nonneg (show 0 ≤ dist u' v' - n by linarith only [hn'])] at h3
    linarith only [h2, h3, hup]
  have hmax : max (|(D u' v' - n) / Q| - M) 0 ≤
      max (P / Q - M / 2) 0 + max (m * L ^ 2 / 2 - M / 2) 0 := by
    have h3 := le_max_left (P / Q - M / 2) 0
    have h4 := le_max_right (P / Q - M / 2) 0
    have h5 := le_max_left ((m : ℝ) * L ^ 2 / 2 - M / 2) 0
    have h6 := le_max_right ((m : ℝ) * L ^ 2 / 2 - M / 2) 0
    exact max_le (by linarith only [h3, h5, hYabs]) (by linarith only [h4, h6])
  -- the third term
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = if ω ∈ stepOneEvent X b n W L i z then 2 * M else 0 := ⟨_, rfl⟩
  have hclip : |clampM M ((D u' v' - n) / Q) - clampM M ((V i z ω (u', v') - n) / Q)| ≤ e := by
    by_cases hE : ω ∈ stepOneEvent X b n W L i z
    · rw [he, ite_eq_left hE]
      exact abs_clampM_sub_clampM_le_two_mul hM _ _
    · have hTG : V i z ω (u', v') = D u' v' := by
        rw [hω u' huc v' hvc, hD]
        exact setTime_eq_slabTime_of_notMem_stepOneEvent X hb hn hE ab hu'f hv's hbu' hbv' huc hvc
      rw [he, ite_eq_right hE, hTG, sub_self, abs_zero]
  have he0 : 0 ≤ e := by
    rw [he]
    split_ifs
    · linarith only [hM]
    · exact le_rfl
  have hY3 := abs_sub_dequantize_quantize_le (x := (D u v - n) / Q) hM hκ hclip
  -- the term of Step 3
  have hcode : psiCode X V n W Q L κ M i z ω pq =
      quantize M κ ((V i z ω (u', v') - n) / Q) := by
    simp only [psiCode, hpts]
  obtain ⟨mR, hmR⟩ : ∃ mR : ℝ, mR = if lambdaCode X V n W Q L κ M θ i z ω ≠
      psiCode X V n W Q L κ M i z ω then 2 * (M + κ) else 0 := ⟨_, rfl⟩
  have hY4 : |dequantize M κ (psiCode X V n W Q L κ M i z ω pq) -
      dequantize M κ (lambdaCode X V n W Q L κ M θ i z ω pq)| ≤ mR := by
    by_cases heq : lambdaCode X V n W Q L κ M θ i z ω = psiCode X V n W Q L κ M i z ω
    · simp only [hmR, heq, ne_eq, not_true_eq_false, ite_false, sub_self, abs_zero, le_refl]
    · simp only [hmR, heq, ne_eq, not_false_eq_true, ite_true]
      have h3 := abs_sub (dequantize M κ (psiCode X V n W Q L κ M i z ω pq))
        (dequantize M κ (lambdaCode X V n W Q L κ M θ i z ω pq))
      have h4 := abs_dequantize_le hM hκ (psiCode X V n W Q L κ M i z ω pq)
      have h5 := abs_dequantize_le hM hκ (lambdaCode X V n W Q L κ M θ i z ω pq)
      linarith only [h3, h4, h5]
  -- the real bound
  have hval : (tgFamily X V n W Q L κ M θ).value ((tgFamily X V n W Q L κ M θ).label i z ω)
      (u - blockCorner n W i z) (v - blockCorner n W i z) =
      dequantize M κ (lambdaCode X V n W Q L κ M θ i z ω pq) := by
    rw [hpq]
    rfl
  rw [← hcode] at hY3
  have hreal : |(D u v - n) / Q - dequantize M κ (lambdaCode X V n W Q L κ M θ i z ω pq)| ≤
      modS / Q + 2 * m * L * κ + max (P / Q - M / 2) 0 + max (m * L ^ 2 / 2 - M / 2) 0 + e + κ +
        mR := by
    have h3 := abs_sub_le ((D u v - n) / Q) (dequantize M κ (psiCode X V n W Q L κ M i z ω pq))
      (dequantize M κ (lambdaCode X V n W Q L κ M θ i z ω pq))
    linarith only [h3, hY1, hY3, hY4, hmax]
  -- to `[0, ∞]`
  rw [hval, ← hD]
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  have hTm : ENNReal.ofReal mR ≤ mergeTerm X V n W Q L κ M θ i z ω := by
    simp only [mergeTerm, hmR]
    split_ifs with hne
    · rw [indicator_of_mem (show ω ∈ {ω | lambdaCode X V n W Q L κ M θ i z ω ≠
        psiCode X V n W Q L κ M i z ω} from hne)]
    · simp
  have hTe : ENNReal.ofReal e ≤ eventTerm X b n W L i z M ω := by
    by_cases hE : ω ∈ stepOneEvent X b n W L i z
    · rw [he, ite_eq_left hE, eventTerm, indicator_of_mem (subset_toMeasurable _ _ hE)]
    · rw [he, ite_eq_right hE, ENNReal.ofReal_zero]
      exact zero_le
  have hTp : ENNReal.ofReal (max (P / Q - M / 2) 0) ≤
      ENNReal.ofReal (profSup X b n W L i z ω / Q - M / 2) := by
    rw [hP, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  have hTc : ENNReal.ofReal (max (m * L ^ 2 / 2 - M / 2) 0) ≤
      ENNReal.ofReal (m * L ^ 2 / 2 - M / 2) := by
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  have hTs : ENNReal.ofReal (modS / Q) ≤ modTerm X b n W Q r L i z ω := by
    rw [hmodS]
    exact Finset.single_le_sum (f := fun ab : PairIdx m L => ENNReal.ofReal (Contracts.modulusSup
      (X.slabTime b (pairOf n W i z ab).slab ω) (pairOf n W i z ab).first
        (pairOf n W i z ab).second r / Q)) (fun _ _ => zero_le) (Finset.mem_univ ab)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ hTm)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ le_rfl)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ hTe)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ hTc)
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ hTp)
  exact ENNReal.ofReal_add_le.trans (add_le_add hTs le_rfl)

end IsotropicVariance.Paper.Proofs.Labels
