/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.EndPoints
public import IsotropicVariance.Paper.Proofs.Localization.TiltCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import IsotropicVariance.Paper.Proofs.Profiles.Asymptotics
import IsotropicVariance.Paper.Proofs.Profiles.Scales

/-!
# Lemma `lem:localization`, equation `eq:localization`

`localization_at_slope`: Lemma `lem:tree`, equation `eq:profiles` and equation `eq:parent` give
equation `eq:localization` for `T_S`, at any slope `κ ≤ 1` of the centers, by the paper's proof of
Lemma `lem:localization`, which has `κ = 1/2`:

* the frame of the pair and the region of the curves (first paragraph of the proof; `TiltCore`);
* the upper bound, through `−(n/16) e₁` and `(r + n/16) e₁` (second paragraph; `EndPoints`);
* the lower bound, equation `eq:boxpenalty`, over the boxes (third paragraph; `LocalBoxes`,
  `EndPoints`, and the union over the boxes `isOs_boxPenalty`);
* the bound on `|w|` and the tilt bound (last paragraph; `Tilt`, `TiltCore`).

Isotropy enters through equation `eq:parent` at general points (`Profiles.isOs_passTime_of_TRV`).

The slope `κ` is read only by the tilt bound and by `r ≤ (1 + κ)n ≤ 2n`, and the constants chosen
in the proof do not depend on it.

* `localizationStatement_of`: Lemma `lem:localization`, the instance `κ = 1/2`.
* `overviewTransverseStatement_of`: display `eq:transverse` of the overview, the instance `κ = 1`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

universe u

open IsotropicVariance.Paper.Proofs.Profiles (Q_nonneg Q_pos W_sq)
namespace IsotropicVariance.Paper.Proofs.Localization

open Contracts Cited Infra.Os

variable {m : ℕ}

/-- **Equation `eq:localization` from the random bounds** (the last paragraph of the proof of Lemma
`lem:localization`): if the bounds for `T(a, u)`, `T(v, b)`, `T_S(u, v)` and equation
`eq:boxpenalty` hold for every outcome, with errors that are `O_1` up to constants, then
`W⁻¹ sup dist(x, [u, v]) ≤ O_2(·)`. -/
theorem isOs_deviation_of_tilt (X : Setting m) {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B)
    {σ : X.Ω → Pt m → ℝ} {a₀ b : ℝ} (ha₀ : 0 < a₀) (haσ : ∀ ω x, a₀ ≤ σ ω x)
    (hσb : ∀ ω x, σ ω x ≤ b) (hρσ : ∀ ω x, X.ρ ω x ≤ σ ω x) {S : Set (Pt m)} (hS : Convex ℝ S)
    (g : Pt m ≃ᵃⁱ[ℝ] Pt m) {n r W Qn C₀ c' κ : ℝ} (hn : 0 < n) (hW : 0 < W) (hQ : 0 < Qn)
    (hWQ : W ^ 2 = n * Qn) (hc' : 0 < c') (hrε : n / 2 ≤ r - 2 * (2 * Real.sqrt m * W))
    (hC₀ : (b * (r + 2 * (2 * Real.sqrt m * W)) + 1) / a₀ + 2 * Real.sqrt m * W ≤ C₀ * n)
    (hκ : κ ≤ 1) (htilt : ∀ z ∈ S, -(κ * ‖Pt.tr (g.symm z)‖) ≤ Pt.lon (g.symm z) ∧
      Pt.lon (g.symm z) ≤ r + κ * ‖Pt.tr (g.symm z)‖)
    {I I' : Set (Pt m)} (hI : ∀ u ∈ I, dist u (g 0) ≤ 2 * Real.sqrt m * W)
    (hI' : ∀ v ∈ I', dist v (g (r • e₁)) ≤ 2 * Real.sqrt m * W) (hIS : I ⊆ S) (hI'S : I' ⊆ S)
    {Z₁ P₁ Z₂ P₂ Y G : X.Ω → ℝ} {θT θP θ₃ θ₄ c₁ c₂ c₃ : ℝ} (hθT : 0 < θT) (hθP : 0 < θP)
    (hθ₃ : 0 < θ₃) (hθ₄ : 0 < θ₄) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (hZ₁ : IsOs X.P 1 θT Z₁) (hP₁ : IsOs X.P 1 θP P₁) (hZ₂ : IsOs X.P 1 θT Z₂)
    (hP₂ : IsOs X.P 1 θP P₂) (hY : IsOs X.P 1 θ₃ Y) (hG : IsOs X.P 1 θ₄ G)
    (h1 : ∀ ω, ∀ u ∈ I, X.passTime ω (anchorA g n C₀) u ≤
      Pt.lon (g.symm u) + 2 * C₀ * n + (Z₁ ω + P₁ ω + c₁))
    (h2 : ∀ ω, ∀ v ∈ I', X.passTime ω v (anchorB g n r C₀) ≤
      r + 2 * C₀ * n - Pt.lon (g.symm v) + (Z₂ ω + P₂ ω + c₂))
    (h3 : ∀ ω, ∀ u ∈ I, ∀ v ∈ I', restrictedPassageTime (σ ω) S u v ≤ dist u v + Y ω)
    (h4 : ∀ ω, ∀ ζ : Pt m, |Pt.lon ζ| ≤ C₀ * n → ‖Pt.tr ζ‖ ≤ C₀ * n →
      c' * ‖Pt.tr ζ‖ ^ 2 / n ≤ X.passTime ω (anchorA g n C₀) (g ζ) +
        X.passTime ω (g ζ) (anchorB g n r C₀) - (r + 4 * C₀ * n) + (G ω + c₃))
    (hΦ : AEMeasurable (fun ω => W⁻¹ * maxSegmentDeviation (σ ω) S I I') X.P) :
    IsOs X.P 2 (Real.sqrt ((2 * 2 ^ 2 + 1) *
        ((θT + θP + (θT + θP) + θ₃ + θ₄ +
            (c₁ + c₂ + c₃ + 1 + 4 * (2 * Real.sqrt m * W) ^ 2 / n + 1) / Real.log 2) / (c' * Qn)) +
        (2 * (2 * Real.sqrt m) ^ 2 + 1) / Real.log 2))
      (fun ω => W⁻¹ * maxSegmentDeviation (σ ω) S I I') := by
  set e := 4 * (2 * Real.sqrt m * W) ^ 2 / n with he
  have he0 : 0 ≤ e := by positivity
  have hH := isOs_endSum (c := c₁ + c₂ + c₃ + 1 + e) hθT hθP hθ₃ hθ₄ (by positivity) hZ₁ hP₁ hZ₂
    hP₂ hY hG
  refine isOs_two_of_le_sqrt (by positivity) (mul_pos hc' hQ) hH hΦ fun ω => ?_
  have h := deviation_le_of_tilt X hB ω ha₀ (haσ ω) (hσb ω) (hρσ ω) hS g hn hW hQ hWQ hc' hrε hC₀
    hκ htilt hI hI' hIS hI'S (h1 ω) (h2 ω) (h3 ω) (h4 ω)
  have e1 : Z₁ ω + P₁ ω + (Z₂ ω + P₂ ω) + Y ω + G ω + (c₁ + c₂ + c₃ + 1 + e) =
      Z₁ ω + P₁ ω + c₁ + (Z₂ ω + P₂ ω + c₂) + Y ω + (G ω + c₃) + 1 + e := by ring
  rw [e1]
  exact h

/-- The numerical scale of the proof of Lemma `lem:localization`. -/
lemma tilt_sum_le {CT L₀ CP KG CPar Qn c₁ c₂ : ℝ} (hQ : 1 ≤ Qn)
    (hc₁ : c₁ ≤ CPar * Real.sqrt L₀ * Qn) (hc₂ : c₂ ≤ CPar * Real.sqrt L₀ * Qn) :
    CT * Qn + Real.sqrt L₀ * Qn / 100 + (CT * Qn + Real.sqrt L₀ * Qn / 100) + CP * Qn + KG * Qn +
        (c₁ + c₂ + (2 * CPar * Real.sqrt L₀ * Qn + m * Qn / (2 * L₀)) + 1 + 16 * m * Qn + 1) /
          Real.log 2 ≤
      (2 * (CT + Real.sqrt L₀ / 100) + CP + KG +
        (4 * CPar * Real.sqrt L₀ + m / (2 * L₀) + 16 * m + 2) / Real.log 2) * Qn := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h : c₁ + c₂ + (2 * CPar * Real.sqrt L₀ * Qn + m * Qn / (2 * L₀)) + 1 + 16 * m * Qn + 1 ≤
      (4 * CPar * Real.sqrt L₀ + m / (2 * L₀) + 16 * m + 2) * Qn := by
    have : m * Qn / (2 * L₀) = m / (2 * L₀) * Qn := by ring
    linarith only [this, hQ, hc₁, hc₂]
  have h2 := div_le_div_of_nonneg_right h hlog.le
  rw [show (4 * CPar * Real.sqrt L₀ + m / (2 * L₀) + 16 * m + 2) * Qn / Real.log 2 =
    (4 * CPar * Real.sqrt L₀ + m / (2 * L₀) + 16 * m + 2) / Real.log 2 * Qn by ring] at h2
  linarith only [h2]

/-- **Equation `eq:localization` at a slope `κ ≤ 1`** (the proof of Lemma `lem:localization` has
`κ = 1/2`), from Lemma `lem:tree`, equation `eq:profiles` and equation `eq:parent`: the statement of
Lemma `lem:localization` for the cubes of equation `eq:cubepair` with `s = n` and `|y| ≤ κn`. -/
theorem localization_at_slope (hTree : TreeStatement.{u}) (hProf : ProfilesStatement.{u})
    (hPar : ParentStatement.{u}) {κ : ℝ} (hκ : κ ≤ 1) :
    ∀ (m : ℕ), 1 ≤ m → ∀ X : Setting.{u} m, X.IsNormalized → ∀ b : ℝ, X.IsUpperBound b →
      ∀ Cstar : ℝ, 0 < Cstar → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 → ∀ K : ℕ,
        ∃ N₀ : ℝ, ∀ A N : ℝ, N₀ ≤ N → Standing X Cstar K A N → ∀ n : ℝ, c₁ * N ≤ n → n ≤ N →
          ∀ p : CubePair m, p.IsAdmissible n (W K A n) κ →
            Cited.IsOs X.P 2 C (fun ω => (W K A n)⁻¹ *
              maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first p.second) := by
  intro m hm X hX b hb Cstar hC
  obtain ⟨a₀, b', ha₀, hab⟩ := X.bounds
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure X.P
  have hρa : ∀ ω x, a₀ ≤ X.ρ ω x := fun ω x => (hab ω x).1
  have hab' : a₀ ≤ b := (hρa ω₀ 0).trans (hb ω₀ 0)
  have hb0 : 0 ≤ b := ha₀.le.trans hab'
  -- the constants, independent of `c₁`, `K`, `A`, `N`
  set C₀ : ℝ := 4 * (b + 1) / a₀ + 4 with hC₀def
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ 4 * (b + 1) / a₀ := by positivity
    linarith only [this, hC₀def]
  set L₀ := boxL m C₀
  have hL₀ : 1 ≤ L₀ := one_le_boxL (by linarith only [hC₀1])
  obtain ⟨CT, hCT, hT⟩ := hTree m hm X hX
  obtain ⟨CP, hCP, hP⟩ := hProf m hm X hX b hb Cstar hC
  obtain ⟨CPar, hCPar, hPa⟩ := hPar m hm X hX Cstar hC L₀ (by positivity)
  set θU : ℝ := CT + Real.sqrt L₀ / 100
  have hθU : 0 < θU := by positivity
  set SG : ℝ := ((boxCountLon C₀ : ℝ) + 1) * (2 / (1 - Real.exp (-(1 / (4 * L₀ * (2 * θU)))))) ^ m
  set KG : ℝ := Real.logb 2 (1 + 2 * SG) * (2 * (2 * θU))
  set KH : ℝ := 2 * θU + CP + KG +
    (4 * CPar * Real.sqrt L₀ + m / (2 * L₀) + 16 * m + 2) / Real.log 2
  set c' : ℝ := 1 / (4 * L₀)
  have hc' : 0 < c' := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq : Real.exp (-(1 / (4 * L₀ * (2 * θU)))) < 1 := by
    have : 0 < 1 / (4 * L₀ * (2 * θU)) := by positivity
    exact Real.exp_lt_one_iff.2 (by linarith only [this])
  have hq0 : 0 < 1 - Real.exp (-(1 / (4 * L₀ * (2 * θU)))) := by linarith only [hq]
  have hSGpos : 0 < SG := by positivity
  have hlb : 0 < Real.logb 2 (1 + 2 * SG) :=
    Real.logb_pos one_lt_two (by linarith only [hSGpos])
  have hKG : 0 < KG := by positivity
  refine ⟨Real.sqrt ((2 * 2 ^ 2 + 1) * (KH / c') + (2 * (2 * Real.sqrt m) ^ 2 + 1) / Real.log 2),
    Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos ?_ (by positivity)), fun c₁ hc₁ _ K => ?_⟩
  · have hKH : 0 ≤ KH := by positivity
    exact mul_nonneg (by positivity) (div_nonneg hKH hc'.le)
  obtain ⟨NP, hNP⟩ := hP c₁ hc₁ K
  obtain ⟨NPa, hNPa⟩ := hPa c₁ hc₁ K
  obtain ⟨NW, hNW⟩ := Profiles.exists_W_le Cstar c₁ (1 / (1000 * (Real.sqrt m + 1))) hc₁
    (by positivity)
  refine ⟨max (max NP NPa) (max NW (256 / c₁)), fun A N hN hS n hn hnN p hp => ?_⟩
  have hNP' : NP ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNPa' : NPa ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNW' : NW ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN256 : 256 / c₁ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hK10 : 10 ≤ K := hS.1
  have hA1 : 1 ≤ A := hS.2.1
  have hA0 : 0 < A := by linarith only [hA1]
  have hn256 : 256 ≤ n := by
    have : c₁ * (256 / c₁) ≤ c₁ * N := mul_le_mul_of_nonneg_left hN256 hc₁.le
    rw [mul_div_cancel₀ _ hc₁.ne'] at this; linarith only [this, hn]
  have hn0 : 0 < n := by linarith only [hn256]
  have hQ1 : 1 ≤ Q K A n := Profiles.one_le_Q hK10 hA1 (by linarith only [hn256])
  have hQ0 : 0 < Q K A n := Q_pos hA0 hn0
  have hW1 : 1 ≤ W K A n := one_le_W hK10 hA1 (by linarith only [hn256])
  have hW0 : 0 < W K A n := zero_lt_one.trans_le hW1
  have hWQ : W K A n ^ 2 = n * Q K A n := W_sq hA0.le hn0.le
  obtain ⟨hε, hWn⟩ := eps_le_of_W_le (m := m) hn0.le
    (hNW K hK10 A N hA0.le hNW' hS.2.2.2.2 n hn hnN)
  -- the frame of the pair
  obtain ⟨g, -, hg0, hgr⟩ := Profiles.exists_properRigidMotion hm p.center₁ p.center₂
  obtain ⟨hr1, hr2⟩ := CubePairFacts.dist_centers hp hn0
  have hr0 : 0 ≤ dist p.center₁ p.center₂ := dist_nonneg
  have hr2' : dist p.center₁ p.center₂ ≤ 2 * n := by
    have := mul_le_mul_of_nonneg_right hκ hn0.le
    linarith only [hr2, this]
  have hI : ∀ u ∈ p.first, dist u (g 0) ≤ 2 * Real.sqrt m * W K A n := fun u hu => by
    rw [hg0]; exact CubePairFacts.dist_first_le hp hu
  have hI' : ∀ v ∈ p.second, dist v (g (dist p.center₁ p.center₂ • e₁)) ≤
      2 * Real.sqrt m * W K A n := fun v hv => by
    rw [hgr]; exact CubePairFacts.dist_second_le hp hv
  have hrε : n / 2 ≤ dist p.center₁ p.center₂ - 2 * (2 * Real.sqrt m * W K A n) := by
    linarith only [hr1, hε, hn0]
  have hC₀n := region_le ha₀ hb0 (by linarith only [hn256] : (1 : ℝ) ≤ n) hr2' hε
  have hoff : ‖p.offset‖ ≤ κ * n := by
    have h := hp.2.2.2.2.2
    rwa [CubePair.centerSlope, hp.1, div_le_iff₀ hn0] at h
  -- Lemma `lem:tree` and equation `eq:parent` at fixed `K`, `A`, `N`
  have hTK : TreeAt X (1 / 2) CT K A N := fun t ht ht' x e he B hBox hd hl =>
    hT K A N hS.1 hS.2.1 hS.2.2.1 hS.2.2.2.1 t ht (by linarith only [ht']) x e he B hBox hd hl
  have hPK : ParentAt X c₁ L₀ CPar K A N := hNPa A N hNPa' hS
  -- the upper bound
  have hZ₁ := isOs_endTreeFirst X hTK hK10 hA0 hn256 hnN hCT g hp hg0 hε
  have hZ₂ := isOs_endTreeSecond X hTK hK10 hA0 hn256 hnN hCT g hp hgr hε
  have hP₁ := isOs_endParentFirst X g hm hPK hK10 hA0 hC₀1 hn0 hn hnN
  have hP₂ := isOs_endParentSecond X g (r := dist p.center₁ p.center₂) hm hPK hK10 hA0 hC₀1 hn0 hn
    hnN
  have hB : ∀ ω x, X.ρ ω x ≤ b := hb
  have h1 : ∀ ω, ∀ u ∈ p.first, X.passTime ω (anchorA g n C₀) u ≤
      Pt.lon (g.symm u) + 2 * C₀ * n + (endTreeFirst X g n p.first ω +
        endParentFirst X g n C₀ CPar K A ω +
          CPar * Q K A (dist (anchorA g n C₀) (nearA g n))) := fun ω u hu =>
    end_first_le g (X.passTime ω) (fun x y z => Profiles.passTime_triangle hB ω x y z) hn0.le hC₀1
      (le_treeSup X hB hb0 ω _ _ (norm_frameDir g) hI hu) le_rfl
  have h2 : ∀ ω, ∀ v ∈ p.second, X.passTime ω v (anchorB g n (dist p.center₁ p.center₂) C₀) ≤
      dist p.center₁ p.center₂ + 2 * C₀ * n - Pt.lon (g.symm v) +
        (endTreeSecond X g n (dist p.center₁ p.center₂) p.second ω +
          endParentSecond X g n (dist p.center₁ p.center₂) C₀ CPar K A ω +
            CPar * Q K A (dist (nearB g n (dist p.center₁ p.center₂))
              (anchorB g n (dist p.center₁ p.center₂) C₀))) := fun ω v hv =>
    end_second_le g (X.passTime ω) (fun x y z => Profiles.passTime_triangle hB ω x y z)
      (fun x y => Profiles.passTime_comm ω x y) hn0.le hC₀1
      (le_treeSup X hB hb0 ω _ _ (by rw [norm_neg, norm_frameDir]) hI' hv) le_rfl
  have hNPn := hNP A N hNP' hS n hn hnN p ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.trans hκ⟩
  have hfs := CubePairFacts.first_subset_slab hp hn0.le
  have hss := CubePairFacts.second_subset_slab hp hn0.le
  have h3 : ∀ ω, ∀ u ∈ p.first, ∀ v ∈ p.second,
      restrictedPassageTime (p.slab.density b (X.ρ ω)) p.slab.set u v ≤ dist u v +
        ⨆ (u : p.first) (v : p.second),
          |X.slabTime b p.slab ω u v - dist (u : Pt m) (v : Pt m)| := by
    intro ω u hu v hv
    have := le_profileSup (D := X.slabTime b p.slab ω) (M := (b + 1) * (3 * n))
      (fun u' hu' v' hv' => (abs_sub_dist_le
        (restrictedPassageTime_nonneg _ _ _ _)
        (Infra.Slab.slabTime_le_mul_dist X hb p.slab ω (hfs hu') (hss hv'))
        dist_nonneg).trans (mul_le_mul_of_nonneg_left (by
          have := dist_cubes_le hp hu' hv'; linarith only [this, hr2', hε, hn0])
          (by linarith only [hb0]))) hu hv
    have h2 := le_abs_self (X.slabTime b p.slab ω u v - dist u v)
    change X.slabTime b p.slab ω u v ≤ dist u v + ⨆ (u : p.first) (v : p.second),
      |X.slabTime b p.slab ω u v - dist (u : Pt m) (v : Pt m)|
    linarith only [this, h2]
  -- the lower bound, equation `eq:boxpenalty`
  have hU : ∀ jk ∈ boxIndex m n (W K A n) C₀, IsOs X.P 1 (2 * θU * Q K A n)
      (boxError X g n (dist p.center₁ p.center₂) (W K A n) C₀ CPar K A jk) := by
    intro jk hjk
    have h := isOs_boxError X g (r := dist p.center₁ p.center₂) (CPar := CPar) (K := K) (A := A)
      (mul_pos hCT hQ0) (by positivity)
      (isOs_treePlus_sixteenth X g hTK hK10 hA0 hn256 hnN hCT hε jk)
      (isOs_treeMinus_sixteenth X g hTK hK10 hA0 hn256 hnN hCT hε jk)
      (isOs_parentPlus X g hm hPK hK10 hA0 hC₀1 hn0 hn hnN hr0 hr2' hW0 hWn hjk)
      (isOs_parentMinus X g hm hPK hK10 hA0 hC₀1 hn0 hn hnN hr0 hr2' hW0 hWn hjk)
    refine h.mono_scale zero_le_one (by positivity) (le_of_eq ?_)
    simp only [θU]; ring
  have hG := isOs_boxPenalty X g (L₀ := L₀) rfl (by positivity : 0 < 2 * θU) hQ0
    (by positivity) (fun jk hjk => (hU jk hjk).mono_scale zero_le_one (by positivity)
      (le_of_eq (by ring)))
  replace hG : IsOs X.P 1 (KG * Q K A n) _ :=
    hG.mono_scale zero_le_one (by positivity) (le_of_eq (by simp only [KG]; ring))
  have h4 : ∀ ω, ∀ ζ : Pt m, |Pt.lon ζ| ≤ C₀ * n → ‖Pt.tr ζ‖ ≤ C₀ * n →
      c' * ‖Pt.tr ζ‖ ^ 2 / n ≤ X.passTime ω (anchorA g n C₀) (g ζ) +
        X.passTime ω (g ζ) (anchorB g n (dist p.center₁ p.center₂) C₀) -
          (dist p.center₁ p.center₂ + 4 * C₀ * n) +
          (boxPenalty X g n (dist p.center₁ p.center₂) (W K A n) C₀ CPar K A L₀ ω +
            (2 * CPar * Real.sqrt L₀ * Q K A n + m * Q K A n / (2 * L₀))) := by
    intro ω ζ hlon htr
    have := penalty_bound X hB hb0 ω g hn0 hW0 hWn hC₀1 hr0 hr2' hK10 hA0.le hWQ
      hCPar.le hlon htr
    linarith only [this]
  -- the last step
  have hend1 := Q_le_of_le_boxL (m := m) hK10 hA0.le hn0.le hC₀1 dist_nonneg
    ((dist_anchorA_nearA g hn0.le hC₀1).trans_le (end_length_bounds hn0.le hC₀1).2)
  have hend2 := Q_le_of_le_boxL (m := m) hK10 hA0.le hn0.le hC₀1 dist_nonneg
    ((dist_nearB_anchorB (r := dist p.center₁ p.center₂) g hn0.le hC₀1).trans_le
      (end_length_bounds hn0.le hC₀1).2)
  have hc₁0 : 0 ≤ CPar * Q K A (dist (anchorA g n C₀) (nearA g n)) :=
    mul_nonneg hCPar.le (Q_nonneg hA0.le dist_nonneg)
  have hc₂0 : 0 ≤ CPar * Q K A (dist (nearB g n (dist p.center₁ p.center₂))
      (anchorB g n (dist p.center₁ p.center₂) C₀)) :=
    mul_nonneg hCPar.le (Q_nonneg hA0.le dist_nonneg)
  have hdev := isOs_deviation_of_tilt X hB (σ := fun ω => p.slab.density b (X.ρ ω)) ha₀
    (fun ω x => le_slabDensity X hb hρa p.slab ω x)
    (fun ω x => (p.slab.density_le b (hb ω) x).trans (max_self b).le)
    (fun ω x => slabDensity_ge p.slab (hb ω) x) (Infra.Slab.convex_slab_set p.slab) g hn0 hW0 hQ0
    hWQ hc' hrε hC₀n hκ
    (fun z hz => tilt_of_mem_slab g hp.1 hn0 hoff (hn0.trans_le hr1) hg0 hgr hz)
    hI hI' hfs hss (mul_pos hCT hQ0) (by positivity) (mul_pos hCP hQ0) (mul_pos hKG hQ0)
    hc₁0 hc₂0 (by positivity) hZ₁ hP₁ hZ₂ hP₂ hNPn.2 hG h1 h2 h3 h4
    ((aemeasurable_maxSegmentDeviation_slab X hb p.slab CubePairFacts.isCompact_first
      CubePairFacts.isCompact_second).const_mul _)
  refine hdev.mono_scale (by norm_num) (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos ?_
    (by positivity))) ?_
  · exact mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity))
  rw [curv_eq (m := m) hn0 hWQ]
  refine final_scale_le hc' hQ0 (by positivity) ?_
  have hscale := tilt_sum_le (m := m) (CT := CT) (L₀ := L₀) (CP := CP) (KG := KG) (CPar := CPar)
    hQ1 (c₁ := CPar * Q K A (dist (anchorA g n C₀) (nearA g n)))
    (c₂ := CPar * Q K A (dist (nearB g n (dist p.center₁ p.center₂))
      (anchorB g n (dist p.center₁ p.center₂) C₀)))
    (by have := mul_le_mul_of_nonneg_left hend1 hCPar.le; linarith only [this])
    (by have := mul_le_mul_of_nonneg_left hend2 hCPar.le; linarith only [this])
  simpa only [θU, KH] using hscale

/-- **Lemma `lem:localization`, equation `eq:localization`**, from Lemma `lem:tree`, equation
`eq:profiles` and equation `eq:parent`: the instance `κ = 1/2` of `localization_at_slope`. -/
theorem localizationStatement_of (hTree : TreeStatement.{u}) (hProf : ProfilesStatement.{u})
    (hPar : ParentStatement.{u}) : LocalizationStatement.{u} :=
  localization_at_slope hTree hProf hPar (by norm_num)

/-- **Equation `eq:transverse`** of the proof overview (Section `ssec:overview`), from Lemma
`lem:tree`, equation `eq:profiles` and equation `eq:parent`: the instance `κ = 1` of
`localization_at_slope`. -/
theorem overviewTransverseStatement_of (hTree : TreeStatement.{u}) (hProf : ProfilesStatement.{u})
    (hPar : ParentStatement.{u}) : OverviewTransverseStatement.{u} :=
  localization_at_slope hTree hProf hPar le_rfl

end IsotropicVariance.Paper.Proofs.Localization
