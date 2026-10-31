/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Modulus.ModulusPhi
public import IsotropicVariance.Paper.Proofs.Modulus.ModulusInstances
public import IsotropicVariance.Paper.Defs.SetTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rerouting the near-geodesics off the event `E`

The second paragraph of the proof of Lemma `lem:modulus`, and the third up to the bound off `E`.

* `reroute_le`: the display of the rerouting, with its slack `3`, for general densities
  and sets: the end pieces of a near-geodesic are replaced by near-geodesics of `S₁`, `S₂`.
* `density_le_of_subset`: `ρ_S ≤ ρ_{S₁}` on `S₁`, through `setDensity_mono`.
* `near_slab_le`, `far_slab_le`: the bound `D` of the proof for `T_{S₁}`, `T_{S₂}`; here
  `D` is the maximum `smallMax` of the union bound over the small pairs of cubes.
* `modulus_one_side_phi`, `modulusSup_le_phi`: off `E`, `Z ≤ 4D + 3 + E₀`, where `E₀` bounds the `φ`
  terms (`phi_terms_le`).

The points `x₁`, `x₂` are points of the curve on `H₁`, `H₂` at times `t₁ ≤ t₂` (`exists_hits`). The
paper takes the first point on `H₁` and the last point on `H₂`; the proof uses only that the points
lie on these hyperplanes, in this order along the curve.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Modulus

open Infra.Slab Infra.Os Proofs.Localization

variable {m : ℕ}

/-- The cost of a near-geodesic bounds the passage times of its end pieces plus the cost of its
middle piece, the end pieces for any smaller density `τ`. -/
lemma cost_cut_le {σ τ : Pt m → ℝ} (hσ : Measurable σ) {B : ℝ} (hσB : ∀ x, σ x ≤ B)
    (hτσ : ∀ x, τ x ≤ σ x) {S : Set (Pt m)} {u v : Pt m} {γ : RectifiableCurve (Pt m)}
    (hγ : IsOneOptimal σ S u v γ) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h1 : t₂ ≤ 1) :
    passageTime τ u (γ.toFun t₁) +
        ((γ.subcurve t₁ t₂ h0 h12 h1).cost fun x => ENNReal.ofReal (σ x)).toReal +
      passageTime τ (γ.toFun t₂) v ≤ restrictedPassageTime σ S u v + 1 := by
  obtain ⟨hγ0, hγ1, hS, hc⟩ := (isOneOptimal_iff hσB).1 hγ
  have hτB : ∀ x, τ x ≤ B := fun x => (hτσ x).trans (hσB x)
  set ρσ : Pt m → ℝ≥0∞ := fun x => ENNReal.ofReal (σ x) with hρσ
  have hρm : Measurable ρσ := ENNReal.measurable_ofReal.comp hσ
  set c₁ := (γ.subcurve 0 t₁ le_rfl h0 (h12.trans h1)).cost ρσ
  set c₂ := (γ.subcurve t₁ t₂ h0 h12 h1).cost ρσ
  set c₃ := (γ.subcurve t₂ 1 (h0.trans h12) h1 le_rfl).cost ρσ
  have hsplit : c₁ + c₂ + c₃ = γ.cost ρσ := by
    rw [γ.cost_subcurve_add hρm le_rfl h0 h12 h1,
      γ.cost_subcurve_add hρm le_rfl (h0.trans h12) h1 le_rfl, cost_subcurve_zero_one]
  have hfin : ∀ δ : RectifiableCurve (Pt m), δ.cost ρσ ≠ ⊤ := fun δ => cost_ne_top hσB δ
  have p₁ : passageTime τ u (γ.toFun t₁) ≤ c₁.toReal := by
    have h := passageTime_le_cost hτB (γ.subcurve 0 t₁ le_rfl h0 (h12.trans h1))
    rw [RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end, hγ0] at h
    exact h.trans (ENNReal.toReal_mono (hfin _)
      (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hτσ _)))
  have p₃ : passageTime τ (γ.toFun t₂) v ≤ c₃.toReal := by
    have h := passageTime_le_cost hτB (γ.subcurve t₂ 1 (h0.trans h12) h1 le_rfl)
    rw [RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end, hγ1] at h
    exact h.trans (ENNReal.toReal_mono (hfin _)
      (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hτσ _)))
  have hR : restrictedInf σ S u v ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin γ) (restrictedInf_le_cost γ hγ0 hγ1 hS)
  have htot : c₁.toReal + c₂.toReal + c₃.toReal ≤ restrictedPassageTime σ S u v + 1 := by
    rw [← ENNReal.toReal_add (hfin _) (hfin _), ← ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩) (hfin _), hsplit, restrictedPassageTime_eq_toReal]
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hR, ENNReal.one_ne_top⟩) hc
    rwa [ENNReal.toReal_add hR ENNReal.one_ne_top, ENNReal.toReal_one] at this
  linarith only [p₁, p₃, htot]

/-- **The rerouting**: for a near-geodesic `γ` from `u` to `v` in `S` and
its points `x₁ = γ(t₁)`, `x₂ = γ(t₂)`, replacing the pieces before `x₁` and after `x₂` by curves of
`Π_{T_{S₁}}(u₁, x₁)` and `Π_{T_{S₂}}(x₂, v₁)` gives
`T_S(u₁, v₁) − T_S(u, v) ≤ T_{S₁}(u₁, x₁) − T(u, x₁) + T_{S₂}(x₂, v₁) − T(x₂, v) + 3`, where
`ρ ≤ σ` is the density of `T`, and `σ ≤ σᵢ` on `Sᵢ ⊆ S`. -/
theorem reroute_le {ρ σ σ₁ σ₂ : Pt m → ℝ} {S S₁ S₂ : Set (Pt m)} {B : ℝ} (hσm : Measurable σ)
    (hσB : ∀ x, σ x ≤ B) (hρσ : ∀ x, ρ x ≤ σ x) (hS₁ : S₁ ⊆ S) (hS₂ : S₂ ⊆ S)
    (hσ₁ : ∀ x ∈ S₁, σ x ≤ σ₁ x) (hσ₂ : ∀ x ∈ S₂, σ x ≤ σ₂ x) {u v u₁ v₁ : Pt m}
    {γ π₁ π₂ : RectifiableCurve (Pt m)} (hγ : IsOneOptimal σ S u v γ) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁)
    (h12 : t₁ ≤ t₂) (h1 : t₂ ≤ 1) (hπ₁ : IsOneOptimal σ₁ S₁ u₁ (γ.toFun t₁) π₁)
    (hπ₂ : IsOneOptimal σ₂ S₂ (γ.toFun t₂) v₁ π₂) :
    restrictedPassageTime σ S u₁ v₁ - restrictedPassageTime σ S u v ≤
      restrictedPassageTime σ₁ S₁ u₁ (γ.toFun t₁) - passageTime ρ u (γ.toFun t₁) +
        (restrictedPassageTime σ₂ S₂ (γ.toFun t₂) v₁ - passageTime ρ (γ.toFun t₂) v) + 3 := by
  have hcut := cost_cut_le hσm hσB hρσ hγ h0 h12 h1
  obtain ⟨-, -, hS, -⟩ := id hγ
  obtain ⟨hπ₁0, hπ₁1, hπ₁S, hπ₁c⟩ := hπ₁
  obtain ⟨hπ₂0, hπ₂1, hπ₂S, hπ₂c⟩ := hπ₂
  set c : Pt m → ℝ≥0∞ := fun x => ENNReal.ofReal (σ x)
  have hcm : Measurable c := ENNReal.measurable_ofReal.comp hσm
  have hfin : ∀ δ : RectifiableCurve (Pt m), δ.cost c ≠ ⊤ := fun δ => cost_ne_top hσB δ
  set mid := γ.subcurve t₁ t₂ h0 h12 h1
  have he₁ : π₁.toFun 1 = mid.toFun 0 := by rw [hπ₁1, RectifiableCurve.subcurve_start]
  set e₁ := π₁.concat mid he₁
  have he₂ : e₁.toFun 1 = π₂.toFun 0 := by
    rw [RectifiableCurve.concat_end, RectifiableCurve.subcurve_end, hπ₂0]
  set e₂ := e₁.concat π₂ he₂
  have h20 : e₂.toFun 0 = u₁ := by
    rw [RectifiableCurve.concat_start, RectifiableCurve.concat_start, hπ₁0]
  have h21 : e₂.toFun 1 = v₁ := by rw [RectifiableCurve.concat_end, hπ₂1]
  have h2S : ∀ t ∈ Icc (0 : ℝ) 1, e₂.toFun t ∈ S :=
    concat_mem he₂ (concat_mem he₁ (fun t ht => hS₁ (hπ₁S t ht)) (subcurve_mem hS h0 h12 h1))
      fun t ht => hS₂ (hπ₂S t ht)
  have hcost : e₂.cost c = π₁.cost c + mid.cost c + π₂.cost c := by
    rw [RectifiableCurve.cost_concat _ _ he₂ hcm, RectifiableCurve.cost_concat _ _ he₁ hcm]
  have hle : restrictedPassageTime σ S u₁ v₁ ≤
      (π₁.cost c).toReal + (mid.cost c).toReal + (π₂.cost c).toReal := by
    rw [restrictedPassageTime_eq_toReal, ← ENNReal.toReal_add (hfin _) (hfin _), ← ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩) (hfin _), ← hcost]
    exact ENNReal.toReal_mono (hfin _) (restrictedInf_le_cost e₂ h20 h21 h2S)
  have hc₁ : (π₁.cost c).toReal ≤ restrictedPassageTime σ₁ S₁ u₁ (γ.toFun t₁) + 1 :=
    ENNReal.toReal_le_of_le_ofReal (add_nonneg (restrictedPassageTime_nonneg _ _ _ _) zero_le_one)
      ((cost_mono_of_forall_mem π₁ fun t ht =>
        ENNReal.ofReal_le_ofReal (hσ₁ _ (hπ₁S t ht))).trans hπ₁c)
  have hc₂ : (π₂.cost c).toReal ≤ restrictedPassageTime σ₂ S₂ (γ.toFun t₂) v₁ + 1 :=
    ENNReal.toReal_le_of_le_ofReal (add_nonneg (restrictedPassageTime_nonneg _ _ _ _) zero_le_one)
      ((cost_mono_of_forall_mem π₂ fun t ht =>
        ENNReal.ofReal_le_ofReal (hσ₂ _ (hπ₂S t ht))).trans hπ₂c)
  linarith only [hcut, hle, hc₁, hc₂]

/-! ## The slabs `S₁`, `S₂` -/

lemma near_slab_subset (p : CubePair m) {κn σ : ℝ} (c : EuclideanSpace ℝ (Fin m)) (a d : Fin m → ℤ)
    (hκ : κn ≤ p.dist) : (nearPair p κn σ c a d).slab.set ⊆ p.slab.set := fun x hx => by
  rw [mem_slab_set_iff, slabCoord_nearPair] at hx
  exact (mem_slab_set_iff _).mpr ⟨hx.1, hx.2.trans hκ⟩

lemma far_slab_subset (p : CubePair m) {κn σ : ℝ} (c : EuclideanSpace ℝ (Fin m)) (d a : Fin m → ℤ)
    (hκ : κn ≤ p.dist) : (farPair p κn σ c d a).slab.set ⊆ p.slab.set := fun x hx => by
  rw [mem_slab_set_iff, slabCoord_farPair] at hx
  have h2 : slabCoord p.slab x - (p.dist - κn) ≤ κn := hx.2
  have h3 : slabCoord p.slab x ≤ p.dist := by linarith only [h2]
  exact (mem_slab_set_iff _).mpr ⟨by linarith only [hx.1, hκ], h3⟩

/-- `ρ_S ≤ ρ_{S₁}` on `S₁`, for a slab `S₁` in the slab `S`. -/
lemma density_le_of_subset {big thin : Slab m} (hbig : 0 < big.width) (hthin : 0 < thin.width)
    (hsub : thin.set ⊆ big.set) {b : ℝ} {τ : Pt m → ℝ} (hb : ∀ y, τ y ≤ b) :
    ∀ x ∈ thin.set, big.density b τ x ≤ thin.density b τ x := fun x hx => by
  rw [big.density_eq_setDensity hbig, thin.density_eq_setDensity hthin]
  exact setDensity_mono hb (isClosed_slab_set thin) hsub hx

/-- The bound `D` for `T_{S₁}`. -/
lemma near_slab_le (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {p : CubePair m} {κn σ : ℝ}
    {L : ℕ} (hσ : 0 ≤ σ) (hκ : 0 ≤ κn) {a d : Fin m → ℤ} (ha : a ∈ box m L) (hd : d ∈ box m L)
    {u x : Pt m} (hu : u ∈ (nearPair p κn σ (nearCenter p κn) a d).first)
    (hx : x ∈ (nearPair p κn σ (nearCenter p κn) a d).second) (ω : X.Ω) :
    X.slabTime b (nearPair p κn σ (nearCenter p κn) a d).slab ω u x - dist u x ≤
      max (smallMax X b p κn σ L ω) 0 := by
  obtain ⟨C, hC⟩ := pairBound_slabTime X hb (nearPair p κn σ (nearCenter p κn) a d) hσ hσ hκ ω
  refine (le_abs_self _).trans ((le_pairSup hC hu hx).trans ((le_of_eq ?_).trans
    ((le_smallMax X b p κn σ (mem_smallIndex 1 ha hd) ω).trans (le_max_left _ _))))
  simp [smallFamily]

/-- The bound `D` for `T_{S₂}`. -/
lemma far_slab_le (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {p : CubePair m} {κn σ : ℝ}
    {L : ℕ} (hσ : 0 ≤ σ) (hκ : 0 ≤ κn) {d a : Fin m → ℤ} (hd : d ∈ box m L) (ha : a ∈ box m L)
    {y v : Pt m} (hy : y ∈ (farPair p κn σ (farCenter p κn) d a).first)
    (hv : v ∈ (farPair p κn σ (farCenter p κn) d a).second) (ω : X.Ω) :
    X.slabTime b (farPair p κn σ (farCenter p κn) d a).slab ω y v - dist y v ≤
      max (smallMax X b p κn σ L ω) 0 := by
  obtain ⟨C, hC⟩ := pairBound_slabTime X hb (farPair p κn σ (farCenter p κn) d a) hσ hσ hκ ω
  refine (le_abs_self _).trans ((le_pairSup hC hy hv).trans ((le_of_eq ?_).trans
    ((le_smallMax X b p κn σ (mem_smallIndex 3 hd ha) ω).trans (le_max_left _ _))))
  simp [smallFamily]

/-! ## The bound off `E` -/

/-- **One side of the bound off `E`**: if the near-geodesics of `T_S`
between `I` and `I'` stay within `λ` of their segments, then
`T_S(ũ, ṽ) − |ṽ − ũ| − T_S(u, v) + |v − u| ≤ 4D + 3 + E₀`, with `D` the maximum `smallMax` and `E₀`
the bound of the `φ` terms. -/
theorem modulus_one_side_phi (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {Bd : ℝ}
    (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd) {p : CubePair m} {κn σ lam R₀ δ : ℝ} {L : ℕ}
    (H : CutData p κn σ lam L) (hR₁ : Real.sqrt m * (p.side₁ / 2) ≤ R₀)
    (hR₂ : Real.sqrt m * (p.side₂ / 2) ≤ R₀) (ω : X.Ω)
    (hgood : Contracts.maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first
      p.second ≤ lam)
    {u u₁ v v₁ : Pt m} (hu : u ∈ p.first) (hu₁ : u₁ ∈ p.first) (hv : v ∈ p.second)
    (hv₁ : v₁ ∈ p.second) (hdu : dist u₁ u ≤ δ) (hdv : dist v₁ v ≤ δ) :
    (X.slabTime b p.slab ω u₁ v₁ - dist u₁ v₁) - (X.slabTime b p.slab ω u v - dist u v) ≤
      4 * max (smallMax X b p κn σ L ω) 0 + 3 +
        (4 * (lam + 2 * R₀) / κn * δ + 8 * R₀ / p.dist * δ) := by
  have MD := modulusData_slabTime X hb hBd hBd0 H ω hgood
  have hκ0 := H.hκ0
  have hκp : κn ≤ p.dist := by linarith only [H.hκ, hκ0]
  obtain ⟨γ, hγ⟩ := MD.hopt u hu v hv
  obtain ⟨hγ0, hγ1, hγS, -⟩ := id hγ
  have hcu : slabCoord p.slab u = 0 := (frame_first hu).1
  have hcv : slabCoord p.slab v = p.dist := (frame_second hv).1
  obtain ⟨t₁, t₂, ht₁, ht₁₂, ht₂, hx, hy⟩ := exists_hits γ (f := slabCoord p.slab)
    (lipschitzWith_slabCoord _).continuous (by rw [hγ0, hcu]) (by rw [hγ1, hcv])
    hκ0.le (show κn ≤ p.dist - κn by linarith only [H.hκ]) (by linarith only [hκ0])
  have hxS := hγS t₁ ⟨ht₁, ht₁₂.trans ht₂⟩
  have hyS := hγS t₂ ⟨ht₁.trans ht₁₂, ht₂⟩
  have hgx := MD.hgood u hu v hv γ hγ t₁ ⟨ht₁, ht₁₂.trans ht₂⟩
  have hgy := MD.hgood u hu v hv γ hγ t₂ ⟨ht₁.trans ht₁₂, ht₂⟩
  have hTx := transverse_near_segment H.hn H.hoff H.h1 H.h2 hu hv hgx hx
  have hTy := transverse_near_segment H.hn H.hoff H.h1 H.h2 hu hv hgy hy
  obtain ⟨-, n₂⟩ := MD.hnear u hu _ hxS hx hTx
  obtain ⟨-, f₂⟩ := MD.hfar _ hyS hy hTy v hv
  -- the curves of `Π_{T_{S₁}}(ũ, x₁)` and `Π_{T_{S₂}}(x₂, ṽ)`
  obtain ⟨a, d, ha, hd, hu₁q, hxq⟩ := near_mem H.hσ H.h1 H.hLu H.hLx hu₁ hx hTx
  obtain ⟨d', a', hd', ha', hyq, hv₁q⟩ := far_mem H.hσ H.h2 H.hLv H.hLx hy hTy hv₁
  have hρb : ∀ y, X.ρ ω y ≤ b := hb ω
  have hsub₁ := near_slab_subset p (σ := σ) (nearCenter p κn) a d hκp
  have hsub₂ := far_slab_subset p (σ := σ) (farCenter p κn) d' a' hκp
  have hpw : 0 < p.slab.width := H.hn
  obtain ⟨π₁, hπ₁⟩ := exists_isOneOptimal_restricted (Slab.density_le _ b hρb)
    (convex_slab_set (nearPair p κn σ (nearCenter p κn) a d).slab)
    (Profiles.cubePair_first_subset_set _ hκ0.le hu₁q)
    (Profiles.cubePair_second_subset_set _ hκ0.le hxq)
  obtain ⟨π₂, hπ₂⟩ := exists_isOneOptimal_restricted (Slab.density_le _ b hρb)
    (convex_slab_set (farPair p κn σ (farCenter p κn) d' a').slab)
    (Profiles.cubePair_first_subset_set _ hκ0.le hyq)
    (Profiles.cubePair_second_subset_set _ hκ0.le hv₁q)
  have hdisp : X.slabTime b p.slab ω u₁ v₁ - X.slabTime b p.slab ω u v ≤
      X.slabTime b (nearPair p κn σ (nearCenter p κn) a d).slab ω u₁ (γ.toFun t₁) -
          passageTime (X.ρ ω) u (γ.toFun t₁) +
        (X.slabTime b (farPair p κn σ (farCenter p κn) d' a').slab ω (γ.toFun t₂) v₁ -
          passageTime (X.ρ ω) (γ.toFun t₂) v) + 3 :=
    reroute_le MD.hσm MD.hσB MD.hρσ hsub₁ hsub₂ (density_le_of_subset hpw hκ0 hsub₁ hρb)
      (density_le_of_subset hpw hκ0 hsub₂ hρb) hγ ht₁ ht₁₂ ht₂ hπ₁ hπ₂
  have n₁ := near_slab_le X hb H.hσ.le hκ0.le ha hd hu₁q hxq ω
  have f₁ := far_slab_le X hb H.hσ.le hκ0.le hd' ha' hyq hv₁q ω
  have hφ := phi_terms_le H.hn hκ0 (fun q hq => (norm_sub_center₁_le H.h1 hq).trans hR₁)
    (fun q hq => (norm_sub_center₂_le H.h2 hq).trans hR₂) hu hu₁ hv hv₁ hx hy hgx hgy hdu hdv
  have hcancel := dist_terms_eq_phi_terms (axis p) u u₁ v v₁ (γ.toFun t₁) (γ.toFun t₂)
  linarith only [hdisp, n₁, n₂, f₁, f₂, hφ, hcancel]

/-- **The bound off `E`**: `Z ≤ 4D + 3 + E₀`. -/
theorem modulusSup_le_phi (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {Bd : ℝ}
    (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd) {p : CubePair m} {κn σ lam R₀ δ : ℝ} {L : ℕ}
    (H : CutData p κn σ lam L) (hR₁ : Real.sqrt m * (p.side₁ / 2) ≤ R₀)
    (hR₂ : Real.sqrt m * (p.side₂ / 2) ≤ R₀) (hδ : 0 ≤ δ) (ω : X.Ω)
    (hgood : Contracts.maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first
      p.second ≤ lam) :
    Contracts.modulusSup (X.slabTime b p.slab ω) p.first p.second δ ≤
      4 * max (smallMax X b p κn σ L ω) 0 + 3 +
        (4 * (lam + 2 * R₀) / κn * δ + 8 * R₀ / p.dist * δ) := by
  have hR₀ : 0 ≤ R₀ := (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg H.h1 zero_le_two)).trans hR₁
  have hc : 0 ≤ 4 * max (smallMax X b p κn σ L ω) 0 + 3 +
      (4 * (lam + 2 * R₀) / κn * δ + 8 * R₀ / p.dist * δ) := by
    have := H.hκ0
    have := H.hn
    have := H.hlam
    have := le_max_right (smallMax X b p κn σ L ω) 0
    positivity
  refine Real.iSup_le (fun u => Real.iSup_le (fun u₁ => Real.iSup_le (fun v =>
    Real.iSup_le (fun v₁ => Real.iSup_le (fun hd => ?_) hc) hc) hc) hc) hc
  rw [abs_le]
  constructor
  · have := modulus_one_side_phi (δ := δ) X hb hBd hBd0 H hR₁ hR₂ ω hgood u.2 u₁.2 v.2 v₁.2
      (by rw [dist_comm]; exact hd.1) (by rw [dist_comm]; exact hd.2)
    linarith only [this]
  · have := modulus_one_side_phi X hb hBd hBd0 H hR₁ hR₂ ω hgood u₁.2 u.2 v₁.2 v.2 hd.1 hd.2
    linarith only [this]

end IsotropicVariance.Paper.Proofs.Modulus
