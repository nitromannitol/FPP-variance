/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Paper.Proofs.Profiles.Basic
public import IsotropicVariance.Paper.Proofs.Profiles.OsTools
public import IsotropicVariance.Infra.Measurability.SlabVersion
public import IsotropicVariance.Infra.Measurability.Projection
public import IsotropicVariance.Infra.Measurability.ArcKernel
public import IsotropicVariance.Infra.Measurability.PassageVersion

/-!
# Measurability of the suprema of Sections `sec:localization` and `sec:gain`

The suprema over all 1-optimal curves in equation `eq:localization` and in the radii `R_i(j, k)`
are measurable for the completed probability: their superlevel sets are
projections of Borel sets of curves (`IsotropicVariance.Infra.Measurability`), once the passage
time in the definition of 1-optimality is replaced by a jointly measurable version. The suprema of
the modulus in equation `eq:modulus` are over endpoints only and reduce to countable suprema.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace IsotropicVariance.Paper.Proofs.Localization

open Contracts

variable {m : ℕ}

/-- The distance from `x` to the segment `[u, v]` is continuous in `(u, v, x)`. -/
theorem continuous_infDist_segment :
    Continuous fun p : Pt m × Pt m × Pt m => infDist p.2.2 (segment ℝ p.1 p.2.1) := by
  refine (LipschitzWith.of_le_add_mul 3 fun q p => ?_).continuous
  obtain ⟨u, v, x⟩ := p
  obtain ⟨u', v', x'⟩ := q
  have hu : dist u u' ≤ dist (u, v, x) (u', v', x') := by
    simp only [Prod.dist_eq]
    exact le_max_left _ _
  have hv : dist v v' ≤ dist (u, v, x) (u', v', x') := by
    simp only [Prod.dist_eq]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hx : dist x x' ≤ dist (u, v, x) (u', v', x') := by
    simp only [Prod.dist_eq]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hne : (segment ℝ u v).Nonempty := ⟨u, left_mem_segment ℝ u v⟩
  have key : infDist x' (segment ℝ u' v') - 3 * dist (u, v, x) (u', v', x') ≤
      infDist x (segment ℝ u v) := by
    rw [le_infDist hne]
    rintro y ⟨a, b, ha, hb, hab, rfl⟩
    have hy' : a • u' + b • v' ∈ segment ℝ u' v' := ⟨a, b, ha, hb, hab, rfl⟩
    have h1 := infDist_le_dist_of_mem (x := x') hy'
    have h2 : dist (a • u' + b • v') (a • u + b • v) ≤ dist u u' + dist v v' := by
      refine (dist_add_add_le _ _ _ _).trans ?_
      rw [dist_smul₀, dist_smul₀, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb,
        dist_comm u', dist_comm v']
      have ha1 : a ≤ 1 := by linarith
      have hb1 : b ≤ 1 := by linarith
      nlinarith [dist_nonneg (x := u) (y := u'), dist_nonneg (x := v) (y := v')]
    have h3 := dist_triangle x' x (a • u + b • v)
    have h4 := dist_triangle x' (a • u + b • v) (a • u' + b • v')
    rw [dist_comm x' x] at h3
    rw [dist_comm (a • u + b • v)] at h4
    linarith
  rw [dist_comm]
  push_cast
  linarith

/-- For a real family bounded above, a level `c ≥ 0` is below the supremum iff it is below one
of the values (the real supremum of an empty family is `0`). -/
lemma lt_iSup_iff_of_le {ι : Sort*} {f : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) {B : ℝ}
    (hB : ∀ i, f i ≤ B) : c < ⨆ i, f i ↔ ∃ i, c < f i := by
  constructor
  · intro h
    by_contra h'
    simp only [not_exists, not_lt] at h'
    exact (Real.iSup_le h' hc).not_gt h
  · rintro ⟨i, hi⟩
    exact hi.trans_le (le_ciSup ⟨B, by rintro _ ⟨j, rfl⟩; exact hB j⟩ i)

/-- **The supremum over 1-optimal curves is measurable** for the completion of any s-finite
measure on a standard Borel space of parameters, given a jointly measurable version of the
restricted passage times and a deterministic bound. -/
theorem aemeasurable_iSup_oneOptimal {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (μ : Measure Θ) [SFinite μ] {σ : Θ → Pt m → ℝ} (hσ : Measurable (Function.uncurry σ))
    {S I I' : Set (Pt m)} (hS : IsClosed S) (hI : MeasurableSet I) (hI' : MeasurableSet I')
    {D : Θ → Pt m × Pt m → ℝ} (hD : Measurable (Function.uncurry D))
    (hDae : ∀ᵐ θ ∂μ, ∀ u ∈ S, ∀ v ∈ S, D θ (u, v) = restrictedPassageTime (σ θ) S u v)
    {V : Pt m × Pt m × Pt m → ℝ} (hV : Continuous V) (hV0 : ∀ p, 0 ≤ V p) {R : ℝ}
    (hR : ∀ θ, ∀ u ∈ I, ∀ v ∈ I', ∀ γ : RectifiableCurve (Pt m), IsOneOptimal (σ θ) S u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, V (u, v, γ.toFun t) ≤ R) :
    AEMeasurable (fun θ => ⨆ (u : I) (v : I')
      (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal (σ θ) S u v γ}) (t : Icc (0 : ℝ) 1),
        V ((u : Pt m), (v : Pt m), γ.1.toFun t)) μ := by
  set Ψ : Θ → ℝ := fun θ => ⨆ (u : I) (v : I')
      (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal (σ θ) S u v γ}) (t : Icc (0 : ℝ) 1),
        V ((u : Pt m), (v : Pt m), γ.1.toFun t) with hΨ
  have hM0 : 0 ≤ max R 0 := le_max_right _ _
  have hbd : ∀ θ (u : I) (v : I')
      (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal (σ θ) S u v γ}) (t : Icc (0 : ℝ) 1),
      V ((u : Pt m), (v : Pt m), γ.1.toFun t) ≤ max R 0 :=
    fun θ u v γ t => (hR θ u u.2 v v.2 γ.1 γ.2 t t.2).trans (le_max_left _ _)
  have hΨ0 : ∀ θ, 0 ≤ Ψ θ := fun θ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => hV0 _
  -- the superlevel sets, as existence statements
  have hlt : ∀ θ, ∀ c, 0 ≤ c → (c < Ψ θ ↔ ∃ (u : I) (v : I')
      (γ : {γ : RectifiableCurve (Pt m) // IsOneOptimal (σ θ) S u v γ}) (t : Icc (0 : ℝ) 1),
        c < V ((u : Pt m), (v : Pt m), γ.1.toFun t)) := by
    intro θ c hc
    rw [hΨ, lt_iSup_iff_of_le hc (B := max R 0)
      (fun u => Real.iSup_le (fun v => Real.iSup_le (fun γ => Real.iSup_le
        (fun t => hbd θ u v γ t) hM0) hM0) hM0)]
    refine exists_congr fun u => ?_
    rw [lt_iSup_iff_of_le hc (B := max R 0)
      (fun v => Real.iSup_le (fun γ => Real.iSup_le (fun t => hbd θ u v γ t) hM0) hM0)]
    refine exists_congr fun v => ?_
    rw [lt_iSup_iff_of_le hc (B := max R 0)
      (fun γ => Real.iSup_le (fun t => hbd θ u v γ t) hM0)]
    refine exists_congr fun γ => ?_
    rw [lt_iSup_iff_of_le hc (B := max R 0) (fun t => hbd θ u v γ t)]
  -- the Borel set of endpoints, curves and parameters whose projection is a superlevel set
  have hlevel : ∀ c : ℝ, NullMeasurableSet {θ | c < Ψ θ} μ := by
    intro c
    rcases lt_or_ge c 0 with hc | hc
    · have huniv : {θ | c < Ψ θ} = univ := eq_univ_of_forall fun θ => hc.trans_le (hΨ0 θ)
      rw [huniv]
      exact MeasurableSet.univ.nullMeasurableSet
    let K := Pt m × Pt m × Infra.Measurability.BVCurves (Pt m)
    let B : Set (K × Θ) := {q | q.1.1 ∈ I ∧ q.1.2.1 ∈ I' ∧ q.1.1 ∈ S ∧ q.1.2.1 ∈ S ∧
      q.1.2.2.curve.toFun 0 = q.1.1 ∧ q.1.2.2.curve.toFun 1 = q.1.2.1 ∧
      (∀ t : unitInterval, q.1.2.2.1 t ∈ S) ∧
      q.1.2.2.curve.cost (fun x => ENNReal.ofReal (σ q.2 x)) ≤
        ENNReal.ofReal (D q.2 (q.1.1, q.1.2.1) + 1) ∧
      ∃ t : unitInterval, c < V (q.1.1, q.1.2.1, q.1.2.2.1 t)}
    have hev : ∀ t : unitInterval,
        Continuous fun γ : Infra.Measurability.BVCurves (Pt m) => γ.1 t :=
      fun t => (continuous_eval_const t).comp continuous_subtype_val
    have hγ : Measurable fun q : K × Θ => q.1.2.2 := measurable_fst.snd.snd
    have hu : Measurable fun q : K × Θ => q.1.1 := measurable_fst.fst
    have hv : Measurable fun q : K × Θ => q.1.2.1 := measurable_fst.snd.fst
    have hθ : Measurable fun q : K × Θ => q.2 := measurable_snd
    have hend : ∀ s : ℝ, Measurable fun q : K × Θ => q.1.2.2.curve.toFun s :=
      fun s => (hev _).measurable.comp hγ
    have hSγ : MeasurableSet {γ : Infra.Measurability.BVCurves (Pt m) | ∀ t : unitInterval,
        γ.1 t ∈ S} := by
      rw [ofPred_forall]
      exact (isClosed_iInter fun t => hS.preimage (hev t)).measurableSet
    have hopen : IsOpen {p : K | ∃ t : unitInterval, c < V (p.1, p.2.1, p.2.2.1 t)} := by
      rw [ofPred_exists]
      exact isOpen_iUnion fun t => isOpen_lt continuous_const
        (hV.comp (continuous_fst.prodMk (continuous_snd.fst.prodMk
          ((hev t).comp continuous_snd.snd))))
    have hcost : Measurable fun q : K × Θ =>
        q.1.2.2.curve.cost (fun x => ENNReal.ofReal (σ q.2 x)) := by
      have h := Infra.Measurability.BVCurves.measurable_cost (E := Pt m) (Ω := Θ)
        (ρ := fun p : Θ × Pt m => ENNReal.ofReal (σ p.1 p.2)) hσ.ennreal_ofReal
      have h' := h.comp (hγ.prodMk measurable_snd)
      exact h'
    have hrhs : Measurable fun q : K × Θ => ENNReal.ofReal (D q.2 (q.1.1, q.1.2.1) + 1) := by
      have h := hD.comp (hθ.prodMk (hu.prodMk hv))
      have h' := (h.add_const 1).ennreal_ofReal
      exact h'
    have hB : MeasurableSet B :=
      (hu hI).inter <| (hv hI').inter <| (hu hS.measurableSet).inter <|
        (hv hS.measurableSet).inter <| (measurableSet_eq_fun (hend 0) hu).inter <|
        (measurableSet_eq_fun (hend 1) hv).inter <|
        (hγ hSγ).inter <| (measurableSet_le hcost hrhs).inter <|
        measurable_fst hopen.measurableSet
    refine (Infra.Measurability.nullMeasurableSet_projection μ hB).congr ?_
    filter_upwards [hDae] with θ hθ
    apply propext
    rw [hlt θ c hc]
    constructor
    · rintro ⟨⟨⟨u, v, γ⟩, θ'⟩, ⟨huI, hvI', huS, hvS, h0, h1, hγS, hcost, t, ht⟩, rfl⟩
      refine ⟨⟨u, huI⟩, ⟨v, hvI'⟩, ⟨γ.curve, h0, h1, fun s _ => hγS _, ?_⟩, ⟨t, t.2⟩, ?_⟩
      · rw [← hθ u huS v hvS]
        exact hcost
      · simpa [Infra.Measurability.BVCurves.curve, projIcc_val] using ht
    · rintro ⟨⟨u, huI⟩, ⟨v, hvI'⟩, ⟨γ, h0, h1, hγS, hcost⟩, ⟨t, ht⟩, hlt'⟩
      change γ.toFun 0 = u at h0
      change γ.toFun 1 = v at h1
      have huS : u ∈ S := by
        rw [← h0]
        exact hγS 0 (left_mem_Icc.2 zero_le_one)
      have hvS : v ∈ S := by
        rw [← h1]
        exact hγS 1 (right_mem_Icc.2 zero_le_one)
      set δ := Infra.Measurability.BVCurves.ofRectifiable γ
      have hδ : EqOn δ.curve.toFun γ.toFun (Icc 0 1) :=
        fun s hs => Infra.Measurability.BVCurves.ofRectifiable_eq γ hs
      have hδ' : ∀ s : unitInterval, δ.1 s = γ.toFun s := fun s => by
        rw [← hδ s.2]
        simp [Infra.Measurability.BVCurves.curve, projIcc_val]
      refine ⟨((u, v, δ), θ), ⟨huI, hvI', huS, hvS, (hδ (left_mem_Icc.2 zero_le_one)).trans h0,
        (hδ (right_mem_Icc.2 zero_le_one)).trans h1, fun s => (hδ' s) ▸ hγS s s.2, ?_,
        ⟨t, ht⟩, ?_⟩, rfl⟩
      · rw [hθ u huS v hvS, RectifiableCurve.cost_congr_curve hδ]
        exact hcost
      · rw [hδ']
        exact hlt'
  have hnm : NullMeasurable Ψ μ := by
    have h : @Measurable (NullMeasurableSpace Θ μ) ℝ inferInstance inferInstance Ψ :=
      measurable_of_Ioi hlevel
    exact fun _ hs => h hs
  exact hnm.aemeasurable

/-! ## Bounds for the points of 1-optimal curves -/

/-- A point of a 1-optimal curve is within `(D(u, v) + 1)/a` of the start, for a density at
least `a > 0`: the cost is at least `a` times the length. -/
lemma dist_le_of_isOneOptimal {σ : Pt m → ℝ} {S : Set (Pt m)} {u v : Pt m}
    {γ : RectifiableCurve (Pt m)} (hγ : IsOneOptimal σ S u v γ) {a : ℝ} (ha : 0 < a)
    (hσ : ∀ x, a ≤ σ x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (γ.toFun t) u ≤ (restrictedPassageTime σ S u v + 1) / a := by
  obtain ⟨h0, -, -, hcost⟩ := hγ
  have hT := restrictedPassageTime_nonneg σ S u v
  have hd : edist (γ.toFun t) u ≤ γ.length := by
    rw [← h0]
    exact eVariationOn.edist_le γ.toFun ht (left_mem_Icc.2 zero_le_one)
  have h1 : ENNReal.ofReal (a * dist (γ.toFun t) u) ≤
      ENNReal.ofReal (restrictedPassageTime σ S u v + 1) := by
    rw [ENNReal.ofReal_mul ha.le, ← edist_dist]
    calc ENNReal.ofReal a * edist (γ.toFun t) u ≤ ENNReal.ofReal a * γ.length := by gcongr
      _ ≤ _ := (γ.mul_length_le_cost fun x => ENNReal.ofReal_le_ofReal (hσ x)).trans hcost
  rw [le_div_iff₀ ha, mul_comm]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1

/-- The points of the 1-optimal curves between two bounded sets stay within a fixed distance of
the start, for densities at least `a > 0` whose restricted passage times are at most `B` times
the distance. -/
lemma exists_dist_le_of_isOneOptimal {Θ : Type*} {σ : Θ → Pt m → ℝ} {S I I' : Set (Pt m)}
    (hI : Bornology.IsBounded I) (hI' : Bornology.IsBounded I') {a B : ℝ} (ha : 0 < a)
    (hσ : ∀ θ x, a ≤ σ θ x)
    (hT : ∀ θ, ∀ u ∈ S, ∀ v ∈ S, restrictedPassageTime (σ θ) S u v ≤ B * dist u v) :
    ∃ R, ∀ θ, ∀ u ∈ I, ∀ v ∈ I', ∀ γ : RectifiableCurve (Pt m), IsOneOptimal (σ θ) S u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, dist (γ.toFun t) u ≤ R := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hI.union hI')
  refine ⟨(|B| * C + 1) / a, fun θ u hu v hv γ hγ t ht => ?_⟩
  have huS : u ∈ S := by
    rw [← hγ.1]
    exact hγ.2.2.1 0 (left_mem_Icc.2 zero_le_one)
  have hvS : v ∈ S := by
    rw [← hγ.2.1]
    exact hγ.2.2.1 1 (right_mem_Icc.2 zero_le_one)
  have hd := hC (mem_union_left _ hu) (mem_union_right _ hv)
  have hT' : restrictedPassageTime (σ θ) S u v ≤ |B| * C :=
    (hT θ u huS v hvS).trans ((mul_le_mul_of_nonneg_right (le_abs_self B) dist_nonneg).trans
      (mul_le_mul_of_nonneg_left hd (abs_nonneg B)))
  exact (dist_le_of_isOneOptimal hγ ha (hσ θ) ht).trans
    (div_le_div_of_nonneg_right (by linarith) ha.le)

/-! ## The instances -/

/-- The slab density of a setting is jointly measurable. -/
lemma measurable_slabDensity (X : Setting m) (b : ℝ) (sl : Slab m) :
    Measurable (Function.uncurry fun ω => sl.density b (X.ρ ω)) := by
  change Measurable fun p : X.Ω × Pt m => if infDist p.2 sl.faces ≤ 1 then b else X.ρ p.1 p.2
  exact Measurable.ite (measurableSet_le ((continuous_infDist_pt _).measurable.comp
    measurable_snd) measurable_const) measurable_const X.measurable_ρ

/-- A lower bound of the density is a lower bound of the slab density. -/
lemma le_slabDensity (X : Setting m) {a b : ℝ} (hb : X.IsUpperBound b)
    (ha : ∀ ω x, a ≤ X.ρ ω x) (sl : Slab m) (ω : X.Ω) (x : Pt m) :
    a ≤ sl.density b (X.ρ ω) x := by
  unfold Slab.density
  split_ifs
  · exact (ha ω x).trans (hb ω x)
  · exact ha ω x

/-- The quantity of equation `eq:localization` for the slab passage time is a random variable. -/
theorem aemeasurable_maxSegmentDeviation_slab (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) {I I' : Set (Pt m)} (hI : IsCompact I) (hI' : IsCompact I') :
    AEMeasurable (fun ω => maxSegmentDeviation (sl.density b (X.ρ ω)) sl.set I I') X.P := by
  obtain ⟨a, b', ha, hab⟩ := X.bounds
  obtain ⟨T, hTm, -, -, hTae⟩ := Infra.Slab.exists_slabTime_version X hb sl
  obtain ⟨R, hR⟩ := exists_dist_le_of_isOneOptimal (σ := fun ω => sl.density b (X.ρ ω))
    (S := sl.set) hI.isBounded hI'.isBounded ha
    (le_slabDensity X hb (fun ω x => (hab ω x).1) sl) (B := b)
    (fun ω u hu v hv => Infra.Slab.slabTime_le_mul_dist X hb sl ω hu hv)
  exact aemeasurable_iSup_oneOptimal X.P (measurable_slabDensity X b sl)
    (Infra.Slab.isClosed_slab_set sl) hI.measurableSet hI'.measurableSet hTm hTae
    (V := fun x => infDist x.2.2 (segment ℝ x.1 x.2.1)) continuous_infDist_segment
    (fun _ => infDist_nonneg)
    (fun ω u hu v hv γ hγ t ht => (infDist_le_dist_of_mem (left_mem_segment ℝ u v)).trans
      (hR ω u hu v hv γ hγ t ht))

/-- The deviation in the radii `R_i(j, k)` is a random variable. -/
theorem aemeasurable_maxDeviation_slab (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) {I I' : Set (Pt m)} (hI : IsCompact I) (hI' : IsCompact I') (p q : Pt m) :
    AEMeasurable (fun ω => maxDeviation (sl.density b (X.ρ ω)) sl.set I I' p q) X.P := by
  obtain ⟨a, b', ha, hab⟩ := X.bounds
  obtain ⟨T, hTm, -, -, hTae⟩ := Infra.Slab.exists_slabTime_version X hb sl
  obtain ⟨R, hR⟩ := exists_dist_le_of_isOneOptimal (σ := fun ω => sl.density b (X.ρ ω))
    (S := sl.set) hI.isBounded hI'.isBounded ha
    (le_slabDensity X hb (fun ω x => (hab ω x).1) sl) (B := b)
    (fun ω u hu v hv => Infra.Slab.slabTime_le_mul_dist X hb sl ω hu hv)
  obtain ⟨r₀, hr₀⟩ := hI.isBounded.subset_closedBall p
  exact aemeasurable_iSup_oneOptimal X.P (measurable_slabDensity X b sl)
    (Infra.Slab.isClosed_slab_set sl) hI.measurableSet hI'.measurableSet hTm hTae
    (V := fun x => infDist x.2.2 (segment ℝ p q)) (R := R + r₀)
    ((continuous_infDist_pt _).comp (continuous_snd.comp continuous_snd))
    (fun _ => infDist_nonneg)
    (fun ω u hu v hv γ hγ t ht => (infDist_le_dist_of_mem (left_mem_segment ℝ p q)).trans <|
      (dist_triangle _ u p).trans (add_le_add (hR ω u hu v hv γ hγ t ht)
        (mem_closedBall.1 (hr₀ hu))))

/-! ## The modulus -/

/-- A real function with `|f x − f y| ≤ K |x − y|` is continuous. -/
lemma continuous_of_abs_sub_le {α : Type*} [PseudoMetricSpace α] {f : α → ℝ} {K : ℝ}
    (h : ∀ x y, |f x - f y| ≤ K * dist x y) : Continuous f := by
  refine (LipschitzWith.of_le_add_mul K.toNNReal fun x y => ?_).continuous
  have h1 := (abs_le.1 (h x y)).2
  have h2 : K * dist x y ≤ (K.toNNReal : ℝ) * dist x y :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) dist_nonneg
  linarith

/-- The modulus in equation `eq:modulus` of a random function of the endpoints that is Lipschitz
on `I × I'` and measurable at each pair of endpoints is a random variable: it is the supremum of
a continuous bounded random field over the separable space of admissible quadruples. -/
lemma aemeasurable_modulusSup {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → Pt m → Pt m → ℝ} {I I' : Set (Pt m)} (r : ℝ) {B : ℝ}
    (hlip : ∀ ω, ∀ u ∈ I, ∀ u₁ ∈ I, ∀ v ∈ I', ∀ v₁ ∈ I',
      |D ω u v - D ω u₁ v₁| ≤ B * (dist u u₁ + dist v v₁))
    (hm : ∀ u ∈ I, ∀ v ∈ I', AEMeasurable (fun ω => D ω u v) P) :
    AEMeasurable (fun ω => modulusSup (D ω) I I' r) P := by
  set M := 2 * (|B| + 1) * max r 0 with hM
  have hM0 : 0 ≤ M := by positivity
  have hbound : ∀ ω, ∀ u ∈ I, ∀ u₁ ∈ I, ∀ v ∈ I', ∀ v₁ ∈ I',
      dist u u₁ ≤ r ∧ dist v v₁ ≤ r → |D ω u v - D ω u₁ v₁ - dist u v + dist u₁ v₁| ≤ M := by
    intro ω u hu u₁ hu₁ v hv v₁ hv₁ hr
    have h1 := abs_le.1 ((hlip ω u hu u₁ hu₁ v hv v₁ hv₁).trans
      (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)))
    have h2 := abs_le.1 (show |dist u v - dist u₁ v₁| ≤ dist u u₁ + dist v v₁ by
      simpa only [Real.dist_eq] using dist_dist_dist_le u v u₁ v₁)
    have hs : dist u u₁ + dist v v₁ ≤ 2 * max r 0 := by
      linarith [hr.1, hr.2, le_max_left r 0]
    have h3 : (|B| + 1) * (dist u u₁ + dist v v₁) ≤ (|B| + 1) * (2 * max r 0) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3]
  let C := {q : Pt m × Pt m × Pt m × Pt m //
    (q.1 ∈ I ∧ q.2.1 ∈ I ∧ q.2.2.1 ∈ I' ∧ q.2.2.2 ∈ I') ∧
      dist q.1 q.2.1 ≤ r ∧ dist q.2.2.1 q.2.2.2 ≤ r}
  let F : Ω → C → ℝ := fun ω q =>
    |D ω q.1.1 q.1.2.2.1 - D ω q.1.2.1 q.1.2.2.2 - dist q.1.1 q.1.2.2.1 + dist q.1.2.1 q.1.2.2.2|
  have hF : ∀ ω q, F ω q ≤ M := fun ω q =>
    hbound ω _ q.2.1.1 _ q.2.1.2.1 _ q.2.1.2.2.1 _ q.2.1.2.2.2 q.2.2
  have hbdd : ∀ ω, BddAbove (range (F ω)) := fun ω => ⟨M, by rintro _ ⟨q, rfl⟩; exact hF ω q⟩
  have heq : ∀ ω, modulusSup (D ω) I I' r = ⨆ q : C, F ω q := by
    intro ω
    have hR0 : 0 ≤ ⨆ q : C, F ω q := Real.iSup_nonneg fun _ => abs_nonneg _
    have hle : ∀ (u u₁ : I) (v v₁ : I'), dist (u : Pt m) u₁ ≤ r ∧ dist (v : Pt m) v₁ ≤ r →
        |D ω u v - D ω u₁ v₁ - dist (u : Pt m) v + dist (u₁ : Pt m) v₁| ≤ M :=
      fun u u₁ v v₁ h => hbound ω u u.2 u₁ u₁.2 v v.2 v₁ v₁.2 h
    apply le_antisymm
    · exact Real.iSup_le (fun u => Real.iSup_le (fun u₁ => Real.iSup_le (fun v => Real.iSup_le
        (fun v₁ => Real.iSup_le (fun h => le_ciSup (hbdd ω)
          ⟨((u : Pt m), (u₁ : Pt m), (v : Pt m), (v₁ : Pt m)), ⟨u.2, u₁.2, v.2, v₁.2⟩, h⟩) hR0)
          hR0) hR0) hR0) hR0
    · have hL0 : 0 ≤ modulusSup (D ω) I I' r := Real.iSup_nonneg fun _ => Real.iSup_nonneg
        fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg
          fun _ => abs_nonneg _
      refine Real.iSup_le (fun q => ?_) hL0
      obtain ⟨⟨u, u₁, v, v₁⟩, ⟨hu, hu₁, hv, hv₁⟩, h⟩ := q
      unfold modulusSup
      refine le_ciSup_of_le ⟨M, ?_⟩ ⟨u, hu⟩ (le_ciSup_of_le ⟨M, ?_⟩ ⟨u₁, hu₁⟩
        (le_ciSup_of_le ⟨M, ?_⟩ ⟨v, hv⟩ (le_ciSup_of_le ⟨M, ?_⟩ ⟨v₁, hv₁⟩
          (le_ciSup_of_le ⟨M, ?_⟩ h le_rfl))))
      · rintro _ ⟨a, rfl⟩
        exact Real.iSup_le (fun b => Real.iSup_le (fun c => Real.iSup_le (fun d =>
          Real.iSup_le (fun e => hle a b c d e) hM0) hM0) hM0) hM0
      · rintro _ ⟨b, rfl⟩
        exact Real.iSup_le (fun c => Real.iSup_le (fun d =>
          Real.iSup_le (fun e => hle _ b c d e) hM0) hM0) hM0
      · rintro _ ⟨c, rfl⟩
        exact Real.iSup_le (fun d => Real.iSup_le (fun e => hle _ _ c d e) hM0) hM0
      · rintro _ ⟨d, rfl⟩
        exact Real.iSup_le (fun e => hle _ _ _ d e) hM0
      · rintro _ ⟨e, rfl⟩
        exact hle _ _ _ _ e
  have hd : ∀ q q' : C, dist q.1.1 q'.1.1 ≤ dist q q' ∧ dist q.1.2.1 q'.1.2.1 ≤ dist q q' ∧
      dist q.1.2.2.1 q'.1.2.2.1 ≤ dist q q' ∧ dist q.1.2.2.2 q'.1.2.2.2 ≤ dist q q' := by
    intro q q'
    rw [Subtype.dist_eq]
    simp only [Prod.dist_eq]
    refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hcont : ∀ ω, Continuous (F ω) := by
    intro ω
    have hB : ∀ {a c d : ℝ}, 0 ≤ a → 0 ≤ c → a ≤ d → c ≤ d → B * (a + c) ≤ 2 * |B| * d := by
      intro a c d ha hc had hcd
      have := mul_le_mul_of_nonneg_right (le_abs_self B) (add_nonneg ha hc)
      nlinarith [abs_nonneg B]
    have h1 : Continuous fun q : C => D ω q.1.1 q.1.2.2.1 :=
      continuous_of_abs_sub_le (K := 2 * |B|) fun q q' => by
        obtain ⟨h1, -, h3, -⟩ := hd q q'
        exact (hlip ω _ q.2.1.1 _ q'.2.1.1 _ q.2.1.2.2.1 _ q'.2.1.2.2.1).trans
          (hB dist_nonneg dist_nonneg h1 h3)
    have h2 : Continuous fun q : C => D ω q.1.2.1 q.1.2.2.2 :=
      continuous_of_abs_sub_le (K := 2 * |B|) fun q q' => by
        obtain ⟨-, h2, -, h4⟩ := hd q q'
        exact (hlip ω _ q.2.1.2.1 _ q'.2.1.2.1 _ q.2.1.2.2.2 _ q'.2.1.2.2.2).trans
          (hB dist_nonneg dist_nonneg h2 h4)
    have h3 : Continuous fun q : C => dist q.1.1 q.1.2.2.1 := by fun_prop
    have h4 : Continuous fun q : C => dist q.1.2.1 q.1.2.2.2 := by fun_prop
    exact continuous_abs.comp (((h1.sub h2).sub h3).add h4)
  have hmF : ∀ q : C, AEMeasurable (fun ω => F ω q) P := fun q =>
    continuous_abs.measurable.comp_aemeasurable
      ((((hm _ q.2.1.1 _ q.2.1.2.2.1).sub (hm _ q.2.1.2.1 _ q.2.1.2.2.2)).sub
        aemeasurable_const).add aemeasurable_const)
  have hfun : (fun ω => modulusSup (D ω) I I' r) = fun ω => ⨆ q : C, F ω q := funext heq
  rw [hfun]
  exact Profiles.aemeasurable_iSup_of_continuous hcont hbdd hmF

/-- The modulus of equation `eq:modulus` for the slab passage time is a random variable. -/
theorem aemeasurable_modulusSup_slabTime (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) {I I' : Set (Pt m)} (_hI : IsCompact I) (_hI' : IsCompact I')
    (hIS : I ⊆ sl.set) (hI'S : I' ⊆ sl.set) (r : ℝ) :
    AEMeasurable (fun ω => modulusSup (X.slabTime b sl ω) I I' r) X.P :=
  aemeasurable_modulusSup r (fun ω _ hu _ hu₁ _ hv _ hv₁ =>
    Infra.Slab.abs_slabTime_sub_le X hb sl ω (hIS hu) (hI'S hv) (hIS hu₁) (hI'S hv₁))
    (fun u _ v _ => Infra.Slab.aemeasurable_slabTime X hb sl u v)

end IsotropicVariance.Paper.Proofs.Localization
