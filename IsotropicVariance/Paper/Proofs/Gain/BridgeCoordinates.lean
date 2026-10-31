/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.BridgeKernel
public import Mathlib.Probability.ProductMeasure
import IsotropicVariance.Paper.Proofs.Gain.BridgeInfo
import IsotropicVariance.Paper.Proofs.Gain.BridgeGeometry
import IsotropicVariance.Infra.Noise.EfronStein

/-!
# Section `sec:gain`: block coordinates of the noise

For countably many Borel regions `S c` with null frontiers meeting in null sets, the
coordinate `c` of the noise is the noise itself carrying the information of `S c`
(`RegionCoord`), and `regionMap N S` sends the noise to its coordinates.

* `map_regionMap`: the coordinates are independent, with the product law `infinitePi`.
* `comap_regionMap`: the information of the coordinates is `⨆ c, info (S c)`.
* `map_pairLaw_regionMap`, `lintegral_pairLaw_regionMap`: under the resampling of the region `c`
  given its label (`pairLaw`), the pair of coordinate vectors has the law of `(x, x[c ↦ y])`, `x`
  drawn from the product and `y` from the law of the coordinate `c` given its label. The proof is
  on boxes: the other coordinates are almost surely information off `S c` (the noise in the null
  set `S c ∩ S d` carries none, `info_le_aeClosure_diff`), so `pairLaw_prod` applies.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace IsotropicVariance.Paper.Proofs.Gain.Bridge

open IsotropicVariance.Paper

universe u

/-- A finite intersection of measurable sets, written with a bounded quantifier, is
measurable. -/
theorem measurableSet_setOf_forall_finset {Ω ι : Type*} {M : MeasurableSpace Ω} (t : Finset ι)
    (T : ι → Set Ω) (hT : ∀ d ∈ t, MeasurableSet[M] (T d)) :
    MeasurableSet[M] {ω | ∀ d ∈ t, ω ∈ T d} := by
  have : {ω | ∀ d ∈ t, ω ∈ T d} = ⋂ d ∈ (t : Set ι), T d := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.biInter (Finset.countable_toSet t) hT

section Region

variable {m : ℕ} (N : NoiseModel.{u} m)

/-- The noise, observed through its information in `A`: a coordinate of the noise. -/
def RegionCoord (N : NoiseModel.{u} m) (_A : Set (Pt m)) : Type u := N.Ω

/-- The coordinate of a region carries the information of the noise in it. -/
instance (A : Set (Pt m)) : MeasurableSpace (RegionCoord N A) := N.info A

/-- The noise as a point of the coordinate of `A`. -/
def toRegion (A : Set (Pt m)) : N.Ω → RegionCoord N A := id

/-- A label of the noise, read on the coordinate of `A`. -/
def regionLabel (A : Set (Pt m)) {V : Type} (ℓ : N.Ω → V) : RegionCoord N A → V := ℓ

/-- The coordinate map is measurable. -/
theorem measurable_toRegion (A : Set (Pt m)) : Measurable (toRegion N A) :=
  fun s hs => N.info_le A s hs

variable {I : Type} (S : I → Set (Pt m))

/-- The coordinates of the noise in the regions `S c`. -/
def regionMap : N.Ω → ∀ c, RegionCoord N (S c) := fun ω c => toRegion N (S c) ω

/-- The law of the coordinate `c`. -/
noncomputable def regionLaw (c : I) : Measure (RegionCoord N (S c)) :=
  N.P.map (toRegion N (S c))

/-- The law of a coordinate is a probability. -/
instance (c : I) : IsProbabilityMeasure (regionLaw N S c) := by
  unfold regionLaw
  infer_instance

/-- The coordinates are measurable. -/
theorem measurable_regionMap : Measurable (regionMap N S) :=
  measurable_pi_iff.2 fun c => measurable_toRegion N (S c)

/-- The law of the coordinate `c` of an event of the noise in `S c`. -/
theorem regionLaw_apply (c : I) {B : Set (RegionCoord N (S c))} (hB : MeasurableSet B) :
    regionLaw N S c B = N.P B :=
  Measure.map_apply (measurable_toRegion N _) hB

/-- Conditional laws of the coordinate `c` are conditional laws of the noise. -/
theorem regionLaw_cond (c : I) {T B : Set (RegionCoord N (S c))} (hT : MeasurableSet T)
    (hB : MeasurableSet B) : (regionLaw N S c)[B | T] = N.P[B | T] := by
  have h₁ : (regionLaw N S c)[B | T] = (regionLaw N S c T)⁻¹ * regionLaw N S c (T ∩ B) :=
    cond_apply hT _ _
  have h₂ : N.P[B | T] = (N.P T)⁻¹ * N.P (T ∩ B) := cond_apply (N.info_le _ _ hT) _ _
  rw [h₁, h₂, regionLaw_apply N S c hT, regionLaw_apply N S c (hT.inter hB)]
  rfl

/-- The information of the coordinates is the information of the regions. -/
theorem comap_regionMap :
    MeasurableSpace.comap (regionMap N S) MeasurableSpace.pi = ⨆ c, N.info (S c) := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  congr 1
  funext c
  rw [MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_id

variable {S}

/-- **Independent coordinates.** For Borel regions with null frontiers and pairwise disjoint
interiors, the coordinates of the noise are independent: their joint law is the product of their
laws. -/
theorem map_regionMap [Countable I] (hS : ∀ c, MeasurableSet (S c))
    (hfr : ∀ c, volume (frontier (S c)) = 0)
    (hd : Pairwise (Function.onFun Disjoint fun c => interior (S c))) :
    N.P.map (regionMap N S) = Measure.infinitePi (regionLaw N S) :=
  Infra.Noise.map_regionCoordinates_eq_infinitePi N S (hS := hS) (hb := hfr) (hd := hd)
    (R := fun c => toRegion N (S c)) (hR := fun _ _ hs => hs)

variable (S) {V : Type} [Fintype V]

/-- The conditional law of the coordinate `c` given its label `ℓ`, at a point of the product. -/
noncomputable def labelCondKernel (c : I) (ℓ : N.Ω → V)
    (hℓ : ∀ v, MeasurableSet[N.info (S c)] (ℓ ⁻¹' {v})) :
    Kernel (∀ d, RegionCoord N (S d)) (RegionCoord N (S c)) where
  toFun x := (regionLaw N S c)[|regionLabel N (S c) ℓ ⁻¹' {regionLabel N (S c) ℓ (x c)}]
  measurable' :=
    (measurable_from_top (f := fun v : V =>
      (regionLaw N S c)[|regionLabel N (S c) ℓ ⁻¹' {v}])).comp
      ((measurable_top_of_fibers (f := regionLabel N (S c) ℓ) hℓ).comp (measurable_pi_apply c))

/-- The conditional laws of a coordinate given its label have mass at most one. -/
instance (c : I) (ℓ : N.Ω → V) (hℓ : ∀ v, MeasurableSet[N.info (S c)] (ℓ ⁻¹' {v})) :
    IsFiniteKernel (labelCondKernel N S c ℓ hℓ) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x => by
    change (regionLaw N S c)[|regionLabel N (S c) ℓ ⁻¹' {regionLabel N (S c) ℓ (x c)}] univ ≤ 1
    exact prob_le_one⟩⟩

variable {S} [Countable I] [DecidableEq I]

/-- **Resampling a coordinate, on boxes.** The law of the pair of coordinate vectors under the
resampling of the region `c` given its label, and the law of `(x, x[c ↦ y])`, agree on products
of boxes. -/
theorem pairLaw_regionMap_box (hS : ∀ c, MeasurableSet (S c))
    (hfr : ∀ c, volume (frontier (S c)) = 0)
    (hnull : Pairwise fun c d => volume (S c ∩ S d) = 0) (c : I) (ℓ : N.Ω → V)
    (hℓ : ∀ v, MeasurableSet[N.info (S c)] (ℓ ⁻¹' {v})) (s s' : Finset I)
    (A B : ∀ d, Set (RegionCoord N (S d))) (hA : ∀ d, MeasurableSet (A d))
    (hB : ∀ d, MeasurableSet (B d)) :
    (pairLaw N (S c) ℓ).map (fun p => (regionMap N S p.1, regionMap N S p.2))
        ((s : Set I).pi A ×ˢ (s' : Set I).pi B) =
      ((Measure.infinitePi (regionLaw N S) ⊗ₘ labelCondKernel N S c ℓ hℓ).map
        fun q => (q.1, Function.update q.1 c q.2)) ((s : Set I).pi A ×ˢ (s' : Set I).pi B) := by
  have hd : Pairwise (Function.onFun Disjoint fun c => interior (S c)) :=
    fun a b hab => disjoint_interior_of_null_inter (hnull hab)
  have hmap := map_regionMap N hS hfr hd
  have hind := indep_info_compl N (hS c) (hfr c)
  have hΦ := measurable_regionMap N S
  have hΨ : Measurable fun p : N.Ω × N.Ω => (regionMap N S p.1, regionMap N S p.2) :=
    (hΦ.comp measurable_fst).prodMk (hΦ.comp measurable_snd)
  have hU : Measurable fun q : (∀ d, RegionCoord N (S d)) × RegionCoord N (S c) =>
      (q.1, Function.update q.1 c q.2) :=
    measurable_fst.prodMk measurable_update'
  -- the coordinates other than `c` are almost surely events off `S c`
  have hface : ∀ d, d ≠ c → N.info (S d) ≤ aeClosure (N.info (S c)ᶜ) N.P := fun d hdc =>
    (info_le_aeClosure_diff N (hS d) (hfr d) (hS c) (hfr c) (hnull hdc)).trans
      (aeClosure_mono (N.info_mono fun _ hx => hx.2))
  have hbox : ∀ (t : Finset I) (T : ∀ d, Set (RegionCoord N (S d))),
      (∀ d, MeasurableSet (T d)) → MeasurableSet ((t : Set I).pi T) :=
    fun t T hT => MeasurableSet.pi (Finset.countable_toSet t) fun d _ => hT d
  -- splitting a box into its coordinate `c` and the others
  have hsplit : ∀ (t : Finset I) (T : ∀ d, Set (RegionCoord N (S d))),
      regionMap N S ⁻¹' (t : Set I).pi T =
        {ω : N.Ω | c ∈ t → ω ∈ T c} ∩ {ω : N.Ω | ∀ d ∈ t.erase c, ω ∈ T d} := by
    intro t T
    ext ω
    simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_inter_iff, mem_ofPred_eq,
      Finset.mem_erase]
    constructor
    · intro h
      exact ⟨fun hc => h c hc, fun d hd => h d hd.2⟩
    · rintro ⟨h1, h2⟩ d hd
      by_cases hdc : d = c
      · subst hdc
        exact h1 hd
      · exact h2 d ⟨hdc, hd⟩
  have hfirst : ∀ (t : Finset I) (T : ∀ d, Set (RegionCoord N (S d))),
      (∀ d, MeasurableSet (T d)) → MeasurableSet[N.info (S c)] {ω : N.Ω | c ∈ t → ω ∈ T c} := by
    intro t T hT
    by_cases hc : c ∈ t
    · have : {ω : N.Ω | c ∈ t → ω ∈ T c} = T c := by
        ext ω
        simp only [mem_ofPred_eq, hc, true_implies]
        exact Iff.rfl
      rw [this]
      exact hT c
    · have : {ω : N.Ω | c ∈ t → ω ∈ T c} = univ := by
        ext ω
        simp [hc]
      rw [this]
      exact @MeasurableSet.univ _ (N.info (S c))
  have hrest : ∀ (t : Finset I) (T : ∀ d, Set (RegionCoord N (S d))),
      (∀ d, MeasurableSet (T d)) →
        MeasurableSet[aeClosure (N.info (S c)ᶜ) N.P] {ω : N.Ω | ∀ d ∈ t.erase c, ω ∈ T d} :=
    fun t T hT => measurableSet_setOf_forall_finset (M := aeClosure (N.info (S c)ᶜ) N.P)
      (t.erase c) (fun d => (T d : Set N.Ω))
      fun d hd => hface d (Finset.ne_of_mem_erase hd) _ (hT d)
  have hrestm : ∀ (t : Finset I) (T : ∀ d, Set (RegionCoord N (S d))),
      (∀ d, MeasurableSet (T d)) → MeasurableSet {ω : N.Ω | ∀ d ∈ t.erase c, ω ∈ T d} :=
    fun t T hT => measurableSet_setOf_forall_finset (t.erase c) (fun d => (T d : Set N.Ω))
      fun d _ => N.info_le _ _ (hT d)
  set A₀ : Set N.Ω := {ω | c ∈ s → ω ∈ A c} with hA₀def
  set B₀ : Set N.Ω := {ω | c ∈ s' → ω ∈ B c} with hB₀def
  set C₁ : Set N.Ω := {ω | ∀ d ∈ s.erase c, ω ∈ A d} with hC₁def
  set C₂ : Set N.Ω := {ω | ∀ d ∈ s'.erase c, ω ∈ B d} with hC₂def
  have hA₀m : MeasurableSet[N.info (S c)] A₀ := hfirst s A hA
  have hB₀m : MeasurableSet[N.info (S c)] B₀ := hfirst s' B hB
  obtain ⟨C₁', hC₁', hC₁e⟩ := hrest s A hA
  obtain ⟨C₂', hC₂', hC₂e⟩ := hrest s' B hB
  -- the law of the pair of coordinate vectors
  rw [Measure.map_apply hΨ ((hbox s A hA).prod (hbox s' B hB)),
    Measure.map_apply hU ((hbox s A hA).prod (hbox s' B hB))]
  have hL : (fun p : N.Ω × N.Ω => (regionMap N S p.1, regionMap N S p.2)) ⁻¹'
      ((s : Set I).pi A ×ˢ (s' : Set I).pi B) =
      (regionMap N S ⁻¹' (s : Set I).pi A) ×ˢ (regionMap N S ⁻¹' (s' : Set I).pi B) := rfl
  have hae : (A₀ ∩ C₁) ×ˢ (B₀ ∩ C₂) =ᵐ[pairLaw N (S c) ℓ] (A₀ ∩ C₁') ×ˢ (B₀ ∩ C₂') := by
    rw [Set.prod_eq, Set.prod_eq]
    exact ((pairLaw_map_fst hℓ).quasiMeasurePreserving.preimage_ae_eq
      (EventuallyEqSet.inter EventuallyEq.rfl hC₁e)).inter
      ((pairLaw_map_snd hℓ).quasiMeasurePreserving.preimage_ae_eq (EventuallyEqSet.inter EventuallyEq.rfl hC₂e))
  rw [hL, hsplit, hsplit, measure_congr hae, pairLaw_prod hℓ hind hA₀m hB₀m hC₁' hC₂']
  -- the law of `(x, x[c ↦ y])`
  have hR : (fun q : (∀ d, RegionCoord N (S d)) × RegionCoord N (S c) =>
      (q.1, Function.update q.1 c q.2)) ⁻¹' ((s : Set I).pi A ×ˢ (s' : Set I).pi B) =
      ((s : Set I).pi A ∩ {x : ∀ d, RegionCoord N (S d) | ∀ d ∈ s'.erase c, x d ∈ B d}) ×ˢ
        {y : RegionCoord N (S c) | c ∈ s' → y ∈ B c} := by
    ext ⟨x, y⟩
    simp only [mem_preimage, mem_prod, Set.mem_pi, Finset.mem_coe, mem_inter_iff, mem_ofPred_eq,
      Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun d hd => ?_⟩, fun hc => ?_⟩
      · have := h2 d hd.2
        rwa [Function.update_of_ne hd.1] at this
      · have := h2 c hc
        rwa [Function.update_self] at this
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun d hd => ?_⟩
      by_cases hdc : d = c
      · subst hdc
        rw [Function.update_self]
        exact h3 hd
      · rw [Function.update_of_ne hdc]
        exact h2 d ⟨hdc, hd⟩
  have hDeq : {x : ∀ d, RegionCoord N (S d) | ∀ d ∈ s'.erase c, x d ∈ B d} =
      ((s'.erase c : Finset I) : Set I).pi B := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_pi, Finset.mem_coe]
  have hD : MeasurableSet ((s : Set I).pi A ∩
      {x : ∀ d, RegionCoord N (S d) | ∀ d ∈ s'.erase c, x d ∈ B d}) := by
    rw [hDeq]
    exact (hbox s A hA).inter (hbox _ B hB)
  have hB₁ : MeasurableSet {y : RegionCoord N (S c) | c ∈ s' → y ∈ B c} := hB₀m
  rw [hR, Measure.compProd_apply_prod hD hB₁]
  set g : V → ℝ≥0∞ := fun v => N.P[B₀ | ℓ ⁻¹' {v}] with hgdef
  have hκ : ∀ x : ∀ d, RegionCoord N (S d),
      labelCondKernel N S c ℓ hℓ x {y : RegionCoord N (S c) | c ∈ s' → y ∈ B c} =
        g (regionLabel N (S c) ℓ (x c)) := by
    intro x
    change (regionLaw N S c)[{y : RegionCoord N (S c) | c ∈ s' → y ∈ B c} |
      regionLabel N (S c) ℓ ⁻¹' {regionLabel N (S c) ℓ (x c)}] = _
    exact regionLaw_cond N S c (hℓ _) hB₁
  have hgm : Measurable fun x : ∀ d, RegionCoord N (S d) => g (regionLabel N (S c) ℓ (x c)) :=
    (measurable_from_top (f := g)).comp
      ((measurable_top_of_fibers (f := regionLabel N (S c) ℓ) hℓ).comp (measurable_pi_apply c))
  simp_rw [hκ]
  rw [← hmap, setLIntegral_map hD hgm hΦ, preimage_inter, hsplit]
  have hpre : regionMap N S ⁻¹' {x : ∀ d, RegionCoord N (S d) | ∀ d ∈ s'.erase c, x d ∈ B d} =
      C₂ := rfl
  rw [hpre]
  have hm₁ : MeasurableSet A₀ := N.info_le _ _ hA₀m
  have hm : MeasurableSet (A₀ ∩ C₁ ∩ C₂) :=
    (hm₁.inter (hrestm s A hA)).inter (hrestm s' B hB)
  rw [setLIntegral_eq_sum_fibers (measurableSet_fiber hℓ) N.P hm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib := measurableSet_fiber hℓ v
  rw [setLIntegral_congr_fun (hm.inter hfib) (g := fun _ => g v)
      (fun ω hω => by
        change g (ℓ ω) = g v
        rw [show ℓ ω = v from hω.2]),
    setLIntegral_const]
  have hset : A₀ ∩ C₁ ∩ C₂ ∩ ℓ ⁻¹' {v} = ℓ ⁻¹' {v} ∩ A₀ ∩ (C₁ ∩ C₂) := by
    ext ω
    simp only [mem_inter_iff]
    tauto
  have hrfl : (ℓ ⁻¹' {v} ∩ A₀ : Set N.Ω) =ᵐ[N.P] (ℓ ⁻¹' {v} ∩ A₀ : Set N.Ω) := EventuallyEq.rfl
  rw [hset, measure_congr (EventuallyEqSet.inter hrfl (EventuallyEqSet.inter hC₁e hC₂e)),
    measure_fiber_inter hℓ hind v hA₀m (hC₁'.inter hC₂'),
    ← cond_mul_eq_inter hfib A₀ N.P]
  ring

/-- **Resampling a coordinate.** Under the resampling of the region `c` given its label, the pair
of coordinate vectors has the law of `(x, x[c ↦ y])`: `x` from the product of the coordinate
laws, `y` from the law of the coordinate `c` given its label at `x`. -/
theorem map_pairLaw_regionMap (hS : ∀ c, MeasurableSet (S c))
    (hfr : ∀ c, volume (frontier (S c)) = 0)
    (hnull : Pairwise fun c d => volume (S c ∩ S d) = 0) (c : I) (ℓ : N.Ω → V)
    (hℓ : ∀ v, MeasurableSet[N.info (S c)] (ℓ ⁻¹' {v})) :
    (pairLaw N (S c) ℓ).map (fun p => (regionMap N S p.1, regionMap N S p.2)) =
      (Measure.infinitePi (regionLaw N S) ⊗ₘ labelCondKernel N S c ℓ hℓ).map
        fun q => (q.1, Function.update q.1 c q.2) := by
  set Cyl := squareCylinders fun d => {s : Set (RegionCoord N (S d)) | MeasurableSet s}
    with hCyl
  have huniv : univ ∈ Cyl := ⟨∅, fun _ => univ, fun d _ => MeasurableSet.univ, by simp⟩
  have hspan : IsCountablySpanning Cyl := ⟨fun _ => univ, fun _ => huniv, iUnion_const _⟩
  have hpi : IsPiSystem Cyl :=
    isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      fun _ => MeasurableSet.univ
  refine ext_of_generate_finite (image2 (· ×ˢ ·) Cyl Cyl)
    (generateFrom_eq_prod generateFrom_squareCylinders generateFrom_squareCylinders hspan
      hspan).symm (hpi.prod hpi) ?_ ?_
  · rintro _ ⟨_, ⟨s, A, hA, rfl⟩, _, ⟨s', B, hB, rfl⟩, rfl⟩
    exact pairLaw_regionMap_box N hS hfr hnull c ℓ hℓ s s' A B (fun d => hA d (mem_univ d))
      (fun d => hB d (mem_univ d))
  · have := pairLaw_regionMap_box N hS hfr hnull c ℓ hℓ ∅ ∅ (fun _ => univ) (fun _ => univ)
      (fun _ => MeasurableSet.univ) (fun _ => MeasurableSet.univ)
    simpa using this

/-- **Resampling a coordinate, in integrals.** For a measurable `f` of two coordinate vectors,
`∫ f(coordinates of old, coordinates of new) dP' = E_x E_{y ~ ℒ(X_c | ℓ_c = ℓ_c(x_c))} f(x, x[c ↦ y])`.
-/
theorem lintegral_pairLaw_regionMap (hS : ∀ c, MeasurableSet (S c))
    (hfr : ∀ c, volume (frontier (S c)) = 0)
    (hnull : Pairwise fun c d => volume (S c ∩ S d) = 0) (c : I) (ℓ : N.Ω → V)
    (hℓ : ∀ v, MeasurableSet[N.info (S c)] (ℓ ⁻¹' {v}))
    {f : (∀ d, RegionCoord N (S d)) × (∀ d, RegionCoord N (S d)) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f (regionMap N S p.1, regionMap N S p.2) ∂pairLaw N (S c) ℓ =
      ∫⁻ x, ∫⁻ y, f (x, Function.update x c y)
        ∂(regionLaw N S c)[|regionLabel N (S c) ℓ ⁻¹' {regionLabel N (S c) ℓ (x c)}]
        ∂Measure.infinitePi (regionLaw N S) := by
  have hΦ := measurable_regionMap N S
  have hΨ : Measurable fun p : N.Ω × N.Ω => (regionMap N S p.1, regionMap N S p.2) :=
    (hΦ.comp measurable_fst).prodMk (hΦ.comp measurable_snd)
  have hU : Measurable fun q : (∀ d, RegionCoord N (S d)) × RegionCoord N (S c) =>
      (q.1, Function.update q.1 c q.2) :=
    measurable_fst.prodMk measurable_update'
  calc ∫⁻ p, f (regionMap N S p.1, regionMap N S p.2) ∂pairLaw N (S c) ℓ
      = ∫⁻ q, f q ∂(pairLaw N (S c) ℓ).map
          (fun p => (regionMap N S p.1, regionMap N S p.2)) := (lintegral_map hf hΨ).symm
    _ = ∫⁻ q, f q ∂(Measure.infinitePi (regionLaw N S) ⊗ₘ labelCondKernel N S c ℓ hℓ).map
          (fun q => (q.1, Function.update q.1 c q.2)) := by
        rw [map_pairLaw_regionMap N hS hfr hnull c ℓ hℓ]
    _ = ∫⁻ q, f (q.1, Function.update q.1 c q.2)
          ∂(Measure.infinitePi (regionLaw N S) ⊗ₘ labelCondKernel N S c ℓ hℓ) :=
        lintegral_map hf hU
    _ = _ := Measure.lintegral_compProd (hf.comp hU)

end Region

end IsotropicVariance.Paper.Proofs.Gain.Bridge
