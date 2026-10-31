/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Measurability.SlabTime
public import IsotropicVariance.Infra.Measurability.PassageVersion
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Slabs with disjoint interiors have independent slab passage times

Section `ssec:overview`: "By the locality in Assumption `ass:local`, `T_P` is determined by
`ω|_P`, so the `T^{(i)}` are independent."

The slab passage time `D(u, v)` is, for endpoints in the slab, the passage time of the extended
density (`passTime_eq_passageTime_extDensity`), which equals the bound `b` within distance one of
the faces and outside the slab, and the density elsewhere. At a point of the slab at distance
more than one from the faces, the closed unit ball lies in the interior of the slab, so the
extended density is jointly measurable for the information of the slab and the Borel sets
(`Setting.determined_joint`). The passage time is a measurable functional of the density only
up to null sets, and only over a standard Borel space; the information of a set is not one.
We therefore

1. find a sequence of sets `Aₙ` in the information of the slab such that the extended density
   is jointly measurable for `σ(Aₙ) ⊗ 𝓑` (`exists_factor_of_measurable_prod`), so that it
   factors as `h(Φ(ω), x)` through `Φ(ω) = (1_{Aₙ}(ω))ₙ ∈ ℕ → Bool` (a standard Borel space) with
   `h` jointly Borel (Doob–Dynkin);
2. take a jointly measurable passage-time version for the density `h` on `ℕ → Bool` under the
   law of `Φ`, continuous in the endpoints (`exists_jointlyMeasurable_passageTime_version`),
   and compose it with `Φ`.

The resulting version of `D` is measurable for the information of the slab, so versions for
slabs with disjoint interiors are independent (`NoiseModel.iIndep_info`; slabs have null
boundaries).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace IsotropicVariance.Infra.Slab

open IsotropicVariance.Paper

/-! ## Countable reduction of product-measurable functions -/

section Factor

variable {Ω Y : Type*} [MeasurableSpace Y]

omit [MeasurableSpace Y] in
lemma prod_mono_left {m₁ m₂ : MeasurableSpace Ω} (h : m₁ ≤ m₂) (mY : MeasurableSpace Y) :
    m₁.prod mY ≤ m₂.prod mY :=
  sup_le_sup_right (MeasurableSpace.comap_mono h) _

/-- A set of `Ω × Y` is countably determined by `G` if it is measurable for `σ(Aₙ) ⊗ 𝓑(Y)` for
a sequence of sets `Aₙ` in `G`. -/
def CountablyDetermined (G : MeasurableSpace Ω) (E : Set (Ω × Y)) : Prop :=
  ∃ A : ℕ → Set Ω, (∀ n, MeasurableSet[G] (A n)) ∧
    MeasurableSet[(MeasurableSpace.generateFrom (range A)).prod ‹MeasurableSpace Y›] E

/-- The countably determined sets form a σ-algebra (merge countably many sequences into one). -/
@[instance_reducible]
def countablyDeterminedSpace (G : MeasurableSpace Ω) : MeasurableSpace (Ω × Y) where
  MeasurableSet' := CountablyDetermined G
  measurableSet_empty := ⟨fun _ => ∅, fun _ => MeasurableSpace.measurableSet_empty _,
    MeasurableSpace.measurableSet_empty _⟩
  measurableSet_compl := fun _ ⟨A, hA, hE⟩ => ⟨A, hA, hE.compl⟩
  measurableSet_iUnion := fun E hE => by
    choose A hA hEA using hE
    refine ⟨fun n => A (Nat.unpair n).1 (Nat.unpair n).2, fun n => hA _ _, ?_⟩
    refine MeasurableSet.iUnion fun k => prod_mono_left (MeasurableSpace.generateFrom_mono ?_)
      _ _ (hEA k)
    rintro _ ⟨j, rfl⟩
    exact ⟨Nat.pair k j, by simp⟩

/-- Every set measurable for `G ⊗ 𝓑(Y)` is countably determined by `G`. -/
lemma prod_le_countablyDeterminedSpace (G : MeasurableSpace Ω) :
    G.prod ‹MeasurableSpace Y› ≤ countablyDeterminedSpace G := by
  refine sup_le ?_ ?_
  · rw [MeasurableSpace.comap_le_iff_le_map]
    intro A hA
    exact ⟨fun _ => A, fun _ => hA, (le_sup_left : MeasurableSpace.comap Prod.fst _ ≤ _) _
      ⟨A, MeasurableSpace.measurableSet_generateFrom ⟨0, rfl⟩, rfl⟩⟩
  · rw [MeasurableSpace.comap_le_iff_le_map]
    intro B hB
    exact ⟨fun _ => ∅, fun _ => MeasurableSpace.measurableSet_empty _,
      (le_sup_right : MeasurableSpace.comap Prod.snd _ ≤ _) _ ⟨B, hB, rfl⟩⟩

/-- **Countable reduction and Doob–Dynkin.** A real function on `Ω × Y` measurable for
`G ⊗ 𝓑(Y)` factors as `h(Φ(ω), y)` with `Φ : Ω → (ℕ → Bool)` measurable for `G` and `h` jointly
measurable. -/
theorem exists_factor_of_measurable_prod {G : MeasurableSpace Ω} {f : Ω × Y → ℝ}
    (hf : Measurable[G.prod ‹MeasurableSpace Y›] f) :
    ∃ Φ : Ω → ℕ → Bool, Measurable[G] Φ ∧
      ∃ h : (ℕ → Bool) × Y → ℝ, Measurable h ∧ ∀ ω y, f (ω, y) = h (Φ ω, y) := by
  classical
  set T := MeasurableSpace.natGeneratingSequence ℝ
  have hT : ∀ n, CountablyDetermined G (f ⁻¹' T n) := fun n =>
    prod_le_countablyDeterminedSpace G _
      (hf (MeasurableSpace.measurableSet_natGeneratingSequence n))
  choose A hA hfA using hT
  set B : ℕ → Set Ω := fun n => A (Nat.unpair n).1 (Nat.unpair n).2 with hBdef
  set Φ : Ω → ℕ → Bool := fun ω n => decide (ω ∈ B n) with hΦdef
  have hpre (n : ℕ) : Φ ⁻¹' {y | y n = true} = B n := by
    ext ω
    simp [Φ]
  have hΦ : Measurable[G] Φ := by
    rw [measurable_pi_iff]
    intro n
    refine measurable_to_bool ?_
    have : (fun ω => Φ ω n) ⁻¹' {true} = B n := by
      ext ω
      simp [Φ]
    rw [this]
    exact hA _ _
  -- `σ(Bₙ)` is contained in the pullback of the product σ-algebra of `ℕ → Bool` by `Φ`.
  have hle : MeasurableSpace.generateFrom (range B) ≤
      (inferInstance : MeasurableSpace (ℕ → Bool)).comap Φ := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨{y | y n = true}, measurableSet_eq_fun (measurable_pi_apply n) measurable_const,
      hpre n⟩
  -- `f` is measurable for `σ(Bₙ) ⊗ 𝓑(Y)`.
  have hfB : Measurable[(MeasurableSpace.generateFrom (range B)).prod ‹MeasurableSpace Y›] f := by
    have h : Measurable[(MeasurableSpace.generateFrom (range B)).prod ‹MeasurableSpace Y›,
        MeasurableSpace.generateFrom (range T)] f := by
      refine @measurable_generateFrom _ _ ((MeasurableSpace.generateFrom (range B)).prod _) _ _
        ?_
      rintro _ ⟨n, rfl⟩
      refine prod_mono_left (MeasurableSpace.generateFrom_mono ?_) _ _ (hfA n)
      rintro _ ⟨j, rfl⟩
      exact ⟨Nat.pair n j, by simp [B]⟩
    rwa [MeasurableSpace.generateFrom_natGeneratingSequence] at h
  have hfΦ : Measurable[(MeasurableSpace.prod (inferInstance : MeasurableSpace (ℕ → Bool))
      ‹MeasurableSpace Y›).comap (Prod.map Φ id)] f := by
    rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
    exact hfB.mono (prod_mono_left hle _) le_rfl
  obtain ⟨h, hh, hfh⟩ := hfΦ.exists_eq_measurable_comp
  exact ⟨Φ, hΦ, h, hh, fun ω y => congrFun hfh (ω, y)⟩

/-- Gluing a function defined on the points of `Y` satisfying `P` with a constant along a
measurable set of such points. -/
lemma measurable_dite_mem [MeasurableSpace Ω] {P : Y → Prop} {A : Set Y}
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (hAP : ∀ y ∈ A, P y)
    {g : Ω × {y // P y} → ℝ} (hg : Measurable g) (c : ℝ) :
    Measurable fun p : Ω × Y => if h : p.2 ∈ A then g (p.1, ⟨p.2, hAP _ h⟩) else c :=
  Measurable.dite (s := {p : Ω × Y | p.2 ∈ A})
    (f := fun q => g (q.1.1, ⟨q.1.2, hAP _ q.2⟩))
    (hg.comp ((measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)))
    (g := fun _ => c) measurable_const (hA.preimage measurable_snd)

end Factor

/-! ## Slab geometry: the inner region and the null boundary -/

variable {m : ℕ}

/-- A point of the slab at distance more than one from the faces has its closed unit ball in the
interior of the slab. -/
lemma closedBall_subset_interior_slab (sl : Slab m) {x : Pt m} (hx : x ∈ sl.set)
    (h1 : ¬ infDist x sl.faces ≤ 1) : closedBall x 1 ⊆ interior sl.set := by
  rw [not_le] at h1
  set z := sl.motion.symm x
  have hxz : x = sl.motion z := (sl.motion.apply_symm_apply x).symm
  -- The two feet of `x` on the faces.
  have hfoot (c : ℝ) (hc : c = 0 ∨ c = sl.width) :
      1 < |slabCoord sl x - c| := by
    let f := sl.motion (WithLp.toLp 2 (c, Pt.tr z))
    have hf : f ∈ sl.faces := by
      rw [mem_slab_faces_iff]
      simpa [f, slabCoord, Pt.lon] using hc
    have hd : dist x f = |slabCoord sl x - c| := by
      rw [hxz, sl.motion.dist_map,
        dist_eq_abs_lon_sub (x := z) (y := WithLp.toLp 2 (c, Pt.tr z)) rfl]
      simp [slabCoord, Pt.lon, z]
    exact h1.trans_le ((infDist_le_dist_of_mem hf).trans_eq hd)
  have hx' := (mem_slab_set_iff sl).mp hx
  have h0 := hfoot 0 (Or.inl rfl)
  have hw := hfoot sl.width (Or.inr rfl)
  rw [sub_zero, abs_of_nonneg hx'.1] at h0
  rw [abs_of_nonpos (sub_nonpos.mpr hx'.2)] at hw
  have hsub : slabCoord sl ⁻¹' Ioo 0 sl.width ⊆ interior sl.set := by
    refine interior_maximal (fun y hy => ?_) (isOpen_Ioo.preimage (continuous_slabCoord sl))
    rw [slab_set_eq_preimage]
    exact Ioo_subset_Icc_self hy
  intro y hy
  apply hsub
  have hd : |slabCoord sl y - slabCoord sl x| ≤ 1 := by
    have := (lipschitzWith_slabCoord sl).dist_le_mul y x
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at this
    exact this.trans (mem_closedBall.mp hy)
  rw [abs_le] at hd
  constructor <;> linarith

/-- A level set of the coordinate across a slab is Lebesgue-null. -/
lemma volume_slabCoord_preimage_singleton (sl : Slab m) (c : ℝ) :
    volume (slabCoord sl ⁻¹' {c}) = 0 := by
  have hset : slabCoord sl ⁻¹' {c} =
      ((({c} : AffineSubspace ℝ ℝ).comap (slabCoordAffine sl) : AffineSubspace ℝ (Pt m)) :
        Set (Pt m)) := by
    rw [AffineSubspace.coe_comap]
    simp
    rfl
  rw [hset]
  refine Measure.addHaar_affineSubspace _ _ fun htop => ?_
  have hp : sl.motion (WithLp.toLp 2 (c + 1, 0)) ∈
      ((({c} : AffineSubspace ℝ ℝ).comap (slabCoordAffine sl) : AffineSubspace ℝ (Pt m)) :
        Set (Pt m)) := by
    rw [htop]
    exact mem_univ _
  rw [← hset] at hp
  simp [slabCoord, Pt.lon] at hp

/-- The boundary of a slab is Lebesgue-null: it lies in the two faces. -/
lemma volume_frontier_slab_set (sl : Slab m) : volume (frontier sl.set) = 0 := by
  have hfr : frontier (Icc (0 : ℝ) sl.width) ⊆ {0, sl.width} := by
    by_cases hw : 0 ≤ sl.width
    · rw [frontier_Icc hw]
    · rw [Icc_eq_empty hw, frontier_empty]
      exact empty_subset _
  have hsub : frontier sl.set ⊆ slabCoord sl ⁻¹' {0} ∪ slabCoord sl ⁻¹' {sl.width} := by
    rw [slab_set_eq_preimage]
    refine ((continuous_slabCoord sl).frontier_preimage_subset _).trans ?_
    intro x hx
    rcases hfr hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hsub (measure_union_null
    (volume_slabCoord_preimage_singleton sl 0) (volume_slabCoord_preimage_singleton sl _))

/-! ## The extended density is determined by the noise in the slab -/

variable (X : Setting m)

/-- The extended density is jointly measurable for the information of the slab and the Borel
sets: it is the bound `b` near the faces and outside the slab, and elsewhere the density at a
point whose closed unit ball lies in the interior of the slab (Assumption `ass:local` (1),
jointly). -/
lemma measurable_extDensity_info (b : ℝ) (sl : Slab m) :
    Measurable[(X.info sl.set).prod inferInstance]
      fun p : X.Ω × Pt m => extDensity sl b (X.ρ p.1) p.2 := by
  classical
  set A : Set (Pt m) := {x | x ∈ sl.set ∧ ¬ infDist x sl.faces ≤ 1}
  have hA : MeasurableSet A :=
    (measurableSet_slab_set sl).inter
      (measurableSet_le (continuous_infDist_pt _).measurable measurable_const).compl
  have hAP : ∀ x ∈ A, closedBall x 1 ⊆ interior sl.set :=
    fun x hx => closedBall_subset_interior_slab sl hx.1 hx.2
  have heq : (fun p : X.Ω × Pt m => extDensity sl b (X.ρ p.1) p.2) = fun p =>
      if h : p.2 ∈ A then X.ρ p.1 (⟨p.2, hAP _ h⟩ : {x : Pt m // closedBall x 1 ⊆ interior sl.set})
      else b := by
    funext p
    by_cases hS : p.2 ∈ sl.set
    · by_cases hd : infDist p.2 sl.faces ≤ 1
      · have hpA : p.2 ∉ A := fun h => h.2 hd
        simp [extDensity_of_mem sl b _ hS, Slab.density, hd, hpA]
      · have hpA : p.2 ∈ A := ⟨hS, hd⟩
        simp [extDensity_of_mem sl b _ hS, Slab.density, hd, hpA]
    · have hpA : p.2 ∉ A := fun h => hS h.1
      simp [extDensity_of_notMem sl b _ hS, hpA]
  rw [heq]
  have hg := X.determined_joint (interior sl.set) isOpen_interior
  have h := @measurable_dite_mem X.Ω (Pt m) _ (X.info (interior sl.set)) _ A _ hA hAP
    (fun p => X.ρ p.1 p.2) hg b
  exact h.mono (prod_mono_left (X.info_mono interior_subset) _) le_rfl

/-- **A version of the slab passage time determined by the noise in the slab**: jointly
measurable, continuous in the endpoints, measurable (as a random function of the endpoints) for
the information of the slab, and equal to the slab passage time at all endpoints in the slab on
one full-measure event. -/
theorem exists_slabTime_version {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m) :
    ∃ V : X.Ω → Pt m × Pt m → ℝ, Measurable (Function.uncurry V) ∧ (∀ ω, Continuous (V ω)) ∧
      Measurable[X.info sl.set] V ∧
      ∀ᵐ ω ∂X.P, ∀ u ∈ sl.set, ∀ v ∈ sl.set, V ω (u, v) = X.slabTime b sl ω u v := by
  obtain ⟨Φ, hΦ, h, hh, hfh⟩ := exists_factor_of_measurable_prod
    (measurable_extDensity_info X b sl)
  have hΦm : Measurable Φ := hΦ.mono (X.info_le _) le_rfl
  let ρ' : (ℕ → Bool) × Pt m → ℝ≥0∞ := fun q => ENNReal.ofReal (min (h q) b)
  have hρ' : Measurable ρ' := (hh.min measurable_const).ennreal_ofReal
  have hbd : ∀ y x, ρ' (y, x) ≤ (b.toNNReal : ℝ≥0∞) :=
    fun _ _ => ENNReal.ofReal_le_ofReal (min_le_right _ _)
  obtain ⟨T, hTm, hTc, hTae⟩ :=
    Infra.Measurability.exists_jointlyMeasurable_passageTime_version (X.P.map Φ) hρ' hbd
  refine ⟨fun ω => T (Φ ω), ?_, fun ω => hTc (Φ ω), ?_, ?_⟩
  · exact hTm.comp (hΦm.prodMap measurable_id)
  · have hT : Measurable T :=
      Measurable.of_eval fun p => hTm.comp (measurable_id.prodMk measurable_const)
    exact hT.comp hΦ
  · filter_upwards [ae_of_ae_map hΦm.aemeasurable hTae] with ω hω u hu v hv
    rw [hω (u, v), slabTime_eq_infra X hb sl ω hu hv]
    congr 2
    funext x
    have hx := hfh ω x
    simp only at hx
    simp only [ρ', ← hx, min_eq_left (extDensity_le sl (hb ω) x)]

/-- **Slabs with disjoint interiors have independent slab passage times**
(Section `ssec:overview`): there are versions of the slab passage times, jointly measurable and
continuous in the endpoints, that are independent random functions of the endpoints and agree
with the slab passage times at all endpoints in their slabs on one full-measure event. -/
theorem exists_iIndep_slabTime_versions {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ}
    (sl : Fin M → Slab m)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => interior (sl i).set)) :
    ∃ V : Fin M → X.Ω → Pt m × Pt m → ℝ,
      (∀ i, Measurable (Function.uncurry (V i))) ∧ (∀ i ω, Continuous (V i ω)) ∧
      ProbabilityTheory.iIndepFun (fun i ω => V i ω) X.P ∧
      ∀ᵐ ω ∂X.P, ∀ i, ∀ u ∈ (sl i).set, ∀ v ∈ (sl i).set,
        V i ω (u, v) = X.slabTime b (sl i) ω u v := by
  choose V hVm hVc hVinfo hVae using fun i => exists_slabTime_version X hb (sl i)
  refine ⟨V, hVm, hVc, ?_, ae_all_iff.mpr hVae⟩
  rw [iIndepFun_iff_iIndep]
  refine iIndep_of_iIndep_of_le (X.iIndep_info (Fin M) (fun i => (sl i).set)
    (fun i => measurableSet_slab_set (sl i)) (fun i => volume_frontier_slab_set (sl i)) hdisj)
    fun i => (hVinfo i).comap_le

end IsotropicVariance.Infra.Slab
