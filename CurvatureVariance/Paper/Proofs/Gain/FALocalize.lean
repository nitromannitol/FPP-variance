/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.Gain.FAGeometry
public import CurvatureVariance.Paper.Proofs.Gain.FAAnalysis
public import CurvatureVariance.Paper.Proofs.Responses.Exchange
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Responses.SlabArrays

/-!
# Localization of the slab passage times in a block

The comparison of `Φ` with `Φ'` in the proof of Lemma `lem:labels`, where `Φ'` is computed with the
weights outside `G` replaced by an independent copy: the passage times between points of `Γ_G`
change only if a geodesic between them, for the old or the new weights, leaves `G`. For the block
`G` of slab `i` and a pair `z = (ω₀, ω)`, the splice `outsideSplice G z` has the weights of `ω` on
`G` and those of `ω₀` off `G`; it has the law `P` under `P ⊗ P` (`measurePreserving_outsideSplice`).

The subcube faces are covered by the cubes `I_{i−1}(j) × I_i(k)` of Section `sec:cubes`, `j, k` in
the row box; each lies in a pair of transverse cubes of side `w` (`finePairCube₁`, `finePairCube₂`)
with the localization radius `fineRadius`. If all these radii are at most `r` with
`C_d (1 + r) < ⌈√L⌉`, then by the tube property every slab geodesic between face points stays in `G`
(`edges_mem_block_of_fineRadius_le`), so the passage times of `ω` and of the splice agree. On the
event `leaveSet` that some radius of `ω` or of the splice exceeds `r`, the change is bounded by the
sum `fineSum` of the variables of Proposition `prop:profiles` on the fine pairs
(`ae_abs_sub_le_leaveSet`). `measure_leaveSet_le` is Markov's inequality for the radii, and
`lintegral_indicator_pow_le` the Cauchy–Schwarz step with the moments of `fineSum`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### The tube property -/

/-- The body of `Contracts.TubeStatement` for a given constant `C_d` and slope bound `T`. -/
def TubeProperty (m : ℕ) (Cd T : ℝ) : Prop :=
  ∀ (M : Model m) (K : ℕ) (A : ℝ), 1 ≤ A → ∀ (ω : Config m) (n : ℕ), 1 ≤ n →
  ∀ (t : EuclideanSpace ℝ (Fin m)), ‖t‖ ≤ T → ∀ (i : ℕ), 1 ≤ i → ∀ j k : Fin m → ℤ,
  ∀ u ∈ rowCube n (wInt M K A n) t ((i : ℤ) - 1) j, ∀ v ∈ rowCube n (wInt M K A n) t i k,
  ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ →
  ∀ e ∈ γ.edges, ∀ j' : Fin m → ℤ,
    ‖transversePoint (j' - fineIndex (wInt M K A n) t (edgeMid e))‖ ≤ 2 →
    j' ∈ tubeIndices j k (slabRadius M K A Cd ω n t i j k)

/-- The tube statement provides, for every slope bound `T ≥ 0`, a constant with the tube
property. -/
theorem exists_tubeProperty (h : Contracts.TubeStatement m) {T : ℝ} (hT : 0 ≤ T) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ TubeProperty m Cd T :=
  h T hT

/-! ### Fine pairs and their radii -/

/-- The transverse cube of side `w` containing `I_{i−1}(j)`. -/
noncomputable def finePairCube₁ (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ)
    (j : Fin m → ℤ) : Set (Vertex m) :=
  transverseCube (((i : ℤ) - 1) * n) (rowCubeCenter n w t ((i : ℤ) - 1) j) w

/-- The transverse cube of side `w` containing `I_i(k)`. -/
noncomputable def finePairCube₂ (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ)
    (k : Fin m → ℤ) : Set (Vertex m) :=
  transverseCube (((i : ℤ) - 1) * n + n) (rowCubeCenter n w t i k) w

/-- The localization radius of the slab geodesics of slab `i` between the cubes of a fine pair. -/
noncomputable def fineRadius (n w : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (Wn : ℝ)
    (jk : (Fin m → ℤ) × (Fin m → ℤ)) (ω : Config m) : ℝ≥0∞ :=
  locRadiusSlab ω (((i : ℤ) - 1) * n) (((i : ℤ) - 1) * n + n) (finePairCube₁ n w t i jk.1)
    (finePairCube₂ n w t i jk.2) Wn

/-- The fine pairs: `rowBox × rowBox`. -/
noncomputable def finePairs (L : ℕ) (o g : Fin m → ℤ) : Finset ((Fin m → ℤ) × (Fin m → ℤ)) :=
  rowBox L o g ×ˢ rowBox L o g

/-- `I_{i}(k)` lies in the second cube of a fine pair. -/
theorem rowCube_subset_finePairCube₂ {n w : ℕ} (hw : 0 < w) (t : EuclideanSpace ℝ (Fin m))
    (i : ℕ) (k : Fin m → ℤ) : rowCube n w t i k ⊆ finePairCube₂ n w t i k := by
  have h := rowCube_subset_transverseCube (n := n) hw t (i : ℤ) k
  rwa [show ((i : ℤ) * n) = ((i : ℤ) - 1) * n + n by ring] at h

/-- The localization radius is monotone in the two sets. -/
theorem locRadiusSlab_mono {ω : Config m} {p q : ℤ} {I I' J J' : Set (Vertex m)} (Wl : ℝ)
    (hI : I ⊆ J) (hI' : I' ⊆ J') : locRadiusSlab ω p q I I' Wl ≤ locRadiusSlab ω p q J J' Wl := by
  have hdev : deviation (fun γ => IsSlabGeodesic ω p q γ) I I' ≤
      deviation (fun γ => IsSlabGeodesic ω p q γ) J J' := by
    unfold deviation
    exact iSup₂_le fun u hu => le_iSup₂_of_le u (hI hu) (iSup₂_le fun v hv =>
      le_iSup₂_of_le v (hI' hv) le_rfl)
  unfold locRadiusSlab
  exact add_le_add_right (ENNReal.div_le_div_right hdev _) 1

/-- The splice `ω` on `G`, `ω₀` off `G`, of a pair `z = (ω₀, ω)`. -/
noncomputable def outsideSplice (G : Set (Sym2 (Vertex m))) (z : Config m × Config m) :
    Config m :=
  resample G z.1 z.2

/-- The splice is measurable. -/
theorem measurable_outsideSplice (G : Set (Sym2 (Vertex m))) :
    Measurable (outsideSplice G) :=
  Responses.measurable_resample G

/-- The splice of two independent configurations has the law of the weights. -/
theorem measurePreserving_outsideSplice {M : Model m} (hM : M.Standing)
    (G : Set (Sym2 (Vertex m))) : MeasurePreserving (outsideSplice G) (M.P.prod M.P) M.P := by
  have := hM.probF
  have := hM.probP
  exact (measurePreserving_fst (μ := M.P) (ν := M.P)).comp
    (Responses.measurePreserving_exchange hM.iid G)

/-- The splice agrees with `ω` on `G`. -/
theorem outsideSplice_eq_of_mem {G : Set (Sym2 (Vertex m))} (z : Config m × Config m)
    (e : Edge m) (he : e.1 ∈ G) : outsideSplice G z e = z.2 e := by
  classical
  simp [outsideSplice, resample, he]

/-! ### Geodesics stay in the block -/

/-- **Slab geodesics between face points stay in the block** when the radii of all fine pairs are at
most `r`, `C_d (1 + r) < ⌈√L⌉` (the proof of Lemma `lem:labels`). -/
theorem edges_mem_block_of_fineRadius_le {Cd T : ℝ} (hCd : 0 ≤ Cd)
    (hTube : TubeProperty m Cd T)
    {M : Model m} {K : ℕ} {A : ℝ} (hA : 1 ≤ A) {n L : ℕ} (hn : 1 ≤ n)
    (hw : 1 ≤ wInt M K A n) {t : EuclideanSpace ℝ (Fin m)} (ht : ‖t‖ ≤ T) {i : ℕ} (hi : 1 ≤ i)
    {o g : Fin m → ℤ} {ω : Config m} {r : ℝ} (hr0 : 0 ≤ r)
    (hrL : Cd * (1 + r) < ⌈Real.sqrt L⌉₊)
    (hrad : ∀ jk ∈ finePairs L o g,
      fineRadius n (wInt M K A n) t i (W M K A n) jk ω ≤ ENNReal.ofReal r)
    {u v : Vertex m} (hu : u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n))
    (hv : v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n))
    (γ : (latticeGraph m).Walk u v) (hγ : IsSlabGeodesic ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) γ) :
    ∀ e ∈ γ.edges, e ∈ block n (wInt M K A n) L t i o g := by
  intro e he
  set w := wInt M K A n
  have hw0 : 0 < w := hw
  set j := rowIndex n w t ((i : ℤ) - 1) u.2
  set k := rowIndex n w t (i : ℤ) v.2
  have hj : j ∈ rowBox L o g := rowIndex_mem_rowBox hw hu
  have hk : k ∈ rowBox L o g := rowIndex_mem_rowBox hw hv
  have hu' : u ∈ rowCube n w t ((i : ℤ) - 1) j := ⟨(mem_subcubeFace_iff.mp hu).1, rfl⟩
  have hv' : v ∈ rowCube n w t i k := ⟨(mem_subcubeFace_iff.mp hv).1, rfl⟩
  have htube := hTube M K A hA ω n hn t ht i hi j k u hu' v hv' γ hγ e he
    (fineIndex w t (edgeMid e)) (by simp [w])
  have hrjk := hrad (j, k) (Finset.mem_product.mpr ⟨hj, hk⟩)
  have hmono : locRadiusSlab ω (((i : ℤ) - 1) * n) ((i : ℤ) * n)
      (rowCube n w t ((i : ℤ) - 1) j) (rowCube n w t i k) (W M K A n) ≤ ENNReal.ofReal r := by
    refine le_trans ?_ hrjk
    rw [fineRadius, show ((i : ℤ) - 1) * n + n = (i : ℤ) * n by ring]
    exact locRadiusSlab_mono _ (rowCube_subset_transverseCube hw0 t _ j)
      ((rowCube_subset_finePairCube₂ hw0 t i k).trans
        (by rw [finePairCube₂, show ((i : ℤ) - 1) * n + n = (i : ℤ) * n by ring]))
  have hslab : slabRadius M K A Cd ω n t i j k ≤ ENNReal.ofReal (Cd * (1 + r)) := by
    unfold slabRadius
    rw [ENNReal.ofReal_mul hCd, ENNReal.ofReal_add zero_le_one hr0, ENNReal.ofReal_one]
    exact mul_le_mul_right (add_le_add_right hmono 1) _
  have htube' : fineIndex w t (edgeMid e) ∈ tubeIndices j k (ENNReal.ofReal (Cd * (1 + r))) :=
    le_trans htube hslab
  exact mem_block_iff.mpr ⟨hγ.2.1 e he,
    mem_blockIndices_of_mem_tubeIndices hj hk (by positivity) hrL htube'⟩

/-! ### The leaving event -/

/-- The event that the radius of some fine pair exceeds `r`, for `ω` or for the splice. -/
def leaveSet (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (Wn : ℝ) (o g : Fin m → ℤ)
    (r : ℝ) : Set (Config m × Config m) :=
  ⋃ jk ∈ finePairs L o g,
    ({z | ENNReal.ofReal r < fineRadius n w t i Wn jk z.2} ∪
      {z | ENNReal.ofReal r < fineRadius n w t i Wn jk (outsideSplice (block n w L t i o g) z)})

/-- The leaving event is measurable. -/
theorem measurableSet_leaveSet (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (Wn : ℝ)
    (o g : Fin m → ℤ) (r : ℝ) : MeasurableSet (leaveSet n w L t i Wn o g r) := by
  refine Finset.measurableSet_biUnion _ fun jk _ => MeasurableSet.union ?_ ?_
  · exact measurableSet_lt measurable_const
      ((Responses.measurable_locRadiusSlab _ _ _ _ _).comp measurable_snd)
  · exact measurableSet_lt measurable_const
      ((Responses.measurable_locRadiusSlab _ _ _ _ _).comp (measurable_outsideSplice _))

/-- **Markov's inequality for the leaving event**: `P⊗P(leave) ≤ 2 ∑_{fine pairs} E R^q / r^q`. -/
theorem measure_leaveSet_le {M : Model m} (hM : M.Standing) (n w L : ℕ)
    (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (Wn : ℝ) (o g : Fin m → ℤ) {r : ℝ} (hr : 0 < r)
    (q : ℕ) :
    (M.P.prod M.P) (leaveSet n w L t i Wn o g r) ≤
      ∑ jk ∈ finePairs L o g,
        2 * ((∫⁻ ω, fineRadius n w t i Wn jk ω ^ q ∂M.P) / ENNReal.ofReal r ^ q) := by
  have := hM.probP
  have hσ := measurePreserving_outsideSplice hM (block n w L t i o g)
  have hsnd : MeasurePreserving Prod.snd (M.P.prod M.P) M.P := measurePreserving_snd
  have hr0 : ENNReal.ofReal r ^ q ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne'
  have hrt : ENNReal.ofReal r ^ q ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hmark : ∀ jk, M.P {ω | ENNReal.ofReal r < fineRadius n w t i Wn jk ω} ≤
      (∫⁻ ω, fineRadius n w t i Wn jk ω ^ q ∂M.P) / ENNReal.ofReal r ^ q := by
    intro jk
    refine le_trans (measure_mono fun ω hω => ?_) (meas_ge_le_lintegral_div
      ((Responses.measurable_locRadiusSlab _ _ _ _ _).pow_const q).aemeasurable hr0 hrt)
    have hω' : ENNReal.ofReal r < fineRadius n w t i Wn jk ω := hω
    exact pow_le_pow_left₀ zero_le hω'.le q
  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun jk _ => ?_)
  refine (measure_union_le _ _).trans ?_
  have h1 : (M.P.prod M.P) {z : Config m × Config m |
      ENNReal.ofReal r < fineRadius n w t i Wn jk z.2} =
      M.P {ω | ENNReal.ofReal r < fineRadius n w t i Wn jk ω} :=
    hsnd.measure_preimage (measurableSet_lt measurable_const
      (Responses.measurable_locRadiusSlab _ _ _ _ _)).nullMeasurableSet
  have h2 : (M.P.prod M.P) {z : Config m × Config m |
      ENNReal.ofReal r < fineRadius n w t i Wn jk (outsideSplice (block n w L t i o g) z)} =
      M.P {ω | ENNReal.ofReal r < fineRadius n w t i Wn jk ω} :=
    hσ.measure_preimage (measurableSet_lt measurable_const
      (Responses.measurable_locRadiusSlab _ _ _ _ _)).nullMeasurableSet
  rw [h1, h2, two_mul]
  exact add_le_add (hmark jk) (hmark jk)

/-! ### The change of slab passage times -/

/-- The sum `∑_{fine pairs} max(X_{jk}, 0)` of the variables of Proposition `prop:profiles`. -/
noncomputable def fineSum (L : ℕ) (o g : Fin m → ℤ)
    (X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ) (ω : Config m) : ℝ :=
  ∑ jk ∈ finePairs L o g, max (X jk ω) 0

/-- Each fine-pair variable is at most `fineSum`. -/
theorem le_fineSum {L : ℕ} {o g : Fin m → ℤ} {X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ}
    {jk : (Fin m → ℤ) × (Fin m → ℤ)} (hjk : jk ∈ finePairs L o g) (ω : Config m) :
    X jk ω ≤ fineSum L o g X ω :=
  (le_max_left _ _).trans (Finset.single_le_sum (f := fun jk => max (X jk ω) 0)
    (fun _ _ => le_max_right _ _) hjk)

/-- The almost sure conditions used at one configuration: slab geodesics exist, and the bounds
of Proposition `prop:profiles` hold on all fine pairs. -/
def FineGood (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (o g : Fin m → ℤ) (μ : PtNorm m)
    (X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ) (ω : Config m) : Prop :=
  (∀ (p q : ℤ), p + 2 ≤ q → ∀ u v : Vertex m, p ≤ u.1 ∧ u.1 ≤ q → p ≤ v.1 ∧ v.1 ≤ q →
      ∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω p q γ) ∧
    ∀ jk ∈ finePairs L o g, ∀ u ∈ finePairCube₁ n w t i jk.1, ∀ v ∈ finePairCube₂ n w t i jk.2,
      |slabTimeReal ω u.1 v.1 u v - μ.1 (point v - point u)| ≤ X jk ω

/-- **The change of slab passage times under resampling outside the block** (the proof of Lemma
`lem:labels`): almost surely in `z = (ω₀, ω)`, for all face points `u, v`,
`|D_i(ω)(u,v) − D_i(splice)(u,v)| ≤ 1_{leave}(z) (S(ω) + S(splice))`, `S = fineSum`. -/
theorem ae_abs_sub_le_leaveSet {M : Model m} (hM : M.Standing) {Cd T : ℝ} (hCd : 0 ≤ Cd)
    (hTube : TubeProperty m Cd T) {K : ℕ} {A : ℝ} (hA : 1 ≤ A) {n L : ℕ} (hn : 2 ≤ n)
    (hw : 1 ≤ wInt M K A n) {t : EuclideanSpace ℝ (Fin m)} (ht : ‖t‖ ≤ T) {i : ℕ} (hi : 1 ≤ i)
    {o g : Fin m → ℤ} {r : ℝ} (hr0 : 0 ≤ r) (hrL : Cd * (1 + r) < ⌈Real.sqrt L⌉₊)
    {X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ}
    (hX : ∀ᵐ ω ∂M.P, FineGood n (wInt M K A n) L t i o g M.μ X ω) :
    ∀ᵐ z ∂(M.P.prod M.P),
      ∀ u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n),
      ∀ v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n),
        |slabTimeReal z.2 (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v -
            slabTimeReal (outsideSplice (block n (wInt M K A n) L t i o g) z)
              (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v| ≤
          (leaveSet n (wInt M K A n) L t i (W M K A n) o g r).indicator
            (fun z => fineSum L o g X z.2 +
              fineSum L o g X (outsideSplice (block n (wInt M K A n) L t i o g) z)) z := by
  have := hM.probP
  set w := wInt M K A n
  set G := block n w L t i o g
  have hσ := measurePreserving_outsideSplice hM G
  have hsnd : MeasurePreserving Prod.snd (M.P.prod M.P) M.P := measurePreserving_snd
  have h1 := hsnd.quasiMeasurePreserving.ae hX
  have h2 := hσ.quasiMeasurePreserving.ae hX
  filter_upwards [h1, h2] with z hz1 hz2 u hu v hv
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hu1 : u.1 = ((i : ℤ) - 1) * n := (mem_subcubeFace_iff.mp hu).1
  have hv1 : v.1 = (i : ℤ) * n := (mem_subcubeFace_iff.mp hv).1
  have hslab : ((i : ℤ) - 1) * n + 2 ≤ (i : ℤ) * n := by
    have : (2 : ℤ) ≤ n := by exact_mod_cast hn
    linarith
  have hus : ((i : ℤ) - 1) * n ≤ u.1 ∧ u.1 ≤ (i : ℤ) * n := ⟨hu1.ge, by rw [hu1]; linarith⟩
  have hvs : ((i : ℤ) - 1) * n ≤ v.1 ∧ v.1 ≤ (i : ℤ) * n := ⟨by rw [hv1]; linarith, hv1.le⟩
  by_cases hb : z ∈ leaveSet n w L t i (W M K A n) o g r
  · rw [indicator_of_mem hb]
    have hw0 : 0 < w := hw
    set j := rowIndex n w t ((i : ℤ) - 1) u.2
    set k := rowIndex n w t (i : ℤ) v.2
    have hjk : (j, k) ∈ finePairs L o g :=
      Finset.mem_product.mpr ⟨rowIndex_mem_rowBox hw hu, rowIndex_mem_rowBox hw hv⟩
    have huc : u ∈ finePairCube₁ n w t i j :=
      rowCube_subset_transverseCube hw0 t _ j ⟨hu1, rfl⟩
    have hvc : v ∈ finePairCube₂ n w t i k :=
      rowCube_subset_finePairCube₂ hw0 t i k ⟨hv1, rfl⟩
    have e1 := hz1.2 (j, k) hjk u huc v hvc
    have e2 := hz2.2 (j, k) hjk u huc v hvc
    rw [hu1, hv1] at e1 e2
    have f1 := le_fineSum (X := X) hjk z.2
    have f2 := le_fineSum (X := X) hjk (outsideSplice G z)
    rw [abs_le] at e1 e2 ⊢
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  · rw [indicator_of_notMem hb]
    simp only [leaveSet, mem_iUnion, mem_union, mem_ofPred_eq, not_exists, not_or,
      not_lt] at hb
    have hrad1 : ∀ jk ∈ finePairs L o g,
        fineRadius n w t i (W M K A n) jk z.2 ≤ ENNReal.ofReal r := fun jk hjk => (hb jk hjk).1
    have hrad2 : ∀ jk ∈ finePairs L o g,
        fineRadius n w t i (W M K A n) jk (outsideSplice G z) ≤ ENNReal.ofReal r :=
      fun jk hjk => (hb jk hjk).2
    obtain ⟨γ, hγ⟩ := hz1.1 _ _ hslab u v hus hvs
    obtain ⟨γ', hγ'⟩ := hz2.1 _ _ hslab u v hus hvs
    have hG := edges_mem_block_of_fineRadius_le hCd hTube hA hn1 hw ht hi hr0 hrL hrad1 hu hv γ hγ
    have hG' := edges_mem_block_of_fineRadius_le hCd hTube hA hn1 hw ht hi hr0 hrL hrad2 hu hv
      γ' hγ'
    have le1 : slabTime (outsideSplice G z) (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v ≤
        slabTime z.2 (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v :=
      slabTime_le_of_isSlabGeodesic hγ fun e he => outsideSplice_eq_of_mem z e (hG e.1 he)
    have le2 : slabTime z.2 (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v ≤
        slabTime (outsideSplice G z) (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v :=
      slabTime_le_of_isSlabGeodesic hγ' fun e he => (outsideSplice_eq_of_mem z e (hG' e.1 he)).symm
    rw [slabTimeReal, slabTimeReal, le_antisymm le1 le2, sub_self, abs_zero]

/-! ### Moments -/

/-- **Cauchy–Schwarz for the localization error**: for `f ≥ 0` and an event `E`,
`E (1_E f)^p ≤ P(E)^{1/2} (E f^{2p})^{1/2}`. -/
theorem lintegral_indicator_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : Set Ω} (hE : MeasurableSet E) {f : Ω → ℝ} (hf : Measurable f) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ z, ENNReal.ofReal (E.indicator f z ^ p) ∂P ≤
      P E ^ (1 / 2 : ℝ) * (∫⁻ z, ENNReal.ofReal (f z ^ (2 * p)) ∂P) ^ (1 / 2 : ℝ) := by
  have heq : (fun z => ENNReal.ofReal (E.indicator f z ^ p)) =
      E.indicator fun z => ENNReal.ofReal (f z ^ p) := by
    funext z
    by_cases hz : z ∈ E
    · simp [hz]
    · simp [hz, zero_pow (by omega : p ≠ 0)]
  rw [heq]
  refine (lintegral_indicator_le_sqrt_mul (hf.pow_const p).ennreal_ofReal.aemeasurable hE).trans ?_
  gcongr with z
  rw [ENNReal.rpow_two]
  rcases le_or_gt 0 (f z ^ p) with h | h
  · rw [← ENNReal.ofReal_pow h, ← pow_mul, mul_comm]
  · rw [ENNReal.ofReal_of_nonpos h.le]
    simp

end CurvatureVariance.Paper.Gain
