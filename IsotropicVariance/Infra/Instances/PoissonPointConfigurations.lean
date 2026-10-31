/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Instances.PoissonConfigurations
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Repartitioning locally finite point families into canonical configurations -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace IsotropicVariance.Infra.Instances

lemma isBounded_poissonCube {d : ℕ} (z : Fin d → ℤ) : Bornology.IsBounded (Poisson.cube z) := by
  let K : Set (Fin d → ℝ) := Set.pi univ (fun i => Icc (z i : ℝ) ((z i : ℝ) + 1))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  apply (hK.image (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))).isBounded.subset
  intro x hx
  refine ⟨WithLp.ofLp x, ?_, by simp only [WithLp.toLp_ofLp]⟩
  intro i _
  have hh := (Int.floor_eq_iff.mp (congrFun hx i))
  exact ⟨hh.1, hh.2.le⟩

lemma poissonCubeCloud_eq_sum_dirac {d : ℕ} (z : Fin d → ℤ)
    (c : PoissonFiniteCloud (Poisson.cube z)) :
    poissonCubeCloud z c = ∑ i : Fin c.1, Measure.dirac ((c.2.val i).val) := by
  rw [poissonCubeCloud, poissonFiniteCloudMeasure,
    Measure.map_finset_sum' measurable_subtype_coe.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  exact Measure.map_dirac' measurable_subtype_coe _

/-- A countable locally finite family, including repetitions, has a canonical representation. -/
theorem exists_poissonConfiguration_of_points {d : ℕ} {ι : Type*} [Countable ι]
    (p : ι → Poisson.E d)
    (hfinite : ∀ B : Set (Poisson.E d), Bornology.IsBounded B → {i | p i ∈ B}.Finite) :
    ∃ c : PoissonConfiguration d, poissonConfigurationMeasure c = Measure.sum (fun i => Measure.dirac (p i)) := by
  classical
  let I (z : Fin d → ℤ) := {i : ι // Poisson.cubeIndex (p i) = z}
  have hI (z : Fin d → ℤ) : Finite (I z) :=
    (hfinite (Poisson.cube z) (isBounded_poissonCube z)).to_subtype
  let (z : Fin d → ℤ) : Fintype (I z) := Fintype.ofFinite _
  choose c hc using fun z : Fin d → ℤ => exists_poissonFiniteCloud_of_fintype
    (fun i : I z => (⟨p i.val, i.property⟩ : Poisson.cube z))
  have hcloud (z : Fin d → ℤ) : poissonCubeCloud z (c z) =
      Measure.sum (fun i : I z => Measure.dirac (p i.val)) := by
    rw [poissonCubeCloud, hc z, Measure.map_finset_sum' measurable_subtype_coe.aemeasurable,
      Measure.sum_fintype]
    apply Finset.sum_congr rfl
    intro i _
    exact Measure.map_dirac' measurable_subtype_coe _
  refine ⟨c, ?_⟩
  ext B hB
  simp only [poissonConfigurationMeasure, Measure.sum_apply _ hB, hcloud]
  exact ENNReal.tsum_fiberwise (fun i => Measure.dirac (p i) B) (fun i => Poisson.cubeIndex (p i))

/-- The countable index of the physical points of a canonical configuration. -/
abbrev PoissonPointIndex {d : ℕ} (c : PoissonConfiguration d) := Σ z : Fin d → ℤ, Fin (c z).1

def poissonConfigurationPoint {d : ℕ} (c : PoissonConfiguration d) (p : PoissonPointIndex c) :
    Poisson.E d := ((c p.1).2.val p.2).val

lemma poissonConfigurationPoint_locallyFinite {d : ℕ} (c : PoissonConfiguration d)
    (B : Set (Poisson.E d)) (hb : Bornology.IsBounded B) :
    {p : PoissonPointIndex c | poissonConfigurationPoint c p ∈ B}.Finite := by
  classical
  let F := (Poisson.finite_cubeIndex_image hb).toFinset
  let G : Finset (PoissonPointIndex c) := F.sigma fun z => Finset.univ
  apply G.finite_toSet.subset
  intro p hp
  apply Finset.mem_sigma.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  simpa only [F, Set.Finite.mem_toFinset] using
    (show p.1 ∈ Poisson.cubeIndex '' B from
      ⟨poissonConfigurationPoint c p, hp, ((c p.1).2.val p.2).property⟩)

lemma poissonConfigurationMeasure_eq_sum_points {d : ℕ} (c : PoissonConfiguration d) :
    poissonConfigurationMeasure c = Measure.sum (fun p : PoissonPointIndex c =>
      Measure.dirac (poissonConfigurationPoint c p)) := by
  ext B hB
  simp only [poissonConfigurationMeasure, Measure.sum_apply _ hB, poissonCubeCloud_eq_sum_dirac,
    Measure.finsetSum_apply]
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype]
  rfl

/-- Proper maps preserve the represented configuration carrier; no probabilistic argument or
lift to an original sample space enters this exact statement. -/
theorem exists_poissonConfiguration_map {d : ℕ} (c : PoissonConfiguration d)
    {g : Poisson.E d → Poisson.E d} (hg : Measurable g)
    (hb : ∀ B : Set (Poisson.E d), Bornology.IsBounded B → Bornology.IsBounded (g ⁻¹' B)) :
    ∃ c' : PoissonConfiguration d, poissonConfigurationMeasure c' = (poissonConfigurationMeasure c).map g := by
  obtain ⟨c', hc'⟩ := exists_poissonConfiguration_of_points
    (fun p : PoissonPointIndex c => g (poissonConfigurationPoint c p))
    (fun B hB => poissonConfigurationPoint_locallyFinite c (g ⁻¹' B) (hb B hB))
  refine ⟨c', hc'.trans ?_⟩
  rw [poissonConfigurationMeasure_eq_sum_points, Measure.map_sum hg.aemeasurable]
  congr 1
  funext p
  exact (Measure.map_dirac' hg _).symm

end IsotropicVariance.Infra.Instances
