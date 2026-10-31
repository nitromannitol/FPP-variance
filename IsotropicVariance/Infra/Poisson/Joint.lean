/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Poisson.Construction
public import IsotropicVariance.Infra.Poisson.Generating
import Mathlib.Probability.Independence.Integration

/-!
# Joint counts of the cube-cloud construction

Independence across cubes combines with splitting within each cube.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Complex
open scoped NNReal ENNReal BigOperators

namespace IsotropicVariance.Infra.Poisson

/-- The joint generating function on a finite cube family factors over cubes and regions. -/
theorem integral_prod_pow_finiteCubeCount {d k : ℕ} (lam : ℝ≥0)
    (F : Finset (Fin d → ℤ)) (B : Fin k → Set (E d))
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ w : ProcessSample d, ∏ i, z i ^ finiteCubeCount F (B i) w ∂processLaw d lam) =
      ∏ c ∈ F, ∏ i, Complex.exp ((lam : ℂ) * (volume (B i ∩ cube c)).toReal * (z i - 1)) := by
  classical
  let f (c : Fin d → ℤ) (v : CloudSample (cube c)) : ℂ :=
    ∏ i, z i ^ cloudCount (Subtype.val ⁻¹' B i) v
  have hfm (c : Fin d → ℤ) : Measurable (f c) := by
    apply Finset.measurable_prod
    intro i _
    exact Measurable.of_discrete.comp (measurable_cloudCount ((hB i).preimage measurable_subtype_coe))
  have hind : iIndepFun (fun c (w : ProcessSample d) => f c (w c)) (processLaw d lam) :=
    iIndepFun_infinitePi hfm
  have hprod (w : ProcessSample d) :
      (∏ i, z i ^ finiteCubeCount F (B i) w) = ∏ c : F, f c (w c) := by
    rw [Finset.prod_coe_sort F (fun c => f c (w c))]
    simp only [finiteCubeCount, ← Finset.prod_pow_eq_pow_sum, f]
    exact Finset.prod_comm
  have hindF : iIndepFun (fun c : F => fun w : ProcessSample d => f c (w c))
      (processLaw d lam) := hind.precomp Subtype.val_injective
  simp_rw [hprod]
  rw [hindF.integral_fun_prod_eq_prod_integral
    (fun c => ((hfm c).comp (measurable_pi_apply c.val)).aestronglyMeasurable)]
  rw [Finset.prod_coe_sort F (fun c => ∫ w : ProcessSample d, f c (w c) ∂processLaw d lam)]
  apply Finset.prod_congr rfl
  intro c _
  have hLaw : HasLaw (fun w : ProcessSample d => w c) (cloudLaw lam (cubeUniform c))
      (processLaw d lam) := by
    simpa only [processLaw, Function.eval] using
      (measurePreserving_eval_infinitePi (fun c => cloudLaw lam (cubeUniform c)) c).hasLaw
  have heq := hLaw.integral_comp (hfm c).aestronglyMeasurable
  simp only [Function.comp_def] at heq
  rw [heq]
  change (∫ v : CloudSample (cube c), ∏ i, z i ^ cloudCount (Subtype.val ⁻¹' B i) v ∂cloudLaw lam (cubeUniform c)) = _
  rw [integral_prod_pow_cloudCount (cubeUniform c) lam
    (fun i => Subtype.val ⁻¹' B i) (fun i => (hB i).preimage measurable_subtype_coe)
    (fun i j hij => (hd hij).preimage Subtype.val) z hz]
  simp only [measureReal_def, cubeUniform_preimage c (hB _)]

/-- Once the cube family covers the regions, the generating function has the physical rates. -/
theorem integral_prod_pow_finiteCubeCount_of_cover {d k : ℕ} (lam : ℝ≥0)
    (F : Finset (Fin d → ℤ)) (B : Fin k → Set (E d))
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hF : ∀ i, cubeIndex '' B i ⊆ (F : Set (Fin d → ℤ)))
    (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ w : ProcessSample d, ∏ i, z i ^ finiteCubeCount F (B i) w ∂processLaw d lam) =
      ∏ i, Complex.exp ((lam : ℂ) * (volume (B i)).toReal * (z i - 1)) := by
  rw [integral_prod_pow_finiteCubeCount lam F B hB hd z hz, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Complex.exp_sum]
  congr 1
  have hfin (c : Fin d → ℤ) (_hc : c ∈ F) : volume (B i ∩ cube c) ≠ ⊤ := by
    apply ne_of_lt
    calc volume (B i ∩ cube c) ≤ volume (cube c) := measure_mono inter_subset_right
         _ < ⊤ := by rw [volume_cube]; exact ENNReal.one_lt_top
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Complex.ofReal_sum,
    ← ENNReal.toReal_sum hfin, sum_volume_inter_cube F (hB i) (hF i)]

/-- Joint finite-cube natural counts have the physical product Poisson law. -/
theorem hasLaw_finiteCubeCounts_of_cover {d k : ℕ} (lam : ℝ≥0)
    (F : Finset (Fin d → ℤ)) (B : Fin k → Set (E d))
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hF : ∀ i, cubeIndex '' B i ⊆ (F : Set (Fin d → ℤ))) :
    HasLaw (fun w => fun i => finiteCubeCount F (B i) w)
      (Measure.pi (fun i => poissonMeasure (lam * (volume (B i)).toNNReal)))
      (processLaw d lam) := by
  apply hasLaw_counts_of_generating (processLaw d lam)
    (fun i => finiteCubeCount F (B i)) (fun i => measurable_finiteCubeCount F (hB i))
  intro z hz
  simpa only [NNReal.coe_mul, Complex.ofReal_mul, ENNReal.toReal, mul_assoc] using
    integral_prod_pow_finiteCubeCount_of_cover lam F B hB hd hF z hz

/-- Disjoint bounded Borel regions have independent counts in the construction. -/
theorem iIndepFun_process_counts {d k : ℕ} (lam : ℝ≥0) (B : Fin k → Set (E d))
    (hB : ∀ i, MeasurableSet (B i)) (hb : ∀ i, Bornology.IsBounded (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    iIndepFun (fun i (w : ProcessSample d) => process w (B i)) (processLaw d lam) := by
  classical
  let F : Finset (Fin d → ℤ) := Finset.univ.biUnion
    (fun i => (finite_cubeIndex_image (hb i)).toFinset)
  have hF (i : Fin k) : cubeIndex '' B i ⊆ (F : Set (Fin d → ℤ)) := by
    intro c hc
    change c ∈ F
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ i, (finite_cubeIndex_image (hb i)).mem_toFinset.mpr hc⟩
  have hi := iIndepFun_of_hasLaw_pi_nat (processLaw d lam)
    (fun i => finiteCubeCount F (B i)) (fun i => measurable_finiteCubeCount F (hB i))
    (fun i => lam * (volume (B i)).toNNReal)
    (hasLaw_finiteCubeCounts_of_cover lam F B hB hd hF)
  have heq : (fun i (w : ProcessSample d) => process w (B i)) =
      (fun i => (Nat.cast : ℕ → ℝ≥0∞) ∘ finiteCubeCount F (B i)) := by
    funext i w
    exact process_apply_eq_finiteCubeCount F (hB i) (hF i) w
  rw [heq]
  exact hi.comp (fun _ => Nat.cast) (fun _ => Measurable.of_discrete)

/-- The explicit independent-cube construction is a homogeneous Poisson process. -/
theorem isPoissonProcess_process (d : ℕ) (lam : ℝ≥0) :
    IsPoissonProcess lam (process : ProcessSample d → Measure (E d)) (processLaw d lam) := by
  refine ⟨measurable_process, process_counting, ?_, ?_⟩
  · intro B hB hb
    exact hasLaw_process_count lam hB hb
  · intro k B hB hb hd
    exact iIndepFun_process_counts lam B hB hb hd

/-- A standard Borel probability realization at every intensity and in every dimension. -/
theorem exists_standardBorel (d : ℕ) (lam : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ η : Ω → Measure (E d), IsPoissonProcess lam η P := by
  exact ⟨ProcessSample d, inferInstance, inferInstance, processLaw d lam, inferInstance,
    process, isPoissonProcess_process d lam⟩

end IsotropicVariance.Infra.Poisson
