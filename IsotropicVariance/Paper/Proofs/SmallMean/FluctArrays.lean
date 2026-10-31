/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.SlabPairs

/-!
# The arrays `X_i` of the proof of Lemma `lem:smallmean`

The first two paragraphs of the proof of Lemma `lem:smallmean`. The array `X_i(j, k)` is the
normalized supremum over the pair of cubes `I_{i−1}(j)`, `I_i(k)` of
`|T^{(i)}(u, v) − E T^{(i)}(u, v)|` when `(sQ_s)^{1/2}|k − j| ≤ s/2`, and zero otherwise. In Lean
the supremum is taken along a dense sequence of the pair, for the continuous versions of the slab
passage times (`Infra.Slab.exists_iIndep_slabTime_versions`), so that the arrays are measurable and
independent over `i`.

* `lintegral_inv_mul_pow_le_one`: a moment bound of `X_i(j, k)` by `κ` is the moment bound of
  `X_i(j, k)/κ` by one.
* `exists_fluct_arrays`: from `E[(X_i(j, k)/κ)^{4d}] ≤ 1`, the arrays `X_i/κ`, independent over `i`,
  and the bound of `|T^{(i)} − E T^{(i)}|` by `Q X_i` on one full-measure event.

The indices are 0-based, as in `IsotropicVariance.Paper.Defs.Minimum`: the slab `i : Fin M` joins
`I_i` and `I_{i+1}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.SmallMean

open Infra.Slab

variable {m : ℕ}

/-- The moment bound of `lintegral_fluct_pow_le_of_pair`, for `f/κ`. -/
theorem lintegral_inv_mul_pow_le_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    {p : ℕ} {κ A η : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hf : ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂P ≤ ENNReal.ofReal (3 ^ (p - 1)) *
      (ENNReal.ofReal A + ENNReal.ofReal (η ^ p) + ENNReal.ofReal (η ^ p)))
    (hconst : κ⁻¹ ^ p * (3 ^ (p - 1) * (A + η ^ p + η ^ p)) ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal ((κ⁻¹ * f ω) ^ p) ∂P ≤ 1 := by
  have heq : ∀ ω, ENNReal.ofReal ((κ⁻¹ * f ω) ^ p) =
      ENNReal.ofReal (κ⁻¹ ^ p) * ENNReal.ofReal (f ω ^ p) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity), mul_pow]
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (κ⁻¹ ^ p) * ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂P
      ≤ ENNReal.ofReal (κ⁻¹ ^ p) * (ENNReal.ofReal (3 ^ (p - 1)) *
          (ENNReal.ofReal A + ENNReal.ofReal (η ^ p) + ENNReal.ofReal (η ^ p))) := by gcongr
    _ = ENNReal.ofReal (κ⁻¹ ^ p * (3 ^ (p - 1) * (A + η ^ p + η ^ p))) := by
        rw [← ENNReal.ofReal_add hA (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hconst

/-- **The arrays of the proof of Lemma `lem:smallmean`**. Given the
moment bound `E[(X_i/κ)^{4d}] ≤ 1` for the fluctuation along any dense sequence of any measurable
version, there are arrays `Z = X_i/κ`, measurable, nonnegative and independent over `i`, with
`E[Z_i(j, k)^{4d}] ≤ 1` at every pair and, on one full-measure event,
`|T^{(i)}(u, v) − E T^{(i)}(u, v)| ≤ Q κ Z_i(j, k)` at the points of every pair of cubes with
`W|k − j| ≤ s/2`. -/
theorem exists_fluct_arrays (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {s W Q κ : ℝ}
    (hs : 0 < s) (hW : 0 ≤ W) (hQ : 0 < Q) (hκ : 0 < κ) (M : ℕ)
    (hmom : ∀ (i : ℕ) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
      ∀ V : X.Ω → Pt m × Pt m → ℝ, Measurable (Function.uncurry V) →
      (∀ᵐ ω ∂X.P, ∀ u ∈ (chainSlab s 0 i).set, ∀ v ∈ (chainSlab s 0 i).set,
        V ω (u, v) = X.slabTime b (chainSlab s 0 i) ω u v) →
      ∀ q : ℕ → Pt m × Pt m, (∀ n, q n ∈ gridCube s W 0 i j ×ˢ gridCube s W 0 (i + 1) k) →
      ∫⁻ ω, ENNReal.ofReal ((κ⁻¹ * fluct (V ω)
        (fun x => ∫ ω', X.slabTime b (chainSlab s 0 i) ω' x.1 x.2 ∂X.P) q Q) ^ (4 * (m + 1)))
          ∂X.P ≤ 1) :
    ∃ Z : Fin M → X.Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ,
      (∀ i j k, Measurable fun ω => Z i ω j k) ∧ (∀ i ω j k, 0 ≤ Z i ω j k) ∧ iIndepFun Z X.P ∧
      (∀ i j k, ∫⁻ ω, ENNReal.ofReal (Z i ω j k ^ (4 * (m + 1))) ∂X.P ≤ 1) ∧
      ∀ᵐ ω ∂X.P, ∀ (i : Fin M) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
        ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 ((i : ℕ) + 1) k,
          |X.slabTime b (chainSlab s 0 i) ω u v -
            ∫ ω', X.slabTime b (chainSlab s 0 i) ω' u v ∂X.P| ≤ Q * (κ * Z i ω j k) := by
  classical
  set p : ℕ := 4 * (m + 1) with hpdef
  -- the slabs and their versions
  set sl : Fin M → Slab m := fun i => chainSlab s 0 i with hsl
  have hdisj : Pairwise (Function.onFun Disjoint fun i => interior (sl i).set) := by
    intro i i' hii'
    exact disjoint_interior_chainSlab hs (fun h => hii' (Fin.ext h))
  obtain ⟨V, hVm, hVc, hVind, hVae⟩ := exists_iIndep_slabTime_versions X hb sl hdisj
  -- the means and the dense sequences
  set e : Fin M → Pt m × Pt m → ℝ := fun i x => ∫ ω, X.slabTime b (sl i) ω x.1 x.2 ∂X.P with hedef
  have hpairne : ∀ (i : ℕ) (j k : Fin m → ℤ),
      (gridCube s W 0 i j ×ˢ gridCube s W 0 (i + 1) k).Nonempty := fun i j k =>
    (gridCube_nonempty s hW i j).prod (gridCube_nonempty s hW (i + 1) k)
  choose q hqmem hqdense using fun (i : ℕ) (j k : Fin m → ℤ) => exists_dense_seq_in (hpairne i j k)
  -- the arrays
  set g : Fin M → (Pt m × Pt m → ℝ) → (Fin m → ℤ) → (Fin m → ℤ) → ℝ := fun i F j k =>
    if W * zNorm (k - j) ≤ s / 2 then κ⁻¹ * fluct F (e i) (q i j k) Q else 0 with hgdef
  set Z : Fin M → X.Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ := fun i ω => g i (V i ω) with hZdef
  have hg : ∀ i j k, Measurable fun F => g i F j k := by
    intro i j k
    by_cases hc : W * zNorm (k - j) ≤ s / 2
    · simp only [hgdef, hc, ite_true]
      exact (measurable_fluct _ _ _).const_mul _
    · simp only [hgdef, hc, ite_false]
      exact measurable_const
  have hVi : ∀ i, Measurable (V i) := fun i =>
    measurable_pi_iff.2 fun x => (hVm i).comp (measurable_id.prodMk measurable_const)
  have hZm : ∀ i j k, Measurable fun ω => Z i ω j k := fun i j k => (hg i j k).comp (hVi i)
  have hZind : iIndepFun Z X.P := iIndepFun_fluct_arrays hVind g hg
  have hZ0 : ∀ i ω j k, 0 ≤ Z i ω j k := by
    intro i ω j k
    simp only [hZdef, hgdef]
    split_ifs
    · exact mul_nonneg (by positivity) (fluct_nonneg _ _ _ hQ.le)
    · exact le_rfl
  -- the moments of the arrays
  have hZmom : ∀ i j k, ∫⁻ ω, ENNReal.ofReal (Z i ω j k ^ p) ∂X.P ≤ 1 := by
    intro i j k
    by_cases hc : W * zNorm (k - j) ≤ s / 2
    · have heq : ∀ ω, Z i ω j k = κ⁻¹ * fluct (V i ω) (e i) (q i j k) Q := fun ω => by
        simp only [hZdef, hgdef, hc, ite_true]
      simp_rw [heq]
      exact hmom i j k hc (V i) (hVm i) (hVae.mono fun ω hω => hω i) (q i j k) (hqmem i j k)
    · have h0 : ∀ ω, Z i ω j k = 0 := fun ω => by simp only [hZdef, hgdef, hc, ite_false]
      simp only [h0]
      have hp0 : p ≠ 0 := by omega
      simp [zero_pow hp0]
  refine ⟨Z, hZm, hZ0, hZind, hZmom, ?_⟩
  -- the fluctuation bounds the field on the full-measure event of the versions
  filter_upwards [hVae] with ω hω i j k hc u hu v hv
  have hsub : gridCube s W 0 i j ×ˢ gridCube s W 0 ((i : ℕ) + 1) k ⊆
      (chainSlab s 0 i).set ×ˢ (chainSlab s 0 i).set :=
    prod_mono (gridCube_subset_set hs.le W i j) (gridCube_succ_subset_set hs.le W i k)
  have hcpt : IsCompact (gridCube s W 0 i j ×ˢ gridCube s W 0 ((i : ℕ) + 1) k) :=
    (isCompact_gridCube s W i j).prod (isCompact_gridCube s W (i + 1) k)
  have habs := abs_sub_le_mul_fluct hcpt (hVc i ω) ((continuousOn_mean_slabTime X hb _).mono hsub)
    (hqmem i j k) (hqdense i j k) hQ (x := (u, v)) ⟨hu, hv⟩
  have hVD := hω i u (gridCube_subset_set hs.le W i j hu) v
    (gridCube_succ_subset_set hs.le W i k hv)
  have hZval : Z i ω j k = κ⁻¹ * fluct (V i ω) (e i) (q i j k) Q := by
    simp only [hZdef, hgdef, hc, ite_true]
  have hκZ : κ * Z i ω j k = fluct (V i ω) (e i) (q i j k) Q := by
    rw [hZval, ← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul]
  rw [hκZ, ← hVD]
  exact habs

end IsotropicVariance.Paper.Proofs.SmallMean
