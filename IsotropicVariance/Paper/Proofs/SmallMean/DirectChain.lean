/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.ChainSum
public import IsotropicVariance.Paper.Proofs.SmallMean.FluctArrays
import IsotropicVariance.Paper.Proofs.Profiles.GridGeometry

/-!
# The bound of the mean of `F` from below

The third paragraph of the proof of Lemma `lem:smallmean`, with `b`, any deterministic upper bound
of the density, for `sup ρ`.

* `abs_mean_sub_le`, `mean_ge_direct`: for `r ≥ s`, `E T_r ≥ r` and, by subadditivity,
  `E T_r ≥ E T_s − (r − s)b`; the weights `b/(1 + b)` and `1/(1 + b)` give
  `E T_r ≥ s + (E T_s − s)/(1 + b)`.
* `mean_slabTime_ge_direct`: the same for `E T^{(i)}(u, v)`, since `T^{(i)} ≥ T` and `T(u, v)` has
  the law of `T_{|v − u|}`.
* `slabSum_ge_of_pair_bound`: summing the bound of `T^{(i)}(u, v) − s` at the points `x_{i−1}`,
  `x_i`, in the cubes that contain them.
* `lintegral_sum_fluct_le`: equation `eq:chainsum`, applied to the arrays `X_i/κ`, gives
  `E Σ_i (X_i/κ)(x_{i−1}, x_i) ≤ CM`.
* `chain_mean_ge`: `E F − Ms ≥ M((E T_s − s)/(1 + b) − CκQ_s)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.SmallMean

open Infra.Slab

variable {m : ℕ}

/-! ### The mean at a longer length -/

/-- Subadditivity: `|E T_s − E T_t| ≤ b|s − t|` for a deterministic upper bound `b` of the
density. -/
theorem abs_mean_sub_le (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (s t : ℝ) :
    |X.mean s - X.mean t| ≤ b * |s - t| := by
  obtain ⟨ω₀⟩ : Nonempty X.Ω := nonempty_of_isProbabilityMeasure X.P
  have hb0 : 0 ≤ b := upperBound_nonneg X hb ω₀
  have hs := Infra.TimeConstant.integrable_TRV X s
  have ht := Infra.TimeConstant.integrable_TRV X t
  rw [Setting.mean, Setting.mean, ← integral_sub hs ht]
  calc
    _ ≤ ∫ ω, |X.TRV s ω - X.TRV t ω| ∂X.P := abs_integral_le_integral_abs
    _ ≤ ∫ _ω, b * |s - t| ∂X.P := integral_mono (hs.sub ht).abs (integrable_const _) (fun ω => by
        simpa only [Setting.TRV, dist_self, zero_add, Infra.TimeConstant.dist_smul_e₁] using
          Profiles.abs_passTime_sub_le hb hb0 ω 0 (s • e₁) 0 (t • e₁))
    _ = _ := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- **The mean at a longer length** (proof of Lemma `lem:smallmean`): for `r ≥ s`,
`E T_r ≥ s + (E T_s − s)/(1 + b)`, by averaging `E T_r ≥ r` and `E T_r ≥ E T_s − (r − s)b` with the
weights `b/(1 + b)` and `1/(1 + b)`. -/
theorem mean_ge_direct (X : Setting m) (hX : X.IsNormalized) {b : ℝ} (hb : X.IsUpperBound b)
    {s r : ℝ} (hs : 0 ≤ s) (hr : s ≤ r) : s + (X.mean s - s) / (1 + b) ≤ X.mean r := by
  obtain ⟨ω₀⟩ : Nonempty X.Ω := nonempty_of_isProbabilityMeasure X.P
  have hb0 : 0 ≤ b := upperBound_nonneg X hb ω₀
  have h1 : r ≤ X.mean r := Infra.TimeConstant.mean_ge_of_isNormalized X hX (hs.trans hr)
  have h2 := (abs_le.1 (abs_mean_sub_le X hb r s)).1
  rw [abs_of_nonneg (sub_nonneg.2 hr)] at h2
  have hd : 0 < 1 + b := by positivity
  have h3 : b * r ≤ b * X.mean r := mul_le_mul_of_nonneg_left h1 hb0
  have e : s + (X.mean s - s) / (1 + b) = ((1 + b) * s + (X.mean s - s)) / (1 + b) := by
    field_simp
  rw [e, div_le_iff₀ hd]
  linarith only [h2, h3]

/-- `E T^{(i)}(u, v) ≥ s + (E T_s − s)/(1 + b)` for `u ∈ I_{i−1}(j)`, `v ∈ I_i(k)`
(proof of Lemma `lem:smallmean`): `T^{(i)} ≥ T`, `T(u, v)` has the law of `T_{|v − u|}`, and
`|v − u| ≥ s`. -/
theorem mean_slabTime_ge_direct (hm : 1 ≤ m) (X : Setting m) (hX : X.IsNormalized) {b : ℝ}
    (hb : X.IsUpperBound b) {s W : ℝ} (hs : 0 ≤ s) {i : ℕ} {j k : Fin m → ℤ} {u v : Pt m}
    (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k)
    (hDT : ∀ ω, X.passTime ω u v ≤ X.slabTime b (chainSlab s 0 i) ω u v) :
    s + (X.mean s - s) / (1 + b) ≤ ∫ ω, X.slabTime b (chainSlab s 0 i) ω u v ∂X.P := by
  have h1 : X.mean (dist u v) ≤ ∫ ω, X.slabTime b (chainSlab s 0 i) ω u v ∂X.P := by
    rw [← integral_passTime_eq_mean hm X u v]
    exact integral_mono (Infra.TimeConstant.integrable_passTime X u v)
      (integrable_slabTime_of_mem X hb _ (gridCube_subset_set hs W i j hu)
        (gridCube_succ_subset_set hs W i k hv)) hDT
  exact (mean_ge_direct X hX hb hs (le_dist_gridCube hs hu hv)).trans h1

/-! ### Summing at the points `x_i` -/

variable (X : Setting.{u} m) {b : ℝ}

/-- **Summing the bound of `T^{(i)} − s`** at the points `x_i` (proof of Lemma `lem:smallmean`):
if every pair of cubes with `W|k − j| ≤ s/2` has `D_i(u, v) − s ≥ a − Qζ_i(j, k)`, then
`F ≥ Ms + Ma − Q Σ_i ζ_i(k_{i−1}, k_i)`. -/
theorem slabSum_ge_of_pair_bound (hb : X.IsUpperBound b) {M : ℕ} {s W Q a : ℝ} (hs : 0 < s)
    (hW : 0 < W) (hWs : W * Real.sqrt m ≤ s / 4) (ω : X.Ω)
    (ζ : Fin M → (Fin m → ℤ) → (Fin m → ℤ) → ℝ)
    (hdisp : ∀ (i : Fin M) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
      ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 ((i : ℕ) + 1) k,
        a - Q * ζ i j k ≤ (chainSlab s 0 i).passTime b (X.ρ ω) u v - s) :
    (M : ℝ) * s + M * a - Q * ∑ i : Fin M,
        ζ i (X.J b M s W 0 ω i.castSucc) (X.J b M s W 0 ω i.succ) ≤
      X.F b M s 0 ω := by
  have hchain := X.isValidChain ω hs.le
  set x := lexMinimizer b (X.ρ ω) M s 0 with hx
  have hWm : 4 * Real.sqrt m * W ≤ s := by linarith only [hWs]
  have hterm : ∀ i : Fin M, s + a - Q * ζ i (X.J b M s W 0 ω i.castSucc)
      (X.J b M s W 0 ω i.succ) ≤
        (chainSlab s 0 i).passTime b (X.ρ ω) (x i.castSucc) (x i.succ) := by
    intro i
    have h1 := Profiles.J_step X hb hs hW hWm ω i
    have h2 : x i.castSucc ∈ gridCube s W 0 i (X.J b M s W 0 ω i.castSucc) :=
      lexMinimizer_mem_gridCube b hchain M hW 0 i.castSucc
    have h3 : x i.succ ∈ gridCube s W 0 ((i : ℕ) + 1) (X.J b M s W 0 ω i.succ) :=
      lexMinimizer_mem_gridCube b hchain M hW 0 i.succ
    have := hdisp i _ _ h1 _ h2 _ h3
    linarith only [this]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [show X.F b M s 0 ω = slabSum b (X.ρ ω) M s 0 x from
    (isLexLeastMinimizer_lexMinimizer b hchain M 0).2.1.symm]
  unfold slabSum
  refine le_trans (le_of_eq ?_) hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]

/-! ### Integrating -/

/-- **`E Σ_i (X_i/κ)(x_{i−1}, x_i) ≤ CM`** (proof of Lemma `lem:smallmean`): equation
`eq:chainsum` for real arrays `Z_i`, independent over `i`, with `E[Z_i(j, k)^{4d}] ≤ 1`. -/
theorem lintegral_sum_fluct_le {M : ℕ} {s W C : ℝ} (hC : Profiles.ChainSumBound X b M s W C)
    (Z : Fin M → X.Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ)
    (hZm : ∀ i j k, Measurable fun ω => Z i ω j k) (hZ0 : ∀ i ω j k, 0 ≤ Z i ω j k)
    (hZind : iIndepFun Z X.P)
    (hZmom : ∀ i j k, ∫⁻ ω, ENNReal.ofReal (Z i ω j k ^ (4 * (m + 1))) ∂X.P ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin M, Z i ω (X.J b M s W 0 ω i.castSucc)
        (X.J b M s W 0 ω i.succ)) ∂X.P ≤
      ENNReal.ofReal (C * M) := by
  have hg : Measurable fun r : (Fin m → ℤ) → (Fin m → ℤ) → ℝ =>
      fun j k => ENNReal.ofReal (r j k) :=
    Measurable.of_eval fun j => Measurable.of_eval fun k =>
      ((measurable_pi_apply j).eval (a := k)).ennreal_ofReal
  refine le_trans (le_of_eq (lintegral_congr fun ω => ?_))
    (hC X.Ω X.P id (MeasurePreserving.id X.P) (fun i ω j k => ENNReal.ofReal (Z i ω j k))
      (fun i j k => (hZm i j k).ennreal_ofReal)
      (hZind.comp (fun _ r j k => ENNReal.ofReal (r j k)) fun _ => hg)
      fun i j k => (lintegral_mono fun ω => ?_).trans (hZmom i j k))
  · exact ENNReal.ofReal_sum_of_nonneg fun i _ => hZ0 i ω _ _
  · rw [ENNReal.ofReal_pow (hZ0 i ω j k)]
    exact pow_le_pow_left₀ bot_le tsub_le_self _

/-- **The mean of `F` from below** (proof of Lemma `lem:smallmean`): the bound of
`T^{(i)}(u, v) − s` at the points `x_i` and `E Σ_i X_i(x_{i−1}, x_i) ≤ κ C M` give
`E F − Ms ≥ M (E T_s − s)/(1 + b) − Q κ C M`. -/
theorem chain_mean_ge (hm : 1 ≤ m) (hX : X.IsNormalized) (hb : X.IsUpperBound b) {M : ℕ}
    {s W Q κ B : ℝ} (hs : 0 < s) (hW : 0 < W) (hQ : 0 < Q) (hκ : 0 < κ) (hB : 0 ≤ B)
    (hWs : W * Real.sqrt m ≤ s / 4) (Z : Fin M → X.Ω → (Fin m → ℤ) → (Fin m → ℤ) → ℝ)
    (hlow : ∀ (i : Fin M) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
      ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 ((i : ℕ) + 1) k, ∀ ω,
        X.passTime ω u v ≤ X.slabTime b (chainSlab s 0 i) ω u v)
    (hZ : ∀ᵐ ω ∂X.P, ∀ (i : Fin M) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
      ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 ((i : ℕ) + 1) k,
        |X.slabTime b (chainSlab s 0 i) ω u v -
          ∫ ω', X.slabTime b (chainSlab s 0 i) ω' u v ∂X.P| ≤ Q * (κ * Z i ω j k))
    (hsum : ∫⁻ ω, ENNReal.ofReal (∑ i : Fin M, Z i ω (X.J b M s W 0 ω i.castSucc)
        (X.J b M s W 0 ω i.succ)) ∂X.P ≤ ENNReal.ofReal B)
    (hF : Integrable (X.F b M s 0) X.P) :
    (M : ℝ) * s + M * ((X.mean s - s) / (1 + b)) ≤
      ∫ ω, X.F b M s 0 ω ∂X.P + Q * κ * B := by
  set a : ℝ := (X.mean s - s) / (1 + b) with ha
  have hQκ : 0 ≤ Q * κ := by positivity
  have hmin : ∀ ω, IsLexLeastMinimizer b (X.ρ ω) M s 0 (lexMinimizer b (X.ρ ω) M s 0) := fun ω =>
    isLexLeastMinimizer_lexMinimizer b (X.isValidChain ω hs.le) M 0
  have hF0 : ∀ ω, 0 ≤ X.F b M s 0 ω := fun ω => by
    have h := slabSum_nonneg b (X.ρ ω) M s 0 (lexMinimizer b (X.ρ ω) M s 0)
    rwa [(hmin ω).2.1] at h
  have hgood : ∀ᵐ ω ∂X.P, ENNReal.ofReal ((M : ℝ) * s + M * a) ≤
      ENNReal.ofReal (X.F b M s 0 ω) + ENNReal.ofReal (Q * κ) *
        ENNReal.ofReal (∑ i : Fin M, Z i ω (X.J b M s W 0 ω i.castSucc)
          (X.J b M s W 0 ω i.succ)) := by
    filter_upwards [hZ] with ω hω
    have hdisp : ∀ (i : Fin M) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 →
        ∀ u ∈ gridCube s W 0 i j, ∀ v ∈ gridCube s W 0 ((i : ℕ) + 1) k,
          a - Q * (κ * Z i ω j k) ≤ (chainSlab s 0 i).passTime b (X.ρ ω) u v - s := by
      intro i j k hc u hu v hv
      have h1 := (abs_le.1 (hω i j k hc u hu v hv)).1
      have h2 := mean_slabTime_ge_direct hm X hX hb hs.le hu hv
        (fun ω' => hlow i j k hc u hu v hv ω')
      change _ ≤ X.slabTime b (chainSlab s 0 i) ω u v - s
      linarith only [h1, h2]
    have hbound := slabSum_ge_of_pair_bound X hb hs hW hWs ω (fun i j k => κ * Z i ω j k) hdisp
    have heq : Q * ∑ i : Fin M, κ * Z i ω (X.J b M s W 0 ω i.castSucc) (X.J b M s W 0 ω i.succ) =
        Q * κ * ∑ i : Fin M, Z i ω (X.J b M s W 0 ω i.castSucc) (X.J b M s W 0 ω i.succ) := by
      rw [← Finset.mul_sum, mul_assoc]
    rw [heq] at hbound
    rw [← ENNReal.ofReal_mul hQκ]
    exact (ENNReal.ofReal_le_ofReal (by linarith only [hbound])).trans ENNReal.ofReal_add_le
  have hfinal := le_integral_add_of_ae (c := Q * κ) (C := 0) (B₂ := 0) (B₃ := B)
    (S := fun _ => 0) (T := X.F b M s 0) hQκ le_rfl le_rfl hB hgood
    (fun ω => by simp) hF hF0 aemeasurable_const (by simp) hsum
  linarith only [hfinal]

end IsotropicVariance.Paper.Proofs.SmallMean
