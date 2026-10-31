/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Gain
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Contracts.Responses
public import CurvatureVariance.Paper.Proofs.Gain.Basic
public import CurvatureVariance.Paper.Proofs.Responses.Basic
public import CurvatureVariance.Infra.FPP.Translation
public import CurvatureVariance.Infra.FPP.Model
public import CurvatureVariance.Infra.FPP.Lattice
public import CurvatureVariance.Infra.FPP.Walks
public import CurvatureVariance.Infra.Os.Moments
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.InnerProductSpace.Dual
import CurvatureVariance.Paper.Proofs.Geometry.SupportAngular
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.ShortLengths.Translate
import CurvatureVariance.Paper.Proofs.Gain.AVEnergy
import CurvatureVariance.Paper.Proofs.Gain.Common
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds

/-!
# Removing the average: the comparison of `F̄` with the passage time

The comparison of `F̄` with the passage time in the proof of Proposition `prop:gain`. For `F̄`, the
average of the minima `F_v` translated by `τ_v = vLwe₂` (`0 ≤ v < V = ⌈K^{2/3}⌉`), and the target
passage time `T = T(0,(ℓ,y))`: `F̄ − T = V⁻¹ ∑_v (F_v − T_v) + V⁻¹ ∑_v (T_v − T)`,
`T_v = T(τ_v, (ℓ,y) + τ_v)`, so `‖F̄ − T‖₂ ≤ sup_v ‖F_v − T_v‖₂ + sup_v ‖T_v − T‖₂`
(`eLpNorm_averagedMin_sub_le`).
* `‖F_v − T_v‖₂ = ‖F − T‖₂` by translation invariance (`eLpNorm_translatedMin_sub`), and equation
  `eq:fixedcomparison` (`Contracts.FixedComparisonStatement`) bounds it by `η Q_n ≤ η Q_ℓ`.
* `T_v − T` compares two passage times whose endpoints differ by the same vector `τ_v`; both
  endpoint pairs lie in one pair of transverse cubes at distance `ℓ` of side
  `a = (V − 1)Lw ≤ 2L K^{−1/12+δ/(2K)} W_ℓ` (`isCubePair_tau`). For `K` large, equation
  `eq:modulus` (`Contracts.ModulusStatement`) makes `‖T_v − T‖₂` at most `η Q_ℓ` (the linear term
  vanishes).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology InnerProductSpace

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### The translations and the averaging -/

/-- The translation `τ_v = vLwe₂`, `w = ⌈W_n⌉`, of the minima `F_m` (the text before Lemma
`lem:residual`). -/
noncomputable def tau (M : Model m) (K : ℕ) (A : ℝ) (L n v : ℕ) : Fin m → ℤ :=
  ((v * L * wInt M K A n : ℕ) : ℤ) • transverseUnit m

/-- `‖F_τ − T(τ, (ℓ,y) + τ)‖₂ = ‖F − T(0,(ℓ,y))‖₂`, by translation invariance. -/
theorem eLpNorm_translatedMin_sub {M : Model m} (hM : M.Standing) (n K ℓ : ℕ)
    (y τ : Fin m → ℤ) :
    eLpNorm (fun ω => translatedMin M ω n K ℓ y τ -
        passageTimeReal ω ((0 : ℤ), τ) ((ℓ : ℤ), y + τ)) 2 M.P =
      eLpNorm (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P := by
  have hcomp : (fun ω => translatedMin M ω n K ℓ y τ -
      passageTimeReal ω ((0 : ℤ), τ) ((ℓ : ℤ), y + τ)) =
      (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) ∘
        translate ((0 : ℤ), τ) := by
    funext ω
    simp only [Function.comp, Gain.translatedMin_eq_targetMin, passageTimeReal,
      passageTime_translate, zero_add, Prod.mk_add_mk, add_zero]
  have hmeas : AEStronglyMeasurable
      (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) M.P :=
    ((Responses.measurable_targetMin M n K ℓ y).sub
      (measurable_passageTime_real 0 ((ℓ : ℤ), y))).aestronglyMeasurable
  rw [hcomp]
  exact eLpNorm_comp_measurePreserving hmeas (Moments.standing_measurePreserving_translate hM _)

/-- **The averaging**: `‖F̄ − T‖₂ ≤ a + b` if `‖F − T‖₂ ≤ a` and `‖T_v − T‖₂ ≤ b` for every
`v < V`. -/
theorem eLpNorm_averagedMin_sub_le {M : Model m} (hM : M.Standing) (K : ℕ) (A : ℝ)
    (L n ℓ : ℕ) (y : Fin m → ℤ) (hV : 0 < numTranslates K) {a b : ℝ≥0∞}
    (ha : eLpNorm (fun ω => targetMin M ω n K ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P ≤ a)
    (hb : ∀ v < numTranslates K, eLpNorm (fun ω =>
      passageTimeReal ω ((0 : ℤ), tau M K A L n v) ((ℓ : ℤ), y + tau M K A L n v) -
        passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P ≤ b) :
    eLpNorm (fun ω => averagedMin M K A L ω n ℓ y - passageTimeReal ω 0 ((ℓ : ℤ), y)) 2 M.P ≤
      a + b := by
  set V := numTranslates K with hVdef
  set T : Config m → ℝ := fun ω => passageTimeReal ω 0 ((ℓ : ℤ), y) with hT
  set g : ℕ → Config m → ℝ :=
    fun v ω => translatedMin M ω n K ℓ y (tau M K A L n v) - T ω with hg
  have hVne : (V : ℝ) ≠ 0 := by exact_mod_cast hV.ne'
  have hfun : (fun ω => averagedMin M K A L ω n ℓ y - T ω) =
      (V : ℝ)⁻¹ • ∑ v ∈ Finset.range V, g v := by
    funext ω
    simp only [averagedMin, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hg,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, tau]
    rw [← hVdef, mul_sub, ← mul_assoc, inv_mul_cancel₀ hVne, one_mul]
  have hgv : ∀ v < V, eLpNorm (g v) 2 M.P ≤ a + b := by
    intro v hv
    have hsplit : g v = (fun ω => translatedMin M ω n K ℓ y (tau M K A L n v) -
        passageTimeReal ω ((0 : ℤ), tau M K A L n v) ((ℓ : ℤ), y + tau M K A L n v)) +
        (fun ω => passageTimeReal ω ((0 : ℤ), tau M K A L n v)
          ((ℓ : ℤ), y + tau M K A L n v) - T ω) := by
      funext ω; simp [hg]
    rw [hsplit]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ (hb v hv))
    rw [eLpNorm_translatedMin_sub hM]
    exact ha
  rw [hfun, eLpNorm_const_smul]
  have hsum : eLpNorm (∑ v ∈ Finset.range V, g v) 2 M.P ≤ (V : ℝ≥0∞) * (a + b) := by
    refine (eLpNorm_sum_le (by norm_num)).trans ?_
    calc ∑ v ∈ Finset.range V, eLpNorm (g v) 2 M.P ≤ ∑ _v ∈ Finset.range V, (a + b) :=
          Finset.sum_le_sum fun v hv => hgv v (Finset.mem_range.1 hv)
      _ = (V : ℝ≥0∞) * (a + b) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hinv : ‖(V : ℝ)⁻¹‖ₑ = (V : ℝ≥0∞)⁻¹ := by
    rw [enorm_inv (by exact_mod_cast hV.ne'), Real.enorm_natCast]
  rw [hinv]
  calc (V : ℝ≥0∞)⁻¹ * eLpNorm (∑ v ∈ Finset.range V, g v) 2 M.P ≤
        (V : ℝ≥0∞)⁻¹ * ((V : ℝ≥0∞) * (a + b)) := by gcongr
    _ = a + b := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hV.ne') (by simp), one_mul]

/-! ### Geometry of the translations -/

theorem transversePoint_zsmul (k : ℤ) (y : Fin m → ℤ) :
    transversePoint (k • y) = (k : ℝ) • transversePoint y := by
  ext j; simp [transversePoint]

theorem transverseUnit_eq_single (hm : 1 ≤ m) :
    transverseUnit m = Pi.single (⟨0, hm⟩ : Fin m) 1 := by
  funext k
  simp only [transverseUnit, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => Fin.ext h, fun h => by rw [h]⟩

theorem norm_transversePoint_tau {M : Model m} (hm : 1 ≤ m) (K : ℕ) (A : ℝ) (L n v : ℕ) :
    ‖transversePoint (tau M K A L n v)‖ = ((v * L * wInt M K A n : ℕ) : ℝ) := by
  rw [tau, transversePoint_zsmul, transverseUnit_eq_single hm, transversePoint_single, norm_smul,
    PiLp.norm_single, norm_one, mul_one, Int.cast_natCast, Real.norm_natCast]

/-- `‖point (0, τ_v)‖ = vLw`. -/
theorem norm_point_tau {M : Model m} (hm : 1 ≤ m) (K : ℕ) (A : ℝ) (L n v : ℕ) :
    ‖point (((0 : ℤ), tau M K A L n v) : Vertex m)‖ = ((v * L * wInt M K A n : ℕ) : ℝ) := by
  have h := norm_point_sq (((0 : ℤ), tau M K A L n v) : Vertex m)
  rw [norm_transversePoint_tau hm] at h
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add] at h
  have h0 : 0 ≤ ‖point (((0 : ℤ), tau M K A L n v) : Vertex m)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖point (((0 : ℤ), tau M K A L n v) : Vertex m)‖ -
    ((v * L * wInt M K A n : ℕ) : ℝ)), Nat.cast_nonneg (α := ℝ) (v * L * wInt M K A n)]

/-- The centre `c = (a/2) e₂` of the transverse cube containing the translations. -/
noncomputable def centre (a : ℝ) : EuclideanSpace ℝ (Fin m) :=
  (a / 2) • transversePoint (transverseUnit m)

theorem centre_apply (a : ℝ) (j : Fin m) :
    centre (m := m) a j = a / 2 * (transverseUnit m j : ℝ) := by
  simp [centre, transversePoint]

/-- The side `a = (V − 1)Lw` of the cubes containing the translations. -/
noncomputable def side (M : Model m) (K : ℕ) (A : ℝ) (L n : ℕ) : ℝ :=
  (((numTranslates K - 1) * L * wInt M K A n : ℕ) : ℝ)

theorem tau_apply (M : Model m) (K : ℕ) (A : ℝ) (L n v : ℕ) (j : Fin m) :
    (tau M K A L n v j : ℝ) = ((v * L * wInt M K A n : ℕ) : ℝ) * (transverseUnit m j : ℝ) := by
  simp [tau]

theorem abs_tau_sub_centre_le {M : Model m} (K : ℕ) (A : ℝ) (L n v : ℕ)
    (hv : v < numTranslates K) (j : Fin m) :
    |(tau M K A L n v j : ℝ) - centre (side M K A L n) j| ≤ side M K A L n / 2 := by
  rw [tau_apply, centre_apply]
  have hle : ((v * L * wInt M K A n : ℕ) : ℝ) ≤ side M K A L n := by
    unfold side
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hv))
  have h0 : (0 : ℝ) ≤ ((v * L * wInt M K A n : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hj : (j : ℕ) = 0
  · simp only [transverseUnit, hj, ↓reduceIte, Int.cast_one, mul_one]
    rw [abs_le]; constructor <;> linarith
  · simp only [transverseUnit, hj, ↓reduceIte, Int.cast_zero, mul_zero, sub_zero, abs_zero]
    have : (0 : ℝ) ≤ side M K A L n := by unfold side; positivity
    linarith

theorem mem_cube_tau {M : Model m} (K : ℕ) (A : ℝ) (L n v : ℕ) (hv : v < numTranslates K) :
    (((0 : ℤ), tau M K A L n v) : Vertex m) ∈
      transverseCube 0 (centre (side M K A L n)) (side M K A L n) :=
  ⟨rfl, fun j => abs_tau_sub_centre_le K A L n v hv j⟩

theorem zero_mem_cube {M : Model m} (K : ℕ) (A : ℝ) (L n : ℕ) (hV : 0 < numTranslates K) :
    (0 : Vertex m) ∈ transverseCube 0 (centre (side M K A L n)) (side M K A L n) := by
  have h := mem_cube_tau (M := M) K A L n 0 hV
  have h0 : tau M K A L n 0 = 0 := by simp [tau]
  rw [h0] at h
  exact h

theorem mem_cube'_tau {M : Model m} (K : ℕ) (A : ℝ) (L n v ℓ : ℕ) (y : Fin m → ℤ)
    (hv : v < numTranslates K) :
    (((ℓ : ℤ), y + tau M K A L n v) : Vertex m) ∈
      transverseCube ((0 : ℤ) + ℓ) (centre (side M K A L n) + transversePoint y)
        (side M K A L n) := by
  refine ⟨by simp, fun j => ?_⟩
  have h := abs_tau_sub_centre_le (M := M) K A L n v hv j
  have : ((y + tau M K A L n v) j : ℝ) -
      (centre (side M K A L n) + transversePoint y : EuclideanSpace ℝ (Fin m)) j =
      (tau M K A L n v j : ℝ) - centre (side M K A L n) j := by
    simp only [Pi.add_apply, Int.cast_add, PiLp.add_apply, transversePoint]
    ring
  rw [this]; exact h

theorem target_mem_cube' {M : Model m} (K : ℕ) (A : ℝ) (L n ℓ : ℕ) (y : Fin m → ℤ)
    (hV : 0 < numTranslates K) :
    (((ℓ : ℤ), y) : Vertex m) ∈
      transverseCube ((0 : ℤ) + ℓ) (centre (side M K A L n) + transversePoint y)
        (side M K A L n) := by
  have h := mem_cube'_tau (M := M) K A L n 0 ℓ y hV
  have h0 : tau M K A L n 0 = 0 := by simp [tau]
  rw [h0, add_zero] at h
  exact h

/-- The two cubes form a pair at distance `ℓ` with the target slope. -/
theorem isCubePair_tau {M : Model m} (K : ℕ) (A : ℝ) (L n ℓ : ℕ) (y : Fin m → ℤ) {b : ℝ}
    (hℓ : 0 < ℓ) (hside : side M K A L n ≤ b * W M K A ℓ) :
    IsCubePair M K A ℓ b (targetSlope ℓ y)
      (transverseCube 0 (centre (side M K A L n)) (side M K A L n))
      (transverseCube ((0 : ℤ) + ℓ) (centre (side M K A L n) + transversePoint y)
        (side M K A L n)) := by
  have h0 : (0 : ℝ) ≤ side M K A L n := by unfold side; positivity
  refine ⟨0, centre (side M K A L n), centre (side M K A L n) + transversePoint y,
    side M K A L n, side M K A L n, rfl, rfl, h0, hside, h0, hside, ?_⟩
  have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have : centre (side M K A L n) + transversePoint y - centre (side M K A L n) -
      (ℓ : ℝ) • targetSlope ℓ y = 0 := by
    rw [targetSlope, smul_smul, mul_inv_cancel₀ hℓ', one_smul]; abel
  rw [this, norm_zero]; positivity

/-! ### Scales -/

theorem one_le_W_of_exponent_nonneg {M : Model m} {K : ℕ} {A s : ℝ} (hA : 1 ≤ A) (hs : 1 ≤ s)
    (he : 0 ≤ (1 : ℝ) / 2 - M.δ / K) : 1 ≤ W M K A s := by
  unfold W Q
  refine Real.sqrt_one.symm.le.trans (Real.sqrt_le_sqrt ?_)
  have h1 : 1 ≤ s ^ ((1 : ℝ) / 2 - M.δ / K) := Real.one_le_rpow hs he
  exact one_le_mul_of_one_le_of_one_le hs (one_le_mul_of_one_le_of_one_le hA h1)

theorem wInt_le_two_mul {M : Model m} {K : ℕ} {A s : ℝ} (h1 : 1 ≤ W M K A s) :
    (wInt M K A s : ℝ) ≤ 2 * W M K A s := by
  unfold wInt
  have := Nat.ceil_lt_add_one (show 0 ≤ W M K A s by linarith)
  linarith

/-- The exponent `1/2 − δ/K` is at least `1/2 − 10⁻⁴` for `K ≥ 10⁴`. -/
theorem exponent_ge {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) :
    (1 : ℝ) / 2 - 1 / 10 ^ 4 ≤ (1 : ℝ) / 2 - M.δ / K := by
  have hK' : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hδ := hM.delta_le_one
  have hδ0 := hM.delta_pos
  have : M.δ / K ≤ 1 / 10 ^ 4 := by
    rw [div_le_div_iff₀ hKpos (by norm_num)]
    nlinarith
  linarith

/-- `V − 1 ≤ K^{2/3}`. -/
theorem numTranslates_sub_one_le (K : ℕ) :
    ((numTranslates K - 1 : ℕ) : ℝ) ≤ (K : ℝ) ^ ((2 : ℝ) / 3) := by
  unfold numTranslates
  have h0 : 0 ≤ (K : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg K) _
  have h := Nat.ceil_lt_add_one h0
  rcases Nat.eq_zero_or_pos ⌈(K : ℝ) ^ ((2 : ℝ) / 3)⌉₊ with hz | hz
  · rw [hz]; simpa using h0
  · rw [Nat.cast_sub hz, Nat.cast_one]; linarith

/-- The target facts: `1 ≤ n`, `1 ≤ ℓ`, `n ≤ ℓ`, and the slope bound `|t − t₀| ≤ ℓ^{δ/100−1/4}`
(for the targets of Section `sec:gain`). -/
theorem target_facts {M : Model m} {K N n ℓ : ℕ} {y : Fin m → ℤ} (hK : 1 ≤ K) (hN : 1 ≤ N)
    (ht : IsTarget M K N n ℓ y) :
    1 ≤ n ∧ 1 ≤ ℓ ∧ n ≤ ℓ ∧ ‖targetSlope ℓ y - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) := by
  obtain ⟨hℓ, hN9, hℓN, hy⟩ := ht
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hN9
    exact_mod_cast this
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, mul_zero] at hℓ; omega
    · exact h
  refine ⟨hn, hℓpos, ?_, ?_⟩
  · rw [hℓ]; exact Nat.le_mul_of_pos_left n (by omega)
  · have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
    rw [Responses.targetSlope_sub_eq hℓpos, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hℓ']
    have hy' : ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤ (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := hy
    calc (ℓ : ℝ)⁻¹ * ‖transversePoint y - (ℓ : ℝ) • M.t₀‖ ≤
          (ℓ : ℝ)⁻¹ * (ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) :=
          mul_le_mul_of_nonneg_left hy' (by positivity)
      _ = (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) := by
          rw [show M.δ / 100 - 1 / 4 = ((3 : ℝ) / 4 + M.δ / 100) - 1 by ring,
            Real.rpow_sub_one hℓ'.ne']
          field_simp

/-! ### From `O₁` and `L^{8d}` bounds to `L²` bounds -/

/-- An `L²` bound from a domination `|f| ≤ X` and an `L^{8d}` bound on `X`. -/
theorem eLpNorm_two_le_of_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f X : Ω → ℝ} (hf : AEStronglyMeasurable f P) {q : ℕ} (hq : 2 ≤ q)
    (hfX : ∀ᵐ ω ∂P, |f ω| ≤ X ω) : eLpNorm f 2 P ≤ eLpNorm X q P := by
  refine (eLpNorm_le_eLpNorm_of_exponent_le
    (show (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) by exact_mod_cast hq)).trans ?_
  refine eLpNorm_mono_ae hf ?_
  filter_upwards [hfX] with ω hω
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ((abs_nonneg _).trans hω)]
  exact hω

end CurvatureVariance.Paper.Gain
