/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.SmallMean.Fluctuation
public import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry
public import IsotropicVariance.Infra.Os.Moments
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Moments at a pair of points and a mesh of grid cubes

Moment estimates for the second paragraph of the proof of Lemma `lem:smallmean`.

* `lintegral_abs_pow_le_of_moments`: integrated interpolation of moments.
* `lintegral_abs_sub_integral_pow_le`: moments of `|D - E D|` from an `O_1` bound.
* `evariance_le_of_comparison`: the variance of `D` against that of `T`.
* `lintegral_rpow_le_of_eLpNorm_le`: from an `eLpNorm` bound to a Lebesgue integral.
* `meshPt`, `meshPt_mem`, `exists_meshPt_near`: mesh points of grid cubes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace IsotropicVariance.Paper.Proofs.SmallMean

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma aemeasurable_ofReal_abs_pow {Y : Ω → ℝ} (hY : AEMeasurable Y P) (k : ℕ) :
    AEMeasurable (fun ω => ENNReal.ofReal (|Y ω| ^ k)) P :=
  ((continuous_abs.measurable.comp_aemeasurable hY).pow_const k).ennreal_ofReal

private lemma lintegral_ofReal_pow_eq_zero {Y : Ω → ℝ} (hY : AEMeasurable Y P) {k : ℕ}
    (hk : 1 ≤ k) (h : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ k) ∂P ≤ 0) :
    ∀ᵐ ω ∂P, Y ω = 0 := by
  have := (lintegral_eq_zero_iff' (aemeasurable_ofReal_abs_pow hY k)).1 (le_antisymm h zero_le)
  filter_upwards [this] with ω hω
  have hω' : |Y ω| ^ k ≤ 0 := ENNReal.ofReal_eq_zero.1 hω
  have : |Y ω| ^ k = 0 := le_antisymm hω' (by positivity)
  exact abs_eq_zero.1 (pow_eq_zero_iff (by omega) |>.1 this)

/-- **Integrated interpolation**: second and `2p`-th moments of `Y` at scale `Q` bound its
`p`-th moment, for any `λ > 0`. -/
theorem lintegral_abs_pow_le_of_moments {Y : Ω → ℝ} (hY : AEMeasurable Y P) {Q l v w : ℝ}
    (hQ : 0 < Q) (hl : 0 < l) {p : ℕ} (hp : 2 ≤ p)
    (h2 : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P ≤ ENNReal.ofReal (v * Q ^ 2))
    (h2p : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (2 * p)) ∂P ≤ ENNReal.ofReal (w * Q ^ (2 * p))) :
    ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ p) ∂P ≤ ENNReal.ofReal ((l ^ (p - 2) * v + w / l ^ p) * Q ^ p) := by
  by_cases hv : 0 ≤ v
  swap
  · have hv' : v * Q ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_le.1 hv).le (by positivity)
    have h0 : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ 2) ∂P ≤ 0 := by
      simpa [sq_abs, ENNReal.ofReal_of_nonpos hv'] using h2
    have hz := lintegral_ofReal_pow_eq_zero hY (k := 2) (by norm_num) h0
    rw [lintegral_congr_ae (g := fun _ => 0) (by
      filter_upwards [hz] with ω hω
      simp [hω, show p ≠ 0 by omega])]
    simp
  by_cases hw : 0 ≤ w
  swap
  · have hw' : w * Q ^ (2 * p) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_le.1 hw).le (by positivity)
    have h0 : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (2 * p)) ∂P ≤ 0 := by
      simpa [ENNReal.ofReal_of_nonpos hw'] using h2p
    have hz := lintegral_ofReal_pow_eq_zero hY (k := 2 * p) (by omega) h0
    rw [lintegral_congr_ae (g := fun _ => 0) (by
      filter_upwards [hz] with ω hω
      simp [hω, show p ≠ 0 by omega])]
    simp
  set a : ℝ := l ^ (p - 2) * Q ^ (p - 2) with ha
  set b : ℝ := 1 / (l ^ p * Q ^ p) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hpt : ∀ ω, ENNReal.ofReal (|Y ω| ^ p) ≤
      ENNReal.ofReal a * ENNReal.ofReal (Y ω ^ 2) +
        ENNReal.ofReal b * ENNReal.ofReal (|Y ω| ^ (2 * p)) := by
    intro ω
    rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hi := abs_pow_le_interp (Y ω / Q) hl hp
    have hQp : 0 < Q ^ p := by positivity
    have e1 : |Y ω / Q| ^ p = |Y ω| ^ p / Q ^ p := by rw [abs_div, abs_of_pos hQ, div_pow]
    have e2 : (Y ω / Q) ^ 2 = Y ω ^ 2 / Q ^ 2 := div_pow _ _ _
    have e3 : |Y ω / Q| ^ (2 * p) = |Y ω| ^ (2 * p) / Q ^ (2 * p) := by
      rw [abs_div, abs_of_pos hQ, div_pow]
    rw [e1, e2, e3] at hi
    have hQe : Q ^ p = Q ^ (p - 2) * Q ^ 2 := by rw [← pow_add]; congr 1; omega
    have hQe2 : Q ^ (2 * p) = Q ^ p * Q ^ p := by rw [← pow_add]; congr 1; omega
    have hlp : 0 < l ^ p := by positivity
    have : |Y ω| ^ p = Q ^ p * (|Y ω| ^ p / Q ^ p) := by field_simp
    rw [this]
    calc Q ^ p * (|Y ω| ^ p / Q ^ p)
        ≤ Q ^ p * (l ^ (p - 2) * (Y ω ^ 2 / Q ^ 2) + |Y ω| ^ (2 * p) / Q ^ (2 * p) / l ^ p) :=
          by gcongr
      _ = a * Y ω ^ 2 + b * |Y ω| ^ (2 * p) := by
          rw [ha, hb, hQe2]
          have hQ2 : 0 < Q ^ 2 := by positivity
          have hQ3 : 0 < Q ^ (p - 2) := by positivity
          rw [hQe]
          field_simp
  have hY2 : AEMeasurable (fun ω => ENNReal.ofReal (Y ω ^ 2)) P :=
    ((hY.pow_const 2).ennreal_ofReal)
  calc ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ p) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal a * ENNReal.ofReal (Y ω ^ 2) +
        ENNReal.ofReal b * ENNReal.ofReal (|Y ω| ^ (2 * p))) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal a * ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P +
        ENNReal.ofReal b * ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (2 * p)) ∂P := by
      rw [lintegral_add_left' (hY2.const_mul _), lintegral_const_mul'' _ hY2,
        lintegral_const_mul'' _ (aemeasurable_ofReal_abs_pow hY _)]
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal (v * Q ^ 2) +
        ENNReal.ofReal b * ENNReal.ofReal (w * Q ^ (2 * p)) := by gcongr
    _ = ENNReal.ofReal ((l ^ (p - 2) * v + w / l ^ p) * Q ^ p) := by
      rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      have hQe : Q ^ p = Q ^ (p - 2) * Q ^ 2 := by rw [← pow_add]; congr 1; omega
      have hQe2 : Q ^ (2 * p) = Q ^ p * Q ^ p := by rw [← pow_add]; congr 1; omega
      have hlp : 0 < l ^ p := by positivity
      have hQ3 : 0 < Q ^ (p - 2) := by positivity
      rw [ha, hb, hQe2]
      rw [hQe]
      field_simp

/-- **Moments of `|D − E D|` from an `O_1` bound on `|D − c|`.** -/
theorem lintegral_abs_sub_integral_pow_le [IsProbabilityMeasure P] {D : Ω → ℝ}
    (hD : Integrable D P) {c θ : ℝ}
    (hθ : 0 < θ) (h : Cited.IsOs P 1 θ fun ω => |D ω - c|) {q : ℕ} (hq : 1 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (|D ω - ∫ ω', D ω' ∂P| ^ q) ∂P ≤
      ENNReal.ofReal (2 ^ (q - 1) * (2 * (1 + (q.factorial : ℝ)) + 4 ^ q) * θ ^ q) := by
  have hmax : ∀ x : ℝ, max |x| 0 = |x| := fun x => max_eq_left (abs_nonneg x)
  have h1 := h.lintegral_pos_rpow_le zero_lt_one hθ (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [hmax, Real.rpow_one, div_one, Nat.ceil_one, Nat.factorial_one, Nat.cast_one] at h1
  have hq' := h.lintegral_pos_rpow_le zero_lt_one hθ (show (0 : ℝ) ≤ q by positivity)
  simp only [hmax, div_one, Nat.ceil_natCast, Real.rpow_natCast] at hq'
  have hInt : Integrable (fun ω => |D ω - c|) P := (hD.sub (integrable_const c)).abs
  have hmean : ∫ ω, |D ω - c| ∂P ≤ 4 * θ := by
    have := ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    have h4 : ENNReal.ofReal (∫ ω, |D ω - c| ∂P) ≤ ENNReal.ofReal (4 * θ) :=
      (this.le.trans h1).trans (ENNReal.ofReal_le_ofReal (by linarith))
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h4
  have hdist : ∀ ω, |D ω - ∫ ω', D ω' ∂P| ≤ |D ω - c| + 4 * θ := by
    intro ω
    have hc : |c - ∫ ω', D ω' ∂P| ≤ ∫ ω, |D ω - c| ∂P := by
      have : c - ∫ ω', D ω' ∂P = ∫ ω', (c - D ω') ∂P := by
        rw [integral_sub (integrable_const c) hD]; simp
      rw [this]
      refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω' => abs_sub_comm _ _)
    calc |D ω - ∫ ω', D ω' ∂P| = |(D ω - c) + (c - ∫ ω', D ω' ∂P)| := by ring_nf
      _ ≤ |D ω - c| + |c - ∫ ω', D ω' ∂P| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hpt : ∀ ω, ENNReal.ofReal (|D ω - ∫ ω', D ω' ∂P| ^ q) ≤
      ENNReal.ofReal (2 ^ (q - 1)) * ENNReal.ofReal (|D ω - c| ^ q) +
        ENNReal.ofReal (2 ^ (q - 1) * (4 * θ) ^ q) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc |D ω - ∫ ω', D ω' ∂P| ^ q ≤ (|D ω - c| + 4 * θ) ^ q :=
          pow_le_pow_left₀ (abs_nonneg _) (hdist ω) q
      _ ≤ 2 ^ (q - 1) * (|D ω - c| ^ q + (4 * θ) ^ q) :=
          add_pow_le (abs_nonneg _) (by positivity) q
      _ = _ := by ring
  have hAE : AEMeasurable (fun ω => ENNReal.ofReal (|D ω - c| ^ q)) P :=
    aemeasurable_ofReal_abs_pow (hD.aemeasurable.sub_const c) q
  calc ∫⁻ ω, ENNReal.ofReal (|D ω - ∫ ω', D ω' ∂P| ^ q) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 ^ (q - 1)) * ENNReal.ofReal (|D ω - c| ^ q) +
        ENNReal.ofReal (2 ^ (q - 1) * (4 * θ) ^ q)) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ (q - 1)) * ∫⁻ ω, ENNReal.ofReal (|D ω - c| ^ q) ∂P +
        ENNReal.ofReal (2 ^ (q - 1) * (4 * θ) ^ q) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul'' _ hAE]
      simp
    _ ≤ ENNReal.ofReal (2 ^ (q - 1)) * ENNReal.ofReal (2 * (1 + (q.factorial : ℝ)) * θ ^ q) +
        ENNReal.ofReal (2 ^ (q - 1) * (4 * θ) ^ q) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      congr 1
      rw [mul_pow]
      ring

/-- **The variance of `D` against that of `T`** when `0 ≤ D − T ≤ C S²` with `S ≤ O_2(θ)`:
`Var D ≤ 2 Var T + 12 C² θ⁴`. Here `0 ≤ S` is assumed (the statement is false for `S` very
negative, since an `O_2` bound controls only the positive part). -/
theorem evariance_le_of_comparison [IsProbabilityMeasure P] {D T S : Ω → ℝ} (hD : MemLp D 2 P)
    (hT : MemLp T 2 P)
    {C θ : ℝ} (_hC : 0 ≤ C) (hθ : 0 < θ) (hS : Cited.IsOs P 2 θ S) (hS0 : ∀ ω, 0 ≤ S ω)
    (hDT : ∀ ω, 0 ≤ D ω - T ω ∧ D ω - T ω ≤ C * S ω ^ 2) :
    evariance D P ≤ ENNReal.ofReal (2 * variance T P + 12 * C ^ 2 * θ ^ 4) := by
  rw [← hD.ofReal_variance_eq]
  apply ENNReal.ofReal_le_ofReal
  have hsplit := variance_le_two_mul_add hD hT
  have hE : MemLp (fun ω => D ω - T ω) 2 P := hD.sub hT
  have hInt : Integrable (fun ω => (D ω - T ω) ^ 2) P := hE.integrable_sq
  have h4 := hS.lintegral_pos_rpow_le (by norm_num : (0 : ℝ) < 2) hθ (show (0 : ℝ) ≤ 4 by norm_num)
  have hc : ⌈(4 : ℝ) / 2⌉₊ = 2 := by norm_num
  rw [hc] at h4
  have hSAE : AEMeasurable (fun ω => ENNReal.ofReal (S ω ^ 4)) P :=
    (hS.1.pow_const 4).ennreal_ofReal
  have hle : ∫⁻ ω, ENNReal.ofReal ((D ω - T ω) ^ 2) ∂P ≤ ENNReal.ofReal (6 * C ^ 2 * θ ^ 4) := by
    calc ∫⁻ ω, ENNReal.ofReal ((D ω - T ω) ^ 2) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (S ω ^ 4) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          obtain ⟨h0, h1⟩ := hDT ω
          calc (D ω - T ω) ^ 2 ≤ (C * S ω ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
            _ = C ^ 2 * S ω ^ 4 := by ring
      _ = ENNReal.ofReal (C ^ 2) * ∫⁻ ω, ENNReal.ofReal (S ω ^ 4) ∂P :=
          lintegral_const_mul'' _ hSAE
      _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (2 * (1 + ((2 : ℕ).factorial : ℝ)) * θ ^ (4 : ℝ)) := by
          gcongr
          refine le_of_eq_of_le (lintegral_congr fun ω => ?_) h4
          rw [max_eq_left (hS0 ω)]
          norm_cast
      _ = ENNReal.ofReal (6 * C ^ 2 * θ ^ 4) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num [Nat.factorial]
          ring
  have hint : ∫ ω, (D ω - T ω) ^ 2 ∂P ≤ 6 * C ^ 2 * θ ^ 4 := by
    have := ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    rw [← this] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
  linarith

/-- From an `L^q` bound by `eLpNorm` (as in the modulus contract) to the Lebesgue integral of the
`q`-th power. -/
theorem lintegral_rpow_le_of_eLpNorm_le {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) {q : ℕ} (hq : 1 ≤ q)
    {B : ℝ} (h : eLpNorm f (q : ENNReal) P ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ^ (q : ℝ) ∂P ≤ ENNReal.ofReal B ^ (q : ℝ) := by
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hm := aestronglyMeasurable_of_eLpNorm_ne_top
    (h.trans_lt ENNReal.ofReal_lt_top).ne
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hm] at h
  have hqr : (0 : ℝ) < (q : ENNReal).toReal := by simp; omega
  have h2 := ENNReal.rpow_le_rpow h hqr.le
  rw [← ENNReal.rpow_mul] at h2
  have e : 1 / (q : ENNReal).toReal * (q : ENNReal).toReal = 1 := by
    field_simp
  rw [e, ENNReal.rpow_one] at h2
  simp only [ENNReal.toReal_natCast] at h2
  refine le_of_eq_of_le (lintegral_congr fun ω => ?_) h2
  rw [Real.enorm_of_nonneg (hf ω)]

end Moments

section Mesh

variable {m : ℕ}

/-- The point `(i s, W(j + t))` of the grid cube `I_i(j)`, for `t` in the unit cube. -/
noncomputable def meshPt (s W : ℝ) (i : ℕ) (j : Fin m → ℤ) (t : EuclideanSpace ℝ (Fin m)) :
    Pt m :=
  Pt.mk ((i : ℝ) * s) (WithLp.toLp 2 fun l => W * ((j l : ℝ) + t l))

theorem meshPt_mem {s W : ℝ} (hW : 0 ≤ W) (i : ℕ) (j : Fin m → ℤ) {t : EuclideanSpace ℝ (Fin m)}
    (ht : t ∈ unitCube m) : meshPt s W i j t ∈ gridCube s W 0 i j := by
  refine ⟨by simp [meshPt], fun k => ?_⟩
  obtain ⟨h0, h1⟩ := ht k
  simp only [meshPt, sub_zero, Pt.tr_mk]
  constructor
  · show W * (j k : ℝ) ≤ W * ((j k : ℝ) + t k)
    nlinarith
  · show W * ((j k : ℝ) + t k) ≤ W * ((j k : ℝ) + 1)
    nlinarith

/-- **Every point of a grid cube is within `Wh` of a mesh point**, for a net of the unit cube of
radius `h`. -/
theorem exists_meshPt_near {s W h : ℝ} (hW : 0 < W) {T : Finset (EuclideanSpace ℝ (Fin m))}
    (hT : ∀ y ∈ unitCube m, ∃ t ∈ T, dist y t ≤ h) {i : ℕ} {j : Fin m → ℤ} {u : Pt m}
    (hu : u ∈ gridCube s W 0 i j) : ∃ t ∈ T, dist u (meshPt s W i j t) ≤ W * h := by
  obtain ⟨hlon, htr⟩ := hu
  set y : EuclideanSpace ℝ (Fin m) :=
    WithLp.toLp 2 fun l => (Pt.tr u l - W * j l) / W with hy
  have hyc : y ∈ unitCube m := by
    intro l
    obtain ⟨a, b⟩ := htr l
    simp only [sub_zero] at a b
    simp only [hy]
    constructor
    · exact div_nonneg (by linarith) hW.le
    · rw [div_le_one hW]; linarith
  obtain ⟨t, htT, hd⟩ := hT y hyc
  refine ⟨t, htT, ?_⟩
  have hsub : Pt.tr (u - meshPt s W i j t) = W • (y - t) := by
    ext l
    simp [meshPt, hy]
    field_simp
    ring
  have hlon' : Pt.lon (u - meshPt s W i j t) = 0 := by
    simp only [sub_zero] at hlon
    simp [meshPt, hlon]
  have hn := Profiles.norm_sq_eq_lon_tr (u - meshPt s W i j t)
  rw [hlon', hsub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hn
  rw [dist_eq_norm]
  have : ‖u - meshPt s W i j t‖ = W * ‖y - t‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) (two_ne_zero)).1 ?_
    rw [hn, mul_pow]; ring
  rw [this, ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left hd hW.le

end Mesh

end IsotropicVariance.Paper.Proofs.SmallMean
