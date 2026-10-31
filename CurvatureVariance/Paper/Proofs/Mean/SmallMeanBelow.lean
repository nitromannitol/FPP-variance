/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Mean.MeanPositive
import CurvatureVariance.Infra.FPP.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp

/-!
# The lower bound of the proof of Lemma `lem:smallmean`, equation `eq:meanbelow`

The paper's display, equation `eq:meanbelow` in the proof of Lemma `lem:smallmean`, under the
contradiction hypothesis `E[T(0,(s,y₀))] − μ(s,y₀) > Q_s/100` of that proof:

* `exists_smallMean_near`: Jensen's inequality and Lemma `lem:modulus` with `b = 2` and `κ = 1/8`,
  at a lattice vector `z`, as in the paper. For a non-integer `z` the rounded endpoint would cost a
  constant; the only use, the entries of the arrays, has `v − u` a lattice vector.
* `exists_smallMean_far`: `E[T] ≥ μ` (equation `eq:classical`) and equation `eq:support`.
* `meanbelow_of_near_far`: the two bounds combine, with `c₁` from `meanbelowConst`.
* `exists_meanbelow`: equation `eq:meanbelow`, where equation `eq:scales` bounds the remainder
  `s|t − t₀|^{2+δ}`. The constant `c₁` comes before `K`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

/-- **Jensen's inequality and Lemma `lem:modulus`** (the proof of Lemma `lem:smallmean`), with
`b = 2` and `κ = 1/8`: the mean inherits the modulus, with the supporting linear term retained
exactly, for `z ∈ ℤ^{d−1}` with `|z| ≤ h(sQ_s)^{1/2}`. The `h` of Lemma `lem:modulus` is replaced by
`min h 1`, so that `z` stays in the cube of side `2 W_s`. -/
theorem exists_smallMean_near {m : ℕ} (hmodulus : ModulusStatement m)
    (hclassical : ClassicalStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
      ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
      Premise M K A N → RangeA M K A N Cstar →
      ∀ s : ℕ, 1 ≤ s → (N : ℝ) / 8 ≤ s → s ≤ N →
      ∀ (y₀ : Fin m → ℤ) (t : EuclideanSpace ℝ (Fin m)),
        (s : ℝ) • t = transversePoint y₀ → ‖t - M.t₀‖ ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
      ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P →
      ∀ z : Fin m → ℤ, ‖transversePoint z‖ ≤ h * W M K A s →
        |((∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀ + z) ∂M.P) -
            inner ℝ P (point ((s : ℤ), y₀ + z))) -
          ((∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀) ∂M.P) -
            inner ℝ P (point ((s : ℤ), y₀)))| ≤ η * Q M K A s := by
  obtain ⟨h₀, hh₀, hm⟩ := hmodulus bd hbd Cstar 2 (by norm_num) η hη
  let h := min h₀ 1
  have hh : 0 < h := lt_min hh₀ zero_lt_one
  have hh1 : h ≤ 1 := min_le_right _ _
  have hhh₀ : h ≤ h₀ := min_le_left _ _
  refine ⟨h, hh, hh1, fun K hK => ?_⟩
  obtain ⟨N₀, hmK⟩ := hm K hK (1 / 8) (by norm_num) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro M hM hfit N hN A hA hPrem hRange s hs hsN hsN' y₀ t hst ht P hP z hz
  let : IsProbabilityMeasure M.P := hM.probP
  have hspos : (0 : ℝ) < s := by exact_mod_cast (zero_lt_one.trans_le hs)
  have hQ : 0 < Q M K A s :=
    mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hspos _)
  have hW : 0 ≤ W M K A s := Real.sqrt_nonneg _
  let I : Set (Vertex m) := transverseCube 0 0 0
  let I' : Set (Vertex m) := transverseCube s (transversePoint y₀) (2 * W M K A s)
  have hpair : IsCubePair M K A s 2 t I I' := by
    refine ⟨0, 0, transversePoint y₀, 0, 2 * W M K A s, rfl, ?_, le_rfl,
      by positivity, by positivity, le_rfl, ?_⟩
    · simp only [zero_add]
      rfl
    · rw [sub_zero, ← hst, sub_self, norm_zero]
      positivity
  obtain ⟨X, hXp, hX⟩ := hmK M hM hfit N hN A hA hPrem hRange s
    (by linarith only [hsN]) hsN' t I I' hpair ht P hP
  have hmem0 : (0 : Vertex m) ∈ I := by
    refine ⟨rfl, fun j => ?_⟩
    simp only [Prod.snd_zero, Pi.zero_apply, Int.cast_zero, PiLp.zero_apply,
      sub_zero, abs_zero, zero_div, le_refl]
  have hmem1 : ((s : ℤ), y₀) ∈ I' := by
    refine ⟨rfl, fun j => ?_⟩
    simp only [transversePoint_apply, sub_self, abs_zero]
    positivity
  have hmem2 : ((s : ℤ), y₀ + z) ∈ I' := by
    refine ⟨rfl, fun j => ?_⟩
    have hj := PiLp.norm_apply_le (transversePoint z) j
    change |(z j : ℝ)| ≤ ‖transversePoint z‖ at hj
    simp only [Pi.add_apply, Int.cast_add, transversePoint_apply, add_sub_cancel_left]
    have hhh := mul_le_mul_of_nonneg_right hh1 hW
    linarith only [hj, hz, hhh]
  have hmod : ∀ᵐ ω ∂M.P,
      |(passageTimeReal ω 0 ((s : ℤ), y₀ + z) - inner ℝ P (point ((s : ℤ), y₀ + z))) -
        (passageTimeReal ω 0 ((s : ℤ), y₀) - inner ℝ P (point ((s : ℤ), y₀)))| ≤ X ω := by
    filter_upwards [hX] with ω hω
    have hb := hω 0 hmem0 0 hmem0 ((s : ℤ), y₀ + z) hmem2 ((s : ℤ), y₀) hmem1
      (by simpa only [sub_self, norm_zero] using mul_nonneg hh₀.le hW)
      (by rw [norm_point_same_face_sub]
          exact hz.trans (mul_le_mul_of_nonneg_right hhh₀ hW))
    simp only [Infra.FPP.point_zero, sub_zero, add_zero, inner_sub_right] at hb
    convert hb using 1
    congr 1
    ring
  obtain ⟨C, hC, hcl⟩ := hclassical bd hbd
  have hnonzero (y : Fin m → ℤ) : ((s : ℤ), y) ≠ (0 : Vertex m) := by
    intro heq
    have heq' := congrArg Prod.fst heq
    simp only [Prod.fst_zero] at heq'
    omega
  have hI₁ := (hcl M hM hfit ((s : ℤ), y₀) (hnonzero _)).1
  have hI₂ := (hcl M hM hfit ((s : ℤ), y₀ + z) (hnonzero _)).1
  have hp : (1 : ℝ≥0∞) ≤ (8 * (m + 1) : ℕ) := by norm_cast; omega
  have hb := abs_integral_sub_le_of_ae_modulus hp
    (hI₁.sub (integrable_const (inner ℝ P (point ((s : ℤ), y₀)))))
    (hI₂.sub (integrable_const (inner ℝ P (point ((s : ℤ), y₀ + z)))))
    hmod (mul_nonneg hη.le hQ.le) hXp
  simp only [Pi.sub_apply] at hb
  simpa only [integral_sub hI₁ (integrable_const _),
    integral_sub hI₂ (integrable_const _), integral_const, probReal_univ, one_smul] using hb

/-- **The far bound** (the proof of Lemma `lem:smallmean`): `E[T] ≥ μ` and
equation `eq:support`, rescaled from length one to length `s`, bound the difference below by
`c|z|²/s − C s|t − t₀|^{2+δ}`. -/
theorem exists_smallMean_far {m : ℕ} (hsupport : SupportStatement m)
    (hclassical : ClassicalStatement m) (bd : Bounds m) (hbd : bd.Valid) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧
      ∀ M : Model m, M.Standing → M.Fits bd → ∀ s : ℕ, 0 < s →
      ∀ (y₀ z : Fin m → ℤ) (t : EuclideanSpace ℝ (Fin m)),
      (s : ℝ) • t = transversePoint y₀ → ‖t - M.t₀‖ ≤ r →
      ‖(s : ℝ)⁻¹ • transversePoint z‖ ≤ r →
      ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P →
        c * ‖transversePoint z‖ ^ 2 / s - C * s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
          (∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀ + z) ∂M.P) -
            inner ℝ P (point ((s : ℤ), y₀ + z)) := by
  obtain ⟨c, C, r, hc, hC, hr, -, hsupport⟩ := hsupport bd hbd
  obtain ⟨_Cc, _hCc, hclass⟩ := hclassical bd hbd
  refine ⟨c, C, r, hc, hC, hr, ?_⟩
  intro M hM hfit s hs y₀ z t hst ht htz P hP
  have hquad := (hsupport M hM hfit).1
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hx : ((s : ℤ), y₀ + z) ≠ (0 : Vertex m) := by
    intro heq
    have hf := congrArg Prod.fst heq
    simp only [Prod.fst_zero] at hf
    omega
  have hmean := (hclass M hM hfit ((s : ℤ), y₀ + z) hx).2.2.1
  have hlow := (hquad t ((s : ℝ)⁻¹ • transversePoint z) ht htz P hP).1
  have hmul := mul_le_mul_of_nonneg_left hlow hspos.le
  have hpoint := point_target_eq_smul_slopeVec hs hst z
  have hhom : M.μ.1 (point ((s : ℤ), y₀ + z)) - inner ℝ P (point ((s : ℤ), y₀ + z)) =
      (s : ℝ) * (M.μ.1 (slopeVec (t + (s : ℝ)⁻¹ • transversePoint z)) -
        inner ℝ P (slopeVec (t + (s : ℝ)⁻¹ • transversePoint z))) := by
    rw [hpoint, map_smul_eq_mul, Real.norm_of_nonneg hspos.le, inner_smul_right]
    ring
  have hscale : (s : ℝ) * (c * ‖(s : ℝ)⁻¹ • transversePoint z‖ ^ 2 -
      C * ‖t - M.t₀‖ ^ (2 + M.δ)) =
      c * ‖transversePoint z‖ ^ 2 / s - C * s * ‖t - M.t₀‖ ^ (2 + M.δ) := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hspos.le)]
    field_simp
  rw [hscale, ← hhom] at hmul
  linarith only [hmul, hmean]

/-- The constant `c₁` of equation `eq:meanbelow`: small enough for both the near and the far
bound, depending only on the constant `c` of equation `eq:support` and on `h`. -/
noncomputable def meanbelowConst (c h : ℝ) : ℝ :=
  min (1 / (200 * (1 + h ^ 2))) (min (c / 2) (c * h ^ 2 / 4))

theorem meanbelowConst_pos {c h : ℝ} (hc : 0 < c) (hh : 0 < h) : 0 < meanbelowConst c h :=
  lt_min (by positivity) (lt_min (by positivity) (by positivity))

/-- The near and far bounds combine into one display (equation `eq:meanbelow`). -/
theorem meanbelow_of_near_far {E : Type*} (size φ : E → ℝ) (hsize : ∀ z, 0 ≤ size z)
    {Q s h c ρ R : ℝ} (hQ : 0 < Q) (hs : 0 < s) (hh : 0 < h) (hc : 0 < c)
    (hρ : ρ ^ 2 = h ^ 2 * (s * Q)) (hρ0 : 0 ≤ ρ)
    (hnear : ∀ z, size z ≤ ρ → Q / 200 ≤ φ z)
    (hfar : ∀ z, size z ≤ R → c * size z ^ 2 / s - c * h ^ 2 * Q / 4 ≤ φ z) :
    ∀ z, size z ≤ R →
      meanbelowConst c h * Q + meanbelowConst c h * size z ^ 2 / s ≤ φ z := by
  intro z hz
  set c₁ := meanbelowConst c h with hc₁
  have hc₁pos : 0 < c₁ := meanbelowConst_pos hc hh
  have hm1 : c₁ ≤ 1 / (200 * (1 + h ^ 2)) := min_le_left _ _
  have hm2 : c₁ ≤ c / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : c₁ ≤ c * h ^ 2 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  by_cases hzρ : size z ≤ ρ
  · have h1 := hnear z hzρ
    have hsq : size z ^ 2 ≤ h ^ 2 * (s * Q) := hρ ▸ pow_le_pow_left₀ (hsize z) hzρ 2
    have h2 : c₁ * size z ^ 2 / s ≤ c₁ * h ^ 2 * Q := by
      rw [div_le_iff₀ hs]
      have hh' := mul_le_mul_of_nonneg_left hsq hc₁pos.le
      linarith only [hh']
    have h3 : c₁ * (1 + h ^ 2) ≤ 1 / 200 := by
      rw [le_div_iff₀ (by positivity)] at hm1
      linarith only [hm1]
    have h4 := mul_le_mul_of_nonneg_right h3 hQ.le
    linarith only [h1, h2, h4]
  · have hzρ' : ρ ≤ size z := (lt_of_not_ge hzρ).le
    have h1 := hfar z hz
    have hsq : h ^ 2 * (s * Q) ≤ size z ^ 2 := hρ ▸ pow_le_pow_left₀ hρ0 hzρ' 2
    set x := size z ^ 2 / s with hx
    have hx0 : 0 ≤ x := div_nonneg (sq_nonneg _) hs.le
    have h2 : h ^ 2 * Q ≤ x := by
      rw [hx, le_div_iff₀ hs]
      linarith only [hsq]
    have e1 : c * size z ^ 2 / s = c * x := by rw [hx]; ring
    have e2 : c₁ * size z ^ 2 / s = c₁ * x := by rw [hx]; ring
    rw [e1] at h1
    rw [e2]
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ c / 2)
    have h4 := mul_le_mul_of_nonneg_right hm2 hx0
    have h5 := mul_le_mul_of_nonneg_right hm3 hQ.le
    nlinarith only [h1, h3, h4, h5]

/-- **Equation `eq:meanbelow`**: under the contradiction hypothesis, for `|z| ≤ s^{3/4+δ/100}/4`,
`E[T(0,(s,y₀+z))] − ζ_t·(s,y₀+z) ≥ c₁Q_s + c₁|z|²/s`, with `z` a lattice vector, as in the paper.
The constant `c₁` comes before `K`, since `h` does. -/
theorem exists_meanbelow {m : ℕ} (hsupport : SupportStatement m) (hscales : ScalesStatement m)
    (hclassical : ClassicalStatement m) (hmodulus : ModulusStatement m)
    (bd : Bounds m) (hbd : bd.Valid) (Cstar : ℝ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
      ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
      Premise M K A N → RangeA M K A N Cstar →
      ∀ s : ℕ, (N : ℝ) / 8 ≤ s → (s : ℝ) ≤ N / 4 → ∀ y₀ : Fin m → ℤ,
      ‖transversePoint y₀ - (s : ℝ) • M.t₀‖ ≤ s * (N : ℝ) ^ (M.δ / 100 - 1 / 4) →
      Q M K A s / 100 <
        (∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀) ∂M.P) - M.μ.1 (point ((s : ℤ), y₀)) →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec ((s : ℝ)⁻¹ • transversePoint y₀)) p →
      ∀ z : Fin m → ℤ, ‖transversePoint z‖ ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 4 →
        c₁ * Q M K A s + c₁ * ‖transversePoint z‖ ^ 2 / s ≤
          (∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀ + z) ∂M.P) -
            inner ℝ p (point ((s : ℤ), y₀ + z)) := by
  obtain ⟨c, C, r, hc, hC, hr, hfar⟩ := exists_smallMean_far hsupport hclassical bd hbd
  obtain ⟨h, hh, -, hnear⟩ := exists_smallMean_near hmodulus hclassical bd hbd Cstar
    (η := 1 / 200) (by norm_num)
  obtain ⟨Cs, hCs, hscales⟩ := hscales bd hbd Cstar
  have hq : 0 < (1 : ℝ) / 4 - bd.law.δ / 100 := by linarith only [hbd.law.delta_le_one]
  have hlim₁ : Tendsto (fun s : ℕ => (s : ℝ) ^ (bd.law.δ / 100 - 1 / 4)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop using 1
    funext s
    change (s : ℝ) ^ (bd.law.δ / 100 - 1 / 4) = (s : ℝ) ^ (-(1 / 4 - bd.law.δ / 100))
    congr 1
    ring
  have hlim₂ : Tendsto (fun s : ℕ => C * Cs * (s : ℝ) ^ (-bd.law.δ / 5)) atTop (𝓝 0) := by
    have hh' := (tendsto_rpow_neg_atTop
      (div_pos hbd.law.delta_pos (by norm_num : (0 : ℝ) < 5))).comp tendsto_natCast_atTop_atTop
    simpa only [neg_div, mul_zero, Function.comp_apply] using tendsto_const_nhds.mul hh'
  obtain ⟨S₁, hS₁⟩ := eventually_atTop.1 (hlim₁.eventually (gt_mem_nhds (half_pos hr)))
  obtain ⟨S₂, hS₂⟩ := eventually_atTop.1
    (hlim₂.eventually (gt_mem_nhds (by positivity : 0 < c * h ^ 2 / 4)))
  let S := max 2 (max S₁ S₂)
  refine ⟨meanbelowConst c h, meanbelowConst_pos hc hh, fun K hK => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hnear K hK
  refine ⟨max N₁ (8 * S), ?_⟩
  intro M hM hfit N hN A hA hPrem hRange s hsLower hsUpper y₀ hy₀ hbias p hp z hz
  simp only [← hfit.δ_eq] at hS₁ hS₂
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hNS : 8 * S ≤ N := (le_max_right _ _).trans hN
  have hsS : S ≤ s := by
    have hhNS : (8 : ℝ) * S ≤ N := by exact_mod_cast hNS
    have hhSs : (S : ℝ) ≤ s := by linarith only [hhNS, hsLower]
    exact_mod_cast hhSs
  have hs2 : 2 ≤ s := (le_max_left _ _).trans hsS
  have hs1 : 1 ≤ s := by omega
  have hspos : (0 : ℝ) < s := by exact_mod_cast (zero_lt_one.trans_le hs1)
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsN : (s : ℝ) ≤ N := by linarith only [hsUpper, hNnonneg]
  have hN2 : 2 ≤ N := by
    have hhh : ((2 : ℕ) : ℝ) ≤ N := by
      have hs2R : (2 : ℝ) ≤ s := by exact_mod_cast hs2
      push_cast
      linarith only [hs2R, hsN]
    exact_mod_cast hhh
  have hQ : 0 < Q M K A s := mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hspos _)
  let t := (s : ℝ)⁻¹ • transversePoint y₀
  have hst : (s : ℝ) • t = transversePoint y₀ := by
    dsimp only [t]
    rw [smul_inv_smul₀ hspos.ne']
  have ht : ‖t - M.t₀‖ ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) := by
    have hbase : ‖t - M.t₀‖ ≤ (N : ℝ) ^ (M.δ / 100 - 1 / 4) := by
      have he : t - M.t₀ = (s : ℝ)⁻¹ •
          (transversePoint y₀ - (s : ℝ) • M.t₀) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
      rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hspos.le)]
      have hh' := mul_le_mul_of_nonneg_left hy₀ (inv_nonneg.2 hspos.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hspos.ne', one_mul] using hh'
    exact hbase.trans (Real.rpow_le_rpow_of_nonpos hspos hsN (by linarith only [hM.delta_le_one]))
  have hscale : (s : ℝ) ^ (M.δ / 100 - 1 / 4) < r / 2 :=
    hS₁ s ((le_max_left _ _).trans ((le_max_right _ _).trans hsS))
  have htr : ‖t - M.t₀‖ ≤ r := ht.trans (by linarith only [hscale, hr])
  have hsN' : s ≤ N := by exact_mod_cast hsN
  have hcontact := inner_target_eq_of_isSubgradient (by omega : 0 < s) hst hp
  have hnear' : ∀ z : Fin m → ℤ, ‖transversePoint z‖ ≤ h * W M K A s →
      Q M K A s / 200 ≤
        (∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀ + z) ∂M.P) -
          inner ℝ p (point ((s : ℤ), y₀ + z)) := by
    intro z' hz'
    have hm := hN₁ M hM hfit N hN₁' A hA hPrem hRange s hs1 hsLower hsN' y₀ t hst ht p hp z' hz'
    rw [hcontact] at hm
    have hlow := (abs_le.mp hm).1
    linarith only [hbias, hlow]
  -- equation `eq:scales` bounds the remainder at `t`
  have hsqrt : Real.sqrt N / 16 ≤ s := by
    have hsqN : Real.sqrt (N : ℝ) ≤ N := by
      apply Real.sqrt_le_iff.2
      refine ⟨hNnonneg, ?_⟩
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      nlinarith only [hN1]
    linarith only [hsqN, hsLower]
  have hremainder : C * s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ c * h ^ 2 * Q M K A s / 4 := by
    have hsc := (hscales K hK M hM hfit N hN2 A hA hRange s hsqrt).2 t
      (ht.trans (by
        have hpos := Real.rpow_nonneg hspos.le (M.δ / 100 - 1 / 4)
        linarith only [hpos]))
    rw [div_le_iff₀ hQ] at hsc
    have hsmall := hS₂ s ((le_max_right _ _).trans ((le_max_right _ _).trans hsS))
    have h1 := mul_le_mul_of_nonneg_left hsc hC.le
    have h2 := mul_le_mul_of_nonneg_right hsmall.le hQ.le
    calc C * s * ‖t - M.t₀‖ ^ (2 + M.δ) = C * (s * ‖t - M.t₀‖ ^ (2 + M.δ)) := by ring
      _ ≤ C * (Cs * (s : ℝ) ^ (-M.δ / 5) * Q M K A s) := h1
      _ = C * Cs * (s : ℝ) ^ (-M.δ / 5) * Q M K A s := by ring
      _ ≤ c * h ^ 2 / 4 * Q M K A s := h2
      _ = c * h ^ 2 * Q M K A s / 4 := by ring
  have hfar' : ∀ z : Fin m → ℤ, ‖transversePoint z‖ ≤
      (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 4 →
      c * ‖transversePoint z‖ ^ 2 / s - c * h ^ 2 * Q M K A s / 4 ≤
        (∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀ + z) ∂M.P) -
          inner ℝ p (point ((s : ℤ), y₀ + z)) := by
    intro z' hz'
    have hzscale' : ‖(s : ℝ)⁻¹ • transversePoint z'‖ ≤
        (s : ℝ) ^ (M.δ / 100 - 1 / 4) / 4 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hspos.le)]
      have hh' := mul_le_mul_of_nonneg_left hz' (inv_nonneg.2 hspos.le)
      have heq : (s : ℝ)⁻¹ * ((s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 4) =
          (s : ℝ) ^ (M.δ / 100 - 1 / 4) / 4 := by
        rw [show (3 : ℝ) / 4 + M.δ / 100 = 1 + (M.δ / 100 - 1 / 4) by ring,
          Real.rpow_add hspos, Real.rpow_one]
        field_simp
      exact hh'.trans_eq heq
    have hf := hfar M hM hfit s (by omega) y₀ z' t hst htr
      (hzscale'.trans (by linarith only [hscale, hr])) p hp
    linarith only [hf, hremainder]
  have hρ : (h * W M K A s) ^ 2 = h ^ 2 * ((s : ℝ) * Q M K A s) := by
    rw [mul_pow, W, Real.sq_sqrt (mul_nonneg hspos.le hQ.le)]
  exact meanbelow_of_near_far (fun z : Fin m → ℤ => ‖transversePoint z‖)
    (fun z => (∫ ω, passageTimeReal ω 0 ((s : ℤ), y₀ + z) ∂M.P) -
      inner ℝ p (point ((s : ℤ), y₀ + z)))
    (fun _ => norm_nonneg _) hQ hspos hh hc hρ
    (mul_nonneg hh.le (Real.sqrt_nonneg _)) hnear' hfar' z hz

end CurvatureVariance.Paper.Mean
