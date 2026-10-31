/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Localization.Common
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# Lemma `lem:localization`, as in the paper

**Lemma `lem:localization`**, with its proof: `localizationStatement_of`, the edge
`lem:localization` of the graph in `Closing.Main`.

The paper's proof is that of [AB26, Lemma 5.1], with three changes. The model is
`IsotropicVariance.Paper.Proofs.Localization.localization_at_slope` in the continuum library. The
steps of the paper's proof of Lemma `lem:localization`:

| Step of the paper's proof | Here |
|---|---|
| Stationarity | `LocTranslate`, `localizationStatement_of_normal` |
| Upper bound | `exists_upper`, with Lemma `lem:tree` at `ℓ/16` and `8b` |
| First change | `LocConfine`, `conf_path` |
| Second change | `LocThick`, `LocCfg`, `LocAnnuli`, `Cfg.deviation_le_good` |
| Third change | `LocMoments`, `exists_length_sup`, `moment_of_bounds` |
| "For `N` large" | `LocNumeric`, `LocPack` |

`Loc.NormalStatement` is the statement for pairs with `|ū| ≤ d^{1/2}`; it is proved by
`normalStatement_of`, and `localizationStatement_of_normal` removes the normalization.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts
  CurvatureVariance.Paper.Proofs.Geometry Radius Loc

variable {m : ℕ}

namespace Loc

/-- The statement of Lemma `lem:localization` for pairs with `ū = (0, c)`, `|c| ≤ √m`, the
normalization "by stationarity, we may assume that `|ū| ≤ d^{1/2}`" of the proof of Lemma
`lem:localization`. -/
def NormalStatement (m : ℕ) : Prop :=
  ∀ bd : Bounds m, bd.Valid → ∀ Cstar : ℝ, ∀ b : ℝ, 1 ≤ b → ∀ p : ℝ, 1 ≤ p →
  ∃ Cb : ℝ, 1 ≤ Cb ∧ ∀ κ : ℝ, 0 < κ → ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
  ∀ M : Model m, M.Standing → M.Fits bd →
  ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
  Premise M K A N → RangeA M K A N Cstar →
  ∀ ℓ : ℕ, κ * N ≤ ℓ → ℓ ≤ N → ∀ (t c c' : EuclideanSpace ℝ (Fin m)) (a₀ a₀' : ℝ),
    0 ≤ a₀ → a₀ ≤ b * W M K A ℓ → 0 ≤ a₀' → a₀' ≤ b * W M K A ℓ →
    ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1) → ‖c‖ ≤ Real.sqrt m →
    ‖t - M.t₀‖ ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) →
    (∫⁻ ω, locRadius ω (transverseCube 0 c a₀) (transverseCube (0 + ℓ) c' a₀') (W M K A ℓ) ^ p
        ∂M.P ≤ ENNReal.ofReal Cb) ∧
    ∫⁻ ω, locRadiusSlab ω 0 (0 + ℓ) (transverseCube 0 c a₀) (transverseCube (0 + ℓ) c' a₀')
        (W M K A ℓ) ^ p ∂M.P ≤ ENNReal.ofReal Cb

/-- The deviation of an empty family of paths. -/
theorem deviation_eq_zero (geo : ∀ {u v : Vertex m}, (latticeGraph m).Walk u v → Prop)
    {I I' : Set (Vertex m)} (h : ¬ (I.Nonempty ∧ I'.Nonempty)) : deviation geo I I' = 0 := by
  refine le_antisymm ?_ bot_le
  simp only [deviation]
  exact iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv =>
    absurd ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ h

/-- The points of `I` lie in `[−N², N²]^d`: its hyperplane is `{x₁ = 0}`. -/
theorem box_left {c : EuclideanSpace ℝ (Fin m)} {a₀ R : ℝ} (ha₀ : 0 ≤ a₀) (hR : ‖c‖ + a₀ ≤ R)
    {u : Vertex m} (hu : u ∈ transverseCube 0 c a₀) : InBox R u := by
  have hR0 : 0 ≤ R := by have := norm_nonneg c; linarith only [this, ha₀, hR]
  refine ⟨by rw [hu.1]; simpa using hR0, fun j => ?_⟩
  have h1 := hu.2 j
  have h2 := PiLp.norm_apply_le c j
  rw [Real.norm_eq_abs] at h2
  have h3 := abs_add_le ((u.2 j : ℝ) - c j) (c j)
  rw [sub_add_cancel] at h3
  linarith only [h1, h2, h3, ha₀, hR]

/-- The points of `I'` lie in `[−N², N²]^d`. -/
theorem box_right {c' : EuclideanSpace ℝ (Fin m)} {a₀ R : ℝ} {ℓ : ℕ} (ha₀ : 0 ≤ a₀)
    (hR : ‖c'‖ + a₀ ≤ R) (hℓ : (ℓ : ℝ) ≤ R) {v : Vertex m}
    (hv : v ∈ transverseCube (0 + ℓ) c' a₀) : InBox R v := by
  refine ⟨?_, fun j => ?_⟩
  · have h1 : v.1 = (ℓ : ℤ) := by rw [hv.1, zero_add]
    rw [h1]
    simpa using hℓ
  · have h1 := hv.2 j
    have h2 := PiLp.norm_apply_le c' j
    rw [Real.norm_eq_abs] at h2
    have h3 := abs_add_le ((v.2 j : ℝ) - c' j) (c' j)
    rw [sub_add_cancel] at h3
    linarith only [h1, h2, h3, ha₀, hR]

/-- `log(2 + J) ≤ (4m + 1) log N`, for `J ≤ N^{4m}` pairs of points of the two cubes. -/
theorem log_card_le {p p' : ℤ} {c c' : EuclideanSpace ℝ (Fin m)} {a₀ a₀' : ℝ} {N : ℕ}
    (ha₀ : 0 ≤ a₀) (ha₀' : 0 ≤ a₀') (hN : 3 ≤ N) (h1 : a₀ + 1 ≤ (N : ℝ) ^ 2)
    (h2 : a₀' + 1 ≤ (N : ℝ) ^ 2) :
    Real.log (2 + ((cubeFinset p c a₀ ×ˢ cubeFinset p' c' a₀').card : ℕ)) ≤
      (4 * (m : ℝ) + 1) * Real.log N := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hN3]
  have hc1 := card_cubeFinset_le (p := p) (c := c) ha₀
  have hc2 := card_cubeFinset_le (p := p') (c := c') ha₀'
  have hp1 : (a₀ + 1) ^ m ≤ ((N : ℝ) ^ 2) ^ m := pow_le_pow_left₀ (by positivity) h1 m
  have hp2 : (a₀' + 1) ^ m ≤ ((N : ℝ) ^ 2) ^ m := pow_le_pow_left₀ (by positivity) h2 m
  have hcard : (((cubeFinset p c a₀ ×ˢ cubeFinset p' c' a₀').card : ℕ) : ℝ) ≤
      (N : ℝ) ^ (4 * m) := by
    rw [Finset.card_product, Nat.cast_mul]
    calc ((cubeFinset p c a₀).card : ℝ) * ((cubeFinset p' c' a₀').card : ℝ)
        ≤ ((N : ℝ) ^ 2) ^ m * ((N : ℝ) ^ 2) ^ m :=
          mul_le_mul (hc1.trans hp1) (hc2.trans hp2) (Nat.cast_nonneg _)
            (pow_nonneg (pow_nonneg hN0.le 2) m)
      _ = (N : ℝ) ^ (4 * m) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (4 * m) := one_le_pow₀ (by linarith only [hN3])
  have h3 : 2 + (((cubeFinset p c a₀ ×ˢ cubeFinset p' c' a₀').card : ℕ) : ℝ) ≤
      (N : ℝ) ^ (4 * m + 1) := by
    rw [pow_succ]
    have h5 := mul_le_mul_of_nonneg_left hN3 (zero_le_one.trans hN1)
    linarith only [hcard, hN1, h5]
  have h4 : (0 : ℝ) < 2 + (((cubeFinset p c a₀ ×ˢ cubeFinset p' c' a₀').card : ℕ) : ℝ) :=
    add_pos_of_pos_of_nonneg two_pos (Nat.cast_nonneg _)
  refine (Real.log_le_log h4 h3).trans (le_of_eq ?_)
  rw [Real.log_pow]
  push_cast
  ring

/-- Twice `a ≤ (3/2) q`. -/
private theorem two_mul_le_three_mul {a q : ℝ} (h : a ≤ 3 / 2 * q) : 2 * a ≤ 3 * q := by
  linarith only [h]

/-- `2 ℓ^{δ/100−1/4} ≤ 3 N^{−1/9}` for `ℓ ≥ κN`, `N` large. -/
theorem exists_slope_threshold {κ : ℝ} (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (x δ : ℝ), 1 ≤ κ * N → κ * N ≤ x → δ ≤ 1 →
      2 * x ^ (δ / 100 - 1 / 4) ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) := by
  have hr : (0 : ℝ) < 6 / 25 - 1 / 9 := by norm_num
  have hε : 0 < 3 / 2 * κ ^ ((6 : ℝ) / 25) := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_rpow_neg_le hr hε
  refine ⟨N₀, fun N hN x δ h1 h2 hδ1 => ?_⟩
  have hκN : 0 < κ * N := by linarith only [h1]
  have hN0 : (0 : ℝ) < N := by
    by_contra hcon
    have h3 : (N : ℝ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg N)
    rw [h3] at hκN
    simp at hκN
  have hx : 1 ≤ x := h1.trans h2
  have h3 : x ^ (δ / 100 - 1 / 4) ≤ x ^ (-((6 : ℝ) / 25)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hδ1])
  have h4 : x ^ (-((6 : ℝ) / 25)) ≤ (κ * N) ^ (-((6 : ℝ) / 25)) :=
    Real.rpow_le_rpow_of_nonpos hκN h2 (by norm_num)
  have h5 : (κ * N) ^ (-((6 : ℝ) / 25)) = (κ ^ ((6 : ℝ) / 25))⁻¹ * (N : ℝ) ^ (-((6 : ℝ) / 25)) := by
    rw [Real.mul_rpow hκ.le hN0.le, Real.rpow_neg hκ.le]
  have h6 : (N : ℝ) ^ (-((6 : ℝ) / 25)) =
      (N : ℝ) ^ (-((6 : ℝ) / 25 - 1 / 9)) * (N : ℝ) ^ (-(1 : ℝ) / 9) := by
    rw [← Real.rpow_add hN0]; congr 1; norm_num
  have h7 := hN₀ N hN
  have hpow : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 9) := by positivity
  have hκi : 0 < (κ ^ ((6 : ℝ) / 25))⁻¹ := by positivity
  have h8 := mul_le_mul_of_nonneg_right h7 hpow
  have h9 := mul_le_mul_of_nonneg_left h8 hκi.le
  have e : (κ ^ ((6 : ℝ) / 25))⁻¹ * (3 / 2 * κ ^ ((6 : ℝ) / 25) * (N : ℝ) ^ (-(1 : ℝ) / 9)) =
      3 / 2 * (N : ℝ) ^ (-(1 : ℝ) / 9) := by field_simp
  rw [h6] at h5
  exact two_mul_le_three_mul (h3.trans (h4.trans (h5.le.trans (h9.trans e.le))))

/-- **Hölder off the good event, for `N` large**: the bound `hnum` of `normal_core`. -/
theorem hnum_of {q L η lg Cg CL Cη f : ℝ} {N : ℕ} (hq : 1 ≤ q) (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hCg : 0 < Cg) (hlg : 0 < lg) (hf : 0 ≤ f) (hLb : 1 + L ≤ CL * N)
    (hηb : η ≤ Cη * N) (hexp : 2 ^ (2 * q) * (CL ^ (2 * q) + 2 * (1 + f) * Cη ^ (2 * q)) * 2 *
      (N : ℝ) ^ (2 * q) * Real.exp (-(lg / Cg) ^ 2) ≤ 1) (hCL : 0 ≤ CL) (hCη : 0 ≤ Cη) :
    2 ^ (2 * q) * ((1 + L) ^ (2 * q) + 2 * (1 + f) * η ^ (2 * q)) *
      (2 * Real.exp (-(1 / (Cg / lg)) ^ 2)) ≤ 1 := by
  have hq2 : 0 ≤ 2 * q := by linarith only [hq]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e : 1 / (Cg / lg) = lg / Cg := by field_simp
  rw [e]
  have h1 : (1 + L) ^ (2 * q) ≤ CL ^ (2 * q) * (N : ℝ) ^ (2 * q) := by
    rw [← Real.mul_rpow hCL hN0]
    exact Real.rpow_le_rpow (by positivity) hLb hq2
  have h2 : η ^ (2 * q) ≤ Cη ^ (2 * q) * (N : ℝ) ^ (2 * q) := by
    rw [← Real.mul_rpow hCη hN0]
    exact Real.rpow_le_rpow hη hηb hq2
  have h3 : (1 + L) ^ (2 * q) + 2 * (1 + f) * η ^ (2 * q) ≤
      (CL ^ (2 * q) + 2 * (1 + f) * Cη ^ (2 * q)) * (N : ℝ) ^ (2 * q) := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * (1 + f))
    linarith only [this, h1]
  have h4 : 0 ≤ (2 : ℝ) ^ (2 * q) * (2 * Real.exp (-(lg / Cg) ^ 2)) := by positivity
  have h5 := mul_le_mul_of_nonneg_right h3 h4
  linarith only [h5, hexp]

/-- A number above finitely many others. -/
theorem exists_ge (l : List ℝ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ l, x ≤ C := by
  induction l with
  | nil => exact ⟨1, le_rfl, by simp⟩
  | cons a l ih =>
    obtain ⟨C, hC, h⟩ := ih
    refine ⟨max a C, hC.trans (le_max_right _ _), fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (h x hx).trans (le_max_right _ _)

/-- The constant `c₀` of the proof. -/
private theorem c₀_bounds {s k : ℝ} (hs : 1 ≤ s) (hk : 1 ≤ k) :
    0 < 1 / (2 ^ 16 * (512 * s * k)) ∧ 2 ^ 16 * (1 / (2 ^ 16 * (512 * s * k))) ≤ 1 ∧
      512 * s * k * (1 / (2 ^ 16 * (512 * s * k))) ≤ 1 := by
  have hs0 : 0 < s := by linarith only [hs]
  have hk0 : 0 < k := by linarith only [hk]
  have h1 : 1 ≤ 512 * s * k := by nlinarith only [hs, hk]
  refine ⟨by positivity, ?_, ?_⟩
  · have e : 2 ^ 16 * (1 / (2 ^ 16 * (512 * s * k))) = 1 / (512 * s * k) := by field_simp
    rw [e, div_le_one (by positivity)]; exact h1
  · have e : 512 * s * k * (1 / (2 ^ 16 * (512 * s * k))) = 1 / 2 ^ 16 := by field_simp
    rw [e]; norm_num

/-- The constant of the Hölder bound is positive. -/
private theorem holder_const_pos {q CL Cη f : ℝ} (hCL : 0 < CL) (hCη : 0 ≤ Cη) (hf : 0 ≤ f) :
    0 < 2 ^ (2 * q) * (CL ^ (2 * q) + 2 * (1 + f) * Cη ^ (2 * q)) * 2 := by
  positivity

/-- The twelve summands of the threshold. -/
private theorem le_of_sum_le {a b c d e f g h i j k l N : ℕ}
    (hN : a + b + c + d + e + f + g + h + i + j + k + l ≤ N) :
    a ≤ N ∧ b ≤ N ∧ c ≤ N ∧ d ≤ N ∧ e ≤ N ∧ f ≤ N ∧ g ≤ N ∧ h ≤ N ∧ i ≤ N ∧ j ≤ N ∧ k ≤ N ∧
      l ≤ N := by
  omega

/-- `√N ≤ κ N` once `N ≥ κ⁻²`. -/
private theorem sqrt_le_mul_of_ceil_le {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (h : ⌈1 / κ ^ 2⌉₊ ≤ N) :
    Real.sqrt N ≤ κ * N := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h3 : 1 / κ ^ 2 ≤ N := (Nat.le_ceil _).trans (Nat.cast_le.2 h)
  rw [div_le_iff₀ (by positivity)] at h3
  have hκ2 : 1 ≤ κ ^ 2 * N := by linarith only [h3, mul_comm (N : ℝ) (κ ^ 2)]
  rw [Real.sqrt_le_left (by positivity)]
  have e : (κ * N) ^ 2 = κ ^ 2 * N * N := by ring
  rw [e]
  exact le_mul_of_one_le_left hN0 hκ2

/-- The bound of the lengths of the geodesics, against `N`. -/
private theorem len_bound_le {Clen m T l N : ℝ} (hClen : 0 ≤ Clen) (hm : 0 ≤ m) (hT : 0 ≤ T)
    (hlN : l ≤ N) (hN : 1 ≤ N) :
    1 + Clen * (1 + (m + 1) * ((1 + T) * l)) ≤ (1 + Clen * (1 + (m + 1) * (1 + T))) * N := by
  have hmT : 0 ≤ (m + 1) * (1 + T) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hlN hmT
  have h3 : Clen * (1 + (m + 1) * ((1 + T) * l)) ≤ Clen * ((1 + (m + 1) * (1 + T)) * N) := by
    refine mul_le_mul_of_nonneg_left ?_ hClen
    have e : (1 + (m + 1) * (1 + T)) * N = N + (m + 1) * (1 + T) * N := by ring
    have e' : (m + 1) * ((1 + T) * l) = (m + 1) * (1 + T) * l := by ring
    linarith only [h1, hN, e, e']
  have e : (1 + Clen * (1 + (m + 1) * (1 + T))) * N =
      N + Clen * ((1 + (m + 1) * (1 + T)) * N) := by ring
  linarith only [h3, hN, e]

/-- From `x / Q ≤ C y` with `y ≤ 1`. -/
private theorem le_mul_of_div_le_mul {x Q C y : ℝ} (hC : 0 < C) (hQ : 0 < Q) (hy : y ≤ 1)
    (h : x / Q ≤ C * y) : x ≤ C * Q := by
  rw [div_le_iff₀ hQ] at h
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy hC.le) hQ.le
  rw [mul_one] at h3
  exact h.trans h3

/-- The constant of the lemma is at least `1`. -/
private theorem one_le_finalConst {T Cv Cp c₂ B τ q : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B) (hq : 1 ≤ q) :
    1 ≤ finalConst T Cv Cp c₂ B τ q := by
  unfold finalConst
  have h2 : (1 : ℝ) ≤ 2 ^ q := Real.one_le_rpow (by norm_num) (by linarith only [hq])
  have h3 : 0 ≤ 2 * (1 + ((Nat.ceil (q / 2)).factorial : ℝ)) *
      (2 * (1 + ((1 + T) * (2 + Real.sqrt (2 * (Cv + Cp) / c₂)) + B)) +
        (1 + T) * Real.sqrt (2 / c₂) * Real.sqrt τ) ^ q := by positivity
  nlinarith only [h2, h3]

end Loc

/-- **Lemma `lem:localization` for `|ū| ≤ d^{1/2}`.** The constants `C(b, p)` come before `κ` and
`K`; the thresholds after them. Every premise of the edge is used. -/
theorem normalStatement_of (hTree : TreeStatement m) (hProf : ProfilesStatement m)
    (hSupp : SupportStatement m) (hScales : ScalesStatement m) (hGood : GoodStatement m)
    (hCone : ConeStatement m) (hSlabs : SlabsStatement m) (hLen : GeodesicLengthStatement m)
    (hUnion : OsUnionStatement.{0, 0}) (hSum : SignedOsSumStatement.{0, 0}) :
    NormalStatement m := by
  intro bd hbd Cstar b hb q hq
  obtain ⟨cS, CS, r₁, hcS, hCS, hr₁, -, hSM⟩ := hSupp bd hbd
  obtain ⟨C₃, hC₃, hsc⟩ := hScales bd hbd Cstar
  obtain ⟨cg, Cg, hcg, hCg, NG, hgood⟩ := hGood bd hbd
  obtain ⟨Cc, hCc, Nc, hcone⟩ := hCone bd hbd Cg cg hCg hcg
  obtain ⟨Csl, hCsl, Nsl, hslab⟩ := hSlabs bd hbd Cg cg hCg hcg
  obtain ⟨Clen, hClen, hlen⟩ := hLen bd hbd
  obtain ⟨CT, hCT, htree⟩ := hTree bd hbd Cstar (8 * b) (by linarith only [hb])
  obtain ⟨CPb, hCPb, hprofb⟩ := hProf bd hbd Cstar b hb
  obtain ⟨CP, hCP, hprof⟩ := hProf bd hbd Cstar 512 (by norm_num)
  have hm1 : 1 ≤ m := hbd.law.one_le_m
  have hδ := hbd.law.delta_pos
  have hbdT := hbd.T_nonneg
  have hd1 : 1 ≤ Real.sqrt (m : ℝ) := Real.one_le_sqrt.mpr (Nat.one_le_cast.2 hm1)
  have hsm0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hb0 : 0 ≤ b := by linarith only [hb]
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = bd.T + 1 := ⟨_, rfl⟩
  have hT : 1 ≤ T := by linarith only [hbdT, hTdef]
  have hT0 : 0 ≤ T := by linarith only [hT]
  obtain ⟨κT, hκT1, hκT'⟩ : ∃ κT : ℕ, 1 ≤ κT ∧ 4 * (1 + T) + 1 / 2 ≤ (κT : ℝ) :=
    ⟨⌈4 * (1 + T) + 1 / 2⌉₊ + 1, Nat.le_add_left _ _,
      (Nat.le_ceil _).trans (Nat.cast_le.2 (Nat.le_succ _))⟩
  have hκTr : (1 : ℝ) ≤ κT := Nat.one_le_cast.2 hκT1
  obtain ⟨c₀, hc₀, hc₀1, hc₀2⟩ :
      ∃ c₀ : ℝ, 0 < c₀ ∧ 2 ^ 16 * c₀ ≤ 1 ∧ 512 * Real.sqrt m * κT * c₀ ≤ 1 :=
    ⟨_, c₀_bounds hd1 hκTr⟩
  obtain ⟨Bq, hBqdef⟩ : ∃ Bq : ℝ, Bq = Real.sqrt m * b + 1 := ⟨_, rfl⟩
  have hBq0 : 0 ≤ Bq := by
    rw [hBqdef]; exact add_nonneg (mul_nonneg hsm0 hb0) zero_le_one
  let Cv := 2 * (2 + T) ^ 2 * CS * Bq ^ 2 + 2 * CS
  let τ := 2 * CT + CPb + Real.logb 2 (1 + 2 * annuliSum m κT c₀ (cS / 8 / (16 * CP))) * (8 * CP)
  have hCb1 : 1 ≤ finalConst T Cv (2 * CS * C₃) (cS / 8) Bq τ q := one_le_finalConst hT0 hBq0 hq
  refine ⟨_, hCb1, fun κ hκ K hK => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hprofb κ hκ K hK
  obtain ⟨N₂, hN₂⟩ := hprof (κ / 32) (div_pos hκ (by norm_num)) K hK
  obtain ⟨N₃, hN₃⟩ := htree K hK
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℝ, Cs = Csl + 1 := ⟨_, rfl⟩
  have hCs1 : 1 ≤ Cs := by linarith only [hCsl, hCsdef]
  have hCsl2 : Csl ≤ Cs ^ 2 :=
    (by linarith only [hCsdef] : Csl ≤ Cs).trans (le_self_pow₀ hCs1 two_ne_zero)
  obtain ⟨K₁, hK₁, hK₁'⟩ : ∃ K₁ : ℝ, Cc ≤ K₁ ∧ (Cc / (aperture T / 2)) ^ 4 ≤ K₁ :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hK₁0 : 0 ≤ K₁ := hCc.le.trans hK₁
  let Cw := 1 + max Cstar 1 / Real.sqrt κ
  have hCw0 : 0 ≤ Cw :=
    add_nonneg zero_le_one (div_nonneg (zero_le_one.trans (le_max_right _ _)) (Real.sqrt_nonneg _))
  obtain ⟨ρ, hρ0, hρr, hρ1⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r₁ ∧ ρ ≤ 1 :=
    ⟨_, lt_min hr₁ one_pos, min_le_left _ _, min_le_right _ _⟩
  let C₀ := (3 + T) * rtd m
  obtain ⟨Ctot, hC1, hCl⟩ := exists_ge [4 * ((1 + T) * rtd m + 1), 2 * C₀, 256 * Real.sqrt m * κT,
    2 * (rtd m + K₁ * Cs ^ 2 + 1) / c₀, 64 * (K₁ * Cs ^ 2 + rtd m), Cw,
    5 * (Bq * Cw) + (1 + T) * (K₁ * Cs ^ 2) + slopeFactor T * Cc * (Cs * (2 * (1 + T)) + 4),
    64 / r₁, 4 * (2 + T) * Bq / ρ, 2 / ρ, 2 * Bq, 2, 4 * Cc / aperture T, Csl]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at hCl
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := hCl
  obtain ⟨N₄, hN₄⟩ := exists_base (C := Ctot) (κ := κ) (δ := bd.law.δ)
    (by linarith only [hC1]) hκ hδ
  obtain ⟨N₅, hN₅⟩ := exists_slope_threshold hκ
  let f : ℝ := ((Nat.ceil (2 * q / 1)).factorial : ℝ)
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  have h1T : 0 ≤ 1 + T := by linarith only [hT0]
  have hm1' : 0 ≤ (m : ℝ) + 1 := by linarith only [hm0]
  obtain ⟨CL, hCLdef⟩ : ∃ CL : ℝ, CL = 1 + Clen * (1 + ((m : ℝ) + 1) * (1 + T)) := ⟨_, rfl⟩
  have hCL1 : 0 < CL := by
    have := mul_nonneg hClen.le (add_nonneg zero_le_one (mul_nonneg hm1' h1T))
    linarith only [this, hCLdef]
  have hUC : 0 < unionConst hUnion * Clen := mul_pos (unionConst_pos hUnion) hClen
  have h4m : 0 < 4 * (m : ℝ) + 1 := by linarith only [hm0]
  obtain ⟨Cη, hCηdef⟩ : ∃ Cη : ℝ, Cη = unionConst hUnion * Clen * (4 * (m : ℝ) + 1) := ⟨_, rfl⟩
  have hCη0 : 0 ≤ Cη := by rw [hCηdef]; exact (mul_pos hUC h4m).le
  have h2q : 0 ≤ 2 * q := by linarith only [hq]
  obtain ⟨N₆, hN₆⟩ := exists_holder (K₀ := 2 ^ (2 * q) * (CL ^ (2 * q) +
    2 * (1 + f) * Cη ^ (2 * q)) * 2) (q := 2 * q) (C := Cg) (holder_const_pos hCL1 hCη0 hf0) h2q hCg
  obtain ⟨N₇, hN₇⟩ : ∃ N₇ : ℕ, ∀ N : ℕ, N₇ ≤ N → Real.sqrt N ≤ κ * N :=
    ⟨_, fun _ h => sqrt_le_mul_of_ceil_le hκ h⟩
  obtain ⟨N₈, hN₈⟩ : ∃ N₈ : ℕ, Real.sqrt m + T + 2 * rtd m + b + 1 ≤ N₈ := ⟨_, Nat.le_ceil _⟩
  refine ⟨NG + Nc + Nsl + N₁ + N₂ + N₃ + N₄ + N₅ + N₆ + N₇ + N₈ + 3, ?_⟩
  intro M hM hfit N hN A hA hprem hrange ℓ hκℓ hℓN t c c' a₀ a₀' ha₀ ha₀b ha₀' ha₀'b hcc hc ht
  obtain ⟨hNG, hNc, hNsl, hNN₁, hNN₂, hNN₃, hNN₄, hNN₅, hNN₆, hNN₇, hNN₈, hN3⟩ := le_of_sum_le hN
  have hδM : M.δ = bd.law.δ := hfit.δ_eq
  have hδ1 := hM.delta_le_one
  have hδ0 := hM.delta_pos
  have ht₀' := hfit.t₀_le
  have ht₀1 : ‖M.t₀‖ + 1 ≤ T := by linarith only [ht₀', hTdef]
  have hN2' : 2 ≤ N := Nat.le_of_succ_le hN3
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith only [hNr]
  have h1N : (1 : ℝ) ≤ N := by linarith only [hNr]
  have hsN : Real.sqrt N ≤ κ * N := hN₇ N hNN₇
  have hsN1 : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr h1N
  have hκN1 : 1 ≤ κ * N := hsN1.trans hsN
  have hN1 : Real.sqrt N ≤ ℓ := hsN.trans hκℓ
  have hℓr : (1 : ℝ) ≤ ℓ := hsN1.trans hN1
  have hℓ1 : 1 ≤ ℓ := by exact_mod_cast hℓr
  have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hℓr]
  have hℓNr : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓN
  let Λ := Real.log (2 + N)
  let lg := Real.log N
  have hΛ1 : 1 ≤ Λ := one_le_log_of_three_le (by linarith only [hNr])
  have hlg1 : 1 ≤ lg := one_le_log_of_three_le hNr
  have hlg0 : 0 < lg := by linarith only [hlg1]
  have hlgΛ : lg ≤ Λ := Real.log_le_log hN0 (by linarith only)
  have hbase : Ctot * Λ ^ 2 ≤ (ℓ : ℝ) ^ (M.δ / 200) := by
    rw [hδM]
    exact (hN₄ N hNN₄).trans (Real.rpow_le_rpow (mul_pos hκ hN0).le hκℓ (by linarith only [hδ]))
  have hend0 : 0 ≤ (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) := Real.rpow_nonneg hℓ0.le _
  have hend1 : (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hℓr (by linarith only [hδ1])
  have htT : ‖t‖ ≤ T := by
    have := norm_le_norm_sub_add t M.t₀
    linarith only [this, ht, hend1, ht₀', hTdef]
  obtain ⟨a, ha⟩ : ∃ a : Vertex m, ‖point a - (basePt 0 c - ((ℓ : ℝ) / 16) • slopeVec t)‖ ≤ rtd m :=
    ⟨_, round_le _⟩
  obtain ⟨a', ha'⟩ : ∃ a' : Vertex m,
      ‖point a' - (basePt (0 + ℓ) c' + ((ℓ : ℝ) / 16) • slopeVec t)‖ ≤ rtd m := ⟨_, round_le _⟩
  obtain ⟨ha₁, hao⟩ := end_left htT ha
  obtain ⟨ha₂, ha'o⟩ := end_right htT hcc ha'
  have ha₂' : |(a'.1 : ℝ) - (((0 : ℤ) : ℝ) + 17 * (ℓ : ℝ) / 16)| ≤ rtd m := by
    have e : ((0 : ℤ) : ℝ) + 17 * (ℓ : ℝ) / 16 = ((0 : ℤ) : ℝ) + ℓ + (ℓ : ℝ) / 16 := by ring
    rw [e]; exact ha₂
  have hd0 := rtd_nonneg m
  have hao' : ‖ofs t 0 c a‖ ≤ C₀ := hao.trans (mul_le_mul_of_nonneg_right
    (by linarith only) hd0)
  have hW := W_le_of_range hM hK hA hκ hrange hκℓ hℓN hΛ1
  have hΓ₀ : 2 * rtd m ≤ W M K A ℓ →
      Real.sqrt m * (b * W M K A ℓ) + 2 * rtd m ≤ Bq * W M K A ℓ := fun h2 => by
    have e : Bq * W M K A ℓ = Real.sqrt m * (b * W M K A ℓ) + W M K A ℓ := by
      rw [hBqdef, add_mul, one_mul, mul_assoc]
    rw [e]; linarith only [h2]
  have hpack : Pack M K A ℓ t 0 c a a' T c₀ C₀ κT ((ℓ : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 200))
      (K₁ * (Cs * lg) ^ 2) (2 * (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4)) lg (Cs * lg) K₁ Cc
      (Real.sqrt m * (b * W M K A ℓ) + 2 * rtd m) Bq r₁ ρ Csl :=
    pack_of_base hM hK hA hℓ1 ht ht₀1 hT hκT1 hκT' ha₁ ha₂' hao' ha'o
      hc₀ hc₀1 hc₀2 hC1 hΛ1 hlgΛ hlg1 hCs1 hK₁0 hCc hBq0 hr₁ hρ0 hCw0 hbase hW hΓ₀
      c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 hCsl.le
  have hcfg := hpack.cfg
  -- the good event
  obtain ⟨G, hGmono, hGos, hGgood⟩ := hgood M hM hfit N hNG
  have hS : lg ≤ Cs * lg := le_mul_of_one_le_left hlg0.le hCs1
  have hτN := hN₅ N hNN₅ ℓ M.δ hκN1 hκℓ hδ1
  have hℓ3 : (ℓ : ℝ) ≤ 3 * N := by linarith only [hℓNr, hN0]
  -- the boxes
  have hWD : W M K A ℓ ≤ ℓ := hcfg.hDW.trans hpack.hDℓ
  have hN8 : Real.sqrt m + T + 2 * rtd m + b + 1 ≤ N := hN₈.trans (Nat.cast_le.2 hNN₈)
  have hbW : b * W M K A ℓ ≤ b * N :=
    mul_le_mul_of_nonneg_left (hWD.trans hℓNr) hb0
  have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := le_self_pow₀ h1N two_ne_zero
  have hCN : (Real.sqrt m + T + 2 * rtd m + b + 1) * (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hN8 hN0.le
  have hcN : Real.sqrt m * 1 ≤ Real.sqrt m * N := mul_le_mul_of_nonneg_left h1N hsm0
  have hdN : rtd m * 1 ≤ rtd m * N := mul_le_mul_of_nonneg_left h1N hd0
  have hTN0 : 0 ≤ T * (N : ℝ) := mul_nonneg hT0 hN0.le
  have hdN0 : 0 ≤ rtd m * (N : ℝ) := mul_nonneg hd0 hN0.le
  have hsN0 : 0 ≤ Real.sqrt m * (N : ℝ) := mul_nonneg hsm0 hN0.le
  have eN : (Real.sqrt m + T + 2 * rtd m + b + 1) * (N : ℝ) =
      Real.sqrt m * N + T * N + 2 * (rtd m * N) + b * N + N := by ring
  have hRI : ‖c‖ + a₀ ≤ (N : ℝ) ^ 2 := by
    linarith only [hc, ha₀b, hbW, hCN, eN, hTN0, hdN0, hcN, hN0]
  have hbI : ∀ u ∈ transverseCube 0 c a₀, InBox ((N : ℝ) ^ 2) u := fun _ hu => box_left ha₀ hRI hu
  have hc'N : ‖c'‖ ≤ Real.sqrt m + T * ℓ + 2 * rtd m := by
    have e : c' = (c' - c - (ℓ : ℝ) • t) + c + (ℓ : ℝ) • t := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_add_le (c' - c - (ℓ : ℝ) • t) c
    rw [norm_smul, Real.norm_of_nonneg hℓ0.le]
    have h2 := mul_le_mul_of_nonneg_left htT hℓ0.le
    have hcc' : ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * rtd m := hcc
    linarith only [h1, h2, hc, hcc', mul_comm (ℓ : ℝ) T]
  have hTℓ : T * ℓ ≤ T * N := mul_le_mul_of_nonneg_left hℓNr hT0
  have hRI' : ‖c'‖ + a₀' ≤ (N : ℝ) ^ 2 := by
    linarith only [hc'N, ha₀'b, hbW, hCN, eN, hTℓ, hcN, hdN, hN0]
  have hℓN2 : (ℓ : ℝ) ≤ (N : ℝ) ^ 2 := hℓNr.trans hN2
  have hbI' : ∀ v ∈ transverseCube (0 + ℓ) c' a₀', InBox ((N : ℝ) ^ 2) v := fun _ hv =>
    box_right ha₀' hRI' hℓN2 hv
  have hΓu : ∀ u ∈ transverseCube 0 c a₀, ‖ofs t 0 c u‖ ≤
      Real.sqrt m * (b * W M K A ℓ) + 2 * rtd m := fun u hu => by
    have h1 := norm_ofs_left_le (t := t) ha₀ hu
    have h2 := mul_le_mul_of_nonneg_left ha₀b hsm0
    linarith only [h1, h2, hd0]
  have hΓv : ∀ v ∈ transverseCube (0 + ℓ) c' a₀', ‖ofs t 0 c v‖ ≤
      Real.sqrt m * (b * W M K A ℓ) + 2 * rtd m := fun v hv => by
    have h1 := norm_ofs_right_le ha₀' hcc hv
    have h2 := mul_le_mul_of_nonneg_left ha₀'b hsm0
    have e : Real.sqrt ((m : ℝ) + 1) = rtd m := rfl
    rw [e] at h1
    linarith only [h1, h2]
  -- the variable of the union, and the Hölder product
  have hη0 : 0 < unionConst hUnion * Clen * ((4 * (m : ℝ) + 1) * lg) :=
    mul_pos hUC (mul_pos h4m hlg0)
  have hcardb : ∀ a₁ : ℝ, a₁ ≤ b * W M K A ℓ → a₁ + 1 ≤ (N : ℝ) ^ 2 := fun a₁ h => by
    linarith only [h, hbW, hCN, eN, hTN0, hdN0, hsN0, hNr]
  have hη : unionConst hUnion * Clen * Real.log (2 + ((cubeFinset 0 c a₀ ×ˢ
      cubeFinset (0 + ℓ) c' a₀').card : ℕ)) ≤
      unionConst hUnion * Clen * ((4 * (m : ℝ) + 1) * lg) :=
    mul_le_mul_of_nonneg_left (log_card_le ha₀ ha₀' hN3 (hcardb _ ha₀b) (hcardb _ ha₀'b)) hUC.le
  have hlgN : lg ≤ N := Real.log_le_self hN0.le
  have hLb : 1 + Clen * (1 + ((m : ℝ) + 1) * ((1 + T) * ℓ)) ≤ CL * N := by
    rw [hCLdef]; exact len_bound_le hClen.le hm0 hT0 hℓNr h1N
  have hηb : unionConst hUnion * Clen * ((4 * (m : ℝ) + 1) * lg) ≤ Cη * N := by
    rw [hCηdef, mul_assoc (unionConst hUnion * Clen)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlgN h4m.le) hUC.le
  have hL0 : 0 ≤ Clen * (1 + ((m : ℝ) + 1) * ((1 + T) * ℓ)) :=
    mul_nonneg hClen.le (add_nonneg zero_le_one (mul_nonneg hm1' (mul_nonneg h1T hℓ0.le)))
  have hnum := hnum_of (f := f) hq hL0 hη0.le hCg hlg0 hf0 hLb hηb (hN₆ N hNN₆) hCL1.le hCη0
  -- the bound of equation `eq:scales`
  have hsN16 : Real.sqrt N / 16 ≤ ℓ := by linarith only [Real.sqrt_nonneg (N : ℝ), hN1]
  have ht3 : ‖t - M.t₀‖ ≤ 3 * (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) := by linarith only [ht, hend0]
  have hτ3 : (ℓ : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ C₃ * Q M K A ℓ :=
    le_mul_of_div_le_mul hC₃ hcfg.Q_pos
      (Real.rpow_le_one_of_one_le_of_nonpos hℓr (by linarith only [hδ0]))
      ((hsc K hK M hM hfit N hN2' A hA hrange ℓ hsN16).2 t ht3)
  by_cases hne : (transverseCube 0 c a₀).Nonempty ∧ (transverseCube (0 + ℓ) c' a₀').Nonempty
  · have hpair : IsCubePair M K A ℓ b t (transverseCube 0 c a₀) (transverseCube (0 + ℓ) c' a₀') :=
      ⟨0, c, c', a₀, a₀', rfl, rfl, ha₀, ha₀b, ha₀', ha₀'b, hcc⟩
    have hℓ2N : (ℓ : ℝ) ≤ 2 * N := by linarith only [hℓNr, hN0]
    have ht32 : ‖t - M.t₀‖ ≤ 3 / 2 * (ℓ : ℝ) ^ (M.δ / 100 - 1 / 4) := by linarith only [ht, hend0]
    have hshort := hN₁ M hM hfit N hNN₁ A hA hprem hrange ℓ t _ _ hpair
      (Or.inr ⟨hκℓ, hℓ2N, ht32⟩)
    have hprof' : ProfAt M K A N (κ / 32) CP := fun s t I I' hp h1 h2 h3 =>
      hN₂ M hM hfit N hNN₂ A hA hprem hrange s t I I' hp (Or.inr ⟨h1, h2, h3⟩)
    have hS1 : 1 ≤ Cs * lg := hlg1.trans hS
    have ht₀2 : ‖M.t₀‖ ≤ T := by linarith only [ht₀1]
    refine normal_core (κ := κ) (Csl := Csl) (Cs := Cs) hSum hUnion hM hK hA hℓ1 hℓN hκℓ hN1 hb0 hCT
      hCPb hCP hcS hCS hC₃ hCc hClen hq hBq0
      (hN₃ M hM hfit N hNN₃ A hA hprem hrange) hshort hprof'
      ((hSM M hM hfit).1) hτ3 (fun u v => hlen M hM hfit u v)
      (hGos lg le_rfl) (fun ω hω => hcone M hM hfit N hNc (Cs * lg) hS ω
        (hGgood _ hS ω (hGmono hS hω)))
      (fun ω hω u hu v hv => ?_) hpack ha ha' ha₀ ha₀b ha₀' ha₀'b hcc ht hbI hbI' hρr hρ1 hCsl2
      hCsl.le hK₁ hK₁' hS1 hlg0.le ht₀2 hℓ3 hτN hη0 hη hnum hne.1 hne.2
    obtain ⟨huv, hτ', -⟩ := slope_near (M := M) hℓ1 hu.1 hv.1 (hΓu u hu) (hΓv v hv) hpack.hτ
      hpack.hTT
    exact ((hslab M hM hfit N hNsl lg le_rfl ω (hGgood _ le_rfl ω hω) ℓ _ u v huv hℓ1 hℓ3
      (hτ'.trans hτN)).1 (hbI u hu) (hbI' v hv) hpack.hCsl).2
  · have hPprob := hM.probP
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (finalConst T Cv (2 * CS * C₃) (cS / 8) Bq τ q) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hCb1
    refine ⟨?_, ?_⟩
    · simp only [locRadius, deviation_eq_zero _ hne, ENNReal.zero_div, add_zero, ENNReal.one_rpow,
        lintegral_const, measure_univ, mul_one]
      exact h1
    · simp only [locRadiusSlab, deviation_eq_zero _ hne, ENNReal.zero_div, add_zero,
        ENNReal.one_rpow, lintegral_const, measure_univ, mul_one]
      exact h1

/-- The translation that normalizes a pair: `|c − ⌊c⌋| ≤ √m`. -/
theorem norm_sub_floor_le (c : EuclideanSpace ℝ (Fin m)) :
    ‖c - transversePoint fun j => ⌊c j⌋‖ ≤ Real.sqrt m := by
  have h := Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le
    (x := c - transversePoint fun j => ⌊c j⌋) (r := 1) zero_le_one fun j => by
      simp only [PiLp.sub_apply, Infra.FPP.transversePoint_apply]
      rw [abs_of_nonneg (sub_nonneg.2 (Int.floor_le _))]
      linarith only [Int.lt_floor_add_one (c j)]
  simpa using h

/-- **Stationarity**: Lemma `lem:localization` from its normalized form (the start of its proof). -/
theorem localizationStatement_of_normal (h : NormalStatement m) : LocalizationStatement m := by
  intro bd hbd Cstar b hb p hp
  obtain ⟨Cb, hCb, hC⟩ := h bd hbd Cstar b hb p hp
  have hCb0 : 0 < Cb := by linarith only [hCb]
  refine ⟨Cb, hCb0, fun κ hκ K hK => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hC κ hκ K hK
  refine ⟨N₀, ?_⟩
  intro M hM hfit N hN A hA hprem hrange ℓ hκℓ hℓN t I I' hpair ht
  obtain ⟨q, c, c', a₀, a₀', rfl, rfl, ha₀, ha₀b, ha₀', ha₀'b, hcc⟩ := hpair
  set z : Vertex m := (q, fun j => ⌊c j⌋) with hz
  set c₁ := c - transversePoint z.2 with hc₁
  set c₂ := c' - transversePoint z.2 with hc₂
  have hcc' : ‖c₂ - c₁ - (ℓ : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1) := by
    have e : c₂ - c₁ = c' - c := by simp only [hc₁, hc₂]; abel
    rw [e]; exact hcc
  have hb := hN₀ M hM hfit N hN A hA hprem hrange ℓ hκℓ hℓN t c₁ c₂ a₀ a₀' ha₀ ha₀b ha₀' ha₀'b hcc'
    (norm_sub_floor_le c) ht
  have hI : ∀ u ∈ transverseCube q c a₀, u - z ∈ transverseCube 0 c₁ a₀ := fun u hu => by
    have := sub_mem_transverseCube z hu
    simpa [hz] using this
  have hI' : ∀ v ∈ transverseCube (q + ℓ) c' a₀', v - z ∈ transverseCube (0 + ℓ) c₂ a₀' :=
    fun v hv => by
      have := sub_mem_transverseCube z hv
      simpa [hz] using this
  have hp0 : 0 ≤ p := by linarith only [hp]
  refine ⟨(lintegral_locRadius_le hM z hI hI' _ hp0).trans hb.1, fun q' hq' => ?_⟩
  by_cases hne : (transverseCube q c a₀).Nonempty
  · obtain ⟨u, hu⟩ := hne
    have hqq : q' = q := (hq' u hu).symm.trans hu.1
    subst hqq
    have h1 := lintegral_locRadiusSlab_le hM z hI hI' q' (q' + ℓ) (W M K A ℓ) hp0
    have e1 : q' - z.1 = 0 := by simp [hz]
    have e2 : q' + (ℓ : ℤ) - z.1 = 0 + ℓ := by simp [hz]
    rw [e1, e2] at h1
    exact h1.trans hb.2
  · have hPprob := hM.probP
    have hne' : ¬ ((transverseCube q c a₀).Nonempty ∧ (transverseCube (q + ℓ) c' a₀').Nonempty) :=
      fun h => hne h.1
    simp only [locRadiusSlab, deviation_eq_zero _ hne', ENNReal.zero_div, add_zero,
      ENNReal.one_rpow, lintegral_const, measure_univ, mul_one]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hCb

/-- **Lemma `lem:localization`**, with its proof: for the geodesics from `u` to `v`, and for the
geodesics in the slab between the hyperplanes of the cubes, `E[R^p] ≤ C(b, p)` for every `p ≥ 1`,
for `N` large depending only on `K`, `b`, `κ` and `p`. This is the proof of [AB26, Lemma 5.1] with
the three changes of the paper; see the module docstring. -/
theorem localizationStatement_of (hTree : TreeStatement m) (hProf : ProfilesStatement m)
    (hSupp : SupportStatement m) (hScales : ScalesStatement m) (hGood : GoodStatement m)
    (hCone : ConeStatement m) (hSlabs : SlabsStatement m) (hLen : GeodesicLengthStatement m)
    (hUnion : OsUnionStatement.{0, 0}) (hSum : SignedOsSumStatement.{0, 0}) :
    LocalizationStatement m :=
  localizationStatement_of_normal
    (normalStatement_of hTree hProf hSupp hScales hGood hCone hSlabs hLen hUnion hSum)

end CurvatureVariance.Paper.Localization
