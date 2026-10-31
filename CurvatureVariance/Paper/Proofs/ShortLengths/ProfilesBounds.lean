/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.ShortLengths.ShortParts
import CurvatureVariance.Paper.Proofs.Geometry.SupportSubgradient
import CurvatureVariance.Paper.Proofs.Moments.Basic
import CurvatureVariance.Paper.Proofs.Moments.Links
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proposition `prop:profiles` at one length

The proof of [AB26, Proposition 4.2] with the changes of the proof of Proposition
`prop:profiles` for `s ≤ N/2`.

The shape is that of `IsotropicVariance.Paper.Proofs.Profiles.profile_bounds_of` in the continuum
library, with its parameters `htree` and `hline`, and the steps are those of
`IsotropicVariance.Paper.Proofs.Profiles.profile_passTime`. On lattice points it is a triangle
inequality, with the paper's length `s/16`, the width `8b`, and the line a parameter.

The bound on the line is a parameter (`LineBound`), so that this one argument gives both cases of
the proposition: equation `eq:premise` for `s ≤ N/2`, equation `eq:parent` for `κN ≤ s ≤ 2N`, as
in the two proofs of Proposition `prop:profiles`. The tree bound is a hypothesis too, at the length
`s/16`, which is real.

The steps of the paper's proof, in `profile_bounds_of`:

* the points `ū ± (s/16)(1,t)` and `v̄ ± (s/16)(1,t)`, rounded to lattice points;
* the vectors between them have lengths `7s/8` and `9s/8` along `e₁` (`link_inner_eq`,
  `link_outer_eq`), and the parameter bounds them;
* `(sQ_s)^{1/2} ≤ 8(s/16 Q_{s/16})^{1/2}` (`W_le_eight_mul`), so Lemma `lem:tree` applies at `s/16`
  and `8b`, and bounds the four other terms;
* the thickenings by `s/1024` are those of Lemma `lem:tree` at `s/16`;
* the terms `ζ_t·(x' − x)` and `μ(x' − x)` add up to `ζ_t·(v − u)` up to `C Q_s`, and
  `0 ≤ μ(v − u) − ζ_t·(v − u) ≤ C(b) Q_s`, by equation `eq:support` and equation `eq:scales`
  (`cost_le_of_scales`), in `abs_passageTime_sub_le`;
* equation `eq:profiledifference` for the slab, since `log²N ≤ 100 Q_s`.

`abs_passageTime_sub_le` is the triangle inequality of the proof of [AB26, Proposition 4.2], with
`ζ_t` for `e₁`. `profileConclusion_of_parts` assembles the bounds, with the scale `Cl` of the line a
parameter. `cost_le_of_scales` is `cost_le_Q`, with the hypothesis `s|t − t₀|^{2+δ} ≤ Q_s`, from
equation `eq:scales`, in place of `|t − t₀| ≤ s^{…}`: the second case has slopes up to
`(3/2)s^{δ/100−1/4}`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Proofs.ShortLengths

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ### Powers of `s` -/

/-- `W_s ≤ 8 W_{s/16}` (the proof of Proposition `prop:profiles` for `s ≤ N/2`), since the exponent
of `sQ_s` is at most `3/2`. -/
theorem W_le_eight_mul {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A s : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) : W M K A s ≤ 8 * W M K A (s / 16) := by
  obtain ⟨hq1, hq2⟩ := Q_exp_bounds hM hK
  have h16 : (16 : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ 4 := by
    calc (16 : ℝ) ^ ((1 : ℝ) / 2 - M.δ / K) ≤ (16 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
      _ = ((4 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by norm_num
      _ = 4 := by rw [← Real.rpow_mul (by norm_num)]; norm_num
  have hrq : 0 ≤ (s / 16) ^ ((1 : ℝ) / 2 - M.δ / K) := by positivity
  have hQ : Q M K A s ≤ 4 * Q M K A (s / 16) := by
    calc Q M K A s = A * (16 ^ ((1 : ℝ) / 2 - M.δ / K) * (s / 16) ^ ((1 : ℝ) / 2 - M.δ / K)) := by
          unfold Q
          rw [← Real.mul_rpow (by norm_num) (by positivity), mul_div_cancel₀ s (by norm_num)]
      _ ≤ A * (4 * (s / 16) ^ ((1 : ℝ) / 2 - M.δ / K)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h16 hrq) hA
      _ = 4 * Q M K A (s / 16) := by unfold Q; ring
  have hQ0 : 0 ≤ Q M K A (s / 16) := Q_nonneg hA (by positivity)
  have h1 : s * Q M K A s ≤ 8 ^ 2 * ((s / 16) * Q M K A (s / 16)) := by
    calc s * Q M K A s ≤ s * (4 * Q M K A (s / 16)) := mul_le_mul_of_nonneg_left hQ hs
      _ = 8 ^ 2 * ((s / 16) * Q M K A (s / 16)) := by ring
  unfold W
  calc Real.sqrt (s * Q M K A s) ≤ Real.sqrt (8 ^ 2 * ((s / 16) * Q M K A (s / 16))) :=
        Real.sqrt_le_sqrt h1
    _ = 8 * Real.sqrt ((s / 16) * Q M K A (s / 16)) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

theorem fifteen_eighths_le_rpow : (15 / 8 : ℝ) ≤ 16 ^ ((6 : ℝ) / 25) := by
  calc (15 / 8 : ℝ) = ((15 / 8 : ℝ) ^ (25 : ℕ)) ^ (((25 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
    _ ≤ ((16 : ℝ) ^ (6 : ℕ)) ^ (((25 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) (by norm_num) (by positivity)
    _ = 16 ^ ((6 : ℝ) / 25) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num

/-- `(3/2) s^{δ/100−1/4} ≤ (4/5)(s/16)^{δ/100−1/4}`: the margin `(3/2)16^{δ/100−1/4} < 4/5` of the
proof of Proposition `prop:profiles` for `κN ≤ s ≤ 2N`. In the first case, with `4/5` on the left,
it is `4/5 ≤ 3/2`. -/
theorem slope_le_sixteen {δ s : ℝ} (hδ1 : δ ≤ 1) (hs : 0 < s) :
    3 / 2 * s ^ (δ / 100 - 1 / 4) ≤ 4 / 5 * (s / 16) ^ (δ / 100 - 1 / 4) := by
  set e := δ / 100 - 1 / 4 with he
  have h1 : (s / 16) ^ e = s ^ e * (16 : ℝ) ^ (-e) := by
    rw [Real.div_rpow hs.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]
  have h2 : (15 / 8 : ℝ) ≤ (16 : ℝ) ^ (-e) :=
    fifteen_eighths_le_rpow.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [he]; linarith only [hδ1]))
  have h3 : 0 ≤ s ^ e := by positivity
  rw [h1]
  nlinarith only [h2, h3]

/-! ### The cost, from equations `eq:support` and `eq:scales` -/

/-- **The cost at scale `s`**: for `v = λ(1, t) + w` with `|λ − s| ≤ s/4`, `|w| ≤ B W_s`,
`4 (2 + T) B W_s ≤ ρ s`, `T ≥ |t₀|`, `ρ ≤ min(r₁, 1)`, `|t − t₀| ≤ ρ/2` and
`s|t − t₀|^{2+δ} ≤ Q_s`: `μ(v) − ζ_t·v ≤ (2 (2 + T)² C B² + 2 C) Q_s`. As `cost_le_Q`, with the
last hypothesis in place of `|t − t₀| ≤ s^{δ/100−1/4}`. -/
theorem cost_le_of_scales {M : Model m} {K : ℕ} {A : ℝ} (hA : 1 ≤ A) {cS CS r₁ : ℝ}
    (hCS : 0 < CS)
    (h24 : ∀ t h : E, ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    {ρ T : ℝ} (hρ : ρ ≤ r₁) (hρ1 : ρ ≤ 1) (hTM : ‖M.t₀‖ ≤ T) {t : E} {P : Pt m}
    (hP : IsSubgradient M.μ (slopeVec t) P) {s : ℝ} (hs : 1 ≤ s) (htr : ‖t - M.t₀‖ ≤ ρ / 2)
    (hsQ : s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Q M K A s) {B lam : ℝ} {w v : Pt m}
    (hv : v = lam • slopeVec t + w) (hlam : |lam - s| ≤ s / 4) (hw : ‖w‖ ≤ B * W M K A s)
    (hBW : 4 * (2 + T) * B * W M K A s ≤ ρ * s) :
    M.μ.1 v - inner ℝ P v ≤ (2 * (2 + T) ^ 2 * CS * B ^ 2 + 2 * CS) * Q M K A s := by
  have hρ0 : 0 ≤ ρ := by linarith only [norm_nonneg (t - M.t₀), htr]
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hTM
  have htt : ‖t‖ ≤ T + 1 := by
    have h1 : ‖t - M.t₀‖ ≤ 1 := by linarith only [htr, hρ1]
    have h2 := norm_le_norm_sub_add t M.t₀
    linarith only [h1, h2, hTM]
  have hQ0 : 0 ≤ Q M K A s := Q_nonneg (by linarith only [hA]) (by linarith only [hs])
  have hW2 := W_sq (M := M) (K := K) (by linarith only [hA] : (0 : ℝ) ≤ A)
    (by linarith only [hs] : (0 : ℝ) ≤ s)
  have hBW0 : 0 ≤ B * W M K A s := (norm_nonneg w).trans hw
  have hBW' : (2 + T) * (B * W M K A s) ≤ ρ * s / 4 := by
    have : 4 * ((2 + T) * (B * W M K A s)) ≤ ρ * s := by linarith only [hBW]
    linarith only [this]
  have hws : ‖w‖ ≤ s / 8 := by
    have h1 : 2 * (B * W M K A s) ≤ (2 + T) * (B * W M K A s) :=
      mul_le_mul_of_nonneg_right (by linarith only [hT0]) hBW0
    nlinarith only [hw, hBW', h1, hρ1, hs, hρ0]
  have hvfst : v.fst = lam + w.fst := by
    rw [hv, WithLp.add_fst, WithLp.smul_fst]
    change lam * 1 + w.fst = lam + w.fst
    ring
  have hvsnd : v.snd = lam • t + w.snd := by
    rw [hv, WithLp.add_snd, WithLp.smul_snd]
    rfl
  have hwf := Geometry.abs_fst_le_norm w
  have hwsn := Geometry.norm_snd_le_norm w
  have hl := abs_le.mp hlam
  have hwf' := abs_le.mp hwf
  have hf1 : s / 2 ≤ v.fst := by rw [hvfst]; linarith only [hl.1, hwf'.1, hws, hs]
  have hf2 : v.fst ≤ 2 * s := by rw [hvfst]; linarith only [hl.2, hwf'.2, hws, hs]
  have hf0 : 0 < v.fst := by linarith only [hf1, hs]
  -- the transverse error `v₂ − v₁ t = w₂ − w₁ t`
  have hy : v.snd - v.fst • t = w.snd - w.fst • t := by
    rw [hvfst, hvsnd, add_smul]; abel
  have hyn : ‖v.snd - v.fst • t‖ ≤ (2 + T) * (B * W M K A s) := by
    rw [hy]
    have h1 := norm_sub_le w.snd (w.fst • t)
    have h2 : ‖w.fst • t‖ ≤ (T + 1) * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith only [hwf, htt, norm_nonneg t, abs_nonneg w.fst, norm_nonneg w]
    nlinarith only [h1, h2, hwsn, hw, hT0]
  -- the slope of `v` is within `r₁` of `t`
  have hv' : ‖v.snd - v.fst • t‖ ≤ r₁ * v.fst := by
    have h1 : ρ * s / 4 ≤ r₁ * v.fst := by nlinarith only [hρ, hρ0, hf1, hs]
    linarith only [h1, hyn, hBW']
  have hcost := Moments.cost_le_of_support h24 (htr.trans (by linarith only [hρ, hρ0])) hP hf0 hv'
  have h1 : CS * ‖v.snd - v.fst • t‖ ^ 2 / v.fst ≤ 2 * (2 + T) ^ 2 * CS * B ^ 2 * Q M K A s := by
    rw [div_le_iff₀ hf0]
    have h2 : ‖v.snd - v.fst • t‖ ^ 2 ≤ (2 + T) ^ 2 * B ^ 2 * (s * Q M K A s) := by
      rw [← hW2]
      calc ‖v.snd - v.fst • t‖ ^ 2 ≤ ((2 + T) * (B * W M K A s)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hyn 2
        _ = (2 + T) ^ 2 * B ^ 2 * W M K A s ^ 2 := by ring
    have h3 : 0 ≤ (2 + T) ^ 2 * CS * B ^ 2 * Q M K A s := by positivity
    nlinarith only [h2, h3, hf1, hCS]
  have h2 : CS * v.fst * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 2 * CS * Q M K A s := by
    have h4 : 0 ≤ ‖t - M.t₀‖ ^ (2 + M.δ) := by positivity
    have h5 : v.fst * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ 2 * (s * ‖t - M.t₀‖ ^ (2 + M.δ)) := by
      nlinarith only [hf2, h4]
    calc CS * v.fst * ‖t - M.t₀‖ ^ (2 + M.δ) = CS * (v.fst * ‖t - M.t₀‖ ^ (2 + M.δ)) := by ring
      _ ≤ CS * (2 * Q M K A s) :=
          mul_le_mul_of_nonneg_left (by linarith only [h5, hsQ]) hCS.le
      _ = 2 * CS * Q M K A s := by ring
  have hexp : (2 * (2 + T) ^ 2 * CS * B ^ 2 + 2 * CS) * Q M K A s =
      2 * (2 + T) ^ 2 * CS * B ^ 2 * Q M K A s + 2 * CS * Q M K A s := by ring
  rw [hexp]
  linarith only [hcost, h1, h2]

/-! ### The random variable -/

/-- **Assembly of the proposition.** The tree variables `X_I`, `X_{I'}` (for the endpoints `a, z` of
`I` and `z', a'` of `I'`), the two errors on the line, the variable of equation
`eq:profiledifference`, and the deterministic costs `≤ Cdet Q_s` give the bounds of equation
`eq:profiles`, with the scale `Cl` of the line a parameter. -/
theorem profileConclusion_of_parts {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {s : ℕ}
    {I I' U U' : Set (Vertex m)} (hIU : I ⊆ U) (hIU' : I' ⊆ U') {P : Pt m}
    (hsub : ∀ x, inner ℝ P x ≤ M.μ.1 x) {Ct Cl Cpd Cdet Cℓ : ℝ} (hCt : 0 < Ct) (hCl : 0 < Cl)
    (hCpd : 0 < Cpd) (hCdet : 0 ≤ Cdet) (hCℓ : 0 ≤ Cℓ) (hQ1 : 1 ≤ Q M K A s) {ℓ : ℝ}
    (hℓ : ℓ ≤ Cℓ * Q M K A s) {a z z' a' : Vertex m} {XI XI' Xpd : Config m → ℝ}
    (hXI : CurvatureVariance.IsOs M.P 1 (Ct * Q M K A s) XI)
    (hXI' : CurvatureVariance.IsOs M.P 1 (Ct * Q M K A s) XI')
    (hL₁ : CurvatureVariance.IsOs M.P 1 (Cl * Q M K A s)
      fun ω => |passageTimeReal ω z z' - M.μ.1 (point z' - point z)|)
    (hL₂ : CurvatureVariance.IsOs M.P 1 (Cl * Q M K A s)
      fun ω => |passageTimeReal ω a a' - M.μ.1 (point a' - point a)|)
    (hXpd : CurvatureVariance.IsOs M.P 1 Cpd Xpd)
    (hI : ∀ᵐ ω ∂M.P, ∀ u ∈ U, passageTimeReal ω a u - inner ℝ P (point u - point a) ≤ XI ω ∧
      passageTimeReal ω u z - inner ℝ P (point z - point u) ≤ XI ω)
    (hI' : ∀ᵐ ω ∂M.P, ∀ v ∈ U', passageTimeReal ω z' v - inner ℝ P (point v - point z') ≤ XI' ω ∧
      passageTimeReal ω v a' - inner ℝ P (point a' - point v) ≤ XI' ω)
    (hpd : ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I',
      (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v ∧
        slabTimeReal ω u.1 v.1 u v - passageTimeReal ω u v ≤ ℓ + Xpd ω)
    (hD : ∀ ω, ∀ u ∈ I, ∀ v ∈ I', slabTime ω u.1 v.1 u v ≠ ⊤)
    (hκ₁ : M.μ.1 (point z' - point z) - inner ℝ P (point z' - point z) ≤ Cdet * Q M K A s)
    (hκ₂ : ∀ u ∈ U, ∀ v ∈ U',
      M.μ.1 (point v - point u) - inner ℝ P (point v - point u) ≤ Cdet * Q M K A s) :
    ∃ X : Config m → ℝ,
      CurvatureVariance.IsOs M.P 1 ((2 * Ct + 2 * Cl + Cpd + 2 * (Cdet + Cℓ)) * Q M K A s) X ∧
      ∀ᵐ ω ∂M.P,
        (∀ u ∈ U, ∀ v ∈ U', |passageTimeReal ω u v - M.μ.1 (point v - point u)| ≤ X ω) ∧
        (∀ u ∈ I, ∀ v ∈ I',
          |slabTimeReal ω u.1 v.1 u v - M.μ.1 (point v - point u)| ≤ X ω) := by
  have := hM.probP
  have hQ0 : 0 < Q M K A s := by linarith only [hQ1]
  have hXpd' : CurvatureVariance.IsOs M.P 1 (Cpd * Q M K A s) (fun ω => max (Xpd ω) 0) := by
    have h : CurvatureVariance.IsOs M.P 1 Cpd (fun ω => max (Xpd ω) 0) := by
      refine ⟨hXpd.1.max aemeasurable_const, ?_⟩
      simp only [max_assoc, max_self]
      exact hXpd.2
    exact h.mono_scale zero_le_one hCpd (le_mul_of_one_le_right hCpd.le hQ1)
  have h1 := Moments.isOs_add hXI hXI' (by positivity) (by positivity)
  have h2 := Moments.isOs_add h1 hL₁ (by positivity) (by positivity)
  have h3 := Moments.isOs_add h2 hL₂ (by positivity) (by positivity)
  have h4 := Moments.isOs_add h3 hXpd' (by positivity) (by positivity)
  have h5 := Moments.isOs_add_const h4 (by positivity)
    (by positivity : 0 ≤ (Cdet + Cℓ) * Q M K A s)
  refine ⟨fun ω => XI ω + XI' ω + |passageTimeReal ω z z' - M.μ.1 (point z' - point z)| +
    |passageTimeReal ω a a' - M.μ.1 (point a' - point a)| + max (Xpd ω) 0 +
    (Cdet + Cℓ) * Q M K A s, ?_, ?_⟩
  · have heq : Ct * Q M K A s + Ct * Q M K A s + Cl * Q M K A s + Cl * Q M K A s +
        Cpd * Q M K A s + 2 * ((Cdet + Cℓ) * Q M K A s) =
        (2 * Ct + 2 * Cl + Cpd + 2 * (Cdet + Cℓ)) * Q M K A s := by ring
    rw [heq] at h5
    exact h5
  · filter_upwards [hI, hI', hpd] with ω hω1 hω2 hω3
    have hm1 : 0 ≤ max (Xpd ω) 0 := le_max_right _ _
    have hm2 : Xpd ω ≤ max (Xpd ω) 0 := le_max_left _ _
    have hcl : 0 ≤ Cℓ * Q M K A s := by positivity
    have hexp : (Cdet + Cℓ) * Q M K A s = Cdet * Q M K A s + Cℓ * Q M K A s := by ring
    have key : ∀ u ∈ U, ∀ v ∈ U', |passageTimeReal ω u v - M.μ.1 (point v - point u)| ≤
        XI ω + XI' ω + |passageTimeReal ω z z' - M.μ.1 (point z' - point z)| +
          |passageTimeReal ω a a' - M.μ.1 (point a' - point a)| + Cdet * Q M K A s :=
      fun u hu v hv => abs_passageTime_sub_le hsub ω (hω1 u hu).1 (hω1 u hu).2 (hω2 v hv).1
        (hω2 v hv).2 le_rfl le_rfl hκ₁ (hκ₂ u hu v hv)
    refine ⟨fun u hu v hv => ?_, fun u hu v hv => ?_⟩
    · have hk := key u hu v hv
      linarith only [hk, hm1, hexp, hcl]
    · have hk := key u (hIU hu) v (hIU' hv)
      have hs := abs_slabTimeReal_sub_le (hω3 u hu v hv).1 (hD ω u hu v hv) (hω3 u hu v hv).2 hk
      linarith only [hs, hm2, hexp, hℓ]

/-! ### The argument at one length -/

/-- **The bound on the line**: the input of `profile_bounds_of` that differs between the two cases
of the proposition, at the two lengths `7s/8` and `9s/8` along `e₁`, and with a transverse offset
`w` of at most `2√d`, the error in the slope of the pair: a pair of lattice points whose
displacement is `λ(1, t) + (0, w)` up to `√d` has `|T − μ| ≤ O₁(Cl Q_s)`. It stands for
equation `eq:premise` in the proof of Proposition `prop:profiles` for `s ≤ N/2`, and equation
`eq:parent` in its proof for `κN ≤ s ≤ 2N`. -/
def LineBound (M : Model m) (K : ℕ) (A : ℝ) (s : ℕ) (t : E) (Cl : ℝ) : Prop :=
  ∀ (x x' : Vertex m) (lam : ℝ) (w : E), (lam = 7 / 8 * s ∨ lam = 9 / 8 * s) →
    ‖w‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1) →
    ‖(point x' - point x) - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), w))‖ ≤
      Real.sqrt ((m : ℝ) + 1) →
    CurvatureVariance.IsOs M.P 1 (Cl * Q M K A s)
      fun ω => |passageTimeReal ω x x' - M.μ.1 (point x' - point x)|

/-- **Proposition `prop:profiles` at one length** (both proofs of the proposition): from Lemma
`lem:tree` at `s/16` and `8b`, the bound on the line, equation `eq:profiledifference` for the pair,
equation `eq:support` and equation `eq:scales`, in the form of the width margin
`4 (2 + T)(b + 4)√d W_s ≤ ρ s` and of `s|t − t₀|^{2+δ} ≤ Q_s`. The thresholds are hypotheses.

The shape is `IsotropicVariance.Paper.Proofs.Profiles.profile_bounds_of`, with its hypothesis
`htree` here and its `hline` as `LineBound`. -/
theorem profile_bounds_of {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 10 ^ 4 ≤ K) {A : ℝ}
    (hA : 1 ≤ A) {N : ℕ} (hN1 : 1 ≤ N) {b : ℝ} (hb : 1 ≤ b) {T cS CS r₁ ρ : ℝ} (hTM : ‖M.t₀‖ ≤ T)
    (hCS : 0 < CS)
    (h24 : ∀ t h : E, ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hρ : ρ ≤ r₁) (hρ1 : ρ ≤ 1) {Ct Cl Cpd : ℝ} (hCt : 0 < Ct) (hCl : 0 < Cl)
    (hCpd : 0 < Cpd) {s : ℕ} (hsN : Real.sqrt N ≤ s) (hs32 : (32 : ℝ) ≤ s) {t : E}
    (htρ : ‖t - M.t₀‖ ≤ ρ / 2)
    (hsQ : (s : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Q M K A s)
    {p : ℤ} {c c' : E} {a₀ a₀' : ℝ} (ha0 : 0 ≤ a₀) (ha0b : a₀ ≤ b * W M K A s)
    (ha0' : 0 ≤ a₀') (ha0'b : a₀' ≤ b * W M K A s)
    (hcc : ‖c' - c - (s : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1))
    (hBW : 4 * (2 + T) * ((b + 4) * Real.sqrt ((m : ℝ) + 1)) * W M K A s ≤ ρ * s)
    (htree : ∀ (q : ℤ) (z : E) (a₁ : ℝ), 0 ≤ a₁ → a₁ ≤ 8 * b * W M K A ((s : ℝ) / 16) →
      ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P → ∀ a a' : Vertex m,
      ‖point a - (WithLp.toLp 2 ((q : ℝ), z) - ((s : ℝ) / 16) • slopeVec t)‖ ≤
        Real.sqrt ((m : ℝ) + 1) →
      ‖point a' - (WithLp.toLp 2 ((q : ℝ), z) + ((s : ℝ) / 16) • slopeVec t)‖ ≤
        Real.sqrt ((m : ℝ) + 1) →
      ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (Ct * Q M K A ((s : ℝ) / 16)) X ∧ ∀ᵐ ω ∂M.P,
        ∀ u ∈ thicken (transverseCube q z a₁) t ((s : ℝ) / 16 / 64),
          passageTimeReal ω a u - inner ℝ P (point u - point a) ≤ X ω ∧
          passageTimeReal ω u a' - inner ℝ P (point a' - point u) ≤ X ω)
    (hline : LineBound M K A s t Cl)
    {Xpd : Config m → ℝ} (hXpd : CurvatureVariance.IsOs M.P 1 Cpd Xpd)
    (hpd : ∀ᵐ ω ∂M.P, ∀ u ∈ transverseCube p c a₀, ∀ v ∈ transverseCube (p + s) c' a₀',
      (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v ∧
        slabTimeReal ω u.1 v.1 u v - passageTimeReal ω u v ≤ Cpd * Real.log N ^ 2 + Xpd ω) :
    ShortConclusion M K A s (2 * Ct + 2 * Cl + Cpd + 2 * (2 * (2 + T) ^ 2 * CS * ((b + 4) *
      Real.sqrt ((m : ℝ) + 1)) ^ 2 + 2 * CS + 100 * Cpd)) t (transverseCube p c a₀)
      (transverseCube (p + s) c' a₀') := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hTM
  have hsq1 : 1 ≤ Real.sqrt ((m : ℝ) + 1) :=
    Real.one_le_sqrt.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) m])
  have hsqm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith only [])
  set B : ℝ := (b + 4) * Real.sqrt ((m : ℝ) + 1) with hB
  have hs1 : (1 : ℝ) ≤ s := by linarith only [hs32]
  have hs0 : (0 : ℝ) ≤ s := by linarith only [hs1]
  have hs2 : 2 ≤ s := by exact_mod_cast (show (2 : ℝ) ≤ s by linarith only [hs32])
  have hA0 : (0 : ℝ) ≤ A := by linarith only [hA]
  have hW1 := one_le_W hM hK hA hs1
  have hQ1 := one_le_Q hM hK hA hs1
  have hB3 : 3 * Real.sqrt ((m : ℝ) + 1) ≤ B := by
    have := mul_le_mul_of_nonneg_right (by linarith only [hb] : (3 : ℝ) ≤ b + 4)
      (Real.sqrt_nonneg ((m : ℝ) + 1))
    linarith only [this]
  have hBW1 : B ≤ B * W M K A s := le_mul_of_one_le_right (by positivity) hW1
  -- the length `r = s/16` of Lemma `lem:tree`, a real number
  set r : ℝ := (s : ℝ) / 16 with hr
  have hr1 : (1 : ℝ) ≤ r := by rw [hr]; linarith only [hs32]
  have hr0 : (0 : ℝ) ≤ r := by linarith only [hr1]
  have hrs : r ≤ s := by rw [hr]; linarith only [hs0]
  -- the widths
  have hWsr := W_le_eight_mul hM hK hA0 hs0
  rw [← hr] at hWsr
  have hwr : ∀ x : ℝ, x ≤ b * W M K A s → x ≤ 8 * b * W M K A r := fun x hx => by
    calc x ≤ b * W M K A s := hx
      _ ≤ b * (8 * W M K A r) := mul_le_mul_of_nonneg_left hWsr (by linarith only [hb])
      _ = 8 * b * W M K A r := by ring
  obtain ⟨P, hP⟩ := Geometry.exists_isSubgradient M.μ (slopeVec t)
  have hround : ∀ Z : Pt m, ‖point (Moments.roundVertex Z) - Z‖ ≤ Real.sqrt ((m : ℝ) + 1) :=
    fun Z => (Moments.norm_point_roundVertex_sub_le Z).trans (by linarith only [hsq1])
  -- Lemma `lem:tree` on `I` and on `I'`
  obtain ⟨XI, hXI, hXIae⟩ := htree p c a₀ ha0 (hwr a₀ ha0b) P hP
    (Moments.roundVertex (WithLp.toLp 2 ((p : ℝ), c) - r • slopeVec t))
    (Moments.roundVertex (WithLp.toLp 2 ((p : ℝ), c) + r • slopeVec t)) (hround _) (hround _)
  obtain ⟨XI', hXI', hXI'ae⟩ := htree (p + s) c' a₀' ha0' (hwr a₀' ha0'b) P hP
    (Moments.roundVertex (WithLp.toLp 2 ((((p + s : ℤ)) : ℝ), c') - r • slopeVec t))
    (Moments.roundVertex (WithLp.toLp 2 ((((p + s : ℤ)) : ℝ), c') + r • slopeVec t))
    (hround _) (hround _)
  -- the two vectors between the points
  have hlinkI := norm_round_link_le (link_inner_eq p s c c' t r)
  have hlinkO := norm_round_link_le (link_outer_eq p s c c' t r)
  set a := Moments.roundVertex (WithLp.toLp 2 ((p : ℝ), c) - r • slopeVec t) with ha
  set z := Moments.roundVertex (WithLp.toLp 2 ((p : ℝ), c) + r • slopeVec t) with hz
  set z' := Moments.roundVertex (WithLp.toLp 2 ((((p + s : ℤ)) : ℝ), c') - r • slopeVec t)
    with hz'
  set a' := Moments.roundVertex (WithLp.toLp 2 ((((p + s : ℤ)) : ℝ), c') + r • slopeVec t)
    with ha'
  have hL₁ := hline z z' _ _ (Or.inl (by rw [hr]; ring)) hcc hlinkI
  have hL₂ := hline a a' _ _ (Or.inr (by rw [hr]; ring)) hcc hlinkO
  -- the tree variables at the scale `Q_s`
  have hQr1 := one_le_Q hM hK hA hr1
  have hQrs : Ct * Q M K A r ≤ Ct * Q M K A s :=
    mul_le_mul_of_nonneg_left (Q_le_Q hM hK hA0 hr0 hrs) hCt.le
  have hXIs := hXI.mono_scale zero_le_one (by positivity) hQrs
  have hXI's := hXI'.mono_scale zero_le_one (by positivity) hQrs
  have hthick : (s : ℝ) / 1024 = r / 64 := by rw [hr]; ring
  have hXIae' : ∀ᵐ ω ∂M.P, ∀ u ∈ thicken (transverseCube p c a₀) t ((s : ℝ) / 1024),
      passageTimeReal ω a u - inner ℝ P (point u - point a) ≤ XI ω ∧
      passageTimeReal ω u z - inner ℝ P (point z - point u) ≤ XI ω := by
    rw [hthick]; exact hXIae
  have hXI'ae' : ∀ᵐ ω ∂M.P, ∀ v ∈ thicken (transverseCube (p + s) c' a₀') t ((s : ℝ) / 1024),
      passageTimeReal ω z' v - inner ℝ P (point v - point z') ≤ XI' ω ∧
      passageTimeReal ω v a' - inner ℝ P (point a' - point v) ≤ XI' ω := by
    rw [hthick]; exact hXI'ae
  -- the deterministic costs
  have hκ₁ : M.μ.1 (point z' - point z) - inner ℝ P (point z' - point z) ≤
      (2 * (2 + T) ^ 2 * CS * B ^ 2 + 2 * CS) * Q M K A s := by
    obtain ⟨w₁, hw₁, hw₁n⟩ := exists_decomp_of_link hlinkI
    exact cost_le_of_scales hA hCS h24 hρ hρ1 hTM hP hs1 htρ hsQ hw₁
      (abs_le.mpr ⟨by rw [hr]; linarith only [hs0], by rw [hr]; linarith only [hs0]⟩)
      (by linarith only [hB3, hBW1, hcc, hw₁n]) hBW
  have hκ₂ : ∀ u ∈ thicken (transverseCube p c a₀) t ((s : ℝ) / 1024),
      ∀ v ∈ thicken (transverseCube (p + s) c' a₀') t ((s : ℝ) / 1024),
      M.μ.1 (point v - point u) - inner ℝ P (point v - point u) ≤
        (2 * (2 + T) ^ 2 * CS * B ^ 2 + 2 * CS) * Q M K A s := by
    intro u hu v hv
    obtain ⟨lam, w, hvw, hlam, hwn⟩ := exists_decomp_of_thicken ha0 ha0' ha0b ha0'b hcc hu hv
    have hwB : Real.sqrt m * (b * W M K A s) + 4 * Real.sqrt ((m : ℝ) + 1) ≤ B * W M K A s := by
      have h1 := mul_le_mul_of_nonneg_right hsqm
        (by positivity : 0 ≤ b * W M K A s)
      have h2 : 4 * Real.sqrt ((m : ℝ) + 1) ≤ 4 * Real.sqrt ((m : ℝ) + 1) * W M K A s :=
        le_mul_of_one_le_right (by positivity) hW1
      have h3 : B * W M K A s = Real.sqrt ((m : ℝ) + 1) * (b * W M K A s) +
          4 * Real.sqrt ((m : ℝ) + 1) * W M K A s := by rw [hB]; ring
      linarith only [h1, h2, h3]
    exact cost_le_of_scales hA hCS h24 hρ hρ1 hTM hP hs1 htρ hsQ hvw
      (hlam.trans (by linarith only [hs0])) (hwn.trans hwB) hBW
  -- the slab passage time is finite
  have hD : ∀ ω, ∀ u ∈ transverseCube p c a₀, ∀ v ∈ transverseCube (p + s) c' a₀',
      slabTime ω u.1 v.1 u v ≠ ⊤ := fun ω u hu v hv =>
    slabTime_ne_top ω (by rw [hu.1, hv.1]; omega)
  have hℓ : Cpd * Real.log N ^ 2 ≤ 100 * Cpd * Q M K A s := by
    have := mul_le_mul_of_nonneg_left (log_sq_le_Q hM hK hA hN1 hsN) hCpd.le
    linarith only [this]
  exact profileConclusion_of_parts hM (fun u hu => mem_thicken_of_mem (by positivity) hu)
    (fun u hu => mem_thicken_of_mem (by positivity) hu) hP.2 hCt hCl hCpd (by positivity)
    (by positivity) hQ1 hℓ hXIs hXI's hL₁ hL₂ hXpd hXIae' hXI'ae' hpd hD hκ₁ hκ₂

end CurvatureVariance.Paper.Proofs.ShortLengths
