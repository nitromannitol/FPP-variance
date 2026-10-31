/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.Links
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes
import CurvatureVariance.Paper.Proofs.ShortLengths.Cubes

/-!
# The links of generation `j` in the chaining of equation `eq:tree`

The proof of Lemma `lem:tree`. For the chain points `φ j u = chainPoint … j u` of
`CurvatureVariance.Paper.Proofs.Moments.Shear` (base point `a` within `√d` of
`(p, c) + sg · r (1, t)`, `sg = ±1`), the link of generation `j` has
longitudinal length `λ ∈ [(29/32) r/2^{j+1}, (35/32) r/2^{j+1}]` and transverse deviation at most
`√m (3/2) R₂/2^j` from the slope `t`. The rounding of its endpoints costs the slack
`ε₁ = (2 + T)√d` for a bound `T ≥ |t₀|` (`roundSlack`): the displacement moves by at most
`ε₀ = 2√d`, and the longitudinal error tilts the transverse deviation by at most
`ε₀|t| ≤ ε₀(1 + |t₀|)`. Under the margin `12 √m R₂ ≤ (1 − θ) r^{3/4+δ/100}`, a slope
`|t − t₀| ≤ 1` and a minimal link length `L₁` (so that the slack keeps the strict margin of every
link), the premise, equation `eq:premise`,
bounds its error by `O₁(Q_{r/2^j})` (`chain_link_bounds`), and equation `eq:support` bounds its
cost by `C (2 (√m (3/2) R₂/2^j)² + 8 ε₁²) 2^{j+3}/r + C (r/2^j) |t − t₀|^{2+δ}`.

* `Q_pos`, `Q_mono`: the scale `Q_s` is positive and nondecreasing in `s`.
* `cost_of_disp`: equation `eq:support` for a displacement `λ(1, t) + (0, ω)` up to `ε₀`.
* `link_bounds`: both bounds for one link from its displacement.
* `chain_link_bounds`: both bounds for the links of generation `j`, in both orientations
  (`sg = −1`: from `a` to the cube; `sg = 1`: from the cube to `a`, with `P` replaced by `−P`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem Q_pos (M : Model m) (K : ℕ) {A s : ℝ} (hA : 0 < A) (hs : 0 < s) : 0 < Q M K A s := by
  unfold Q; positivity

theorem Q_mono (M : Model m) (K : ℕ) {A s s' : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) (hss : s ≤ s')
    (he : 0 ≤ (1 : ℝ) / 2 - M.δ / K) : Q M K A s ≤ Q M K A s' := by
  unfold Q; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hss he) hA

/-- The exponent of `Q` is nonnegative for `K ≥ 2`. -/
theorem Q_exponent_nonneg {M : Model m} (hM : M.Standing) {K : ℕ} (hK : 2 ≤ K) :
    0 ≤ (1 : ℝ) / 2 - M.δ / K := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 := hM.delta_le_one
  rw [sub_nonneg, div_le_iff₀ (by linarith only [hKr])]
  nlinarith only [h1, hKr, hM.delta_pos]

/-- The rounding slack `ε₁ = (2 + T)√d` of a link, for a bound `T ≥ |t₀|` (the module
docstring). -/
noncomputable def roundSlack (m : ℕ) (T : ℝ) : ℝ :=
  (2 + T) * Real.sqrt ((m : ℝ) + 1)

theorem one_le_roundSlack (m : ℕ) {T : ℝ} (hT : 0 ≤ T) : 1 ≤ roundSlack m T := by
  have h1 : 1 ≤ Real.sqrt ((m : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; linarith only [Nat.cast_nonneg (α := ℝ) m]
  unfold roundSlack
  nlinarith only [h1, hT]

/-- `‖t‖ ≤ 1 + |t₀|` on the slopes `|t − t₀| ≤ 1`. -/
theorem norm_le_of_norm_sub_le_one {M : Model m} {t : E} (ht1 : ‖t - M.t₀‖ ≤ 1) :
    ‖t‖ ≤ 1 + ‖M.t₀‖ := by
  have := norm_le_norm_sub_add t M.t₀
  linarith only [this, ht1]

/-- The cost bound, equation `eq:support`, for a displacement `v = λ(1,t) + (0,ω)` up to `ε₀`,
`λ > 2ε₀`, with `|t − t₀| ≤ 1`:
`μ(v) − P_t·v ≤ C(|ω| + (2 + |t₀|)ε₀)²/(λ/2) + C(λ + ε₀)|t − t₀|^{2+δ}`. -/
theorem cost_of_disp {M : Model m} {cS CS r₁ : ℝ}
    (h24 : ∀ t h : E, ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hCS : 0 < CS) {t : E} (ht1 : ‖t - M.t₀‖ ≤ 1) (ht : ‖t - M.t₀‖ ≤ r₁) {P : Pt m}
    (hP : IsSubgradient M.μ (slopeVec t) P) {v : Pt m} {ω : E} {lam ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (hdisp : ‖v - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))‖ ≤ ε₀)
    (hlam : 2 * ε₀ < lam) (hsmall : (‖ω‖ + (2 + ‖M.t₀‖) * ε₀) / (lam / 2) ≤ r₁) :
    M.μ.1 v - inner ℝ P v ≤
      CS * (‖ω‖ + (2 + ‖M.t₀‖) * ε₀) ^ 2 / (lam / 2) +
        CS * (lam + ε₀) * ‖t - M.t₀‖ ^ (2 + M.δ) := by
  set z := v - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω)) with hz
  have hzf : z.fst = v.fst - lam := by
    rw [hz, WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst]
    change v.fst - (lam * 1 + 0) = _; ring
  have hzs : z.snd = v.snd - (lam • t + ω) := by
    rw [hz, WithLp.sub_snd, WithLp.add_snd, WithLp.smul_snd]; rfl
  have h1 : |v.fst - lam| ≤ ε₀ := by
    rw [← hzf]; exact (Proofs.Geometry.abs_fst_le_norm z).trans hdisp
  have h2 : ‖v.snd - (lam • t + ω)‖ ≤ ε₀ := by
    rw [← hzs]; exact (Proofs.Geometry.norm_snd_le_norm z).trans hdisp
  have h1' := abs_le.mp h1
  have hlam2 : 0 < lam / 2 := by linarith only [hlam, hε₀]
  have hvf : lam / 2 ≤ v.fst := by linarith only [h1'.1, hlam]
  have hvf0 : 0 < v.fst := by linarith only [hvf, hlam2]
  have hdev : ‖v.snd - v.fst • t‖ ≤ ‖ω‖ + (2 + ‖M.t₀‖) * ε₀ := by
    have hdecomp : v.snd - v.fst • t = (v.snd - (lam • t + ω)) + ω + (lam - v.fst) • t := by
      rw [sub_smul]; abel
    rw [hdecomp]
    have e1 := norm_add₃_le (a := v.snd - (lam • t + ω)) (b := ω) (c := (lam - v.fst) • t)
    have e2 : ‖(lam - v.fst) • t‖ ≤ ε₀ * (1 + ‖M.t₀‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul h1 (norm_le_of_norm_sub_le_one ht1) (norm_nonneg _) hε₀
    linarith only [e1, e2, h2]
  have hsmall' : ‖v.snd - v.fst • t‖ ≤ r₁ * v.fst := by
    have h3 : ‖v.snd - v.fst • t‖ / v.fst ≤ (‖ω‖ + (2 + ‖M.t₀‖) * ε₀) / (lam / 2) :=
      div_le_div₀ (by positivity) hdev hlam2 hvf
    rw [← div_le_iff₀ hvf0]
    exact h3.trans hsmall
  refine (cost_le_of_support h24 ht hP hvf0 hsmall').trans ?_
  apply add_le_add
  · rw [mul_div_assoc, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hCS.le
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hdev 2) hlam2 hvf
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith only [h1'.2]) hCS.le

/-- **One link.** If the displacement of `x' − x` is `λ(1, t) + (0, ω)` up to `ε₀`, with the slope
and transverse margins in equation `eq:premise`, `|t − t₀| ≤ min(1, r₁)` and
`(|ω| + (2 + |t₀|)ε₀)/(λ/2) ≤ r₁`, then the link error is `O₁(Q_{λ+ε₀})` and the link cost is at
most `C(|ω| + (2 + |t₀|)ε₀)²/(λ/2) + C(λ + ε₀)|t − t₀|^{2+δ}`. -/
theorem link_bounds {M : Model m} (hM : M.Standing) {cS CS r₁ : ℝ}
    (h24 : ∀ t h : E, ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hCS : 0 < CS) {K : ℕ} (hK : 2 ≤ K) {A : ℝ} (hA : 1 ≤ A) {N : ℕ} (hPrem : Premise M K A N)
    {t : E} (ht1 : ‖t - M.t₀‖ ≤ 1) (ht : ‖t - M.t₀‖ ≤ r₁) {P : Pt m}
    (hP : IsSubgradient M.μ (slopeVec t) P) {x x' : Vertex m} {ω : E} {lam ε₀ θ : ℝ}
    (hε₀ : 1 ≤ ε₀)
    (hdisp : ‖(point x' - point x) - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))‖ ≤ ε₀)
    (hlam : 2 * ε₀ + 1 ≤ lam) (hlamN : lam + ε₀ ≤ 2 * (N : ℝ) / 3)
    (hslope : lam * ‖t - M.t₀‖ ≤ θ * lam ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hmargin : ‖ω‖ + (2 + ‖M.t₀‖) * ε₀ ≤ (1 - θ) * lam ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hsmall : (‖ω‖ + (2 + ‖M.t₀‖) * ε₀) / (lam / 2) ≤ r₁) :
    IsOs M.P 1 (Q M K A (lam + ε₀)) (fun ω' => linkError M ω' x x') ∧
      linkCost M P x x' ≤
        CS * (‖ω‖ + (2 + ‖M.t₀‖) * ε₀) ^ 2 / (lam / 2) +
          CS * (lam + ε₀) * ‖t - M.t₀‖ ^ (2 + M.δ) := by
  have heQ := Q_exponent_nonneg hM hK
  obtain ⟨s, -, hslam, habs⟩ := exists_premise_link hM hPrem hε₀ hdisp
    (by linarith only [hlam, hε₀]) hlamN hslope hmargin
  have hslam' := abs_le.mp hslam
  have hs0 : (0 : ℝ) < s := by linarith only [hslam'.1, hlam, hε₀]
  have hA0 : (0 : ℝ) < A := by linarith only [hA]
  refine ⟨?_, ?_⟩
  · have h := isAbsOs_upper habs zero_le_one (Q_pos M K hA0 hs0)
    exact h.mono_scale zero_le_one (Q_pos M K hA0 hs0)
      (Q_mono M K hA0.le hs0.le (by linarith only [hslam'.2]) heQ)
  · unfold linkCost
    exact cost_of_disp h24 hCS ht1 ht hP (by linarith only [hε₀]) hdisp
      (by linarith only [hlam, hε₀]) hsmall

/-- The numeric facts about a link of generation `j` used in `chain_link_bounds`. -/
theorem link_numeric {M : Model m} (hM : M.Standing) {r₁ r R₂ θ lam L₁ H ε₀ Ω : ℝ} {j : ℕ}
    (hr₁ : 0 < r₁) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε₀ : 1 ≤ ε₀) (hR₂ : 0 < R₂) (hr : 0 < r)
    (hH : H = r / 2 ^ (j + 1)) (hHL : L₁ ≤ H)
    (hL₁ : 2 * ε₀ + 1 ≤ 29 / 32 * L₁ ∧ (4 * ε₀ / (1 - θ)) ^ 2 ≤ 29 / 32 * L₁ ∧
      (4 / r₁) ^ 5 ≤ 29 / 32 * L₁)
    (hmarg : 12 * Real.sqrt m * R₂ ≤ (1 - θ) * r ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hlam : |lam - H| ≤ 3 / 32 * H) (hΩ : Ω ≤ Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j))) :
    2 * ε₀ + 1 ≤ lam ∧ lam + ε₀ ≤ r / 2 ^ j ∧ r / 2 ^ (j + 3) ≤ lam / 2 ∧
      Ω + 2 * ε₀ ≤ (1 - θ) * lam ^ ((3 : ℝ) / 4 + M.δ / 100) ∧
      (Ω + 2 * ε₀) / (lam / 2) ≤ r₁ / 2 := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  set e : ℝ := (3 : ℝ) / 4 + M.δ / 100 with he
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hH2 : r / 2 ^ j = 2 * H := by rw [hH, pow_succ]; field_simp
  have hH3 : r / 2 ^ (j + 3) = H / 4 := by rw [hH]; ring
  obtain ⟨hL1, hL2, hL3⟩ := hL₁
  have hlam' := abs_le.mp hlam
  have hlamlo : 29 / 32 * H ≤ lam := by linarith only [hlam'.1]
  have hlam1 : 2 * ε₀ + 1 ≤ lam := by linarith only [hL1, hlamlo, hHL]
  have hlampos : 0 < lam := by linarith only [hlam1, hε₀]
  have hlam1' : 1 ≤ lam := by linarith only [hlam1, hε₀]
  refine ⟨hlam1, ?_, ?_, ?_⟩
  · rw [hH2]; linarith only [hlam'.2, hlamlo, hlam1, hHL, hL1, hε₀]
  · rw [hH3]; linarith only [hlamlo, hHL, hL1, hε₀]
  -- the transverse margin
  have hmθ : 0 < 1 - θ := by linarith only [hθ1]
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by rw [he]; linarith only [hδ1]
  -- `λ^e ≥ r^e / 2^{j+2}`
  have hlamq : r / 2 ^ (j + 2) ≤ lam := by
    have : r / 2 ^ (j + 2) = H / 2 := by rw [hH]; ring
    rw [this]; linarith only [hlamlo, hHL, hL1, hε₀]
  have hpow2 : (1 : ℝ) ≤ 2 ^ (j + 2) := one_le_pow₀ (by norm_num)
  have hlame : r ^ e / 2 ^ (j + 2) ≤ lam ^ e := by
    calc r ^ e / 2 ^ (j + 2) ≤ r ^ e / ((2 : ℝ) ^ (j + 2)) ^ e := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          calc ((2 : ℝ) ^ (j + 2)) ^ e ≤ ((2 : ℝ) ^ (j + 2)) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hpow2 he1
            _ = 2 ^ (j + 2) := Real.rpow_one _
      _ = (r / 2 ^ (j + 2)) ^ e := (Real.div_rpow hr.le (by positivity) e).symm
      _ ≤ lam ^ e := Real.rpow_le_rpow (by positivity) hlamq he0
  have hΩ' : Ω ≤ (1 - θ) / 2 * lam ^ e := by
    have h1 : Ω ≤ (1 - θ) * r ^ e / 2 ^ (j + 3) := by
      refine hΩ.trans ?_
      rw [pow_add, show ((2 : ℝ) ^ 3) = 8 by norm_num]
      rw [le_div_iff₀ (by positivity)]
      have : Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j)) * (2 ^ j * 8) = 12 * Real.sqrt m * R₂ := by
        field_simp; ring
      rw [this]; exact hmarg
    have h2 : (1 - θ) * r ^ e / 2 ^ (j + 3) = (1 - θ) / 2 * (r ^ e / 2 ^ (j + 2)) := by
      rw [pow_succ 2 (j + 2)]; field_simp
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hlame (by positivity))
  -- `λ^e ≥ √λ ≥ 4ε₀/(1 − θ)`
  have hsqrt : Real.sqrt lam ≤ lam ^ e := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlam1' (by rw [he]; linarith only [hδ])
  have hε₀' : 2 * ε₀ ≤ (1 - θ) / 2 * lam ^ e := by
    have h1 : 4 * ε₀ / (1 - θ) ≤ Real.sqrt lam := by
      rw [Real.le_sqrt (by positivity) hlampos.le]
      linarith only [hL2, hlamlo, hHL]
    have h2 : 4 * ε₀ ≤ (1 - θ) * lam ^ e := by
      have := (div_le_iff₀ hmθ).mp (h1.trans hsqrt)
      linarith only [this]
    linarith only [h2]
  have hmain : Ω + 2 * ε₀ ≤ (1 - θ) * lam ^ e := by linarith only [hΩ', hε₀']
  refine ⟨hmain, ?_⟩
  -- the small slope perturbation
  have h1 : Ω + 2 * ε₀ ≤ lam ^ e := by
    have : (1 - θ) * lam ^ e ≤ lam ^ e := by
      have : 0 ≤ lam ^ e := by positivity
      nlinarith only [this, hθ0]
    linarith only [hmain, this]
  have h2 : lam ^ e / (lam / 2) = 2 * lam ^ (e - 1) := by
    rw [Real.rpow_sub_one hlampos.ne']; field_simp
  have h3 : lam ^ (e - 1) ≤ lam ^ (-(1 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le hlam1' (by rw [he]; linarith only [hδ1])
  have h4 : lam ^ (-(1 : ℝ) / 5) ≤ r₁ / 4 := by
    have h5 : 4 / r₁ ≤ lam ^ ((1 : ℝ) / 5) := by
      have hle : (4 / r₁) ^ 5 ≤ lam := by linarith only [hL3, hlamlo, hHL]
      calc 4 / r₁ = ((4 / r₁) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ lam ^ ((1 : ℝ) / 5) := Real.rpow_le_rpow (by positivity) hle (by norm_num)
    have hpos5 : 0 < lam ^ ((1 : ℝ) / 5) := by positivity
    rw [show (-(1 : ℝ) / 5) = -((1 : ℝ) / 5) by ring, Real.rpow_neg hlampos.le]
    rw [inv_le_iff_one_le_mul₀ hpos5]
    have := mul_le_mul_of_nonneg_right h5 (show 0 ≤ r₁ / 4 by positivity)
    have h6 : 4 / r₁ * (r₁ / 4) = 1 := by field_simp
    linarith only [this, h6]
  calc (Ω + 2 * ε₀) / (lam / 2) ≤ lam ^ e / (lam / 2) :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = 2 * lam ^ (e - 1) := h2
    _ ≤ r₁ / 2 := by linarith only [h3, h4]

/-- **The links of generation `j`**, in both orientations: with `P' = −sg · P`, the link error
of `(φ j u, φ (j+1) u)` is `O₁(Q_{r/2^j})` and its cost `μ(Δ) − P'·Δ` is at most
`C (2 (√m (3/2) R₂/2^j)² + 8 ε₁²) 2^{j+3}/r + C (r/2^j) |t − t₀|^{2+δ}`, `ε₁ = (2 + T)√d` for
`T ≥ |t₀|`. -/
theorem chain_link_bounds {M : Model m} (hM : M.Standing) {T : ℝ} (hT : ‖M.t₀‖ ≤ T)
    {cS CS r₁ : ℝ}
    (h24 : ∀ t h : E, ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hCS : 0 < CS) (hr₁ : 0 < r₁) {K : ℕ} (hK : 2 ≤ K) {A : ℝ} (hA : 1 ≤ A) {N : ℕ}
    (hPrem : Premise M K A N) {p : ℤ} {c t : E} {R₁ R₂ r sg θ L₁ : ℝ} (hsg : sg = 1 ∨ sg = -1)
    {a : Vertex m}
    (ha : ‖point a - (WithLp.toLp 2 ((p : ℝ), c) + (sg * r) • slopeVec t)‖ ≤
      Real.sqrt ((m : ℝ) + 1))
    {P : Pt m} (hP : IsSubgradient M.μ (slopeVec t) P) (ht1 : ‖t - M.t₀‖ ≤ 1)
    (htr : ‖t - M.t₀‖ ≤ r₁ / 2) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hslope : ∀ lam : ℝ, 0 < lam → lam ≤ r →
      lam * ‖t - M.t₀‖ ≤ θ * lam ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hr : 0 < r) (hR₁r : R₁ ≤ r / 32) (hrN : r ≤ N / 2)
    (hmarg : 12 * Real.sqrt m * R₂ ≤ (1 - θ) * r ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hL₁ : 2 * roundSlack m T + 1 ≤ 29 / 32 * L₁ ∧
      (4 * roundSlack m T / (1 - θ)) ^ 2 ≤ 29 / 32 * L₁ ∧ (4 / r₁) ^ 5 ≤ 29 / 32 * L₁)
    {j : ℕ} (hj : L₁ ≤ r / 2 ^ (j + 1)) {u : Vertex m} (hu : u ∈ shearBox p c t R₁ R₂) :
    IsOs M.P 1 (Q M K A (r / 2 ^ j)) (fun ω => linkError M ω
        (chainPoint p c t R₁ R₂ r sg a j u) (chainPoint p c t R₁ R₂ r sg a (j + 1) u)) ∧
      linkCost M ((-sg) • P) (chainPoint p c t R₁ R₂ r sg a j u)
          (chainPoint p c t R₁ R₂ r sg a (j + 1) u) ≤
        CS * (2 * (Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j))) ^ 2 + 8 * roundSlack m T ^ 2) *
            (2 ^ (j + 3) / r) +
          CS * (r / 2 ^ j) * ‖t - M.t₀‖ ^ (2 + M.δ) := by
  set ε₀ := 2 * Real.sqrt ((m : ℝ) + 1) with hε₀def
  have hε₀ : 1 ≤ ε₀ := by
    have : 1 ≤ Real.sqrt ((m : ℝ) + 1) := by
      rw [Real.one_le_sqrt]; linarith only [Nat.cast_nonneg (α := ℝ) m]
    linarith only [this]
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hT
  set ε₁ := roundSlack m T with hε₁def
  have hε₁ : (2 + ‖M.t₀‖) * ε₀ ≤ 2 * ε₁ := by
    have := mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg ((m : ℝ) + 1))
    rw [hε₀def, hε₁def, roundSlack]; linarith only [this]
  have hε₀₁ : ε₀ ≤ ε₁ := by
    have h0 : 0 ≤ T * Real.sqrt ((m : ℝ) + 1) := mul_nonneg hT0 (Real.sqrt_nonneg _)
    have : ε₁ = ε₀ + T * Real.sqrt ((m : ℝ) + 1) := by
      rw [hε₀def, hε₁def, roundSlack]; ring
    linarith only [this, h0]
  have hε₁1 : 1 ≤ ε₁ := one_le_roundSlack m hT0
  set H := r / 2 ^ (j + 1) with hHdef
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hA0 : (0 : ℝ) < A := by linarith only [hA]
  have heQ := Q_exponent_nonneg hM hK
  obtain ⟨δτ, δw, hτ, hw, hstep⟩ := exists_chain_step (p := p) (c := c) (t := t) (r := r)
    (sg := sg) hR₁ hR₂ ha j hu
  have hδw : ‖δw‖ ≤ Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j)) :=
    Proofs.ShortLengths.norm_le_sqrt_mul_of_abs_le (x := δw) (by positivity) hw
  have hτH : |δτ| ≤ 3 / 32 * H := by
    have h1 : R₁ / 2 ^ j ≤ H / 16 := by
      calc R₁ / 2 ^ j ≤ r / 32 / 2 ^ j := div_le_div_of_nonneg_right hR₁r hpow.le
        _ = H / 16 := by rw [hHdef]; ring
    linarith only [hτ, h1]
  have hrj : r / 2 ^ j ≤ r := div_le_self hr.le (one_le_pow₀ (by norm_num))
  -- the bounds for an oriented link with the displacement of generation `j`
  have key : ∀ (x x' : Vertex m) (lam : ℝ) (ω : E),
      ‖(point x' - point x) - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))‖ ≤ ε₀ →
      |lam - H| ≤ 3 / 32 * H → ‖ω‖ ≤ Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j)) →
      IsOs M.P 1 (Q M K A (r / 2 ^ j)) (fun ω' => linkError M ω' x x') ∧
        linkCost M P x x' ≤
          CS * (2 * (Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j))) ^ 2 + 8 * ε₁ ^ 2) * (2 ^ (j + 3) / r) +
            CS * (r / 2 ^ j) * ‖t - M.t₀‖ ^ (2 + M.δ) := by
    intro x x' lam ω hd hl hω
    obtain ⟨n1, n2, n3, n4, n5⟩ := link_numeric (lam := lam) (Ω := ‖ω‖) hM hr₁ hθ0 hθ1 hε₁1 hR₂
      hr hHdef hj hL₁ hmarg hl hω
    have hlampos : 0 < lam := by linarith only [n1, hε₁1]
    have hlamN : lam + ε₀ ≤ 2 * (N : ℝ) / 3 := by linarith only [n2, hrj, hrN, hr, hε₀₁]
    have hlamr : lam ≤ r := by linarith only [n2, hrj, hε₁1]
    have hd0 : 0 ≤ ‖ω‖ + (2 + ‖M.t₀‖) * ε₀ :=
      add_nonneg (norm_nonneg _) (mul_nonneg (by linarith only [norm_nonneg M.t₀])
        (by linarith only [hε₀]))
    obtain ⟨hOs, hcost₀⟩ := link_bounds hM h24 hCS hK hA hPrem ht1
      (by linarith only [htr, hr₁]) hP hε₀ hd (by linarith only [n1, hε₀₁]) hlamN
      (hslope lam hlampos hlamr) (by linarith only [hε₁, n4])
      (calc (‖ω‖ + (2 + ‖M.t₀‖) * ε₀) / (lam / 2) ≤ (‖ω‖ + 2 * ε₁) / (lam / 2) :=
            div_le_div_of_nonneg_right (by linarith only [hε₁]) (half_pos hlampos).le
        _ ≤ r₁ := by linarith only [n5, hr₁])
    have hcost : linkCost M P x x' ≤ CS * (‖ω‖ + 2 * ε₁) ^ 2 / (lam / 2) +
        CS * (lam + ε₀) * ‖t - M.t₀‖ ^ (2 + M.δ) := by
      refine hcost₀.trans (add_le_add ?_ le_rfl)
      apply div_le_div_of_nonneg_right _ (half_pos hlampos).le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0 (by linarith only [hε₁]) 2) hCS.le
    refine ⟨hOs.mono_scale zero_le_one (Q_pos M K hA0 (by linarith only [hlampos, hε₀]))
      (Q_mono M K hA0.le (by linarith only [hlampos, hε₀]) (by linarith only [n2, hε₀₁])
        heQ), hcost.trans ?_⟩
    have hsq : (‖ω‖ + 2 * ε₁) ^ 2 ≤ 2 * (Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j))) ^ 2 +
        8 * ε₁ ^ 2 := by
      have h1 : (‖ω‖ + 2 * ε₁) ^ 2 ≤ 2 * ‖ω‖ ^ 2 + 8 * ε₁ ^ 2 := by
        nlinarith only [sq_nonneg (‖ω‖ - 2 * ε₁)]
      have h2 : ‖ω‖ ^ 2 ≤ (Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hω 2
      linarith only [h1, h2]
    have hinv : 1 / (lam / 2) ≤ 2 ^ (j + 3) / r := by
      rw [div_le_div_iff₀ (by positivity) hr]
      have := mul_le_mul_of_nonneg_left n3 (show (0 : ℝ) ≤ 2 ^ (j + 3) by positivity)
      rw [mul_div_cancel₀ _ (by positivity)] at this
      linarith only [this]
    apply add_le_add
    · rw [mul_div_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hCS.le
      calc (‖ω‖ + 2 * ε₁) ^ 2 / (lam / 2) = (‖ω‖ + 2 * ε₁) ^ 2 * (1 / (lam / 2)) := by ring
        _ ≤ (2 * (Real.sqrt m * (3 / 2 * (R₂ / 2 ^ j))) ^ 2 + 8 * ε₁ ^ 2) *
            (2 ^ (j + 3) / r) :=
          mul_le_mul hsq hinv (by positivity) (by positivity)
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith only [n2, hε₀₁]) hCS.le
  rcases hsg with rfl | rfl
  · -- after the cube: the link runs from `φ (j+1) u` to `φ j u`, with `−P`
    have hneg : (WithLp.toLp 2 ((0 : ℝ), -δw) : Pt m) = -WithLp.toLp 2 ((0 : ℝ), δw) := by
      apply Infra.FPP.pt_ext
      · change (0 : ℝ) = -0; simp
      · rfl
    have hd : ‖(point (chainPoint p c t R₁ R₂ r 1 a j u) -
          point (chainPoint p c t R₁ R₂ r 1 a (j + 1) u)) -
        ((H - δτ) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), -δw))‖ ≤ ε₀ := by
      have heq : (point (chainPoint p c t R₁ R₂ r 1 a j u) -
            point (chainPoint p c t R₁ R₂ r 1 a (j + 1) u)) -
          ((H - δτ) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), -δw)) =
          -((point (chainPoint p c t R₁ R₂ r 1 a (j + 1) u) -
            point (chainPoint p c t R₁ R₂ r 1 a j u)) -
            ((δτ - 1 * r / 2 ^ (j + 1)) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), δw))) := by
        rw [hneg, show H - δτ = -(δτ - 1 * r / 2 ^ (j + 1)) by rw [hHdef]; ring, neg_smul]
        abel
      rw [heq, norm_neg]
      exact hstep
    obtain ⟨h1, h2⟩ := key _ _ (H - δτ) (-δw) hd
      (by rw [show H - δτ - H = -δτ by ring, abs_neg]; exact hτH) (by rw [norm_neg]; exact hδw)
    refine ⟨?_, ?_⟩
    · convert h1 using 2 with ω'
      exact linkError_comm M ω' _ _
    · rw [show (-(1 : ℝ)) • P = -P from neg_one_smul ℝ P, linkCost_neg]
      exact h2
  · -- before the cube: the link runs from `φ j u` to `φ (j+1) u`, with `P`
    have hd : ‖(point (chainPoint p c t R₁ R₂ r (-1) a (j + 1) u) -
          point (chainPoint p c t R₁ R₂ r (-1) a j u)) -
        ((δτ + H) • slopeVec t + WithLp.toLp 2 ((0 : ℝ), δw))‖ ≤ ε₀ := by
      rw [show δτ + H = δτ - -1 * r / 2 ^ (j + 1) by rw [hHdef]; ring]
      exact hstep
    obtain ⟨h1, h2⟩ := key _ _ (δτ + H) δw hd
      (by rw [show δτ + H - H = δτ by ring]; exact hτH) hδw
    refine ⟨h1, ?_⟩
    rw [neg_neg, one_smul]
    exact h2

end CurvatureVariance.Paper.Moments
