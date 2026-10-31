/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.Shear
public import CurvatureVariance.Paper.Proofs.Moments.Chaining
public import CurvatureVariance.Paper.Contracts.Geometry
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes

/-!
# Links of the chaining: the premise and the deterministic cost

The proof of Lemma `lem:tree`: consecutive points of the chain differ by a vector whose slope lies
within the margin of equation `eq:premise`, so that equation applies to them, and, by equation
`eq:support`, the costs `μ(z) − P_t·z` of the links are small. For two lattice points whose
displacement is
`λ(1, t) + (0, ω)` up to a rounding error `ε₀`:

* `exists_premise_link`: if `λ|t − t₀| ≤ θ λ^{3/4+δ/100}` and
  `|ω| + (2 + |t₀|)ε₀ ≤ (1 − θ) λ^{3/4+δ/100}` (the margin), the longitudinal displacement is an
  integer `s` with `|s − λ| ≤ ε₀` and the premise, equation `eq:premise`, gives
  `|T(x, x') − μ(x' − x)| ≤ O₁(Q_s)`. The term `|t₀|ε₀` pays for the recentring of `𝒟(s)` at
  `s t₀` instead of `λ t₀`.
* `cost_le_of_support`: equation `eq:support` by homogeneity,
  `μ(v) − P_t·v ≤ C|v₂ − v₁t|²/v₁ + C v₁|t − t₀|^{2+δ}` when `|v₂ − v₁t| ≤ r₁ v₁`.
* `linkError_comm`, `linkCost_neg`: reversing a link (for the chain after the cube).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem fst_sub_link (x x' : Vertex m) (t ω : E) (lam : ℝ) :
    ((point x' - point x) - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))).fst =
      ((x'.1 : ℝ) - x.1) - lam := by
  simp only [WithLp.sub_fst, WithLp.add_fst, WithLp.smul_fst, Infra.FPP.point_fst]
  change (x'.1 : ℝ) - x.1 - (lam * 1 + 0) = _
  ring

theorem snd_sub_link (x x' : Vertex m) (t ω : E) (lam : ℝ) :
    ((point x' - point x) - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))).snd =
      transversePoint (x'.2 - x.2) - (lam • t + ω) := by
  simp only [WithLp.sub_snd, WithLp.add_snd, WithLp.smul_snd, Infra.FPP.point_snd,
    Infra.FPP.transversePoint_sub]
  rfl

/-- **A link with a margin in equation `eq:premise`.** -/
theorem exists_premise_link {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {N : ℕ}
    (hPrem : Premise M K A N) {x x' : Vertex m} {t ω : E} {lam ε₀ θ : ℝ} (hε₀ : 1 ≤ ε₀)
    (hdisp : ‖(point x' - point x) - (lam • slopeVec t + WithLp.toLp 2 ((0 : ℝ), ω))‖ ≤ ε₀)
    (hlam : ε₀ + 1 ≤ lam) (hlamN : lam + ε₀ ≤ 2 * (N : ℝ) / 3)
    (hslope : lam * ‖t - M.t₀‖ ≤ θ * lam ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hmargin : ‖ω‖ + (2 + ‖M.t₀‖) * ε₀ ≤ (1 - θ) * lam ^ ((3 : ℝ) / 4 + M.δ / 100)) :
    ∃ s : ℕ, x'.1 - x.1 = s ∧ |(s : ℝ) - lam| ≤ ε₀ ∧
      IsAbsOs M.P 1 (Q M K A s)
        (fun ω' => passageTimeReal ω' x x' - M.μ.1 (point x' - point x)) := by
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  set e : ℝ := (3 : ℝ) / 4 + M.δ / 100 with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by rw [he]; linarith only [hδ1]
  have hfst := Proofs.Geometry.abs_fst_le_norm ((point x' - point x) - (lam • slopeVec t +
    WithLp.toLp 2 ((0 : ℝ), ω)))
  rw [fst_sub_link] at hfst
  have hsnd := Proofs.Geometry.norm_snd_le_norm ((point x' - point x) - (lam • slopeVec t +
    WithLp.toLp 2 ((0 : ℝ), ω)))
  rw [snd_sub_link] at hsnd
  have h1 := (abs_le.mp (hfst.trans hdisp))
  -- the longitudinal displacement
  have hpos : (1 : ℝ) ≤ ((x'.1 - x.1 : ℤ) : ℝ) := by push_cast; linarith only [h1.1, hlam]
  have hposZ : (1 : ℤ) ≤ x'.1 - x.1 := by exact_mod_cast hpos
  set s : ℕ := (x'.1 - x.1).toNat with hs
  have hsZ : x'.1 - x.1 = (s : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  have hsR : (s : ℝ) = (x'.1 : ℝ) - x.1 := by
    have : ((s : ℤ) : ℝ) = ((x'.1 - x.1 : ℤ) : ℝ) := by rw [hsZ]
    push_cast at this; exact_mod_cast this
  have hs1 : 1 ≤ s := by have : (1 : ℤ) ≤ (s : ℤ) := hsZ ▸ hposZ; exact_mod_cast this
  have hslam : |(s : ℝ) - lam| ≤ ε₀ := by rw [hsR, abs_le]; exact h1
  refine ⟨s, hsZ, hslam, ?_⟩
  have hsN : (s : ℝ) ≤ 2 * (N : ℝ) / 3 := by linarith only [(abs_le.mp hslam).2, hlamN]
  -- the transverse displacement lies in `𝒟(s)`
  have hlam0 : 0 ≤ lam := by linarith only [hlam, hε₀]
  have hy : ‖transversePoint (x'.2 - x.2) - (s : ℝ) • M.t₀‖ ≤ (s : ℝ) ^ e := by
    have hsplit : transversePoint (x'.2 - x.2) - (s : ℝ) • M.t₀ =
        (transversePoint (x'.2 - x.2) - (lam • t + ω)) + (lam • (t - M.t₀) + ω) +
          (lam - s) • M.t₀ := by
      rw [smul_sub, sub_smul]; abel
    have hn1 : ‖transversePoint (x'.2 - x.2) - (s : ℝ) • M.t₀‖ ≤
        ε₀ + ‖lam • (t - M.t₀) + ω‖ + ‖(lam - s) • M.t₀‖ := by
      rw [hsplit]
      refine (norm_add₃_le).trans ?_
      linarith only [hsnd, hdisp]
    have hn2 : ‖lam • (t - M.t₀) + ω‖ ≤ lam * ‖t - M.t₀‖ + ‖ω‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0]
    have hn3 : ‖(lam - s) • M.t₀‖ ≤ ε₀ * ‖M.t₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right hslam (norm_nonneg _)
    have hsub : lam ^ e ≤ (lam - ε₀) ^ e + ε₀ := by
      have h := Real.rpow_add_le_add_rpow (a := lam - ε₀) (b := ε₀) (by linarith only [hlam])
        (by linarith only [hε₀]) he0 he1
      rw [sub_add_cancel] at h
      have hε : ε₀ ^ e ≤ ε₀ := by
        calc ε₀ ^ e ≤ ε₀ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hε₀ he1
          _ = ε₀ := Real.rpow_one ε₀
      linarith only [h, hε]
    have hmono : (lam - ε₀) ^ e ≤ (s : ℝ) ^ e :=
      Real.rpow_le_rpow (by linarith only [hlam]) (by linarith only [(abs_le.mp hslam).1]) he0
    linarith only [hn1, hn2, hn3, hslope, hmargin, hsub, hmono]
  exact premise_isAbsOs_pair hM hPrem hsZ hs1 hsN hy

/-- **Equation `eq:support` by homogeneity.** For `v = v₁ (1, t + h)` with `v₁ > 0` and
`|h| = |v₂ − v₁ t|/v₁ ≤ r₁`: `μ(v) − P_t·v ≤ C|v₂ − v₁ t|²/v₁ + C v₁ |t − t₀|^{2+δ}`. -/
theorem cost_le_of_support {M : Model m} {cS CS r₁ : ℝ}
    (h24 : ∀ t h : E, ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        cS * ‖h‖ ^ 2 - CS * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ))
    {t : E} (ht : ‖t - M.t₀‖ ≤ r₁) {P : Pt m} (hP : IsSubgradient M.μ (slopeVec t) P) {v : Pt m}
    (hv : 0 < v.fst) (hv' : ‖v.snd - v.fst • t‖ ≤ r₁ * v.fst) :
    M.μ.1 v - inner ℝ P v ≤
      CS * ‖v.snd - v.fst • t‖ ^ 2 / v.fst + CS * v.fst * ‖t - M.t₀‖ ^ (2 + M.δ) := by
  set h : E := v.fst⁻¹ • v.snd - t with hh
  have hth : t + h = v.fst⁻¹ • v.snd := by rw [hh]; abel
  have hdecomp : v = v.fst • slopeVec (t + h) := by
    apply Infra.FPP.pt_ext
    · simp only [WithLp.smul_fst, slopeVec, smul_eq_mul]
      change v.fst = v.fst * 1
      ring
    · simp only [WithLp.smul_snd, slopeVec]
      change v.snd = v.fst • (t + h)
      rw [hth, smul_smul, mul_inv_cancel₀ hv.ne', one_smul]
  have hhn : ‖h‖ = ‖v.snd - v.fst • t‖ / v.fst := by
    have : h = v.fst⁻¹ • (v.snd - v.fst • t) := by
      rw [hh, smul_sub, smul_smul, inv_mul_cancel₀ hv.ne', one_smul]
    rw [this, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hv, inv_mul_eq_div]
  have hhr : ‖h‖ ≤ r₁ := by rw [hhn, div_le_iff₀ hv]; exact hv'
  have hb := (h24 t h ht hhr P hP).2
  have hμ : M.μ.1 v = v.fst * M.μ.1 (slopeVec (t + h)) := by
    conv_lhs => rw [hdecomp]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hv]
  have hin : inner ℝ P v = v.fst * inner ℝ P (slopeVec (t + h)) := by
    conv_lhs => rw [hdecomp]
    rw [inner_smul_right]
  rw [hμ, hin, ← mul_sub]
  calc v.fst * (M.μ.1 (slopeVec (t + h)) - inner ℝ P (slopeVec (t + h)))
      ≤ v.fst * (CS * ‖h‖ ^ 2 + CS * ‖t - M.t₀‖ ^ (2 + M.δ)) :=
        mul_le_mul_of_nonneg_left hb hv.le
    _ = _ := by rw [hhn]; field_simp

/-- Reversing a link does not change its error, by the symmetry of `T` and of the norm `μ`. -/
theorem linkError_comm (M : Model m) (ω : Config m) (x y : Vertex m) :
    linkError M ω x y = linkError M ω y x := by
  unfold linkError
  rw [passageTimeReal_symm, ← map_neg_eq_map M.μ.1 (point y - point x), neg_sub]

/-- Reversing a link and the functional `P` does not change its cost. -/
theorem linkCost_neg (M : Model m) (P : Pt m) (x y : Vertex m) :
    linkCost M (-P) x y = linkCost M P y x := by
  unfold linkCost
  rw [← map_neg_eq_map M.μ.1 (point y - point x), neg_sub, inner_neg_left,
    ← inner_neg_right, neg_sub]

end CurvatureVariance.Paper.Moments
