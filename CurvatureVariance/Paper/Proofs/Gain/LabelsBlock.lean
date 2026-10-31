/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.LabelsStep
public import CurvatureVariance.Paper.Proofs.Gain.LabelsMesh
public import CurvatureVariance.Paper.Proofs.Gain.FACore
public import CurvatureVariance.Paper.Proofs.Gain.FARate
import CurvatureVariance.Paper.Proofs.Gain.FAClip
import CurvatureVariance.Paper.Proofs.Gain.FAEvents
import CurvatureVariance.Paper.Proofs.Gain.FAMesh
import CurvatureVariance.Paper.Proofs.Gain.FAMoments
import CurvatureVariance.Paper.Proofs.Localization.ModulusSupport
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The estimates of Lemma `lem:labels` in one block

Steps 1 and 2 of the proof of [AB26, Lemma 6.2], as the proof of Lemma `lem:labels` changes them,
for one block `G` of slab `i`, from the contracts already instantiated.

* The event. `labelLeaveProb`, the bound `π(L) = 2 (L+1)^{2(d−1)} C / r(L)^{8d}`, with `p = 8d` in
  Lemma `lem:localization` and `r(L) = leaveRadius` of order `L^{1/2}`
  (`measure_leaveSet_le_labelLeaveProb`). This is the paper's `CL^{2(d−1)}L^{−4d}`.
  `exists_labelLeaveEvent`: an event `E` of probability at most `π(L)`, off which `Φ' = Φ` on `Γ_G`,
  and on which `|Φ − Φ'| ≤ (S(τ) + S(τ'))/Q_n`, the affine parts being cancelled, for any `S` above
  the variables of Proposition `prop:profiles` on the pairs of cubes covering `Γ_G`.
* `abs_drift_le`: `|μ(v−u) − ζ_t·(v−u)| ≤ C L² Q_n` on `Γ_G`, from equations `eq:support` and
  `eq:scales`.
* `exists_labelBlockError`: for `S`, the modulus and the comparison on the pair of cubes containing
  the two faces, one variable `Y`, of `L^k` norm at most `ε`, with
  `|Φ − Ψ| + |Ψ − Ψ(u_g,v_g)| + (|Ψ(u_g,v_g)| − B)₊ ≤ Y` on `Γ_G`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### The event -/

/-- The bound `π(L)` of the probability of the event of the proof of Lemma `lem:labels` (`1` if the
threshold `r(L) = leaveRadius` is not positive): Markov's inequality with the moment of order `8d`.
-/
noncomputable def labelLeaveProb (m : ℕ) (Cd CR : ℝ) (L : ℕ) : ℝ :=
  if 0 < leaveRadius Cd L then
    2 * ((L : ℝ) + 1) ^ (2 * m) * CR / leaveRadius Cd L ^ (8 * (m + 1))
  else 1

theorem labelLeaveProb_nonneg (m : ℕ) {Cd CR : ℝ} (hCR : 0 ≤ CR) (L : ℕ) :
    0 ≤ labelLeaveProb m Cd CR L := by
  unfold labelLeaveProb
  split_ifs with h
  · positivity
  · exact zero_le_one

/-- **Markov's inequality for the event** (the proof of Lemma `lem:labels`), with `p = 8d`. -/
theorem measure_leaveSet_le_labelLeaveProb {M : Model m} (hM : M.Standing) {n w L : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {i : ℕ} {Wn : ℝ} {o g : Fin m → ℤ} {Cd CR : ℝ} (hCR : 0 ≤ CR)
    (hr : 0 < leaveRadius Cd L)
    (hrad : ∀ jk ∈ finePairs L o g,
      ∫⁻ ω, fineRadius n w t i Wn jk ω ^ (8 * (m + 1)) ∂M.P ≤ ENNReal.ofReal CR) :
    (M.P.prod M.P) (leaveSet n w L t i Wn o g (leaveRadius Cd L)) ≤
      ENNReal.ofReal (labelLeaveProb m Cd CR L) := by
  set q := 8 * (m + 1)
  set r := leaveRadius Cd L
  have hrq : 0 < r ^ q := pow_pos hr q
  have hterm : ∀ jk ∈ finePairs L o g,
      2 * ((∫⁻ ω, fineRadius n w t i Wn jk ω ^ q ∂M.P) / ENNReal.ofReal r ^ q) ≤
        ENNReal.ofReal (2 * (CR / r ^ q)) := by
    intro jk hjk
    rw [← ENNReal.ofReal_pow hr.le, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_div_of_pos hrq]
    gcongr
    exact hrad jk hjk
  refine (measure_leaveSet_le hM n w L t i Wn o g hr q).trans
    ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard := card_finePairs_le L o g
  have h0 : 0 ≤ 2 * (CR / r ^ q) := by positivity
  unfold labelLeaveProb
  rw [ite_eq_left hr]
  calc ((finePairs L o g).card : ℝ) * (2 * (CR / r ^ q))
      ≤ ((L : ℝ) + 1) ^ (2 * m) * (2 * (CR / r ^ q)) := mul_le_mul_of_nonneg_right hcard h0
    _ = 2 * ((L : ℝ) + 1) ^ (2 * m) * CR / r ^ q := by ring

/-- `Φ − Φ'` is the change of the slab passage times divided by `Q_n`: the term `ζ_t·(v−u)` cancels.
-/
theorem normSlabTime_sub_eq (M : Model m) (K : ℕ) (A : ℝ) (ω ω' : Config m) (n : ℕ) (P : Pt m)
    (i : ℕ) (u v : Vertex m) :
    normSlabTime M K A ω n P i u v - normSlabTime M K A ω' n P i u v =
      (slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v -
        slabTimeReal ω' (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v) / Q M K A n := by
  unfold normSlabTime
  rw [← sub_div]
  ring_nf

/-- **The change of `Φ` when the weights outside `G` are replaced, with the affine parts cancelled**:
for `S` above the variables `X_{jk}` of Proposition `prop:profiles` on the pairs of cubes covering
`Γ_G`, almost surely `|D(τ) − D(τ')| ≤ S(τ) + S(τ')` on `Γ_G`, since `μ(v−u)` cancels. -/
theorem ae_abs_slabTimeReal_sub_le {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {n L : ℕ}
    (hw : 1 ≤ wInt M K A n) {t : EuclideanSpace ℝ (Fin m)} {i : ℕ} {o g : Fin m → ℤ}
    {X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ}
    (hX : ∀ᵐ ω ∂M.P, FineGood n (wInt M K A n) L t i o g M.μ X ω) {S : Config m → ℝ}
    (hS : ∀ jk ∈ finePairs L o g, ∀ ω, X jk ω ≤ S ω) :
    ∀ᵐ z ∂(M.P.prod M.P),
      ∀ u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n),
      ∀ v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n),
        |slabTimeReal z.2 (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v -
            slabTimeReal (outsideSplice (block n (wInt M K A n) L t i o g) z)
              (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v| ≤
          S z.2 + S (outsideSplice (block n (wInt M K A n) L t i o g) z) := by
  have := hM.probP
  set w := wInt M K A n
  set G := block n w L t i o g
  have hσ := measurePreserving_outsideSplice hM G
  have hsnd : MeasurePreserving Prod.snd (M.P.prod M.P) M.P := measurePreserving_snd
  filter_upwards [hsnd.quasiMeasurePreserving.ae hX, hσ.quasiMeasurePreserving.ae hX]
    with z hz1 hz2 u hu v hv
  have hw0 : 0 < w := hw
  have hu1 : u.1 = ((i : ℤ) - 1) * n := (mem_subcubeFace_iff.mp hu).1
  have hv1 : v.1 = (i : ℤ) * n := (mem_subcubeFace_iff.mp hv).1
  set j := rowIndex n w t ((i : ℤ) - 1) u.2
  set k := rowIndex n w t (i : ℤ) v.2
  have hjk : (j, k) ∈ finePairs L o g :=
    Finset.mem_product.mpr ⟨rowIndex_mem_rowBox hw hu, rowIndex_mem_rowBox hw hv⟩
  have huc : u ∈ finePairCube₁ n w t i j := rowCube_subset_transverseCube hw0 t _ j ⟨hu1, rfl⟩
  have hvc : v ∈ finePairCube₂ n w t i k := rowCube_subset_finePairCube₂ hw0 t i k ⟨hv1, rfl⟩
  have e1 := hz1.2 (j, k) hjk u huc v hvc
  have e2 := hz2.2 (j, k) hjk u huc v hvc
  rw [hu1, hv1] at e1 e2
  have f1 := hS (j, k) hjk z.2
  have f2 := hS (j, k) hjk (outsideSplice G z)
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith only [e1.1, e1.2, e2.1, e2.2, f1, f2]

/-- **The event** (the proof of Lemma `lem:labels`): an event `E` of probability at most `π(L)` such
that, for `S` above the variables `X_{jk}`, almost surely `|Φ − Φ'| ≤ 1_E (S(τ) + S(τ'))/Q_n` on
`Γ_G`. So `Φ' ≠ Φ` somewhere on `Γ_G` only on `E`: a geodesic for `τ` or for `τ'` leaves `G`, so
that the localization radius of one of the at most `(L+1)^{2(d−1)}` pairs of cubes covering `Γ_G`,
for `τ` or for `τ'`, exceeds `r(L)`. -/
theorem exists_labelLeaveEvent {M : Model m} (hM : M.Standing) {Cd T : ℝ} (hCd : 0 ≤ Cd)
    (hTube : TubeProperty m Cd T) {K : ℕ} {A : ℝ} (hA : 1 ≤ A) {n L : ℕ} (hn : 2 ≤ n)
    (hw : 1 ≤ wInt M K A n) (hQ : 0 < Q M K A n) {t : EuclideanSpace ℝ (Fin m)} (ht : ‖t‖ ≤ T)
    {i : ℕ} (hi : 1 ≤ i) {P : Pt m} {o g : Fin m → ℤ}
    {X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ}
    (hX : ∀ᵐ ω ∂M.P, FineGood n (wInt M K A n) L t i o g M.μ X ω) {S : Config m → ℝ}
    (hS : ∀ jk ∈ finePairs L o g, ∀ ω, X jk ω ≤ S ω) {CR : ℝ} (hCR : 0 ≤ CR)
    (hrad : ∀ jk ∈ finePairs L o g,
      ∫⁻ ω, fineRadius n (wInt M K A n) t i (W M K A n) jk ω ^ (8 * (m + 1)) ∂M.P ≤
        ENNReal.ofReal CR) :
    ∃ E : Set (Config m × Config m), MeasurableSet E ∧
      (M.P.prod M.P) E ≤ ENNReal.ofReal (labelLeaveProb m Cd CR L) ∧
      ∀ᵐ z ∂(M.P.prod M.P), ∀ p ∈ blockFacePairs n (wInt M K A n) L t i o g,
        |normSlabTime M K A z.2 n P i p.1 p.2 -
            normSlabTime M K A (outsideSplice (block n (wInt M K A n) L t i o g) z) n P i
              p.1 p.2| ≤
          E.indicator (fun z => S z.2 / Q M K A n +
            S (outsideSplice (block n (wInt M K A n) L t i o g) z) / Q M K A n) z := by
  have := hM.probP
  have hA' := ae_abs_slabTimeReal_sub_le (i := i) hM hw hX hS
  by_cases hr : 0 < leaveRadius Cd L
  · refine ⟨leaveSet n (wInt M K A n) L t i (W M K A n) o g (leaveRadius Cd L),
      measurableSet_leaveSet _ _ _ _ _ _ _ _ _, measure_leaveSet_le_labelLeaveProb hM hCR hr hrad,
      ?_⟩
    have h0 := ae_abs_sub_le_leaveSet hM hCd hTube hA hn hw ht hi hr.le
      (mul_one_add_leaveRadius_lt hCd hr) hX
    filter_upwards [h0, hA'] with z hz0 hz1 p hp
    rw [normSlabTime_sub_eq]
    obtain ⟨hu, hv⟩ := hp
    by_cases hb : z ∈ leaveSet n (wInt M K A n) L t i (W M K A n) o g (leaveRadius Cd L)
    · rw [indicator_of_mem hb, ← add_div, abs_div, abs_of_pos hQ]
      exact div_le_div_of_nonneg_right (hz1 _ hu _ hv) hQ.le
    · have h := hz0 _ hu _ hv
      rw [indicator_of_notMem hb] at h ⊢
      have h0 : slabTimeReal z.2 (((i : ℤ) - 1) * n) ((i : ℤ) * n) p.1 p.2 -
          slabTimeReal (outsideSplice (block n (wInt M K A n) L t i o g) z)
            (((i : ℤ) - 1) * n) ((i : ℤ) * n) p.1 p.2 = 0 :=
        abs_nonpos_iff.mp h
      rw [h0, zero_div, abs_zero]
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      unfold labelLeaveProb
      rw [ite_eq_right hr, ENNReal.ofReal_one]
    · filter_upwards [hA'] with z hz1 p hp
      rw [normSlabTime_sub_eq, indicator_of_mem (Set.mem_univ z), ← add_div, abs_div,
        abs_of_pos hQ]
      exact div_le_div_of_nonneg_right (hz1 _ hp.1 _ hp.2) hQ.le

/-! ### The deterministic part -/

/-- **The size of `μ(v−u) − ζ_t·(v−u)` on `Γ_G`** (the proof of Lemma `lem:labels`,
"`sup_{Γ_G}|Φ| ≤ CL² + …`"): from equation `eq:support`, for `|t − t₀| ≤ r₁`,
`|v − u − n(1,t)|/n ≤ r₁`, and a bound `n|t − t₀|^{2+δ} ≤ D Q_n` (equation `eq:scales`). -/
theorem abs_drift_le {M : Model m} {K : ℕ} {A : ℝ} {n L i : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {P : Pt m} {o g : Fin m → ℤ} {c₀ C₀ r₁ D : ℝ} (hC₀ : 0 ≤ C₀)
    (hsupp : ∀ t h : EuclideanSpace ℝ (Fin m), ‖t - M.t₀‖ ≤ r₁ → ‖h‖ ≤ r₁ →
      ∀ p : Pt m, IsSubgradient M.μ (slopeVec t) p →
        c₀ * ‖h‖ ^ 2 - C₀ * ‖t - M.t₀‖ ^ (2 + M.δ) ≤
            M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ∧
          M.μ.1 (slopeVec (t + h)) - inner ℝ p (slopeVec (t + h)) ≤
            C₀ * ‖h‖ ^ 2 + C₀ * ‖t - M.t₀‖ ^ (2 + M.δ))
    (hP : IsSubgradient M.μ (slopeVec t) P) (ht : ‖t - M.t₀‖ ≤ r₁) (hn : 0 < n)
    (hw : (wInt M K A n : ℝ) ≤ 2 * W M K A n) (hWn : W M K A n ^ 2 = n * Q M K A n)
    (hr : (m : ℝ) * ((L : ℝ) * wInt M K A n) / n ≤ r₁)
    (hD : (n : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ D * Q M K A n) {u v : Vertex m}
    (hu : u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n))
    (hv : v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n)) :
    |M.μ.1 (point v - point u) - inner ℝ P (point v - point u)| ≤
      C₀ * (4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2 + D) * Q M K A n := by
  set w := wInt M K A n with hwdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hu1 : u.1 = ((i : ℤ) - 1) * n := (mem_subcubeFace_iff.mp hu).1
  have hv1 : v.1 = (i : ℤ) * n := (mem_subcubeFace_iff.mp hv).1
  have hvu : v.1 = u.1 + n := by rw [hu1, hv1]; ring
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  -- `v − u = (n, y)` with `|y − n t| ≤ m L w`
  have hpt := Moments.ExpArray.point_sub_eq (s := n) hvu
  set y : EuclideanSpace ℝ (Fin m) := transversePoint (v.2 - u.2) with hy
  have hy1 : ‖y - (n : ℝ) • t‖ ≤ (m : ℝ) * ((L : ℝ) * w) := by
    refine Localization.Modulus.norm_le_of_forall_abs_le (by positivity) fun k => ?_
    have h1 := blockCoord_mem_Ico hu k
    have h2 := blockCoord_mem_Ico hv k
    have e : (y - (n : ℝ) • t) k = blockCoord w L t o g v k - blockCoord w L t o g u k := by
      simp only [hy, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, transversePoint_apply,
        Pi.sub_apply, Int.cast_sub, blockCoord, hu1, hv1]
      push_cast
      ring
    rw [e, abs_le]
    constructor <;> nlinarith only [h1.1, h1.2, h2.1, h2.2]
  have hy2 : ‖(n : ℝ)⁻¹ • y - t‖ ≤ r₁ := by
    have e : (n : ℝ)⁻¹ • y - t = (n : ℝ)⁻¹ • (y - (n : ℝ) • t) := by
      rw [smul_sub, inv_smul_smul₀ hn0.ne']
    rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hn0.le, inv_mul_eq_div]
    exact (div_le_div_of_nonneg_right hy1 hn0.le).trans hr
  obtain ⟨-, hub⟩ := Moments.ExpArray.support_bounds hsupp hP hn0 y ht hy2
  rw [← hpt] at hub
  have hlow : 0 ≤ M.μ.1 (point v - point u) - inner ℝ P (point v - point u) :=
    sub_nonneg.mpr (hP.2 _)
  rw [abs_of_nonneg hlow]
  refine hub.trans ?_
  have h1 : ‖y - (n : ℝ) • t‖ ^ 2 ≤ ((m : ℝ) * ((L : ℝ) * (2 * W M K A n))) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) (hy1.trans ?_) 2
    gcongr
  have h2 : C₀ * ‖y - (n : ℝ) • t‖ ^ 2 / n ≤ C₀ * (4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2) * Q M K A n := by
    rw [div_le_iff₀ hn0]
    have e : ((m : ℝ) * ((L : ℝ) * (2 * W M K A n))) ^ 2 =
        4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2 * (n * Q M K A n) := by
      rw [← hWn]
      ring
    rw [e] at h1
    calc C₀ * ‖y - (n : ℝ) • t‖ ^ 2 ≤ C₀ * (4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2 * (n * Q M K A n)) :=
          mul_le_mul_of_nonneg_left h1 hC₀
      _ = C₀ * (4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2) * Q M K A n * n := by ring
  have h3 : C₀ * (n : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ C₀ * D * Q M K A n := by
    calc C₀ * (n : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ) = C₀ * ((n : ℝ) * ‖t - M.t₀‖ ^ (2 + M.δ)) := by ring
      _ ≤ C₀ * (D * Q M K A n) := mul_le_mul_of_nonneg_left hD hC₀
      _ = C₀ * D * Q M K A n := by ring
  linarith only [h2, h3, show C₀ * (4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2 + D) * Q M K A n =
    C₀ * (4 * (m : ℝ) ^ 2 * (L : ℝ) ^ 2) * Q M K A n + C₀ * D * Q M K A n by ring]

/-- **The bound of `sup_{Γ_G}|Φ|`**: `|Φ| ≤ a + S/Q_n` on `Γ_G`, for `S` above the variables
`X_{jk}` on the pairs of cubes covering `Γ_G`, if `|μ(v−u) − ζ_t·(v−u)| ≤ a Q_n` on `Γ_G`. -/
theorem abs_normSlabTime_le {M : Model m} {K : ℕ} {A : ℝ} {n L i : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {P : Pt m} {o g : Fin m → ℤ} (hw : 1 ≤ wInt M K A n)
    (hQ : 0 < Q M K A n) {X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ} {ω : Config m}
    (hX : FineGood n (wInt M K A n) L t i o g M.μ X ω) {S : Config m → ℝ}
    (hS : ∀ jk ∈ finePairs L o g, ∀ ω, X jk ω ≤ S ω) {a : ℝ}
    {u v : Vertex m} (hu : u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n))
    (hv : v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n))
    (hdrift : |M.μ.1 (point v - point u) - inner ℝ P (point v - point u)| ≤ a * Q M K A n) :
    |normSlabTime M K A ω n P i u v| ≤ a + S ω / Q M K A n := by
  set w := wInt M K A n
  have hw0 : 0 < w := hw
  have hu1 : u.1 = ((i : ℤ) - 1) * n := (mem_subcubeFace_iff.mp hu).1
  have hv1 : v.1 = (i : ℤ) * n := (mem_subcubeFace_iff.mp hv).1
  set j := rowIndex n w t ((i : ℤ) - 1) u.2
  set k := rowIndex n w t (i : ℤ) v.2
  have hjk : (j, k) ∈ finePairs L o g :=
    Finset.mem_product.mpr ⟨rowIndex_mem_rowBox hw hu, rowIndex_mem_rowBox hw hv⟩
  have huc : u ∈ finePairCube₁ n w t i j := rowCube_subset_transverseCube hw0 t _ j ⟨hu1, rfl⟩
  have hvc : v ∈ finePairCube₂ n w t i k := rowCube_subset_finePairCube₂ hw0 t i k ⟨hv1, rfl⟩
  have e1 := hX.2 (j, k) hjk u huc v hvc
  rw [hu1, hv1] at e1
  have f1 := hS (j, k) hjk ω
  have e2 : normSlabTime M K A ω n P i u v =
      (slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v - M.μ.1 (point v - point u)) /
          Q M K A n +
        (M.μ.1 (point v - point u) - inner ℝ P (point v - point u)) / Q M K A n := by
    unfold normSlabTime
    rw [← add_div]
    ring_nf
  rw [e2]
  have h1 : |(slabTimeReal ω (((i : ℤ) - 1) * n) ((i : ℤ) * n) u v -
      M.μ.1 (point v - point u)) / Q M K A n| ≤ S ω / Q M K A n := by
    rw [abs_div, abs_of_pos hQ]
    exact div_le_div_of_nonneg_right (e1.trans f1) hQ.le
  have h2 : |(M.μ.1 (point v - point u) - inner ℝ P (point v - point u)) / Q M K A n| ≤ a := by
    rw [abs_div, abs_of_pos hQ, div_le_iff₀ hQ]
    exact hdrift
  exact (abs_add_le _ _).trans (by linarith only [h1, h2])

/-! ### The modulus -/

/-- **The modulus on `Γ_G`** (the proof of Lemma `lem:labels`: equation `eq:modulus` "holds for
`T^{(i)}` with `2ηQ_n` in place of `ηQ_n`"): equations `eq:modulus` and `eq:profiledifference` on a
pair of cubes `I, I'` containing the two faces bound `|Φ(u,v) − Φ(u_g,v_g)|` by a measurable
variable of `L^k` norm at most `η + 2c/Q_n + 2C_p/Q_n`, for the mesh of spacing `w τ` with
`m w τ ≤ h W_n`. -/
theorem exists_labelModError {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {n L i : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {o g : Fin m → ℤ} {P : Pt m} (hQ : 0 < Q M K A n)
    (hn : 2 ≤ n) (hw : 0 < wInt M K A n) {τ h : ℝ} (hτ : 0 < τ)
    (hτh : (m : ℝ) * ((wInt M K A n : ℝ) * τ) ≤ h * W M K A n) {I I' : Set (Vertex m)}
    (hI : subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n) ⊆ I)
    (hI' : subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n) ⊆ I')
    {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 ≤ η)
    (hmodF : ∃ X : Config m → ℝ, eLpNorm X k M.P ≤ ENNReal.ofReal (η * Q M K A n) ∧
      ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ u₂ ∈ I, ∀ v ∈ I', ∀ v₂ ∈ I',
        ‖point u - point u₂‖ ≤ h * W M K A n → ‖point v - point v₂‖ ≤ h * W M K A n →
        |passageTimeReal ω u v - passageTimeReal ω u₂ v₂ -
          inner ℝ P (point v - point u - point v₂ + point u₂)| ≤ X ω)
    {c Cpd : ℝ} (hc : 0 ≤ c) (hCpd : 0 < Cpd)
    (hpdF : ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 Cpd X ∧ ∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I',
      (passageTime ω u v : ℝ≥0∞) ≤ slabTime ω u.1 v.1 u v ∧
      slabTimeReal ω u.1 v.1 u v - passageTimeReal ω u v ≤ c + X ω) :
    ∃ Z : Config m → ℝ, Measurable Z ∧
      eLpNorm Z k M.P ≤ ENNReal.ofReal (η + (2 * c / Q M K A n +
        2 * ((2 * (1 + (k.factorial : ℝ))) ^ (1 / (k : ℝ)) * Cpd) / Q M K A n)) ∧
      ∀ᵐ ω ∂M.P, ∀ p ∈ blockFacePairs n (wInt M K A n) L t i o g,
        |normSlabTime M K A ω n P i p.1 p.2 - normSlabTime M K A ω n P i
          (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n)
            (meshIndex (wInt M K A n) L t o g τ p.1))
          (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n)
            (meshIndex (wInt M K A n) L t o g τ p.2))| ≤ Z ω := by
  have := hM.probP
  obtain ⟨Xmod₀, hXmod₀, hmodae⟩ := hmodF
  obtain ⟨Xmod, hXmodm, hXeq, hXmod⟩ := exists_measurable_eq_of_eLpNorm_le hXmod₀
  obtain ⟨Xpd₀, hXpdos, hpdae⟩ := hpdF
  have hXpdm : Measurable (hXpdos.1.mk Xpd₀) := hXpdos.1.measurable_mk
  have hXpdeq := hXpdos.1.ae_eq_mk
  have hCp : 0 ≤ (2 * (1 + (k.factorial : ℝ))) ^ (1 / (k : ℝ)) * Cpd := by positivity
  have hXpd := eLpNorm_posPart_le_of_isOs hCpd (hXpdos.congr hXpdeq) hk
  refine ⟨fun ω => (Xmod ω + 2 * c + 2 * max (hXpdos.1.mk Xpd₀ ω) 0) / Q M K A n, ?_,
    eLpNorm_meshError_le hQ hk hη hc hCp hXmod hXpd, ?_⟩
  · exact ((hXmodm.add measurable_const).add
      ((hXpdm.max measurable_const).const_mul 2)).div_const _
  filter_upwards [hmodae, hpdae, hXeq, hXpdeq] with ω hmω hpω hmeq hpeq p hp
  obtain ⟨hu, hv⟩ := hp
  set u := p.1
  set v := p.2
  have hu₂ := blockRep_mem (τ := τ) hu
  have hv₂ := blockRep_mem (τ := τ) hv
  have hu1 := (mem_subcubeFace_iff.mp hu).1
  have hv1 := (mem_subcubeFace_iff.mp hv).1
  have hu₂1 := (mem_subcubeFace_iff.mp hu₂).1
  have hv₂1 := (mem_subcubeFace_iff.mp hv₂).1
  have hdu := (norm_sub_blockRep_le hw hτ hu).trans hτh
  have hdv := (norm_sub_blockRep_le hw hτ hv).trans hτh
  have hmod := hmω u (hI hu) _ (hI hu₂) v (hI' hv) _ (hI' hv₂) hdu hdv
  rw [hmeq] at hmod
  obtain ⟨p1, p2⟩ := hpω u (hI hu) v (hI' hv)
  obtain ⟨p3, p4⟩ := hpω _ (hI hu₂) _ (hI' hv₂)
  rw [hpeq] at p2 p4
  rw [hu1, hv1] at p1 p2
  rw [hu₂1, hv₂1] at p3 p4
  have hpq : ((i : ℤ) - 1) * n + 2 ≤ (i : ℤ) * n := by
    have : (2 : ℤ) ≤ n := by exact_mod_cast hn
    linarith
  have hlow : ((i : ℤ) - 1) * n ≤ (i : ℤ) * n := by linarith
  refine abs_normSlabTime_sub_le hQ hmod p1 p2 p3 p4 ?_ ?_
  · exact Responses.slabTime_ne_top ω hpq ⟨hu1.ge, hu1.le.trans hlow⟩ ⟨hv1.ge.trans' hlow, hv1.le⟩
  · exact Responses.slabTime_ne_top ω hpq ⟨hu₂1.ge, hu₂1.le.trans hlow⟩
      ⟨hv₂1.ge.trans' hlow, hv₂1.le⟩

/-! ### The estimates in one block -/

/-- **Steps 1 and 2 of the proof of [AB26, Lemma 6.2], as the proof of Lemma `lem:labels` changes
them, in one block.** Let `S ≥ 0` be above the variables of Proposition `prop:profiles` on the pairs
of cubes covering `Γ_G`, with a moment of order `2k` of `S/Q_n` at most `c`; let `π(L)` bound the
event, `|μ − ζ_t·| ≤ a Q_n` on `Γ_G`, and `Z` bound `|Φ(u,v) − Φ(u_g,v_g)|` on `Γ_G`, with
`‖Z‖_k ≤ ε₂`. Then one variable `Y` of `L^k` norm at most `ε₁ + ε₂ + (a − B/2)₊ + ε₃` has, on `Γ_G`,
`|Φ − Ψ| + |Ψ − Ψ(u_g,v_g)| + (|Ψ(u_g,v_g)| − B)₊ ≤ Y`.

This is the paper's argument: the Hölder step, then the modulus and the bound of `sup|Φ|` inherited
by `Ψ`, the latter at the clipping level `B = L⁴`. -/
theorem exists_labelBlockError {M : Model m} (hM : M.Standing) {Cd T : ℝ} (hCd : 0 ≤ Cd)
    (hTube : TubeProperty m Cd T) {K : ℕ} {A : ℝ} (hA : 1 ≤ A) {n L i : ℕ} (hn : 2 ≤ n)
    (hw : 1 ≤ wInt M K A n) (hQ : 0 < Q M K A n) {t : EuclideanSpace ℝ (Fin m)} (ht : ‖t‖ ≤ T)
    (hi : 1 ≤ i) {P : Pt m} {o g : Fin m → ℤ}
    {X : (Fin m → ℤ) × (Fin m → ℤ) → Config m → ℝ}
    (hX : ∀ᵐ ω ∂M.P, FineGood n (wInt M K A n) L t i o g M.μ X ω) {S : Config m → ℝ}
    (hSm : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω) (hS : ∀ jk ∈ finePairs L o g, ∀ ω, X jk ω ≤ S ω)
    {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∫⁻ ω, ENNReal.ofReal ((S ω / Q M K A n) ^ (2 * k)) ∂M.P ≤ ENNReal.ofReal c)
    {CR : ℝ} (hCR : 0 ≤ CR)
    (hrad : ∀ jk ∈ finePairs L o g,
      ∫⁻ ω, fineRadius n (wInt M K A n) t i (W M K A n) jk ω ^ (8 * (m + 1)) ∂M.P ≤
        ENNReal.ofReal CR)
    {a : ℝ} (hdrift : ∀ u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n),
      ∀ v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n),
        |M.μ.1 (point v - point u) - inner ℝ P (point v - point u)| ≤ a * Q M K A n)
    {τ : ℝ} {Z : Config m → ℝ} (hZm : Measurable Z) {ε₁ ε₂ ε₃ B : ℝ}
    (hZ : eLpNorm Z k M.P ≤ ENNReal.ofReal ε₂)
    (hmod : ∀ᵐ ω ∂M.P, ∀ p ∈ blockFacePairs n (wInt M K A n) L t i o g,
      |normSlabTime M K A ω n P i p.1 p.2 - normSlabTime M K A ω n P i
        (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n)
          (meshIndex (wInt M K A n) L t o g τ p.1))
        (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n)
          (meshIndex (wInt M K A n) L t o g τ p.2))| ≤ Z ω)
    (hB : 0 < B) (hε₁0 : 0 ≤ ε₁) (hε₂0 : 0 ≤ ε₂) (hε₃0 : 0 ≤ ε₃)
    (hε₁ : Real.sqrt (labelLeaveProb m Cd CR L) * Real.sqrt (2 ^ (2 * k) * (2 * c)) ≤ ε₁ ^ k)
    (hε₃ : c ≤ (2 * B * ε₃) ^ k) :
    ∃ Y : Config m → ℝ,
      eLpNorm Y k M.P ≤ ENNReal.ofReal (ε₁ + ε₂ + (max (a - B / 2) 0 + ε₃)) ∧
      ∀ᵐ ω ∂M.P, ∀ u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n),
        ∀ v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n),
        |normSlabTime M K A ω n P i u v -
            labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω u v| +
          |labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω u v -
            labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω
              (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n)
                (meshIndex (wInt M K A n) L t o g τ u))
              (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n)
                (meshIndex (wInt M K A n) L t o g τ v))| +
          max (|labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω
              (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n)
                (meshIndex (wInt M K A n) L t o g τ u))
              (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n)
                (meshIndex (wInt M K A n) L t o g τ v))| - B) 0 ≤ Y ω := by
  have := hM.probP
  set w := wInt M K A n with hwdef
  set G := block n w L t i o g with hGdef
  set Γ := blockFacePairs n w L t i o g with hΓdef
  set Qn := Q M K A n with hQndef
  set g₀ : Config m → ℝ := fun ω => S ω / Qn with hg₀def
  have hg₀m : Measurable g₀ := hSm.div_const _
  have hg₀0 : ∀ ω, 0 ≤ g₀ ω := fun ω => div_nonneg (hS0 ω) hQ.le
  have hk2 : 1 ≤ 2 * k := by omega
  have hc' : ∫⁻ ω, ENNReal.ofReal (|g₀ ω| ^ (2 * k)) ∂M.P ≤ ENNReal.ofReal c := by
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hc
    rw [abs_of_nonneg (hg₀0 ω)]
  have hg₀int : Integrable g₀ M.P :=
    integrable_of_lintegral_ofReal_pow_lt hg₀m.aestronglyMeasurable hk2 hc'
  -- the bound of `sup_{Γ_G}|Φ|`
  have hsup : ∀ᵐ ω ∂M.P, ∀ p ∈ Γ, |normSlabTime M K A ω n P i p.1 p.2| ≤ a + g₀ ω := by
    filter_upwards [hX] with ω hω p hp
    exact abs_normSlabTime_le hw hQ hω hS hp.1 hp.2 (hdrift _ hp.1 _ hp.2)
  have hΨ := ae_abs_labelPsi_le hM G hg₀m hg₀int hsup
  have hint : ∀ᵐ ω ∂M.P, ∀ p ∈ Γ, Integrable (fun ω' =>
      normSlabTime M K A (outsideSplice G (ω', ω)) n P i p.1 p.2) M.P :=
    hΨ.mono fun ω h p hp => (h p hp).1
  -- the Hölder step
  obtain ⟨E, hE, hπ, hEae⟩ := exists_labelLeaveEvent (P := P) hM hCd hTube hA hn hw hQ ht hi hX hS
    hCR hrad
  obtain ⟨Y₁, hY₁m, hY₁, hY₁ae⟩ := exists_abs_sub_labelPsi_le hM G hg₀m hg₀0 hE hEae hint hk
    (labelLeaveProb_nonneg m hCR L) hπ hc0 hc hε₁0 hε₁
  -- the modulus, inherited
  let ρ : Vertex m × Vertex m → Vertex m × Vertex m := fun p =>
    (blockRep w L t o g τ (((i : ℤ) - 1) * n) (meshIndex w L t o g τ p.1),
      blockRep w L t o g τ ((i : ℤ) * n) (meshIndex w L t o g τ p.2))
  have hρ : ∀ p ∈ Γ, ρ p ∈ Γ := fun p hp => ⟨blockRep_mem hp.1, blockRep_mem hp.2⟩
  have hZmom := lintegral_ofReal_pow_le_of_eLpNorm_le hk hε₂0 hZ
  have hZint : Integrable Z M.P :=
    integrable_of_lintegral_ofReal_pow_lt hZm.aestronglyMeasurable hk hZmom
  have hΨmod := ae_abs_labelPsi_sub_le hM G hρ hZm hZint hmod hint
  have hY₂ : eLpNorm (psiMean M.P G Z) k M.P ≤ ENNReal.ofReal ε₂ :=
    eLpNorm_le_ofReal_of_lintegral_le (measurable_psiMean G hZm).aestronglyMeasurable hk hε₂0
      ((lintegral_ofReal_psiMean_pow_le hM G hZm hk).trans hZmom)
  -- the clipping
  have hEg := (lintegral_ofReal_psiMean_pow_le hM G hg₀m hk2).trans hc'
  have hb : 0 ≤ max (a - B / 2) 0 := le_max_right _ _
  have hB2 : 0 < (2 * B) ^ k := by positivity
  have hY₃ : eLpNorm (fun ω => psiMean M.P G g₀ ω ^ 2 / (2 * B)) k M.P ≤ ENNReal.ofReal ε₃ := by
    refine eLpNorm_le_ofReal_of_lintegral_le
      (((measurable_psiMean G hg₀m).pow_const 2).div_const _).aestronglyMeasurable hk hε₃0 ?_
    have e : ∀ ω, ENNReal.ofReal (|psiMean M.P G g₀ ω ^ 2 / (2 * B)| ^ k) =
        ENNReal.ofReal (|psiMean M.P G g₀ ω| ^ (2 * k)) * ENNReal.ofReal (((2 * B) ^ k)⁻¹) := by
      intro ω
      rw [← ENNReal.ofReal_mul (by positivity), abs_div, abs_of_pos (by positivity : 0 < 2 * B),
        abs_pow, div_pow, ← pow_mul, div_eq_mul_inv]
    simp_rw [e]
    have hm : Measurable fun ω => ENNReal.ofReal (|psiMean M.P G g₀ ω| ^ (2 * k)) :=
      ((_root_.continuous_abs.measurable.comp (measurable_psiMean G hg₀m)).pow_const _).ennreal_ofReal
    rw [lintegral_mul_const _ hm]
    calc _ ≤ ENNReal.ofReal c * ENNReal.ofReal (((2 * B) ^ k)⁻¹) := by gcongr
      _ = ENNReal.ofReal (c * ((2 * B) ^ k)⁻¹) := (ENNReal.ofReal_mul hc0).symm
      _ ≤ ENNReal.ofReal (ε₃ ^ k) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← div_eq_mul_inv, div_le_iff₀ hB2, ← mul_pow, mul_comm ε₃]
          exact hε₃
  have hY₃' := eLpNorm_add_le_ofReal hk hb hε₃0 (eLpNorm_const_le_ofReal hb hk) hY₃
  refine ⟨fun ω => Y₁ ω + psiMean M.P G Z ω +
    (max (a - B / 2) 0 + psiMean M.P G g₀ ω ^ 2 / (2 * B)), ?_, ?_⟩
  · exact eLpNorm_add_le_ofReal hk (by positivity) (by positivity)
      (eLpNorm_add_le_ofReal hk hε₁0 hε₂0 hY₁ hY₂) hY₃'
  · filter_upwards [hY₁ae, hΨmod, hΨ] with ω h1 h2 h3 u hu v hv
    have hp : (u, v) ∈ Γ := ⟨hu, hv⟩
    have e1 := h1 _ hp
    have e2 := h2 _ hp
    have e3 := max_abs_sub_le_of_le hB (h3 _ (hρ _ hp)).2
    simp only [ρ] at e2 e3
    linarith only [e1, e2, e3]

end CurvatureVariance.Paper.Gain
