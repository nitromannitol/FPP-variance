/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ExpArraySlabs
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The two halves of equation `eq:rowenergy`

At a fixed scale (`Scale`), with a subgradient `P_t` of `μ` at `(1, t)`, `t = Mst/(Ms)`, the
minimum `F` of equation `eq:F` from `0` to `(Ms, Mst)` (the proof of Lemma `lem:rowenergy`):

* `exists_upper`: `F − μ(Ms, Mst) ≤ C M Q_s + O₁(θ)`, `θ = C(1) Q_s`, along the floor tuple
  `y_i = ⌊ist⌋` (Proposition `prop:profiles` for its singleton cubes, independence over the slabs,
  exponential Markov).
* `exists_lower`: almost surely, for every minimizing tuple,
  `μ(Ms, Mst) − F + (c/4) Q_s ∑ᵢ |J_i − J_{i−1}|² ≤ C M Q_s + O₁(θ)` (the entries `entry_lower`,
  the slab variables `rowE`, and the sum over index paths `exists_isOs_pathSum`); the linear terms
  telescope to `P_t·(Ms, Mst) = μ(Ms, Mst)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Moments.ExpArray

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

/-! ## Hypotheses at a scale -/

/-- Proposition `prop:profiles` at width `s` with `b = 1` and constant `C(1) = Cb`. -/
def ShortAt (M : Model m) (K : ℕ) (A : ℝ) (s : ℕ) (Cb : ℝ) : Prop :=
  ∀ (t' : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
    IsCubePair M K A s 1 t' I I' → ‖t' - M.t₀‖ ≤ 4 / 5 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
      Contracts.ShortConclusion M K A s Cb t' I I'

/-! ## Tuples from `0` -/

/-- The point `u_i = (is, Y_i)` of a tuple at the start of slab `i`. -/
def lowPt (s : ℕ) {Ms : ℕ} (Y : Fin (Ms + 1) → Fin m → ℤ) (i : Fin Ms) : Vertex m :=
  (((i : ℕ) : ℤ) * s, Y i.castSucc)

/-- The point `u_{i+1} = ((i+1)s, Y_{i+1})` of a tuple at the end of slab `i`. -/
def highPt (s : ℕ) {Ms : ℕ} (Y : Fin (Ms + 1) → Fin m → ℤ) (i : Fin Ms) : Vertex m :=
  ((((i : ℕ) : ℤ) + 1) * s, Y i.succ)

/-- The slab passage time `D_i(u_i, u_{i+1})` of a tuple. -/
noncomputable def slabCost (ω : Config m) (s : ℕ) {Ms : ℕ} (Y : Fin (Ms + 1) → Fin m → ℤ)
    (i : Fin Ms) : ℝ :=
  slabTimeReal ω (((i : ℕ) : ℤ) * s) ((((i : ℕ) : ℤ) + 1) * s) (lowPt s Y i) (highPt s Y i)

/-- The step `u_{i+1} − u_i` of a tuple, in `ℝ^d`. -/
def stepVec (s : ℕ) {Ms : ℕ} (Y : Fin (Ms + 1) → Fin m → ℤ) (i : Fin Ms) : Pt m :=
  point (highPt s Y i) - point (lowPt s Y i)

/-- Telescoping over `Fin`. -/
theorem sum_fin_succ_sub {G : Type*} [AddCommGroup G] :
    ∀ {n : ℕ} (f : Fin (n + 1) → G),
      ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0
  | 0, f => by simp
  | n + 1, f => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [sum_fin_succ_sub (fun i : Fin (n + 1) => f i.castSucc)]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    abel

/-- The real cost of a tuple from `0` is the sum of its slab passage times. -/
theorem tupleCost_toReal (ω : Config m) {s : ℕ} (hs : 2 ≤ s) {Ms : ℕ}
    (Y : Fin (Ms + 1) → Fin m → ℤ) :
    (tupleCost ω 0 s Y).toReal = ∑ i : Fin Ms, slabCost ω s Y i := by
  unfold tupleCost
  rw [ENNReal.toReal_sum fun i _ => Responses.tuple_slabTime_ne_top ω 0 hs Y i]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [slabCost, slabTimeReal, tuplePoint, lowPt, highPt]

/-- The steps telescope: `∑ᵢ P·(u_{i+1} − u_i) = P·(Ms, Y_M)` for a tuple with `Y₀ = 0`. -/
theorem sum_inner_stepVec (P : Pt m) (s : ℕ) {Ms : ℕ} (Y : Fin (Ms + 1) → Fin m → ℤ)
    (h0 : Y 0 = 0) :
    ∑ i : Fin Ms, inner ℝ P (stepVec s Y i) =
      inner ℝ P (point (((Ms * s : ℕ) : ℤ), Y (Fin.last Ms))) := by
  rw [← inner_sum]
  congr 1
  have h := sum_fin_succ_sub (fun i : Fin (Ms + 1) => point ((((i : ℕ) : ℤ) * s : ℤ), Y i))
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_zero, h0] at h
  push_cast at h
  simp only [stepVec, lowPt, highPt]
  rw [h]
  simp only [zero_mul]
  rw [show point ((0 : ℤ), (0 : Fin m → ℤ)) = 0 from Infra.FPP.point_zero, sub_zero]
  push_cast
  rfl

/-- The target `(ℓ, z)` is `ℓ · (1, z/ℓ)`. -/
theorem point_target {ℓ : ℕ} (hℓ : 0 < ℓ) (z : Fin m → ℤ) :
    point ((ℓ : ℤ), z) = (ℓ : ℝ) • slopeVec (targetSlope ℓ z) := by
  unfold point slopeVec targetSlope
  rw [← WithLp.toLp_smul, Prod.smul_mk, smul_eq_mul, mul_one,
    smul_inv_smul₀ (by positivity : (ℓ : ℝ) ≠ 0)]
  simp

/-- `P_t·(ℓ, z) = μ(ℓ, z)` for a subgradient `P_t` at `(1, z/ℓ)`. -/
theorem inner_target {μ : PtNorm m} {ℓ : ℕ} (hℓ : 0 < ℓ) {z : Fin m → ℤ} {P : Pt m}
    (hP : IsSubgradient μ (slopeVec (targetSlope ℓ z)) P) :
    inner ℝ P (point ((ℓ : ℤ), z)) = μ.1 (point ((ℓ : ℤ), z)) := by
  rw [point_target hℓ, inner_smul_right, hP.1, map_smul_eq_mul,
    Real.norm_of_nonneg (by positivity)]

/-! ## The floor tuple -/

/-- The floor tuple `y_i = ⌊ist⌋`. -/
noncomputable def floorTuple (s : ℕ) (t : EuclideanSpace ℝ (Fin m)) (Ms : ℕ) :
    Fin (Ms + 1) → Fin m → ℤ :=
  fun i => floorPt s t ((i : ℕ) : ℤ)

theorem floorTuple_step (s : ℕ) (t : EuclideanSpace ℝ (Fin m)) {Ms : ℕ} (i : Fin Ms) :
    floorTuple s t Ms i.succ - floorTuple s t Ms i.castSucc =
      floorPt s t (((i : ℕ) : ℤ) + 1) - floorPt s t ((i : ℕ) : ℤ) := by
  simp [floorTuple, Fin.val_succ]

/-- The floor tuple ends at the target. -/
theorem floorPt_last {Ms s : ℕ} (h : 0 < Ms * s) (z : Fin m → ℤ) :
    floorPt s (targetSlope (Ms * s) z) (Ms : ℤ) = z := by
  funext k
  have h' : (0 : ℝ) < Ms * s := by exact_mod_cast h
  simp only [floorPt, targetSlope, PiLp.smul_apply, Infra.FPP.transversePoint_apply, smul_eq_mul,
    Int.cast_natCast, Nat.cast_mul]
  rw [show (Ms : ℝ) * s * (((Ms : ℝ) * s)⁻¹ * z k) = z k by
    rw [← mul_assoc, mul_inv_cancel₀ h'.ne', one_mul]]
  exact Int.floor_intCast _

section Bounds

variable {M : Model m} {K : ℕ} {A : ℝ} {s Ms : ℕ} {z : Fin m → ℤ} {r₁ c₀ C₀ Cb : ℝ}
  {P : Pt m}

/-- The floor tuple is admissible. -/
theorem floorTuple_adm (h : Scale M K A s Ms (targetSlope (Ms * s) z) r₁) (hMs : 0 < Ms * s) :
    IsAdmissibleTuple M s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)
      (floorTuple s (targetSlope (Ms * s) z) Ms) := by
  refine ⟨?_, ?_, fun i => ?_⟩
  · funext k; simp [floorTuple, floorPt]
  · simp only [floorTuple, Fin.val_last]
    exact floorPt_last hMs z
  · rw [floorTuple_step]
    have h1 := norm_floorPt_sub_le s (targetSlope (Ms * s) z) ((i : ℕ) : ℤ)
    have h2 := h.hsa
    have h3 := Real.sqrt_nonneg (m : ℝ)
    linarith

/-- **Upper bound, deterministic part**: along the floor tuple, `F − μ(Ms, Mst) ≤
∑ᵢ (D_i − μ(u_{i+1} − u_i)) + M (Cm + 8C) Q_s`. -/
theorem upper_det (hM : M.Standing) (h : Scale M K A s Ms (targetSlope (Ms * s) z) r₁)
    (hC₀ : 0 < C₀) (hsupp : SupportAt M c₀ C₀ r₁)
    (hP : IsSubgradient M.μ (slopeVec (targetSlope (Ms * s) z)) P) (hMs : 0 < Ms * s)
    (ω : Config m) :
    (slabMin M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)).toReal -
        M.μ.1 (point (((Ms * s : ℕ) : ℤ), z)) ≤
      ∑ i, (slabCost ω s (floorTuple s (targetSlope (Ms * s) z) Ms) i -
          M.μ.1 (stepVec s (floorTuple s (targetSlope (Ms * s) z) Ms) i)) +
        Ms * ((C₀ * m + 8 * C₀) * Q M K A s) := by
  have hadm := floorTuple_adm h hMs
  set t := targetSlope (Ms * s) z with ht
  set yU := floorTuple s t Ms with hyU
  have hF : (slabMin M ω s Ms t 0 (((Ms * s : ℕ) : ℤ), z)).toReal ≤ ∑ i, slabCost ω s yU i := by
    rw [← tupleCost_toReal ω h.two_le]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ =>
      Responses.tuple_slabTime_ne_top ω 0 h.two_le yU i) (Responses.slabMin_le_tupleCost hadm ω)
  have hlin := sum_inner_stepVec P s yU hadm.1
  rw [hadm.2.1, inner_target hMs hP] at hlin
  have hent : ∀ i : Fin Ms, M.μ.1 (stepVec s yU i) - inner ℝ P (stepVec s yU i) ≤
      (C₀ * m + 8 * C₀) * Q M K A s := by
    intro i
    refine entry_upper hM h hC₀ (c₀ := c₀) hsupp hP (by simp [lowPt, highPt]; ring) ?_
    simp only [lowPt, highPt]
    rw [floorTuple_step]
    exact norm_floorPt_sub_le s t _
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hent i
  have e1 : ∑ i : Fin Ms, (M.μ.1 (stepVec s yU i) - inner ℝ P (stepVec s yU i)) =
      ∑ i, M.μ.1 (stepVec s yU i) - ∑ i, inner ℝ P (stepVec s yU i) := Finset.sum_sub_distrib _ _
  have e2 : ∑ _i : Fin Ms, (C₀ * m + 8 * C₀) * Q M K A s = Ms * ((C₀ * m + 8 * C₀) * Q M K A s) :=
    by simp
  have e3 : ∑ i, (slabCost ω s yU i - M.μ.1 (stepVec s yU i)) =
      ∑ i, slabCost ω s yU i - ∑ i, M.μ.1 (stepVec s yU i) := Finset.sum_sub_distrib _ _
  linarith

/-- **Upper bound** (in equation `eq:rowenergy`):
`F − μ(Ms, Mst) ≤ M (Cm + 8C) Q_s + θ log(2·2^M) + O₁(θ)`, `θ = C(1) Q_s`. -/
theorem exists_upper (hM : M.Standing) (h : Scale M K A s Ms (targetSlope (Ms * s) z) r₁)
    (hCb : 0 < Cb) (hShortK : ShortAt M K A s Cb) (hC₀ : 0 < C₀) (hsupp : SupportAt M c₀ C₀ r₁)
    (hP : IsSubgradient M.μ (slopeVec (targetSlope (Ms * s) z)) P) (hMs : 0 < Ms * s) :
    ∃ G : Config m → ℝ, IsOs M.P 1 (Cb * Q M K A s) G ∧ ∀ᵐ ω ∂M.P,
      (slabMin M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)).toReal -
          M.μ.1 (point (((Ms * s : ℕ) : ℤ), z)) ≤
        Ms * ((C₀ * m + 8 * C₀) * Q M K A s) + Cb * Q M K A s * Real.log (2 * 2 ^ Ms) + G ω := by
  have := hM.probF
  have := hM.probP
  set t := targetSlope (Ms * s) z with ht
  set yU := floorTuple s t Ms with hyU
  have hθ : 0 < Cb * Q M K A s := mul_pos hCb (by linarith [h.one_le_Q hM])
  obtain ⟨G, hG, hae⟩ := exists_isOs_sum_local hM.iid (fun i : Fin Ms => slabSet s i)
    (pairwise_disjoint_slabSet_fin s Ms)
    (fun i ω => slabCost ω s yU i - M.μ.1 (stepVec s yU i))
    (fun i => (measurable_slabTimeReal _ _ _ _).sub_const _)
    (fun i ω ω' hω => by
      simp only [slabCost]
      rw [slabTimeReal_congr _ _ (fun e he => hω e he)])
    hθ (fun i => isOs_slabStep hM h hCb hShortK ((i : ℕ) : ℤ) (u := lowPt s yU i)
      (v := highPt s yU i) rfl rfl (by
        simp only [lowPt, highPt]
        rw [floorTuple_step]
        exact norm_floorPt_sub_le s t _))
  refine ⟨G, hG, ?_⟩
  filter_upwards [hae] with ω hω
  have h1 := upper_det hM h hC₀ hsupp hP hMs ω
  linarith

/-! ## The lower bound -/

/-- Consecutive cube indices of an admissible tuple are allowed jumps. -/
theorem jump_mem_allowedSet (hM : M.Standing) (h : Scale M K A s Ms (targetSlope (Ms * s) z) r₁)
    {Y : Fin (Ms + 1) → Fin m → ℤ}
    (hY : IsAdmissibleTuple M s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) Y)
    (i : Fin Ms) :
    tupleIndex s (wInt M K A s) (targetSlope (Ms * s) z) Y i.succ -
        tupleIndex s (wInt M K A s) (targetSlope (Ms * s) z) Y i.castSucc ∈
      allowedSet (wInt M K A s) ((s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 +
        Real.sqrt m * ((wInt M K A s : ℝ) + 1)) := by
  set t := targetSlope (Ms * s) z with ht
  set w := wInt M K A s with hw
  set J := tupleIndex s w t Y with hJ
  have hw0 := h.w_pos hM
  rw [mem_allowedSet hw0]
  have hu : lowPt s Y i ∈ rowCube s w t ((i : ℕ) : ℤ) (J i.castSucc) :=
    ⟨rfl, by simp [hJ, tupleIndex, lowPt]⟩
  have hv : highPt s Y i ∈ rowCube s w t (((i : ℕ) : ℤ) + 1) (J i.succ) :=
    ⟨rfl, by simp [hJ, tupleIndex, highPt, Fin.val_succ]⟩
  have hg := entry_geometry hw0 hu hv
  simp only [lowPt, highPt] at hg
  have h1 := norm_sub_norm_le ((w : ℝ) • transversePoint (J i.succ - J i.castSucc))
    (transversePoint (Y i.succ - Y i.castSucc) - (s : ℝ) • t)
  rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)] at h1
  have h2 : ‖(w : ℝ) • transversePoint (J i.succ - J i.castSucc) -
      (transversePoint (Y i.succ - Y i.castSucc) - (s : ℝ) • t)‖ =
      ‖transversePoint (Y i.succ - Y i.castSucc) - (s : ℝ) • t -
        (w : ℝ) • transversePoint (J i.succ - J i.castSucc)‖ := by
    rw [← norm_neg]; congr 1; abel
  have h3 := hY.2.2 i
  linarith

/-- **Lower bound, deterministic part**: for a minimizing tuple,
`μ(Ms, Mst) − F + (c/4) Q_s ∑|ΔJ|² ≤ M C Q_s + ∑ᵢ (μ(u_{i+1} − u_i) − D_i − (c/4) Q_s |ΔJ_i|²)`. -/
theorem lower_det (hM : M.Standing) (h : Scale M K A s Ms (targetSlope (Ms * s) z) r₁)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hsupp : SupportAt M c₀ C₀ r₁)
    (hP : IsSubgradient M.μ (slopeVec (targetSlope (Ms * s) z)) P) (hMs : 0 < Ms * s)
    {ω : Config m} {Y : Fin (Ms + 1) → Fin m → ℤ}
    (hY : IsMinTuple M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) Y) :
    M.μ.1 (point (((Ms * s : ℕ) : ℤ), z)) -
        (slabMin M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)).toReal +
        c₀ / 4 * Q M K A s * ∑ i, indexJumpSq s (wInt M K A s) (targetSlope (Ms * s) z) Y i ≤
      Ms * ((9 * c₀ * m + 8 * C₀) * Q M K A s) +
        ∑ i, (M.μ.1 (stepVec s Y i) - slabCost ω s Y i -
          c₀ / 4 * Q M K A s * indexJumpSq s (wInt M K A s) (targetSlope (Ms * s) z) Y i) := by
  set t := targetSlope (Ms * s) z with ht
  set w := wInt M K A s with hw
  set Qs := Q M K A s with hQs
  set x := fun i => indexJumpSq s w t Y i with hx
  have hw0 := h.w_pos hM
  have hF : (slabMin M ω s Ms t 0 (((Ms * s : ℕ) : ℤ), z)).toReal = ∑ i, slabCost ω s Y i := by
    rw [← hY.2, tupleCost_toReal ω h.two_le]
  have hlin := sum_inner_stepVec P s Y hY.1.1
  rw [hY.1.2.1, inner_target hMs hP] at hlin
  have hent : ∀ i : Fin Ms, c₀ / 2 * Qs * x i - (9 * c₀ * m + 8 * C₀) * Qs ≤
      M.μ.1 (stepVec s Y i) - inner ℝ P (stepVec s Y i) := by
    intro i
    have hu : lowPt s Y i ∈ rowCube s w t ((i : ℕ) : ℤ) (tupleIndex s w t Y i.castSucc) :=
      ⟨rfl, by simp [tupleIndex, lowPt]⟩
    have hv : highPt s Y i ∈ rowCube s w t (((i : ℕ) : ℤ) + 1) (tupleIndex s w t Y i.succ) :=
      ⟨rfl, by simp [tupleIndex, highPt, Fin.val_succ]⟩
    exact entry_lower hM h hc₀ hC₀ hsupp hP hu hv (hY.1.2.2 i)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hent i
  have e1 : ∑ i : Fin Ms, (c₀ / 2 * Qs * x i - (9 * c₀ * m + 8 * C₀) * Qs) =
      c₀ / 2 * Qs * ∑ i, x i - Ms * ((9 * c₀ * m + 8 * C₀) * Qs) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
  have e2 : ∑ i : Fin Ms, (M.μ.1 (stepVec s Y i) - inner ℝ P (stepVec s Y i)) =
      ∑ i, M.μ.1 (stepVec s Y i) - ∑ i, inner ℝ P (stepVec s Y i) := Finset.sum_sub_distrib _ _
  have e3 : ∑ i : Fin Ms, (M.μ.1 (stepVec s Y i) - slabCost ω s Y i - c₀ / 4 * Qs * x i) =
      ∑ i, M.μ.1 (stepVec s Y i) - ∑ i, slabCost ω s Y i - c₀ / 4 * Qs * ∑ i, x i := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have e4 : ∑ i, indexJumpSq s w t Y i = ∑ i, x i := rfl
  rw [e4, e3, hF]
  linarith

/-- The exponential of the penalized sum is dominated by the product of the slab variables. -/
theorem lower_exp (hCb : 0 < Cb) (hQ : 0 < Q M K A s) {ω : Config m}
    {Y : Fin (Ms + 1) → Fin m → ℤ} {t : EuclideanSpace ℝ (Fin m)} :
    ENNReal.ofReal (Real.exp ((∑ i, (M.μ.1 (stepVec s Y i) - slabCost ω s Y i -
        c₀ / 4 * Q M K A s * indexJumpSq s (wInt M K A s) t Y i)) / (Cb * Q M K A s))) ≤
      ∏ i : Fin Ms, rowE M s (wInt M K A s) t (Cb * Q M K A s) i
          (tupleIndex s (wInt M K A s) t Y i.castSucc) (tupleIndex s (wInt M K A s) t Y i.succ) ω *
        ENNReal.ofReal (Real.exp (-(c₀ / (4 * Cb)) *
          ‖transversePoint (tupleIndex s (wInt M K A s) t Y i.succ -
            tupleIndex s (wInt M K A s) t Y i.castSucc)‖ ^ 2)) := by
  set w := wInt M K A s
  set Qs := Q M K A s
  have hsplit : (∑ i, (M.μ.1 (stepVec s Y i) - slabCost ω s Y i -
        c₀ / 4 * Qs * indexJumpSq s w t Y i)) / (Cb * Qs) =
      ∑ i, ((M.μ.1 (stepVec s Y i) - slabCost ω s Y i) / (Cb * Qs) +
        -(c₀ / (4 * Cb)) * ‖transversePoint (tupleIndex s w t Y i.succ -
            tupleIndex s w t Y i.castSucc)‖ ^ 2) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold indexJumpSq
    field_simp
    ring
  rw [hsplit, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  refine Finset.prod_le_prod fun i _ => ?_
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr
  have hu : lowPt s Y i ∈ rowCube s w t ((i : ℕ) : ℤ) (tupleIndex s w t Y i.castSucc) :=
    ⟨rfl, by simp [tupleIndex, lowPt]⟩
  have hv : highPt s Y i ∈ rowCube s w t (((i : ℕ) : ℤ) + 1) (tupleIndex s w t Y i.succ) :=
    ⟨rfl, by simp [tupleIndex, highPt, Fin.val_succ]⟩
  unfold rowE
  exact le_iSup₂_of_le _ hu (le_iSup₂_of_le _ hv le_rfl)

/-- **Lower bound** (equation `eq:rowenergy`): almost surely, for every minimizing tuple,
`μ(Ms, Mst) − F + (c/4) Q_s ∑|ΔJ|² ≤ M C Q_s + θ log(2 B_c^M) + O₁(θ)`, `θ = C(1) Q_s`,
`B_c = 2 (4/√min(c/(4C(1)), 1))^m`. -/
theorem exists_lower (hM : M.Standing) (h : Scale M K A s Ms (targetSlope (Ms * s) z) r₁)
    (hCb : 0 < Cb) (hShortK : ShortAt M K A s Cb) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hsupp : SupportAt M c₀ C₀ r₁)
    (hP : IsSubgradient M.μ (slopeVec (targetSlope (Ms * s) z)) P) (hMs : 0 < Ms * s) :
    ∃ G : Config m → ℝ, IsOs M.P 1 (Cb * Q M K A s) G ∧ ∀ᵐ ω ∂M.P,
      ∀ Y : Fin (Ms + 1) → Fin m → ℤ,
        IsMinTuple M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z) Y →
        M.μ.1 (point (((Ms * s : ℕ) : ℤ), z)) -
            (slabMin M ω s Ms (targetSlope (Ms * s) z) 0 (((Ms * s : ℕ) : ℤ), z)).toReal +
            c₀ / 4 * Q M K A s *
              ∑ i, indexJumpSq s (wInt M K A s) (targetSlope (Ms * s) z) Y i ≤
          Ms * ((9 * c₀ * m + 8 * C₀) * Q M K A s) +
            Cb * Q M K A s * Real.log (2 * (2 * (4 / Real.sqrt (min (c₀ / (4 * Cb)) 1)) ^ m) ^ Ms) +
            G ω := by
  have := hM.probF
  have := hM.probP
  set t := targetSlope (Ms * s) z with ht
  set w := wInt M K A s with hw
  have hw0 := h.w_pos hM
  have hQ : 0 < Q M K A s := by linarith [h.one_le_Q hM]
  have hθ : 0 < Cb * Q M K A s := mul_pos hCb hQ
  have hc' : 0 < c₀ / (4 * Cb) := by positivity
  have hBc1 : 1 ≤ 2 * (4 / Real.sqrt (min (c₀ / (4 * Cb)) 1)) ^ m := by
    have h1 : Real.sqrt (min (c₀ / (4 * Cb)) 1) ≤ 1 := Real.sqrt_le_one.mpr (min_le_right _ _)
    have h2 : 0 < Real.sqrt (min (c₀ / (4 * Cb)) 1) := Real.sqrt_pos.mpr (lt_min hc' one_pos)
    have h3 : 1 ≤ 4 / Real.sqrt (min (c₀ / (4 * Cb)) 1) := by rw [le_div_iff₀ h2]; linarith
    have h4 : 1 ≤ (4 / Real.sqrt (min (c₀ / (4 * Cb)) 1)) ^ m := one_le_pow₀ h3
    linarith
  obtain ⟨G, hG, hae⟩ := exists_isOs_pathSum hM.iid (fun i : Fin Ms => slabSet s i)
    (pairwise_disjoint_slabSet_fin s Ms) (fun i j k => rowE M s w t (Cb * Q M K A s) i j k)
    (fun i j k => measurable_rowE M s w t _ i j k)
    (fun i j k ω ω' hω => rowE_congr M s w t _ i j k hω)
    (allowedSet w ((s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 + Real.sqrt m * ((w : ℝ) + 1)))
    (fun i j k hjk => lintegral_rowE_le hM h hCb hShortK i ((mem_allowedSet hw0).mp hjk))
    (fun z => ENNReal.ofReal (Real.exp (-(c₀ / (4 * Cb)) * ‖transversePoint z‖ ^ 2))) hBc1
    (sum_gaussian_le _ hc') hθ
  refine ⟨G, hG, ?_⟩
  filter_upwards [hae] with ω hω Y hY
  have h1 := lower_det hM h hc₀ hC₀ hsupp hP hMs hY
  have hJ0 : tupleIndex s w t Y 0 = 0 := by
    funext k; simp [tupleIndex, rowIndex, hY.1.1]
  have h2 := hω (tupleIndex s w t Y) hJ0 (fun i => jump_mem_allowedSet hM h hY.1 i) _
    (lower_exp hCb hQ)
  linarith

end Bounds

end CurvatureVariance.Paper.Moments.ExpArray
