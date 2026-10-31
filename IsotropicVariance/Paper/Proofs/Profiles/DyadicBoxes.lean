/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.Tree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The dyadic subboxes of Lemma `lem:tree`

The geometry of the proof of Lemma `lem:tree`, for a box
`B = g(∏[−r_k, r_k])` centered at `x + te`, where `g` is a rigid motion. The paper takes `x = 0`,
`e = e₁` and writes `B = Θ([0,1]^d)`; here the coordinates of the box are those of `stdBox`.

* `subboxCenter`: the center of the dyadic subbox of generation `j` with index `μ`.
* `attachedPt`: the point attached to it, its center minus `2^{−j} t e`.
* `treePairs`: the set `𝒜_j` of pairs attached to a subbox of generation `j` and to one of its
  subboxes of generation `j + 1`.
* `attached_step`: equation `eq:treestep`. The difference of such a pair is `2^{−j−1} (v − x)` for
  a vertex `v` of `B`.
* `dyadicDepth`: the integer `j₀`, the largest with `2^{−j₀} t ≥ 4`.
* `chainIndex`: the nested subboxes containing a point, and `dist_attached_le`, the bound
  `|z − y_{j₀}| ≤ 9`.
-/

@[expose] public section

open Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

variable {m : ℕ}

/-! ## Nested dyadic intervals -/

/-- The two halves of an interval of generation `j`. -/
lemma cellCenter_child (j l b : ℕ) (R : ℝ) :
    cellCenter (2 ^ (j + 1)) R (2 * l + b) =
      cellCenter (2 ^ j) R l + ((2 : ℝ) ^ (j + 1))⁻¹ * ((2 * b - 1) * R) := by
  simp only [cellCenter, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, pow_succ]
  field_simp
  ring

/-- The index of the interval of generation `j` containing `y`, chosen by bisection, so that the
intervals are nested. -/
noncomputable def dyadicIndex (R y : ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 2 * dyadicIndex R y j +
      if y ≤ cellCenter (2 ^ j) R (dyadicIndex R y j) then 0 else 1

lemma exists_dyadicIndex_succ (R y : ℝ) (j : ℕ) :
    ∃ b, b < 2 ∧ dyadicIndex R y (j + 1) = 2 * dyadicIndex R y j + b :=
  ⟨if y ≤ cellCenter (2 ^ j) R (dyadicIndex R y j) then 0 else 1, by split_ifs <;> norm_num, rfl⟩

lemma dyadicIndex_spec {R y : ℝ} (hy : |y| ≤ R) (j : ℕ) :
    dyadicIndex R y j < 2 ^ j ∧
      |y - cellCenter (2 ^ j) R (dyadicIndex R y j)| ≤ ((2 : ℝ) ^ j)⁻¹ * R := by
  induction j with
  | zero => simpa [dyadicIndex, cellCenter] using hy
  | succ j ih =>
    obtain ⟨hlt, hle⟩ := ih
    set l := dyadicIndex R y j with hl
    set c := cellCenter (2 ^ j) R l with hc
    have hh : ((2 : ℝ) ^ j)⁻¹ = 2 * ((2 : ℝ) ^ (j + 1))⁻¹ := by
      rw [inv_two_pow_succ]; ring
    rw [hh] at hle
    obtain ⟨h1, h2⟩ := abs_le.mp hle
    by_cases hyc : y ≤ c
    · have e : dyadicIndex R y (j + 1) = 2 * l + 0 := by
        rw [dyadicIndex, ite_eq_left hyc]
      rw [e, cellCenter_child, ← hc]
      refine ⟨by rw [pow_succ]; omega, abs_le.mpr ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith
    · have e : dyadicIndex R y (j + 1) = 2 * l + 1 := by
        rw [dyadicIndex, ite_eq_right hyc]
      rw [e, cellCenter_child, ← hc]
      have hyc' := not_le.mp hyc
      refine ⟨by rw [pow_succ]; omega, abs_le.mpr ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith

/-! ## Subboxes and attached points -/

/-- The center of the dyadic subbox of generation `j` with index `μ ∈ {0, …, 2^j − 1}^d` of the
box `stdBox r₀ r`. -/
noncomputable def subboxCenter (r₀ : ℝ) (r : Fin m → ℝ) (j : ℕ) (μ : Fin (m + 1) → ℕ) : Pt m :=
  Pt.mk (cellCenter (2 ^ j) r₀ (μ 0))
    (WithLp.toLp 2 fun k => cellCenter (2 ^ j) (r k) (μ k.succ))

/-- The vertex of the box `stdBox r₀ r` with signs `2σ − 1`, for `σ ∈ {0, 1}^d`. -/
noncomputable def boxVertex (r₀ : ℝ) (r : Fin m → ℝ) (σ : Fin (m + 1) → ℕ) : Pt m :=
  Pt.mk ((2 * (σ 0 : ℝ) - 1) * r₀) (WithLp.toLp 2 fun k => (2 * (σ k.succ : ℝ) - 1) * r k)

lemma subboxCenter_child (r₀ : ℝ) (r : Fin m → ℝ) (j : ℕ) (μ σ : Fin (m + 1) → ℕ) :
    subboxCenter r₀ r (j + 1) (fun κ => 2 * μ κ + σ κ) =
      subboxCenter r₀ r j μ + ((2 : ℝ) ^ (j + 1))⁻¹ • boxVertex r₀ r σ := by
  apply pt_ext
  · simp [subboxCenter, boxVertex, cellCenter_child]
  · ext k
    simp [subboxCenter, boxVertex, cellCenter_child]

lemma abs_sign_mul_le {b : ℕ} (hb : b < 2) {R : ℝ} (hR : 0 ≤ R) :
    |(2 * (b : ℝ) - 1) * R| ≤ R := by
  interval_cases b <;> norm_num [abs_of_nonneg hR]

lemma boxVertex_mem {r₀ : ℝ} {r : Fin m → ℝ} (hr₀ : 0 ≤ r₀) (hr : ∀ k, 0 ≤ r k)
    {σ : Fin (m + 1) → ℕ} (hσ : ∀ κ, σ κ < 2) : boxVertex r₀ r σ ∈ stdBox r₀ r := by
  refine ⟨?_, fun k => ?_⟩
  · simpa [boxVertex] using abs_sign_mul_le (hσ 0) hr₀
  · simpa [boxVertex] using abs_sign_mul_le (hσ k.succ) (hr k)

/-- The point attached to the subbox of generation `j` with index `μ` of the box `g(stdBox r₀ r)`:
its center minus `2^{−j} t e`. -/
noncomputable def attachedPt (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (r₀ : ℝ) (r : Fin m → ℝ) (e : Pt m) (t : ℝ)
    (j : ℕ) (μ : Fin (m + 1) → ℕ) : Pt m :=
  g (subboxCenter r₀ r j μ) - genScale t j • e

open scoped Classical in
/-- The set `𝒜_j` of the proof of Lemma `lem:tree`: the pairs of points attached to a subbox of
generation `j` and to one of its subboxes of generation `j + 1`. The index of the child of `μ` with
bits `σ` is `2μ + σ`. -/
noncomputable def treePairs (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (r₀ : ℝ) (r : Fin m → ℝ) (e : Pt m) (t : ℝ)
    (j : ℕ) : Finset (Pt m × Pt m) :=
  (Finset.univ : Finset ((Fin (m + 1) → Fin (2 ^ j)) × (Fin (m + 1) → Fin 2))).image fun q =>
    (attachedPt g r₀ r e t j (fun κ => q.1 κ),
      attachedPt g r₀ r e t (j + 1) fun κ => 2 * (q.1 κ : ℕ) + q.2 κ)

open scoped Classical in
lemma treePairs_nonempty (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (r₀ : ℝ) (r : Fin m → ℝ) (e : Pt m) (t : ℝ)
    (j : ℕ) : (treePairs g r₀ r e t j).Nonempty :=
  have : NeZero (2 ^ j) := ⟨by positivity⟩
  Finset.univ_nonempty.image _

open scoped Classical in
/-- The number of pairs: at most `2^{d(j+1)}`. -/
lemma card_treePairs_le (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (r₀ : ℝ) (r : Fin m → ℝ) (e : Pt m) (t : ℝ)
    (j : ℕ) : (treePairs g r₀ r e t j).card ≤ 2 ^ ((m + 1) * (j + 1)) := by
  refine Finset.card_image_le.trans ?_
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith only [])

/-! ## The generations -/

/-- The integer `j₀`: the largest with `2^{−j₀} t ≥ 4`, for `t ≥ 4`. -/
noncomputable def dyadicDepth (t : ℝ) : ℕ := Nat.log 2 ⌊t / 4⌋₊

lemma dyadicDepth_spec {t : ℝ} (ht : 4 ≤ t) :
    (2 : ℝ) ^ dyadicDepth t ≤ t / 4 ∧ t / 4 < (2 : ℝ) ^ (dyadicDepth t + 1) := by
  have h1 : 1 ≤ t / 4 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hn : ⌊t / 4⌋₊ ≠ 0 := (Nat.floor_pos.mpr h1).ne'
  constructor
  · have := Nat.pow_log_le_self 2 hn
    calc (2 : ℝ) ^ dyadicDepth t = ((2 ^ dyadicDepth t : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊t / 4⌋₊ : ℝ) := Nat.cast_le.mpr this
      _ ≤ t / 4 := Nat.floor_le (by linarith)
  · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊t / 4⌋₊
    calc t / 4 < (⌊t / 4⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      _ ≤ ((2 ^ (dyadicDepth t + 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (2 : ℝ) ^ (dyadicDepth t + 1) := by push_cast; rfl

/-- For `j < j₀`, `2^{−j} t ≥ 8`. -/
lemma eight_le_genScale {t : ℝ} (ht : 4 ≤ t) {j : ℕ} (hj : j < dyadicDepth t) :
    8 ≤ genScale t j := by
  have h1 := (dyadicDepth_spec ht).1
  have h2 : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ dyadicDepth t := pow_le_pow_right₀ (by norm_num) hj
  have h3 : (2 : ℝ) * 2 ^ j ≤ t / 4 := by rw [mul_comm, ← pow_succ]; exact h2.trans h1
  unfold genScale
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith only [h3]

/-- `2^{−j₀} t < 8`. -/
lemma genScale_depth_lt {t : ℝ} (ht : 4 ≤ t) : genScale t (dyadicDepth t) < 8 := by
  have h1 := (dyadicDepth_spec ht).2
  rw [pow_succ] at h1
  unfold genScale
  rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
  linarith only [h1]

/-! ## The nested subboxes containing a point -/

/-- The index of the subbox of generation `j` containing `y`, these subboxes being nested. -/
noncomputable def chainIndex (r₀ : ℝ) (r : Fin m → ℝ) (y : Pt m) (j : ℕ) : Fin (m + 1) → ℕ :=
  Fin.cases (dyadicIndex r₀ (Pt.lon y) j) fun k => dyadicIndex (r k) (Pt.tr y k) j

lemma chainIndex_zero (r₀ : ℝ) (r : Fin m → ℝ) (y : Pt m) :
    chainIndex r₀ r y 0 = fun _ => 0 := by
  funext κ
  exact Fin.cases rfl (fun _ => rfl) κ

lemma chainIndex_lt {r₀ : ℝ} {r : Fin m → ℝ} {y : Pt m} (hy : y ∈ stdBox r₀ r) (j : ℕ)
    (κ : Fin (m + 1)) : chainIndex r₀ r y j κ < 2 ^ j :=
  Fin.cases (dyadicIndex_spec hy.1 j).1 (fun k => (dyadicIndex_spec (hy.2 k) j).1) κ

/-- The subbox of generation `j + 1` is a child of the subbox of generation `j`. -/
lemma exists_chainIndex_succ (r₀ : ℝ) (r : Fin m → ℝ) (y : Pt m) (j : ℕ) :
    ∃ σ : Fin (m + 1) → ℕ, (∀ κ, σ κ < 2) ∧
      chainIndex r₀ r y (j + 1) = fun κ => 2 * chainIndex r₀ r y j κ + σ κ := by
  obtain ⟨b₀, hb₀, h₀⟩ := exists_dyadicIndex_succ r₀ (Pt.lon y) j
  choose b hb h using fun k => exists_dyadicIndex_succ (r k) (Pt.tr y k) j
  refine ⟨Fin.cases b₀ b, fun κ => Fin.cases hb₀ hb κ, ?_⟩
  funext κ
  exact Fin.cases h₀ h κ

/-- A point of the box lies in its subboxes: within `2^{−j}` half-sides of their centers. -/
lemma chainIndex_close {r₀ : ℝ} {r : Fin m → ℝ} {y : Pt m} (hy : y ∈ stdBox r₀ r) (j : ℕ) :
    |Pt.lon (y - subboxCenter r₀ r j (chainIndex r₀ r y j))| ≤ ((2 : ℝ) ^ j)⁻¹ * r₀ ∧
      ∀ k, |Pt.tr (y - subboxCenter r₀ r j (chainIndex r₀ r y j)) k| ≤ ((2 : ℝ) ^ j)⁻¹ * r k := by
  refine ⟨?_, fun k => ?_⟩
  · simpa [subboxCenter, chainIndex] using (dyadicIndex_spec hy.1 j).2
  · simpa [subboxCenter, chainIndex] using (dyadicIndex_spec (hy.2 k) j).2

/-! ## Equation `eq:treestep` -/

section Box

variable {g : Pt m ≃ᵃⁱ[ℝ] Pt m} {r₀ : ℝ} {r : Fin m → ℝ} {x e : Pt m} {t w : ℝ}

/-- A point of the standard box has norm at most `t/16`: `g v` and `g(−v)` lie in `B`, whose
diameter is at most `t/8`. -/
lemma norm_le_of_mem_stdBox (hdiam : ∀ z ∈ g '' stdBox r₀ r, ∀ z' ∈ g '' stdBox r₀ r,
      dist z z' ≤ t / 8) {v : Pt m} (hv : v ∈ stdBox r₀ r) : ‖v‖ ≤ t / 16 := by
  have hneg : -v ∈ stdBox r₀ r := ⟨by simpa using hv.1, fun k => by simpa using hv.2 k⟩
  have h := hdiam _ (mem_image_of_mem g hv) _ (mem_image_of_mem g hneg)
  rw [g.dist_map, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ v, norm_smul] at h
  norm_num at h
  linarith only [h]

lemma norm_le_of_close (hdiam : ∀ z ∈ g '' stdBox r₀ r, ∀ z' ∈ g '' stdBox r₀ r,
      dist z z' ≤ t / 8) {d : Pt m} {c : ℝ} (hc : 0 < c) (hd₀ : |Pt.lon d| ≤ c * r₀)
    (hd : ∀ k, |Pt.tr d k| ≤ c * r k) : ‖d‖ ≤ c * (t / 16) := by
  have hη : c⁻¹ • d ∈ stdBox r₀ r := by
    refine ⟨?_, fun k => ?_⟩
    · rw [Pt.lon_smul, abs_mul, abs_inv, abs_of_pos hc, inv_mul_le_iff₀ hc]
      exact hd₀
    · rw [Pt.tr_smul, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hc,
        inv_mul_le_iff₀ hc]
      exact hd k
  have h := norm_le_of_mem_stdBox hdiam hη
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_le_iff₀ hc] at h
  exact h

/-- A point `v` of the box seen from `x`: its component along `e` is at least `15t/16`, its length
at most `17t/16`, and its length exceeds that component by at most `8w²/(15t)`. -/
lemma vertex_bounds (he : ‖e‖ = 1) (hg0 : g 0 = x + t • e)
    (hdiam : ∀ z ∈ g '' stdBox r₀ r, ∀ z' ∈ g '' stdBox r₀ r, dist z z' ≤ t / 8)
    (hline : ∀ z ∈ g '' stdBox r₀ r, ‖perp e (z - x)‖ ≤ w) (ht : 0 < t) {v : Pt m}
    (hv : v ∈ stdBox r₀ r) :
    15 / 16 * t ≤ ⟪g v - x, e⟫ ∧ ‖g v - x‖ ≤ 17 / 16 * t ∧
      ‖g v - x‖ - ⟪g v - x, e⟫ ≤ 8 / 15 * w ^ 2 / t := by
  have hv0 := norm_le_of_mem_stdBox hdiam hv
  set L := g.linearIsometryEquiv v with hL
  have hnorm : ‖L‖ = ‖v‖ := g.linearIsometryEquiv.norm_map v
  have hu : g v - x = L + t • e := by
    have h := g.map_vsub v 0
    simp only [vsub_eq_sub, sub_zero, hg0] at h
    rw [hL, h]
    abel
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hin : ⟪g v - x, e⟫ = ⟪L, e⟫ + t := by
    rw [hu, inner_add_left, real_inner_smul_left, hee, mul_one]
  have hLe : |⟪L, e⟫| ≤ t / 16 := (abs_real_inner_le_norm L e).trans (by
    rw [he, mul_one, hnorm]; exact hv0)
  have hlow : 15 / 16 * t ≤ ⟪g v - x, e⟫ := by
    rw [hin]
    linarith only [neg_abs_le ⟪L, e⟫, hLe]
  have hup : ‖g v - x‖ ≤ 17 / 16 * t := by
    rw [hu]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos ht, hnorm]
    linarith only [hv0]
  refine ⟨hlow, hup, ?_⟩
  have hpos : 0 < ⟪g v - x, e⟫ := lt_of_lt_of_le (by positivity) hlow
  refine (norm_sub_inner_le he hpos).trans ?_
  have hp := hline _ (mem_image_of_mem g hv)
  have hp2 : ‖perp e (g v - x)‖ ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  rw [div_le_div_iff₀ (by positivity) ht]
  have h1 := mul_le_mul_of_nonneg_right hp2 ht.le
  have h2 := mul_le_mul_of_nonneg_left hlow (sq_nonneg w)
  linarith only [h1, h2]

/-- The difference of a pair of `𝒜_j`: `w − y = 2^{−j−1} (v − x)` for the vertex `v` of `B` with
the bits of the child (the paper takes `x = 0`). -/
lemma attachedPt_child (hg0 : g 0 = x + t • e) (j : ℕ) (μ σ : Fin (m + 1) → ℕ) :
    attachedPt g r₀ r e t (j + 1) (fun κ => 2 * μ κ + σ κ) - attachedPt g r₀ r e t j μ =
      ((2 : ℝ) ^ (j + 1))⁻¹ • (g (boxVertex r₀ r σ) - x) := by
  set h : ℝ := ((2 : ℝ) ^ (j + 1))⁻¹ with hh
  set c := subboxCenter r₀ r j μ with hc
  set v := boxVertex r₀ r σ with hv
  have h1 : g (c + h • v) - g c = h • (g v - (x + t • e)) := by
    have e1 := g.map_vsub (c + h • v) c
    have e2 := g.map_vsub v 0
    simp only [vsub_eq_sub, add_sub_cancel_left, sub_zero, hg0, map_smul] at e1 e2
    rw [← e1, e2]
  have hscale : genScale t j = t * h + genScale t (j + 1) := by
    simp only [genScale, hh, inv_two_pow_succ]
    ring
  simp only [attachedPt, subboxCenter_child, ← hc, ← hv, ← hh, hscale, add_smul, smul_sub, mul_smul]
  rw [smul_sub, smul_add] at h1
  have h2 : g (c + h • v) = g c + (h • g v - (h • x + h • t • e)) := by
    rw [← h1]; abel
  rw [h2, smul_comm t h e]
  abel

/-- **Equation `eq:treestep`**, with `w` for `16(d tQ_t)^{1/2}`: for
a pair `(y, w')` of `𝒜_j`, `(15/32) 2^{−j} t ≤ |w' − y| ≤ 2^{−j} t` and
`|w' − y| − (w' − y)·e ≤ 2^{−j} · 4w²/(15t)`. -/
lemma attached_step (he : ‖e‖ = 1) (hg0 : g 0 = x + t • e)
    (hdiam : ∀ z ∈ g '' stdBox r₀ r, ∀ z' ∈ g '' stdBox r₀ r, dist z z' ≤ t / 8)
    (hline : ∀ z ∈ g '' stdBox r₀ r, ‖perp e (z - x)‖ ≤ w) (ht : 0 < t) (hr₀ : 0 ≤ r₀)
    (hr : ∀ k, 0 ≤ r k) (j : ℕ) (μ : Fin (m + 1) → ℕ) {σ : Fin (m + 1) → ℕ}
    (hσ : ∀ κ, σ κ < 2) :
    15 / 32 * genScale t j ≤ dist (attachedPt g r₀ r e t j μ)
        (attachedPt g r₀ r e t (j + 1) fun κ => 2 * μ κ + σ κ) ∧
      dist (attachedPt g r₀ r e t j μ)
          (attachedPt g r₀ r e t (j + 1) fun κ => 2 * μ κ + σ κ) ≤ genScale t j ∧
      dist (attachedPt g r₀ r e t j μ)
          (attachedPt g r₀ r e t (j + 1) fun κ => 2 * μ κ + σ κ) -
        ⟪attachedPt g r₀ r e t (j + 1) (fun κ => 2 * μ κ + σ κ) - attachedPt g r₀ r e t j μ, e⟫ ≤
          ((2 : ℝ) ^ j)⁻¹ * (4 / 15 * w ^ 2 / t) := by
  obtain ⟨h1, h2, h3⟩ := vertex_bounds he hg0 hdiam hline ht (boxVertex_mem hr₀ hr hσ)
  rw [dist_comm, dist_eq_norm, attachedPt_child hg0, norm_smul, real_inner_smul_left]
  set h : ℝ := ((2 : ℝ) ^ (j + 1))⁻¹ with hh
  have hpos : 0 < h := by positivity
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  set u := g (boxVertex r₀ r σ) - x with hu
  have hle := inner_le_norm he u
  have hgen : genScale t j = 2 * h * t := by
    simp only [genScale, hh, inv_two_pow_succ]
    ring
  have hinv : ((2 : ℝ) ^ j)⁻¹ = 2 * h := by
    simp only [hh, inv_two_pow_succ]
    ring
  rw [hgen, hinv]
  have h4 := mul_le_mul_of_nonneg_left (h1.trans hle) hpos.le
  have h5 := mul_le_mul_of_nonneg_left h2 hpos.le
  have h6 := mul_le_mul_of_nonneg_left h3 hpos.le
  have hht : 0 < h * t := by positivity
  refine ⟨?_, ?_, ?_⟩
  · linarith only [h4]
  · linarith only [h5, hht]
  · have e1 : h * (8 / 15 * w ^ 2 / t) = 2 * h * (4 / 15 * w ^ 2 / t) := by ring
    linarith only [h6, e1]

/-- A point of a subbox of generation `j` is within `(17/16) 2^{−j} t` of the attached point. -/
lemma dist_attached_le (he : ‖e‖ = 1)
    (hdiam : ∀ z ∈ g '' stdBox r₀ r, ∀ z' ∈ g '' stdBox r₀ r, dist z z' ≤ t / 8) (ht : 0 < t)
    {j : ℕ} {μ : Fin (m + 1) → ℕ} {y : Pt m}
    (hy₀ : |Pt.lon (y - subboxCenter r₀ r j μ)| ≤ ((2 : ℝ) ^ j)⁻¹ * r₀)
    (hy : ∀ k, |Pt.tr (y - subboxCenter r₀ r j μ) k| ≤ ((2 : ℝ) ^ j)⁻¹ * r k) :
    dist (g y) (attachedPt g r₀ r e t j μ) ≤ 17 / 16 * genScale t j := by
  have h1 := norm_le_of_close hdiam (by positivity) hy₀ hy
  have hs : 0 < genScale t j := genScale_pos ht j
  have h2 : dist (g (subboxCenter r₀ r j μ)) (attachedPt g r₀ r e t j μ) = genScale t j := by
    rw [attachedPt, dist_eq_norm, sub_sub_cancel, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos hs]
  have h3 := dist_triangle (g y) (g (subboxCenter r₀ r j μ)) (attachedPt g r₀ r e t j μ)
  rw [h2, g.dist_map, dist_eq_norm y] at h3
  have h4 : ((2 : ℝ) ^ j)⁻¹ * (t / 16) = genScale t j / 16 := by
    simp only [genScale]
    ring
  rw [h4] at h1
  linarith only [h1, h3]

end Box

end IsotropicVariance.Paper.Proofs.Profiles
