/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Localization.Frame
public import IsotropicVariance.Paper.Proofs.Localization.Scales
public import IsotropicVariance.Paper.Proofs.Profiles.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import IsotropicVariance.Paper.Proofs.Responses.GaussianSum
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry

/-!
# The proof of Lemma `lem:localization`: the deterministic inequalities

In the frame `g` of a cube pair (`g 0`, `g (r e₁)` the centers), with the exterior points
`a = g(−2C₀n e₁)` and `b = g((r + 2C₀n) e₁)` (the first paragraph of the proof of Lemma
`lem:localization`):

* The upper bound: for a 1-optimal curve `π` for `D` from `u` to `v` and a point `z` of `π`,
  `T(a, z) + T(z, b) ≤ T(a, u) + D(u, v) + 1 + T(v, b)`.
* The lower bound: the boxes `[t_j ± n/1000] × W(k + [−1, 1]^{d−1})` with the points
  `x_± = (t_j ± n/16, Wk)`; for `z` in a box,
  `T(a, z) + T(z, b) ≥ |b − a| + W²|k|²/(2|x₊ − a|) + W²|k|²/(2|b − x₋|) − (errors)`, the errors
  being the tree bounds at `x_±` and the parent bounds for `T(a, x₊)`, `T(x₋, b)`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal RealInnerProductSpace

open IsotropicVariance.Paper.Proofs.Profiles (abs_lon_le_norm)
open IsotropicVariance.Paper.Proofs.Responses (transverseIntegerPoint)
namespace IsotropicVariance.Paper.Proofs.Localization

variable {m : ℕ}

/-! ## Coordinates -/

lemma inner_e₁ (x : Pt m) : ⟪x, e₁⟫ = Pt.lon x := by
  simp [WithLp.prod_inner_apply, e₁, Pt.lon]

/-- `|v| ≥ v · e₁ + |v_⊥|²/(2|v|)` when `v · e₁ > 0`: the curvature of Euclidean length. -/
lemma lon_add_le_norm {v : Pt m} (hv : 0 < Pt.lon v) :
    Pt.lon v + ‖Pt.tr v‖ ^ 2 / (2 * ‖v‖) ≤ ‖v‖ := by
  have h := Profiles.norm_sq_eq_lon_tr v
  have hle : Pt.lon v ≤ ‖v‖ := (le_abs_self _).trans (abs_lon_le_norm v)
  have hpos : 0 < ‖v‖ := hv.trans_le hle
  rw [← le_sub_iff_add_le', div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖v‖ - Pt.lon v)]

/-- `|v| − v · e₁ ≤ |v_⊥|²/(2 v · e₁)` when `v · e₁ > 0`. -/
lemma norm_sub_lon_le {v : Pt m} (hv : 0 < Pt.lon v) :
    ‖v‖ - Pt.lon v ≤ ‖Pt.tr v‖ ^ 2 / (2 * Pt.lon v) := by
  have h := Profiles.norm_sq_eq_lon_tr v
  have hle : Pt.lon v ≤ ‖v‖ := (le_abs_self _).trans (abs_lon_le_norm v)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖v‖ - Pt.lon v)]

lemma norm_kvec_sq (k : Fin m → ℤ) : ‖transverseIntegerPoint k‖ ^ 2 = ∑ i, ((k i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [transverseIntegerPoint]

/-! ## The frame -/

variable (g : Pt m ≃ᵃⁱ[ℝ] Pt m)

/-- The direction `e` of the frame, the image of `e₁`. -/
noncomputable def frameDir : Pt m := g.linearIsometryEquiv e₁

lemma norm_frameDir : ‖frameDir g‖ = 1 := by
  rw [frameDir, LinearIsometryEquiv.norm_map, norm_e₁]

lemma frame_add (p v : Pt m) : g (p + v) = g p + g.linearIsometryEquiv v := by
  have := g.map_vadd p v
  rw [vadd_eq_add, vadd_eq_add, add_comm v p, add_comm (g.linearIsometryEquiv v)] at this
  exact this

lemma frame_sub (p q : Pt m) : g q - g p = g.linearIsometryEquiv (q - p) := by
  have := g.map_vsub q p
  rw [vsub_eq_sub, vsub_eq_sub] at this
  exact this.symm

lemma inner_frameDir (p q : Pt m) : ⟪g q - g p, frameDir g⟫ = Pt.lon (q - p) := by
  rw [frame_sub, frameDir, LinearIsometryEquiv.inner_map_map, inner_e₁]

lemma dist_frame (p q : Pt m) : dist (g p) (g q) = ‖p - q‖ := by
  rw [g.dist_map, dist_eq_norm]

/-! ## The boxes of the lower bound -/

/-- The longitudinal centers `t_j = −C₀n + j n/500` of the boxes. -/
noncomputable def boxLon (n C₀ : ℝ) (j : ℕ) : ℝ := -(C₀ * n) + j * (n / 500)

/-- The center `(t_j, Wk)` of the box `(j, k)`, in the frame. -/
noncomputable def boxCtr (n W C₀ : ℝ) (j : ℕ) (k : Fin m → ℤ) : Pt m :=
  Pt.mk (boxLon n C₀ j) (W • transverseIntegerPoint k)

/-- The box `[t_j ± n/1000] × W(k + [−1, 1]^{d−1})`, in the frame. -/
def boxSet (n W C₀ : ℝ) (j : ℕ) (k : Fin m → ℤ) : Set (Pt m) :=
  {ζ | |Pt.lon ζ - boxLon n C₀ j| ≤ n / 1000 ∧ ∀ i, |Pt.tr ζ i - W * k i| ≤ W}

/-- The exterior point `a = g(−2C₀n e₁)`. -/
noncomputable def anchorA (n C₀ : ℝ) : Pt m := g ((-(2 * C₀ * n)) • e₁)

/-- The exterior point `b = g((r + 2C₀n) e₁)`. -/
noncomputable def anchorB (n r C₀ : ℝ) : Pt m := g ((r + 2 * C₀ * n) • e₁)

/-- `x₊ = (t_j + n/16, Wk)`. -/
noncomputable def plusPt (n W C₀ : ℝ) (j : ℕ) (k : Fin m → ℤ) : Pt m :=
  g (boxCtr n W C₀ j k + (n / 16) • e₁)

/-- `x₋ = (t_j − n/16, Wk)`. -/
noncomputable def minusPt (n W C₀ : ℝ) (j : ℕ) (k : Fin m → ℤ) : Pt m :=
  g (boxCtr n W C₀ j k - (n / 16) • e₁)

variable {g}

lemma mem_boxSet_dist_le {n W C₀ : ℝ} (hW : 0 ≤ W) {j : ℕ} {k : Fin m → ℤ} {ζ ζ' : Pt m}
    (hζ : ζ ∈ boxSet n W C₀ j k) (hζ' : ζ' ∈ boxSet n W C₀ j k) :
    dist (g ζ) (g ζ') ≤ n / 500 + 2 * Real.sqrt m * W := by
  rw [dist_frame]
  refine (Pt.lon_tr_norm_le _).trans ?_
  have h1 : |Pt.lon (ζ - ζ')| ≤ n / 500 := by
    rw [Pt.lon_sub]
    have := abs_sub_le (Pt.lon ζ) (boxLon n C₀ j) (Pt.lon ζ')
    rw [abs_sub_comm (boxLon n C₀ j)] at this
    linarith [hζ.1, hζ'.1]
  have h2 : ‖Pt.tr (ζ - ζ')‖ ≤ Real.sqrt m * (2 * W) := by
    refine Profiles.norm_le_of_abs_le (by positivity) fun i => ?_
    rw [Pt.tr_sub]
    have := abs_sub_le (Pt.tr ζ i) (W * k i) (Pt.tr ζ' i)
    rw [abs_sub_comm (W * k i)] at this
    simp only [PiLp.sub_apply]
    linarith [hζ.2 i, hζ'.2 i]
  linarith

lemma norm_tr_sub_kvec_le {n W C₀ : ℝ} (hW : 0 ≤ W) {j : ℕ} {k : Fin m → ℤ} {ζ : Pt m}
    (hζ : ζ ∈ boxSet n W C₀ j k) : ‖Pt.tr ζ - W • transverseIntegerPoint k‖ ≤ Real.sqrt m * W :=
  Profiles.norm_le_of_abs_le hW fun i => by
    have := hζ.2 i
    simpa [transverseIntegerPoint] using this

/-- The transverse coordinate of a point of the box `(j, k)`: `|y|² ≤ 2W²|k|² + 2mW²`. -/
lemma norm_tr_sq_le {n W C₀ : ℝ} (hW : 0 ≤ W) {j : ℕ} {k : Fin m → ℤ} {ζ : Pt m}
    (hζ : ζ ∈ boxSet n W C₀ j k) :
    ‖Pt.tr ζ‖ ^ 2 ≤ 2 * W ^ 2 * ‖transverseIntegerPoint k‖ ^ 2 + 2 * m * W ^ 2 := by
  have h := norm_tr_sub_kvec_le hW hζ
  have h2 : ‖Pt.tr ζ‖ ≤ ‖Pt.tr ζ - W • transverseIntegerPoint k‖ +
      W * ‖transverseIntegerPoint k‖ := by
    have := norm_add_le (Pt.tr ζ - W • transverseIntegerPoint k) (W • transverseIntegerPoint k)
    rw [sub_add_cancel, norm_smul, Real.norm_of_nonneg hW] at this
    exact this
  have hm : Real.sqrt m ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  nlinarith [norm_nonneg (Pt.tr ζ - W • transverseIntegerPoint k),
    norm_nonneg (transverseIntegerPoint k), norm_nonneg (Pt.tr ζ),
    sq_nonneg (‖Pt.tr ζ - W • transverseIntegerPoint k‖ - W * ‖transverseIntegerPoint k‖),
    Real.sqrt_nonneg m]

/-! ## The lower bound -/

/-- **The lower bound for one box**: for `z = g ζ` in the box `(j, k)`,
`T(a, z) + T(z, b)` exceeds `|b − a| = r + 4C₀n` by the curvature gain of the detours through
`x₊` and `x₋`, up to the tree errors `Z_±` at `x_±` and the parent errors `P_±`. -/
theorem step2_box (T : Pt m → Pt m → ℝ) (htri : ∀ x y z, T x z ≤ T x y + T y z)
    (hsym : ∀ x y, T x y = T y x) {n r W C₀ Cp Qp Qm Zp Zm Pp Pm : ℝ} {j : ℕ}
    {k : Fin m → ℤ} (hlp : 0 < boxLon n C₀ j + n / 16 + 2 * C₀ * n)
    (hlm : 0 < r + 2 * C₀ * n - boxLon n C₀ j + n / 16)
    (hZp : ∀ ζ ∈ boxSet n W C₀ j k, T (plusPt g n W C₀ j k) (g ζ) -
      ⟪g ζ - plusPt g n W C₀ j k, -frameDir g⟫ ≤ Zp)
    (hZm : ∀ ζ ∈ boxSet n W C₀ j k, T (minusPt g n W C₀ j k) (g ζ) -
      ⟪g ζ - minusPt g n W C₀ j k, frameDir g⟫ ≤ Zm)
    (hPp : |T (anchorA g n C₀) (plusPt g n W C₀ j k) -
      dist (anchorA g n C₀) (plusPt g n W C₀ j k)| - Cp * Qp ≤ Pp)
    (hPm : |T (minusPt g n W C₀ j k) (anchorB g n r C₀) -
      dist (minusPt g n W C₀ j k) (anchorB g n r C₀)| - Cp * Qm ≤ Pm)
    {ζ : Pt m} (hζ : ζ ∈ boxSet n W C₀ j k) :
    r + 4 * C₀ * n +
        W ^ 2 * ‖transverseIntegerPoint k‖ ^ 2 / (2 * dist (anchorA g n C₀) (plusPt g n W C₀ j k)) +
        W ^ 2 * ‖transverseIntegerPoint k‖ ^ 2 /
          (2 * dist (minusPt g n W C₀ j k) (anchorB g n r C₀)) -
        Cp * (Qp + Qm) - (Pp + Pm + Zp + Zm) ≤
      T (anchorA g n C₀) (g ζ) + T (g ζ) (anchorB g n r C₀) := by
  set c := boxCtr n W C₀ j k
  set P := c + (n / 16) • (e₁ : Pt m)
  set M := c - (n / 16) • (e₁ : Pt m)
  set a := (-(2 * C₀ * n)) • (e₁ : Pt m)
  set b := (r + 2 * C₀ * n) • (e₁ : Pt m)
  have hlonc : Pt.lon c = boxLon n C₀ j := rfl
  have htrc : Pt.tr c = W • transverseIntegerPoint k := rfl
  -- the tree bounds in coordinates
  have hTp : T (g P) (g ζ) ≤ boxLon n C₀ j + n / 16 - Pt.lon ζ + Zp := by
    have h := hZp ζ hζ
    have hin : ⟪g ζ - g P, -frameDir g⟫ = -(Pt.lon ζ - (boxLon n C₀ j + n / 16)) := by
      rw [inner_neg_right, inner_frameDir]
      simp [P, hlonc]
    change T (g P) (g ζ) - ⟪g ζ - g P, -frameDir g⟫ ≤ Zp at h
    rw [hin] at h
    linarith
  have hTm : T (g M) (g ζ) ≤ Pt.lon ζ - boxLon n C₀ j + n / 16 + Zm := by
    have h := hZm ζ hζ
    have hin : ⟪g ζ - g M, frameDir g⟫ = Pt.lon ζ - (boxLon n C₀ j - n / 16) := by
      rw [inner_frameDir]
      simp [M, hlonc]
    change T (g M) (g ζ) - ⟪g ζ - g M, frameDir g⟫ ≤ Zm at h
    rw [hin] at h
    linarith
  -- the curvature of the detours
  have hvp : Pt.lon (P - a) = boxLon n C₀ j + n / 16 + 2 * C₀ * n := by
    simp [P, a, hlonc]
  have hvm : Pt.lon (b - M) = r + 2 * C₀ * n - boxLon n C₀ j + n / 16 := by
    simp [M, b, hlonc]; ring
  have htrp : ‖Pt.tr (P - a)‖ ^ 2 = W ^ 2 * ‖transverseIntegerPoint k‖ ^ 2 := by
    simp [P, a, htrc, norm_smul, mul_pow]
  have htrm : ‖Pt.tr (b - M)‖ ^ 2 = W ^ 2 * ‖transverseIntegerPoint k‖ ^ 2 := by
    simp [M, b, htrc, norm_smul, mul_pow]
  have hdp : dist (g a) (g P) = ‖P - a‖ := by rw [dist_frame, norm_sub_rev]
  have hdm : dist (g M) (g b) = ‖b - M‖ := by rw [dist_frame, norm_sub_rev]
  have hcp := lon_add_le_norm (v := P - a) (by rw [hvp]; exact hlp)
  have hcm := lon_add_le_norm (v := b - M) (by rw [hvm]; exact hlm)
  rw [hvp, htrp] at hcp
  rw [hvm, htrm] at hcm
  change r + 4 * C₀ * n + W ^ 2 * ‖transverseIntegerPoint k‖ ^ 2 / (2 * dist (g a) (g P)) +
      W ^ 2 * ‖transverseIntegerPoint k‖ ^ 2 / (2 * dist (g M) (g b)) - Cp * (Qp + Qm) -
        (Pp + Pm + Zp + Zm) ≤
    T (g a) (g ζ) + T (g ζ) (g b)
  change |T (g a) (g P) - dist (g a) (g P)| - Cp * Qp ≤ Pp at hPp
  change |T (g M) (g b) - dist (g M) (g b)| - Cp * Qm ≤ Pm at hPm
  rw [hdp] at hPp ⊢
  rw [hdm] at hPm ⊢
  have h1 := htri (g a) (g ζ) (g P)
  have h2 := htri (g M) (g ζ) (g b)
  rw [hsym (g ζ) (g P)] at h1
  have h3 := neg_abs_le (T (g a) (g P) - ‖P - a‖)
  have h4 := neg_abs_le (T (g M) (g b) - ‖b - M‖)
  linarith

/-! ## The upper bound -/

/-- **The upper bound at one point**: for a 1-optimal curve `π` for the density
`σ ≥ ρ` from `u` to `v` and a point `z` of `π`,
`T(a, z) + T(z, b) ≤ T(a, u) + D(u, v) + 1 + T(v, b)`. -/
theorem step1_point (X : Setting m) {B : ℝ} (hB : ∀ ω x, X.ρ ω x ≤ B) (ω : X.Ω)
    {σ : Pt m → ℝ} (hρσ : ∀ x, X.ρ ω x ≤ σ x) {S : Set (Pt m)} {u v : Pt m}
    {γ : RectifiableCurve (Pt m)} (hγ : IsOneOptimal σ S u v γ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (a b : Pt m) :
    X.passTime ω a (γ.toFun t) + X.passTime ω (γ.toFun t) b ≤
      X.passTime ω a u + (restrictedPassageTime σ S u v + 1) + X.passTime ω v b := by
  obtain ⟨h0, h1, -, hc⟩ := hγ
  have hBω : ∀ x, X.ρ ω x ≤ B := hB ω
  have hρm : Measurable fun x => ENNReal.ofReal (X.ρ ω x) :=
    ENNReal.measurable_ofReal.comp (Profiles.measurable_ρ_apply X ω)
  set ρ := fun x => ENNReal.ofReal (X.ρ ω x)
  set γ₁ := γ.subcurve 0 t le_rfl ht.1 ht.2
  set γ₂ := γ.subcurve t 1 ht.1 ht.2 le_rfl
  have hc₁ : X.passTime ω u (γ.toFun t) ≤ (γ₁.cost ρ).toReal := by
    have := passageTime_le_cost hBω γ₁
    rwa [RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end, h0] at this
  have hc₂ : X.passTime ω (γ.toFun t) v ≤ (γ₂.cost ρ).toReal := by
    have := passageTime_le_cost hBω γ₂
    rwa [RectifiableCurve.subcurve_start, RectifiableCurve.subcurve_end, h1] at this
  have hsum : γ₁.cost ρ + γ₂.cost ρ = γ.cost ρ := by
    rw [γ.cost_subcurve_add hρm le_rfl ht.1 ht.2 le_rfl, cost_subcurve_zero_one]
  have hle : γ.cost ρ ≤ ENNReal.ofReal (restrictedPassageTime σ S u v + 1) :=
    (γ.cost_mono fun x => ENNReal.ofReal_le_ofReal (hρσ x)).trans hc
  have hfin₁ : γ₁.cost ρ ≠ ⊤ := cost_ne_top hBω _
  have hfin₂ : γ₂.cost ρ ≠ ⊤ := cost_ne_top hBω _
  have hreal : (γ₁.cost ρ).toReal + (γ₂.cost ρ).toReal ≤ restrictedPassageTime σ S u v + 1 := by
    rw [← ENNReal.toReal_add hfin₁ hfin₂, hsum]
    exact ENNReal.toReal_le_of_le_ofReal
      (by linarith [restrictedPassageTime_nonneg σ S u v]) hle
  have t1 := Profiles.passTime_triangle hB ω a u (γ.toFun t)
  have t2 := Profiles.passTime_triangle hB ω (γ.toFun t) v b
  linarith

end IsotropicVariance.Paper.Proofs.Localization
