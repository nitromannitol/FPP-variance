/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Restricted
public import IsotropicVariance.Infra.Selection.Subtype
public import Mathlib.Order.PiLex
import Mathlib.Tactic.Linarith

/-!
# The slab minimum `F`, its lexicographically least minimizer, the indices `J_i`

`F = min Σ_{i=1}^M D_i(x_{i−1}, x_i)` over the points with `x_i · e₁ = is`, `x₀ = 0`,
`x_M = ℓe₁`, `|x_i − x_{i−1} − se₁| ≤ s/4`, where `D_i` is the slab passage time of
`[(i−1)s, is] × ℝ^m` (equation `eq:F`), and its version for the slabs and endpoints translated
by `τ` (Lemma `lem:slab`, and the minima `F_m` of Section `sec:gain`).
Indices are 0-based in Lean: the slab `i : Fin M` is `[τ₁ + is, τ₁ + (i+1)s] × ℝ^m`.

The lexicographically least minimizing points and the indices
`J_i = (⌊x_i · e₂/W_s⌋, …, ⌊x_i · e_d/W_s⌋)` (the proof of Lemma `lem:rowenergy`). The order
compares the points `x₀, …, x_M` in turn, each by its coordinates `(x · e₁, x · e₂, …)`; the paper
fixes no particular lexicographic order.

The minimizing points exist and are unique for a nonnegative width and a measurable density
bounded above (`IsValidChain`; every density of the paper qualifies, `Setting.isValidChain`): the
admissible lists form a nonempty compact set, on which `Σ_i D_i` is Lipschitz
(`IsotropicVariance.Paper.Defs.Restricted`), and the lexicographically least list among the
minimizing ones is the compact selection `Infra.Selection.exists_measurable_lexMinimizer`.
`lexMinimizer` is chosen from that theorem (`exists_isLexLeastMinimizer`) and characterized by
`isLexLeastMinimizer_lexMinimizer`; outside the valid chains it is the straight chain, a value no
statement uses.
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace IsotropicVariance.Paper

/-- The admissible points of equation `eq:F`, for `M` slabs of width `s`, translated by `τ`. -/
def IsAdmissible {m : ℕ} (M : ℕ) (s : ℝ) (τ : Pt m) (x : Fin (M + 1) → Pt m) : Prop :=
  x 0 = τ ∧ x (Fin.last M) = τ + ((M : ℝ) * s) • e₁ ∧
    (∀ i : Fin (M + 1), Pt.lon (x i - τ) = (i : ℝ) * s) ∧
    ∀ i : Fin M, ‖x i.succ - x i.castSucc - s • e₁‖ ≤ s / 4

/-- The slab `i` (0-based) of the chain translated by `τ`: `[τ₁ + is, τ₁ + (i+1)s] × ℝ^m`. -/
noncomputable def chainSlab {m : ℕ} (s : ℝ) (τ : Pt m) (i : ℕ) : Slab m :=
  e1Slab (Pt.lon τ + (i : ℝ) * s) s

/-- `Σ_i D_i(x_{i−1}, x_i)` for the density `σ` and the slab upper bound `b`. -/
noncomputable def slabSum {m : ℕ} (b : ℝ) (σ : Pt m → ℝ) (M : ℕ) (s : ℝ) (τ : Pt m)
    (x : Fin (M + 1) → Pt m) : ℝ :=
  ∑ i : Fin M, (chainSlab s τ i).passTime b σ (x i.castSucc) (x i.succ)

/-- The slab minimum `F` of equation `eq:F`, translated by `τ`. -/
noncomputable def slabMinimum {m : ℕ} (b : ℝ) (σ : Pt m → ℝ) (M : ℕ) (s : ℝ) (τ : Pt m) : ℝ :=
  ⨅ x : {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x}, slabSum b σ M s τ x

/-- The coordinates of a list of points, point by point and within a point in the order
`(x · e₁, x · e₂, …)`: `finProdFinEquiv (i, k) = k + (m + 1) i` orders the pairs `(i, k)`
lexicographically. -/
noncomputable def flatCoords {m M : ℕ} (x : Fin (M + 1) → Pt m) :
    Fin ((M + 1) * (m + 1)) → ℝ :=
  fun p => Pt.coords (x (finProdFinEquiv.symm p).1) (finProdFinEquiv.symm p).2

/-- The lexicographic key of a list of points: the first points are compared first, each by its
coordinates in order. -/
noncomputable def lexKey {m M : ℕ} (x : Fin (M + 1) → Pt m) :
    Lex (Fin ((M + 1) * (m + 1)) → ℝ) :=
  toLex (flatCoords x)

/-- `x` is the lexicographically least list of points attaining the minimum of equation `eq:F`. -/
def IsLexLeastMinimizer {m : ℕ} (b : ℝ) (σ : Pt m → ℝ) (M : ℕ) (s : ℝ) (τ : Pt m)
    (x : Fin (M + 1) → Pt m) : Prop :=
  IsAdmissible M s τ x ∧ slabSum b σ M s τ x = slabMinimum b σ M s τ ∧
    ∀ x', IsAdmissible M s τ x' → slabSum b σ M s τ x' = slabMinimum b σ M s τ →
      lexKey x ≤ lexKey x'

/-- The chains and densities for which the minimizing points exist: a nonnegative width and a
measurable density bounded above (Assumption `ass:local`). -/
structure IsValidChain {m : ℕ} (σ : Pt m → ℝ) (s : ℝ) : Prop where
  /-- The width is nonnegative. -/
  nonneg : 0 ≤ s
  /-- The density is measurable. -/
  measurable : Measurable σ
  /-- The density is bounded above. -/
  bddAbove : BddAbove (range σ)

/-! ## Existence and uniqueness of the minimizing points -/

section Existence

variable {m : ℕ}

lemma Pt.coords_injective : Function.Injective (Pt.coords : Pt m → Fin (m + 1) → ℝ) := by
  intro x y h
  have hlon : Pt.lon x = Pt.lon y := by simpa [Pt.coords] using congr_fun h 0
  have htr : Pt.tr x = Pt.tr y := by
    ext k
    simpa [Pt.coords] using congr_fun h k.succ
  apply (WithLp.ofLp_injective 2)
  exact Prod.ext hlon htr

lemma flatCoords_injective {M : ℕ} :
    Function.Injective (flatCoords : (Fin (M + 1) → Pt m) → Fin ((M + 1) * (m + 1)) → ℝ) := by
  intro x y h
  funext i
  apply Pt.coords_injective
  funext k
  simpa [flatCoords] using congr_fun h (finProdFinEquiv (i, k))

lemma continuous_flatCoords {M : ℕ} :
    Continuous (flatCoords : (Fin (M + 1) → Pt m) → Fin ((M + 1) * (m + 1)) → ℝ) := by
  refine continuous_pi fun p => ?_
  unfold flatCoords Pt.coords
  rcases (finProdFinEquiv.symm p).2.eq_zero_or_eq_succ with h | ⟨k, hk⟩
  · simp only [h, Fin.cons_zero]
    exact Pt.continuous_lon.comp (continuous_apply _)
  · simp only [hk, Fin.cons_succ, Pt.tr]
    fun_prop

/-- The first-differing-coordinate characterization gives the lexicographic order. -/
lemma toLex_le_of_forall {k : ℕ} {x y : Fin k → ℝ}
    (h : ∀ i : Fin k, (∀ j : Fin k, j < i → y j = x j) → x i ≤ y i) : toLex x ≤ toLex y := by
  classical
  by_cases hxy : x = y
  · rw [hxy]
  · refine le_of_lt ?_
    have hne : (Finset.univ.filter fun i => x i ≠ y i).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
      exact ⟨i, by simpa using hi⟩
    set i := (Finset.univ.filter fun i => x i ≠ y i).min' hne
    have hi : x i ≠ y i := by
      simpa using (Finset.univ.filter fun i => x i ≠ y i).min'_mem hne
    have hbefore : ∀ j : Fin k, j < i → x j = y j := by
      intro j hj
      by_contra hne'
      exact absurd ((Finset.univ.filter fun i => x i ≠ y i).min'_le j (by simpa using hne'))
        (not_le.2 hj)
    exact ⟨i, fun j hj => hbefore j hj,
      lt_of_le_of_ne (h i fun j hj => (hbefore j hj).symm) hi⟩

lemma isClosed_admissible (M : ℕ) (s : ℝ) (τ : Pt m) :
    IsClosed {x : Fin (M + 1) → Pt m | IsAdmissible M s τ x} := by
  simp only [IsAdmissible, ofPred_and, ofPred_forall]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    ((isClosed_eq (continuous_apply _) continuous_const).inter
    ((isClosed_iInter fun i => isClosed_eq
      (Pt.continuous_lon.comp ((continuous_apply i).sub continuous_const)) continuous_const).inter
      (isClosed_iInter fun i : Fin M => isClosed_le
        (((continuous_apply i.succ).sub (continuous_apply i.castSucc)).sub
          (continuous_const (y := s • (e₁ : Pt m)))).norm continuous_const)))

lemma norm_sub_le_of_admissible {M : ℕ} {s : ℝ} (hs : 0 ≤ s) {τ : Pt m}
    {x : Fin (M + 1) → Pt m} (hx : IsAdmissible M s τ x) (i : Fin (M + 1)) :
    ‖x i - τ‖ ≤ (i : ℝ) * (2 * s) := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => simp [show (⟨0, hi⟩ : Fin (M + 1)) = 0 from rfl, hx.1]
  | succ n ih =>
    have hn : n < M := by omega
    have h := hx.2.2.2 ⟨n, hn⟩
    have e1 : (⟨n, hn⟩ : Fin M).succ = ⟨n + 1, hi⟩ := rfl
    have e2 : (⟨n, hn⟩ : Fin M).castSucc = ⟨n, by omega⟩ := rfl
    rw [e1, e2] at h
    have ih' := ih (by omega)
    have hsplit : x ⟨n + 1, hi⟩ - τ =
        (x ⟨n + 1, hi⟩ - x ⟨n, by omega⟩ - s • e₁) + s • e₁ + (x ⟨n, by omega⟩ - τ) := by abel
    rw [hsplit]
    refine (norm_add₃_le).trans ?_
    rw [norm_smul, norm_e₁, Real.norm_of_nonneg hs]
    push_cast
    linarith

lemma isCompact_admissible (M : ℕ) {s : ℝ} (hs : 0 ≤ s) (τ : Pt m) :
    IsCompact {x : Fin (M + 1) → Pt m | IsAdmissible M s τ x} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_admissible M s τ) ?_
  refine (Metric.isBounded_closedBall (x := fun _ => τ) (r := M * (2 * s))).subset ?_
  intro x hx
  rw [mem_closedBall, dist_pi_le_iff (by positivity)]
  intro i
  rw [dist_eq_norm]
  refine (norm_sub_le_of_admissible hs hx i).trans ?_
  have : (i : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.1 i.2
  nlinarith

lemma isAdmissible_straight (M : ℕ) (s : ℝ) (hs : 0 ≤ s) (τ : Pt m) :
    IsAdmissible M s τ fun i => τ + ((i : ℝ) * s) • e₁ := by
  refine ⟨by simp, by simp, fun i => by simp, fun i => ?_⟩
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  rw [show τ + (((i : ℝ) + 1) * s) • e₁ - (τ + ((i : ℝ) * s) • e₁) - s • e₁ = 0 by
    rw [add_mul, one_mul, add_smul]; abel]
  simp only [norm_zero]
  positivity

lemma mem_chainSlab_set {s : ℝ} {τ : Pt m} {i : ℕ} {x : Pt m} :
    x ∈ (chainSlab s τ i).set ↔
      Pt.lon τ + i * s ≤ Pt.lon x ∧ Pt.lon x ≤ Pt.lon τ + i * s + s := by
  simp [chainSlab, e1Slab_set]

lemma admissible_mem_chainSlab {M : ℕ} {s : ℝ} (hs : 0 ≤ s) {τ : Pt m}
    {x : Fin (M + 1) → Pt m} (hx : IsAdmissible M s τ x) (i : Fin M) :
    x i.castSucc ∈ (chainSlab s τ i).set ∧ x i.succ ∈ (chainSlab s τ i).set := by
  have h1 := hx.2.2.1 i.castSucc
  have h2 := hx.2.2.1 i.succ
  simp only [Pt.lon_sub, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h1 h2
  simp only [mem_chainSlab_set]
  constructor <;> constructor <;> nlinarith

lemma slabSum_nonneg (b : ℝ) (σ : Pt m → ℝ) (M : ℕ) (s : ℝ) (τ : Pt m)
    (x : Fin (M + 1) → Pt m) : 0 ≤ slabSum b σ M s τ x :=
  Finset.sum_nonneg fun _ _ => restrictedPassageTime_nonneg _ _ _ _

/-- `Σ_i D_i(x_{i−1}, x_i)` is Lipschitz on the admissible lists. -/
lemma lipschitzOnWith_slabSum (b : ℝ) {σ : Pt m → ℝ} {s : ℝ} (h : IsValidChain σ s) (M : ℕ)
    (τ : Pt m) : ∃ K : ℝ≥0, LipschitzOnWith K (slabSum b σ M s τ)
      {x : Fin (M + 1) → Pt m | IsAdmissible M s τ x} := by
  obtain ⟨B₀, hB₀⟩ := h.bddAbove
  set B := max (max b B₀) 0
  have hB : ∀ i : ℕ, ∀ x, (chainSlab s τ i).density b σ x ≤ B := fun i x =>
    ((chainSlab s τ i).density_le b (fun y => hB₀ (mem_range_self y)) x).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  refine ⟨Real.toNNReal (2 * M * B), LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, slabSum, slabSum,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i : Fin M,
      |(chainSlab s τ i).passTime b σ (x i.castSucc) (x i.succ) -
        (chainSlab s τ i).passTime b σ (y i.castSucc) (y i.succ)| ≤ B * (2 * dist x y) := by
    intro i
    obtain ⟨hx1, hx2⟩ := admissible_mem_chainSlab h.nonneg hx i
    obtain ⟨hy1, hy2⟩ := admissible_mem_chainSlab h.nonneg hy i
    refine (abs_restrictedPassageTime_sub_le ((chainSlab s τ i).measurable_density b h.measurable)
      (hB i) hB0 (convex_e1Slab_set _ _) hx1 hy1 hx2 hy2).trans ?_
    have := dist_le_pi_dist x y i.castSucc
    have := dist_le_pi_dist x y i.succ
    nlinarith
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-- **The minimizing points exist.** -/
theorem exists_isLexLeastMinimizer (b : ℝ) {σ : Pt m → ℝ} {s : ℝ} (h : IsValidChain σ s)
    (M : ℕ) (τ : Pt m) : ∃ x, IsLexLeastMinimizer b σ M s τ x := by
  have hA : IsCompact {x : Fin (M + 1) → Pt m | IsAdmissible M s τ x} :=
    isCompact_admissible M h.nonneg τ
  have hAne : {x : Fin (M + 1) → Pt m | IsAdmissible M s τ x}.Nonempty :=
    ⟨fun i => τ + ((i : ℝ) * s) • e₁, isAdmissible_straight M s h.nonneg τ⟩
  obtain ⟨K, hK⟩ := lipschitzOnWith_slabSum b h M τ
  have hcont := hK.continuousOn
  obtain ⟨x₀, hx₀, hmin⟩ := hA.exists_isMinOn hAne hcont
  have hbdd : BddBelow (range fun x : {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x} =>
      slabSum b σ M s τ x) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact slabSum_nonneg _ _ _ _ _ _
  have hval : slabMinimum b σ M s τ = slabSum b σ M s τ x₀ := by
    refine le_antisymm (ciInf_le hbdd ⟨x₀, hx₀⟩) ?_
    have : Nonempty {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x} := ⟨⟨x₀, hx₀⟩⟩
    exact le_ciInf fun x => hmin x.2
  have hMn : IsCompact ({x : Fin (M + 1) → Pt m | IsAdmissible M s τ x} ∩
      slabSum b σ M s τ ⁻¹' {slabSum b σ M s τ x₀}) :=
    hA.of_isClosed_subset (hcont.preimage_isClosed_of_isClosed (isClosed_admissible M s τ)
      isClosed_singleton) inter_subset_left
  obtain ⟨sel, -, hsel⟩ := Infra.Selection.exists_measurable_lexMinimizer (Ω := Unit)
    _ (hMn.image continuous_flatCoords) ⟨_, x₀, ⟨hx₀, rfl⟩, rfl⟩ (fun _ _ => 0)
    (fun _ => continuous_const) (fun _ => measurable_const)
  obtain ⟨x, ⟨hxA, hxv⟩, hxs⟩ := (sel ()).2
  refine ⟨x, hxA, ?_, fun x' hx'A hx'v => ?_⟩
  · rw [hval]
    exact hxv
  · have hx'K : flatCoords x' ∈ flatCoords '' ({x : Fin (M + 1) → Pt m | IsAdmissible M s τ x} ∩
        slabSum b σ M s τ ⁻¹' {slabSum b σ M s τ x₀}) :=
      ⟨x', ⟨hx'A, by rw [mem_preimage, mem_singleton_iff, hx'v, hval]⟩, rfl⟩
    have := (hsel ()).2 ⟨_, hx'K⟩ rfl
    unfold lexKey
    rw [hxs]
    exact toLex_le_of_forall this

/-- **The minimizing points are unique.** -/
theorem IsLexLeastMinimizer.unique {b : ℝ} {σ : Pt m → ℝ} {M : ℕ} {s : ℝ} {τ : Pt m}
    {x y : Fin (M + 1) → Pt m} (hx : IsLexLeastMinimizer b σ M s τ x)
    (hy : IsLexLeastMinimizer b σ M s τ y) : x = y := by
  have h := le_antisymm (hx.2.2 y hy.1 hy.2.1) (hy.2.2 x hx.1 hx.2.1)
  exact flatCoords_injective (toLex.injective h)

end Existence

/-- The lexicographically least minimizing points (the proof of Lemma `lem:rowenergy`), chosen from
`exists_isLexLeastMinimizer` for the valid chains (characterized by
`isLexLeastMinimizer_lexMinimizer`); the straight chain otherwise. -/
@[no_expose] noncomputable def lexMinimizer {m : ℕ} (b : ℝ) (σ : Pt m → ℝ) (M : ℕ) (s : ℝ) (τ : Pt m) :
    Fin (M + 1) → Pt m :=
  haveI := Classical.propDecidable (IsValidChain σ s)
  if h : IsValidChain σ s then (exists_isLexLeastMinimizer b h M τ).choose
  else fun i => τ + ((i : ℝ) * s) • e₁

/-- **Characterization of the minimizing points.** -/
theorem isLexLeastMinimizer_lexMinimizer {m : ℕ} (b : ℝ) {σ : Pt m → ℝ} {s : ℝ}
    (h : IsValidChain σ s) (M : ℕ) (τ : Pt m) :
    IsLexLeastMinimizer b σ M s τ (lexMinimizer b σ M s τ) := by
  simp only [lexMinimizer, h, ↓reduceDIte]
  exact (exists_isLexLeastMinimizer b h M τ).choose_spec

theorem lexMinimizer_eq_iff {m : ℕ} (b : ℝ) {σ : Pt m → ℝ} {s : ℝ} (h : IsValidChain σ s)
    (M : ℕ) (τ : Pt m) {x : Fin (M + 1) → Pt m} :
    lexMinimizer b σ M s τ = x ↔ IsLexLeastMinimizer b σ M s τ x :=
  ⟨fun hx => hx ▸ isLexLeastMinimizer_lexMinimizer b h M τ,
    fun hx => (isLexLeastMinimizer_lexMinimizer b h M τ).unique hx⟩

/-- The indices `J_i = (⌊(x_i − τ) · e₂/W⌋, …)` of the minimizing points (the proof of Lemma
`lem:rowenergy`), so that `x_i ∈ I_i(J_i)` (translated by `τ`) for `W > 0`
(`lexMinimizer_mem_gridCube`); zero for `W ≤ 0`, a value no statement uses. -/
noncomputable def minimizerIndex {m : ℕ} (b : ℝ) (σ : Pt m → ℝ) (M : ℕ) (s W : ℝ) (τ : Pt m)
    (i : Fin (M + 1)) : Fin m → ℤ :=
  fun k => if 0 < W then ⌊Pt.tr (lexMinimizer b σ M s τ i - τ) k / W⌋ else 0

/-- The minimizing point `x_i` lies in the cube `I_i(J_i)`. -/
theorem lexMinimizer_mem_gridCube {m : ℕ} (b : ℝ) {σ : Pt m → ℝ} {s : ℝ}
    (h : IsValidChain σ s) (M : ℕ) {W : ℝ} (hW : 0 < W) (τ : Pt m) (i : Fin (M + 1)) :
    lexMinimizer b σ M s τ i ∈ gridCube s W τ i (minimizerIndex b σ M s W τ i) := by
  refine ⟨(isLexLeastMinimizer_lexMinimizer b h M τ).1.2.2.1 i, fun k => ?_⟩
  simp only [minimizerIndex, hW, ↓reduceIte]
  set y := Pt.tr (lexMinimizer b σ M s τ i - τ) k
  constructor
  · rw [← le_div_iff₀' hW]
    exact Int.floor_le _
  · rw [← div_le_iff₀' hW]
    exact (Int.lt_floor_add_one _).le

/-- The Euclidean norm `|k|` of an integer vector. -/
noncomputable def zNorm {m : ℕ} (k : Fin m → ℤ) : ℝ :=
  Real.sqrt (∑ i, ((k i : ℝ)) ^ 2)

namespace Setting

variable {m : ℕ} (X : Setting m)

/-- The slab passage time `D(u, v)` of a configuration. -/
noncomputable def slabTime (b : ℝ) (sl : Slab m) (c : X.Ω) (u v : Pt m) : ℝ :=
  sl.passTime b (X.ρ c) u v

/-- The slab minimum `F` of a configuration (equation `eq:F`). -/
noncomputable def F (b : ℝ) (M : ℕ) (s : ℝ) (τ : Pt m) (c : X.Ω) : ℝ :=
  slabMinimum b (X.ρ c) M s τ

/-- The indices `J_i` of a configuration. -/
noncomputable def J (b : ℝ) (M : ℕ) (s W : ℝ) (τ : Pt m) (c : X.Ω)
    (i : Fin (M + 1)) : Fin m → ℤ :=
  minimizerIndex b (X.ρ c) M s W τ i

/-- The density of every outcome gives valid chains of nonnegative width. -/
theorem isValidChain (c : X.Ω) {s : ℝ} (hs : 0 ≤ s) : IsValidChain (X.ρ c) s := by
  obtain ⟨a, b, -, hab⟩ := X.bounds
  exact ⟨hs, X.measurable_ρ.comp measurable_prodMk_left, ⟨b, by
    rintro _ ⟨x, rfl⟩
    exact (hab c x).2⟩⟩

end Setting

end IsotropicVariance.Paper
