/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocFrame
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Geometry.TurningSlopes

/-!
# Lemma `lem:localization`: the thickenings of the second change

The sentences of the second change in the proof of Lemma `lem:localization` on the thickenings, for
one outcome.

* `Loc.ctr`, `Loc.gapOf`: the cube of side `W` of index `(j, k)` in an annulus `β`: its hyperplane
  is `p + j g_β` and its center is at the offset `(W − 1) k` from the line, where `g_β = ⌊c₀ℓ/β⌋`
  is the spacing of the hyperplanes. Spacing `W − 1` makes the closed cubes of side `W` cover the
  lattice points of the hyperplane (`mem_thicken_of_coord`).
* `mem_thicken_cube`: the cover: every vertex lies in the thickening by `g_β` along `(1, t)` of the
  cube of its index, and `abs_round_le`, `mem_family` place the index in the finite family.
* `Loc.family`: the family of the paper, and `sum_family_eq` counts it: `C β^d` indices at `β`.
* `thicken_subset_thicken`: "for `c₀` small, the thickening lies in the thickenings of `I''`".
* `isCubePair_left`, `isCubePair_right`: the pairs `{a}, I''` and `I'', {a'}`, whose slopes are the
  slopes of the vectors from `a` to the center of `I''`, and from this center to `a'`
  (`Loc.slopeL`, `Loc.slopeR`), and `smul_slopeL_sub`, `smul_slopeR_sub`, `norm_sub_le_of_smul`:
  `|t₁ − t|, |t₂ − t|` from the offsets.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper Radius

variable {m : ℕ}

/-! ## Membership in thickenings -/

/-- `mem_thicken_of_coord` of `CurvatureVariance.Paper.Proofs.Localization.RadiusGeometry`,
two-sided: `x` lies at distance at most `ρ` on either side of the hyperplane. -/
theorem mem_thicken_of_coord' {q : ℤ} {c t' : EuclideanSpace ℝ (Fin m)} {side ρ : ℝ} {x : Vertex m}
    (hτρ : |((x.1 - q : ℤ) : ℝ)| ≤ ρ)
    (hcoord : ∀ i, |(x.2 i : ℝ) - ((x.1 - q : ℤ) : ℝ) * t' i - c i| ≤ side / 2 - 1 / 2) :
    x ∈ thicken (transverseCube q c side) t' ρ := by
  set τ : ℝ := ((x.1 - q : ℤ) : ℝ)
  set y : EuclideanSpace ℝ (Fin m) := transversePoint x.2 - τ • t'
  refine ⟨roundVertex q y, ⟨rfl, fun i => ?_⟩, τ, hτρ, ?_⟩
  · simp only [roundVertex]
    have h1 := abs_sub_round (y i)
    have h2 := hcoord i
    have hy : y i = (x.2 i : ℝ) - τ * t' i := by
      simp [y, transversePoint]
    calc |(round (y i) : ℝ) - c i| ≤ |(round (y i) : ℝ) - y i| + |y i - c i| := abs_sub_le _ _ _
      _ ≤ 1 / 2 + (side / 2 - 1 / 2) := by
          rw [abs_sub_comm] at h1; rw [hy]; exact add_le_add h1 h2
      _ = side / 2 := by ring
  · have h := norm_point_roundVertex_sub_le q y
    have heq : point x - (point (roundVertex q y) + τ • slopeVec t') =
        -(point (roundVertex q y) - WithLp.toLp 2 ((q : ℝ), y)) := by
      refine Infra.FPP.pt_ext ?_ ?_
      · simp [roundVertex, τ, slopeVec]
      · simp [roundVertex, y, slopeVec]; abel
    rw [heq, norm_neg]; exact h

/-! ## The cubes of the annuli -/

/-- The spacing `g_β = ⌊ρ₀/β⌋` of the hyperplanes of the annulus `β`, with `ρ₀ = c₀ℓ`. -/
noncomputable def gapOf (ρ₀ : ℝ) (β : ℕ) : ℕ := ⌊ρ₀ / β⌋₊

/-- The center of the cube of offset index `k`, in the hyperplane at `h` from `p`. -/
noncomputable def ctr (t c : EuclideanSpace ℝ (Fin m)) (G : ℝ) (h : ℤ) (k : Fin m → ℤ) :
    EuclideanSpace ℝ (Fin m) :=
  c + (h : ℝ) • t + G • transversePoint k

theorem ctr_apply (t c : EuclideanSpace ℝ (Fin m)) (G : ℝ) (h : ℤ) (k : Fin m → ℤ) (i : Fin m) :
    ctr t c G h k i = c i + (h : ℝ) * t i + G * k i := by
  simp [ctr, transversePoint]

/-- `|y − G round(y/G)| ≤ G/2`. -/
theorem abs_sub_mul_round_le {y G : ℝ} (hG : 0 < G) : |y - G * round (y / G)| ≤ G / 2 := by
  have h := abs_sub_round (y / G)
  have e : y - G * round (y / G) = G * (y / G - round (y / G)) := by field_simp
  rw [e, abs_mul, abs_of_pos hG]
  nlinarith only [h, hG]

/-- **The cover**: `x` lies in the thickening by `g` along `(1, t)` of the cube of side `G + 1` of
its index, `j = ⌊(x₁ − p)/g⌋`, `k = round(ofs x/G)`. -/
theorem mem_thicken_cube {t : EuclideanSpace ℝ (Fin m)} (p : ℤ) (c : EuclideanSpace ℝ (Fin m))
    {G : ℝ} (hG : 0 < G) {g : ℕ} (hg : 0 < g) (x : Vertex m) :
    x ∈ thicken (transverseCube (p + (x.1 - p) / g * g)
        (ctr t c G ((x.1 - p) / g * g) fun i => round (ofs t p c x i / G)) (G + 1)) t g := by
  have hg' : (0 : ℤ) < g := by exact_mod_cast hg
  set j : ℤ := (x.1 - p) / g with hj
  set q : ℤ := p + j * g with hq
  have hr : x.1 - q = (x.1 - p) % g := by
    have := Int.emod_add_mul_ediv (x.1 - p) g
    rw [← hj] at this
    rw [hq]; linarith only [this]
  have h0 : 0 ≤ x.1 - q := by rw [hr]; exact Int.emod_nonneg _ hg'.ne'
  have h1 : x.1 - q < g := by rw [hr]; exact Int.emod_lt_of_pos _ hg'
  refine mem_thicken_of_coord (by omega) (by exact_mod_cast h1.le) fun i => ?_
  set k : Fin m → ℤ := fun i => round (ofs t p c x i / G)
  have e : (x.2 i : ℝ) - ((x.1 - q : ℤ) : ℝ) * t i - ctr t c G (j * g) k i =
      ofs t p c x i - G * k i := by
    rw [ctr_apply, ofs_apply, hq]
    push_cast
    ring
  rw [e]
  have := abs_sub_mul_round_le (y := ofs t p c x i) hG
  linarith only [this]

/-- The offset index is at most `‖ofs x‖/G + 1/2`. -/
theorem abs_round_le {t : EuclideanSpace ℝ (Fin m)} (p : ℤ) (c : EuclideanSpace ℝ (Fin m))
    {G : ℝ} (hG : 0 < G) (x : Vertex m) (i : Fin m) :
    |(round (ofs t p c x i / G) : ℝ)| ≤ ‖ofs t p c x‖ / G + 1 / 2 := by
  have h1 := abs_sub_round (ofs t p c x i / G)
  have h2 : |ofs t p c x i / G| ≤ ‖ofs t p c x‖ / G := by
    rw [abs_div, abs_of_pos hG]
    have := PiLp.norm_apply_le (ofs t p c x) i
    rw [Real.norm_eq_abs] at this
    exact div_le_div_of_nonneg_right this hG.le
  have h3 := abs_sub_abs_le_abs_sub (round (ofs t p c x i / G) : ℝ) (ofs t p c x i / G)
  rw [abs_sub_comm (round (ofs t p c x i / G) : ℝ)] at h3
  linarith only [h1, h2, h3]

/-! ## The family of the thickenings -/

/-- An index: the annulus `β`, and the indices `(j, k)` of a cube. -/
abbrev Idx (m : ℕ) := (_ : ℕ) × ℤ × (Fin m → ℤ)

/-- **The family of the paper**: `1 ≤ β ≤ B`, `−1 ≤ j ≤ ℓ/g_β + 1`, `|k_i| ≤ κβ`. -/
noncomputable def family (m B κ ℓ : ℕ) (ρ₀ : ℝ) : Finset (Idx m) :=
  (Finset.Icc 1 B).sigma fun β =>
    Finset.Icc (-1 : ℤ) (((ℓ / gapOf ρ₀ β : ℕ) : ℤ) + 1) ×ˢ
      Fintype.piFinset fun _ : Fin m => Finset.Icc (-((κ * β : ℕ) : ℤ)) ((κ * β : ℕ) : ℤ)

/-- The membership in the family, from the coordinates. -/
theorem mem_family {B κ ℓ : ℕ} {ρ₀ : ℝ} {β : ℕ} {j : ℤ} {k : Fin m → ℤ} (h1 : 1 ≤ β)
    (h2 : β ≤ B) (hj1 : -1 ≤ j) (hj2 : j ≤ ((ℓ / gapOf ρ₀ β : ℕ) : ℤ) + 1)
    (hk : ∀ i, |(k i : ℝ)| ≤ ((κ * β : ℕ) : ℝ)) :
    (⟨β, j, k⟩ : Idx m) ∈ family m B κ ℓ ρ₀ := by
  simp only [family, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_product, Fintype.mem_piFinset]
  refine ⟨⟨h1, h2⟩, ⟨hj1, hj2⟩, fun i => ?_⟩
  have := hk i
  rw [abs_le] at this
  constructor
  · have h3 : ((-((κ * β : ℕ) : ℤ) : ℤ) : ℝ) ≤ (k i : ℝ) := by
      push_cast; push_cast at this; linarith [this.1]
    exact_mod_cast h3
  · have h3 : (k i : ℝ) ≤ (((κ * β : ℕ) : ℤ) : ℝ) := by
      push_cast; push_cast at this; linarith [this.2]
    exact_mod_cast h3

/-- The first index of a member. -/
theorem family_fst {B κ ℓ : ℕ} {ρ₀ : ℝ} {i : Idx m} (hi : i ∈ family m B κ ℓ ρ₀) :
    1 ≤ i.1 ∧ i.1 ≤ B := by
  simp only [family, Finset.mem_sigma, Finset.mem_Icc] at hi
  exact hi.1

/-- The hyperplane index of a member. -/
theorem family_snd {B κ ℓ : ℕ} {ρ₀ : ℝ} {i : Idx m} (hi : i ∈ family m B κ ℓ ρ₀) :
    -1 ≤ i.2.1 ∧ i.2.1 ≤ ((ℓ / gapOf ρ₀ i.1 : ℕ) : ℤ) + 1 := by
  simp only [family, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_product] at hi
  exact hi.2.1

/-- The offset index of a member. -/
theorem family_abs_le {B κ ℓ : ℕ} {ρ₀ : ℝ} {i : Idx m} (hi : i ∈ family m B κ ℓ ρ₀) (l : Fin m) :
    |(i.2.2 l : ℝ)| ≤ ((κ * i.1 : ℕ) : ℝ) := by
  simp only [family, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_product, Fintype.mem_piFinset]
    at hi
  have h := hi.2.2 l
  rw [abs_le]
  constructor
  · have h3 : ((-((κ * i.1 : ℕ) : ℤ) : ℤ) : ℝ) ≤ (i.2.2 l : ℝ) := by exact_mod_cast h.1
    push_cast at h3 ⊢
    linarith only [h3]
  · have h3 : (i.2.2 l : ℝ) ≤ (((κ * i.1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast h.2
    push_cast at h3 ⊢
    linarith only [h3]

/-- **The sum over the family** of a function of the annulus: the number of indices at `β` is
`(ℓ/g_β + 3) (2κβ + 1)^m`. -/
theorem sum_family_eq {B κ ℓ : ℕ} {ρ₀ : ℝ} (f : ℕ → ℝ) :
    ∑ i ∈ family m B κ ℓ ρ₀, f i.1 =
      ∑ β ∈ Finset.Icc 1 B,
        ((ℓ / gapOf ρ₀ β : ℕ) + 3 : ℝ) * (2 * ((κ * β : ℕ) : ℝ) + 1) ^ m * f β := by
  rw [family, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Fintype.card_piFinset,
    Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e1 : ∀ n : ℕ, ((n : ℤ) + 1 + 1 - -1).toNat = n + 3 := fun n => by omega
  have e2 : ∀ n : ℕ, ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := fun n => by omega
  rw [e1, e2]
  push_cast
  ring

/-- The spacing: `ρ₀/(2β) ≤ g_β ≤ ρ₀/β` when `β ≤ ρ₀`. -/
theorem gapOf_bounds {ρ₀ : ℝ} {β : ℕ} (hβ : 1 ≤ β) (h : (β : ℝ) ≤ ρ₀) :
    ρ₀ / (2 * β) ≤ gapOf ρ₀ β ∧ (gapOf ρ₀ β : ℝ) ≤ ρ₀ / β := by
  have hβ0 : (0 : ℝ) < β := by exact_mod_cast hβ
  have h1 : 1 ≤ ρ₀ / β := by rwa [le_div_iff₀ hβ0, one_mul]
  have h2 := Nat.lt_floor_add_one (ρ₀ / β)
  have h3 := Nat.floor_le (a := ρ₀ / β) (by linarith only [h1])
  have h4 : ρ₀ / (2 * β) = ρ₀ / β / 2 := by field_simp
  have h5 : (1 : ℝ) ≤ (gapOf ρ₀ β : ℝ) := by
    have : 1 ≤ ⌊ρ₀ / β⌋₊ := Nat.le_floor (by simpa using h1)
    exact_mod_cast this
  simp only [gapOf] at *
  rw [h4]
  constructor <;> linarith only [h1, h2, h3, h5]

/-! ## The thickenings of `I''` -/

/-- **The thickening lies in the thickening of the double cube** along a nearby slope: for
`(ρ + √d) ‖t − t'‖ ≤ W/4` and `W` large, `I_W` thickened by `ρ` along `(1, t)` lies in `I_{2W}`,
with the same center, thickened by `ρ' ≥ ρ + √d` along `(1, t')`. -/
theorem thicken_subset_thicken {h : ℤ} {c t t' : EuclideanSpace ℝ (Fin m)} {W ρ ρ' T : ℝ}
    (ht : ‖t‖ ≤ T) (hρ : ρ + Real.sqrt ((m : ℝ) + 1) ≤ ρ') (hsl : ρ' * ‖t - t'‖ ≤ W / 4)
    (hW : (1 + T) * Real.sqrt ((m : ℝ) + 1) + 1 / 2 ≤ W / 4) {x : Vertex m}
    (hx : x ∈ thicken (transverseCube h c W) t ρ) :
    x ∈ thicken (transverseCube h c (2 * W)) t' ρ' := by
  obtain ⟨u, hu, τ, hτ, hxu⟩ := hx
  set d := Real.sqrt ((m : ℝ) + 1)
  set y : Pt m := point x - (point u + τ • slopeVec t) with hy
  have hyfst : y.fst = (x.1 : ℝ) - h - τ := by
    have : u.1 = h := hu.1
    simp [hy, slopeVec, this]; ring
  have hysnd : ∀ i, y.snd i = (x.2 i : ℝ) - u.2 i - τ * t i := by
    intro i
    simp [hy, slopeVec, transversePoint]; ring
  have h1 : |y.fst| ≤ d := (Proofs.Geometry.abs_fst_le_norm y).trans hxu
  have h2 : ‖y.snd‖ ≤ d := (Proofs.Geometry.norm_snd_le_norm y).trans hxu
  set r : ℝ := ((x.1 - h : ℤ) : ℝ) with hr
  have hre : r = τ + y.fst := by rw [hyfst, hr]; push_cast; ring
  have hrρ : |r| ≤ ρ' := by
    rw [hre]
    exact (abs_add_le _ _).trans (by linarith only [hτ, h1, hρ])
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  refine mem_thicken_of_coord' hrρ fun i => ?_
  have e : (x.2 i : ℝ) - r * t' i - c i = y.snd i + ((u.2 i : ℝ) - c i) - y.fst * t i +
      r * (t i - t' i) := by
    rw [hysnd, hre]; ring
  rw [e]
  have a1 : |y.snd i| ≤ d := by
    have := PiLp.norm_apply_le y.snd i
    rw [Real.norm_eq_abs] at this
    exact this.trans h2
  have a2 : |(u.2 i : ℝ) - c i| ≤ W / 2 := hu.2 i
  have a3 : |y.fst * t i| ≤ d * T := by
    rw [abs_mul]
    have := PiLp.norm_apply_le t i
    rw [Real.norm_eq_abs] at this
    exact mul_le_mul h1 (this.trans ht) (abs_nonneg _) (by positivity)
  have a4 : |r * (t i - t' i)| ≤ W / 4 := by
    rw [abs_mul]
    have := PiLp.norm_apply_le (t - t') i
    rw [Real.norm_eq_abs, PiLp.sub_apply] at this
    exact (mul_le_mul hrρ this (abs_nonneg _) ((abs_nonneg _).trans hrρ)).trans hsl
  have a5 := abs_add_le (y.snd i + ((u.2 i : ℝ) - c i) - y.fst * t i) (r * (t i - t' i))
  have a6 := abs_sub (y.snd i + ((u.2 i : ℝ) - c i)) (y.fst * t i)
  have a7 := abs_add_le (y.snd i) ((u.2 i : ℝ) - c i)
  have a8 : (1 + T) * d = d + d * T := by ring
  linarith only [a1, a2, a3, a4, a5, a6, a7, hW, a8]

/-! ## The pairs `{a}, I''` and `I'', {a'}` -/

/-- The lattice point `a` as a cube of side `0`. -/
noncomputable def pointCube (a : Vertex m) : Set (Vertex m) :=
  transverseCube a.1 (transversePoint a.2) 0

theorem mem_pointCube (a : Vertex m) : a ∈ pointCube a :=
  ⟨rfl, fun i => by simp [transversePoint]⟩

/-- The slope `t₁` of the vector from `a` to the center `z` of `I''`, in the hyperplane at `s`. -/
noncomputable def slopeL (s : ℕ) (a : Vertex m) (z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  (s : ℝ)⁻¹ • (z - transversePoint a.2)

/-- The slope `t₂` of the vector from the center `z` of `I''` to `a'`, at `s` from `I''`. -/
noncomputable def slopeR (s : ℕ) (a' : Vertex m) (z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  (s : ℝ)⁻¹ • (transversePoint a'.2 - z)

/-- The pair `{a}, I''`. -/
theorem isCubePair_left (M : Model m) (K : ℕ) (A : ℝ) {W b₀ : ℝ} (a : Vertex m) {s : ℕ}
    (hs : 0 < s) (z : EuclideanSpace ℝ (Fin m)) (hW : 0 ≤ W)
    (hside : 2 * W ≤ b₀ * Paper.W M K A s) (hb₀ : 0 ≤ b₀ * Paper.W M K A s) :
    IsCubePair M K A s b₀ (slopeL s a z) (pointCube a)
      (transverseCube (a.1 + s) z (2 * W)) := by
  refine ⟨a.1, transversePoint a.2, z, 0, 2 * W, rfl, rfl, le_rfl, hb₀, by positivity, hside, ?_⟩
  have hspos : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have : z - transversePoint a.2 - (s : ℝ) • slopeL s a z = 0 := by
    rw [slopeL, smul_smul, mul_inv_cancel₀ hspos, one_smul, sub_self]
  rw [this, norm_zero]; positivity

/-- The pair `I'', {a'}`. -/
theorem isCubePair_right (M : Model m) (K : ℕ) (A : ℝ) {W b₀ : ℝ} (a' : Vertex m) {s : ℕ} {h : ℤ}
    (hs : 0 < s) (hh : a'.1 = h + s) (z : EuclideanSpace ℝ (Fin m)) (hW : 0 ≤ W)
    (hside : 2 * W ≤ b₀ * Paper.W M K A s) (hb₀ : 0 ≤ b₀ * Paper.W M K A s) :
    IsCubePair M K A s b₀ (slopeR s a' z) (transverseCube h z (2 * W)) (pointCube a') := by
  refine ⟨h, z, transversePoint a'.2, 2 * W, 0, rfl, by rw [pointCube, hh], by positivity, hside,
    le_rfl, hb₀, ?_⟩
  have hspos : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have : transversePoint a'.2 - z - (s : ℝ) • slopeR s a' z = 0 := by
    rw [slopeR, smul_smul, mul_inv_cancel₀ hspos, one_smul, sub_self]
  rw [this, norm_zero]; positivity

/-- `s (t₁ − t) = G k − ofs a`, for the cube at `a₁ + s = p + h`. -/
theorem smul_slopeL_sub {t c : EuclideanSpace ℝ (Fin m)} {p : ℤ} {G : ℝ} {h : ℤ}
    {k : Fin m → ℤ} {a : Vertex m} {s : ℕ} (hs : 0 < s) (hh : p + h = a.1 + s) :
    (s : ℝ) • (slopeL s a (ctr t c G h k) - t) = G • transversePoint k - ofs t p c a := by
  have hspos : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have e : (s : ℝ) = (p : ℝ) + h - a.1 := by
    have : ((p + h : ℤ) : ℝ) = ((a.1 + s : ℤ) : ℝ) := by exact_mod_cast hh
    push_cast at this; linarith only [this]
  rw [smul_sub, slopeL, smul_smul, mul_inv_cancel₀ hspos, one_smul]
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, ctr_apply, ofs_apply,
    Infra.FPP.transversePoint_apply]
  rw [e]
  ring

/-- `s (t₂ − t) = ofs a' − G k`, for the cube at `a'₁ − s = p + h`. -/
theorem smul_slopeR_sub {t c : EuclideanSpace ℝ (Fin m)} {p : ℤ} {G : ℝ} {h : ℤ}
    {k : Fin m → ℤ} {a' : Vertex m} {s : ℕ} (hs : 0 < s) (hh : a'.1 = p + h + s) :
    (s : ℝ) • (slopeR s a' (ctr t c G h k) - t) = ofs t p c a' - G • transversePoint k := by
  have hspos : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have e : (a'.1 : ℝ) = (p : ℝ) + h + s := by exact_mod_cast hh
  rw [smul_sub, slopeR, smul_smul, mul_inv_cancel₀ hspos, one_smul]
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, ctr_apply, ofs_apply,
    Infra.FPP.transversePoint_apply]
  rw [e]
  ring

/-- `|t₁ − t|, |t₂ − t|` from `s (t_i − t) = E`. -/
theorem norm_sub_le_of_smul {s : ℝ} (hs : 0 < s) {u t e : EuclideanSpace ℝ (Fin m)}
    (h : s • (u - t) = e) : ‖u - t‖ ≤ ‖e‖ / s := by
  rw [le_div_iff₀ hs, ← h, norm_smul, Real.norm_of_nonneg hs.le, mul_comm]

end CurvatureVariance.Paper.Localization.Loc
