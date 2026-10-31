/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusSupport
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith

/-!
# Lemma `lem:modulus`: the rerouting of a geodesic

The deterministic steps of the paper's proof of Lemma `lem:modulus`, which replace the subslabs of
the proof of [AB26, Lemma 5.2]:

* `exists_first_hit`: along a walk on which a height `f` rises by at most one at each edge, the
  first vertex with `f ≥ k` has `f = k`;
* `exists_first_last`: a walk from `u` to `v`, with `u₁ ≤ k ≤ k' ≤ v₁`, has a first vertex `x` with
  `x₁ ≥ k` and a last vertex `x'` with `x'₁ ≤ k'`, with `x₁ = k` and `x'₁ = k'`, and `x` precedes
  `x'`. The paper's `k` and `k'` are `u·e₁ + ⌈gℓ⌉` and `v·e₁ − ⌈gℓ⌉`, and a vertex of height at
  least `u·e₁ + gℓ` has height at least `k`, since heights are integers;
* `passageTimeReal_eq_add_add`: a geodesic splits the passage time at the two points;
* `reroute_le`, `abs_modulus_le_of_reroute`: the display
  `T(ũ,ṽ) − T(u,v) ≤ T(ũ,x) − T(u,x) + T(x',ṽ) − T(x',v)`, with `T` on both sides, and the bound
  it gives for the quantity of equation `eq:modulus`, writing `μ = ζ_t· + φ`. The linear terms
  cancel.
-/

@[expose] public section

open Set
open scoped NNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-! ## The first vertex and the last vertex -/

/-- If `f` rises by at most one along each edge, the first vertex with `f ≥ k` of a walk from
`f ≤ k` to `f ≥ k` has `f = k`: the walk splits there, and every earlier vertex has `f < k`. -/
theorem exists_first_hit {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hf : ∀ a b, G.Adj a b → f b ≤ f a + 1) {u v : V} (γ : G.Walk u v) {k : ℤ} (hu : f u ≤ k)
    (hv : k ≤ f v) :
    ∃ (x : V) (γ₁ : G.Walk u x) (γ₂ : G.Walk x v), γ = γ₁.append γ₂ ∧ f x = k ∧
      ∀ y ∈ γ₁.support, y ≠ x → f y < k := by
  induction γ with
  | nil =>
    refine ⟨_, .nil, .nil, rfl, le_antisymm hu hv, fun y hy hne => ?_⟩
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
    exact absurd hy hne
  | @cons a b c hadj p ih =>
    by_cases hk : f a = k
    · refine ⟨a, .nil, .cons hadj p, rfl, hk, fun y hy hne => ?_⟩
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      exact absurd hy hne
    · have ha : f a < k := lt_of_le_of_ne hu hk
      obtain ⟨x, γ₁, γ₂, rfl, hx, hy⟩ := ih (by have := hf a b hadj; omega) hv
      refine ⟨x, .cons hadj γ₁, γ₂, rfl, hx, fun y hy' hne => ?_⟩
      rcases SimpleGraph.Walk.support_cons hadj γ₁ ▸ hy' with _ | ⟨_, hy'⟩
      · exact ha
      · exact hy y hy' hne

/-- The first coordinate changes by at most one along each edge. -/
theorem abs_fst_sub_le_one_of_adj {a b : Vertex m} (h : (latticeGraph m).Adj a b) :
    b.1 ≤ a.1 + 1 ∧ a.1 ≤ b.1 + 1 := by
  rcases Infra.FPP.latticeGraph_adj.mp h with h | h | ⟨j, h | h⟩ <;> subst h <;>
    simp only [Prod.fst_add, Prod.fst_sub] <;> omega

/-- **The first and the last vertex** (the proof of Lemma `lem:modulus`): for a walk from `u` to `v`
and integers `u₁ ≤ k ≤ k' ≤ v₁`, the first vertex `x` with `x₁ ≥ k` has `x₁ = k`, the last vertex
`x'` with `x'₁ ≤ k'` has `x'₁ = k'`, since the first coordinate changes by at most one along each
edge, and `x` precedes `x'`. -/
theorem exists_first_last {u v : Vertex m} (γ : (latticeGraph m).Walk u v) {k k' : ℤ}
    (h₁ : u.1 ≤ k) (h₂ : k ≤ k') (h₃ : k' ≤ v.1) :
    ∃ (x x' : Vertex m) (γ₁ : (latticeGraph m).Walk u x) (γ₂ : (latticeGraph m).Walk x x')
      (γ₃ : (latticeGraph m).Walk x' v), γ = γ₁.append (γ₂.append γ₃) ∧ x.1 = k ∧ x'.1 = k' ∧
      (∀ y ∈ γ₁.support, y ≠ x → y.1 < k) ∧ (∀ y ∈ γ₃.support, y ≠ x' → k' < y.1) := by
  obtain ⟨x, γ₁, γ', rfl, hx, hfirst⟩ := exists_first_hit (fun y : Vertex m => y.1)
    (fun _ _ h => (abs_fst_sub_le_one_of_adj h).1) γ h₁ (h₂.trans h₃)
  obtain ⟨x', δ₁, δ₂, hrev, hx', hlast⟩ := exists_first_hit (fun y : Vertex m => -y.1)
    (fun _ _ h => by have := (abs_fst_sub_le_one_of_adj h).2; omega) γ'.reverse
    (by show -v.1 ≤ -k'; omega) (by show -k' ≤ -x.1; omega)
  have hγ' : γ' = δ₂.reverse.append δ₁.reverse := by
    rw [← SimpleGraph.Walk.reverse_append, ← hrev, SimpleGraph.Walk.reverse_reverse]
  refine ⟨x, x', γ₁, δ₂.reverse, δ₁.reverse, by rw [hγ'], hx, by omega, hfirst,
    fun y hy hne => ?_⟩
  have hy' : y ∈ δ₁.support := by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse]
    using hy
  have := hlast y hy' hne
  omega

/-! ## The passage time at the two points -/

/-- A geodesic splits the passage time at two vertices `x`, `x'`, with `x` before `x'`. -/
theorem passageTimeReal_eq_add_add {ω : Config m} {u v x x' : Vertex m}
    {γ : (latticeGraph m).Walk u v} (hγ : walkCost ω γ = passageTime ω u v)
    {γ₁ : (latticeGraph m).Walk u x} {γ₂ : (latticeGraph m).Walk x x'}
    {γ₃ : (latticeGraph m).Walk x' v} (hsplit : γ = γ₁.append (γ₂.append γ₃)) :
    passageTimeReal ω u v =
      passageTimeReal ω u x + passageTimeReal ω x x' + passageTimeReal ω x' v := by
  have h₁ := Infra.FPP.passageTime_le_walkCost ω γ₁
  have h₂ := Infra.FPP.passageTime_le_walkCost ω γ₂
  have h₃ := Infra.FPP.passageTime_le_walkCost ω γ₃
  have t₁ := Infra.FPP.passageTime_triangle ω u x v
  have t₂ := Infra.FPP.passageTime_triangle ω x x' v
  have hc : walkCost ω γ = walkCost ω γ₁ + (walkCost ω γ₂ + walkCost ω γ₃) := by
    rw [hsplit, Infra.FPP.walkCost_append, Infra.FPP.walkCost_append]
  have heq : passageTime ω u v =
      passageTime ω u x + passageTime ω x x' + passageTime ω x' v := by
    refine le_antisymm ?_ ?_
    · rw [add_assoc]
      exact t₁.trans (add_le_add le_rfl t₂)
    · rw [← hγ, hc, add_assoc]
      exact add_le_add h₁ (add_le_add h₂ h₃)
  unfold passageTimeReal
  rw [heq, NNReal.coe_add, NNReal.coe_add]

/-! ## The comparison -/

/-- **The rerouting** (the proof of Lemma `lem:modulus`): if
`T(u,v) = T(u,x) + T(x,x') + T(x',v)`, then `T(ũ,ṽ) − T(u,v) ≤ T(ũ,x) − T(u,x) + T(x',ṽ) − T(x',v)`,
and writing `μ = P· + φ`, the linear terms cancel:
`T(ũ,ṽ) − T(u,v) − P·(ṽ − ũ − v + u) ≤ 4Y + (φ(x−ũ) − φ(x−u)) + (φ(ṽ−x') − φ(v−x'))`, for `Y`
bounding `|T − μ|` at the four pairs. -/
theorem reroute_le {T : Vertex m → Vertex m → ℝ} (μ : PtNorm m) (P : Pt m)
    {u u₂ v v₂ x x' : Vertex m} {Y D₁ D₂ : ℝ}
    (htri : T u₂ v₂ ≤ T u₂ x + T x x' + T x' v₂)
    (hsplit : T u v = T u x + T x x' + T x' v)
    (h₁ : |T u x - μ.1 (point x - point u)| ≤ Y)
    (h₂ : |T u₂ x - μ.1 (point x - point u₂)| ≤ Y)
    (h₃ : |T x' v - μ.1 (point v - point x')| ≤ Y)
    (h₄ : |T x' v₂ - μ.1 (point v₂ - point x')| ≤ Y)
    (hD₁ : supportExcess μ P (point x - point u₂) - supportExcess μ P (point x - point u) ≤ D₁)
    (hD₂ : supportExcess μ P (point v₂ - point x') - supportExcess μ P (point v - point x') ≤ D₂) :
    T u₂ v₂ - T u v - inner ℝ P (point v₂ - point u₂ - point v + point u) ≤ 4 * Y + D₁ + D₂ := by
  have hE (a b : Vertex m) : supportExcess μ P (point a - point b) =
      μ.1 (point a - point b) - (inner ℝ P (point a) - inner ℝ P (point b)) := by
    rw [supportExcess, inner_sub_right]
  have hP : inner ℝ P (point v₂ - point u₂ - point v + point u) =
      inner ℝ P (point v₂) - inner ℝ P (point u₂) - inner ℝ P (point v) + inner ℝ P (point u) := by
    simp only [inner_add_right, inner_sub_right]
  rw [hE, hE] at hD₁ hD₂
  have a₁ := abs_le.mp h₁
  have a₂ := abs_le.mp h₂
  have a₃ := abs_le.mp h₃
  have a₄ := abs_le.mp h₄
  rw [hP]
  linarith only [htri, hsplit, a₁.1, a₂.2, a₃.1, a₄.2, hD₁, hD₂]

/-- The bound for the quantity of equation `eq:modulus`, from the rerouting of the geodesics from
`u` to `v` and, exchanging the roles, from `ũ` to `ṽ`: if every pair of `I × I'` splits at a point
of `X₁` and a point of `X₂`, then
`|T(u,v) − T(ũ,ṽ) − P·(v − u − ṽ + ũ)| ≤ 4Y + 2D`. -/
theorem abs_modulus_le_of_reroute {T : Vertex m → Vertex m → ℝ}
    (htri : ∀ a b c, T a c ≤ T a b + T b c) (μ : PtNorm m) (P : Pt m)
    {I I' X₁ X₂ : Set (Vertex m)} {Y D : ℝ} {close : Vertex m → Vertex m → Prop}
    (hclose : ∀ a b, close a b → close b a)
    (hs : ∀ u ∈ I, ∀ v ∈ I', ∃ x ∈ X₁, ∃ x' ∈ X₂, T u v = T u x + T x x' + T x' v)
    (hY₁ : ∀ u ∈ I, ∀ x ∈ X₁, |T u x - μ.1 (point x - point u)| ≤ Y)
    (hY₂ : ∀ x ∈ X₂, ∀ v ∈ I', |T x v - μ.1 (point v - point x)| ≤ Y)
    (hD₁ : ∀ u ∈ I, ∀ u₂ ∈ I, close u u₂ → ∀ x ∈ X₁,
      |supportExcess μ P (point x - point u₂) - supportExcess μ P (point x - point u)| ≤ D)
    (hD₂ : ∀ v ∈ I', ∀ v₂ ∈ I', close v v₂ → ∀ x ∈ X₂,
      |supportExcess μ P (point v₂ - point x) - supportExcess μ P (point v - point x)| ≤ D)
    {u u₂ v v₂ : Vertex m} (hu : u ∈ I) (hu₂ : u₂ ∈ I) (hv : v ∈ I') (hv₂ : v₂ ∈ I')
    (huu : close u u₂) (hvv : close v v₂) :
    |T u v - T u₂ v₂ - inner ℝ P (point v - point u - point v₂ + point u₂)| ≤ 4 * Y + 2 * D := by
  -- the geodesic from `u` to `v`
  obtain ⟨x, hx, x', hx', hsp⟩ := hs u hu v hv
  have up := reroute_le μ P (u := u) (u₂ := u₂) (v := v) (v₂ := v₂)
    (((htri u₂ x v₂).trans (add_le_add le_rfl (htri x x' v₂))).trans_eq (by ring)) hsp
    (hY₁ u hu x hx) (hY₁ u₂ hu₂ x hx) (hY₂ x' hx' v hv) (hY₂ x' hx' v₂ hv₂)
    (abs_le.mp (hD₁ u hu u₂ hu₂ huu x hx)).2 (abs_le.mp (hD₂ v hv v₂ hv₂ hvv x' hx')).2
  -- exchanging the roles: the geodesic from `ũ` to `ṽ`
  obtain ⟨y, hy, y', hy', hsq⟩ := hs u₂ hu₂ v₂ hv₂
  have lo := reroute_le μ P (u := u₂) (u₂ := u) (v := v₂) (v₂ := v)
    (((htri u y v).trans (add_le_add le_rfl (htri y y' v))).trans_eq (by ring)) hsq
    (hY₁ u₂ hu₂ y hy) (hY₁ u hu y hy) (hY₂ y' hy' v₂ hv₂) (hY₂ y' hy' v hv)
    (abs_le.mp (hD₁ u₂ hu₂ u hu (hclose _ _ huu) y hy)).2
    (abs_le.mp (hD₂ v₂ hv₂ v hv (hclose _ _ hvv) y' hy')).2
  have e₁ : inner ℝ P (point v₂ - point u₂ - point v + point u) =
      -inner ℝ P (point v - point u - point v₂ + point u₂) := by
    rw [← inner_neg_right]; congr 1; abel
  rw [e₁] at up
  rw [abs_le]
  constructor <;> linarith only [up, lo]

end CurvatureVariance.Paper.Localization.Modulus
