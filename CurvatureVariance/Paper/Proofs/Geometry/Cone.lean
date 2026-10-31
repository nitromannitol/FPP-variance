/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.ConeChain
public import CurvatureVariance.Paper.Proofs.Geometry.SlabsCone
public import CurvatureVariance.Paper.Proofs.Geometry.SlabSurgery

/-!
# Lemma `lem:cone`

`coneStatement_of`: the contract `ConeStatement`, Lemma `lem:cone` and its proof, from Lemma
`lem:support`.

* `IsGood.length_le`, `IsGood.length_le_mul`: the first sentence of the proof: on `IsGood`, a path
  with passage time at most `T(u,v) + S²` has at most `C(N + S²)` edges.
* `IsExcessPath.reflect`: the reflected path `u + v − z`, traversed from `u` to `v`, of the last
  sentences of the proof.
* `cone_exit_bounds`: equation `eq:cone` for a path in a set on which the passage time concentrates,
  from the chain of last exits (`Proofs.Geometry.ConeChain`), and, through the reflected path, its
  second clause.
* `coneStatement_of`: the case `S² ≥ N` of the proof, where the lemma is vacuous, and the
  case `S² < N`, where the path stays in the box `[−2N², 2N²]^d`.

Reading. `Bounds.T` is general (`Contracts.ConeStatement`), so `T = bd.T + 1` bounds the slopes, the
constant `|t_j' − t| ≤ C θ_j` of the paper is `slopeFactor T`, and `C` depends on `T`.
-/

@[expose] public section

open InnerProductGeometry
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### The number of edges -/

section Good

variable {M : Model m} {Cg cg : ℝ} {N : ℕ} {S : ℝ} {ω : Config m}

/-- On `IsGood`, `T(x, y) ≤ C(|y − x| + S²)`, by Lemma `lem:good` (2) in a slab containing `x` and
`y`, and `T ≤ T_P`. -/
theorem _root_.CurvatureVariance.Paper.IsGood.passageTimeReal_le (hω : IsGood M Cg cg N S ω)
    (hCg : 0 ≤ Cg) {x y : Vertex m} (hx : InBox (2 * (N : ℝ) ^ 2) x)
    (hy : InBox (2 * (N : ℝ) ^ 2) y) :
    passageTimeReal ω x y ≤ Cg * (‖point y - point x‖ + S ^ 2) := by
  have h := (passageTime_le_slabTime ω _ _ x y).trans
    (hω.slabTime_le x y hx hy (min x.1 y.1 - 1) (max x.1 y.1 + 1) (by omega) (by omega) (by omega)
      (by omega) (by omega))
  have hX : 0 ≤ Cg * (‖point y - point x‖ + S ^ 2) := by positivity
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hX] at h
  exact h

/-- **The number of edges** (the proof of Lemma `lem:cone`): on `IsGood`, a
self-avoiding path from `u` to `v` with passage time at most `T(u,v) + S²` has at most
`max(C S², (C(|v − u| + S²) + S²) / c)` edges, by Lemma `lem:good` (2) and (3). -/
theorem _root_.CurvatureVariance.Paper.IsGood.length_le (hω : IsGood M Cg cg N S ω) (hCg : 0 ≤ Cg)
    (hcg : 0 < cg) {u v : Vertex m} (hu : InBox (2 * (N : ℝ) ^ 2) u)
    (hv : InBox (2 * (N : ℝ) ^ 2) v) (γ : (latticeGraph m).Walk u v) (hγ : γ.IsPath)
    (hcost : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2) :
    (γ.length : ℝ) ≤
      max (Cg * S ^ 2) ((Cg * (‖point v - point u‖ + S ^ 2) + S ^ 2) / cg) := by
  by_contra hcon
  push Not at hcon
  have h1 : Cg * S ^ 2 ≤ γ.length := (le_max_left _ _).trans hcon.le
  have hexp := hω.le_walkCost u hu v γ hγ h1
  have hT := hω.passageTimeReal_le hCg hu hv
  have h2 : (Cg * (‖point v - point u‖ + S ^ 2) + S ^ 2) / cg < γ.length :=
    (le_max_right _ _).trans_lt hcon
  rw [div_lt_iff₀ hcg] at h2
  linarith only [hexp, hT, h2, hcost, mul_comm cg (γ.length : ℝ)]

/-- The constant of the bound `C(N + S²)` on the number of edges, for displacements of norm at most
`3(1 + T)N`. -/
noncomputable def goodLen (Cg cg T : ℝ) : ℝ :=
  max Cg ((Cg * (3 * (1 + T) + 1) + 1) / cg)

theorem goodLen_nonneg {Cg cg T : ℝ} (hCg : 0 ≤ Cg) : 0 ≤ goodLen Cg cg T :=
  le_max_of_le_left hCg

/-- The bound `C(N + S²)`, for `W ≥ S²`: at most `goodLen Cg cg T · W` edges. -/
theorem _root_.CurvatureVariance.Paper.IsGood.length_le_mul (hω : IsGood M Cg cg N S ω)
    (hCg : 0 ≤ Cg) (hcg : 0 < cg) {T W : ℝ} (hSW : S ^ 2 ≤ W) {u v : Vertex m}
    (hu : InBox (2 * (N : ℝ) ^ 2) u) (hv : InBox (2 * (N : ℝ) ^ 2) v)
    (hvu : ‖point v - point u‖ ≤ 3 * (1 + T) * W) (γ : (latticeGraph m).Walk u v) (hγ : γ.IsPath)
    (hcost : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2) :
    (γ.length : ℝ) ≤ goodLen Cg cg T * W := by
  have hW : 0 ≤ W := (sq_nonneg S).trans hSW
  refine (hω.length_le hCg hcg hu hv γ hγ hcost).trans (max_le ?_ ?_)
  · exact (mul_le_mul_of_nonneg_left hSW hCg).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hW)
  · rw [div_le_iff₀ hcg]
    calc Cg * (‖point v - point u‖ + S ^ 2) + S ^ 2
        ≤ Cg * (3 * (1 + T) * W + W) + W := by
          have := mul_le_mul_of_nonneg_left (add_le_add hvu hSW) hCg
          linarith only [this, hSW]
      _ = (Cg * (3 * (1 + T) + 1) + 1) / cg * W * cg := by field_simp
      _ ≤ goodLen Cg cg T * W * cg :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hW) hcg.le

end Good

/-! ### The reflected path -/

/-- **The reflected path** (the end of the proof of Lemma `lem:cone`): since `μ(−z) = μ(z)`, the
inequality `(*)` of the proof holds also for the path with the vertices `a − z`, traversed in the
opposite direction. With `a = u + v` it runs from `u` to `v`. -/
theorem IsExcessPath.reflect {μ : Seminorm ℝ (Pt m)} {b S : ℝ} {f : ℕ → Pt m}
    (hf : IsExcessPath μ b S f) (a : Pt m) (n : ℕ) :
    IsExcessPath μ b S (fun i => a - f (n - i)) where
  norm_succ_sub_le i := by
    simp only [sub_sub_sub_cancel_left]
    rcases lt_or_ge i n with h | h
    · have e : n - i = (n - (i + 1)) + 1 := by omega
      rw [e]
      exact hf.norm_succ_sub_le _
    · have e1 : n - i = 0 := by omega
      have e2 : n - (i + 1) = 0 := by omega
      rw [e1, e2, sub_self, norm_zero]
      exact zero_le_one
  excess_le i j k hij hjk D hD h1 h2 h3 := by
    simp only [sub_sub_sub_cancel_left] at h1 h2 h3 ⊢
    have := hf.excess_le (n - k) (n - j) (n - i) (by omega) (by omega) D hD h2 h1 h3
    linarith only [this]

/-! ### Equation `eq:cone` on a set where the passage time concentrates -/

/-- **Equation `eq:cone`**, for a path in a set `B` on which the passage time concentrates. For a
slope bound `T ≥ 0` there are `K, ε₀ > 0`, depending only on `μlo, μhi, δ, c, C, r₁, A, T`, such
that for the angular bound centred at any `t₀`, every path `γ` in `B` from `u` to `v = u + ℓ (1, t)`
with passage time at most `T(u,v) + S²`, `‖t‖ ≤ T`, `‖t − t₀‖ ≤ ε₀`, `‖t − t₀‖^{δ/2} L ≤ ε₀` and
`‖v − u‖ ≤ S² e^L` satisfies, at its vertices `z` with `‖v − z‖ ≥ K S²`,
`∠(v − z, (1, t)) ≤ K (S^{1/2} ‖v − z‖^{−1/4} + ‖t − t₀‖^{1+δ/2} L)`, and the same bound for `z − u`
at its vertices with `‖z − u‖ ≥ K S²`. The first bound is `angle_end_exit`. The second is the first
for the path with the vertices `u + v − z`, as in the paper, since `v − (u + v − z) = z − u`. -/
theorem cone_exit_bounds {μ : Seminorm ℝ (Pt m)} {μlo μhi δ c C r₁ A T : ℝ}
    (hμlo : 0 < μlo) (hlo : ∀ z, μlo * ‖z‖ ≤ μ z) (hhi : ∀ z, μ z ≤ μhi * ‖z‖)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < c) (hC : 0 ≤ C) (hr₁ : 0 < r₁) (hA : 0 ≤ A)
    (hT : 0 ≤ T) :
    ∃ K ε₀ : ℝ, 0 < K ∧ 0 < ε₀ ∧
      ∀ t₀ : EuclideanSpace ℝ (Fin m), AngularSupport μ t₀ δ c C r₁ →
      ∀ (ω : Config m) (B : Set (Vertex m)) (S L : ℝ), 1 ≤ S → 1 ≤ L →
      ConcentrationOn ω μ B A S →
      ∀ (u v : Vertex m) (γ : (latticeGraph m).Walk u v),
        (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2 → (∀ z ∈ γ.support, z ∈ B) →
      ∀ (ℓ : ℝ) (t : EuclideanSpace ℝ (Fin m)), 0 < ℓ → point v - point u = ℓ • slopeVec t →
        ‖t‖ ≤ T → ‖t - t₀‖ ≤ ε₀ → ‖t - t₀‖ ^ (δ / 2) * L ≤ ε₀ →
        ‖point v - point u‖ ≤ S ^ 2 * Real.exp L →
      ∀ z ∈ γ.support,
        (K * S ^ 2 ≤ ‖point v - point z‖ →
          angle (point v - point z) (slopeVec t) ≤
            K * (S ^ ((1 : ℝ) / 2) * ‖point v - point z‖ ^ (-(1 : ℝ) / 4) +
              ‖t - t₀‖ ^ (1 + δ / 2) * L)) ∧
        (K * S ^ 2 ≤ ‖point z - point u‖ →
          angle (point z - point u) (slopeVec t) ≤
            K * (S ^ ((1 : ℝ) / 2) * ‖point z - point u‖ ^ (-(1 : ℝ) / 4) +
              ‖t - t₀‖ ^ (1 + δ / 2) * L)) := by
  have hμ : μlo ≤ μhi := by
    have h := (hlo (slopeVec 0)).trans (hhi (slopeVec 0))
    have h1 := one_le_norm_slopeVec (0 : EuclideanSpace ℝ (Fin m))
    exact le_of_mul_le_mul_right h (by linarith only [h1])
  set b := 1 + 6 * A with hbdef
  have hb : 0 < b := by positivity
  -- the constants of the chain, at `μlo / 2`, and a lowest radius for the no-return property
  have hμlo₂ : 0 < μlo / 2 := half_pos hμlo
  obtain ⟨Kc, P, Q, η, ε₁, M₀, ε₀, hε₀, hK₀⟩ :=
    exists_chainConstants hμlo₂ ((half_le_self hμlo.le).trans hμ) hδ hδ1 hc hC hr₁ hb hT
  set M := max M₀ (noReturnConst (μlo / 2) μhi b) with hMdef
  have hK := hK₀.mono_M (M' := M) (le_max_left _ _)
  have hM : noReturnConst (μlo / 2) μhi b ≤ M := le_max_right _ _
  have hlo₂ : ∀ z, 2 * (μlo / 2) * ‖z‖ ≤ μ z := fun z => by
    have e : 2 * (μlo / 2) = μlo := by ring
    rw [e]
    exact hlo z
  set K := max (8 * M / (μlo / 2))
    (max (P * (min (μlo / 2 / 4) 1)⁻¹) (max (3 * Q) 1)) with hKdef
  have hK1 : 8 * M / (μlo / 2) ≤ K := le_max_left _ _
  have hK3 : P * (min (μlo / 2 / 4) 1)⁻¹ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK4 : 3 * Q ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hK5 : 1 ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨K, ε₀, by linarith only [hK5], hε₀, ?_⟩
  intro t₀ hsupp ω B S L hS hL hconc u v γ hcost hB ℓ t hℓ hend htT ht htL hlen z hz
  have hf := isExcessPath_of_concentrationOn hA (by linarith only [hS]) hconc hcost hB
  obtain ⟨k, hkz, hkn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hz
  constructor
  · -- the bound for `v − z`
    intro hRk
    have key := angle_end_exit hK hlo₂ hhi hM hsupp hf hS hL hℓ
      (by simpa only [γ.getVert_length, γ.getVert_zero] using hend) htT ht htL
      (by simpa only [γ.getVert_length, γ.getVert_zero] using hlen) hK1 hK3 hK4 hK5 hkn
      (by simpa only [γ.getVert_length, hkz] using hRk)
    simpa only [γ.getVert_length, hkz] using key
  · -- the bound for `z − u`: the first bound for the path with the vertices `u + v − z`
    intro hRk
    have hg := hf.reflect (point u + point v) γ.length
    have hsub : γ.length - (γ.length - k) = k := Nat.sub_sub_self hkn
    have key := angle_end_exit hK hlo₂ hhi hM hsupp hg hS hL hℓ
      (by simpa only [Nat.sub_self, Nat.sub_zero, γ.getVert_length, γ.getVert_zero,
        sub_sub_sub_cancel_left] using hend) htT ht htL
      (by simpa only [Nat.sub_self, Nat.sub_zero, γ.getVert_length, γ.getVert_zero,
        sub_sub_sub_cancel_left] using hlen) hK1 hK3 hK4 hK5 (Nat.sub_le γ.length k)
      (by simpa only [Nat.sub_self, hsub, γ.getVert_zero, hkz, sub_sub_sub_cancel_left] using hRk)
    simpa only [Nat.sub_self, hsub, γ.getVert_zero, hkz, sub_sub_sub_cancel_left] using key

/-! ### Lemma `lem:cone` -/

/-- At every slope `τ` with `‖τ − t₀‖ ≤ r₁` there is a subgradient with equation `eq:angular`,
from the second clause of `SupportStatement`. -/
theorem angularSupport_of_support (hS : SupportStatement m) {bd : Bounds m} (hbd : bd.Valid) :
    ∃ c C r₁ : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 < r₁ ∧ ∀ M : Model m, M.Standing → M.Fits bd →
      AngularSupport M.μ.1 M.t₀ M.δ c C r₁ := by
  obtain ⟨c, C, r₁, hc, hC, hr₁, -, h⟩ := hS bd hbd
  refine ⟨c, C, r₁, hc, hC.le, hr₁, fun M hM hfit τ hτ => ?_⟩
  obtain ⟨p, hp⟩ := exists_isSubgradient M.μ (slopeVec τ)
  exact ⟨p, hp.1, hp.2, (h M hM hfit).2 τ hτ p hp⟩

/-- For `N` large and `0 ≤ x ≤ 3 N^{−1/9}`: `x ≤ ε` and `x^{δ/2} log N ≤ ε`. -/
theorem exists_small_of_le_three_rpow {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ x : ℝ, 0 ≤ x → x ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) →
      x ≤ ε ∧ x ^ (δ / 2) * Real.log N ≤ ε := by
  obtain ⟨N₁, hN₁⟩ := exists_nat_rpow_neg_le (r := 1 / 9) (by norm_num) (ε := ε / 3)
    (by positivity)
  obtain ⟨N₂, hN₂⟩ := exists_nat_rpow_neg_mul_log_le (r := 1 / 9 * (δ / 2)) (by positivity)
    (ε := ε / 3 ^ (δ / 2)) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun N hN x hx0 hx => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  have e : (-(1 : ℝ) / 9) = -(1 / 9) := by ring
  rw [e] at hx
  refine ⟨?_, ?_⟩
  · have h := hN₁ N hN1
    linarith only [h, hx]
  · have h1 : x ^ (δ / 2) ≤ (3 * (N : ℝ) ^ (-(1 / 9 : ℝ))) ^ (δ / 2) :=
      Real.rpow_le_rpow hx0 hx (by positivity)
    have h2 : (3 * (N : ℝ) ^ (-(1 / 9 : ℝ))) ^ (δ / 2) =
        3 ^ (δ / 2) * (N : ℝ) ^ (-(1 / 9 * (δ / 2))) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNpos.le _),
        ← Real.rpow_mul hNpos.le, neg_mul]
    have h3 := hN₂ N hN2
    rw [le_div_iff₀ (by positivity)] at h3
    rcases le_or_gt (Real.log N) 0 with hl | hl
    · have : 0 ≤ x ^ (δ / 2) := Real.rpow_nonneg hx0 _
      nlinarith only [this, hl, hε]
    · calc x ^ (δ / 2) * Real.log N
          ≤ 3 ^ (δ / 2) * (N : ℝ) ^ (-(1 / 9 * (δ / 2))) * Real.log N := by
            rw [← h2]; exact mul_le_mul_of_nonneg_right h1 hl.le
        _ = (N : ℝ) ^ (-(1 / 9 * (δ / 2))) * Real.log N * 3 ^ (δ / 2) := by ring
        _ ≤ ε := h3

/-- **The conclusion of Lemma `lem:cone`** at one configuration: `ConeStatement` is
`IsGood → ConeAt`. -/
def ConeAt (M : Model m) (C S : ℝ) (N : ℕ) (ω : Config m) : Prop :=
  ∀ (ℓ : ℕ) (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m),
    InBox ((N : ℝ) ^ 2) u → InBox ((N : ℝ) ^ 2) v →
    point v - point u = (ℓ : ℝ) • slopeVec t → 1 ≤ ℓ → (ℓ : ℝ) ≤ 3 * N →
    ‖t - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) →
    ∀ γ : (latticeGraph m).Walk u v, γ.IsPath →
      (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2 → ∀ z ∈ γ.support,
        ConeBound M C S N t (point v - point z) ∧ ConeBound M C S N t (point z - point u)

/-- **Lemma `lem:cone`**, with its proof, from Lemma `lem:support`.
The constant and the threshold depend on `bd`, `C_g` and `c_g`: the norm and `δ` of the law, the
constants of `SupportStatement` at `bd`, and `T = bd.T + 1`. -/
theorem coneStatement_of (hsupport : SupportStatement m) : ConeStatement m := by
  intro bd hbd Cg cg hCg hcg
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := PtNorm.exists_bounds bd.law.μ
  obtain ⟨c₅, C₅, r₅, hc₅, hC₅, hr₅, hsupp⟩ := angularSupport_of_support hsupport hbd
  set T := bd.T + 1 with hTdef
  have hT : 0 ≤ T := by linarith only [hbd.T_nonneg, hTdef]
  obtain ⟨K, ε₀, hK, hε₀, hcone⟩ := cone_exit_bounds hlo (fun z => (hb z).1) (fun z => (hb z).2)
    hbd.law.delta_pos hbd.law.delta_le_one hc₅ hC₅ hr₅ hCg.le hT
  set Cv := goodLen Cg cg T with hCv
  have hCv0 : 0 ≤ Cv := goodLen_nonneg hCg.le
  set C := max (2 * K) (Cv + 3 * (1 + T) + 1) with hCdef
  have hC2K : 2 * K ≤ C := le_max_left _ _
  have hCv7 : Cv + 3 * (1 + T) + 1 ≤ C := le_max_right _ _
  refine ⟨C, by positivity, ?_⟩
  obtain ⟨N₁, hN₁⟩ := exists_small_of_le_three_rpow hbd.law.delta_pos
    (ε := min (ε₀ / 2) 1) (by positivity)
  refine ⟨max N₁ (max (max 6 ⌈3 * (1 + T)⌉₊) ⌈Cv⌉₊),
    fun M hM hfit N hN S hS ω hω => ?_⟩
  -- the facts chosen at the law of `bd`, for the model
  rw [← hfit.μ_eq, ← hfit.δ_eq] at hcone
  rw [← hfit.δ_eq] at hN₁
  have hδ := hM.delta_pos
  have ht₀ := hfit.t₀_le
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN6 : 6 ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hNT' : ⌈3 * (1 + T)⌉₊ ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hNT : 3 * (1 + T) ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNT')
  have hNCv : Cv ≤ N := (Nat.le_ceil Cv).trans
    (by exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hNr : (6 : ℝ) ≤ N := by exact_mod_cast hN6
  have hNpos : (0 : ℝ) < N := by linarith only [hNr]
  have hlogN : 1 ≤ Real.log N := one_le_log_of_three_le (by linarith only [hNr])
  have hS1 : 1 ≤ S := hlogN.trans hS
  have hS2 : 0 < S ^ 2 := by positivity
  intro ℓ t u v hu hv huv hℓ1 hl3 ht γ hγ hcost z hz
  -- the slope is small
  obtain ⟨htε, htlog⟩ := hN₁ N hN1 ‖t - M.t₀‖ (norm_nonneg _) ht
  have ht1 : ‖t - M.t₀‖ ≤ 1 := htε.trans (min_le_right _ _)
  have htε₀ : ‖t - M.t₀‖ ≤ ε₀ :=
    htε.trans ((min_le_left _ _).trans (half_le_self hε₀.le))
  have htT : ‖t‖ ≤ T := by
    calc ‖t‖ = ‖(t - M.t₀) + M.t₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖t - M.t₀‖ + ‖M.t₀‖ := norm_add_le _ _
      _ ≤ T := by rw [hTdef]; linarith only [ht1, ht₀]
  -- the displacement
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hsl : ‖slopeVec t‖ ≤ 1 + T := norm_slopeVec_le htT
  have hvu : ‖point v - point u‖ ≤ 3 * (1 + T) * N := by
    rw [huv, norm_smul, Real.norm_eq_abs, abs_of_pos hℓpos]
    calc (ℓ : ℝ) * ‖slopeVec t‖ ≤ (3 * N) * (1 + T) :=
          mul_le_mul hl3 hsl (norm_nonneg _) (by positivity)
      _ = 3 * (1 + T) * N := by ring
  -- the box
  have hbox : ∀ x : Vertex m, InBox ((N : ℝ) ^ 2) x → InBox (2 * (N : ℝ) ^ 2) x := fun x hx =>
    inBox_mono (by linarith only [sq_nonneg (N : ℝ)]) hx
  have hzu : ‖point z - point u‖ ≤ γ.length := norm_point_sub_le_length_of_mem γ hz
  by_cases hSN : S ^ 2 ≤ N
  · -- the path stays in the box `[−2N², 2N²]^d`, where the passage time concentrates
    have hΛ : (γ.length : ℝ) ≤ Cv * N :=
      hω.length_le_mul hCg.le hcg hSN (hbox u hu) (hbox v hv) hvu γ hγ hcost
    have hsupp_box : ∀ y ∈ γ.support, y ∈ {x : Vertex m | InBox (2 * (N : ℝ) ^ 2) x} := by
      intro y hy
      refine inBox_mono ?_ (inBox_of_mem_support γ hu hy)
      have := mul_le_mul_of_nonneg_right hNCv hNpos.le
      nlinarith only [this, hΛ]
    have hconc : ConcentrationOn ω M.μ.1 {x : Vertex m | InBox (2 * (N : ℝ) ^ 2) x} Cg S :=
      fun x hx y hy => hω.passageTime_sub x y hx hy
    have hL1 : (1 : ℝ) ≤ 2 * Real.log N := by linarith only [hlogN]
    have hsmall : ‖t - M.t₀‖ ^ (M.δ / 2) * (2 * Real.log N) ≤ ε₀ := by
      have h1 : ‖t - M.t₀‖ ^ (M.δ / 2) * Real.log N ≤ ε₀ / 2 := htlog.trans (min_le_left _ _)
      linarith only [h1]
    have hvuL : ‖point v - point u‖ ≤ S ^ 2 * Real.exp (2 * Real.log N) := by
      rw [show 2 * Real.log N = Real.log ((N : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
      have hS21 : (1 : ℝ) ≤ S ^ 2 := one_le_pow₀ hS1
      have h6 : 3 * (1 + T) * (N : ℝ) ≤ (N : ℝ) ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hNT hNpos.le
      have h7 : (N : ℝ) ^ 2 ≤ S ^ 2 * (N : ℝ) ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) hS21
      linarith only [hvu, h6, h7]
    obtain ⟨h1, h2⟩ := hcone M.t₀ (hsupp M hM hfit) ω _ S (2 * Real.log N) hS1 hL1 hconc
      u v γ hcost hsupp_box ℓ t hℓpos huv htT htε₀ hsmall hvuL z hz
    have hK2 : K * S ^ 2 ≤ C * S ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hC2K, hK]) hS2.le
    have hbound : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        K * (x + y * (2 * Real.log N)) ≤ C * (x + y * Real.log N) := by
      intro x y hx hy
      have hlog0 : 0 ≤ Real.log N := by linarith only [hlogN]
      have : K * (x + y * (2 * Real.log N)) ≤ 2 * K * (x + y * Real.log N) := by
        linarith only [mul_nonneg hK.le hx]
      exact this.trans (mul_le_mul_of_nonneg_right hC2K (by positivity))
    exact ⟨fun hCa => (h1 (hK2.trans hCa)).trans (hbound _ _ (by positivity) (by positivity)),
      fun hCa => (h2 (hK2.trans hCa)).trans (hbound _ _ (by positivity) (by positivity))⟩
  · -- every vertex is within `(Cv + 3(1 + T) + 1) S²` of both endpoints: the lemma is vacuous
    push Not at hSN
    have hvuS : ‖point v - point u‖ ≤ 3 * (1 + T) * S ^ 2 :=
      hvu.trans (mul_le_mul_of_nonneg_left hSN.le (by positivity))
    have hΛ : (γ.length : ℝ) ≤ Cv * S ^ 2 :=
      hω.length_le_mul hCg.le hcg le_rfl (hbox u hu) (hbox v hv) hvuS γ hγ hcost
    have hzv : ‖point v - point z‖ ≤ 3 * (1 + T) * S ^ 2 + Cv * S ^ 2 := by
      have := norm_sub_le_norm_sub_add_norm_sub (point v) (point u) (point z)
      rw [norm_sub_rev (point u) (point z)] at this
      linarith only [this, hvuS, hzu, hΛ]
    have hCS := mul_le_mul_of_nonneg_right hCv7 hS2.le
    have e : (Cv + 3 * (1 + T) + 1) * S ^ 2 = Cv * S ^ 2 + 3 * (1 + T) * S ^ 2 + S ^ 2 := by ring
    have hTS : 0 ≤ 3 * (1 + T) * S ^ 2 := by positivity
    exact ⟨fun hCa => absurd hCa (not_le.2 (by linarith only [hzv, hCS, e, hS2])),
      fun hCa => absurd hCa (not_le.2 (by linarith only [hzu, hΛ, hCS, e, hS2, hTS]))⟩

end CurvatureVariance.Paper.Proofs.Geometry
