/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SlabsFirstPart

/-!
# Lemma `lem:slabs` (2), and Lemma `lem:slabs`

`slabsStatement_of`: the contract `SlabsStatement`, Lemma `lem:slabs` and its proof, from Lemma
`lem:cone`.

The proof of Lemma `lem:slabs` (2), along a geodesic, which
exists by `IsGood.exists_isGeodesic`:

* the geodesic has at most `C(N + S²)` edges, so it lies in `[−N², N²]^d`;
* `increment_of_coneAt`: `v − x_i = (M − i) n (1, t_i')`; the cone bound at `x_i` gives `t_i'`, and
  Lemma `lem:cone` with `t_i'` in place of `t`, for the part of the geodesic from `x_i`, at its
  vertex `x_{i+1}`, gives `|x_{i+1} − x_i − n(1, t)| ≤ n^{3/4+δ/100}/16`;
* the `x_i` form a chain, and by (1) each piece has passage time at least
  `T^{(i)}(x_{i−1}, x_i) − C S²`, so `F ≤ T(u, v) + C M S²`.

The first hits `x_i` come in order along the geodesic (`exists_hitIndex`), and the smallness of the
cone bounds at distance `n` is `eventually_cone_small`.

The paper's `M` is `Ms`, since `M` is the model.
-/

@[expose] public section

open InnerProductGeometry
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-- `n ≥ N^{1/2}` gives `n^{δ/100−1/4} ≤ N^{−1/9}`, for `δ ≤ 1`: the paper's
`3n^{δ/100−1/4} ≤ 3N^{−1/9}`. -/
theorem rpow_slope_le_rpow_neg {δ : ℝ} (hδ : δ ≤ 1) {n N : ℝ} (hN : 1 ≤ N)
    (hn : Real.sqrt N ≤ n) : n ^ (δ / 100 - 1 / 4) ≤ N ^ (-(1 : ℝ) / 9) :=
  (rpow_le_rpow_neg_of_sqrt_le hδ (by linarith only [hN]) hn).trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hδ]))

section Increments

variable {M : Model m} {C S ε : ℝ} {N : ℕ} {ω : Config m}

/-- **The increment between consecutive first hits** (the proof of Lemma `lem:slabs` (2)). For a
geodesic `γ` from `u` to `v = u + ℓ (1, t)`, `ℓ = M n ≤ 3N`, and two of its vertices `x_i = γ_a`,
`x_{i+1} = γ_b`, `a ≤ b`, on the hyperplanes `{x₁ = u₁ + i n}` and `{x₁ = u₁ + (i + 1) n}`, `i < M`,
with `x_i ∈ [−N², N²]^d`, the conclusion of Lemma `lem:cone` and the smallness of the cone bounds at
the scale `n` (`hsmall`, with `κ ε ≤ 1` for `κ = slopeFactor (‖t₀‖ + 1)`) give
`‖(x_{i+1} − x_i)⊥ − n t‖ ≤ 2 κ ε n · n^{δ/100−1/4}`. -/
theorem increment_of_coneAt (hcone : ConeAt M C S N ω) (hε0 : 0 < ε)
    (hε : slopeFactor (‖M.t₀‖ + 1) * ε ≤ 1) {n Ms ℓ : ℕ} (hn0 : (0 : ℝ) < n) (hℓ : ℓ = Ms * n)
    (hℓN : (ℓ : ℝ) ≤ 3 * N) (hρ : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 1 / 3)
    (hρN : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ (N : ℝ) ^ (-(1 : ℝ) / 9)) (hCS : C * S ^ 2 ≤ n)
    (hsmall : ∀ r : ℝ, (n : ℝ) ≤ r → ∀ x : ℝ, 0 ≤ x → x ≤ 3 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) →
      C * (S ^ ((1 : ℝ) / 2) * r ^ (-(1 : ℝ) / 4) + x ^ (1 + M.δ / 2) * Real.log N) ≤
        ε * (n : ℝ) ^ (M.δ / 100 - 1 / 4))
    {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m}
    (huv : point v - point u = (ℓ : ℝ) • slopeVec t)
    (ht : ‖t - M.t₀‖ ≤ 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4))
    (hu : InBox ((N : ℝ) ^ 2) u) (hv : InBox ((N : ℝ) ^ 2) v)
    {γ : (latticeGraph m).Walk u v} (hγ : IsGeodesic ω γ) {i a b : ℕ} (hiK : i < Ms)
    (hab : a ≤ b) (ha : (γ.getVert a).1 = u.1 + i * n)
    (hb : (γ.getVert b).1 = u.1 + (i + 1 : ℕ) * n) (hz : InBox ((N : ℝ) ^ 2) (γ.getVert a)) :
    ‖(point (γ.getVert b) - point (γ.getVert a)).snd - (n : ℝ) • t‖ ≤
      2 * slopeFactor (‖M.t₀‖ + 1) * ε * ((n : ℝ) * (n : ℝ) ^ (M.δ / 100 - 1 / 4)) := by
  set ρ := (n : ℝ) ^ (M.δ / 100 - 1 / 4) with hρdef
  set z := γ.getVert a with hzdef
  set y := γ.getVert b with hydef
  set T := ‖M.t₀‖ + 1 with hTdef
  set κ := slopeFactor T with hκdef
  have hT : 0 ≤ T := by positivity
  have ht0 : 0 ≤ ‖M.t₀‖ := norm_nonneg _
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hn0 _
  have hn1 : 0 < n := by exact_mod_cast hn0
  have hερ : ε * ρ ≤ aperture T := mul_le_aperture hT hε0.le hε hρ
  have hκερ : κ * (ε * ρ) ≤ ρ := by
    calc κ * (ε * ρ) = (κ * ε) * ρ := by ring
      _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hε hρ0.le
      _ = ρ := one_mul ρ
  have htT : ‖t‖ ≤ T := by
    calc ‖t‖ = ‖(t - M.t₀) + M.t₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖t - M.t₀‖ + ‖M.t₀‖ := norm_add_le _ _
      _ ≤ T := by rw [hTdef]; linarith only [ht, hρ]
  have hv1 : v.1 = u.1 + Ms * n := by rw [fst_eq_of_point_sub huv, hℓ]; push_cast; ring
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have hcost : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2 := by
    rw [passageTimeReal, hγ.2]
    linarith only [hS2]
  -- `v − x_i = (M − i) n (1, t_i')`, and the cone bound at `x_i`
  set ℓ' : ℕ := (Ms - i) * n with hℓ'def
  have hKi : ((Ms - i : ℕ) : ℝ) = (Ms : ℝ) - i := by rw [Nat.cast_sub hiK.le]
  have hℓ'n : n ≤ ℓ' := Nat.le_mul_of_pos_left n (by omega)
  have hℓ'ℓ : ℓ' ≤ ℓ := by rw [hℓ]; exact Nat.mul_le_mul_right n (Nat.sub_le Ms i)
  have hℓ'N : (ℓ' : ℝ) ≤ 3 * N := le_trans (by exact_mod_cast hℓ'ℓ) hℓN
  set W := point v - point z with hWdef
  have hWfst : W.fst = ℓ' := by
    have e : W.fst = (v.1 : ℝ) - z.1 := by simp [hWdef]
    rw [e, hv1, ha, hℓ'def]
    push_cast
    rw [hKi]
    ring
  have hWn : (n : ℝ) ≤ ‖W‖ := by
    have := abs_fst_le_norm W
    rw [hWfst, abs_of_nonneg (Nat.cast_nonneg _)] at this
    exact le_trans (by exact_mod_cast hℓ'n) this
  have htN : ‖t - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) := by linarith only [ht, hρN, hρ0]
  have hcone1 := (hcone ℓ t u v hu hv huv (hn1.trans_le (hℓ'n.trans hℓ'ℓ)) hℓN htN γ hγ.1 hcost z
    (γ.getVert_mem_support a)).1 (hCS.trans hWn)
  have hθ0 : angle W (slopeVec t) ≤ ε * ρ :=
    hcone1.trans (hsmall ‖W‖ hWn ‖t - M.t₀‖ (norm_nonneg _) (by linarith only [ht, hρ0]))
  obtain ⟨-, hsl0⟩ := fst_pos_and_norm_slope_sub_le htT hερ hθ0
  obtain ⟨t', ht'def⟩ : ∃ t' : EuclideanSpace ℝ (Fin m), t' = W.fst⁻¹ • W.snd := ⟨_, rfl⟩
  rw [← ht'def] at hsl0
  have ht'ρ : ‖t' - M.t₀‖ ≤ 3 * ρ := by
    calc ‖t' - M.t₀‖ = ‖(t' - t) + (t - M.t₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖t' - t‖ + ‖t - M.t₀‖ := norm_add_le _ _
      _ ≤ 3 * ρ := by linarith only [hsl0, hκερ, ht]
  have ht'T : ‖t'‖ ≤ T := by
    calc ‖t'‖ = ‖(t' - M.t₀) + M.t₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖t' - M.t₀‖ + ‖M.t₀‖ := norm_add_le _ _
      _ ≤ T := by rw [hTdef]; linarith only [ht'ρ, hρ]
  have hW : point v - point z = (ℓ' : ℝ) • slopeVec t' := by
    have hℓ'pos : (0 : ℝ) < ℓ' := hn0.trans_le (by exact_mod_cast hℓ'n)
    have hWne : W.fst ≠ 0 := by rw [hWfst]; exact hℓ'pos.ne'
    have e := eq_smul_slopeVec W hWne
    rw [← ht'def, hWfst] at e
    exact e
  -- Lemma `lem:cone` with `t_i'` in place of `t`, for the part of `γ` from `x_i`, at `x_{i+1}`
  have hy : y ∈ (γ.drop a).support := by
    have e : (γ.drop a).getVert (b - a) = y := by
      rw [SimpleGraph.Walk.drop_getVert, Nat.add_sub_cancel' hab]
    rw [← e]
    exact SimpleGraph.Walk.getVert_mem_support _ _
  have hcost' : (walkCost ω (γ.drop a) : ℝ) ≤ passageTimeReal ω z v + S ^ 2 :=
    walkCost_drop_le hcost a
  have ht'N : ‖t' - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) := by linarith only [ht'ρ, hρN]
  set Y := point y - point z with hYdef
  have hYfst : Y.fst = n := by
    have e : Y.fst = (y.1 : ℝ) - z.1 := by simp [hYdef]
    rw [e, hb, ha]
    push_cast
    ring
  have hYn : (n : ℝ) ≤ ‖Y‖ := by
    have := abs_fst_le_norm Y
    rwa [hYfst, abs_of_nonneg (Nat.cast_nonneg _)] at this
  have hcone2 := (hcone ℓ' t' z v hz hv hW (hn1.trans_le hℓ'n) hℓ'N ht'N (γ.drop a) (hγ.1.drop a)
    hcost' y hy).2 (hCS.trans hYn)
  have hθ1 : angle Y (slopeVec t') ≤ ε * ρ :=
    hcone2.trans (hsmall ‖Y‖ hYn ‖t' - M.t₀‖ (norm_nonneg _) ht'ρ)
  obtain ⟨-, hsl1⟩ := fst_pos_and_norm_slope_sub_le ht'T hερ hθ1
  calc ‖Y.snd - (n : ℝ) • t‖ ≤ n * (κ * (ε * ρ) + κ * (ε * ρ)) :=
        norm_snd_sub_smul_le hYfst hn0 hsl1 hsl0
    _ = 2 * κ * ε * ((n : ℝ) * ρ) := by ring

/-- The first hits of a geodesic come in order along it, and their increments are bounded
(`increment_of_coneAt`). -/
theorem hits_of_geodesic (hcone : ConeAt M C S N ω) (hε0 : 0 < ε)
    (hε : slopeFactor (‖M.t₀‖ + 1) * ε ≤ 1) {n Ms ℓ : ℕ} (hn0 : (0 : ℝ) < n) (hMs : 1 ≤ Ms)
    (hℓ : ℓ = Ms * n) (hℓN : (ℓ : ℝ) ≤ 3 * N) (hρ : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ 1 / 3)
    (hρN : (n : ℝ) ^ (M.δ / 100 - 1 / 4) ≤ (N : ℝ) ^ (-(1 : ℝ) / 9)) (hCS : C * S ^ 2 ≤ n)
    (hsmall : ∀ r : ℝ, (n : ℝ) ≤ r → ∀ x : ℝ, 0 ≤ x → x ≤ 3 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) →
      C * (S ^ ((1 : ℝ) / 2) * r ^ (-(1 : ℝ) / 4) + x ^ (1 + M.δ / 2) * Real.log N) ≤
        ε * (n : ℝ) ^ (M.δ / 100 - 1 / 4))
    {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m}
    (huv : point v - point u = (ℓ : ℝ) • slopeVec t)
    (ht : ‖t - M.t₀‖ ≤ 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4))
    (hu : InBox ((N : ℝ) ^ 2) u) (hv : InBox ((N : ℝ) ^ 2) v)
    {γ : (latticeGraph m).Walk u v} (hγ : IsGeodesic ω γ)
    (hbox : ∀ z ∈ γ.support, InBox ((N : ℝ) ^ 2) z) :
    ∃ k : ℕ → ℕ, (∀ i < Ms, k i ≤ k (i + 1)) ∧
      (∀ i ≤ Ms, hitPoint γ n Ms i = γ.getVert (k i) ∧ (γ.getVert (k i)).1 = u.1 + i * n) ∧
      ∀ i < Ms, ‖(point (γ.getVert (k (i + 1))) - point (γ.getVert (k i))).snd - (n : ℝ) • t‖ ≤
        2 * slopeFactor (‖M.t₀‖ + 1) * ε * (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := by
  have hv1 : v.1 = u.1 + Ms * n := by rw [fst_eq_of_point_sub huv, hℓ]; push_cast; ring
  obtain ⟨k, -, -, hkmono, hkval⟩ := exists_hitIndex γ hMs hv1
  refine ⟨k, hkmono, hkval, fun i hi => ?_⟩
  rw [← mul_rpow_slope hn0]
  exact increment_of_coneAt hcone hε0 hε hn0 hℓ hℓN hρ hρN hCS hsmall huv ht hu hv hγ hi
    (hkmono i hi) (hkval i hi.le).2 (hkval (i + 1) hi).2 (hbox _ (γ.getVert_mem_support _))

/-- The first hits form a chain: the increments bounded by `n^{3/4+δ/100}/16` are the admissibility
of the tuple of the transverse parts. -/
theorem isAdmissibleTuple_of_hits {n Ms : ℕ} {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m}
    {γ : (latticeGraph m).Walk u v} (hMs : 1 ≤ Ms) {k : ℕ → ℕ} {c : ℝ} (hc : c ≤ 1 / 16)
    (hX : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100))
    (hkval : ∀ i ≤ Ms, hitPoint γ n Ms i = γ.getVert (k i))
    (hinc : ∀ i < Ms,
      ‖(point (γ.getVert (k (i + 1))) - point (γ.getVert (k i))).snd - (n : ℝ) • t‖ ≤
        c * (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) :
    IsAdmissibleTuple M n Ms t u v fun i => (hitPoint γ n Ms i).2 := by
  refine ⟨by simp [hitPoint], by simp [hitPoint, Nat.pos_iff_ne_zero.1 hMs], fun i => ?_⟩
  have hi : (i : ℕ) < Ms := i.2
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [hkval i hi.le, hkval (i + 1) hi, ← point_sub_snd]
  refine (hinc i hi).trans ?_
  have := mul_le_mul_of_nonneg_right hc hX
  linarith only [this]

end Increments

/-- **Lemma `lem:slabs` (2)**, from `IsGood`, the conclusion of Lemma
`lem:cone` and (1), at one constant `C`. The threshold depends on `bd`, `C_g, c_g` and `C`. -/
theorem slabTwo_of (bd : Bounds m) (hbd : bd.Valid) {Cg cg : ℝ} (hCg : 0 < Cg) (hcg : 0 < cg)
    {C : ℝ} (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ S : ℝ, Real.log N ≤ S → ∀ ω : Config m, IsGood M Cg cg N S ω →
        ConeAt M C S N ω → SlabOneAt M C S N ω →
      ∀ (ℓ : ℕ) (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m),
        point v - point u = (ℓ : ℝ) • slopeVec t → (ℓ : ℝ) ≤ 3 * N →
      ∀ Ms n : ℕ, ℓ = Ms * n → 1 ≤ Ms → Real.sqrt N ≤ n →
        ‖t - M.t₀‖ ≤ 2 * (n : ℝ) ^ (M.δ / 100 - 1 / 4) → S ≤ (N : ℝ) ^ (M.δ / 1000) →
        InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) u → InBox (3 * (1 + ‖M.t₀‖) * (N : ℝ)) v →
        (∀ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ →
          (∀ i : ℕ, i ≤ Ms → (hitPoint γ n Ms i).1 = u.1 + (i : ℤ) * n) ∧
            IsAdmissibleTuple M n Ms t u v fun i => (hitPoint γ n Ms i).2) ∧
        (passageTime ω u v : ℝ≥0∞) ≤ slabMin M ω n Ms t u v ∧
          slabMin M ω n Ms t u v ≤
            (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C * Ms * S ^ 2) := by
  have hT0 := hbd.T_nonneg
  set T := bd.T + 1 with hTdef
  set κ := slopeFactor T with hκdef
  have hκ : 0 < κ := slopeFactor_pos (by linarith only [hT0, hTdef])
  set ε := 1 / 16 / (2 * κ) with hεdef
  have hε0 : 0 < ε := by positivity
  have h2κε : 2 * κ * ε = 1 / 16 := by rw [hεdef]; field_simp
  obtain ⟨N₀, hN₀⟩ := eventually_cone_small hbd.law.delta_pos hbd.law.delta_le_one hC hε0
  set Cv := goodLen Cg cg T with hCv
  have hCv0 : 0 ≤ Cv := goodLen_nonneg hCg.le
  refine ⟨max N₀ ⌈3 * (1 + T) + Cv⌉₊, fun M hM hfit N hN S hS ω hω hcone hone => ?_⟩
  -- the threshold chosen at the law of `bd`, and the slope factor of the model
  rw [← hfit.δ_eq] at hN₀
  have ht₀ := hfit.t₀_le
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hκM : slopeFactor (‖M.t₀‖ + 1) ≤ κ :=
    slopeFactor_le_slopeFactor (by positivity) (by linarith only [ht₀, hTdef])
  have hεM : 2 * slopeFactor (‖M.t₀‖ + 1) * ε ≤ 1 / 16 := by
    rw [← h2κε]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκM zero_le_two) hε0.le
  have hε5M : slopeFactor (‖M.t₀‖ + 1) * ε ≤ 1 := by linarith only [hεM]
  obtain ⟨hN6, hNn⟩ := hN₀ N (le_trans (le_max_left _ _) hN)
  have hNT : 3 * (1 + T) + Cv ≤ (N : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_max_right _ _) hN)
  intro ℓ t u v huv hl3 Ms n hℓ hMs hn ht hSN hu hv
  obtain ⟨hρ, hSn⟩ := hNn n hn
  obtain ⟨hCS, hsmall⟩ := hSn S hS hSN
  have hN0 : (0 : ℝ) < N := by linarith only [hN6]
  have hN1 : (1 : ℝ) ≤ N := by linarith only [hN6]
  have hn0 : (0 : ℝ) < n := (Real.sqrt_pos.2 hN0).trans_le hn
  have hn1 : 0 < n := by exact_mod_cast hn0
  have hnℓ : n ≤ ℓ := by rw [hℓ]; exact Nat.le_mul_of_pos_left n hMs
  have hℓ1 : 1 ≤ ℓ := hn1.trans_le hnℓ
  have hρN := rpow_slope_le_rpow_neg hδ1 hN1 hn
  have hρ0 : 0 < (n : ℝ) ^ (M.δ / 100 - 1 / 4) := Real.rpow_pos_of_pos hn0 _
  have hX0 : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) := Real.rpow_nonneg hn0.le _
  have hv1 : v.1 = u.1 + Ms * n := by rw [fst_eq_of_point_sub huv, hℓ]; push_cast; ring
  have hlogN : 1 ≤ Real.log N := one_le_log_of_three_le (by linarith only [hN6])
  have hS1 : 1 ≤ S := hlogN.trans hS
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have hS2N : S ^ 2 ≤ N := by
    calc S ^ 2 ≤ ((N : ℝ) ^ (M.δ / 1000)) ^ 2 :=
          pow_le_pow_left₀ (by linarith only [hS1]) hSN 2
      _ = (N : ℝ) ^ (M.δ / 500) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          ring_nf
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδ1])
      _ = N := Real.rpow_one _
  -- the slope `t` and the endpoints
  have htT : ‖t‖ ≤ T := by
    calc ‖t‖ = ‖(t - M.t₀) + M.t₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖t - M.t₀‖ + ‖M.t₀‖ := norm_add_le _ _
      _ ≤ T := by rw [hTdef]; linarith only [ht, hρ, ht₀]
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hvu : ‖point v - point u‖ ≤ 3 * (1 + T) * N := by
    rw [huv, norm_smul, Real.norm_eq_abs, abs_of_pos hℓpos]
    calc (ℓ : ℝ) * ‖slopeVec t‖ ≤ (3 * N) * (1 + T) :=
          mul_le_mul hl3 (norm_slopeVec_le htT) (norm_nonneg _)
            (by linarith only [hT0, hTdef, hN0])
      _ = 3 * (1 + T) * N := by ring
  have hT1 : 0 ≤ 1 + T := by linarith only [hT0, hTdef]
  have hbox0 : 3 * (1 + ‖M.t₀‖) * (N : ℝ) + Cv * N ≤ (N : ℝ) ^ 2 := by
    have e1 : 3 * (1 + ‖M.t₀‖) ≤ 3 * (1 + T) := by linarith only [ht₀, hTdef]
    have e2 : (3 * (1 + ‖M.t₀‖) + Cv) * N ≤ N * N :=
      mul_le_mul_of_nonneg_right (by linarith only [e1, hNT]) hN0.le
    rw [sq]
    linarith only [e2]
  have hbox1 : 3 * (1 + ‖M.t₀‖) * (N : ℝ) ≤ (N : ℝ) ^ 2 := by
    have : 0 ≤ Cv * N := by positivity
    linarith only [hbox0, this]
  have hu2 : InBox ((N : ℝ) ^ 2) u := inBox_mono hbox1 hu
  have hv2 : InBox ((N : ℝ) ^ 2) v := inBox_mono hbox1 hv
  have hbox : ∀ x : Vertex m, InBox ((N : ℝ) ^ 2) x → InBox (2 * (N : ℝ) ^ 2) x := fun x hx =>
    inBox_mono (by linarith only [sq_nonneg (N : ℝ)]) hx
  -- the geodesic has at most `C(N + S²)` edges, so it lies in `[−N², N²]^d`
  have hconf : ∀ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ →
      ∀ z ∈ γ.support, InBox ((N : ℝ) ^ 2) z := by
    intro γ hγ z hz
    have hcost : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2 := by
      rw [passageTimeReal, hγ.2]
      linarith only [hS2]
    have hlen := hω.length_le_mul hCg.le hcg hS2N (hbox u hu2) (hbox v hv2) hvu γ hγ.1 hcost
    exact inBox_mono (by linarith only [hbox0, hlen]) (inBox_of_mem_support γ hu hz)
  have hhits : ∀ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ → _ := fun γ hγ =>
    hits_of_geodesic hcone hε0 hε5M hn0 hMs hℓ hl3 hρ hρN hCS hsmall huv ht hu2 hv2 hγ (hconf γ hγ)
  refine ⟨fun γ hγ => ?_, passageTime_le_slabMin M ω t hv1, ?_⟩
  · -- the first hits form a chain
    obtain ⟨k, -, hkval, hinc⟩ := hhits γ hγ
    refine ⟨fun i hi => ?_, isAdmissibleTuple_of_hits hMs hεM hX0 (fun i hi => (hkval i hi).1) hinc⟩
    rw [(hkval i hi).1]
    exact (hkval i hi).2
  · -- `F ≤ T(u, v) + C M S²`, along a geodesic
    obtain ⟨γ, hγ⟩ := hω.exists_isGeodesic hcg (hbox u hu2) v
    obtain ⟨k, hkmono, hkval, hinc⟩ := hhits γ hγ
    have hadm : IsAdmissibleTuple M n Ms t u v fun i => (hitPoint γ n Ms i).2 :=
      isAdmissibleTuple_of_hits hMs hεM hX0 (fun i hi => (hkval i hi).1) hinc
    set y : Fin (Ms + 1) → Fin m → ℤ := fun i => (hitPoint γ n Ms i).2 with hydef
    have hyP : ∀ i : Fin (Ms + 1), tuplePoint u n y i = γ.getVert (k i) := by
      intro i
      obtain ⟨e0, f0⟩ := hkval i (Nat.lt_succ_iff.1 i.2)
      refine Prod.ext ?_ ?_
      · simp only [tuplePoint]
        rw [f0]
      · simp only [tuplePoint, hydef]
        rw [e0]
    -- by (1), each piece has passage time at least `T^{(i)}(x_{i−1}, x_i) − C S²`
    have hD : ∀ i : Fin Ms, slabTime ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
        (tuplePoint u n y i.castSucc) (tuplePoint u n y i.succ) ≤
          passageTime ω (γ.getVert (k i)) (γ.getVert (k ((i : ℕ) + 1))) +
            ENNReal.ofReal (C * S ^ 2) := by
      intro i
      have hi : (i : ℕ) < Ms := i.2
      rw [hyP, hyP, Fin.val_castSucc, Fin.val_succ]
      obtain ⟨-, fa⟩ := hkval i hi.le
      obtain ⟨-, fb⟩ := hkval (i + 1) hi
      have ha := hconf γ hγ _ (γ.getVert_mem_support (k i))
      have hb := hconf γ hγ _ (γ.getVert_mem_support (k ((i : ℕ) + 1)))
      set a := γ.getVert (k i) with hadef
      set b := γ.getVert (k ((i : ℕ) + 1)) with hbdef
      have hpa : u.1 + (i : ℤ) * n = a.1 := fa.symm
      have hpb : u.1 + ((i : ℤ) + 1) * n = b.1 := by rw [fb]; push_cast; ring
      rw [hpa, hpb]
      set w := point b - point a with hwdef
      have hwfst : w.fst = n := by
        have e : w.fst = (b.1 : ℝ) - a.1 := by simp [hwdef]
        rw [e, fb, fa]
        push_cast
        ring
      have hw : point b - point a = (n : ℝ) • slopeVec ((n : ℝ)⁻¹ • w.snd) := by
        have := eq_smul_slopeVec w (by rw [hwfst]; exact hn0.ne')
        rwa [hwfst] at this
      have hslope : ‖(n : ℝ)⁻¹ • w.snd - t‖ ≤ (n : ℝ) ^ (M.δ / 100 - 1 / 4) := by
        have h1 := hinc i hi
        rw [← mul_rpow_slope hn0] at h1
        have e : (n : ℝ)⁻¹ • w.snd - t = (n : ℝ)⁻¹ • (w.snd - (n : ℝ) • t) := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul]
        rw [e, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn0, inv_mul_le_iff₀ hn0]
        have hρ0' : 0 ≤ (n : ℝ) * (n : ℝ) ^ (M.δ / 100 - 1 / 4) :=
          mul_nonneg hn0.le (Real.rpow_nonneg hn0.le _)
        have h2 := mul_le_mul_of_nonneg_right hεM hρ0'
        linarith only [h1, h2, hρ0']
      have hslope' : ‖(n : ℝ)⁻¹ • w.snd - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) := by
        have h1 : ‖(n : ℝ)⁻¹ • w.snd - M.t₀‖ ≤ ‖(n : ℝ)⁻¹ • w.snd - t‖ + ‖t - M.t₀‖ := by
          calc ‖(n : ℝ)⁻¹ • w.snd - M.t₀‖ = ‖((n : ℝ)⁻¹ • w.snd - t) + (t - M.t₀)‖ := by
                rw [sub_add_sub_cancel]
            _ ≤ _ := norm_add_le _ _
        linarith only [h1, hslope, ht, hρN]
      have hnN : (n : ℝ) ≤ 3 * N := le_trans (by exact_mod_cast hnℓ) hl3
      exact hone n _ a b hw hn1 hnN hslope' ha hb hCS
    have hKC : (Ms : ℝ≥0∞) * ENNReal.ofReal (C * S ^ 2) = ENNReal.ofReal (C * Ms * S ^ 2) := by
      rw [show C * Ms * S ^ 2 = Ms * (C * S ^ 2) by ring,
        ENNReal.ofReal_mul (Nat.cast_nonneg Ms), ENNReal.ofReal_natCast]
    calc slabMin M ω n Ms t u v ≤ tupleCost ω u n y := iInf₂_le y hadm
      _ ≤ walkCost ω γ + Ms * ENNReal.ofReal (C * S ^ 2) := tupleCost_le_walkCost γ hkmono hD
      _ = (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C * Ms * S ^ 2) := by rw [hγ.2, hKC]

/-- **Lemma `lem:slabs`**, with its proof, from Lemma `lem:cone`.
The lower bounds are `T_P ≥ T` and the triangle inequality. -/
theorem slabsStatement_of (hcone : ConeStatement m) : SlabsStatement m := by
  intro bd hbd Cg cg hCg hcg
  obtain ⟨C₁, hC₁, N₁, hc⟩ := hcone bd hbd Cg cg hCg hcg
  obtain ⟨C₂, hC₂, N₂, h1⟩ := slabOneAt_of bd hbd hCg hcg hC₁
  set C := max C₁ C₂ with hCdef
  have hC1 : C₁ ≤ C := le_max_left _ _
  have hC2 : C₂ ≤ C := le_max_right _ _
  have hC0 : 0 < C := lt_of_lt_of_le hC₁ hC1
  obtain ⟨N₃, h2⟩ := slabTwo_of bd hbd hCg hcg hC0
  refine ⟨C, hC0, max (max N₁ N₂) (max N₃ 1),
    fun M hM hfit N hN S hS ω hω ℓ t u v huv hℓ hl3 ht => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hN1' : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hS0 : 0 ≤ S := le_trans (Real.log_nonneg (by exact_mod_cast hN1')) hS
  have hcone₁ := hc M hM hfit N hN1 S hS ω hω
  have hcone' : ConeAt M C S N ω := ConeAt.mono hS0 hN1' hC1 hcone₁
  have hone' : SlabOneAt M C S N ω :=
    SlabOneAt.mono hC2 (h1 M hM hfit N hN2 S hS ω hω hcone₁)
  refine ⟨fun hu hv hCℓ => ⟨passageTime_le_slabTime ω _ _ u v,
    hone' ℓ t u v huv hℓ hl3 ht hu hv hCℓ⟩, fun Ms n hMs hMs1 hn ht' hSN hu hv => ?_⟩
  exact h2 M hM hfit N hN3 S hS ω hω hcone' hone' ℓ t u v huv hl3 Ms n hMs hMs1 hn ht' hSN hu hv

end CurvatureVariance.Paper.Proofs.Geometry
