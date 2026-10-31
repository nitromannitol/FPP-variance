/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.Cone
public import CurvatureVariance.Paper.Proofs.Geometry.Slabs
public import CurvatureVariance.Infra.Geodesics.Basic

/-!
# Lemma `lem:slabs` (1)

The first part of the proof of Lemma `lem:slabs` (the lower bounds and (1)), on one configuration
with `IsGood` and the conclusion of Lemma `lem:cone` (`ConeAt`).

* `IsGood.exists_isGeodesic`: on `IsGood`, geodesics from the box exist, by Lemma `lem:good` (3)
  (only finitely many self-avoiding paths are cheap enough).
* `slabTime_add_le`: the triangle inequality for `T_P`.
* `slabTime_le_of_interior_slabTime`: the surgery, with the joins at cost `T_P`.
* `slabOneAt_of`: Lemma `lem:slabs` (1), along a geodesic, as in the paper.

Readings. The aperture is `aperture T = 1/(2(1 + T))`, `T = bd.T + 1`, for the paper's
`1/(8d^{1/2})`: `Bounds.T` is general (`Contracts.SlabsStatement`), and `fst_pos_of_coneBound` is
the paper's sentence on positive first coordinates. The paper joins `u` and `v` to the last vertex
near `u` and the first vertex near `v` afterwards; the Lean joins them to the neighbours of these
two vertices on the part between them, whose vertices are strictly between the faces.
-/

@[expose] public section

open InnerProductGeometry
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Geodesics exist on `IsGood` -/

/-- **Geodesics exist on the good event** (recalled before Lemma `lem:good`; here by Lemma
`lem:good` (3)): from a vertex of the box, the passage time to every vertex is attained by a
self-avoiding path. -/
theorem _root_.CurvatureVariance.Paper.IsGood.exists_isGeodesic {M : Model m} {Cg cg : ℝ} {N : ℕ}
    {S : ℝ} {ω : Config m} (hω : IsGood M Cg cg N S ω) (hcg : 0 < cg) {u : Vertex m}
    (hu : InBox (2 * (N : ℝ) ^ 2) u) (v : Vertex m) :
    ∃ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ := by
  refine Infra.Geodesics.exists_isPath_walkCost_eq_passageTime hcg ?_ v
  filter_upwards [Filter.eventually_ge_atTop ⌈Cg * S ^ 2⌉₊] with n hn w γ hγ hl
  have h1 : Cg * S ^ 2 ≤ γ.length :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn.trans hl)
  have h2 := hω.le_walkCost u hu w γ hγ h1
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hl) hcg.le).trans h2

/-! ### The triangle inequality for `T_P` -/

/-- The triangle inequality for `T_P`. -/
theorem slabTime_add_le (ω : Config m) (p q : ℤ) (x y z : Vertex m) :
    slabTime ω p q x z ≤ slabTime ω p q x y + slabTime ω p q y z := by
  unfold slabTime restrictedTime
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun r => le_iInf fun hr => le_iInf fun s => le_iInf fun hs => ?_
  refine iInf₂_le_of_le (s.append r) (fun e he => ?_) ?_
  · rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    exact he.elim (hs e) (hr e)
  · rw [walkCost_append]
    push_cast
    exact le_rfl

/-- A walk strictly between the faces has its edges in the slab. -/
theorem slabTime_le_walkCost_of_interior {ω : Config m} {p q : ℤ} {a b : Vertex m}
    (r : (latticeGraph m).Walk a b) (hr : ∀ z ∈ r.support, p < z.1 ∧ z.1 < q) :
    slabTime ω p q a b ≤ walkCost ω r := by
  refine iInf₂_le r (edges_mem_slabEdges r fun δ hδ => ?_)
  have h1 := hr _ (SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ hδ)
  have h2 := hr _ (SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ hδ)
  exact ⟨⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, h2.2.le⟩, fun _ => h1⟩

/-! ### The surgery -/

/-- **The surgery** of the proof of Lemma `lem:slabs` (1): if the
vertices of `γ` at distance at least `R₀` from `u` lie after the face of `u`, those at distance at
least `R₀` from `v` lie before the face of `v`, the two balls are separated, and `T_P` from `u` to
vertices near `u` and from vertices near `v` to `v` is at most `E`, then
`T_P(u, v) ≤ cost(γ) + 2E`. The part of `γ` strictly between the faces, from its last exit from
the first ball to its next entry into the second, has its edges in the slab
(`slabTime_le_walkCost_of_interior`). -/
theorem slabTime_le_of_interior_slabTime {ω : Config m} {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) {R₀ E : ℝ} (hR₀ : 0 < R₀) (hE : 0 ≤ E)
    (hu' : ∀ z ∈ γ.support, R₀ ≤ ‖point z - point u‖ → u.1 < z.1)
    (hv' : ∀ z ∈ γ.support, R₀ ≤ ‖point v - point z‖ → z.1 < v.1)
    (hfar : 2 * R₀ + 2 ≤ ‖point v - point u‖)
    (hcu : ∀ a ∈ γ.support, ‖point a - point u‖ ≤ R₀ + 1 → u.1 < a.1 → a.1 < v.1 →
      slabTime ω u.1 v.1 u a ≤ ENNReal.ofReal E)
    (hcv : ∀ b ∈ γ.support, ‖point v - point b‖ ≤ R₀ + 1 → u.1 < b.1 → b.1 < v.1 →
      slabTime ω u.1 v.1 b v ≤ ENNReal.ofReal E) :
    slabTime ω u.1 v.1 u v ≤ (walkCost ω γ : ℝ≥0∞) + ENNReal.ofReal (2 * E) := by
  classical
  set n := γ.length with hn
  have hx0 : γ.getVert 0 = u := γ.getVert_zero
  have hxn : γ.getVert n = v := γ.getVert_length
  have hstep : ∀ i, ‖point (γ.getVert (i + 1)) - point (γ.getVert i)‖ ≤ 1 :=
    norm_point_getVert_succ_sub_le γ
  have hmem : ∀ i, γ.getVert i ∈ γ.support := fun i => γ.getVert_mem_support i
  -- the last vertex near `u`
  let Pu : ℕ → Prop := fun i => ‖point (γ.getVert i) - point u‖ < R₀
  have hPu0 : Pu 0 := by simp only [Pu, hx0, sub_self, norm_zero]; exact hR₀
  set i₀ := Nat.findGreatest Pu n with hi₀def
  have hi₀ : Pu i₀ := Nat.findGreatest_spec (Nat.zero_le n) hPu0
  have hi₀n : i₀ ≤ n := Nat.findGreatest_le n
  have hgreat : ∀ i, i₀ < i → i ≤ n → ¬ Pu i := fun i h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  have hi₀lt : i₀ < n := by
    rcases hi₀n.lt_or_eq with h | h
    · exact h
    · exfalso
      have : Pu n := h ▸ hi₀
      simp only [Pu, hxn] at this
      linarith only [this, hfar, hR₀]
  -- the first vertex after it near `v`
  have hex : ∃ j, i₀ < j ∧ ‖point v - point (γ.getVert j)‖ < R₀ :=
    ⟨n, hi₀lt, by simp only [hxn, sub_self, norm_zero]; exact hR₀⟩
  set j₀ := Nat.find hex with hj₀def
  have hj₀ := Nat.find_spec hex
  have hmin : ∀ j, j < j₀ → ¬ (i₀ < j ∧ ‖point v - point (γ.getVert j)‖ < R₀) :=
    fun j h => Nat.find_min hex h
  have hj₀n : j₀ ≤ n :=
    Nat.find_min' hex ⟨hi₀lt, by simp only [hxn, sub_self, norm_zero]; exact hR₀⟩
  have hj₀2 : i₀ + 2 ≤ j₀ := by
    by_contra h
    have hj : j₀ = i₀ + 1 := by omega
    have h1 := hstep i₀
    rw [← hj] at h1
    have htri : ‖point v - point u‖ ≤ ‖point v - point (γ.getVert j₀)‖ +
        ‖point (γ.getVert j₀) - point (γ.getVert i₀)‖ + ‖point (γ.getVert i₀) - point u‖ := by
      have e1 := norm_sub_le_norm_sub_add_norm_sub (point v) (point (γ.getVert j₀)) (point u)
      have e2 := norm_sub_le_norm_sub_add_norm_sub (point (γ.getVert j₀)) (point (γ.getVert i₀))
        (point u)
      linarith only [e1, e2]
    have e3 := hj₀.2
    have e4 : ‖point (γ.getVert i₀) - point u‖ < R₀ := hi₀
    linarith only [e3, e4, htri, h1, hfar]
  -- the vertices strictly between lie strictly between the faces
  have hint : ∀ i, i₀ + 1 ≤ i → i ≤ j₀ - 1 →
      u.1 < (γ.getVert i).1 ∧ (γ.getVert i).1 < v.1 := by
    intro i h1 h2
    have h3 : ¬ Pu i := hgreat i (by omega) (by omega)
    have h4 := hmin i (by omega)
    refine ⟨hu' _ (hmem i) (not_lt.1 h3), hv' _ (hmem i) (not_lt.1 fun h => h4 ⟨by omega, h⟩)⟩
  -- the segment
  set k := j₀ - 1 - (i₀ + 1) with hk
  set d := γ.drop (i₀ + 1) with hd
  set r := d.take k with hr
  have hrsupp : ∀ z ∈ r.support, ∃ i, i₀ + 1 ≤ i ∧ i ≤ j₀ - 1 ∧ z = γ.getVert i := by
    intro z hz
    obtain ⟨l, hl, -⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hz
    refine ⟨i₀ + 1 + min k l, by omega, by omega, ?_⟩
    rw [← hl, hr, SimpleGraph.Walk.take_getVert, hd, SimpleGraph.Walk.drop_getVert]
  have hrint : ∀ z ∈ r.support, u.1 < z.1 ∧ z.1 < v.1 := by
    intro z hz
    obtain ⟨i, h1, h2, rfl⟩ := hrsupp z hz
    exact hint i h1 h2
  have hbeq : d.getVert k = γ.getVert (j₀ - 1) := by
    rw [hd, SimpleGraph.Walk.drop_getVert]
    congr 1
    omega
  have hau : ‖point (γ.getVert (i₀ + 1)) - point u‖ ≤ R₀ + 1 := by
    have e1 := norm_sub_le_norm_sub_add_norm_sub (point (γ.getVert (i₀ + 1)))
      (point (γ.getVert i₀)) (point u)
    have e2 := hstep i₀
    have e3 : ‖point (γ.getVert i₀) - point u‖ < R₀ := hi₀
    linarith only [e1, e2, e3]
  have hbv : ‖point v - point (d.getVert k)‖ ≤ R₀ + 1 := by
    rw [hbeq]
    have e1 := norm_sub_le_norm_sub_add_norm_sub (point v) (point (γ.getVert j₀))
      (point (γ.getVert (j₀ - 1)))
    have h1 := hstep (j₀ - 1)
    rw [show j₀ - 1 + 1 = j₀ by omega] at h1
    have e3 := hj₀.2
    linarith only [e1, h1, e3]
  have haint := hint (i₀ + 1) le_rfl (by omega)
  have hbint : u.1 < (d.getVert k).1 ∧ (d.getVert k).1 < v.1 := by
    rw [hbeq]; exact hint (j₀ - 1) (by omega) le_rfl
  -- costs
  have hcr : (walkCost ω r : ℝ≥0∞) ≤ walkCost ω γ := by
    have h1 : walkCost ω γ = walkCost ω (γ.take (i₀ + 1)) + walkCost ω d := by
      rw [hd, ← walkCost_append, SimpleGraph.Walk.append_take_drop_eq]
    have h2 : walkCost ω d = walkCost ω r + walkCost ω (d.drop k) := by
      rw [hr, ← walkCost_append, SimpleGraph.Walk.append_take_drop_eq]
    refine ENNReal.coe_le_coe.2 ?_
    rw [h1, h2]
    exact le_add_left (le_add_right le_rfl)
  have hc1 := hcu _ (hmem _) hau haint.1 haint.2
  have hc2 := hcv (d.getVert k) (by rw [hbeq]; exact hmem _) hbv hbint.1 hbint.2
  have hmid := slabTime_le_walkCost_of_interior (ω := ω) r hrint
  calc slabTime ω u.1 v.1 u v
      ≤ slabTime ω u.1 v.1 u (γ.getVert (i₀ + 1)) +
          slabTime ω u.1 v.1 (γ.getVert (i₀ + 1)) v := slabTime_add_le ω _ _ _ _ _
    _ ≤ slabTime ω u.1 v.1 u (γ.getVert (i₀ + 1)) +
          (slabTime ω u.1 v.1 (γ.getVert (i₀ + 1)) (d.getVert k) +
            slabTime ω u.1 v.1 (d.getVert k) v) :=
        add_le_add le_rfl (slabTime_add_le ω _ _ _ _ _)
    _ ≤ ENNReal.ofReal E + ((walkCost ω γ : ℝ≥0∞) + ENNReal.ofReal E) :=
        add_le_add hc1 (add_le_add (hmid.trans hcr) hc2)
    _ = (walkCost ω γ : ℝ≥0∞) + ENNReal.ofReal (2 * E) := by
        rw [two_mul, ENNReal.ofReal_add hE hE]
        ring

/-! ### Lemma `lem:slabs` (1) -/

/-- **The conclusion of Lemma `lem:slabs` (1)** at one configuration: the upper bound; the lower
bound is `T ≤ T_P`. -/
def SlabOneAt (M : Model m) (C S : ℝ) (N : ℕ) (ω : Config m) : Prop :=
  ∀ (ℓ : ℕ) (t : EuclideanSpace ℝ (Fin m)) (u v : Vertex m),
    point v - point u = (ℓ : ℝ) • slopeVec t → 1 ≤ ℓ → (ℓ : ℝ) ≤ 3 * N →
    ‖t - M.t₀‖ ≤ 3 * (N : ℝ) ^ (-(1 : ℝ) / 9) →
    InBox ((N : ℝ) ^ 2) u → InBox ((N : ℝ) ^ 2) v → C * S ^ 2 ≤ ℓ →
    slabTime ω u.1 v.1 u v ≤ (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C * S ^ 2)

theorem SlabOneAt.mono {M : Model m} {C C' S : ℝ} {N : ℕ} {ω : Config m} (hCC' : C ≤ C')
    (h : SlabOneAt M C S N ω) : SlabOneAt M C' S N ω := by
  intro ℓ t u v huv hℓ hl3 ht hu hv hCℓ
  have hmul := mul_le_mul_of_nonneg_right hCC' (sq_nonneg S)
  exact (h ℓ t u v huv hℓ hl3 ht hu hv (hmul.trans hCℓ)).trans
    (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hmul))

theorem ConeAt.mono {M : Model m} {C C' S : ℝ} {N : ℕ} {ω : Config m} (hS : 0 ≤ S) (hN : 1 ≤ N)
    (hCC' : C ≤ C') (h : ConeAt M C S N ω) : ConeAt M C' S N ω := by
  intro ℓ t u v hu hv huv hℓ hl3 ht γ hγ hcost z hz
  obtain ⟨h1, h2⟩ := h ℓ t u v hu hv huv hℓ hl3 ht γ hγ hcost z hz
  exact ⟨coneBound_mono hS hN hCC' h1, coneBound_mono hS hN hCC' h2⟩

/-- **Lemma `lem:slabs` (1)**, from `IsGood` and the conclusion of Lemma
`lem:cone`: a geodesic from `u` to `v` stays strictly between the faces outside the balls of radius
`C₁ S²` around `u` and `v`, and the surgery joins that part to `u` and `v` at cost `T_P`, which is
at most `C S²` by Lemma `lem:good` (2). The constants depend on `bd`, `C_g, c_g` and the constant
`C₁` of the cone. -/
theorem slabOneAt_of (bd : Bounds m) (hbd : bd.Valid) {Cg cg : ℝ} (hCg : 0 < Cg) (hcg : 0 < cg)
    {C₁ : ℝ} (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ S : ℝ, Real.log N ≤ S → ∀ ω : Config m, IsGood M Cg cg N S ω →
        ConeAt M C₁ S N ω → SlabOneAt M C S N ω := by
  set T := bd.T + 1 with hTdef
  have hT : 0 ≤ T := by linarith only [hbd.T_nonneg, hTdef]
  have hap : 0 < aperture T / 2 := by have := aperture_pos hT; positivity
  set K₁ := max C₁ ((C₁ / (aperture T / 2)) ^ 4) with hK₁def
  have hK₁ : C₁ ≤ K₁ := le_max_left _ _
  have hK₁' : (C₁ / (aperture T / 2)) ^ 4 ≤ K₁ := le_max_right _ _
  have hK₁0 : 0 < K₁ := lt_of_lt_of_le hC₁ hK₁
  set E₀ := Cg * (K₁ + 2) with hE₀
  have hE₀0 : 0 ≤ E₀ := by positivity
  set C := max 3 (max (2 * K₁ + 2) (2 * E₀)) with hCdef
  have hC3 : 3 ≤ C := le_max_left _ _
  have hCK : 2 * K₁ + 2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCE : 2 * E₀ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, by linarith only [hC3], ?_⟩
  obtain ⟨N₂, hN₂⟩ := exists_small_of_le_three_rpow hbd.law.delta_pos
    (ε := min 1 (aperture T / 2 / C₁)) (by positivity)
  set Cv := goodLen Cg cg T with hCv
  have hCv0 : 0 ≤ Cv := goodLen_nonneg hCg.le
  refine ⟨max N₂ (max 6 ⌈Cv⌉₊), fun M hM hfit N hN S hS ω hω hcone => ?_⟩
  -- the threshold chosen at the law of `bd`, for the model
  rw [← hfit.δ_eq] at hN₂
  have ht₀ := hfit.t₀_le
  have hδ := hM.delta_pos
  have hN2 : N₂ ≤ N := le_trans (le_max_left _ _) hN
  have hN6 : (6 : ℝ) ≤ N := by
    exact_mod_cast le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNCv : Cv ≤ N := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN))
  have hNpos : (0 : ℝ) < N := by linarith only [hN6]
  have hlogN : 1 ≤ Real.log N := one_le_log_of_three_le (by linarith only [hN6])
  have hS1 : 1 ≤ S := hlogN.trans hS
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS1
  have hS2' : 0 ≤ S ^ 2 := sq_nonneg S
  intro ℓ t u v huv hℓ1 hl3 ht hu hv hCℓ
  have hC3S : 3 * S ^ 2 ≤ C * S ^ 2 := mul_le_mul_of_nonneg_right hC3 hS2'
  have hSN : S ^ 2 ≤ N := by linarith only [hC3S, hCℓ, hl3]
  -- small slopes
  obtain ⟨htε, htlogε⟩ := hN₂ N hN2 ‖t - M.t₀‖ (norm_nonneg _) ht
  have ht1 : ‖t - M.t₀‖ ≤ 1 := htε.trans (min_le_left _ _)
  have htT : ‖t‖ ≤ T := by
    calc ‖t‖ = ‖(t - M.t₀) + M.t₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖t - M.t₀‖ + ‖M.t₀‖ := norm_add_le _ _
      _ ≤ T := by rw [hTdef]; linarith only [ht1, ht₀]
  have htlog : C₁ * (‖t - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N) ≤ aperture T / 2 := by
    have h1 : ‖t - M.t₀‖ ^ (1 + M.δ / 2) ≤ ‖t - M.t₀‖ ^ (M.δ / 2) :=
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) ht1 (by positivity)
        (by linarith only)
    have h2 : ‖t - M.t₀‖ ^ (M.δ / 2) * Real.log N ≤ aperture T / 2 / C₁ :=
      htlogε.trans (min_le_right _ _)
    have h3 : ‖t - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N ≤ aperture T / 2 / C₁ :=
      (mul_le_mul_of_nonneg_right h1 (by linarith only [hlogN])).trans h2
    calc C₁ * (‖t - M.t₀‖ ^ (1 + M.δ / 2) * Real.log N) ≤ C₁ * (aperture T / 2 / C₁) :=
          mul_le_mul_of_nonneg_left h3 hC₁.le
      _ = aperture T / 2 := by field_simp
  -- a geodesic from `u` to `v`
  have hbox : ∀ x : Vertex m, InBox ((N : ℝ) ^ 2) x → InBox (2 * (N : ℝ) ^ 2) x := fun x hx =>
    inBox_mono (by linarith only [sq_nonneg (N : ℝ)]) hx
  obtain ⟨γ, hγ⟩ := hω.exists_isGeodesic hcg (hbox u hu) v
  have hcost : (walkCost ω γ : ℝ) ≤ passageTimeReal ω u v + S ^ 2 := by
    rw [passageTimeReal, hγ.2]
    linarith only [hS2]
  have hcones := hcone ℓ t u v hu hv huv hℓ1 hl3 ht γ hγ.1 hcost
  -- geometry of the endpoints
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hfst : ((v.1 : ℝ) - u.1) = ℓ := by
    have := congrArg (fun w : Pt m => w.fst) huv
    simpa [point, slopeVec] using this
  have huv2 : u.1 + 2 ≤ v.1 := by
    have : (2 : ℝ) ≤ v.1 - u.1 := by
      rw [hfst]
      linarith only [hC3S, hCℓ, hS2]
    have : ((u.1 + 2 : ℤ) : ℝ) ≤ v.1 := by push_cast; linarith only [this]
    exact_mod_cast this
  have hvu : ‖point v - point u‖ ≤ 3 * (1 + T) * N := by
    rw [huv, norm_smul, Real.norm_eq_abs, abs_of_pos hℓpos]
    calc (ℓ : ℝ) * ‖slopeVec t‖ ≤ (3 * N) * (1 + T) :=
          mul_le_mul hl3 (norm_slopeVec_le htT) (norm_nonneg _) (by positivity)
      _ = 3 * (1 + T) * N := by ring
  have hvu' : (ℓ : ℝ) ≤ ‖point v - point u‖ := by
    rw [huv, norm_smul, Real.norm_eq_abs, abs_of_pos hℓpos]
    exact le_mul_of_one_le_right hℓpos.le (one_le_norm_slopeVec t)
  -- the box
  have hlen : (γ.length : ℝ) ≤ Cv * N :=
    hω.length_le_mul hCg.le hcg hSN (hbox u hu) (hbox v hv) hvu γ hγ.1 hcost
  have hsupp : ∀ y ∈ γ.support, InBox (2 * (N : ℝ) ^ 2) y := by
    intro y hy
    refine inBox_mono ?_ (inBox_of_mem_support γ hu hy)
    have := mul_le_mul_of_nonneg_right hNCv hNpos.le
    nlinarith only [this, hlen]
  -- the geodesic is strictly between the faces away from the endpoints
  have hfstz : ∀ z : Vertex m, (point z - point u).fst = (z.1 : ℝ) - u.1 := fun z => by
    simp [point]
  have hfstv : ∀ z : Vertex m, (point v - point z).fst = (v.1 : ℝ) - z.1 := fun z => by
    simp [point]
  have hu' : ∀ z ∈ γ.support, K₁ * S ^ 2 ≤ ‖point z - point u‖ → u.1 < z.1 := by
    intro z hz hzr
    have h := fst_pos_of_coneBound (M := M) hC₁ hS1 hK₁ hK₁' htT htlog (hcones z hz).2 hzr
    rw [hfstz] at h
    have : (u.1 : ℝ) < z.1 := by linarith only [h]
    exact_mod_cast this
  have hv' : ∀ z ∈ γ.support, K₁ * S ^ 2 ≤ ‖point v - point z‖ → z.1 < v.1 := by
    intro z hz hzr
    have h := fst_pos_of_coneBound (M := M) hC₁ hS1 hK₁ hK₁' htT htlog (hcones z hz).1 hzr
    rw [hfstv] at h
    have : (z.1 : ℝ) < v.1 := by linarith only [h]
    exact_mod_cast this
  have hfar : 2 * (K₁ * S ^ 2) + 2 ≤ ‖point v - point u‖ := by
    have h1 := mul_le_mul_of_nonneg_right hCK hS2'
    have h2 : 2 * (K₁ * S ^ 2) + 2 ≤ (2 * K₁ + 2) * S ^ 2 := by
      have e : (2 * K₁ + 2) * S ^ 2 = 2 * (K₁ * S ^ 2) + 2 * S ^ 2 := by ring
      linarith only [e, hS2]
    linarith only [h1, h2, hCℓ, hvu']
  -- `T_P` from `u` and to `v` is at most `C S²`, by Lemma `lem:good` (2)
  have hE : ∀ x y : Vertex m, ‖point y - point x‖ ≤ K₁ * S ^ 2 + 1 →
      Cg * (‖point y - point x‖ + S ^ 2) ≤ E₀ * S ^ 2 := by
    intro x y hxy
    have e : E₀ * S ^ 2 = Cg * (K₁ * S ^ 2 + 2 * S ^ 2) := by rw [hE₀]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith only [hxy, hS2]) hCg.le
  have hcu : ∀ x ∈ γ.support, ‖point x - point u‖ ≤ K₁ * S ^ 2 + 1 → u.1 < x.1 → x.1 < v.1 →
      slabTime ω u.1 v.1 u x ≤ ENNReal.ofReal (E₀ * S ^ 2) := by
    intro x hx hxr h1 h2
    exact (hω.slabTime_le u x (hbox u hu) (hsupp x hx) u.1 v.1 huv2 le_rfl (by omega) h1.le
      h2.le).trans (ENNReal.ofReal_le_ofReal (hE u x hxr))
  have hcv : ∀ x ∈ γ.support, ‖point v - point x‖ ≤ K₁ * S ^ 2 + 1 → u.1 < x.1 → x.1 < v.1 →
      slabTime ω u.1 v.1 x v ≤ ENNReal.ofReal (E₀ * S ^ 2) := by
    intro x hx hxr h1 h2
    exact (hω.slabTime_le x v (hsupp x hx) (hbox v hv) u.1 v.1 huv2 h1.le h2.le (by omega)
      le_rfl).trans (ENNReal.ofReal_le_ofReal (hE x v hxr))
  -- the surgery
  have hsurg := slabTime_le_of_interior_slabTime γ (R₀ := K₁ * S ^ 2) (E := E₀ * S ^ 2)
    (by positivity) (by positivity) hu' hv' hfar hcu hcv
  have hfin : 2 * (E₀ * S ^ 2) ≤ C * S ^ 2 := by
    have := mul_le_mul_of_nonneg_right hCE hS2'
    linarith only [this]
  calc slabTime ω u.1 v.1 u v
      ≤ (walkCost ω γ : ℝ≥0∞) + ENNReal.ofReal (2 * (E₀ * S ^ 2)) := hsurg
    _ ≤ (passageTime ω u v : ℝ≥0∞) + ENNReal.ofReal (C * S ^ 2) := by
        rw [hγ.2]
        exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hfin)

end CurvatureVariance.Paper.Proofs.Geometry
