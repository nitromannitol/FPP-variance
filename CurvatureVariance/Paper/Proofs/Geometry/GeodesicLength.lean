/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Proofs.Geometry.KestenVar
public import CurvatureVariance.Paper.Proofs.Geometry.SlabPaths
public import CurvatureVariance.Infra.FPP.Statements
public import CurvatureVariance.Infra.Os.Sum
import CurvatureVariance.Paper.Proofs.OsSum
import CurvatureVariance.Statements.Inputs.IsOsOfMeasureGeLe

/-!
# The number of edges of geodesics

`GeodesicLengthStatement` (the bound `C(1 + |v − u|₁) + O₁(C)` on the number of edges of geodesics
and of geodesics in a slab, in the text after equation `eq:classical`), in almost-sure form
(pointwise, the bound fails when all weights vanish, since then every simple path is a geodesic):
for fixed `u, v`, one variable `X ≤ O₁(C)` bounds the number of edges of every geodesic and every
slab geodesic from `u` to `v` by `C(1 + |v − u|₁) + X`.

A simple path `γ` from `u` either costs at most `a` per edge, and then has at most `N_u` edges, the
Kesten variable (`cheapLength`); or it has fewer than `cost(γ)/a` edges. A geodesic, and a slab
geodesic, costs at most a coordinate path through one of the levels `u₁ − 1, u₁, u₁ + 1`
(`slabPath`), which has at most `|v − u|₁ + 2` edges and, by Chernoff, costs at most
`(log M / α)` per edge plus an `O₁(2/α)` variable. So `X = N_u + a⁻¹ Σ_c (W_c)₊` with `W_c` the
centred cost of the coordinate path through the level `c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP
  CurvatureVariance.Infra.Os

variable {m : ℕ}

/-- The `ℓ¹` norm of a difference of vertices, as an integer. -/
theorem oneNorm_sub_eq (u v : Vertex m) :
    oneNorm (v - u) = (((|v.1 - u.1| + ∑ j, |v.2 j - u.2 j| : ℤ)) : ℝ) := by
  rw [oneNorm]
  push_cast
  simp

/-- **The number of edges of geodesics** for a law under the standing hypotheses, for geodesics and
slab geodesics, almost surely: the constant depends on the law only. -/
theorem geodesicLength_of_law {L : Law m} (hL : L.Valid) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Vertex m,
      ∃ X : Config m → ℝ, CurvatureVariance.IsOs L.P 1 C X ∧ ∀ᵐ ω ∂L.P,
        (∀ γ : (latticeGraph m).Walk u v, IsGeodesic ω γ →
          (γ.length : ℝ) ≤ C * (1 + oneNorm (v - u)) + X ω) ∧
        (∀ p q : ℤ, p + 2 ≤ q → p ≤ u.1 → u.1 ≤ q → p ≤ v.1 → v.1 ≤ q →
          ∀ γ : (latticeGraph m).Walk u v, IsSlabGeodesic ω p q γ →
            (γ.length : ℝ) ≤ C * (1 + oneNorm (v - u)) + X ω) := by
  have := hL.probF
  have := hL.probP
  obtain ⟨⟨α, hα, hexp⟩, -⟩ := hL.assumptionW
  obtain ⟨a, c, ha, hc, hcheapAll⟩ :=
    KestenEstimate.exists_cheapPaths (kestenEstimate hL.one_le_m L.F hL.assumptionW.2)
  have hcheap := hcheapAll L.P hL.iid
  have hM1 : 1 ≤ expMom L.F α := one_le_expMom hα.le hexp
  set Kl := Real.log (expMom L.F α) / α with hKl
  have hKl0 : 0 ≤ Kl := div_nonneg (Real.log_nonneg hM1) hα.le
  set θK := (1 + Real.log (Real.exp (c / 2) / (1 - Real.exp (-(c / 2)))) / (2 * Real.log 2)) *
    (2 * (2 / c)) with hθK
  have hθK0 : 0 < θK := by
    have hr : Real.exp (-(c / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have hK : 1 ≤ Real.exp (c / 2) / (1 - Real.exp (-(c / 2))) := by
      rw [le_div_iff₀ (by linarith)]
      have : 1 ≤ Real.exp (c / 2) := Real.one_le_exp (by linarith)
      linarith [(Real.exp_pos (-(c / 2))).le]
    have := Real.log_nonneg hK
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity
  set θs : Option (Fin 3) → ℝ := fun o => o.elim θK fun _ => a⁻¹ * (2 / α) with hθs
  have hθs0 : ∀ o, 0 < θs o := by
    intro o
    cases o
    · exact hθK0
    · simp only [hθs, Option.elim]; positivity
  set C := max (sumConstant 1 * ∑ o, θs o) (2 * Kl / a + 1) with hC
  have hC0 : 0 < C := lt_max_of_lt_right (by positivity)
  refine ⟨C, hC0, fun u v => ?_⟩
  -- the coordinate paths through the levels `u₁ − 1, u₁, u₁ + 1`
  set lev : Fin 3 → ℤ := fun i => u.1 + ((i : ℕ) : ℤ) - 1 with hlev
  set π : Fin 3 → (latticeGraph m).Walk u v := fun i => slabPath u v (lev i) with hπ
  set W : Fin 3 → Config m → ℝ := fun i ω => (walkCost ω (π i) : ℝ) - Kl * (π i).length with hW
  set Y : Option (Fin 3) → Config m → ℝ := fun o ω =>
    o.elim (cheapLength a u ω).toReal fun i => a⁻¹ * max (W i ω) 0 with hY
  have hlen : ∀ i, ((π i).length : ℝ) ≤ oneNorm (v - u) + 2 := by
    intro i
    have hi := i.isLt
    have h := slabPath_length_le_add_two u v (c := lev i) (by
      simp only [hlev]
      rw [abs_le]
      constructor <;> omega)
    rw [oneNorm_sub_eq]
    have h' : (((π i).length : ℤ) : ℝ) ≤ ((|v.1 - u.1| + ∑ j, |v.2 j - u.2 j| + 2 : ℤ) : ℝ) :=
      Int.cast_le.2 h
    push_cast at h' ⊢
    linarith
  -- the centred costs are `O₁(2/α)`
  have hWos : ∀ i, IsOs L.P 1 (2 / α) (W i) := by
    intro i
    have hnodup := (slabPath_isPath u v (lev i)).isTrail.edges_nodup
    have hWm : AEMeasurable (W i) L.P :=
      ((measurable_walkCost_real (π i)).sub measurable_const).aemeasurable
    have h := CurvatureVariance.isOs_of_measure_ge_le (s := 1) (θ := 1 / α) (X := W i) one_pos (by positivity) hWm
      fun x hx => by
        have hset : {ω | 1 / α * x ≤ W i ω} =
            {ω | 1 / α * x + Kl * (π i).length ≤ (walkCost ω (π i) : ℝ)} := by
          ext ω
          simp only [hW, Set.mem_ofPred_eq]
          constructor <;> intro h <;> linarith
        rw [hset]
        refine (IsIIDWeights.measure_le_walkCost_le hL.iid (π i) hnodup hα.le hexp _).trans
          (le_of_eq ?_)
        congr 1
        have hMpos : 0 < expMom L.F α := by linarith
        rw [Real.rpow_one, show (∫ x : ℝ≥0, Real.exp (α * x) ∂L.F) = expMom L.F α from rfl,
          ← Real.exp_log hMpos, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        rw [hKl]
        field_simp
        ring
    rwa [div_one, Real.rpow_one, show (2 : ℝ) * (1 / α) = 2 / α by ring] at h
  have hYos : ∀ o ∈ (Finset.univ : Finset (Option (Fin 3))), IsOs L.P 1 (θs o) (Y o) := by
    intro o _
    cases o with
    | none => exact isOs_toReal_cheapLength hc hcheap u
    | some i =>
      have hmax : IsOs L.P 1 (2 / α) (fun ω => max (W i ω) 0) :=
        ⟨(hWos i).1.max aemeasurable_const, by simpa only [max_assoc, max_self] using (hWos i).2⟩
      exact (isOs_mul_iff (inv_pos.2 ha)).2 hmax
  refine ⟨fun ω => ∑ o, Y o ω, ?_, ?_⟩
  · exact (CurvatureVariance.Paper.isOs_sum_of_one_le le_rfl Finset.univ Finset.univ_nonempty θs
      (fun o _ => hθs0 o) Y hYos).mono_scale zero_le_one
      (Finset.sum_pos (fun o _ => hθs0 o) Finset.univ_nonempty)
      (le_trans (by simp [sumConstant]) (le_max_left _ _))
  · filter_upwards [ae_cheapLength_lt_top hc hcheap u] with ω hω
    have hY0 : ∀ o, 0 ≤ Y o ω := by
      intro o
      cases o
      · exact ENNReal.toReal_nonneg
      · simp only [hY, Option.elim]; positivity
    have hle : ∀ o, Y o ω ≤ ∑ o, Y o ω := fun o =>
      Finset.single_le_sum (f := fun o => Y o ω) (fun o _ => hY0 o) (Finset.mem_univ o)
    have hr0 : 0 ≤ oneNorm (v - u) := by rw [oneNorm]; positivity
    -- a simple path from `u` costing at most a coordinate path has few edges
    have key : ∀ (i : Fin 3) (γ : (latticeGraph m).Walk u v), γ.IsPath →
        (walkCost ω γ : ℝ) ≤ walkCost ω (π i) →
        (γ.length : ℝ) ≤ C * (1 + oneNorm (v - u)) + ∑ o, Y o ω := by
      intro i γ hγ hcost
      have hCr : 0 ≤ C * (1 + oneNorm (v - u)) := by positivity
      by_cases hγc : (walkCost ω γ : ℝ) ≤ a * γ.length
      · have h1 := le_cheapLength γ hγ hγc
        have h2 : (γ.length : ℝ) ≤ (cheapLength a u ω).toReal := by
          have := ENNReal.toReal_mono hω.ne h1
          simpa using this
        have h3 : (cheapLength a u ω).toReal ≤ ∑ o, Y o ω := hle none
        linarith
      · push Not at hγc
        have h3 : a⁻¹ * max (W i ω) 0 ≤ ∑ o, Y o ω := hle (some i)
        have hW' : (walkCost ω (π i) : ℝ) ≤ max (W i ω) 0 + Kl * (oneNorm (v - u) + 2) := by
          have := le_max_left (W i ω) 0
          have h4 := mul_le_mul_of_nonneg_left (hlen i) hKl0
          simp only [hW] at this
          linarith
        have hk : a * γ.length ≤ max (W i ω) 0 + Kl * (oneNorm (v - u) + 2) := by linarith
        have hk' : (γ.length : ℝ) ≤ a⁻¹ * max (W i ω) 0 + Kl / a * (oneNorm (v - u) + 2) := by
          have h6 : (γ.length : ℝ) ≤ (max (W i ω) 0 + Kl * (oneNorm (v - u) + 2)) / a := by
            rw [le_div_iff₀ ha]
            linarith
          calc (γ.length : ℝ) ≤ (max (W i ω) 0 + Kl * (oneNorm (v - u) + 2)) / a := h6
            _ = _ := by rw [div_eq_mul_inv]; ring
        have hCK : 2 * Kl / a ≤ C := (le_of_lt (lt_add_one _)).trans (le_max_right _ _)
        have h5 : Kl / a * (oneNorm (v - u) + 2) ≤ C * (1 + oneNorm (v - u)) := by
          calc Kl / a * (oneNorm (v - u) + 2) ≤ Kl / a * (2 * (1 + oneNorm (v - u))) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = 2 * Kl / a * (1 + oneNorm (v - u)) := by ring
            _ ≤ C * (1 + oneNorm (v - u)) := mul_le_mul_of_nonneg_right hCK (by linarith)
        linarith
    refine ⟨fun γ hγ => key 1 γ hγ.1 ?_, fun p q hpq hpu huq hpv hvq γ hγ => ?_⟩
    · rw [hγ.2]
      exact_mod_cast Infra.FPP.passageTime_le_walkCost ω (π 1)
    · obtain ⟨i, hi⟩ : ∃ i : Fin 3, lev i = slabLevel p q u := by
        rcases slabLevel_mem p q u with h | h | h
        · exact ⟨0, by simp [hlev, h]⟩
        · exact ⟨1, by simp [hlev, h]⟩
        · exact ⟨2, by simp only [hlev, h]; norm_num; ring⟩
      obtain ⟨hpc, hcq⟩ := slabLevel_bounds hpq hpu huq
      have hedges : ∀ e ∈ (π i).edges, e ∈ slabEdges p q := by
        simp only [hπ, hi]
        exact slabPath_edges_mem hpu huq hpv hvq hpc hcq
      refine key i γ hγ.1 ?_
      have h1 : (walkCost ω γ : ℝ≥0∞) ≤ walkCost ω (π i) := by
        rw [hγ.2.2]
        exact iInf₂_le (π i) hedges
      exact_mod_cast ENNReal.coe_le_coe.1 h1

/-- **The number of edges of geodesics and slab geodesics**, almost surely, with the constant of
the law of `bd` (`geodesicLength_of_law`). -/
theorem geodesicLengthStatement_holds (m : ℕ) : GeodesicLengthStatement m := by
  intro bd hbd
  obtain ⟨C, hC, h⟩ := geodesicLength_of_law hbd.law
  refine ⟨C, hC, fun M _ hfit => ?_⟩
  rw [hfit.P_eq]
  exact h

end CurvatureVariance.Paper.Proofs.Geometry
