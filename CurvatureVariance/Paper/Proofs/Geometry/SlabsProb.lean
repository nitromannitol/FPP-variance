/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Geometry.SlabsPair
public import CurvatureVariance.Paper.Proofs.Geometry.Classical
public import CurvatureVariance.Paper.Proofs.Geometry.GeodesicLength

/-!
# The events `𝒢_N(S)`: the union bound

The proof of Lemma `lem:good`: with union bounds over the box, the events
of (H1)–(H3), the bounds (1)–(3) of the lemma, fail with probability at most
`K |B|² e^{-cS²}`, `|B|` the number of vertices of the box (`exists_goodEvent_bound`). (H1) is the
tails of `exists_tails_of_law`, from [ADH, Theorem 3.13] and the Chernoff bound along a path of
`|y − x|₁` edges, and the mean bound of equation `eq:classical`, at most
`C √(r log(2 + r)) ≤ C' S |y − x|^{1/2}` once `log` of the box size is at most `3S²`. (H2) is the
Chernoff bound for a path in the slab, and (H3) is Kesten's bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Proofs.Geometry

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

variable {m : ℕ}

theorem measure_biUnion_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ι) (f : ι → Set Ω) (b : ℝ≥0∞) (h : ∀ i ∈ s, P (f i) ≤ b) :
    P (⋃ i ∈ s, f i) ≤ s.card * b :=
  (measure_biUnion_finset_le s f).trans
    ((Finset.sum_le_sum h).trans (by rw [Finset.sum_const, nsmul_eq_mul]))

/-- The `ℓ¹` distance between two vertices of the box `[−R, R]^d` is at most `2(d)R`. -/
theorem l1Dist_le_of_mem_box {R : ℕ} {x y : Vertex m} (hx : x ∈ boxFinset R)
    (hy : y ∈ boxFinset R) : (l1Dist x y : ℝ) ≤ 2 * ((m : ℝ) + 1) * R := by
  simp only [boxFinset, Finset.mem_product, Finset.mem_Icc, Fintype.mem_piFinset] at hx hy
  have h1 : ((x.1 - y.1).natAbs : ℝ) ≤ 2 * R := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    rw [abs_le]
    constructor
    · have := hx.1.1; have := hy.1.2
      have h : (-(R : ℤ) : ℝ) ≤ x.1 := by exact_mod_cast hx.1.1
      have h' : (y.1 : ℝ) ≤ R := by exact_mod_cast hy.1.2
      push_cast at h
      linarith
    · have h : (x.1 : ℝ) ≤ R := by exact_mod_cast hx.1.2
      have h' : (-(R : ℤ) : ℝ) ≤ y.1 := by exact_mod_cast hy.1.1
      push_cast at h'
      linarith
  have h2 : ∀ j, ((x.2 j - y.2 j).natAbs : ℝ) ≤ 2 * R := by
    intro j
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    rw [abs_le]
    have a1 : (-(R : ℤ) : ℝ) ≤ x.2 j := by exact_mod_cast (hx.2 j).1
    have a2 : (x.2 j : ℝ) ≤ R := by exact_mod_cast (hx.2 j).2
    have a3 : (-(R : ℤ) : ℝ) ≤ y.2 j := by exact_mod_cast (hy.2 j).1
    have a4 : (y.2 j : ℝ) ≤ R := by exact_mod_cast (hy.2 j).2
    push_cast at a1 a3
    constructor <;> linarith
  have h3 : ∑ j, ((x.2 j - y.2 j).natAbs : ℝ) ≤ ∑ _j : Fin m, 2 * (R : ℝ) :=
    Finset.sum_le_sum fun j _ => h2 j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  simp only [l1Dist]
  push_cast
  nlinarith

/-- **The union bound** (the proof of Lemma `lem:good`): for valid bounds `bd` there are
`A, a, K, c > 0`, depending on the law of `bd` only, such that for every model fitting `bd`, on
every box `[−R, R]^d` and at every scale `S ≥ 1` with `log(2 + 2dR) ≤ 3S²`, the events of
(H1)–(H3) fail with probability at most `K |B|² e^{-cS²}`. -/
theorem exists_goodEvent_bound (bd : Bounds m) (hbd : bd.Valid) :
    ∃ A a K c : ℝ, 0 < A ∧ 0 < a ∧ 0 ≤ K ∧ 0 < c ∧
      ∀ M : Model m, M.Standing → M.Fits bd → ∀ (R : ℕ) (S : ℝ), 1 ≤ S →
        Real.log (2 + 2 * ((m : ℝ) + 1) * R) ≤ 3 * S ^ 2 →
        M.P (GoodEvent M.μ.1 A a R S)ᶜ ≤
          ENNReal.ofReal (K * ((boxFinset R : Finset (Vertex m)).card : ℝ) ^ 2 *
            Real.exp (-(c * S ^ 2))) := by
  have hL := hbd.law
  have := hL.probF
  have := hL.probP
  obtain ⟨ρ, hρ, htail⟩ := exists_tails_of_law hL
  obtain ⟨⟨α, hα, hexp⟩, -⟩ := hL.assumptionW
  obtain ⟨a, c, ha, hc, hcheapAll⟩ :=
    KestenEstimate.exists_cheapPaths (kestenEstimate hL.one_le_m bd.law.F hL.assumptionW.2)
  have hcheap := hcheapAll bd.law.P hL.iid
  obtain ⟨Ccl, hCcl, hcl⟩ := classical_of_law hL
  have hMx := one_le_expMom hα.le hexp
  have hlogM : 0 ≤ Real.log (expMom bd.law.F α) := Real.log_nonneg hMx
  set Cg := Ccl * Real.sqrt (3 * ((m : ℝ) + 1)) with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  set A := 2 * Cg + Real.log (expMom bd.law.F α) / α + 1 with hAdef
  have hA : 0 < A := by positivity
  have hAM : Real.log (expMom bd.law.F α) ≤ α * A := by
    have : Real.log (expMom bd.law.F α) / α ≤ A := by linarith
    rwa [div_le_iff₀ hα, mul_comm] at this
  have hlMα : 0 ≤ Real.log (expMom bd.law.F α) / α := div_nonneg hlogM hα.le
  have h2Cg : 2 * Cg ≤ A := by linarith
  set ρ₁ := concRate ρ A m with hρ₁
  have hρ₁0 : 0 < ρ₁ := concRate_pos hρ hA
  set cc := min ρ₁ (min (α * A) (c * A / 2)) with hcc
  have hcc0 : 0 < cc := lt_min hρ₁0 (lt_min (by positivity) (by positivity))
  set K₁ : ℝ := 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := zero_le_two
  have hr : Real.exp (-(c / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  set K₃ := Real.exp (c / 2) / (1 - Real.exp (-(c / 2))) with hK₃
  have hK₃0 : 0 ≤ K₃ := div_nonneg (Real.exp_pos _).le (by linarith)
  set K := K₁ + 3 * expMom bd.law.F α ^ 2 + K₃ with hK
  refine ⟨A, a, K, cc, hA, ha, by positivity, hcc0, fun M _ hfit R S hS hlog => ?_⟩
  rw [hfit.P_eq, hfit.μ_eq]
  have hS0 : 0 ≤ S := by linarith
  set B : Finset (Vertex m) := boxFinset R with hB
  set nB : ℝ := (B.card : ℝ) with hnB
  have hnB0 : 0 ≤ nB := Nat.cast_nonneg _
  have hnB2 : nB ≤ nB ^ 2 := by
    rcases (Nat.eq_zero_or_pos B.card) with h0 | h0
    · simp [hnB, h0]
    · have : (1 : ℝ) ≤ nB := by
        rw [hnB]; exact_mod_cast Nat.one_le_iff_ne_zero.2 h0.ne'
      exact le_self_pow₀ this two_ne_zero
  have hT : ∀ a : Vertex m, MeasurePreserving (translate a) bd.law.P bd.law.P :=
    fun a => IsIIDWeights.measurePreserving_translate hL.iid a
  -- the three failure sets
  set F1 : Set (Config m) := ⋃ x ∈ B, ⋃ y ∈ B, {ω | A * (S * Real.sqrt ‖point y - point x‖ +
      S ^ 2) < |passageTimeReal ω x y - bd.law.μ.1 (point y - point x)|} with hF1
  set F2 : Set (Config m) := ⋃ x ∈ B, ⋃ y ∈ B, ⋃ i ∈ (Finset.univ : Finset (Fin 3)),
      {ω | A * (oneNorm (y - x) + S ^ 2) <
        (walkCost ω (slabPath x y (x.1 + (i : ℕ) - 1)) : ℝ)} with hF2
  set F3 : Set (Config m) := ⋃ x ∈ B,
      {ω | ENNReal.ofReal (A * S ^ 2 - 1) < cheapLength a x ω} with hF3
  have hsub : (GoodEvent bd.law.μ.1 A a R S)ᶜ ⊆ F1 ∪ F2 ∪ F3 := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    apply hω
    refine ⟨fun x hx y hy => ?_, fun x hx y hy i => ?_, fun x hx k hk hkω => ?_⟩
    · by_contra h'
      push Not at h'
      exact hcon.1.1 (Set.mem_iUnion₂.2 ⟨x, hx, Set.mem_iUnion₂.2 ⟨y, hy, h'⟩⟩)
    · by_contra h'
      push Not at h'
      exact hcon.1.2 (Set.mem_iUnion₂.2 ⟨x, hx, Set.mem_iUnion₂.2 ⟨y, hy,
        Set.mem_iUnion₂.2 ⟨i, Finset.mem_univ _, h'⟩⟩⟩)
    · apply hcon.2
      refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
      obtain ⟨v, γ, hγ, hlen, hcost⟩ := hkω
      have h1 := le_cheapLength γ hγ (by rw [hlen]; exact hcost)
      rw [hlen] at h1
      show ENNReal.ofReal (A * S ^ 2 - 1) < cheapLength a x ω
      refine lt_of_lt_of_le ?_ h1
      rw [← ENNReal.ofReal_natCast]
      have hAS : (0 : ℝ) < A * S ^ 2 := by positivity
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  -- (H1)
  have hP1 : bd.law.P F1 ≤ (B.card : ℝ≥0∞) * ((B.card : ℝ≥0∞) *
      ENNReal.ofReal (K₁ * Real.exp (-(ρ₁ * S ^ 2)))) := by
    refine measure_biUnion_le_card_mul B _ _ fun x hx =>
      measure_biUnion_le_card_mul B _ _ fun y hy => ?_
    by_cases hxy : x = y
    · subst hxy
      have : {ω : Config m | A * (S * Real.sqrt ‖point x - point x‖ + S ^ 2) <
          |passageTimeReal ω x x - bd.law.μ.1 (point x - point x)|} = ∅ := by
        ext ω
        simp only [sub_self, norm_zero, Real.sqrt_zero, mul_zero, zero_add, map_zero,
          passageTimeReal, passageTime_self, NNReal.coe_zero, abs_zero, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_lt]
        positivity
      rw [this, measure_empty]
      exact zero_le
    · have hne : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
      have hn1 : 1 ≤ l1Dist x y := by
        rw [l1Dist_eq_l1Dist_zero_sub]; exact one_le_l1Dist_zero hne
      obtain ⟨-, -, hg0, hg1⟩ := hcl (y - x) hne
      have hET :
          ∫ ω, passageTimeReal ω x y ∂bd.law.P = ∫ ω, passageTimeReal ω 0 (y - x) ∂bd.law.P :=
        integral_passageTime_eq_meanTime hT x y
      rw [← hET, point_sub] at hg0 hg1
      have hgap : (∫ ω, passageTimeReal ω x y ∂bd.law.P) - bd.law.μ.1 (point y - point x) ≤
          Cg * S * Real.sqrt ‖point y - point x‖ := by
        refine hg1.trans ?_
        rw [oneNorm_sub_eq_l1Dist]
        have hnr := l1Dist_le_mul_norm x y
        have hnR := l1Dist_le_of_mem_box hx hy
        have hl : Real.log (2 + (l1Dist x y : ℝ)) ≤ 3 * S ^ 2 :=
          (Real.log_le_log (by positivity) (by linarith)).trans hlog
        have hl0 : 0 ≤ Real.log (2 + (l1Dist x y : ℝ)) := Real.log_nonneg (by linarith)
        have hprod : (l1Dist x y : ℝ) * Real.log (2 + (l1Dist x y : ℝ)) ≤
            (3 * ((m : ℝ) + 1)) * S ^ 2 * ‖point y - point x‖ := by
          calc (l1Dist x y : ℝ) * Real.log (2 + (l1Dist x y : ℝ))
              ≤ (((m : ℝ) + 1) * ‖point y - point x‖) * (3 * S ^ 2) :=
                mul_le_mul hnr hl hl0 (by positivity)
            _ = _ := by ring
        calc Ccl * Real.sqrt ((l1Dist x y : ℝ) * Real.log (2 + (l1Dist x y : ℝ)))
            ≤ Ccl * Real.sqrt ((3 * ((m : ℝ) + 1)) * S ^ 2 * ‖point y - point x‖) :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod) hCcl.le
          _ = Cg * S * Real.sqrt ‖point y - point x‖ := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
                Real.sqrt_sq hS0, hCg]
              ring
      exact measure_concentration_fail_le bd.law.μ.1 hn1 hρ hA hS0 h2Cg (by linarith) hgap
        (htail x y hxy)
  -- (H2)
  have hP2 : bd.law.P F2 ≤ (B.card : ℝ≥0∞) * ((B.card : ℝ≥0∞) *
      ((Finset.univ : Finset (Fin 3)).card *
        ENNReal.ofReal (expMom bd.law.F α ^ 2 * Real.exp (-(α * A * S ^ 2))))) := by
    refine measure_biUnion_le_card_mul B _ _ fun x hx =>
      measure_biUnion_le_card_mul B _ _ fun y hy =>
        measure_biUnion_le_card_mul _ _ _ fun i _ => ?_
    have hi := i.isLt
    have hlen := slabPath_length_le_add_two x y (c := x.1 + (i : ℕ) - 1) (by
      rw [abs_le]; constructor <;> omega)
    refine IsIIDWeights.measure_lt_walkCost_le hL.iid hα hexp _ (slabPath_isPath _ _ _)
      (by rw [oneNorm]; positivity) ?_ hAM
    rw [oneNorm_sub_eq]
    have h' : (((slabPath x y (x.1 + (i : ℕ) - 1)).length : ℤ) : ℝ) ≤
        ((|y.1 - x.1| + ∑ j, |y.2 j - x.2 j| + 2 : ℤ) : ℝ) := Int.cast_le.2 hlen
    push_cast at h' ⊢
    linarith
  -- (H3)
  have hP3 :
      bd.law.P F3 ≤ (B.card : ℝ≥0∞) * ENNReal.ofReal (K₃ * Real.exp (-(c * A / 2 * S ^ 2))) := by
    refine measure_biUnion_le_card_mul B _ _ fun x _ => ?_
    refine (measure_ofReal_lt_cheapLength_le hc hcheap x _).trans (le_of_eq ?_)
    congr 1
    rw [hK₃, div_mul_eq_mul_div (Real.exp (c / 2)), ← Real.exp_add]
    congr 2
    ring
  -- the sum
  have e1 : ∀ x : ℝ, Real.exp (-(x * S ^ 2)) ≤ Real.exp (-(cc * S ^ 2)) ↔ cc ≤ x := by
    intro x
    rw [Real.exp_le_exp, neg_le_neg_iff]
    constructor
    · intro hx
      have hS2 : 0 < S ^ 2 := by positivity
      exact le_of_mul_le_mul_right hx hS2
    · intro hx
      exact mul_le_mul_of_nonneg_right hx (sq_nonneg S)
  have b1 := (e1 ρ₁).2 (min_le_left _ _)
  have b2 := (e1 (α * A)).2 ((min_le_right _ _).trans (min_le_left _ _))
  have b3 := (e1 (c * A / 2)).2 ((min_le_right _ _).trans (min_le_right _ _))
  have hexp0 := (Real.exp_pos (-(cc * S ^ 2))).le
  calc bd.law.P (GoodEvent bd.law.μ.1 A a R S)ᶜ ≤ bd.law.P F1 + bd.law.P F2 + bd.law.P F3 :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl))
    _ ≤ _ := add_le_add (add_le_add hP1 hP2) hP3
    _ = ENNReal.ofReal (nB * (nB * (K₁ * Real.exp (-(ρ₁ * S ^ 2))))) +
          ENNReal.ofReal (nB * (nB * (3 * (expMom bd.law.F α ^ 2 *
            Real.exp (-(α * A * S ^ 2)))))) +
          ENNReal.ofReal (nB * (K₃ * Real.exp (-(c * A / 2 * S ^ 2)))) := by
        simp only [Finset.card_univ, Fintype.card_fin, hnB]
        rw [ENNReal.ofReal_mul hnB0, ENNReal.ofReal_mul hnB0, ENNReal.ofReal_mul hnB0,
          ENNReal.ofReal_mul hnB0, ENNReal.ofReal_mul hnB0,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_natCast,
          ENNReal.ofReal_ofNat]
        norm_cast
    _ ≤ ENNReal.ofReal (K * nB ^ 2 * Real.exp (-(cc * S ^ 2))) := by
        have hM2 : 0 ≤ expMom bd.law.F α ^ 2 := sq_nonneg _
        have h1 : 0 ≤ nB * (nB * (K₁ * Real.exp (-(ρ₁ * S ^ 2)))) :=
          mul_nonneg hnB0 (mul_nonneg hnB0 (mul_nonneg hK₁0 (Real.exp_pos _).le))
        have h2 : 0 ≤ nB * (nB * (3 * (expMom bd.law.F α ^ 2 * Real.exp (-(α * A * S ^ 2))))) :=
          mul_nonneg hnB0 (mul_nonneg hnB0 (mul_nonneg zero_le_three
            (mul_nonneg hM2 (Real.exp_pos _).le)))
        have h3 : 0 ≤ nB * (K₃ * Real.exp (-(c * A / 2 * S ^ 2))) :=
          mul_nonneg hnB0 (mul_nonneg hK₃0 (Real.exp_pos _).le)
        rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) h3]
        refine ENNReal.ofReal_le_ofReal ?_
        have t1 : nB * (nB * (K₁ * Real.exp (-(ρ₁ * S ^ 2)))) ≤
            K₁ * nB ^ 2 * Real.exp (-(cc * S ^ 2)) := by
          calc nB * (nB * (K₁ * Real.exp (-(ρ₁ * S ^ 2))))
              = K₁ * nB ^ 2 * Real.exp (-(ρ₁ * S ^ 2)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left b1 (mul_nonneg hK₁0 (sq_nonneg _))
        have t2 : nB * (nB * (3 * (expMom bd.law.F α ^ 2 * Real.exp (-(α * A * S ^ 2))))) ≤
            3 * expMom bd.law.F α ^ 2 * nB ^ 2 * Real.exp (-(cc * S ^ 2)) := by
          calc nB * (nB * (3 * (expMom bd.law.F α ^ 2 * Real.exp (-(α * A * S ^ 2)))))
              = 3 * expMom bd.law.F α ^ 2 * nB ^ 2 * Real.exp (-(α * A * S ^ 2)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left b2
              (mul_nonneg (mul_nonneg zero_le_three hM2) (sq_nonneg _))
        have t3 : nB * (K₃ * Real.exp (-(c * A / 2 * S ^ 2))) ≤
            K₃ * nB ^ 2 * Real.exp (-(cc * S ^ 2)) := by
          calc nB * (K₃ * Real.exp (-(c * A / 2 * S ^ 2)))
              = K₃ * nB * Real.exp (-(c * A / 2 * S ^ 2)) := by ring
            _ ≤ K₃ * nB * Real.exp (-(cc * S ^ 2)) :=
                mul_le_mul_of_nonneg_left b3 (mul_nonneg hK₃0 hnB0)
            _ ≤ K₃ * nB ^ 2 * Real.exp (-(cc * S ^ 2)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnB2 hK₃0) hexp0
        have : K * nB ^ 2 * Real.exp (-(cc * S ^ 2)) =
            K₁ * nB ^ 2 * Real.exp (-(cc * S ^ 2)) +
              3 * expMom bd.law.F α ^ 2 * nB ^ 2 * Real.exp (-(cc * S ^ 2)) +
              K₃ * nB ^ 2 * Real.exp (-(cc * S ^ 2)) := by rw [hK]; ring
        rw [this]
        linarith

end CurvatureVariance.Paper.Proofs.Geometry
