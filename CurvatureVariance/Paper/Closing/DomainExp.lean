/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Closing
import CurvatureVariance.Paper.Closing.Induction
import CurvatureVariance.Paper.Proofs.Responses.TargetBounds

/-!
# The closing: equation `eq:premise` at every length

The second and third sentences of the proof of Theorem `thm:main`:

* for integers `1 ≤ s < N₀` and `y ∈ 𝒟(s)`, the bound in equation `eq:premise` holds once `A` is
  large, depending on `K`, by the base case. These points lie in a finite box, since
  `|y| ≤ |y − s t₀| + s |t₀| ≤ N₁ (1 + T)` for the bound `T` of `|t₀|`;
* by Proposition `prop:induction` and induction on `N`, it holds for every integer `s ≥ 1`.

`domainExpStatement` proves `Contracts.DomainExpStatement` from
`Contracts.ImprovementAllKStatement` and `Contracts.BaseCaseStatement`. The box, `θ` and `A` are
chosen from the bounds and `K`, before the model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Closing

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts

/-- **Equation `eq:premise` at every length** (the second and third sentences of the proof of
Theorem `thm:main`). -/
theorem domainExpStatement {m : ℕ} (hI : ImprovementAllKStatement m)
    (hB : BaseCaseStatement m) : DomainExpStatement m := by
  intro bd hbd
  obtain ⟨K₀, hstep⟩ := hI bd hbd
  choose θ hθpos hθ using fun x => hB bd hbd x
  refine ⟨K₀, fun K hK₀ hK => ?_⟩
  obtain ⟨N₁, hstep⟩ := hstep K hK₀ hK
  set e : ℝ := 1 / 2 - bd.law.δ / K with he
  -- the finite box of base cases: `|y_j| ≤ |y − s t₀| + s |t₀| ≤ N₁ (1 + T)`
  classical
  set R : ℤ := ⌈(N₁ : ℝ) * (1 + bd.T)⌉ with hRdef
  let box : Finset (Vertex m) :=
    Finset.Icc (0 : ℤ) N₁ ×ˢ Fintype.piFinset fun _ => Finset.Icc (-R) R
  set A : ℝ := 1 + ∑ x ∈ box, θ x / (x.1 : ℝ) ^ e with hAdef
  have hterm : ∀ x ∈ box, 0 ≤ θ x / (x.1 : ℝ) ^ e := fun x hx => by
    have hx1 : (0 : ℝ) ≤ x.1 := by
      have := (Finset.mem_Icc.1 (Finset.mem_product.1 hx).1).1
      exact_mod_cast this
    exact div_nonneg (hθpos x).le (Real.rpow_nonneg hx1 _)
  have hA1 : 1 ≤ A := by
    have := Finset.sum_nonneg hterm
    linarith
  refine ⟨A, hA1, fun M hMs hfit => ?_⟩
  have hMδ : M.δ = bd.law.δ := hfit.δ_eq
  have hexp_le_one : (3 : ℝ) / 4 + M.δ / 100 ≤ 1 := by
    have := hMs.delta_le_one
    linarith
  have hbase : ∀ n : ℕ, 1 ≤ n → n < N₁ → ∀ y ∈ premiseDomain M n,
      θ ((n : ℤ), y) ≤ Q M K A n := by
    intro n hn1 hnN y hy
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hmem : ((n : ℤ), y) ∈ box := by
      refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨show (0 : ℤ) ≤ n by positivity,
        show (n : ℤ) ≤ N₁ by exact_mod_cast hnN.le⟩, ?_⟩
      refine Fintype.mem_piFinset.2 fun j => Finset.mem_Icc.2 ?_
      have hnN' : (n : ℝ) ≤ N₁ := by exact_mod_cast hnN.le
      have hrad : (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) ≤ n :=
        calc (n : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) ≤ (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hexp_le_one
          _ = n := Real.rpow_one _
      have hnorm : ‖transversePoint y‖ ≤ (N₁ : ℝ) * (1 + bd.T) := by
        have h1 : ‖transversePoint y‖ ≤ ‖transversePoint y - (n : ℝ) • M.t₀‖ +
            ‖(n : ℝ) • M.t₀‖ := norm_le_norm_sub_add _ _
        rw [norm_smul, Real.norm_of_nonneg hnpos.le] at h1
        have h2 : ‖transversePoint y - (n : ℝ) • M.t₀‖ ≤ n := le_trans hy hrad
        have hT := hfit.t₀_le
        nlinarith [norm_nonneg M.t₀]
      have hyj : |(y j : ℝ)| ≤ R :=
        ((Responses.abs_coord_le_norm_transversePoint y j).trans hnorm).trans (Int.le_ceil _)
      have := abs_le.1 hyj
      constructor
      · have h' : ((-R : ℤ) : ℝ) ≤ y j := by push_cast; exact this.1
        exact_mod_cast h'
      · have h' : (y j : ℝ) ≤ (R : ℝ) := this.2
        exact_mod_cast h'
    have hle : θ ((n : ℤ), y) / ((n : ℤ) : ℝ) ^ e ≤ A := by
      have := Finset.single_le_sum hterm hmem
      linarith
    have hpe : 0 < ((n : ℤ) : ℝ) ^ e := Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _
    rw [div_le_iff₀ hpe] at hle
    simpa [Q, he, hMδ, Int.cast_natCast] using hle
  -- strong induction
  have hall : ∀ N : ℕ, 1 ≤ N → ∀ y ∈ premiseDomain M N,
      IsAbsOs M.P 1 (Q M K A N)
        (fun ω => passageTimeReal ω 0 ((N : ℤ), y) - M.μ.1 (point ((N : ℤ), y))) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro hN y hy
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      by_cases hlt : N < N₁
      · exact IsAbsOs.mono_scale (hθ ((N : ℤ), y) M hMs hfit) zero_le_one (hθpos _)
          (hbase N hN hlt y hy)
      · have hprem : Premise M K A N := by
          intro s hs1 hs2 y' hy'
          have hsN : s < N := by
            have : (s : ℝ) < N := by linarith
            exact_mod_cast this
          exact ih s hsN hs1 y' hy'
        have h := hstep M hMs hfit N (not_lt.1 hlt) A hA1 hprem y hy
        have hQ := Q_pos M K hA1 hNpos
        exact IsAbsOs.mono_scale h zero_le_one (by linarith) (by linarith)
  exact fun N s hs1 _ y hy => hall s hs1 y hy

end CurvatureVariance.Paper.Closing
