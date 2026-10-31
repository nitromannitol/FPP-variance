/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! # The deterministic doubling lemma of Howard and Newman

Howard and Newman, Lemma 4.2, p. 611, by their proof: for `c > 1/(2 − ψ)`, the function
`ã(L) = a(L) − c g(L)` satisfies `ã(2L) ≥ 2ã(L)` for all large `L`. Iterating gives
`ã(L)/L ≤ ã(2ⁿL)/(2ⁿL)`, and `ã(x)/x → ν` as `x → ∞` gives `ã(L)/L ≤ ν`.

The ratio hypothesis is the eventual doubling estimate `g(2L) ≤ ψ g(L)` for a number `ψ < 2`, and
the doubling inequality of `a` is required only for large `L`.
-/

@[expose] public section
open Filter
open scoped Topology
namespace IsotropicVariance.Infra.Subadditive

/-- A function that is superadditive under doubling from a positive scale on is bounded above by
its linear-growth limit from that scale on. -/
theorem le_mul_limit_of_doubling_real (b : ℝ → ℝ) (ν : ℝ)
    (hb : Tendsto (fun L => b L / L) atTop (𝓝 ν)) (L₀ : ℝ) (hL₀ : 0 < L₀)
    (hDouble : ∀ L, L₀ ≤ L → 2 * b L ≤ b (2 * L)) :
    ∀ L, L₀ ≤ L → b L ≤ ν * L := by
  intro L hL
  have hLpos : 0 < L := hL₀.trans_le hL
  have hstep (M : ℝ) (hM : L₀ ≤ M) : b M / M ≤ b (2 * M) / (2 * M) := by
    have hMpos : 0 < M := hL₀.trans_le hM
    rw [div_le_div_iff₀ hMpos (mul_pos two_pos hMpos)]
    have hh := mul_le_mul_of_nonneg_right (hDouble M hM) hMpos.le
    linarith only [hh]
  have hge (n : ℕ) : L ≤ 2 ^ n * L :=
    le_mul_of_one_le_left hLpos.le (one_le_pow₀ one_le_two)
  have hIter (n : ℕ) : b L / L ≤ b (2 ^ n * L) / (2 ^ n * L) := by
    induction n with
    | zero => simp only [pow_zero, one_mul, le_refl]
    | succ n ih =>
      have hh := ih.trans (hstep (2 ^ n * L) (hL.trans (hge n)))
      rwa [← mul_assoc, ← pow_succ'] at hh
  have hIndex : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * L) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const hLpos
  have hle : b L / L ≤ ν := ge_of_tendsto (hb.comp hIndex) (Eventually.of_forall hIter)
  exact (div_le_iff₀ hLpos).mp hle

/-- Howard and Newman, Lemma 4.2, with exactly the binders and carriers of the theorem
`IsotropicVariance.Cited.hn_lemma4_2`. -/
theorem hn_lemma4_2 (a g : ℝ → ℝ) (ν : ℝ) (hg : ∀ L, 0 < L → 0 ≤ g L)
    (ha : Tendsto (fun L => a L / L) atTop (𝓝 ν))
    (hgo : Tendsto (fun L => g L / L) atTop (𝓝 0))
    (hdouble : ∀ᶠ L in atTop, 2 * a L - g L ≤ a (2 * L))
    (ψ : ℝ) (hψ : ψ < 2) (hψg : ∀ᶠ L in atTop, g (2 * L) ≤ ψ * g L)
    (c : ℝ) (hc : 1 / (2 - ψ) < c) :
    ∀ᶠ L in atTop, a L ≤ ν * L + c * g L := by
  have hgap : 0 < 2 - ψ := sub_pos.mpr hψ
  have hc1 : 1 < c * (2 - ψ) := (div_lt_iff₀ hgap).mp hc
  have hc0 : 0 < c := (one_div_pos.mpr hgap).trans hc
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp (hdouble.and hψg)
  have hL₀ : 0 < max L₁ 1 := lt_of_lt_of_le one_pos (le_max_right L₁ 1)
  let b := fun L => a L - c * g L
  have hb : Tendsto (fun L => b L / L) atTop (𝓝 ν) := by
    have hh := ha.sub (hgo.const_mul c)
    simp only [mul_zero, sub_zero] at hh
    simpa only [b, sub_div, mul_div_assoc] using hh
  have hDouble (L : ℝ) (hL : max L₁ 1 ≤ L) : 2 * b L ≤ b (2 * L) := by
    obtain ⟨h2a, h2g⟩ := hL₁ L ((le_max_left L₁ 1).trans hL)
    have hcg := mul_le_mul_of_nonneg_left h2g hc0.le
    have hgL := mul_nonneg (sub_pos.mpr hc1).le (hg L (hL₀.trans_le hL))
    dsimp only [b]
    linarith only [h2a, hcg, hgL]
  filter_upwards [eventually_ge_atTop (max L₁ 1)] with L hL
  have hh := le_mul_limit_of_doubling_real b ν hb (max L₁ 1) hL₀ hDouble L hL
  dsimp only [b] at hh
  linarith only [hh]

end IsotropicVariance.Infra.Subadditive
