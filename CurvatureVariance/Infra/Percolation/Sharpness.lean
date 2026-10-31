/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Monotonicity
public import CurvatureVariance.Infra.Percolation.Decay
public import CurvatureVariance.Infra.Percolation.Transitive
public import CurvatureVariance.Infra.Percolation.Differential
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Sharpness of the phase transition

H. Duminil-Copin and V. Tassion, *A new proof of the sharpness of the phase transition for
Bernoulli percolation on `ℤ^d`* (arXiv:1502.03051v1),
on a countable, locally finite, connected graph `G` with root `o`; vertex-transitivity
(`∀ v, ∃ g : G ≃g G, g o = v`) is assumed where their translation invariance is used.

* `le_percolationProb_mean_field`: for `p̃_c < p < 1`, `θ(p) ≥ (p - p̃_c)/(p (1 - p̃_c))`
  ([DC-T, §2.2], Item 2 for `p̃_c`); no transitivity. Hence `p_c ≤ p̃_c`
  (`criticalProb_le_phiCriticalProb`).
* `exists_armProb_le_exp_of_lt_phiCriticalProb`: for `p < p̃_c`, `P_p(o ↔ distance n) ≤ e^{-cn}`
  for every `n ≥ 1` ([DC-T, §2.1], Item 1 for `p̃_c`); transitive graphs.
* `phiCriticalProb_eq_criticalProb`: `p̃_c = p_c` ([DC-T, Theorem 1.1], first assertion).
* `exists_armProb_le_exp`: **[DC-T, Theorem 1.1(1)]**, exponential decay for `p < p_c`.
* `inv_degree_le_criticalProb`: `1/deg(o) ≤ p_c` ([DC-T, Remark 4]; `1/(2d)` on `ℤ^d`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Countable V] [G.LocallyFinite] {o : V}

/-! ### Above `p̃_c`: the mean-field lower bound -/

omit [Countable V] in
/-- Above `p̃_c`, every finite set containing `o` has `φ_p(S) ≥ 1`. -/
theorem one_le_phi_of_phiCriticalProb_lt {p : I} (hp : phiCriticalProb G o < p) (S : Finset V)
    (hoS : o ∈ S) : 1 ≤ phi G p o S :=
  not_lt.1 fun h => absurd (le_sSup_image_val (s := {p : I | ∃ S : Finset V, o ∈ S ∧ phi G p o S < 1})
    ⟨S, hoS, h⟩) (not_le.2 hp)

/-- The mean-field lower bound with any `q ∈ (p̃_c, p]` in place of `p̃_c`. -/
theorem le_percolationProb_of_lt (hG : G.Connected) {q : ℝ} {p : I}
    (hq : phiCriticalProb G o < q) (hqp : q ≤ p) (hp1 : (p : ℝ) < 1) :
    ENNReal.ofReal ((p - q) / (p * (1 - q))) ≤ percolationProb G o p := by
  rw [percolationProb_eq]
  exact le_percolation_infinite hG ((phiCriticalProb_mem_Icc G o).1.trans_lt hq) hqp hp1
    fun p' hqp' _ S hoS => one_le_phi_of_phiCriticalProb_lt (hq.trans hqp') S hoS

/-- **The mean-field lower bound** ([Duminil-Copin and Tassion, Theorem 1.1(2)] for `p̃_c`, proved
in §2.2): for `p̃_c < p < 1`, `θ(p) ≥ (p - p̃_c)/(p (1 - p̃_c))`. -/
theorem le_percolationProb_mean_field (hG : G.Connected) {p : I}
    (hp : phiCriticalProb G o < p) (hp1 : (p : ℝ) < 1) :
    ENNReal.ofReal ((p - phiCriticalProb G o) / (p * (1 - phiCriticalProb G o))) ≤
      percolationProb G o p := by
  set pc := phiCriticalProb G o
  have hcont : ContinuousAt (fun q : ℝ => ENNReal.ofReal ((p - q) / (p * (1 - q)))) pc := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    refine ContinuousAt.div (continuousAt_const.sub continuousAt_id)
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) ?_
    have : 0 < (p : ℝ) := (phiCriticalProb_mem_Icc G o).1.trans_lt hp
    have : 0 < 1 - pc := by linarith
    positivity
  refine le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi pc))) ?_
  filter_upwards [Ioo_mem_nhdsGT hp] with q hq
  exact le_percolationProb_of_lt hG hq.1 hq.2.le hp1

/-- The mean-field bound is positive above `p̃_c`. -/
theorem percolationProb_pos_of_phiCriticalProb_lt (hG : G.Connected) {p : I}
    (hp : phiCriticalProb G o < p) : 0 < percolationProb G o p := by
  set pc := phiCriticalProb G o
  have hpc0 : 0 ≤ pc := (phiCriticalProb_mem_Icc G o).1
  -- a parameter strictly between `p̃_c` and `min p 1` with `p' < 1`
  set p' : ℝ := (pc + p) / 2
  have hp'1 : p' < 1 := by
    have := p.2.2; simp only [p']; linarith
  have hp'p : p' ≤ p := by simp only [p']; linarith
  have hpcp' : pc < p' := by simp only [p']; linarith
  set p'I : I := ⟨p', by linarith, hp'1.le⟩
  have hpos : 0 < ENNReal.ofReal ((p' - pc) / (p' * (1 - pc))) := by
    rw [ENNReal.ofReal_pos]
    have : 0 < 1 - pc := by linarith
    have : 0 < p' := by linarith
    have : 0 < p' - pc := by linarith
    positivity
  exact (hpos.trans_le (le_percolationProb_mean_field (p := p'I) hG hpcp' hp'1)).trans_le
    (monotone_percolationProb hG o (show p'I ≤ p from hp'p))

/-- **`p_c ≤ p̃_c`.** -/
theorem criticalProb_le_phiCriticalProb (hG : G.Connected) :
    criticalProb G o ≤ phiCriticalProb G o := by
  refine Real.sSup_le ?_ (phiCriticalProb_mem_Icc G o).1
  rintro _ ⟨p, hp, rfl⟩
  by_contra h
  exact (percolationProb_pos_of_phiCriticalProb_lt hG (not_le.1 h)).ne' hp

/-! ### Below `p̃_c` on transitive graphs -/

/-- Below `p̃_c`, some finite set containing `o` has `φ_p(S) < 1` (since `φ_p(S)` increases with
`p`). -/
theorem exists_phi_lt_one_of_lt_phiCriticalProb {p : I} (hp : (p : ℝ) < phiCriticalProb G o) :
    ∃ S : Finset V, o ∈ S ∧ phi G p o S < 1 := by
  have hne : (Subtype.val '' {p : I | ∃ S : Finset V, o ∈ S ∧ phi G p o S < 1}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : phiCriticalProb G o = 0 := by rw [phiCriticalProb, h, Real.sSup_empty]
    have := p.2.1
    linarith
  obtain ⟨_, ⟨p', ⟨S, hoS, hS⟩, rfl⟩, hpp'⟩ := exists_lt_of_lt_csSup hne hp
  exact ⟨S, hoS, (monotone_phi o S (show p ≤ p' from hpp'.le)).trans_lt hS⟩

variable (htrans : ∀ v, ∃ g : G ≃g G, g o = v)
include htrans

/-- On a transitive graph, a set `S ∋ o` gives every vertex a set of the same size, radius and
`φ`. -/
theorem uniform_phi {p : I} {S : Finset V} (hoS : o ∈ S) (v : V) :
    ∃ T : Finset V, v ∈ T ∧ (∀ z ∈ T, G.dist v z < S.sup (G.dist o ·) + 1) ∧
      T.card ≤ S.card ∧ phi G p v T ≤ phi G p o S := by
  obtain ⟨g, rfl⟩ := htrans v
  refine ⟨S.map g.toEquiv.toEmbedding, Finset.mem_map_of_mem _ hoS, ?_, (Finset.card_map _).le,
    (phi_map g p o S).le⟩
  intro z hz
  obtain ⟨z, hzS, rfl⟩ := Finset.mem_map.1 hz
  change G.dist (g o) (g z) < _
  rw [dist_map g o z]
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun x => G.dist o x) hzS)

/-- On a transitive graph, the arm to distance one has probability `< 1` when `p < 1`. -/
theorem iSup_percolation_armEvent_one_lt {p : I} (hp : (p : ℝ) < 1) :
    (⨆ v, percolation G p (armEvent G v 1)) < 1 := by
  have hbound : percolation G p (armEvent G o 1) < 1 := by
    refine (percolation_armEvent_one_le p o).trans_lt ?_
    have hpos : 0 < ENNReal.ofReal ((1 - p) ^ G.degree o) := by
      rw [ENNReal.ofReal_pos]; exact pow_pos (by linarith) _
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
  refine lt_of_le_of_lt (iSup_le fun v => ?_) hbound
  obtain ⟨g, rfl⟩ := htrans v
  rw [percolation_armEvent_map]

/-- **Exponential decay below `p̃_c`** ([Duminil-Copin and Tassion, Theorem 1.1(1)] for `p̃_c`,
proved in §2.1), on a transitive graph. -/
theorem exists_armProb_le_exp_of_lt_phiCriticalProb (hG : G.Connected) {p : I}
    (hp : (p : ℝ) < phiCriticalProb G o) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → armProb G o p n ≤ ENNReal.ofReal (Real.exp (-(c * n))) := by
  obtain ⟨S, hoS, hS⟩ := exists_phi_lt_one_of_lt_phiCriticalProb hp
  have hp1 : (p : ℝ) < 1 := hp.trans_le (phiCriticalProb_mem_Icc G o).2
  obtain ⟨κ, hκ, h⟩ := exists_percolation_armEvent_le_exp hG p (Nat.le_add_left 1 _) hS
    (fun v => let ⟨T, hvT, hT, _, hφ⟩ := uniform_phi htrans hoS v; ⟨T, hvT, hT, hφ⟩)
    (iSup_percolation_armEvent_one_lt htrans hp1)
  exact ⟨κ, hκ, fun n hn => (armProb_eq p n).trans_le (h o n hn)⟩

/-- Exponential decay forces `θ(p) = 0`. -/
theorem percolationProb_eq_zero_of_lt_phiCriticalProb (hG : G.Connected) {p : I}
    (hp : (p : ℝ) < phiCriticalProb G o) : percolationProb G o p = 0 := by
  obtain ⟨c, hc, h⟩ := exists_armProb_le_exp_of_lt_phiCriticalProb htrans hG hp
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(c * n)))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hc))
  refine le_antisymm (ge_of_tendsto ht ?_) zero_le
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (percolationProb_le_armProb hG o p n).trans (h n hn)

/-- **`p̃_c ≤ p_c`**, on a transitive graph. -/
theorem phiCriticalProb_le_criticalProb (hG : G.Connected) :
    phiCriticalProb G o ≤ criticalProb G o := by
  by_contra h
  rw [not_le] at h
  set p' : ℝ := (criticalProb G o + phiCriticalProb G o) / 2
  have h0 := (criticalProb_mem_Icc G o).1
  have h1 := (phiCriticalProb_mem_Icc G o).2
  have hp'0 : 0 ≤ p' := by simp only [p']; linarith
  have hp'1 : p' ≤ 1 := by simp only [p']; linarith
  have hlt : p' < phiCriticalProb G o := by simp only [p']; linarith
  have hgt : criticalProb G o < p' := by simp only [p']; linarith
  set pI : I := ⟨p', hp'0, hp'1⟩
  have := le_sSup_image_val (s := {p : I | percolationProb G o p = 0}) (p := pI)
    (percolationProb_eq_zero_of_lt_phiCriticalProb htrans hG hlt)
  exact absurd this (not_le.2 hgt)

/-- **`p̃_c = p_c`** ([Duminil-Copin and Tassion, Theorem 1.1], first assertion), on a transitive
graph. -/
theorem phiCriticalProb_eq_criticalProb (hG : G.Connected) :
    phiCriticalProb G o = criticalProb G o :=
  le_antisymm (phiCriticalProb_le_criticalProb htrans hG) (criticalProb_le_phiCriticalProb hG)

/-- **[Duminil-Copin and Tassion, Theorem 1.1(1)]**: for `p < p_c`, there is `c > 0` such that
`P_p(o ↔ distance n) ≤ e^{-cn}` for every `n ≥ 1`. -/
theorem exists_armProb_le_exp (hG : G.Connected) {p : I} (hp : (p : ℝ) < criticalProb G o) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → armProb G o p n ≤ ENNReal.ofReal (Real.exp (-(c * n))) :=
  exists_armProb_le_exp_of_lt_phiCriticalProb htrans hG
    (hp.trans_eq (phiCriticalProb_eq_criticalProb htrans hG).symm)

omit htrans [Countable V] in
/-- `φ_p({o}) = p deg(o)`. -/
theorem phi_singleton (p : I) : phi G p o {o} = p * G.degree o := by
  have hP : (percolation G p {ω | OpenConnected G ω (edgesWithin ({o} : Set V)) o o}).toReal = 1 := by
    have : {ω : G.edgeSet → Bool | OpenConnected G ω (edgesWithin ({o} : Set V)) o o} = Set.univ :=
      Set.eq_univ_of_forall fun ω => OpenConnected.refl _ _ _
    rw [this, measure_univ, ENNReal.toReal_one]
  have hfilter : (G.neighborFinset o).filter (· ∉ ({o} : Finset V)) = G.neighborFinset o := by
    refine Finset.filter_true_of_mem fun y hy => ?_
    rw [Finset.mem_singleton]
    exact fun h => G.ne_of_adj ((G.mem_neighborFinset o y).1 hy) h.symm
  simp only [phi, Finset.sum_singleton, hfilter, Finset.coe_singleton, hP, Finset.sum_const,
    nsmul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree]

omit htrans [Countable V] in
/-- `1/deg(o) ≤ p̃_c` ([Duminil-Copin and Tassion, Remark 4]). -/
theorem inv_degree_le_phiCriticalProb : ((G.degree o : ℝ))⁻¹ ≤ phiCriticalProb G o := by
  rcases Nat.eq_zero_or_pos (G.degree o) with h0 | hpos
  · rw [h0, Nat.cast_zero, inv_zero]; exact (phiCriticalProb_mem_Icc G o).1
  by_contra h
  rw [not_le] at h
  have hd : (1 : ℝ) ≤ G.degree o := by exact_mod_cast hpos
  set p' : ℝ := (phiCriticalProb G o + (G.degree o : ℝ)⁻¹) / 2
  have h0 := (phiCriticalProb_mem_Icc G o).1
  have hinv1 : (G.degree o : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd
  have hp'0 : 0 ≤ p' := by simp only [p']; positivity
  have hp'1 : p' ≤ 1 := by simp only [p']; linarith
  have hlt : p' < (G.degree o : ℝ)⁻¹ := by simp only [p']; linarith
  have hgt : phiCriticalProb G o < p' := by simp only [p']; linarith
  set pI : I := ⟨p', hp'0, hp'1⟩
  have hφ : phi G pI o {o} < 1 := by
    rw [phi_singleton]
    have hdpos : (0 : ℝ) < G.degree o := by linarith
    calc (p' : ℝ) * G.degree o < (G.degree o : ℝ)⁻¹ * G.degree o :=
          mul_lt_mul_of_pos_right hlt hdpos
      _ = 1 := inv_mul_cancel₀ hdpos.ne'
  have := le_sSup_image_val (s := {p : I | ∃ S : Finset V, o ∈ S ∧ phi G p o S < 1}) (p := pI)
    ⟨{o}, Finset.mem_singleton_self o, hφ⟩
  exact absurd this (not_le.2 hgt)

/-- **`1/deg(o) ≤ p_c`** on a transitive graph (`1/(2d) ≤ p_c(d)` on `ℤ^d`). -/
theorem inv_degree_le_criticalProb (hG : G.Connected) :
    ((G.degree o : ℝ))⁻¹ ≤ criticalProb G o :=
  inv_degree_le_phiCriticalProb.trans_eq (phiCriticalProb_eq_criticalProb htrans hG)

end CurvatureVariance.Infra.Percolation
