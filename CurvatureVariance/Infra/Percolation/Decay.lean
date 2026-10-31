/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Infra.Percolation.Exploration
public import CurvatureVariance.Infra.Percolation.Balls

/-!
# Exponential decay from a uniform `φ` bound

Duminil-Copin and Tassion (*A new proof of the sharpness of the phase transition for Bernoulli
percolation on `ℤ^d`*, arXiv:1502.03051, §2.1). If for every vertex `v` there is a finite set
`S ∋ v` of radius `< L` with `φ_p(S) ≤ c`, then the one-arm probabilities contract by the factor
`c` every `L` steps (`iSup_percolation_armEvent_add_le`), whence exponential decay
(`exists_percolation_armEvent_le_exp`) once the arm probability to distance one is `< 1`
(`percolation_armEvent_one_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Countable V] [G.LocallyFinite]

/-! ### The contraction step -/

/-- **One step of the exploration**: with a uniform `φ` bound at radius `L`, the arm probability
at distance `n + L` is at most `c` times the largest arm probability at distance `n`. -/
theorem iSup_percolation_armEvent_add_le (hG : G.Connected) (p : unitInterval) {L : ℕ} {c : ℝ}
    (hS : ∀ v, ∃ S : Finset V, v ∈ S ∧ (∀ z ∈ S, G.dist v z < L) ∧ phi G p v S ≤ c) (n : ℕ) :
    (⨆ v, percolation G p (armEvent G v (n + L))) ≤
      ENNReal.ofReal c * ⨆ v, percolation G p (armEvent G v n) := by
  refine iSup_le fun v => ?_
  obtain ⟨S, hvS, hSd, hφ⟩ := hS v
  have ha : ∀ x ∈ S, ∀ y, G.Adj x y → y ∉ S →
      percolation G p {ω | ∃ w ∈ {w | n + L ≤ G.dist v w}, OpenConnected G ω Set.univ y w} ≤
        ⨆ u, percolation G p (armEvent G u n) := by
    intro x hx y hxy _
    refine le_iSup_of_le y (measure_mono ?_)
    rintro ω ⟨w, hw, hc⟩
    exact ⟨w, le_dist_of_le_dist hG (dist_le_of_adj_of_dist_lt hG hxy (hSd x hx)) hw, hc⟩
  have h := measure_exists_openConnected_le_phi (G := G) hvS
    (W := {w | n + L ≤ G.dist v w})
    (fun w hw hwS => by
      have := hSd w hwS
      simp only [Set.mem_ofPred_eq] at hw
      omega) p ha
  exact h.trans (by gcongr)

theorem iSup_percolation_armEvent_mul_add_le (hG : G.Connected) (p : unitInterval) {L : ℕ}
    {c : ℝ} (hS : ∀ v, ∃ S : Finset V, v ∈ S ∧ (∀ z ∈ S, G.dist v z < L) ∧ phi G p v S ≤ c)
    (j m : ℕ) :
    (⨆ v, percolation G p (armEvent G v (j * L + m))) ≤
      ENNReal.ofReal c ^ j * ⨆ v, percolation G p (armEvent G v m) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have : (j + 1) * L + m = (j * L + m) + L := by ring
    rw [this]
    calc _ ≤ ENNReal.ofReal c * ⨆ v, percolation G p (armEvent G v (j * L + m)) :=
          iSup_percolation_armEvent_add_le hG p hS _
      _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c ^ j * ⨆ v, percolation G p (armEvent G v m)) :=
          by gcongr
      _ = _ := by rw [pow_succ', mul_assoc]

/-! ### Exponential decay -/

/-- **Exponential decay from a uniform `φ` bound** ([Duminil-Copin and Tassion, §2.1]), in the
form `≤ e^{-κ n}` for every `n ≥ 1`. -/
theorem exists_percolation_armEvent_le_exp (hG : G.Connected) (p : unitInterval) {L : ℕ}
    (hL : 1 ≤ L) {c : ℝ} (hc : c < 1)
    (hS : ∀ v, ∃ S : Finset V, v ∈ S ∧ (∀ z ∈ S, G.dist v z < L) ∧ phi G p v S ≤ c)
    (h1 : (⨆ v, percolation G p (armEvent G v 1)) < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ v, ∀ n : ℕ, 1 ≤ n →
      percolation G p (armEvent G v n) ≤ ENNReal.ofReal (Real.exp (-(κ * n))) := by
  set a₁ := ⨆ v, percolation G p (armEvent G v 1) with ha₁
  set q : ℝ := max a₁.toReal (max c 0) with hq
  have hq0 : 0 ≤ q := (le_max_right _ _).trans' (le_max_right _ _)
  have hq1 : q < 1 := by
    refine max_lt ?_ (max_lt hc one_pos)
    have := (ENNReal.toReal_lt_toReal (ne_top_of_lt h1) ENNReal.one_ne_top).2 h1
    simpa using this
  have hcq : ENNReal.ofReal c ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal ((le_max_left c 0).trans (le_max_right _ _))
  have haq : a₁ ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_toReal (ne_top_of_lt h1)]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have key : ∀ v j, percolation G p (armEvent G v (j * L + 1)) ≤ ENNReal.ofReal (q ^ (j + 1)) := by
    intro v j
    calc _ ≤ ⨆ v, percolation G p (armEvent G v (j * L + 1)) := le_iSup (fun v =>
            percolation G p (armEvent G v (j * L + 1))) v
      _ ≤ ENNReal.ofReal c ^ j * a₁ := iSup_percolation_armEvent_mul_add_le hG p hS j 1
      _ ≤ ENNReal.ofReal q ^ j * ENNReal.ofReal q := by gcongr
      _ = ENNReal.ofReal (q ^ (j + 1)) := by rw [← pow_succ, ENNReal.ofReal_pow hq0]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have bound : ∀ v n, 1 ≤ n → percolation G p (armEvent G v n) ≤
      ENNReal.ofReal (q ^ ((n - 1) / L + 1)) := by
    intro v n hn
    refine (measure_mono (armEvent_antitone v ?_)).trans (key v _)
    have := Nat.div_mul_le_self (n - 1) L
    omega
  have hnle : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (((n - 1) / L + 1 : ℕ) : ℝ) * L := by
    intro n hn
    have h1 := Nat.div_add_mod (n - 1) L
    have h2 := Nat.mod_lt (n - 1) (show 0 < L by omega)
    have e : ((n - 1) / L + 1) * L = L * ((n - 1) / L) + L := by ring
    have : n ≤ ((n - 1) / L + 1) * L := by omega
    exact_mod_cast this
  rcases hq0.eq_or_lt with h0 | hpos
  · refine ⟨1, one_pos, fun v n hn => (bound v n hn).trans ?_⟩
    rw [← h0, zero_pow (Nat.succ_ne_zero _)]
    simp
  · refine ⟨-Real.log q / L, div_pos (neg_pos.2 (Real.log_neg hpos hq1)) hLpos, fun v n hn => ?_⟩
    refine (bound v n hn).trans (ENNReal.ofReal_le_ofReal ?_)
    set j := (n - 1) / L
    have hlog : Real.log q < 0 := Real.log_neg hpos hq1
    have e1 : q ^ (j + 1) = Real.exp (((j + 1 : ℕ) : ℝ) * Real.log q) := by
      rw [Real.exp_nat_mul, Real.exp_log hpos]
    rw [e1]
    refine Real.exp_le_exp.2 ?_
    have := hnle n hn
    have h3 : Real.log q * (((j + 1 : ℕ) : ℝ) * L) ≤ Real.log q * n :=
      mul_le_mul_of_nonpos_left this hlog.le
    have h4 : -(-Real.log q / L * n) = Real.log q * n / L := by field_simp
    rw [h4, le_div_iff₀ hLpos]
    linarith

/-! ### The arm to distance one -/

section One

omit [Countable V] in
/-- The arm to distance one needs an open edge at `v`. -/
theorem percolation_armEvent_one_le (p : unitInterval) (v : V) :
    percolation G p (armEvent G v 1) ≤ 1 - ENNReal.ofReal ((1 - p) ^ G.degree v) := by
  let f : G.neighborFinset v → G.edgeSet := fun y =>
    ⟨s(v, y.1), (SimpleGraph.mem_edgeSet G).2 ((G.mem_neighborFinset v y.1).1 y.2)⟩
  have hf : Function.Injective f := by
    intro y y' h
    have := congrArg Subtype.val h
    exact Subtype.ext (Sym2.congr_right.1 this)
  let s : Finset G.edgeSet := Finset.univ.image f
  have hcard : s.card = G.degree v := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe,
      G.card_neighborFinset_eq_degree]
  let B : Set (G.edgeSet → Bool) := Set.pi (s : Set G.edgeSet) fun _ => {false}
  have hBm : MeasurableSet B :=
    MeasurableSet.pi (Finset.countable_toSet s) fun _ _ => measurableSet_singleton false
  have hB : percolation G p B = ENNReal.ofReal ((1 - p) ^ G.degree v) := by
    rw [percolation, bernoulliProduct, Measure.infinitePi_pi _ fun _ _ => measurableSet_singleton _]
    simp only [bernoulliMeasure_false, Finset.prod_const, hcard]
    rw [ENNReal.ofReal_pow (sub_nonneg.2 p.2.2)]
  have hsub : armEvent G v 1 ⊆ Bᶜ := by
    rintro ω ⟨w, hw, q, hq⟩ hωB
    cases q with
    | nil => simp at hw
    | @cons _ b _ h q' =>
      rw [isOpenIn_cons] at hq
      have h1 : ω ⟨s(v, b), (SimpleGraph.mem_edgeSet G).2 h⟩ = false := by
        refine hωB ⟨s(v, b), (SimpleGraph.mem_edgeSet G).2 h⟩ ?_
        rw [Finset.mem_coe, Finset.mem_image]
        exact ⟨⟨b, (G.mem_neighborFinset v b).2 h⟩, Finset.mem_univ _, rfl⟩
      have h2 : ω ⟨s(v, b), (SimpleGraph.mem_edgeSet G).2 h⟩ = true := hq.1.2
      rw [h1] at h2
      exact Bool.false_ne_true h2
  calc _ ≤ percolation G p Bᶜ := measure_mono hsub
    _ = _ := by rw [prob_compl_eq_one_sub hBm, hB]

end One

end CurvatureVariance.Infra.Percolation
