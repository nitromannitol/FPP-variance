/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.Profiles
public import IsotropicVariance.Infra.Measurability.SlabTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Passage times between transverse cubes: the slab passage time (end of the proof of Proposition
`prop:profiles`)

At the end of the proof of Proposition `prop:profiles` for `s ≤ N/4`: "For `N` large,
`|v − u| ≤ 5^{1/2} s`, so equation `eq:slab` with `P = S` and `z = 0` adds
`O_1(C log²(2+N)) ≤ O_1(Q_s)`". Pathwise:
`|D(u, v) − |v − u|| ≤ |T(u, v) − |v − u|| + (D(u, v) − T(u, v))`, so with `0 ≤ D − T ≤ C S²` the
supremum for `D` is at most the supremum for `T` plus `C S²`.

The lines-along-`e` bounds of that proof are also derived here from the induction hypothesis
(equation `eq:premise`) and from the parent bound (equation `eq:parent`, as for `N/4 < s ≤ N`), in
absolute value.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os Infra.Slab

variable {m : ℕ}

lemma cubePair_first_subset_set (p : CubePair m) (hs : 0 ≤ p.dist) : p.first ⊆ p.slab.set := by
  rintro _ ⟨x, ⟨hx₀, -⟩, rfl⟩
  exact ⟨x, by simp [hx₀, hs, Paper.CubePair.slab], rfl⟩

lemma cubePair_second_subset_set (p : CubePair m) (hs : 0 ≤ p.dist) :
    p.second ⊆ p.slab.set := by
  rintro _ ⟨x, ⟨hx₀, -⟩, rfl⟩
  exact ⟨x, by simp [hx₀, hs, Paper.CubePair.slab], rfl⟩

/-- `(u, v) ↦ D(u, v)` is continuous on a pair of sets in the slab. -/
lemma continuous_slabTime_on (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) (ω : X.Ω) {I I' : Set (Pt m)} (hI : I ⊆ sl.set) (hI' : I' ⊆ sl.set) :
    Continuous fun q : I × I' => X.slabTime b sl ω q.1 q.2 := by
  have hb0 : 0 ≤ b := upperBound_nonneg X hb ω
  apply LipschitzWith.continuous (K := (2 * b).toNNReal)
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  refine (abs_slabTime_sub_le X hb sl ω (hI q.1.2) (hI' q.2.2) (hI q'.1.2)
    (hI' q'.2.2)).trans ?_
  have h1 : dist (q.1 : Pt m) q'.1 ≤ dist q q' :=
    (Subtype.dist_eq _ _).symm.le.trans (by rw [Prod.dist_eq]; exact le_max_left _ _)
  have h2 : dist (q.2 : Pt m) q'.2 ≤ dist q q' :=
    (Subtype.dist_eq _ _).symm.le.trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  nlinarith only [mul_le_mul_of_nonneg_left h1 hb0, mul_le_mul_of_nonneg_left h2 hb0]

/-- `(u, v) ↦ |D(u, v) − |v − u||` is continuous on a pair of sets in the slab. -/
lemma continuous_abs_slabTime_sub_dist {X : Setting m} {b : ℝ} (hb : X.IsUpperBound b)
    (sl : Slab m) (ω : X.Ω) {I I' : Set (Pt m)} (hI : I ⊆ sl.set) (hI' : I' ⊆ sl.set) :
    Continuous fun q : I × I' => |X.slabTime b sl ω q.1 q.2 - dist (q.1 : Pt m) q.2| := by
  have h1 : Continuous fun q : I × I' => ((q.1 : Pt m), (q.2 : Pt m)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_slabTime_on X hb sl ω hI hI').sub (continuous_dist.comp h1)).abs

/-- **End of the proof of Proposition `prop:profiles` for `s ≤ N/4`**: the profile bound for the
slab passage time from that for `T` and the pathwise slab comparison `0 ≤ D − T ≤ C S²`. -/
theorem profile_slabTime {X : Setting m} {b : ℝ} (hb : X.IsUpperBound b) {Bd : ℝ}
    (hBd : ∀ ω x, X.ρ ω x ≤ Bd) (hBd0 : 0 ≤ Bd) (sl : Slab m) {I I' : Set (Pt m)}
    (hI : I ⊆ sl.set) (hI' : I' ⊆ sl.set) (hIn : I.Nonempty) (hIn' : I'.Nonempty) {R : ℝ} (hR : ∀ u ∈ I, ∀ v ∈ I', dist u v ≤ R)
    {θT θS : ℝ} (hθT : 0 < θT) (hθS : 0 < θS)
    (HT : IsOs X.P 1 θT fun ω => ⨆ (u : I) (v : I'), |X.passTime ω u v - dist (u : Pt m) v|)
    {G : X.Ω → ℝ} (HS : IsOs X.P 1 θS G)
    (hcomp : ∀ ω, ∀ u ∈ I, ∀ v ∈ I', X.slabTime b sl ω u v - X.passTime ω u v ≤ G ω ∧
      0 ≤ X.slabTime b sl ω u v - X.passTime ω u v) :
    IsOs X.P 1 (θT + θS) fun ω =>
      ⨆ (u : I) (v : I'), |X.slabTime b sl ω u v - dist (u : Pt m) v| := by
  have hbddT : ∀ ω, BddAbove (range fun q : I × I' =>
      |X.passTime ω q.1 q.2 - dist (q.1 : Pt m) q.2|) := by
    intro ω
    refine ⟨(Bd + 1) * R, ?_⟩
    rintro _ ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, rfl⟩
    have h1 := passTime_le_mul_dist hBd hBd0 ω u v
    have h0 := passTime_nonneg ω u v
    have hd := hR u hu v hv
    have hd0 := dist_nonneg (x := u) (y := v)
    simp only
    rw [abs_le]
    constructor <;> nlinarith
  have hbddD : ∀ ω, BddAbove (range fun q : I × I' =>
      |X.slabTime b sl ω q.1 q.2 - dist (q.1 : Pt m) q.2|) := by
    intro ω
    have hb0 : 0 ≤ b := upperBound_nonneg X hb ω
    refine ⟨(b + 1) * R, ?_⟩
    rintro _ ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, rfl⟩
    have h1 := slabTime_le_mul_dist X hb sl ω (hI hu) (hI' hv)
    have h0 := slabTime_nonneg X b sl ω u v
    have hd := hR u hu v hv
    have hd0 := dist_nonneg (x := u) (y := v)
    simp only
    rw [abs_le]
    constructor <;> nlinarith
  have hmeas : AEMeasurable (fun ω => ⨆ (u : I) (v : I'),
      |X.slabTime b sl ω u v - dist (u : Pt m) v|) X.P :=
    aemeasurable_iSup₂_of_continuous (continuous_abs_slabTime_sub_dist hb sl · hI hI') hbddD
      fun u v => continuous_abs.measurable.comp_aemeasurable
        ((aemeasurable_slabTime X hb sl u v).sub_const _)
  refine IsOs.mono (isOs_add HT HS hθT hθS) zero_le_one (by positivity) hmeas
    (ae_of_all _ fun ω => ?_)
  have : Nonempty I := hIn.to_subtype
  have : Nonempty I' := hIn'.to_subtype
  refine ciSup_le fun ⟨u, hu⟩ => ciSup_le fun ⟨v, hv⟩ => ?_
  obtain ⟨hc1, hc2⟩ := hcomp ω u hu v hv
  have hT : |X.passTime ω u v - dist u v| ≤
      ⨆ (u : I) (v : I'), |X.passTime ω u v - dist (u : Pt m) v| := by
    rw [iSup_iSup_eq_iSup_prod (hbddT ω)]
    exact le_ciSup (f := fun q : I × I' => |X.passTime ω q.1 q.2 - dist (q.1 : Pt m) q.2|)
      (hbddT ω) (⟨u, hu⟩, ⟨v, hv⟩)
  simp only
  have := abs_sub_le (X.slabTime b sl ω u v) (X.passTime ω u v) (dist u v)
  rw [abs_of_nonneg hc2] at this
  linarith

/-! ## Lines along `e`: the induction hypothesis and the parent bound, in absolute value -/

theorem lineAbs_of_premise {X : Setting m} (hm : 1 ≤ m) {K : ℕ} {A N : ℝ}
    (hP : Premise X K A N) (p q : Pt m) (h1 : 1 ≤ dist p q) (h2 : dist p q ≤ N / 2) :
    IsOs X.P 1 (Q K A (dist p q)) fun ω => |X.passTime ω p q - dist p q| :=
  isOs_passTime_of_TRV hm (f := fun y => |y - dist p q|) (by fun_prop) p q (hP _ h1 h2)

theorem lineAbs_of_parent {X : Setting m} (hm : 1 ≤ m) {K : ℕ} (hK : 10 ≤ K) {A C : ℝ}
    (hA : 1 ≤ A) (hC : 0 ≤ C) {lo hi : ℝ}
    (hpar : ∀ ℓ : ℝ, lo ≤ ℓ → ℓ ≤ hi →
      IsOs X.P 1 (Q K A ℓ / 100) fun ω => |X.TRV ℓ ω - ℓ| - C * Q K A ℓ)
    (p q : Pt m) (h0 : 1 ≤ dist p q) (h1 : lo ≤ dist p q) (h2 : dist p q ≤ hi) :
    IsOs X.P 1 (parentStepConst C * Q K A (dist p q)) fun ω => |X.passTime ω p q - dist p q| := by
  set ℓ := dist p q with hℓ
  have hQ : 1 ≤ Q K A ℓ := one_le_Q hK hA h0
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have H := isOs_passTime_of_TRV hm (f := fun y => |y - ℓ| - C * Q K A ℓ)
    (by fun_prop) p q (hpar ℓ h1 h2)
  have H2 := isOs_add_const H (by positivity) (mul_nonneg hC (by linarith) : 0 ≤ C * Q K A ℓ)
  have hpos : 0 < Q K A ℓ / 100 + (C * Q K A ℓ + 1) / Real.log 2 := by positivity
  refine (IsOs.mono H2 zero_le_one hpos
    (continuous_abs.measurable.comp_aemeasurable ((aemeasurable_passTime p q).sub_const _))
    (ae_of_all _ fun ω => ?_)).mono_scale zero_le_one hpos ?_
  · simp only [Function.comp_apply]; linarith
  · unfold parentStepConst
    have : (C * Q K A ℓ + 1) / Real.log 2 ≤ (C + 1) / Real.log 2 * Q K A ℓ := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by nlinarith) hl.le
    nlinarith

lemma one_le_parentStepConst {C : ℝ} (hC : 0 ≤ C) : 1 ≤ parentStepConst C := by
  unfold parentStepConst
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num); linarith
  have : 1 ≤ (C + 1) / Real.log 2 := by rw [le_div_iff₀ hl]; linarith
  linarith

lemma Q_le_two_mul {K : ℕ} (hK : 10 ≤ K) {A ℓ s : ℝ} (hA : 0 ≤ A) (hs : 0 < s) (hℓ : 0 ≤ ℓ)
    (hℓs : ℓ ≤ 2 * s) : Q K A ℓ ≤ 2 * Q K A s := by
  refine (Q_mono hK hA hℓ hℓs).trans ?_
  have h := Q_le_sqrt_mul (K := K) hA hs (show s ≤ 2 * s by linarith)
  have h2 : (2 * s / s) ^ (1 / 2 : ℝ) ≤ 2 := by
    rw [mul_div_assoc, div_self hs.ne', mul_one]
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  nlinarith [Q_nonneg (K := K) hA hs.le]

end IsotropicVariance.Paper.Proofs.Profiles
