/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Statements.Space.PtNorm
public import CurvatureVariance.Infra.FPP.Lattice
import CurvatureVariance.Infra.FPP.MeanDefs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Norms on `ℝ^d` and the time constant on `ℤ^d`

Deterministic facts about norms on the Euclidean space `Pt m = ℝ^d`, `d = m + 1`:

* `PtNorm.exists_bounds`: every norm is equivalent to the Euclidean norm;
* `exists_ptNorm_extend`: a function on the lattice points `ℤ^d` which is subadditive, symmetric,
  homogeneous along `ℕ`-multiples and comparable to the Euclidean norm is the restriction of a
  norm on `ℝ^d` (the sublinear hull `hullFun`);
* `ptNorm_ext_of_point`: two norms agreeing on lattice points are equal.

The norms are those of `PtNorm m`.
-/

@[expose] public section

namespace CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### Equivalence of norms -/

/-- A seminorm on `ℝ^d` is bounded by a multiple of the Euclidean norm. -/
theorem exists_seminorm_le (μ : Seminorm ℝ (Pt m)) :
    ∃ hi : ℝ, 0 < hi ∧ ∀ x : Pt m, μ x ≤ hi * ‖x‖ := by
  let b := Module.finBasis ℝ (Pt m)
  let C : Fin (Module.finrank ℝ (Pt m)) → ℝ := fun i =>
    ‖LinearMap.toContinuousLinearMap (b.coord i)‖
  refine ⟨∑ i, C i * μ (b i) + 1, ?_, fun x => ?_⟩
  · have : 0 ≤ ∑ i, C i * μ (b i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg μ _)
    linarith only [this]
  · have hx : μ x ≤ ∑ i, |b.repr x i| * μ (b i) := by
      conv_lhs => rw [← b.sum_repr x]
      refine (Finset.le_sum_of_subadditive μ (map_zero μ).le (map_add_le_add μ) _ _).trans
        (Finset.sum_le_sum fun i _ => ?_)
      rw [map_smul_eq_mul, Real.norm_eq_abs]
    have hc : ∀ i, |b.repr x i| ≤ C i * ‖x‖ := fun i => by
      have := (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm x
      simpa [C] using this
    calc μ x ≤ ∑ i, |b.repr x i| * μ (b i) := hx
      _ ≤ ∑ i, (C i * ‖x‖) * μ (b i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (apply_nonneg μ _)
      _ = (∑ i, C i * μ (b i)) * ‖x‖ := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (∑ i, C i * μ (b i) + 1) * ‖x‖ := by
          nlinarith only [norm_nonneg x]

/-- Every norm on `ℝ^d` is equivalent to the Euclidean norm. -/
theorem PtNorm.exists_bounds (μ : PtNorm m) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ x : Pt m, lo * ‖x‖ ≤ μ.1 x ∧ μ.1 x ≤ hi * ‖x‖ := by
  obtain ⟨hi, hhi, hle⟩ := exists_seminorm_le μ.1
  have hcont : Continuous μ.1 := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨hi, hhi.le⟩) fun x y => ?_).continuous
    rw [Real.dist_eq, dist_eq_norm]
    calc |μ.1 x - μ.1 y| ≤ μ.1 (x - y) := abs_sub_map_le_sub μ.1 x y
      _ ≤ hi * ‖x - y‖ := hle _
  have hmem : point ((1, 0) : Vertex m) ∈ Metric.sphere (0 : Pt m) 1 := by
    rw [mem_sphere_zero_iff_norm]; exact norm_point_longitudinal
  obtain ⟨x₀, hx₀, hmin⟩ :=
    (isCompact_sphere (0 : Pt m) 1).exists_isMinOn ⟨_, hmem⟩ hcont.continuousOn
  have hn0 : ‖x₀‖ = 1 := by simpa using hx₀
  have hpos : 0 < μ.1 x₀ := by
    refine lt_of_le_of_ne (apply_nonneg _ _) fun h => ?_
    have := μ.2 x₀ h.symm
    rw [this, norm_zero] at hn0; exact zero_ne_one hn0
  refine ⟨μ.1 x₀, hi, hpos, hhi, fun x => ⟨?_, hle x⟩⟩
  by_cases hx : x = 0
  · simp [hx]
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : Pt m) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
    have h1 := hmin hy
    simp only [Set.mem_ofPred_eq] at h1
    rw [map_smul_eq_mul, norm_inv, norm_norm] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hnx.le
    rw [← mul_assoc, mul_inv_cancel₀ hnx.ne', one_mul] at h2
    linarith only [h2]

/-! ### Lattice points -/

/-- Every point of `ℝ^d` is within `m + 1` of a lattice point. -/
theorem exists_point_near (y : Pt m) : ∃ z : Vertex m, ‖point z - y‖ ≤ (m : ℝ) + 1 := by
  refine ⟨(⌊y.fst⌋, fun j => ⌊y.snd j⌋), ?_⟩
  set w : Pt m := point ((⌊y.fst⌋, fun j => ⌊y.snd j⌋) : Vertex m) - y with hw
  have h1 : |w.fst| ≤ 1 := by
    have : w.fst = (⌊y.fst⌋ : ℝ) - y.fst := by simp [hw]
    rw [this, abs_le]
    constructor <;> linarith only [Int.floor_le y.fst, Int.lt_floor_add_one y.fst]
  have h2 : ‖w.snd‖ ^ 2 ≤ m := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ j, ‖w.snd j‖ ^ 2 ≤ ∑ _j : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have : w.snd j = (⌊y.snd j⌋ : ℝ) - y.snd j := by simp [hw]
          rw [this, Real.norm_eq_abs, sq_abs, sq_le_one_iff_abs_le_one, abs_le]
          constructor <;> linarith only [Int.floor_le (y.snd j), Int.lt_floor_add_one (y.snd j)]
      _ = m := by simp
  have h3 : ‖w‖ ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    have : w.fst ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith only [this, h2, hm]
  exact le_of_sq_le_sq h3 (by positivity)

/-- Two norms on `ℝ^d` that agree at the lattice points are equal. -/
theorem ptNorm_ext_of_point {μ μ' : PtNorm m}
    (h : ∀ z : Vertex m, μ.1 (point z) = μ'.1 (point z)) : μ = μ' := by
  obtain ⟨_, hi, _, hhi, hb⟩ := PtNorm.exists_bounds μ
  obtain ⟨_, hi', _, hhi', hb'⟩ := PtNorm.exists_bounds μ'
  refine Subtype.ext (Seminorm.ext fun x => ?_)
  set K : ℝ := (hi + hi') * ((m : ℝ) + 1) with hK
  have hN : ∀ N : ℕ, (N : ℝ) * |μ.1 x - μ'.1 x| ≤ K := fun N => by
    obtain ⟨z, hz⟩ := exists_point_near ((N : ℝ) • x)
    have e1 : |μ.1 ((N : ℝ) • x) - μ.1 (point z)| ≤ hi * ((m : ℝ) + 1) := by
      refine (abs_sub_map_le_sub μ.1 _ _).trans ?_
      calc μ.1 ((N : ℝ) • x - point z) ≤ hi * ‖(N : ℝ) • x - point z‖ := hb _ |>.2
        _ ≤ hi * ((m : ℝ) + 1) := by rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hz hhi.le
    have e2 : |μ'.1 ((N : ℝ) • x) - μ'.1 (point z)| ≤ hi' * ((m : ℝ) + 1) := by
      refine (abs_sub_map_le_sub μ'.1 _ _).trans ?_
      calc μ'.1 ((N : ℝ) • x - point z) ≤ hi' * ‖(N : ℝ) • x - point z‖ := hb' _ |>.2
        _ ≤ hi' * ((m : ℝ) + 1) := by rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hz hhi'.le
    have e3 : (N : ℝ) * |μ.1 x - μ'.1 x| = |μ.1 ((N : ℝ) • x) - μ'.1 ((N : ℝ) • x)| := by
      rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_natCast, ← mul_sub, abs_mul,
        Nat.abs_cast]
    rw [e3]
    have e4 : μ.1 ((N : ℝ) • x) - μ'.1 ((N : ℝ) • x) =
        (μ.1 ((N : ℝ) • x) - μ.1 (point z)) - (μ'.1 ((N : ℝ) • x) - μ'.1 (point z)) := by
      rw [h z]; ring
    rw [e4, hK]
    refine (abs_sub _ _).trans ?_
    linarith only [e1, e2]
  by_contra hne
  have hd : 0 < |μ.1 x - μ'.1 x| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hNK⟩ := exists_nat_gt (K / |μ.1 x - μ'.1 x|)
  have := (div_lt_iff₀ hd).mp hNK
  linarith only [this, hN N]

/-! ### The sublinear hull of a function on the lattice -/

/-- `HullRep g x s` says that `s = ∑ cⱼ g(zⱼ)` for a representation `x = ∑ cⱼ • point zⱼ` of `x`
as a nonnegative combination of lattice points. -/
inductive HullRep (g : Vertex m → ℝ) : Pt m → ℝ → Prop
  | zero : HullRep g 0 0
  | cons {x : Pt m} {s : ℝ} (c : ℝ) (hc : 0 ≤ c) (z : Vertex m) :
      HullRep g x s → HullRep g (c • point z + x) (c * g z + s)

namespace HullRep

variable {g : Vertex m → ℝ} {x y : Pt m} {s t : ℝ}

theorem single (z : Vertex m) : HullRep g (point z) (g z) := by
  simpa using (HullRep.zero (g := g)).cons 1 zero_le_one z

theorem add (hx : HullRep g x s) (hy : HullRep g y t) : HullRep g (x + y) (s + t) := by
  induction hx with
  | zero => simpa using hy
  | cons c hc z _ ih =>
    rw [add_assoc, add_assoc]; exact (ih).cons c hc z

theorem smul {r : ℝ} (hr : 0 ≤ r) (hx : HullRep g x s) : HullRep g (r • x) (r * s) := by
  induction hx with
  | zero => simpa using HullRep.zero
  | cons c hc z _ ih =>
    have := ih.cons (r * c) (mul_nonneg hr hc) z
    convert this using 1
    · rw [smul_add, smul_smul]
    · ring

theorem neg (hneg : ∀ z, g (-z) = g z) (hx : HullRep g x s) : HullRep g (-x) s := by
  induction hx with
  | zero => simpa using HullRep.zero
  | cons c hc z _ ih =>
    have := ih.cons c hc (-z)
    rw [hneg] at this
    convert this using 1
    rw [neg_add, point_neg, smul_neg]

theorem lower {a : ℝ} (ha : 0 ≤ a) (hlo : ∀ z, a * ‖point z‖ ≤ g z) (hx : HullRep g x s) :
    a * ‖x‖ ≤ s := by
  induction hx with
  | zero => simp
  | @cons x' s' c hc z _ ih =>
    have h1 := norm_add_le (c • point z) x'
    rw [norm_smul, Real.norm_of_nonneg hc] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 ha
    have h3 := mul_le_mul_of_nonneg_left (hlo z) hc
    linarith only [h2, h3, ih]

/-- Every point is a nonnegative combination of lattice points. -/
theorem exists_rep (hneg : ∀ z, g (-z) = g z) (x : Pt m) : ∃ s, HullRep g x s := by
  let S : Set (Pt m) := {x | ∃ s, HullRep g x s}
  have hadd : ∀ {x y}, x ∈ S → y ∈ S → x + y ∈ S := fun ⟨s, hs⟩ ⟨t, ht⟩ => ⟨_, hs.add ht⟩
  have hsm : ∀ (r : ℝ) (z : Vertex m), r • point z ∈ S := fun r z => by
    rcases le_total 0 r with hr | hr
    · exact ⟨_, (single z).smul hr⟩
    · have h := ((single z).smul (neg_nonneg.mpr hr)).neg hneg
      exact ⟨_, by rwa [neg_smul, neg_neg] at h⟩
  have hzero : (0 : Pt m) ∈ S := ⟨0, HullRep.zero⟩
  have hnorm : ∀ v : EuclideanSpace ℝ (Fin m), (WithLp.toLp 2 ((0 : ℝ), v) : Pt m) ∈ S :=
      fun v => by
    have hv : v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    have := Finset.sum_induction (s := Finset.univ) (fun j => v j • EuclideanSpace.single j (1 : ℝ))
      (fun u : EuclideanSpace ℝ (Fin m) => (WithLp.toLp 2 ((0 : ℝ), u) : Pt m) ∈ S)
      (fun a b ha hb => by
        have e : (WithLp.toLp 2 ((0 : ℝ), a + b) : Pt m) =
            WithLp.toLp 2 ((0 : ℝ), a) + WithLp.toLp 2 ((0 : ℝ), b) := pt_ext (by simp) (by simp)
        rw [e]; exact hadd ha hb)
      (by
        have e0 : (WithLp.toLp 2 ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) : Pt m) = 0 :=
          pt_ext (by simp) (by simp)
        show _ ∈ S
        rw [e0]; exact hzero)
      (fun j _ => by
        have e : (WithLp.toLp 2 ((0 : ℝ), v j • EuclideanSpace.single j (1 : ℝ)) : Pt m) =
            v j • point ((0, Pi.single j 1) : Vertex m) :=
          pt_ext (by simp) (by simp [transversePoint_single])
        rw [e]; exact hsm _ _)
    rwa [← hv] at this
  have e : x = x.fst • point ((1, 0) : Vertex m) + WithLp.toLp 2 ((0 : ℝ), x.snd) :=
    pt_ext (by simp) (by simp)
  rw [e]
  exact hadd (hsm _ _) (hnorm _)

/-- Approximation of a representation by integer combinations of the lattice points. -/
theorem approx (hsmul : ∀ (n : ℕ) (z : Vertex m), g (n • z) = n * g z)
    (hadd : ∀ z w, g (z + w) ≤ g z + g w) (hg : ∀ z, 0 ≤ g z) (hx : HullRep g x s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∃ w : Vertex m, g w ≤ N * s ∧ ‖(N : ℝ) • x - point w‖ ≤ B := by
  induction hx with
  | zero =>
    refine ⟨0, le_rfl, fun N => ⟨0, ?_, by simp⟩⟩
    have h0 : g 0 = 0 := by simpa using hsmul 0 0
    simp [h0]
  | @cons x' s' c hc z _ ih =>
    obtain ⟨B', hB', hN'⟩ := ih
    refine ⟨‖point z‖ + B', add_nonneg (norm_nonneg _) hB', fun N => ?_⟩
    obtain ⟨w', hw'g, hw'n⟩ := hN' N
    have hNc : (0 : ℝ) ≤ N * c := mul_nonneg (Nat.cast_nonneg N) hc
    set p : ℕ := ⌊(N : ℝ) * c⌋₊ with hp
    have hp1 : (p : ℝ) ≤ N * c := Nat.floor_le hNc
    have hp2 : (N : ℝ) * c < p + 1 := Nat.lt_floor_add_one _
    refine ⟨p • z + w', ?_, ?_⟩
    · have h1 := hadd (p • z) w'
      rw [hsmul] at h1
      have h2 := mul_le_mul_of_nonneg_right hp1 (hg z)
      linarith only [h1, h2, hw'g]
    · have e : (N : ℝ) • (c • point z + x') - point (p • z + w') =
          ((N : ℝ) * c - p) • point z + ((N : ℝ) • x' - point w') := by
        rw [point_add, point_nsmul]; module
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hp1])]
      have : ((N : ℝ) * c - p) * ‖point z‖ ≤ ‖point z‖ := by
        nlinarith only [norm_nonneg (point z), hp2]
      linarith only [this, hw'n]

/-- A representation of a lattice point bounds `g` there. -/
theorem ge_of_point {a A : ℝ} (ha : 0 < a) (hsmul : ∀ (n : ℕ) (z : Vertex m), g (n • z) = n * g z)
    (hadd : ∀ z w, g (z + w) ≤ g z + g w) (hlo : ∀ z, a * ‖point z‖ ≤ g z)
    (hhi : ∀ z, g z ≤ A * ‖point z‖) {z : Vertex m} (hz : HullRep g (point z) s) : g z ≤ s := by
  have hg : ∀ z, 0 ≤ g z := fun z => (mul_nonneg ha.le (norm_nonneg _)).trans (hlo z)
  obtain ⟨B, hB, hN⟩ := approx hsmul hadd hg hz
  set K : ℝ := |A| * B with hK
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) hB
  have key : ∀ N : ℕ, (N : ℝ) * g z ≤ N * s + K := fun N => by
    obtain ⟨w, hw1, hw2⟩ := hN N
    have e : point (N • z - w) = (N : ℝ) • point z - point w := by
      rw [point_sub, point_nsmul]
    have h1 := hadd w (N • z - w)
    rw [add_sub_cancel, hsmul] at h1
    have h2 : g (N • z - w) ≤ K := by
      refine (hhi _).trans ?_
      rw [e]
      exact (mul_le_mul_of_nonneg_right (le_abs_self A) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hw2 (abs_nonneg A))
    linarith only [h1, h2, hw1]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN1⟩ := exists_nat_gt (K / ε)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hK0 hε.le) hN1
  have h3 : K < N * ε := (div_lt_iff₀ hε).mp hN1
  refine le_of_mul_le_mul_left ?_ hNpos
  linarith only [key N, h3]

end HullRep

/-- The sublinear hull of `g`: the infimum of `∑ cⱼ g(zⱼ)` over nonnegative representations
`x = ∑ cⱼ • point zⱼ`. -/
noncomputable def hullFun (g : Vertex m → ℝ) (x : Pt m) : ℝ := sInf {s | HullRep g x s}

section hull

variable {g : Vertex m → ℝ} {a : ℝ}

theorem hullFun_le {x : Pt m} {s : ℝ} (ha : 0 ≤ a) (hlo : ∀ z, a * ‖point z‖ ≤ g z)
    (hx : HullRep g x s) : hullFun g x ≤ s :=
  csInf_le ⟨a * ‖x‖, fun _ hs => HullRep.lower ha hlo hs⟩ hx

theorem le_hullFun (ha : 0 ≤ a) (hneg : ∀ z, g (-z) = g z) (hlo : ∀ z, a * ‖point z‖ ≤ g z)
    (x : Pt m) : a * ‖x‖ ≤ hullFun g x :=
  le_csInf (HullRep.exists_rep hneg x) fun _ hs => HullRep.lower ha hlo hs

theorem hullFun_add_le (ha : 0 ≤ a) (hneg : ∀ z, g (-z) = g z) (hlo : ∀ z, a * ‖point z‖ ≤ g z)
    (x y : Pt m) : hullFun g (x + y) ≤ hullFun g x + hullFun g y := by
  have h1 : ∀ t, HullRep g y t → hullFun g (x + y) - t ≤ hullFun g x := fun t ht =>
    le_csInf (HullRep.exists_rep hneg x) fun s hs => by
      have := hullFun_le ha hlo (HullRep.add hs ht)
      linarith only [this]
  have h2 : hullFun g (x + y) - hullFun g x ≤ hullFun g y :=
    le_csInf (HullRep.exists_rep hneg y) fun t ht => by
      have := h1 t ht
      linarith only [this]
  linarith only [h2]

theorem hullFun_neg (ha : 0 ≤ a) (hneg : ∀ z, g (-z) = g z) (hlo : ∀ z, a * ‖point z‖ ≤ g z)
    (x : Pt m) : hullFun g (-x) = hullFun g x := by
  have key : ∀ x : Pt m, hullFun g (-x) ≤ hullFun g x := fun x =>
    le_csInf (HullRep.exists_rep hneg x) fun s hs => hullFun_le ha hlo (HullRep.neg hneg hs)
  exact le_antisymm (key x) (by simpa using key (-x))

theorem hullFun_smul_le (ha : 0 ≤ a) (hneg : ∀ z, g (-z) = g z) (hlo : ∀ z, a * ‖point z‖ ≤ g z)
    {t : ℝ} (ht : 0 < t) (x : Pt m) : hullFun g (t • x) ≤ t * hullFun g x := by
  have : hullFun g (t • x) / t ≤ hullFun g x :=
    le_csInf (HullRep.exists_rep hneg x) fun s hs => by
      rw [div_le_iff₀ ht, mul_comm]
      exact hullFun_le ha hlo (HullRep.smul ht.le hs)
  rwa [div_le_iff₀ ht, mul_comm] at this

theorem hullFun_zero (ha : 0 ≤ a) (hlo : ∀ z, a * ‖point z‖ ≤ g z) : hullFun g 0 = 0 := by
  refine le_antisymm (hullFun_le ha hlo HullRep.zero) ?_
  refine le_csInf ⟨0, HullRep.zero⟩ fun s hs => ?_
  simpa using HullRep.lower ha hlo hs

theorem hullFun_smul (ha : 0 ≤ a) (hneg : ∀ z, g (-z) = g z) (hlo : ∀ z, a * ‖point z‖ ≤ g z)
    (r : ℝ) (x : Pt m) : hullFun g (r • x) = ‖r‖ * hullFun g x := by
  have pos : ∀ {t : ℝ}, 0 < t → ∀ x : Pt m, hullFun g (t • x) = t * hullFun g x :=
      fun {t} ht x => by
    refine le_antisymm (hullFun_smul_le ha hneg hlo ht x) ?_
    have h := hullFun_smul_le ha hneg hlo (inv_pos.mpr ht) (t • x)
    rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h
    have := mul_le_mul_of_nonneg_left h ht.le
    rwa [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at this
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have : r • x = (-r) • (-x) := by rw [neg_smul, smul_neg, neg_neg]
    rw [this, pos (neg_pos.mpr hr), hullFun_neg ha hneg hlo, Real.norm_eq_abs, abs_of_neg hr]
  · simp [hr, hullFun_zero ha hlo]
  · rw [pos hr, Real.norm_eq_abs, abs_of_pos hr]

end hull

/-- The sublinear hull of a function with the lattice properties of the time constant is a norm
on `ℝ^d`. -/
theorem exists_ptNorm_extend {g : Vertex m → ℝ} {a A : ℝ} (ha : 0 < a)
    (hsmul : ∀ (n : ℕ) (z : Vertex m), g (n • z) = n * g z)
    (hadd : ∀ z w, g (z + w) ≤ g z + g w) (hneg : ∀ z, g (-z) = g z)
    (hlo : ∀ z, a * ‖point z‖ ≤ g z) (hhi : ∀ z, g z ≤ A * ‖point z‖) :
    ∃ μ : PtNorm m, ∀ z : Vertex m, μ.1 (point z) = g z := by
  have ha' := ha.le
  refine ⟨⟨Seminorm.of (hullFun g) (hullFun_add_le ha' hneg hlo) (hullFun_smul ha' hneg hlo),
    fun x hx => ?_⟩, fun z => ?_⟩
  · have h1 := le_hullFun ha' hneg hlo x
    have h2 : hullFun g x = 0 := hx
    rw [h2] at h1
    have : ‖x‖ ≤ 0 := by
      by_contra h
      have := mul_pos ha (not_le.mp h)
      linarith only [this, h1]
    exact norm_le_zero_iff.mp this
  · refine le_antisymm (hullFun_le ha' hlo (by simpa using HullRep.single z)) ?_
    exact le_csInf ⟨_, HullRep.single z⟩ fun s hs =>
      HullRep.ge_of_point ha hsmul hadd hlo hhi hs

end CurvatureVariance.Infra.FPP
