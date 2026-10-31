/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Contracts.Localization
public import IsotropicVariance.Infra.Measurability.SlabTime
import IsotropicVariance.Paper.Proofs.Labels.Geometry
import Mathlib.Tactic.Linarith
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
import IsotropicVariance.Paper.Proofs.Profiles.ProfilesSlab

/-!
# Extracting single values from the suprema of Sections `sec:exponential` and `sec:localization`

The quantities of equation `eq:profiles` and Lemma `lem:localization` are real suprema `⨆`, which
are `0` for families unbounded above. For a pair of transverse cubes, the families in question are
bounded: the cubes are bounded and lie in the slab of the pair, the slab passage time is between `0`
and `b` times the distance, and a `1`-optimal curve for a density between `a > 0` and `B` stays
within `(B|u − v| + 1)/a` of its starting point `u`. So each value is at most the supremum (equation
`eq:profiles` of Proposition `prop:profiles` and Lemma `lem:localization`, used in the proofs of
Lemmas `lem:labels` and `lem:residual`).

* Cube pairs: the cubes are bounded and lie in the slab of the pair.
* Extraction from nested real suprema of families bounded above (two and four indices, with a
  final `Prop` index as in the modulus of equation `eq:modulus`).
* The profile supremum of equation `eq:profiles` and the modulus of equation `eq:modulus`, for any
  `D` within a bounded distance of `|v − u|` on the cubes, and for the slab passage time.
* The deviation of a `1`-optimal curve from the segment is at most the supremum of equation
  `eq:localization`, for a density bounded above and below by positive constants, and for the slab
  density of a setting.
-/

@[expose] public section

open Set Metric Bornology

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper

variable {m : ℕ}

/-! ## Cube pairs -/

section Cubes

/-- The points of a hyperplane `{t}` whose transverse coordinates are within `c` of those of `y`
form a bounded set. -/
theorem isBounded_setOf_lon_eq (t : ℝ) (y : EuclideanSpace ℝ (Fin m)) (c : ℝ) :
    IsBounded {x : Pt m | Pt.lon x = t ∧ ∀ k, |Pt.tr x k - y k| ≤ c} := by
  refine (isBounded_iff_subset_closedBall (Pt.mk t y)).2 ⟨Real.sqrt m * |c|, fun x hx => ?_⟩
  rw [mem_closedBall, dist_eq_norm_tr_sub (hx.1.trans rfl)]
  refine Profiles.norm_le_of_abs_le (abs_nonneg c) fun k => ?_
  exact (hx.2 k).trans (le_abs_self c)

/-- The first cube of a pair is bounded. -/
theorem CubePair.isBounded_first (p : CubePair m) : IsBounded p.first := by
  refine p.motion.isometry.lipschitzWith.isBounded_image ((isBounded_setOf_lon_eq 0 0
    (p.side₁ / 2)).subset fun x hx => ⟨hx.1, fun k => ?_⟩)
  simpa using hx.2 k

/-- The second cube of a pair is bounded. -/
theorem CubePair.isBounded_second (p : CubePair m) : IsBounded p.second :=
  p.motion.isometry.lipschitzWith.isBounded_image (isBounded_setOf_lon_eq _ _ _)

/-- Two bounded sets: the distances between their points are bounded by a nonnegative constant. -/
theorem exists_dist_le_of_isBounded {I I' : Set (Pt m)} (hI : IsBounded I) (hI' : IsBounded I') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ I, ∀ v ∈ I', dist u v ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hI.union hI')
  exact ⟨max C 0, le_max_right _ _, fun u hu v hv =>
    (hC (mem_union_left _ hu) (mem_union_right _ hv)).trans (le_max_left _ _)⟩

/-- The distances between the points of the two cubes of a pair are bounded. -/
theorem CubePair.exists_dist_le (p : CubePair m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ p.first, ∀ v ∈ p.second, dist u v ≤ C :=
  exists_dist_le_of_isBounded (CubePair.isBounded_first p) (CubePair.isBounded_second p)

end Cubes

/-! ## Nested real suprema -/

section Suprema

/-- A lower bound of a member of a family of reals bounded above is a lower bound of its
supremum. -/
theorem le_iSup_of_le_of_forall_le {ι : Sort*} {f : ι → ℝ} {x B : ℝ} (hf : ∀ i, f i ≤ B)
    (i : ι) (hx : x ≤ f i) : x ≤ ⨆ j, f j :=
  le_ciSup_of_le ⟨B, by rintro _ ⟨j, rfl⟩; exact hf j⟩ i hx

/-- The real supremum of a family bounded above by `B` is at most `max B 0` (it is `0` for an
empty family). -/
theorem iSup_le_max_zero {ι : Sort*} {f : ι → ℝ} {B : ℝ} (hf : ∀ i, f i ≤ B) :
    ⨆ i, f i ≤ max B 0 :=
  Real.iSup_le (fun i => (hf i).trans (le_max_left _ _)) (le_max_right _ _)

/-- The double version of `iSup_le_max_zero`. -/
theorem iSup₂_le_max_zero {ι : Sort*} {κ : ι → Sort*} {f : (i : ι) → κ i → ℝ} {B : ℝ}
    (hf : ∀ i k, f i k ≤ B) : ⨆ (i) (k), f i k ≤ max B 0 :=
  Real.iSup_le (fun i => iSup_le_max_zero (hf i)) (le_max_right _ _)

/-- Extraction from a double real supremum of a family bounded above. -/
theorem le_iSup₂_of_le_of_forall_le {ι : Sort*} {κ : ι → Sort*} {f : (i : ι) → κ i → ℝ}
    {x B : ℝ} (hf : ∀ i k, f i k ≤ B) (i : ι) (k : κ i) (hx : x ≤ f i k) :
    x ≤ ⨆ (i) (k), f i k :=
  le_iSup_of_le_of_forall_le (f := fun i => ⨆ k, f i k) (fun j => iSup_le_max_zero (hf j)) i
    (le_iSup_of_le_of_forall_le (hf i) k hx)

/-- Extraction from a fourfold real supremum (with dependent index types, as in
`Contracts.maxSegmentDeviation`) of a family bounded above. -/
theorem le_iSup₄_of_le_of_forall_le {ι₁ : Sort*} {ι₂ : ι₁ → Sort*}
    {ι₃ : (a : ι₁) → ι₂ a → Sort*} {ι₄ : (a : ι₁) → (b : ι₂ a) → ι₃ a b → Sort*}
    {f : (a : ι₁) → (b : ι₂ a) → (c : ι₃ a b) → ι₄ a b c → ℝ} {x B : ℝ}
    (hf : ∀ a b c d, f a b c d ≤ B) (a : ι₁) (b : ι₂ a) (c : ι₃ a b) (d : ι₄ a b c)
    (hx : x ≤ f a b c d) : x ≤ ⨆ (a) (b) (c) (d), f a b c d :=
  le_iSup₂_of_le_of_forall_le (f := fun a b => ⨆ (c) (d), f a b c d)
    (fun a' b' => iSup₂_le_max_zero (hf a' b')) a b
    (le_iSup₂_of_le_of_forall_le (hf a b) c d hx)

/-- Extraction from a fourfold real supremum restricted by a condition (a final `Prop` index, as
in `Contracts.modulusSup`) of a family bounded above. Over a false condition the supremum is
`sSup ∅ = 0`, which the bound `max B 0` absorbs. -/
theorem le_iSup₄_prop_of_le_of_forall_le {ι₁ ι₂ ι₃ ι₄ : Sort*} {P : ι₁ → ι₂ → ι₃ → ι₄ → Prop}
    {f : (a : ι₁) → (b : ι₂) → (c : ι₃) → (d : ι₄) → P a b c d → ℝ} {x B : ℝ}
    (hf : ∀ a b c d h, f a b c d h ≤ B) (a : ι₁) (b : ι₂) (c : ι₃) (d : ι₄) (h : P a b c d)
    (hx : x ≤ f a b c d h) : x ≤ ⨆ (a) (b) (c) (d) (h : P a b c d), f a b c d h :=
  le_iSup₄_of_le_of_forall_le (f := fun a b c d => ⨆ h : P a b c d, f a b c d h)
    (fun a' b' c' d' => iSup_le_max_zero (hf a' b' c' d')) a b c d
    (le_iSup_of_le_of_forall_le (hf a b c d) h hx)

end Suprema

/-! ## The profile supremum and the modulus -/

section Profile

/-- **Profile supremum, general form.** If `|D(u, v) − |u − v||` is bounded on `I × I'`, each of
its values is at most its supremum over `I × I'` (the quantity of equation `eq:profiles`). -/
theorem abs_sub_dist_le_iSup {D : Pt m → Pt m → ℝ} {I I' : Set (Pt m)} {B : ℝ}
    (hD : ∀ u ∈ I, ∀ v ∈ I', |D u v - dist u v| ≤ B) {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I') :
    |D u v - dist u v| ≤ ⨆ (u : I) (v : I'), |D u v - dist (u : Pt m) v| := by
  refine le_iSup₂_of_le_of_forall_le (B := B) ?_ (⟨u, hu⟩ : I) (⟨v, hv⟩ : I') le_rfl
  rintro ⟨u', hu'⟩ ⟨v', hv'⟩
  exact hD u' hu' v' hv'

/-- **Modulus, general form.** If `|D(u, v) − |u − v||` is bounded on `I × I'`, each value of the
modulus quantity of equation `eq:modulus` is at most `Contracts.modulusSup`. -/
theorem abs_sub_sub_add_le_modulusSup {D : Pt m → Pt m → ℝ} {I I' : Set (Pt m)} {B : ℝ}
    (hD : ∀ u ∈ I, ∀ v ∈ I', |D u v - dist u v| ≤ B) {r : ℝ} {u u₁ v v₁ : Pt m} (hu : u ∈ I)
    (hu₁ : u₁ ∈ I) (hv : v ∈ I') (hv₁ : v₁ ∈ I') (huu : dist u u₁ ≤ r) (hvv : dist v v₁ ≤ r) :
    |D u v - D u₁ v₁ - dist u v + dist u₁ v₁| ≤ Contracts.modulusSup D I I' r := by
  unfold Contracts.modulusSup
  refine le_iSup₄_prop_of_le_of_forall_le (B := B + B) ?_ (⟨u, hu⟩ : I) (⟨u₁, hu₁⟩ : I)
    (⟨v, hv⟩ : I') (⟨v₁, hv₁⟩ : I') ⟨huu, hvv⟩ le_rfl
  rintro ⟨u', hu'⟩ ⟨u₁', hu₁'⟩ ⟨v', hv'⟩ ⟨v₁', hv₁'⟩ -
  have h1 := abs_le.1 (hD u' hu' v' hv')
  have h2 := abs_le.1 (hD u₁' hu₁' v₁' hv₁')
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The slab passage time differs from the distance by at most `b` times the distance. -/
theorem abs_slabTime_sub_dist_le (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) (sl : Slab m)
    (ω : X.Ω) {u v : Pt m} (hu : u ∈ sl.set) (hv : v ∈ sl.set) :
    |X.slabTime b sl ω u v - dist u v| ≤ b * dist u v + dist u v := by
  have h0 := Infra.Slab.slabTime_nonneg X b sl ω u v
  have h1 := Infra.Slab.slabTime_le_mul_dist X hb sl ω hu hv
  have hbd : 0 ≤ b * dist u v := mul_nonneg (Infra.Slab.upperBound_nonneg X hb ω) dist_nonneg
  have hd : 0 ≤ dist u v := dist_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- On the cubes of a pair, `|D(u, v) − |u − v||` is bounded for the slab passage time. -/
theorem CubePair.exists_abs_slabTime_sub_dist_le (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (p : CubePair m) (hd : 0 ≤ p.dist) (ω : X.Ω) :
    ∃ B : ℝ, ∀ u ∈ p.first, ∀ v ∈ p.second,
      |X.slabTime b p.slab ω u v - dist u v| ≤ B := by
  obtain ⟨C, -, hC⟩ := CubePair.exists_dist_le p
  have hb0 := Infra.Slab.upperBound_nonneg X hb ω
  refine ⟨b * C + C, fun u hu v hv => ?_⟩
  have h := abs_slabTime_sub_dist_le X hb p.slab ω (Profiles.cubePair_first_subset_set p hd hu)
    (Profiles.cubePair_second_subset_set p hd hv)
  have hbC : b * dist u v ≤ b * C := mul_le_mul_of_nonneg_left (hC u hu v hv) hb0
  linarith [hC u hu v hv]

/-- **Profile supremum for the slab passage time**: for `u ∈ I`, `v ∈ I'`, `|D(u, v) − |u − v||`
is at most `sup_{u ∈ I, v ∈ I'} |D(u, v) − |u − v||`, `D` the slab passage time of the pair. -/
theorem abs_slabTime_sub_dist_le_iSup (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (p : CubePair m) (hd : 0 ≤ p.dist) (ω : X.Ω) {u v : Pt m} (hu : u ∈ p.first)
    (hv : v ∈ p.second) :
    |X.slabTime b p.slab ω u v - dist u v| ≤
      ⨆ (u : p.first) (v : p.second), |X.slabTime b p.slab ω u v - dist (u : Pt m) v| := by
  obtain ⟨B, hB⟩ := CubePair.exists_abs_slabTime_sub_dist_le X hb p hd ω
  exact abs_sub_dist_le_iSup hB hu hv

/-- **Modulus for the slab passage time**: each value of the modulus quantity of equation
`eq:modulus` at scale `r` is at most `Contracts.modulusSup` of the slab passage time of the pair. -/
theorem abs_slabTime_sub_sub_add_le_modulusSup (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (p : CubePair m) (hd : 0 ≤ p.dist) (ω : X.Ω) {r : ℝ} {u u₁ v v₁ : Pt m} (hu : u ∈ p.first)
    (hu₁ : u₁ ∈ p.first) (hv : v ∈ p.second) (hv₁ : v₁ ∈ p.second) (huu : dist u u₁ ≤ r)
    (hvv : dist v v₁ ≤ r) :
    |X.slabTime b p.slab ω u v - X.slabTime b p.slab ω u₁ v₁ - dist u v + dist u₁ v₁| ≤
      Contracts.modulusSup (X.slabTime b p.slab ω) p.first p.second r := by
  obtain ⟨B, hB⟩ := CubePair.exists_abs_slabTime_sub_dist_le X hb p hd ω
  exact abs_sub_sub_add_le_modulusSup hB hu hu₁ hv hv₁ huu hvv

end Profile

/-! ## The deviation of a `1`-optimal curve -/

section Deviation

/-- The restricted passage time in a convex set is at most `B` times the distance, for a density
bounded by `B ≥ 0`. -/
theorem restrictedPassageTime_le_mul_dist {σ : Pt m → ℝ} {B : ℝ} (hσB : ∀ x, σ x ≤ B)
    (hB : 0 ≤ B) {S : Set (Pt m)} (hS : Convex ℝ S) {u v : Pt m} (hu : u ∈ S) (hv : v ∈ S) :
    restrictedPassageTime σ S u v ≤ B * dist u v := by
  rw [restrictedPassageTime_eq_toReal]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (edist_ne_top u v))
    (restrictedInf_le hσB hS hu hv)).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, edist_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- **A `1`-optimal curve stays near its start**: for a density between `a > 0` and `B`, a point
of a `1`-optimal curve from `u` to `v` in a convex set `S ∋ u, v` is within `(B|u − v| + 1)/a`
of `u` (its cost is at least `a` times its length, and at most `B|u − v| + 1`). -/
theorem mul_dist_le_of_isOneOptimal {σ : Pt m → ℝ} {a B : ℝ} (ha : 0 < a)
    (hσa : ∀ x, a ≤ σ x) (hσB : ∀ x, σ x ≤ B) {S : Set (Pt m)} (hS : Convex ℝ S) {u v : Pt m}
    (hu : u ∈ S) (hv : v ∈ S) {γ : RectifiableCurve (Pt m)} (hγ : IsOneOptimal σ S u v γ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : a * dist u (γ.toFun t) ≤ B * dist u v + 1 := by
  have hB : 0 ≤ B := ha.le.trans ((hσa u).trans (hσB u))
  have hT := restrictedPassageTime_le_mul_dist hσB hB hS hu hv
  have hq : 0 ≤ B * dist u v + 1 := by positivity
  have hcost : γ.cost (fun x => ENNReal.ofReal (σ x)) ≤ ENNReal.ofReal (B * dist u v + 1) :=
    hγ.2.2.2.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hlen : ENNReal.ofReal a * γ.length ≤ γ.cost (fun x => ENNReal.ofReal (σ x)) :=
    γ.mul_length_le_cost fun x => ENNReal.ofReal_le_ofReal (hσa x)
  have hed : edist u (γ.toFun t) ≤ γ.length := by
    rw [← hγ.1]
    exact eVariationOn.edist_le γ.toFun (left_mem_Icc.2 zero_le_one) ht
  have h : ENNReal.ofReal (a * dist u (γ.toFun t)) ≤ ENNReal.ofReal (B * dist u v + 1) := by
    rw [ENNReal.ofReal_mul ha.le, ← edist_dist]
    exact (mul_le_mul_right hed _).trans (hlen.trans hcost)
  exact (ENNReal.ofReal_le_ofReal_iff hq).1 h

/-- **Deviation of a `1`-optimal curve, general form**: for a density between `a > 0` and `B`, a
convex `S` and bounded `I, I' ⊆ S`, the distance from `[u, v]` of a point of a `1`-optimal curve
from `u ∈ I` to `v ∈ I'` is at most `Contracts.maxSegmentDeviation σ S I I'`. -/
theorem infDist_le_maxSegmentDeviation {σ : Pt m → ℝ} {a B : ℝ} (ha : 0 < a)
    (hσa : ∀ x, a ≤ σ x) (hσB : ∀ x, σ x ≤ B) {S I I' : Set (Pt m)} (hS : Convex ℝ S)
    (hI : IsBounded I) (hI' : IsBounded I') (hIS : I ⊆ S) (hI'S : I' ⊆ S) {u v : Pt m}
    (hu : u ∈ I) (hv : v ∈ I') {γ : RectifiableCurve (Pt m)} (hγ : IsOneOptimal σ S u v γ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    infDist (γ.toFun t) (segment ℝ u v) ≤ Contracts.maxSegmentDeviation σ S I I' := by
  have hB : 0 ≤ B := ha.le.trans ((hσa u).trans (hσB u))
  obtain ⟨C, -, hC⟩ := exists_dist_le_of_isBounded hI hI'
  have key : ∀ u' ∈ I, ∀ v' ∈ I', ∀ γ' : RectifiableCurve (Pt m), IsOneOptimal σ S u' v' γ' →
      ∀ t' ∈ Icc (0 : ℝ) 1, infDist (γ'.toFun t') (segment ℝ u' v') ≤ (B * C + 1) / a := by
    intro u' hu' v' hv' γ' hγ' t' ht'
    have h1 := mul_dist_le_of_isOneOptimal ha hσa hσB hS (hIS hu') (hI'S hv') hγ' ht'
    have h2 : infDist (γ'.toFun t') (segment ℝ u' v') ≤ dist u' (γ'.toFun t') := by
      rw [dist_comm]
      exact infDist_le_dist_of_mem (left_mem_segment ℝ u' v')
    have h3 : B * dist u' v' ≤ B * C := mul_le_mul_of_nonneg_left (hC u' hu' v' hv') hB
    rw [le_div_iff₀ ha]
    have h4 : infDist (γ'.toFun t') (segment ℝ u' v') * a ≤ dist u' (γ'.toFun t') * a :=
      mul_le_mul_of_nonneg_right h2 ha.le
    linarith
  unfold Contracts.maxSegmentDeviation
  refine le_iSup₄_of_le_of_forall_le (B := (B * C + 1) / a) ?_ (⟨u, hu⟩ : I) (⟨v, hv⟩ : I')
    ⟨γ, hγ⟩ ⟨t, ht⟩ le_rfl
  rintro ⟨u', hu'⟩ ⟨v', hv'⟩ ⟨γ', hγ'⟩ ⟨t', ht'⟩
  exact key u' hu' v' hv' γ' hγ' t' ht'

/-- The slab density is at least a lower bound of the density that is also at most `b`. -/
theorem Slab.le_density (sl : Slab m) {b a : ℝ} {σ : Pt m → ℝ} (hab : a ≤ b)
    (hσ : ∀ x, a ≤ σ x) (x : Pt m) : a ≤ sl.density b σ x := by
  unfold Slab.density
  split_ifs
  · exact hab
  · exact hσ x

/-- **Deviation of a `1`-optimal curve for the slab passage time of a pair**: the distance from
`[u, v]` of a point of a `1`-optimal curve for the slab density from `u ∈ I` to `v ∈ I'` is at
most the supremum of equation `eq:localization` for the slab passage time. -/
theorem infDist_le_maxSegmentDeviation_slab (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b)
    (p : CubePair m) (hd : 0 ≤ p.dist) (ω : X.Ω) {u v : Pt m} (hu : u ∈ p.first)
    (hv : v ∈ p.second) {γ : RectifiableCurve (Pt m)}
    (hγ : IsOneOptimal (p.slab.density b (X.ρ ω)) p.slab.set u v γ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    infDist (γ.toFun t) (segment ℝ u v) ≤
      Contracts.maxSegmentDeviation (p.slab.density b (X.ρ ω)) p.slab.set p.first p.second := by
  obtain ⟨a, B', ha, hab⟩ := X.bounds
  exact infDist_le_maxSegmentDeviation ha
    (Slab.le_density p.slab ((hab ω 0).1.trans (hb ω 0)) fun x => (hab ω x).1)
    (fun x => (p.slab.density_le b (hb ω) x).trans (max_self b).le)
    (Infra.Slab.convex_slab_set p.slab)
    (CubePair.isBounded_first p) (CubePair.isBounded_second p)
    (Profiles.cubePair_first_subset_set p hd) (Profiles.cubePair_second_subset_set p hd) hu hv hγ ht

end Deviation

end IsotropicVariance.Paper.Proofs.Labels
