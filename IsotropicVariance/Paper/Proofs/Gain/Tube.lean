/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Translation
public import IsotropicVariance.Paper.Proofs.Gain.Locality
import IsotropicVariance.Paper.Proofs.Localization.Measurable
import IsotropicVariance.Paper.Proofs.Profiles.CubeGeometry
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry
import IsotropicVariance.Infra.Measurability.SlabTime
public import IsotropicVariance.Paper.Defs.Restricted
import IsotropicVariance.Infra.Measurability.MinimizerMeasurable

/-!
# Lemma `lem:fewtranslates`: the tube of the slab minimum

The proof of Lemma `lem:fewtranslates`: the change `F_m − F_m^G` vanishes unless `G` meets,
before or after the replacement, the tube of radius `R_i(J_{i−1}, J_i) W_n` around the segment
between the centers of `I_{i−1}(J_{i−1})` and `I_i(J_i)`, where `i` is the slab of `G`
(the tube `U_i(j, k)` of Section `sec:gain`). This file proves the deterministic half of it.

* `segTube`, `tube`: the closed tube of radius `R_i(J_i, J_{i+1}) W` around the segment between
  the centers of `I_i(J_i)` and `I_{i+1}(J_{i+1})` (0-based slab `i`), for the indices `J` and
  radii `R` of a configuration.
* `mul_zNorm_J_sub_le`: the admissibility `|x_{i+1} − x_i − n e₁| ≤ n/4` of the minimizing points
  gives `W |J_{i+1} − J_i| ≤ n/2` once `W √m ≤ n/4`, so the radius `R_i(J_i, J_{i+1})` is the
  deviation radius and not the value zero of the unused pairs.
* `le_maxDeviation`: a 1-optimal curve between the two cubes stays within the largest deviation
  `maxDeviation`, whose supremum is bounded (`exists_bound_deviation_slab`, from the bound
  `Localization.exists_dist_le_of_isOneOptimal` on 1-optimal curves).
* `closedBall_subset_compl_closure_block`: in a slab other than that of the block, the points at
  distance more than one from the faces are at distance more than one from the block.
* `F_le_of_disjoint_tube`: **the tube lemma**. If the densities of `c` and `c'` agree at every
  point at distance more than one from the block `G` of the slab `i`, and `G` does not meet the
  tube of `c` in its slab, then `F(c') ≤ F(c)`: the minimizing points of `c` cost the same for
  `c'` in the other slabs, and in the slab `i` the near-optimal curves of `c` stay in the tube,
  at distance more than one from `G` (`radiusConst m ≥ 2`, `W ≥ 1`).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

variable {m : ℕ}

/-! ### The tube -/

/-- The closed tube of radius `r W` around the segment between the centers of `I_i(j)` and
`I_{i+1}(k)`. -/
def segTube (n W : ℝ) (i : ℕ) (j k : Fin m → ℤ) (r : ℝ) : Set (Pt m) :=
  {y | infDist y (segment ℝ (gridCubeCenter n W 0 i j) (gridCubeCenter n W 0 (i + 1) k)) ≤
    r * W}

/-- **The tube of `F` in the slab `i`** (the proof of Lemma `lem:fewtranslates`): the closed
tube of radius `R_i(J_i, J_{i+1}) W` around the segment between the centers of `I_i(J_i)` and
`I_{i+1}(J_{i+1})`, for the indices `J` and the radii `R` of the configuration `c` (0-based slab
`i`). -/
def tube (X : Setting.{u} m) (b : ℝ) (K : ℕ) (n W : ℝ) (c : X.Ω) (i : Fin K) : Set (Pt m) :=
  segTube n W i (X.J b K n W 0 c i.castSucc) (X.J b K n W 0 c i.succ)
    (X.R b n W c i (X.J b K n W 0 c i.castSucc) (X.J b K n W 0 c i.succ))

/-- An upper bound of the radius gives a larger tube. -/
theorem segTube_mono {n W : ℝ} (hW : 0 ≤ W) {i : ℕ} {j k : Fin m → ℤ} {r r' : ℝ} (h : r ≤ r') :
    segTube n W i j k r ⊆ segTube n W i j k r' :=
  fun _ hy => le_trans hy (mul_le_mul_of_nonneg_right h hW)

/-! ### Coordinates and cubes -/

/-! ### Slabs and blocks -/

/-- The closure of a block lies in its slab. -/
theorem closure_block_subset (n W : ℝ) (L i : ℕ) (z : Fin m → ℤ) :
    closure (block n W L i z) ⊆ {y | (i : ℝ) * n ≤ Pt.lon y ∧ Pt.lon y ≤ ((i : ℝ) + 1) * n} :=
  closure_minimal (fun _ hy => ⟨hy.1, hy.2.1⟩)
    ((isClosed_le continuous_const Pt.continuous_lon).inter
      (isClosed_le Pt.continuous_lon continuous_const))

/-- The distance to the faces of the slab `i` is at most the distance to either hyperplane. -/
theorem infDist_chainSlab_faces_le (s : ℝ) (i : ℕ) (x : Pt m) {a : ℝ}
    (ha : a = i * s ∨ a = i * s + s) : infDist x (chainSlab s 0 i).faces ≤ |Pt.lon x - a| := by
  have hmem : x - (Pt.lon x - a) • (e₁ : Pt m) ∈ (chainSlab s 0 i).faces := by
    rw [chainSlab, mem_e1Slab_faces]
    have : Pt.lon (x - (Pt.lon x - a) • (e₁ : Pt m)) = a := by simp
    rw [this, Pt.lon_zero, zero_add]
    exact ha
  refine (infDist_le_dist_of_mem hmem).trans_eq ?_
  rw [dist_eq_norm, sub_sub_cancel, norm_smul, norm_e₁, mul_one, Real.norm_eq_abs]

/-- **Other slabs are far from the block**: a point of the slab `i' ≠ i` at distance more than
one from its faces has its closed unit ball off the closure of every block of the slab `i`. -/
theorem closedBall_subset_compl_closure_block {n W : ℝ} (hn : 0 ≤ n) {L i i' : ℕ}
    (hii : i' ≠ i) (z : Fin m → ℤ) {x : Pt m} (hx : x ∈ (chainSlab n 0 i').set)
    (hf : 1 < infDist x (chainSlab n 0 i').faces) :
    closedBall x 1 ⊆ (closure (block n W L i z))ᶜ := by
  rw [mem_chainSlab_set, Pt.lon_zero, zero_add] at hx
  have h1 := infDist_chainSlab_faces_le n i' x (Or.inl rfl)
  have h2 := infDist_chainSlab_faces_le n i' x (Or.inr rfl)
  have hlo : (i' : ℝ) * n + 1 < Pt.lon x := by
    have h := hf.trans_le h1
    rw [abs_of_nonneg (by linarith only [hx])] at h
    linarith only [h]
  have hhi : Pt.lon x < (i' : ℝ) * n + n - 1 := by
    have h := hf.trans_le h2
    rw [abs_of_nonpos (by linarith only [hx])] at h
    linarith only [h]
  intro y hy hyc
  have hyG := closure_block_subset n W L i z hyc
  have hdy := (Infra.Slab.abs_lon_sub_le y x).trans (mem_closedBall.1 hy)
  rw [abs_le] at hdy
  rcases Nat.lt_or_gt_of_ne hii with h | h
  · have hc : ((i' : ℝ) + 1) * n ≤ (i : ℝ) * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt h) hn
    linarith only [hc, hyG.1, hdy.1, hdy.2, hhi]
  · have hc : ((i : ℝ) + 1) * n ≤ (i' : ℝ) * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt h) hn
    linarith only [hc, hyG.2, hdy.1, hdy.2, hlo]

/-! ### The radii -/

/-- The largest deviation is nonnegative. -/
theorem maxDeviation_nonneg (σ : Pt m → ℝ) (S I I' : Set (Pt m)) (p q : Pt m) :
    0 ≤ maxDeviation σ S I I' p q :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
    Real.iSup_nonneg fun _ => infDist_nonneg

/-- The radii are nonnegative. -/
theorem R_nonneg (X : Setting.{u} m) (b n : ℝ) {W : ℝ} (hW : 0 ≤ W) (c : X.Ω) (i : ℕ)
    (j k : Fin m → ℤ) : 0 ≤ X.R b n W c i j k := by
  unfold Setting.R
  split_ifs
  · have h1 : 0 ≤ radiusConst m := by unfold radiusConst; positivity
    have h2 := maxDeviation_nonneg ((chainSlab n 0 i).density b (X.ρ c)) (chainSlab n 0 i).set
      (gridCube n W 0 i j) (gridCube n W 0 (i + 1) k) (gridCubeCenter n W 0 i j)
      (gridCubeCenter n W 0 (i + 1) k)
    positivity
  · exact le_rfl

/-- **A 1-optimal curve stays within the largest deviation**, when the deviations of the 1-optimal
curves between the two sets are bounded. -/
theorem le_maxDeviation {σ : Pt m → ℝ} {S I I' : Set (Pt m)} {p q : Pt m} {B : ℝ}
    (hB : ∀ u ∈ I, ∀ v ∈ I', ∀ γ : RectifiableCurve (Pt m), IsOneOptimal σ S u v γ →
      ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ p q) ≤ B)
    {u v : Pt m} (hu : u ∈ I) (hv : v ∈ I') {γ : RectifiableCurve (Pt m)}
    (hγ : IsOneOptimal σ S u v γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    infDist (γ.toFun t) (segment ℝ p q) ≤ maxDeviation σ S I I' p q := by
  have hB0 : 0 ≤ B := infDist_nonneg.trans (hB u hu v hv γ hγ t ht)
  unfold maxDeviation
  refine le_ciSup_of_le ⟨B, forall_mem_range.2 fun u' => ?_⟩ ⟨u, hu⟩ ?_
  · exact Real.iSup_le (fun v' => Real.iSup_le (fun γ' => Real.iSup_le
      (fun t' => hB _ u'.2 _ v'.2 _ γ'.2 _ t'.2) hB0) hB0) hB0
  refine le_ciSup_of_le ⟨B, forall_mem_range.2 fun v' => ?_⟩ ⟨v, hv⟩ ?_
  · exact Real.iSup_le (fun γ' => Real.iSup_le (fun t' => hB _ hu _ v'.2 _ γ'.2 _ t'.2) hB0) hB0
  refine le_ciSup_of_le ⟨B, forall_mem_range.2 fun γ' => ?_⟩ ⟨γ, hγ⟩ ?_
  · exact Real.iSup_le (fun t' => hB _ hu _ hv _ γ'.2 _ t'.2) hB0
  exact le_ciSup_of_le ⟨B, forall_mem_range.2 fun t' => hB _ hu _ hv _ hγ _ t'.2⟩ ⟨t, ht⟩ le_rfl

/-- The deviations from a segment of the 1-optimal curves of a slab passage time between two
bounded sets are bounded. -/
theorem exists_bound_deviation_slab (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b)
    (c : X.Ω) (sl : Slab m) {I I' : Set (Pt m)} (hI : Bornology.IsBounded I)
    (hI' : Bornology.IsBounded I') (p q : Pt m) :
    ∃ B, ∀ u ∈ I, ∀ v ∈ I', ∀ γ : RectifiableCurve (Pt m),
      IsOneOptimal (sl.density b (X.ρ c)) sl.set u v γ →
        ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ p q) ≤ B := by
  obtain ⟨a, b', ha, hab⟩ := X.bounds
  obtain ⟨R₀, hR₀⟩ := Localization.exists_dist_le_of_isOneOptimal (Θ := Unit)
    (σ := fun _ => sl.density b (X.ρ c)) (S := sl.set) hI hI' ha
    (fun _ x => Localization.le_slabDensity X hb (fun ω x => (hab ω x).1) sl c x) (B := b)
    (fun _ u hu v hv => Infra.Slab.slabTime_le_mul_dist X hb sl c hu hv)
  obtain ⟨r₀, hr₀⟩ := hI.subset_closedBall p
  exact ⟨R₀ + r₀, fun u hu v hv γ hγ t ht =>
    (infDist_le_dist_of_mem (left_mem_segment ℝ p q)).trans <|
      (dist_triangle _ u p).trans (add_le_add (hR₀ () u hu v hv γ hγ t ht)
        (mem_closedBall.1 (hr₀ hu)))⟩

/-! ### The indices of the minimizing points -/

/-- **Consecutive indices are admissible pairs**: the admissibility
`|x_{i+1} − x_i − n e₁| ≤ n/4` of the minimizing points gives `W |J_{i+1} − J_i| ≤ n/2` once
`W √m ≤ n/4`. -/
theorem mul_zNorm_J_sub_le (X : Setting.{u} m) (b : ℝ) {K : ℕ} {n W : ℝ} (hn : 0 < n)
    (hW : 0 < W) (hWn : W * Real.sqrt m ≤ n / 4) (c : X.Ω) (i : Fin K) :
    W * zNorm (X.J b K n W 0 c i.succ - X.J b K n W 0 c i.castSucc) ≤ n / 2 := by
  set x := lexMinimizer b (X.ρ c) K n 0 with hxdef
  have hxm := (isLexLeastMinimizer_lexMinimizer b (X.isValidChain c hn.le) K 0).1
  rw [← hxdef] at hxm
  have hJ : ∀ (i' : Fin (K + 1)) (k : Fin m),
      ((X.J b K n W 0 c i' k : ℤ) : ℝ) = (⌊Pt.tr (x i') k / W⌋ : ℤ) := by
    intro i' k
    simp [Setting.J, minimizerIndex, hW, hxdef]
  set a := Pt.tr (x i.castSucc)
  set a' := Pt.tr (x i.succ)
  set e : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun k =>
    (((X.J b K n W 0 c i.succ - X.J b K n W 0 c i.castSucc) k : ℤ) : ℝ)
  have hze : zNorm (X.J b K n W 0 c i.succ - X.J b K n W 0 c i.castSucc) = ‖e‖ := by
    rw [zNorm, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [e]
  have hr : ‖e - W⁻¹ • (a' - a)‖ ≤ Real.sqrt m * 1 := by
    refine Profiles.norm_le_of_abs_le zero_le_one fun k => ?_
    have h1 := hJ i.succ k
    have h2 := hJ i.castSucc k
    have f1 := Int.floor_le (a' k / W)
    have f2 := Int.lt_floor_add_one (a' k / W)
    have f3 := Int.floor_le (a k / W)
    have f4 := Int.lt_floor_add_one (a k / W)
    have e1 : (e - W⁻¹ • (a' - a)) k = ((X.J b K n W 0 c i.succ k : ℤ) : ℝ) -
        ((X.J b K n W 0 c i.castSucc k : ℤ) : ℝ) - (a' k / W - a k / W) := by
      simp only [e, PiLp.sub_apply, PiLp.smul_apply, Pi.sub_apply, Int.cast_sub, smul_eq_mul]
      ring
    rw [e1, h1, h2, abs_le]
    constructor <;> linarith only [f1, f2, f3, f4]
  have hd : ‖a' - a‖ ≤ n / 4 := by
    have h := hxm.2.2.2 i
    refine le_trans ?_ h
    have e2 : a' - a = Pt.tr (x i.succ - x i.castSucc - n • (e₁ : Pt m)) := by
      have : Pt.tr (n • (e₁ : Pt m)) = 0 := by
        ext k
        simp [Pt.tr, e₁]
      rw [Pt.tr_sub, Pt.tr_sub, this, sub_zero]
    rw [e2]
    exact Profiles.norm_tr_le_norm _
  have he : ‖e‖ ≤ W⁻¹ * ‖a' - a‖ + Real.sqrt m := by
    calc ‖e‖ = ‖W⁻¹ • (a' - a) + (e - W⁻¹ • (a' - a))‖ := by rw [add_sub_cancel]
      _ ≤ ‖W⁻¹ • (a' - a)‖ + ‖e - W⁻¹ • (a' - a)‖ := norm_add_le _ _
      _ ≤ W⁻¹ * ‖a' - a‖ + Real.sqrt m := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hW.le)]
          linarith only [hr]
  rw [hze]
  calc W * ‖e‖ ≤ W * (W⁻¹ * ‖a' - a‖ + Real.sqrt m) := mul_le_mul_of_nonneg_left he hW.le
    _ = ‖a' - a‖ + W * Real.sqrt m := by field_simp
    _ ≤ n / 2 := by linarith only [hd, hWn]

/-! ### The tube lemma -/

/-- **The tube lemma in the slab of the block**: if the densities of `c` and `c'` agree at every
point whose closed unit ball misses the closure of the block `G` of the slab `i`, and `G` does not
meet the tube of `c` in its slab, then the slab passage time of `c'` between the minimizing points
`x_i`, `x_{i+1}` of `c` is at most that of `c` plus `ε`, for `0 < ε ≤ 1`: an `ε`-optimal curve of
`c` is 1-optimal, so it stays in the tube, at distance more than one from `G`. -/
theorem passTime_le_of_disjoint_tube (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {K : ℕ}
    {n W : ℝ} (hn : 0 < n) (hW : 1 ≤ W) (hWn : W * Real.sqrt m ≤ n / 4) (L : ℕ) (i : Fin K)
    (z : Fin m → ℤ) {c c' : X.Ω}
    (hagree : ∀ x, closedBall x 1 ⊆ (closure (block n W L i z))ᶜ → X.ρ c x = X.ρ c' x)
    (hdisj : Disjoint (block n W L i z) (tube X b K n W c i)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (chainSlab n 0 i).passTime b (X.ρ c') (lexMinimizer b (X.ρ c) K n 0 i.castSucc)
        (lexMinimizer b (X.ρ c) K n 0 i.succ) ≤
      (chainSlab n 0 i).passTime b (X.ρ c) (lexMinimizer b (X.ρ c) K n 0 i.castSucc)
        (lexMinimizer b (X.ρ c) K n 0 i.succ) + ε := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hval := X.isValidChain c hn.le
  have hxm := isLexLeastMinimizer_lexMinimizer b hval K 0
  set x := lexMinimizer b (X.ρ c) K n 0 with hxdef
  set sl := chainSlab n 0 (i : ℕ) with hsl
  set σ := sl.density b (X.ρ c) with hσ
  set σ' := sl.density b (X.ρ c') with hσ'
  set u := x i.castSucc with hu_def
  set v := x i.succ with hv_def
  set J₁ := X.J b K n W 0 c i.castSucc with hJ₁
  set J₂ := X.J b K n W 0 c i.succ with hJ₂
  set p := gridCubeCenter n W 0 (i : ℕ) J₁ with hp
  set q := gridCubeCenter n W 0 ((i : ℕ) + 1) J₂ with hq
  obtain ⟨huS, hvS⟩ := admissible_mem_chainSlab hn.le hxm.1 i
  have hu : u ∈ gridCube n W 0 (i : ℕ) J₁ := lexMinimizer_mem_gridCube b hval K hW0 0 i.castSucc
  have hv : v ∈ gridCube n W 0 ((i : ℕ) + 1) J₂ :=
    lexMinimizer_mem_gridCube b hval K hW0 0 i.succ
  have hσb : ∀ y, σ y ≤ b := fun y => by
    simp only [hσ, Slab.density]
    split_ifs
    exacts [le_rfl, hb c y]
  have hσ'b : ∀ y, σ' y ≤ b := fun y => by
    simp only [hσ', Slab.density]
    split_ifs
    exacts [le_rfl, hb c' y]
  have hconv : Convex ℝ sl.set := convex_e1Slab_set _ _
  have hfin : restrictedInf σ sl.set u v ≠ ⊤ := restrictedInf_ne_top hσb hconv huS hvS
  -- an `ε`-optimal curve of `c`
  have hlt : restrictedInf σ sl.set u v < restrictedInf σ sl.set u v + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hfin (by simpa using hε)
  unfold restrictedInf at hlt
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hlt
  obtain ⟨h0, hγ⟩ := iInf_lt_iff.1 hγ
  obtain ⟨h1, hγ⟩ := iInf_lt_iff.1 hγ
  obtain ⟨hS, hcost⟩ := iInf_lt_iff.1 hγ
  set D := sl.passTime b (X.ρ c) u v with hDdef
  have hD0 : 0 ≤ D := restrictedPassageTime_nonneg _ _ _ _
  have hD : restrictedInf σ sl.set u v = ENNReal.ofReal D := (ENNReal.ofReal_toReal hfin).symm
  have hcostD : γ.cost (fun y => ENNReal.ofReal (σ y)) ≤ ENNReal.ofReal (D + ε) := by
    rw [ENNReal.ofReal_add hD0 hε.le, ← hD]
    exact hcost.le
  have hopt : IsOneOptimal σ sl.set u v γ :=
    ⟨h0, h1, hS, hcostD.trans (ENNReal.ofReal_le_ofReal (add_le_add le_rfl hε1))⟩
  -- the curve stays within the deviation radius
  obtain ⟨B, hB⟩ := exists_bound_deviation_slab X hb c sl
    (SmallMean.isCompact_gridCube _ _ (i : ℕ) J₁).isBounded
    (SmallMean.isCompact_gridCube _ _ ((i : ℕ) + 1) J₂).isBounded p q
  have hdev : ∀ t ∈ Icc (0 : ℝ) 1, infDist (γ.toFun t) (segment ℝ p q) ≤
      maxDeviation σ sl.set (gridCube n W 0 (i : ℕ) J₁) (gridCube n W 0 ((i : ℕ) + 1) J₂) p q :=
    fun t ht => le_maxDeviation hB hu hv hopt ht
  have hJ := mul_zNorm_J_sub_le X b hn hW0 hWn c i
  have hR : X.R b n W c i J₁ J₂ = radiusConst m + W⁻¹ *
      maxDeviation σ sl.set (gridCube n W 0 (i : ℕ) J₁) (gridCube n W 0 ((i : ℕ) + 1) J₂) p q := by
    unfold Setting.R
    rw [ite_eq_left hJ]
  -- the closure of the block is far from the segment
  have hfar : ∀ y ∈ closure (block n W L i z),
      X.R b n W c i J₁ J₂ * W ≤ infDist y (segment ℝ p q) := by
    have hsub : block n W L i z ⊆ {y | X.R b n W c i J₁ J₂ * W ≤ infDist y (segment ℝ p q)} := by
      intro y hy
      have hy' : y ∉ tube X b K n W c i := Set.disjoint_left.1 hdisj hy
      simp only [tube, segTube, mem_ofPred_eq, not_le] at hy'
      exact hy'.le
    exact closure_minimal hsub (isClosed_le continuous_const (continuous_infDist_pt _))
  have hrc : 2 ≤ radiusConst m := by
    unfold radiusConst
    linarith only [Real.sqrt_nonneg (m : ℝ)]
  have h2W : 2 ≤ radiusConst m * W :=
    hrc.trans (le_mul_of_one_le_right (zero_le_two.trans hrc) hW)
  have hρeq : ∀ t ∈ Icc (0 : ℝ) 1, X.ρ c (γ.toFun t) = X.ρ c' (γ.toFun t) := by
    intro t ht
    refine hagree _ fun y hy hyc => ?_
    have e1 := hfar y hyc
    have e2 := infDist_le_infDist_add_dist (s := segment ℝ p q) (x := y) (y := γ.toFun t)
    have e3 := hdev t ht
    rw [mem_closedBall] at hy
    have hmd : maxDeviation σ sl.set (gridCube n W 0 (i : ℕ) J₁) (gridCube n W 0 ((i : ℕ) + 1) J₂)
        p q = (X.R b n W c i J₁ J₂ - radiusConst m) * W := by
      rw [hR]
      field_simp
      ring
    rw [hmd] at e3
    linarith only [e1, e2, e3, hy, h2W]
  have hcost' : γ.cost (fun y => ENNReal.ofReal (σ' y)) =
      γ.cost (fun y => ENNReal.ofReal (σ y)) :=
    γ.cost_congr fun t ht => by simp only [hσ, hσ', Slab.density, hρeq t ht]
  have hle : restrictedInf σ' sl.set u v ≤ γ.cost (fun y => ENNReal.ofReal (σ' y)) :=
    restrictedInf_le_cost γ h0 h1 hS
  calc sl.passTime b (X.ρ c') u v = (restrictedInf σ' sl.set u v).toReal := rfl
    _ ≤ (γ.cost (fun y => ENNReal.ofReal (σ' y))).toReal :=
        ENNReal.toReal_mono
          (γ.cost_ne_top ENNReal.ofReal_ne_top fun y => ENNReal.ofReal_le_ofReal (hσ'b y)) hle
    _ ≤ D + ε := by
        rw [hcost']
        exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hD0 hε.le) hcostD

/-- **The tube lemma** (the proof of Lemma `lem:fewtranslates`): if the densities of `c` and
`c'` agree at every point whose closed unit ball misses the closure of the block `G` of the slab
`i`, and `G` does not meet the tube of `c` in its slab, then `F(c') ≤ F(c)`, for `W ≥ 1` and
`W √m ≤ n/4`. -/
theorem F_le_of_disjoint_tube (X : Setting.{u} m) {b : ℝ} (hb : X.IsUpperBound b) {K : ℕ}
    {n W : ℝ} (hn : 0 < n) (hW : 1 ≤ W) (hWn : W * Real.sqrt m ≤ n / 4) (L : ℕ) (i : Fin K)
    (z : Fin m → ℤ) {c c' : X.Ω}
    (hagree : ∀ x, closedBall x 1 ⊆ (closure (block n W L i z))ᶜ → X.ρ c x = X.ρ c' x)
    (hdisj : Disjoint (block n W L i z) (tube X b K n W c i)) :
    X.F b K n 0 c' ≤ X.F b K n 0 c := by
  have hxm := isLexLeastMinimizer_lexMinimizer b (X.isValidChain c hn.le) K 0
  set x := lexMinimizer b (X.ρ c) K n 0 with hxdef
  have hFc : X.F b K n 0 c = slabSum b (X.ρ c) K n 0 x := hxm.2.1.symm
  have hFc' : X.F b K n 0 c' ≤ slabSum b (X.ρ c') K n 0 x :=
    ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact slabSum_nonneg _ _ _ _ _ _⟩
      (⟨x, hxm.1⟩ : {x : Fin (K + 1) → Pt m // IsAdmissible K n 0 x})
  have hslab : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ i' : Fin K,
      (chainSlab n 0 i').passTime b (X.ρ c') (x i'.castSucc) (x i'.succ) ≤
        (chainSlab n 0 i').passTime b (X.ρ c) (x i'.castSucc) (x i'.succ) +
          if i' = i then ε else 0 := by
    intro ε hε hε1 i'
    by_cases hii : i' = i
    · subst hii
      rw [ite_eq_left rfl]
      exact passTime_le_of_disjoint_tube X hb hn hW hWn L i' z hagree hdisj hε hε1
    · rw [ite_eq_right hii, add_zero]
      refine le_of_eq (Slab.passTime_congr _ b (fun y hy hf => ?_) _ _)
      exact (hagree y (closedBall_subset_compl_closure_block hn.le
        (fun h => hii (Fin.ext h)) z hy hf)).symm
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : 0 < min ε 1 := lt_min hε one_pos
  have hsum := Finset.sum_le_sum fun i' (_ : i' ∈ Finset.univ) =>
    hslab (min ε 1) hε' (min_le_right _ _) i'
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i (fun _ => min ε 1),
    ite_eq_left (Finset.mem_univ i)] at hsum
  rw [hFc]
  refine hFc'.trans ?_
  unfold slabSum
  linarith only [hsum, min_le_left ε 1]

end IsotropicVariance.Paper.Proofs.Gain
