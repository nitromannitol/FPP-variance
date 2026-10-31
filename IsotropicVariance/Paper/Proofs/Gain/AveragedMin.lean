/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Steps
public import IsotropicVariance.Infra.Measurability.SlabVersion
import IsotropicVariance.Infra.TimeConstant.Mean
public import IsotropicVariance.Paper.Defs.Minimum

/-!
# The averaged minimum is a square-integrable function of the noise in the slabs

The slab minima `F_j` of Section `sec:gain` and their average `F̄`:

* the slabs of a translated chain are those of the untranslated chain when the translation is
  transverse (`chainSlab_of_lon_eq_zero`), and the admissible points of equation `eq:F` lie in
  their slabs (`mem_chainSlab_set_of_isAdmissible`);
* `0 ≤ F ≤ K b n` (`F_nonneg`, `F_le`);
* `F_j` is almost surely equal to a function measurable for the information of the closed union
  `[0, Kn] × ℝ^m` of the slabs (`exists_F_version`): replace each slab passage time by a version
  determined by the noise in its slab and continuous in the endpoints (`Infra.Slab`), and take
  the infimum over a countable dense set of admissible points;
* hence `F̄` is square integrable and has such a version (`averagedMin_regular`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper Infra.Slab

variable {m : ℕ}

/-! ### Geometry of the chain -/

/-- The slabs of a chain translated transversally are those of the untranslated chain. -/
theorem chainSlab_of_lon_eq_zero (s : ℝ) {τ : Pt m} (hτ : Pt.lon τ = 0) (i : ℕ) :
    chainSlab s τ i = chainSlab s 0 i := by
  simp [chainSlab, hτ]

/-- **The admissible points of equation `eq:F` lie in their slabs.** -/
theorem mem_chainSlab_set_of_isAdmissible {M : ℕ} {s : ℝ} {τ : Pt m}
    {x : Fin (M + 1) → Pt m} (hx : IsAdmissible M s τ x) (i : Fin M) :
    x i.castSucc ∈ (chainSlab s τ i).set ∧ x i.succ ∈ (chainSlab s τ i).set := by
  obtain ⟨-, -, hlon, hstep⟩ := hx
  have h₁ := hlon i.castSucc
  have h₂ := hlon i.succ
  rw [Pt.lon_sub] at h₁ h₂
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h₁ h₂
  have hs : 0 ≤ s := by
    have := (norm_nonneg _).trans (hstep i)
    linarith
  rw [mem_chainSlab_set, mem_chainSlab_set]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

variable (X : Setting.{u} m)

/-- The slab minimum is nonnegative. -/
theorem F_nonneg (b : ℝ) (M : ℕ) (s : ℝ) (τ : Pt m) (ω : X.Ω) : 0 ≤ X.F b M s τ ω :=
  Real.iInf_nonneg fun _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- **The slab minimum is at most `M b s`**: the straight admissible points cost at most `b s` in
each slab. -/
theorem F_le {b : ℝ} (hb : X.IsUpperBound b) (M : ℕ) {s : ℝ} (hs : 0 ≤ s) (τ : Pt m)
    (ω : X.Ω) : X.F b M s τ ω ≤ M * b * s := by
  set x := fun i : Fin (M + 1) => τ + (((i : ℕ) : ℝ) * s) • (e₁ : Pt m)
  have hx : IsAdmissible M s τ x := isAdmissible_straight M _ hs τ
  have hbdd : BddBelow (Set.range fun x : {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x} =>
      slabSum b (X.ρ ω) M s τ x) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg⟩
  refine (ciInf_le hbdd ⟨x, hx⟩).trans ?_
  calc slabSum b (X.ρ ω) M s τ x
      ≤ ∑ _i : Fin M, b * s := by
        refine Finset.sum_le_sum fun i _ => ?_
        obtain ⟨h₁, h₂⟩ := mem_chainSlab_set_of_isAdmissible hx i
        refine (slabTime_le_mul_dist X hb _ ω h₁ h₂).trans (le_of_eq ?_)
        congr 1
        rw [dist_eq_norm]
        simp only [x, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Paper.norm_e₁,
          mul_one, Real.norm_eq_abs]
        rw [show ((i : ℕ) : ℝ) * s - ((i : ℕ) + 1) * s = -s by ring, abs_neg, abs_of_nonneg hs]
    _ = M * b * s := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-! ### A version determined by the noise in the slabs -/

/-- The infimum of a nonnegative continuous function is its infimum over a dense set. -/
theorem iInf_eq_iInf_of_dense {A : Type*} [TopologicalSpace A] [Nonempty A] {f : A → ℝ}
    (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) {D : Set A} (hD : Dense D) :
    ⨅ x, f x = ⨅ d : D, f d := by
  have : Nonempty D := hD.nonempty.to_subtype
  have hbdd : BddBelow (range f) := ⟨0, by rintro _ ⟨x, rfl⟩; exact h0 x⟩
  have hbddD : BddBelow (range fun d : D => f d) := ⟨0, by rintro _ ⟨x, rfl⟩; exact h0 x⟩
  refine le_antisymm (le_ciInf fun d => ciInf_le hbdd d) (le_ciInf fun x => ?_)
  have hclosed : IsClosed {y | (⨅ d : D, f d) ≤ f y} := isClosed_le continuous_const hf
  have hsub : D ⊆ {y | (⨅ d : D, f d) ≤ f y} := fun y hy => ciInf_le hbddD ⟨y, hy⟩
  have hx : x ∈ closure D := by rw [hD.closure_eq]; exact mem_univ x
  exact hclosed.closure_subset_iff.2 hsub hx

/-- The slab `i < M` of a chain from a transverse point lies in the closed strip `[0, Ms]`. -/
theorem chainSlab_set_subset_strip {s : ℝ} (hs : 0 ≤ s) {M : ℕ} (i : Fin M) :
    (chainSlab s (0 : Pt m) i).set ⊆ {x : Pt m | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ M * s} := by
  intro x hx
  rw [mem_chainSlab_set, Pt.lon_zero, zero_add] at hx
  have hi : ((i : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast i.isLt
  constructor <;> nlinarith [hx.1, hx.2]

/-- **The slab minimum is determined by the noise in its slabs** (up to a null set): for a
transverse starting point, `F` is almost surely equal to a function measurable for the
information of the closed strip `[0, Ms] × ℝ^m`. -/
theorem exists_F_version {b : ℝ} (hb : X.IsUpperBound b) (M : ℕ) {s : ℝ} (hs : 0 ≤ s)
    {τ : Pt m} (hτ : Pt.lon τ = 0) :
    ∃ G : X.Ω → ℝ, Measurable[X.info {x | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ M * s}] G ∧
      X.F b M s τ =ᵐ[X.P] G := by
  classical
  choose V _ hVc hVinfo hVae using fun i : Fin M => exists_slabTime_version X hb (chainSlab s 0 i)
  let A := {x : Fin (M + 1) → Pt m // IsAdmissible M s τ x}
  have : Nonempty A := ⟨⟨_, isAdmissible_straight M _ hs τ⟩⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense A
  have : Countable D := hDc.to_subtype
  let f : X.Ω → A → ℝ := fun ω x =>
    ∑ i : Fin M, max (V i ω ((x : Fin (M + 1) → Pt m) i.castSucc, (x : Fin (M + 1) → Pt m) i.succ)) 0
  have hfc : ∀ ω, Continuous (f ω) := fun ω =>
    continuous_finsetSum _ fun i _ => ((hVc i ω).comp (((continuous_apply i.castSucc).comp
      continuous_subtype_val).prodMk ((continuous_apply i.succ).comp
        continuous_subtype_val))).max continuous_const
  have hf0 : ∀ ω x, 0 ≤ f ω x := fun ω x => Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hfm : ∀ x : A, Measurable[X.info {x | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ M * s}]
      fun ω => f ω x := by
    intro x
    refine Finset.measurable_sum _ fun i _ => Measurable.max ?_ measurable_const
    have h := (@measurable_pi_iff X.Ω (Pt m × Pt m) (fun _ => ℝ) (X.info (chainSlab s 0 i).set) _
      (V i)).1 (hVinfo i) ((x : Fin (M + 1) → Pt m) i.castSucc, (x : Fin (M + 1) → Pt m) i.succ)
    exact h.mono (X.info_mono (chainSlab_set_subset_strip hs i)) le_rfl
  refine ⟨fun ω => ⨅ d : D, f ω d, Measurable.iInf fun d => hfm d, ?_⟩
  filter_upwards [ae_all_iff.2 hVae] with ω hω
  have heq : (fun x : A => slabSum b (X.ρ ω) M s τ x) = f ω := by
    funext x
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨h₁, h₂⟩ := mem_chainSlab_set_of_isAdmissible x.2 i
    rw [IsotropicVariance.Paper.Proofs.Gain.chainSlab_of_lon_eq_zero s hτ] at h₁ h₂ ⊢
    rw [hω i _ h₁ _ h₂, max_eq_left (slabTime_nonneg X b _ ω _ _)]
    rfl
  change (⨅ x : A, slabSum b (X.ρ ω) M s τ x) = _
  rw [heq]
  exact iInf_eq_iInf_of_dense (hfc ω) (hf0 ω) hDd

/-- **The averaged minimum is square integrable and determined by the noise in the slabs** (up
to a null set). -/
theorem averagedMin_regular {b : ℝ} (hb : X.IsUpperBound b) (K : ℕ) {n : ℝ} (hn : 0 ≤ n)
    (W : ℝ) (L : ℕ) :
    MemLp (averagedMin X b K n W L) 2 X.P ∧
      ∃ Z' : X.Ω → ℝ, Measurable[X.info {x | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ K * n}] Z' ∧
        averagedMin X b K n W L =ᵐ[X.P] Z' := by
  have hτ : ∀ j : ℕ, Pt.lon (((j : ℝ) * L * W) • e₂ m) = 0 := fun j => by
    rw [Pt.lon_smul, lon_e₂, mul_zero]
  choose G hGm hGae using fun j : ℕ => exists_F_version X hb K hn (hτ j)
  let Z' := fun ω => ((colCount K : ℝ))⁻¹ * ∑ j ∈ Finset.range (colCount K), G j ω
  have hZ'm : Measurable[X.info {x | 0 ≤ Pt.lon x ∧ Pt.lon x ≤ K * n}] Z' :=
    (Finset.measurable_sum _ fun j _ => hGm j).const_mul _
  have hae : averagedMin X b K n W L =ᵐ[X.P] Z' := by
    have h := (Filter.eventually_all_finset (Finset.range (colCount K))).2 fun j _ => hGae j
    filter_upwards [h] with ω hω
    simp only [averagedMin, Z']
    congr 1
    exact Finset.sum_congr rfl hω
  refine ⟨?_, Z', hZ'm, hae⟩
  have hbd : ∀ ω, ‖averagedMin X b K n W L ω‖ ≤ K * b * n := by
    intro ω
    have hb0 : 0 ≤ b := upperBound_nonneg X hb ω
    have hF : ∀ j ∈ Finset.range (colCount K),
        X.F b K n (((j : ℝ) * L * W) • e₂ m) ω ∈ Icc 0 (K * b * n) :=
      fun j _ => ⟨F_nonneg X b K n _ ω, F_le X hb K hn _ ω⟩
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range (colCount K), X.F b K n (((j : ℝ) * L * W) • e₂ m) ω :=
      Finset.sum_nonneg fun j hj => (hF j hj).1
    have hsum : ∑ j ∈ Finset.range (colCount K), X.F b K n (((j : ℝ) * L * W) • e₂ m) ω ≤
        (colCount K : ℝ) * (K * b * n) := by
      calc _ ≤ ∑ _j ∈ Finset.range (colCount K), (K : ℝ) * b * n :=
            Finset.sum_le_sum fun j hj => (hF j hj).2
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [averagedMin]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) hsum0)]
    by_cases hc : (colCount K : ℝ) = 0
    · rw [hc, inv_zero, zero_mul]; positivity
    · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc))]
      exact hsum
  exact MemLp.of_bound ((hZ'm.mono (X.info_le _) le_rfl).aestronglyMeasurable.congr hae.symm)
    (K * b * n) (ae_of_all _ hbd)

end IsotropicVariance.Paper.Proofs.Gain
