/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Blocks
public import IsotropicVariance.Infra.Measurability.SlabVersion

/-!
# Locality of block couplings: the density away from a block is unchanged

Replacing the noise in a set `G` does not change the density at the points whose closed unit
ball misses the closure of `G` (the locality condition of Assumption `ass:local`): if old and new
noise are, almost surely, indistinguishable by every event of the information off `G` (the
`agree_compl` field of a block coupling, Section `sec:gain`), then almost surely the old
and new densities agree at every point `x` with `dist(x, G) > 1`, simultaneously for all such `x`.

This serves Section `sec:gain`: "Changing `ω|_G` can increase `T^{(i)}(u, v)` only if some curve in
`Π_{T^{(i)}}(u, v)` passes within distance one of `G`", which gives the tube bound of the proof of
Lemma `lem:fewtranslates`.

**Proof.** With `U = (closure G)ᶜ` (open, contained in `Gᶜ`), the density at the points whose
closed unit ball lies in `U` is jointly measurable for the information of `U` and the Borel sets
(`Setting.determined_joint`), so it factors as `ρ(ω, x) = h(Φ(ω), x)` with `Φ : Ω → ℕ → Bool`
measurable for the information of `U` (`Infra.Slab.exists_factor_of_measurable_prod`). The
countably many events `{Φ(·) k = true}` lie in the information of `Gᶜ`, so almost surely
`Φ(old) = Φ(new)`, and then `ρ(old, x) = ρ(new, x)` for every such `x`.

* `ae_rho_eq_of_agree_compl_closure`, `ae_rho_eq_of_agree_compl`: the general statements, for
  points whose closed unit ball misses `closure G`, and for points at distance `> 1` from `G`.
* `IsBlockCoupling.ae_rho_eq(_closure)`: for couplings.
* `restrictedPassageTime_congr`, `Slab.passTime_congr`: restricted and slab passage times only
  see the density on the set, away from the faces.
* `ae_slabTime_eq_of_agree_compl`, `IsBlockCoupling.ae_slabTime_eq`: hence almost surely the slab
  passage times of every slab whose points at distance `> 1` from its faces are at distance `> 1`
  from `G` are unchanged.
-/

@[expose] public section

open MeasureTheory Set Metric

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

variable {m : ℕ}

/-- A point at distance more than one from `G` has its closed unit ball in the complement of the
closure of `G`. -/
theorem closedBall_subset_compl_closure_of_one_lt_infDist {G : Set (Pt m)} {x : Pt m}
    (h : 1 < infDist x G) : closedBall x 1 ⊆ (closure G)ᶜ := by
  intro y hy hyG
  have h1 : infDist x (closure G) ≤ dist x y := infDist_le_dist_of_mem hyG
  rw [infDist_closure] at h1
  rw [mem_closedBall, dist_comm] at hy
  linarith

/-- **Locality, closure form**: if old and new noise are almost surely indistinguishable by the
information off `G`, then almost surely the old and new densities agree at every point whose
closed unit ball misses the closure of `G`. -/
theorem ae_rho_eq_of_agree_compl_closure (X : Setting.{u} m) {G : Set (Pt m)} {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (h : ∀ A : Set X.Ω, MeasurableSet[X.info Gᶜ] A → ∀ᵐ ω ∂P', (old ω ∈ A ↔ new ω ∈ A)) :
    ∀ᵐ ω ∂P', ∀ x, closedBall x 1 ⊆ (closure G)ᶜ → X.ρ (old ω) x = X.ρ (new ω) x := by
  have hU : IsOpen (closure G)ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨Φ, hΦ, g, -, hg⟩ :=
    Infra.Slab.exists_factor_of_measurable_prod (X.determined_joint _ hU)
  have hle : X.info (closure G)ᶜ ≤ X.info Gᶜ := X.info_mono (compl_subset_compl.2 subset_closure)
  have hev : ∀ k : ℕ, ∀ᵐ ω ∂P', Φ (old ω) k = Φ (new ω) k := by
    intro k
    have hk : Measurable[X.info (closure G)ᶜ] fun ω => Φ ω k := (measurable_pi_apply k).comp hΦ
    have hA : MeasurableSet[X.info Gᶜ] ((fun ω => Φ ω k) ⁻¹' {true}) :=
      hle _ (hk (measurableSet_singleton true))
    filter_upwards [h _ hA] with ω hω
    simp only [mem_preimage, mem_singleton_iff] at hω
    cases h1 : Φ (old ω) k <;> cases h2 : Φ (new ω) k <;> simp_all
  filter_upwards [ae_all_iff.2 hev] with ω hω x hx
  have hΦeq : Φ (old ω) = Φ (new ω) := funext hω
  have e1 := hg (old ω) ⟨x, hx⟩
  have e2 := hg (new ω) ⟨x, hx⟩
  simp only at e1 e2
  rw [e1, e2, hΦeq]

/-- **Locality**: if old and new noise are almost surely indistinguishable by the information off
`G`, then almost surely the old and new densities agree at every point at distance more than one
from `G`. -/
theorem ae_rho_eq_of_agree_compl (X : Setting.{u} m) {G : Set (Pt m)} {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (h : ∀ A : Set X.Ω, MeasurableSet[X.info Gᶜ] A → ∀ᵐ ω ∂P', (old ω ∈ A ↔ new ω ∈ A)) :
    ∀ᵐ ω ∂P', ∀ x, 1 < infDist x G → X.ρ (old ω) x = X.ρ (new ω) x := by
  filter_upwards [ae_rho_eq_of_agree_compl_closure X h] with ω hω x hx
  exact hω x (closedBall_subset_compl_closure_of_one_lt_infDist hx)

/-- **Locality of a block coupling**, closure form. -/
theorem IsBlockCoupling.ae_rho_eq_closure {X : Setting.{u} m} {G : Set (Pt m)} {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (h : X.IsBlockCoupling G P' old new) :
    ∀ᵐ ω ∂P', ∀ x, closedBall x 1 ⊆ (closure G)ᶜ → X.ρ (old ω) x = X.ρ (new ω) x :=
  ae_rho_eq_of_agree_compl_closure X h.agree_compl

/-- **Locality of a block coupling**: almost surely the old and new densities agree at every point
at distance more than one from the block. -/
theorem IsBlockCoupling.ae_rho_eq {X : Setting.{u} m} {G : Set (Pt m)} {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (h : X.IsBlockCoupling G P' old new) :
    ∀ᵐ ω ∂P', ∀ x, 1 < infDist x G → X.ρ (old ω) x = X.ρ (new ω) x :=
  ae_rho_eq_of_agree_compl X h.agree_compl

/-! ### Passage times only see the density where they are computed -/

/-- **Restricted passage times only see the density on the set.** -/
theorem restrictedPassageTime_congr {σ σ' : Pt m → ℝ} {S : Set (Pt m)}
    (h : ∀ x ∈ S, σ x = σ' x) (u v : Pt m) :
    restrictedPassageTime σ S u v = restrictedPassageTime σ' S u v := by
  unfold restrictedPassageTime
  congr 1
  refine iInf_congr fun γ => iInf_congr fun _ => iInf_congr fun _ => iInf_congr fun hγ => ?_
  exact γ.cost_congr fun t ht => by rw [h _ (hγ t ht)]

/-- **Slab passage times only see the density in the slab away from its faces.** -/
theorem Slab.passTime_congr (sl : Slab m) (b : ℝ) {σ σ' : Pt m → ℝ}
    (h : ∀ x ∈ sl.set, 1 < infDist x sl.faces → σ x = σ' x) (u v : Pt m) :
    sl.passTime b σ u v = sl.passTime b σ' u v := by
  unfold Slab.passTime
  refine restrictedPassageTime_congr (fun x hx => ?_) u v
  unfold Slab.density
  split_ifs with h1
  · rfl
  · exact h x hx (not_le.1 h1)

/-- **Slab passage times away from `G` are unchanged**: if old and new noise are almost surely
indistinguishable by the information off `G`, then almost surely, for every slab whose points at
distance more than one from its faces are at distance more than one from `G`, the old and new
slab passage times agree between all endpoints. -/
theorem ae_slabTime_eq_of_agree_compl (X : Setting.{u} m) (b : ℝ) {G : Set (Pt m)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (h : ∀ A : Set X.Ω, MeasurableSet[X.info Gᶜ] A → ∀ᵐ ω ∂P', (old ω ∈ A ↔ new ω ∈ A)) :
    ∀ᵐ ω ∂P', ∀ sl : Slab m, (∀ x ∈ sl.set, 1 < infDist x sl.faces → 1 < infDist x G) →
      ∀ u v, X.slabTime b sl (old ω) u v = X.slabTime b sl (new ω) u v := by
  filter_upwards [ae_rho_eq_of_agree_compl X h] with ω hω sl hsl u v
  exact Slab.passTime_congr sl b (fun x hx hf => hω x (hsl x hx hf)) u v

/-- **Slab passage times away from a replaced block are unchanged** (Section `sec:gain`,
the slabs other than that of the block). -/
theorem IsBlockCoupling.ae_slabTime_eq {X : Setting.{u} m} (b : ℝ) {G : Set (Pt m)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (h : X.IsBlockCoupling G P' old new) :
    ∀ᵐ ω ∂P', ∀ sl : Slab m, (∀ x ∈ sl.set, 1 < infDist x sl.faces → 1 < infDist x G) →
      ∀ u v, X.slabTime b sl (old ω) u v = X.slabTime b sl (new ω) u v :=
  ae_slabTime_eq_of_agree_compl X b h.agree_compl

end IsotropicVariance.Paper.Proofs.Gain
