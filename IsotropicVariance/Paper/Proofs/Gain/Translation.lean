/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Gain.Steps
import IsotropicVariance.Infra.TimeConstant.Mean
import IsotropicVariance.Paper.Proofs.Gain.AveragedMin
import IsotropicVariance.Paper.Proofs.Profiles.Basic

/-!
# Proposition `prop:gain`: translation covariance

The translated slab minima `F_j` of Section `sec:gain` are the slab
minimum `F_0` of the noise moved by the transverse translation `x ↦ x − j L W e₂`, and moving the
noise moves the block couplings and the label resamplings with it. This file proves:

* `shiftBy v`, the translation by `−v`, is a proper rigid motion (`isProperRigidMotion_shiftBy`).
* Restricted passage times move with isometries (`restrictedPassageTime_comp_isometryEquiv`).
* Slab passage times and slab minima are covariant under transverse translations
  (`slabTime_act_shiftBy`, `F_eq_F_zero_act`).
* The translation by `j L W e₂` maps the block `(i, z + j L e₀)` to the block `(i, z)`
  (`image_shiftBy_block`, `image_shiftBy_block_add`), and `z ↦ z + j L e₀` preserves the block
  indices of every offset (`isBlockIndex_add_blockShift_iff`).
* Label resamplings are transported by proper rigid motions (`LabelResamplingData.transport`).
* The label energy of `Z ∘ act (shiftBy (j L W e₂))` is the label energy of `Z` for the transported
  family (`labelCouplingEnergy_comp_act_shiftBy`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

universe u

namespace IsotropicVariance.Paper.Proofs.Gain

open IsotropicVariance.Paper

/-! ### Coordinates -/

section Coordinates

variable {m : ℕ}

/-- A point is determined by its coordinates. -/
theorem Pt.ext_coord {x y : Pt m} (h₁ : Pt.lon x = Pt.lon y) (h₂ : ∀ k, Pt.tr x k = Pt.tr y k) :
    x = y :=
  WithLp.ofLp_injective 2 (Prod.ext h₁ (PiLp.ext h₂))

/-- The transverse coordinates of `e₂`. -/
theorem tr_e₂ (k : Fin m) : Pt.tr (e₂ m) k = if (k : ℕ) = 0 then 1 else 0 := rfl

end Coordinates

/-! ### Translations are proper rigid motions -/

/-- The translation by `−v`, `x ↦ x − v`. -/
noncomputable def shiftBy {m : ℕ} (v : Pt m) : Pt m ≃ᵃⁱ[ℝ] Pt m :=
  AffineIsometryEquiv.constVAdd ℝ (Pt m) (-v)

/-- `shiftBy v x = x − v`. -/
theorem shiftBy_apply {m : ℕ} (v x : Pt m) : shiftBy v x = x - v := by
  simp [shiftBy, neg_add_eq_sub]

/-- The translation `shiftBy v` is a proper rigid motion. -/
theorem isProperRigidMotion_shiftBy {m : ℕ} (v : Pt m) : IsProperRigidMotion (shiftBy v) :=
  Infra.TimeConstant.isProperRigidMotion_translation (-v)

/-- Moving the noise by `shiftBy v` translates the density: `ρ(act ω, y) = ρ(ω, y + v)`. -/
theorem ρ_act_shiftBy {m : ℕ} (X : Setting m) (v : Pt m) (ω : X.Ω) (y : Pt m) :
    X.ρ (X.act (shiftBy v) ω) y = X.ρ ω (y + v) := by
  have h := X.covariant (shiftBy v) (isProperRigidMotion_shiftBy v) ω (y + v)
  rwa [shiftBy_apply, add_sub_cancel_right] at h

/-! ### Restricted passage times and isometries -/

section Isometry

open Infra.TimeConstant (mapCurve cost_mapCurve)

variable {m : ℕ}

/-- The infimum defining a restricted passage time decreases when the curves of `(σ', S, u, v)`
are moved by an isometry into the admissible curves of `(σ, S', u', v')`. -/
private theorem restrictedInf_le (g : Pt m ≃ᵢ Pt m) {σ σ' : Pt m → ℝ}
    (hσ : ∀ x, σ' x = σ (g x)) {S S' : Set (Pt m)} (hS : ∀ x ∈ S, g x ∈ S') {u v u' v' : Pt m}
    (hu : g u = u') (hv : g v = v') :
    (⨅ (γ : RectifiableCurve (Pt m)) (_ : γ.toFun 0 = u') (_ : γ.toFun 1 = v')
        (_ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S'), γ.cost (fun x => ENNReal.ofReal (σ x))) ≤
      ⨅ (γ : RectifiableCurve (Pt m)) (_ : γ.toFun 0 = u) (_ : γ.toFun 1 = v)
        (_ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ S), γ.cost (fun x => ENNReal.ofReal (σ' x)) := by
  refine le_iInf fun γ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hγ => ?_
  have hc := cost_mapCurve g γ (fun x => ENNReal.ofReal (σ x))
  have hσ' : ((fun x => ENNReal.ofReal (σ x)) ∘ g) = fun x => ENNReal.ofReal (σ' x) := by
    funext x
    simp [hσ]
  rw [hσ'] at hc
  have h0' : (mapCurve g γ).toFun 0 = u' := by simp [mapCurve, h0, hu]
  have h1' : (mapCurve g γ).toFun 1 = v' := by simp [mapCurve, h1, hv]
  have hS' : ∀ t ∈ Icc (0 : ℝ) 1, (mapCurve g γ).toFun t ∈ S' := fun t ht => hS _ (hγ t ht)
  calc _ ≤ (mapCurve g γ).cost (fun x => ENNReal.ofReal (σ x)) :=
        iInf_le_of_le (mapCurve g γ) (iInf_le_of_le h0' (iInf_le_of_le h1' (iInf_le _ hS')))
    _ = _ := hc

/-- **Restricted passage times move with isometries**: pulling the density back by `g` is
moving the set and the endpoints by `g`. -/
theorem restrictedPassageTime_comp_isometryEquiv (g : Pt m ≃ᵢ Pt m) (σ : Pt m → ℝ)
    (S : Set (Pt m)) (u v : Pt m) :
    restrictedPassageTime (σ ∘ g) S u v = restrictedPassageTime σ (g '' S) (g u) (g v) := by
  unfold restrictedPassageTime
  congr 1
  refine le_antisymm ?_ (restrictedInf_le g (fun x => rfl) (fun x hx => mem_image_of_mem g hx)
    rfl rfl)
  refine restrictedInf_le g.symm (fun x => by simp) ?_ (g.symm_apply_apply u)
    (g.symm_apply_apply v)
  rintro _ ⟨x, hx, rfl⟩
  simpa using hx

/-- Restricted passage times move with rigid motions. -/
theorem restrictedPassageTime_comp_affineIsometryEquiv (g : Pt m ≃ᵃⁱ[ℝ] Pt m) (σ : Pt m → ℝ)
    (S : Set (Pt m)) (u v : Pt m) :
    restrictedPassageTime (σ ∘ g) S u v = restrictedPassageTime σ (g '' S) (g u) (g v) :=
  restrictedPassageTime_comp_isometryEquiv g.toIsometryEquiv σ S u v

end Isometry

/-! ### Slabs perpendicular to `e₁` are invariant under transverse translations -/

section Slabs

variable {m : ℕ}

/-- A translation by `v` maps a set onto itself if membership is invariant under it. -/
theorem image_constVAdd_eq {v : Pt m} {S : Set (Pt m)} (hS : ∀ x, v + x ∈ S ↔ x ∈ S) :
    AffineIsometryEquiv.constVAdd ℝ (Pt m) v '' S = S := by
  ext y
  simp only [AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hS x).2 hx
  · intro hy
    refine ⟨-v + y, (hS _).1 ?_, by simp⟩
    simpa using hy

/-- The slab `[a, a + s] × ℝ^m`. -/
theorem mem_e1Slab_set {a s : ℝ} {x : Pt m} :
    x ∈ (e1Slab a s).set ↔ a ≤ Pt.lon x ∧ Pt.lon x ≤ a + s := by
  rw [e1Slab_set]
  rfl

/-- The faces `{a, a + s} × ℝ^m` of the slab `[a, a + s] × ℝ^m`. -/
theorem mem_e1Slab_faces {a s : ℝ} {x : Pt m} :
    x ∈ (e1Slab a s).faces ↔ Pt.lon x = a ∨ Pt.lon x = a + s := by
  simp only [Slab.faces, e1Slab, AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, mem_image,
    mem_ofPred_eq]
  constructor
  · rintro ⟨y, h, rfl⟩
    simp only [Pt.lon_add, Pt.lon_smul, Pt.lon_e₁, mul_one]
    rcases h with h | h
    · left; linarith
    · right; linarith
  · intro h
    refine ⟨x - a • e₁, ?_, by abel⟩
    simp only [Pt.lon_sub, Pt.lon_smul, Pt.lon_e₁, mul_one]
    rcases h with h | h
    · left; linarith
    · right; linarith

/-- A transverse translation maps the slab `[a, a + s] × ℝ^m` onto itself. -/
theorem image_constVAdd_e1Slab_set {v : Pt m} (hv : Pt.lon v = 0) (a s : ℝ) :
    AffineIsometryEquiv.constVAdd ℝ (Pt m) v '' (e1Slab a s).set = (e1Slab a s).set :=
  image_constVAdd_eq fun x => by simp [mem_e1Slab_set, hv]

/-- A transverse translation maps the faces of the slab `[a, a + s] × ℝ^m` onto themselves. -/
theorem image_constVAdd_e1Slab_faces {v : Pt m} (hv : Pt.lon v = 0) (a s : ℝ) :
    AffineIsometryEquiv.constVAdd ℝ (Pt m) v '' (e1Slab a s).faces = (e1Slab a s).faces :=
  image_constVAdd_eq fun x => by simp [mem_e1Slab_faces, hv]

/-- **Slab passage times are covariant under transverse translations**: for the slab
`[a, a + s] × ℝ^m`, the passage time for the density `σ' = σ(· + v)` is the passage time for `σ`
between the translated endpoints. -/
theorem e1Slab_passTime_translate {v : Pt m} (hv : Pt.lon v = 0) (a s b : ℝ)
    {σ σ' : Pt m → ℝ} (hσ : ∀ x, σ' x = σ (x + v)) (x y : Pt m) :
    (e1Slab a s).passTime b σ' x y = (e1Slab a s).passTime b σ (x + v) (y + v) := by
  set g := AffineIsometryEquiv.constVAdd ℝ (Pt m) v with hg
  have hdens : (e1Slab a s).density b σ' = (e1Slab a s).density b σ ∘ g := by
    funext x
    have hinf : infDist (g x) (e1Slab a s).faces = infDist x (e1Slab a s).faces := by
      conv_lhs => rw [← image_constVAdd_e1Slab_faces hv a s]
      exact infDist_image g.isometry
    simp only [Slab.density, Function.comp_apply, hinf, hσ]
    simp [hg, add_comm v x]
  unfold Slab.passTime
  rw [hdens, restrictedPassageTime_comp_affineIsometryEquiv, image_constVAdd_e1Slab_set hv]
  simp [hg, add_comm v]

/-- **Slab passage times move with the noise** (Section `sec:gain`): moving the noise by the
transverse translation `x ↦ x − v` translates the slab passage times of `[in, (i+1)n] × ℝ^m` by
`v`. -/
theorem slabTime_act_shiftBy (X : Setting m) (b n : ℝ) (i : ℕ) {v : Pt m} (hv : Pt.lon v = 0)
    (ω : X.Ω) (x y : Pt m) :
    X.slabTime b (chainSlab n 0 i) (X.act (shiftBy v) ω) x y =
      X.slabTime b (chainSlab n 0 i) ω (x + v) (y + v) :=
  e1Slab_passTime_translate hv _ _ b (ρ_act_shiftBy X v ω) x y

/-- Translating admissible points by `v` gives the admissible points of the chain translated by
`v`. -/
theorem isAdmissible_add_iff {M : ℕ} {s : ℝ} (τ v : Pt m) (x : Fin (M + 1) → Pt m) :
    IsAdmissible M s (τ + v) (fun i => x i + v) ↔ IsAdmissible M s τ x := by
  simp only [IsAdmissible, add_left_inj, add_sub_add_right_eq_sub, add_right_comm τ v]

/-- **Slab minima move with the noise** (Section `sec:gain`): the slab minimum of the chain
translated by a transverse `v` is the slab minimum of the untranslated chain for the noise moved by
`x ↦ x − v`. -/
theorem F_eq_F_zero_act (X : Setting m) (b : ℝ) (K : ℕ) (n : ℝ) {v : Pt m} (hv : Pt.lon v = 0)
    (ω : X.Ω) : X.F b K n v ω = X.F b K n 0 (X.act (shiftBy v) ω) := by
  let e : {x : Fin (K + 1) → Pt m // IsAdmissible K n 0 x} ≃
      {x : Fin (K + 1) → Pt m // IsAdmissible K n v x} :=
    { toFun := fun x => ⟨fun i => x.1 i + v, by
        simpa using (isAdmissible_add_iff (M := K) (s := n) 0 v x.1).2 x.2⟩
      invFun := fun y => ⟨fun i => y.1 i - v, by
        refine (isAdmissible_add_iff (M := K) (s := n) 0 v _).1 ?_
        simpa using y.2⟩
      left_inv := fun x => Subtype.ext (funext fun i => add_sub_cancel_right _ _)
      right_inv := fun y => Subtype.ext (funext fun i => sub_add_cancel _ _) }
  unfold Setting.F slabMinimum
  rw [← e.iInf_comp]
  refine iInf_congr fun x => ?_
  unfold slabSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [IsotropicVariance.Paper.Proofs.Gain.chainSlab_of_lon_eq_zero n hv]
  exact (slabTime_act_shiftBy X b n i hv ω _ _).symm

end Slabs

/-! ### Blocks and transverse translations -/

section Blocks

variable {m : ℕ}

/-- The index shift `j L e₀` (`e₀` the first unit vector of `ℤ^m`) of the translation by
`j L W e₂`. -/
def blockShift (hm : 1 ≤ m) (j L : ℕ) : Fin m → ℤ :=
  ((j * L : ℕ) : ℤ) • Pi.single ⟨0, hm⟩ 1

/-- The entries of the index shift. -/
theorem blockShift_apply_real (hm : 1 ≤ m) (j L : ℕ) (k : Fin m) :
    ((blockShift hm j L k : ℤ) : ℝ) = if (k : ℕ) = 0 then (j : ℝ) * L else 0 := by
  by_cases hk : (k : ℕ) = 0
  · have hk' : k = ⟨0, hm⟩ := Fin.ext hk
    subst hk'
    simp [blockShift]
  · have hk' : k ≠ ⟨0, hm⟩ := fun h => hk (by simp [h])
    simp [blockShift, hk, hk']

/-- The entries of the index shift are multiples of `L`. -/
theorem dvd_blockShift (hm : 1 ≤ m) (j L : ℕ) (k : Fin m) : (L : ℤ) ∣ blockShift hm j L k := by
  simp only [blockShift, Pi.smul_apply, smul_eq_mul]
  exact Dvd.dvd.mul_right (by exact_mod_cast dvd_mul_left L j) _

/-- Adding a vector of multiples of `L` preserves the block indices of every offset. -/
theorem isBlockIndex_add_iff {L : ℕ} {o : Fin m → Fin L} {z d : Fin m → ℤ}
    (hd : ∀ k, (L : ℤ) ∣ d k) : IsBlockIndex L o (z + d) ↔ IsBlockIndex L o z := by
  refine forall_congr' fun k => ?_
  rw [Pi.add_apply, add_sub_right_comm]
  exact dvd_add_left (hd k)

/-- **The reindexing `z ↦ z + j L e₀` preserves the block indices** of every offset. -/
theorem isBlockIndex_add_blockShift_iff (hm : 1 ≤ m) (j L : ℕ) (o : Fin m → Fin L)
    (z : Fin m → ℤ) : IsBlockIndex L o (z + blockShift hm j L) ↔ IsBlockIndex L o z :=
  isBlockIndex_add_iff (dvd_blockShift hm j L)

/-- The reindexing `z ↦ z + j L e₀` of the blocks of a slab with offset `o`. -/
def blockIndexShift (hm : 1 ≤ m) (j L : ℕ) (o : Fin m → Fin L) :
    {z : Fin m → ℤ | IsBlockIndex L o z} ≃ {z : Fin m → ℤ | IsBlockIndex L o z} :=
  (Equiv.addRight (blockShift hm j L)).subtypeEquiv fun z =>
    (isBlockIndex_add_blockShift_iff hm j L o z).symm

/-- The translation vector `j L W e₂` is transverse. -/
@[simp] theorem lon_smul_e₂ (c : ℝ) : Pt.lon (c • e₂ m) = 0 := by
  simp

/-- A point is in the image of a set under `shiftBy v` iff its translate by `v` is in the set. -/
theorem mem_image_shiftBy {v x : Pt m} {S : Set (Pt m)} : x ∈ shiftBy v '' S ↔ x + v ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [shiftBy_apply] using hy
  · intro h
    exact ⟨x + v, h, by simp [shiftBy_apply]⟩

/-- **The translation by `j L W e₂` moves the blocks**: `x ↦ x − j L W e₂` maps the block
`(i, z)` onto the block `(i, z − j L e₀)`. -/
theorem image_shiftBy_block (hm : 1 ≤ m) (n W : ℝ) (L i j : ℕ) (z : Fin m → ℤ) :
    shiftBy (((j : ℝ) * L * W) • e₂ m) '' block n W L i z =
      block n W L i (z - blockShift hm j L) := by
  ext x
  simp only [mem_image_shiftBy, block, mem_ofPred_eq, Pt.lon_add, lon_smul_e₂, add_zero,
    Pt.tr_add_apply, Pt.tr_smul_apply, tr_e₂, Pi.sub_apply, Int.cast_sub, blockShift_apply_real]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun k => ?_))
  split_ifs <;> constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The translation `x ↦ x − j L W e₂` maps the block `(i, z + j L e₀)` onto the block `(i, z)`.
-/
theorem image_shiftBy_block_add (hm : 1 ≤ m) (n W : ℝ) (L i j : ℕ) (z : Fin m → ℤ) :
    shiftBy (((j : ℝ) * L * W) • e₂ m) '' block n W L i (z + blockShift hm j L) =
      block n W L i z := by
  rw [image_shiftBy_block hm, add_sub_cancel_right]

/-- The corners of the blocks `(i, z)` and `(i, z + j L e₀)` differ by `j L W e₂`. -/
theorem blockCorner_sub_blockCorner_add (hm : 1 ≤ m) (n W : ℝ) (L i j : ℕ) (z : Fin m → ℤ) :
    blockCorner n W i z - blockCorner n W i (z + blockShift hm j L) =
      -(((j : ℝ) * L * W) • e₂ m) := by
  refine Pt.ext_coord ?_ fun k => ?_
  · simp [blockCorner]
  · simp only [blockCorner, Pt.tr_sub_apply, Pt.tr_mk, Pt.tr_neg_apply, Pt.tr_smul_apply, tr_e₂,
      PiLp.toLp_apply, Pi.add_apply, Int.cast_add, blockShift_apply_real]
    split_ifs <;> ring

end Blocks

/-! ### Transport of couplings and resamplings by rigid motions -/

section Transport

variable {m : ℕ} (X : Setting m)

/-- Moving the noise by a proper rigid motion `g` after `f` pulls the information of `g '' S`
back to the information of `S` pulled back by `f`. -/
theorem comap_info_act_comp {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g)
    (S : Set (Pt m)) {Ω' : Type*} (f : Ω' → X.Ω) :
    (X.info (g '' S)).comap (fun ω => X.act g (f ω)) = (X.info S).comap f := by
  rw [show (fun ω => X.act g (f ω)) = X.act g ∘ f from rfl, ← MeasurableSpace.comap_comp,
    X.comap_info_act g hg S]

/-- The preimage under the action of `g` of an event of the noise in `g '' S` is an event of the
noise in `S`. -/
theorem measurableSet_info_preimage_act {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g)
    {S : Set (Pt m)} {A : Set X.Ω} (hA : MeasurableSet[X.info (g '' S)] A) :
    MeasurableSet[X.info S] (X.act g ⁻¹' A) := by
  rw [← X.comap_info_act g hg S]
  exact ⟨A, hA, rfl⟩

variable {X}

/-- **Block couplings move with the noise**: moving the old and new noise of a coupling of `G`
by a proper rigid motion `g` gives a coupling of `g '' G`. -/
theorem isBlockCoupling_act {G G' : Set (Pt m)} {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {old new : Ω' → X.Ω} (h : X.IsBlockCoupling G P' old new)
    {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g) (hG : g '' G = G') :
    X.IsBlockCoupling G' P' (fun ω => X.act g (old ω)) (fun ω => X.act g (new ω)) := by
  subst hG
  have hc : g '' Gᶜ = (g '' G)ᶜ := image_compl_eq g.bijective
  have hact := X.measurePreserving_act g hg
  refine ⟨hact.comp h.measurePreserving_old, hact.comp h.measurePreserving_new, ?_, ?_, ?_⟩
  · have hpm : Measurable (Prod.map (X.act g) (X.act g)) :=
      hact.measurable.prodMap hact.measurable
    have hon : Measurable fun ω => (old ω, new ω) :=
      h.measurePreserving_old.measurable.prodMk h.measurePreserving_new.measurable
    have hno : Measurable fun ω => (new ω, old ω) :=
      h.measurePreserving_new.measurable.prodMk h.measurePreserving_old.measurable
    calc P'.map (fun ω => (X.act g (old ω), X.act g (new ω)))
        = (P'.map fun ω => (old ω, new ω)).map (Prod.map (X.act g) (X.act g)) :=
          (Measure.map_map hpm hon).symm
      _ = (P'.map fun ω => (new ω, old ω)).map (Prod.map (X.act g) (X.act g)) := by
          rw [h.exchangeable]
      _ = P'.map (fun ω => (X.act g (new ω), X.act g (old ω))) := Measure.map_map hpm hno
  · intro A hA
    rw [← hc] at hA
    exact h.agree_compl _ (measurableSet_info_preimage_act X hg hA)
  · rw [← hc, comap_info_act_comp X hg, comap_info_act_comp X hg, comap_info_act_comp X hg]
    exact h.indep

/-- **Label resamplings move with the noise**: moving the old and new noise of a resampling of
the block `(i, z)` given its label by a proper rigid motion `g` mapping the block onto the block
`(i', z')` and moving the label of `(i, z)` to the label of `(i', z')` almost surely gives a
resampling of `(i', z')` given its label. -/
theorem isLabelResampling_act {Λ : X.LabelFamily} {n W : ℝ} {L i i' : ℕ} {z z' : Fin m → ℤ}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {old new : Ω' → X.Ω}
    (h : X.IsLabelResampling Λ n W L i z P' old new) {g : Pt m ≃ᵃⁱ[ℝ] Pt m}
    (hg : IsProperRigidMotion g) (hG : g '' block n W L i z = block n W L i' z')
    (hlab : ∀ᵐ ω ∂X.P, Λ.label i' z' (X.act g ω) = Λ.label i z ω) :
    X.IsLabelResampling Λ n W L i' z' P' (fun ω => X.act g (old ω))
      (fun ω => X.act g (new ω)) := by
  have hold : ∀ᵐ ω ∂P', Λ.label i' z' (X.act g (old ω)) = Λ.label i z (old ω) :=
    h.isBlockCoupling.measurePreserving_old.quasiMeasurePreserving.ae hlab
  have hnew : ∀ᵐ ω ∂P', Λ.label i' z' (X.act g (new ω)) = Λ.label i z (new ω) :=
    h.isBlockCoupling.measurePreserving_new.quasiMeasurePreserving.ae hlab
  refine ⟨isBlockCoupling_act h.isBlockCoupling hg hG, ?_, ?_⟩
  · filter_upwards [h.label_eq, hold, hnew] with ω hω h1 h2
    rw [h1, h2]
    exact hω
  · intro A B hA hB v
    rw [← hG] at hA hB
    have h' := h.condIndep _ _ (measurableSet_info_preimage_act X hg hA)
      (measurableSet_info_preimage_act X hg hB) v
    -- the moved label and the label agree almost surely, so the four events change by null sets
    have key : ∀ q : Ω' → Prop, P' {ω | q ω ∧ Λ.label i' z' (X.act g (old ω)) = v} =
        P' {ω | q ω ∧ Λ.label i z (old ω) = v} := fun q =>
      measure_congr (Filter.eventuallyEqSet_iff.2 (hold.mono fun ω hω => by
        simp only [mem_ofPred_eq, hω]))
    have e1 := key fun ω => X.act g (old ω) ∈ A ∧ X.act g (new ω) ∈ B
    have e2 := key fun _ => True
    have e3 := key fun ω => X.act g (old ω) ∈ A
    have e4 := key fun ω => X.act g (old ω) ∈ B
    simp only [and_assoc, true_and] at e1 e2
    rw [e1, e2, e3, e4]
    exact h'

/-- **Transport of a label resampling** by a proper rigid motion `g` mapping the block `(i, z)`
onto the block `(i', z')` and moving the label of `(i, z)` to the label of `(i', z')` almost
surely: the
resampling of `(i', z')` on the same probability space whose old and new noise are those of
`rs` moved by `g`. -/
noncomputable def LabelResamplingData.transport {Λ : X.LabelFamily} {n W : ℝ} {L i : ℕ}
    {z : Fin m → ℤ} (rs : X.LabelResamplingData Λ n W L i z) (g : Pt m ≃ᵃⁱ[ℝ] Pt m)
    (hg : IsProperRigidMotion g) {i' : ℕ} {z' : Fin m → ℤ}
    (hG : g '' block n W L i z = block n W L i' z')
    (hlab : ∀ᵐ ω ∂X.P, Λ.label i' z' (X.act g ω) = Λ.label i z ω) :
    X.LabelResamplingData Λ n W L i' z' where
  Ω' := rs.Ω'
  P' := rs.P'
  old ω := X.act g (rs.old ω)
  new ω := X.act g (rs.new ω)
  isLabelResampling := isLabelResampling_act rs.isLabelResampling hg hG hlab

/-- **Covariant labels move with the noise**: moving the noise by the translation
`x ↦ x − j L W e₂` moves the label of the block `(i, z + j L e₀)` to the label of the block
`(i, z)`, almost surely. -/
theorem label_act_shiftBy {Λ : X.LabelFamily} {n W : ℝ} {L : ℕ} (hΛ : IsCovariantAE Λ n W L)
    (hm : 1 ≤ m) (i j : ℕ) (z : Fin m → ℤ) :
    ∀ᵐ ω ∂X.P, Λ.label i z (X.act (shiftBy (((j : ℝ) * L * W) • e₂ m)) ω) =
      Λ.label i (z + blockShift hm j L) ω := by
  have h := hΛ i (z + blockShift hm j L) z fun k => by
    simpa using dvd_blockShift hm j L k
  rw [blockCorner_sub_blockCorner_add hm n W L i j z] at h
  exact h

end Transport

/-! ### Energies of translated functions -/

section Energies

variable {m : ℕ} (X : Setting.{u} m)

/-- The resamplings given the labels of the blocks `(i, z)` obtained by moving the resamplings of
the blocks `(i, z + j L e₀)` by the translation `x ↦ x − j L W e₂`, for covariant labels. -/
noncomputable def shiftResamplings {Λ : X.LabelFamily} {n W : ℝ} {L : ℕ}
    (hΛ : IsCovariantAE Λ n W L)
    (hm : 1 ≤ m) (j : ℕ) (rcpl : (i : ℕ) → (z : Fin m → ℤ) → X.LabelResamplingData Λ n W L i z)
    (i : ℕ) (z : Fin m → ℤ) : X.LabelResamplingData Λ n W L i z :=
  LabelResamplingData.transport (rcpl i (z + blockShift hm j L))
    (shiftBy (((j : ℝ) * L * W) • e₂ m)) (isProperRigidMotion_shiftBy _)
    (image_shiftBy_block_add hm n W L i j z) (label_act_shiftBy hΛ hm i j z)

/-- **The label energy of a translated function** (Section `sec:gain`): for covariant labels, the
energy `½ Σ_G E (Z^{G, X_G} − Z)²` of `Z ∘ act (x ↦ x − j L W e₂)` for a family of resamplings
given the labels is that of `Z` for the family moved by the translation. -/
theorem labelCouplingEnergy_comp_act_shiftBy (hm : 1 ≤ m) {n W : ℝ} (L K j : ℕ)
    {Λ : X.LabelFamily} (hΛ : IsCovariantAE Λ n W L) (o : Fin K → Fin m → Fin L)
    (rcpl : (i : ℕ) → (z : Fin m → ℤ) → X.LabelResamplingData Λ n W L i z) (Z : X.Ω → ℝ) :
    labelCouplingEnergy X n W L K Λ o rcpl
        (fun ω => Z (X.act (shiftBy (((j : ℝ) * L * W) • e₂ m)) ω)) =
      labelCouplingEnergy X n W L K Λ o (shiftResamplings X hΛ hm j rcpl) Z := by
  unfold labelCouplingEnergy
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ((blockIndexShift hm j L (o i)).tsum_eq fun z => ∫⁻ ω, ENNReal.ofReal
    ((Z (X.act (shiftBy (((j : ℝ) * L * W) • e₂ m)) ((rcpl i z).new ω)) -
      Z (X.act (shiftBy (((j : ℝ) * L * W) • e₂ m)) ((rcpl i z).old ω))) ^ 2) ∂(rcpl i z).P').symm

/-- The translated slab minimum `F_j` of Section `sec:gain` is `F_0` of the noise moved by
`x ↦ x − j L W e₂`. -/
theorem F_shift_eq (b : ℝ) (K : ℕ) (n W : ℝ) (L j : ℕ) :
    X.F b K n (((j : ℝ) * L * W) • e₂ m) =
      fun ω => X.F b K n 0 (X.act (shiftBy (((j : ℝ) * L * W) • e₂ m)) ω) :=
  funext fun ω => F_eq_F_zero_act X b K n (lon_smul_e₂ _) ω

/-- For covariant labels, the label energy of the translated slab minimum `F_j` for a family of
resamplings given the labels is that of `F_0` for the family moved by the translation
`x ↦ x − j L W e₂`. -/
theorem labelCouplingEnergy_F_shift (hm : 1 ≤ m) (b : ℝ) {n W : ℝ} (L K j : ℕ)
    {Λ : X.LabelFamily} (hΛ : IsCovariantAE Λ n W L) (o : Fin K → Fin m → Fin L)
    (rcpl : (i : ℕ) → (z : Fin m → ℤ) → X.LabelResamplingData Λ n W L i z) :
    labelCouplingEnergy X n W L K Λ o rcpl (X.F b K n (((j : ℝ) * L * W) • e₂ m)) =
      labelCouplingEnergy X n W L K Λ o (shiftResamplings X hΛ hm j rcpl) (X.F b K n 0) := by
  rw [F_shift_eq, labelCouplingEnergy_comp_act_shiftBy X hm]

end Energies

end IsotropicVariance.Paper.Proofs.Gain
