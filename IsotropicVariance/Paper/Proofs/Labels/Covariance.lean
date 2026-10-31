/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Labels.Construction
public import IsotropicVariance.Paper.Proofs.Gain.LabelCovariance
public import IsotropicVariance.Paper.Contracts.Gain

/-!
# The labels of Lemma `lem:labels` are given by one rule, translated

The translation clause of Lemma `lem:labels`, and Step 3 of its proof: `X_{G+τ}(u+τ, v+τ)`, computed
with `ω` translated by `τ`, equals `X_G(u, v)`. The passage time `T_G` moves pathwise with the noise
(`setTime_act`, from `Setting.covariant`). The labels read versions of it, equal to it almost
surely, so the rule holds almost surely (`tgFamily_isCovariantAE`), as `Proofs.Gain.IsCovariantAE`
states: the versions of two blocks agree after moving the noise (`ae_version_act_closure_block`), so
do the values of `Ψ_G` (`ae_psiCode_act`), and replacing the values of small probability reads only
the probabilities of the values of `Ψ_G`, which are then the same in the two blocks
(`Proofs.Gain.ae_fiberRule_comp_eq`). The proof holds for any two blocks; `IsCovariantAE` is the
instance the paper states.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace IsotropicVariance.Paper.Proofs.Labels

open IsotropicVariance.Paper IsotropicVariance.Paper.Proofs.Gain

variable {m : ℕ} (X : Setting.{u} m)

/-- **`T_P` moves with the noise**, for every outcome: `T_{g P}(act g ω; g x, g y) = T_P(ω; x, y)`,
for a proper rigid motion `g`. -/
theorem setTime_act (b : ℝ) {g : Pt m ≃ᵃⁱ[ℝ] Pt m} (hg : IsProperRigidMotion g) (P : Set (Pt m))
    (ω : X.Ω) (x y : Pt m) :
    X.setTime b (g '' P) (X.act g ω) (g x) (g y) = X.setTime b P ω x y := by
  have hdens : setDensity b (X.ρ ω) P = setDensity b (X.ρ (X.act g ω)) (g '' P) ∘ g := by
    funext x
    have hfr : frontier (g '' P) = g '' frontier P := (g.toHomeomorph.image_frontier P).symm
    have hinf : infEDist (g x) (g '' frontier P) = infEDist x (frontier P) :=
      infEDist_image g.isometry
    have hiff : g x ∈ cthickening 1 (frontier (g '' P)) ↔ x ∈ cthickening 1 (frontier P) := by
      rw [mem_cthickening_iff, mem_cthickening_iff, hfr, hinf]
    by_cases hx : x ∈ cthickening 1 (frontier P)
    · simp only [setDensity, Function.comp_apply, ite_eq_left hx, ite_eq_left (hiff.2 hx)]
    · simp only [setDensity, Function.comp_apply, ite_eq_right hx,
        ite_eq_right (fun h => hx (hiff.1 h)), X.covariant g hg ω x]
  unfold Setting.setTime
  rw [hdens, restrictedPassageTime_comp_affineIsometryEquiv]

/-- The translation between the corners maps the closure of the block `(i, z)` onto the closure of
the block `(i', z')`. -/
theorem image_blockTranslation_closure_block (n W : ℝ) (L : ℕ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ)
    (z' : Fin m → ℤ) :
    blockTranslation n W i z i' z' '' closure (block n W L i z) =
      closure (block n W L i' z') := by
  rw [← image_constVAdd_block n W L i z i' z']
  exact (blockTranslation n W i z i' z').toHomeomorph.image_closure _

/-- **Versions of `T_G` move with the noise between blocks**: if `V` and `V'` agree almost surely
with the passage times of the closures of two blocks, then almost surely
`V'(act g ω)(g u, g v) = V(ω)(u, v)` for all `u, v` in the closure of the first block. -/
theorem ae_version_act_closure_block (b n W : ℝ) (L : ℕ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ)
    (z' : Fin m → ℤ) {V V' : X.Ω → Pt m × Pt m → ℝ}
    (hV : ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n W L i z), ∀ v ∈ closure (block n W L i z),
      V ω (u, v) = X.setTime b (closure (block n W L i z)) ω u v)
    (hV' : ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n W L i' z'), ∀ v ∈ closure (block n W L i' z'),
      V' ω (u, v) = X.setTime b (closure (block n W L i' z')) ω u v) :
    ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n W L i z), ∀ v ∈ closure (block n W L i z),
      V' (X.act (blockTranslation n W i z i' z') ω)
          (blockTranslation n W i z i' z' u, blockTranslation n W i z i' z' v) = V ω (u, v) := by
  set g := blockTranslation n W i z i' z'
  have hg : IsProperRigidMotion g := isProperRigidMotion_blockTranslation n W i z i' z'
  have hV'g := (X.measurePreserving_act g hg).quasiMeasurePreserving.ae hV'
  have himg := image_blockTranslation_closure_block n W L i z i' z'
  filter_upwards [hV, hV'g] with ω hω hω' u hu v hv
  have hgu : g u ∈ closure (block n W L i' z') := himg ▸ mem_image_of_mem g hu
  have hgv : g v ∈ closure (block n W L i' z') := himg ▸ mem_image_of_mem g hv
  rw [hω' _ hgu _ hgv, hω u hu v hv, ← himg]
  exact setTime_act X b hg _ ω u v

/-- The two points of a pair of indices of the block `(i', z')` are the translates of those of the
block `(i, z)`. -/
theorem pairPts_blockTranslation (n W : ℝ) (L : ℕ) (κ : ℝ) (i : ℕ) (z : Fin m → ℤ) (i' : ℕ)
    (z' : Fin m → ℤ) (pq : GridPair m L κ) :
    pairPts n W L κ i' z' pq =
      (blockTranslation n W i z i' z' (pairPts n W L κ i z pq).1,
        blockTranslation n W i z i' z' (pairPts n W L κ i z pq).2) := by
  simp only [pairPts, blockTranslation_apply]
  refine Prod.ext ?_ ?_ <;> simp only <;> abel

/-- The two points of a pair of indices lie in the closure of the block. -/
theorem pairPts_mem {n W κ : ℝ} (hn : 0 ≤ n) (hW : 0 < W) (hκ : 0 < κ) {L : ℕ} (hL : 1 ≤ L)
    (i : ℕ) (z : Fin m → ℤ) (pq : GridPair m L κ) :
    (pairPts n W L κ i z pq).1 ∈ closure (block n W L i z) ∧
      (pairPts n W L κ i z pq).2 ∈ closure (block n W L i z) :=
  ⟨subset_closure (corner_add_gridRel_mem_block hW hκ hL le_rfl hn i z pq.1),
    subset_closure (corner_add_gridRel_mem_block hW hκ hL hn le_rfl i z pq.2)⟩

/-- **`Ψ_G` moves with the noise between blocks.** -/
theorem ae_psiCode_act {b : ℝ} {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W : ℝ}
    (hn : 0 ≤ n) (hW : 0 < W) (Q : ℝ) {L : ℕ} (hL : 1 ≤ L) {κ : ℝ} (hκ : 0 < κ) (M : ℝ) (i : ℕ)
    (z : Fin m → ℤ) (i' : ℕ) (z' : Fin m → ℤ)
    (hV : ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n W L i z), ∀ v ∈ closure (block n W L i z),
      V i z ω (u, v) = X.setTime b (closure (block n W L i z)) ω u v)
    (hV' : ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n W L i' z'), ∀ v ∈ closure (block n W L i' z'),
      V i' z' ω (u, v) = X.setTime b (closure (block n W L i' z')) ω u v) :
    (fun ω => psiCode X V n W Q L κ M i' z' (X.act (blockTranslation n W i z i' z') ω)) =ᵐ[X.P]
      psiCode X V n W Q L κ M i z := by
  filter_upwards [ae_version_act_closure_block X b n W L i z i' z' hV hV'] with ω hω
  funext pq
  obtain ⟨h1, h2⟩ := pairPts_mem hn hW hκ hL i z pq
  simp only [psiCode]
  rw [pairPts_blockTranslation n W L κ i z i' z' pq, hω _ h1 _ h2]

/-- **The labels of Lemma `lem:labels` are given by one rule, translated, almost surely.** -/
theorem tgFamily_isCovariantAE {b : ℝ} {V : ℕ → (Fin m → ℤ) → X.Ω → Pt m × Pt m → ℝ} {n W : ℝ}
    (hn : 0 ≤ n) (hW : 0 < W) (Q : ℝ) {L : ℕ} (hL : 1 ≤ L) {κ : ℝ} (hκ : 0 < κ) (M θ : ℝ)
    (hVm : ∀ i z, Measurable[X.info (block n W L i z)] (V i z))
    (hV : ∀ i z, ∀ᵐ ω ∂X.P, ∀ u ∈ closure (block n W L i z), ∀ v ∈ closure (block n W L i z),
      V i z ω (u, v) = X.setTime b (closure (block n W L i z)) ω u v) :
    IsCovariantAE (tgFamily X V n W Q L κ M θ) n W L := by
  refine isCovariantAE_of_blockTranslation _ n W L fun i i' z z' => ?_
  have hT := X.measurePreserving_act _ (isProperRigidMotion_blockTranslation n W i z i' z')
  have hcode := ae_psiCode_act X hn hW Q hL hκ M i z i' z' (hV i z) (hV i' z')
  have hlab := ae_fiberRule_comp_eq hT
    (fun c => (X.info_le _) _ (measurableSet_psiCode_preimage X (hVm i' z') c)) hcode
    (fun (F : GridCode m L κ M → ℝ≥0∞) (v : GridCode m L κ M) =>
      if F v < ENNReal.ofReal θ then
        (Finset.univ.exists_max_image F Finset.univ_nonempty).choose else v)
  filter_upwards [hlab] with ω hω
  exact hω

end IsotropicVariance.Paper.Proofs.Labels
