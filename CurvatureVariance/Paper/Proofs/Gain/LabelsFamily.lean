/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.LabelsBlock
public import CurvatureVariance.Paper.Proofs.Gain.FALabel
import CurvatureVariance.Paper.Proofs.Moments.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The family of labels `X_G` of Lemma `lem:labels`

The end of Step 2 and Step 3 of the proof of [AB26, Lemma 6.2], as the proof of Lemma `lem:labels`
changes Step 2 and applies Step 3 in the coordinates of the block.

* `labelVec`: the values of `Ψ` at the mesh of a block, in the coordinates of the block: a function
  of the pair of mesh indices. So `labelVec` of `G + z` at the weights `(τ_{e−z})_e` is `labelVec` of
  `G` at `(τ_e)_e` (`labelVec_translate`), at every `ω`, and the law of `labelVec` does not depend on
  the block: `labelVec_eq_ref` writes it at the reference block `g = 0`, translated.
* `labelValue`: a code, read as a function on all pairs of vertices: the value of the code at the
  mesh indices on `Γ_G`, extended by `0` off `Γ_G`. It moves with the block
  (`labelValue_add_blockShift`), since `Γ_{G+z} = Γ_G + z`.
* `exists_isLabelFamily`: Step 3. The rule of the clipping, the rounding and the merging
  (`exists_finiteLabel`, `Ψ_G` and then `X_G`) is chosen **once per slab and offset**, at the
  reference block: the value `ψ*` of largest probability is that of the reference block. The label
  of every block is this rule applied to `labelVec` of the block, so every value of every label has
  probability at least `α_L`, not "`0` or at least `α_L`", and the translation property holds at
  every `ω` and on all pairs. The merge is `Gain.exists_merge`, the rule of
  `IsotropicVariance.Paper.Proofs.Labels.mergeRare` in the continuum library: the values of
  probability below `α_L` go to a value of largest probability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Infra.FPP

variable {m : ℕ}

/-! ### The values of `Ψ` at the mesh -/

/-- The values `Ψ(u_g, v_g)` at the mesh of the block `(i, o, g)`, indexed by the pairs of mesh
indices. -/
noncomputable def labelVec (M : Model m) (K : ℕ) (A : ℝ) (L n : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (P : Pt m) (τ : ℝ) (i : ℕ) (o g : Fin m → ℤ) (ω : Config m) (s : meshPairs m L τ) : ℝ :=
  labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω
    (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n) s.1.1)
    (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n) s.1.2)

theorem measurable_labelVec (M : Model m) (hP : IsProbabilityMeasure M.P) (K : ℕ) (A : ℝ)
    (L n : ℕ) (t : EuclideanSpace ℝ (Fin m)) (P : Pt m) (τ : ℝ) (i : ℕ) (o g : Fin m → ℤ) :
    Measurable (labelVec M K A L n t P τ i o g) :=
  measurable_pi_iff.mpr fun _ => measurable_labelPsi M K A n P i _ _ _ hP

/-- `labelVec` is determined by the weights of the block. -/
theorem labelVec_congr (M : Model m) (K : ℕ) (A : ℝ) (L n : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (P : Pt m) (τ : ℝ) (i : ℕ) (o g : Fin m → ℤ) {ω ω' : Config m}
    (h : ∀ e : Edge m, e.1 ∈ block n (wInt M K A n) L t i o g → ω e = ω' e) :
    labelVec M K A L n t P τ i o g ω = labelVec M K A L n t P τ i o g ω' := by
  funext s
  simp only [labelVec, labelPsi_congr M K A n P i _ h]

/-- **The translation property of `labelVec`, at every `ω`.** -/
theorem labelVec_translate {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {L n : ℕ}
    (hw : 0 < wInt M K A n) (t : EuclideanSpace ℝ (Fin m)) (P : Pt m) (τ : ℝ) (i : ℕ)
    (o g m' : Fin m → ℤ) (ω : Config m) :
    labelVec M K A L n t P τ i o (g + m') (translate (-blockShift (wInt M K A n) L m') ω) =
      labelVec M K A L n t P τ i o g ω := by
  funext s
  simp only [labelVec, blockRep_add]
  exact labelPsi_translate hM K A n P i (blockShift_fst _ _ _)
    (fun e => map_add_blockShift_mem_block_iff hw t i o g m' e) ω _ _

/-- `labelVec` of a block is `labelVec` of the reference block at the translated weights. -/
theorem labelVec_eq_ref {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {L n : ℕ}
    (hw : 0 < wInt M K A n) (t : EuclideanSpace ℝ (Fin m)) (P : Pt m) (τ : ℝ) (i : ℕ)
    (o g : Fin m → ℤ) (ω : Config m) :
    labelVec M K A L n t P τ i o g ω =
      labelVec M K A L n t P τ i o 0 (translate (blockShift (wInt M K A n) L g) ω) := by
  have h := labelVec_translate (L := L) hM hw t P τ i o 0 g
    (translate (blockShift (wInt M K A n) L g) ω)
  rwa [zero_add, translate_translate, neg_add_cancel, translate_zero] at h

/-! ### Codes as functions on pairs of vertices -/

open Classical in
/-- The value of a code at an index, `0` if the index is not in the finite set. -/
noncomputable def codeAt {ι : Type*} (S : Finset ι) (a : S → ℤ) (p : ι) : ℤ :=
  if h : p ∈ S then a ⟨p, h⟩ else 0

open Classical in
/-- A code read as a function on pairs of vertices: `ξ` times its value at the mesh indices of
`(u, v)` on `Γ_G`, and `0` off `Γ_G`. -/
noncomputable def labelValue (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ) (o g : Fin m → ℤ)
    (τ ξ : ℝ) (a : meshPairs m L τ → ℤ) (u v : Vertex m) : ℝ :=
  if (u, v) ∈ blockFacePairs n w L t i o g then
    ξ * codeAt (meshPairs m L τ) a (meshIndex w L t o g τ u, meshIndex w L t o g τ v)
  else 0

/-- **A code moves with the block, on all pairs**: since `Γ_{G+z} = Γ_G + z` and the mesh indices do
not move, the extension by `0` has the translation property. -/
theorem labelValue_add_blockShift (n w L : ℕ) (t : EuclideanSpace ℝ (Fin m)) (i : ℕ)
    (o g m' : Fin m → ℤ) (τ ξ : ℝ) (a : meshPairs m L τ → ℤ) (u v : Vertex m) :
    labelValue n w L t i o (g + m') τ ξ a (u + blockShift w L m') (v + blockShift w L m') =
      labelValue n w L t i o g τ ξ a u v := by
  classical
  unfold labelValue
  simp only [add_blockShift_mem_blockFacePairs_iff, meshIndex_add_blockShift]

/-- **The values of a code in the alphabet are bounded.** -/
theorem abs_labelValue_le {n w L : ℕ} {t : EuclideanSpace ℝ (Fin m)} {i : ℕ} {o g : Fin m → ℤ}
    {τ ξ B : ℝ} (hB : 0 ≤ B) (hξ : 0 < ξ) {a : meshPairs m L τ → ℤ}
    (ha : a ∈ labelAlphabet (meshPairs m L τ) B ξ) (u v : Vertex m) :
    |labelValue n w L t i o g τ ξ a u v| ≤ B + ξ := by
  classical
  unfold labelValue codeAt
  split_ifs with h1 h2
  · have h := mem_labelAlphabet_bounds hξ ha ⟨_, h2⟩
    rw [abs_le]
    constructor <;> linarith only [h.1, h.2, hB, hξ]
  · simp only [Int.cast_zero, mul_zero, abs_zero]
    linarith
  · simp only [abs_zero]
    linarith

/-! ### Step 3 of the proof of [AB26, Lemma 6.2] -/

/-- **Step 3 of the proof of [AB26, Lemma 6.2]**, which the proof of Lemma `lem:labels` applies to
`Ψ_G` unchanged. Let `Λ` be the alphabet of the values of `Ψ_G`, and `α |Λ| ≤ 1`. If, in every block
of slabs `1 ≤ i ≤ K`, one variable of `L^{8d}` norm at most `ε₀` bounds
`|Φ − Ψ| + |Ψ − Ψ(u_g,v_g)| + (|Ψ(u_g,v_g)| − B)₊` on `Γ_G`, then the merged and rounded values of
`Ψ` at the mesh form a family with `Gain.IsLabelFamily` at the atom bound `α` and the error
`ε₀ + ξ + ε₅`, whenever `(2B + ξ)^{8d} |Λ| α ≤ ε₅^{8d}`.

The rule of the merging depends on the slab and the offset, not on the block: it is chosen at the
reference block `g = 0`, and transported. -/
theorem exists_isLabelFamily {M : Model m} (hM : M.Standing) {K : ℕ} {A : ℝ} {L n : ℕ}
    (hw : 0 < wInt M K A n) (t : EuclideanSpace ℝ (Fin m)) (P : Pt m) {τ B ξ α ε₀ ε₅ : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B) (hξ : 0 < ξ) (hα : 0 ≤ α)
    (hαΛ : α * (labelAlphabet (meshPairs m L τ) B ξ).card ≤ 1) (hε₀ : 0 ≤ ε₀) (hε₅ : 0 ≤ ε₅)
    (hmerge : (2 * B + ξ) ^ (8 * (m + 1)) *
      ((labelAlphabet (meshPairs m L τ) B ξ).card * α) ≤ ε₅ ^ (8 * (m + 1)))
    (hblock : ∀ i : ℕ, 1 ≤ i → i ≤ K → ∀ o g : Fin m → ℤ, (∀ k, 0 ≤ o k ∧ o k < L) →
      ∃ Y : Config m → ℝ, eLpNorm Y (8 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal ε₀ ∧
        ∀ᵐ ω ∂M.P, ∀ u ∈ subcubeFace (wInt M K A n) L t o g (((i : ℤ) - 1) * n),
          ∀ v ∈ subcubeFace (wInt M K A n) L t o g ((i : ℤ) * n),
          |normSlabTime M K A ω n P i u v -
              labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω u v| +
            |labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω u v -
              labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω
                (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n)
                  (meshIndex (wInt M K A n) L t o g τ u))
                (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n)
                  (meshIndex (wInt M K A n) L t o g τ v))| +
            max (|labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω
                (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n)
                  (meshIndex (wInt M K A n) L t o g τ u))
                (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n)
                  (meshIndex (wInt M K A n) L t o g τ v))| - B) 0 ≤ Y ω) :
    ∃ lam : ℕ → (Fin m → ℤ) → (Fin m → ℤ) → Config m → Vertex m → Vertex m → ℝ,
      Gain.IsLabelFamily M K A L n t P α (ε₀ + ξ + ε₅) lam := by
  classical
  have := hM.probP
  have hmp : ∀ g : Fin m → ℤ,
      MeasurePreserving (translate (blockShift (wInt M K A n) L g)) M.P M.P := fun g =>
    Moments.standing_measurePreserving_translate hM _
  have hVm : ∀ i o, Measurable (labelVec M K A L n t P τ i o 0) := fun i o =>
    measurable_labelVec M hM.probP K A L n t P τ i o 0
  have hVeq : ∀ i o g ω, labelVec M K A L n t P τ i o g ω =
      labelVec M K A L n t P τ i o 0 (translate (blockShift (wInt M K A n) L g) ω) :=
    fun i o g ω => labelVec_eq_ref hM hw t P τ i o g ω
  have hVtr : ∀ i o g m' ω,
      labelVec M K A L n t P τ i o (g + m') (translate (-blockShift (wInt M K A n) L m') ω) =
        labelVec M K A L n t P τ i o g ω := fun i o g m' ω =>
    labelVec_translate hM hw t P τ i o g m' ω
  have hVdep : ∀ i o g ω ω', (∀ e : Edge m, e.1 ∈ block n (wInt M K A n) L t i o g → ω e = ω' e) →
      labelVec M K A L n t P τ i o g ω = labelVec M K A L n t P τ i o g ω' := fun i o g _ _ h =>
    labelVec_congr M K A L n t P τ i o g h
  have hVpt : ∀ i o g ω (s : meshPairs m L τ), labelVec M K A L n t P τ i o g ω s =
      labelPsi M K A n P i (block n (wInt M K A n) L t i o g) ω
        (blockRep (wInt M K A n) L t o g τ (((i : ℤ) - 1) * n) s.1.1)
        (blockRep (wInt M K A n) L t o g τ ((i : ℤ) * n) s.1.2) := fun _ _ _ _ _ => rfl
  generalize labelVec M K A L n t P τ = V at hVm hVeq hVtr hVdep hVpt
  set w := wInt M K A n with hwdef
  set Λ := labelAlphabet (meshPairs m L τ) B ξ with hΛdef
  have hp₀ : ENNReal.ofReal α * (Λ.card : ℝ≥0∞) ≤ 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hαΛ
  -- the rule, chosen at the reference block
  have hrule := fun (i : ℕ) (o : Fin m → ℤ) => exists_finiteLabel M.P (hVm i o) hB hξ hp₀
  choose Φ hΦmem hΦmass hΦmeas Bad hBadm hBadP hΦerr using hrule
  have hmemV : ∀ i o g ω, Φ i o (V i o g ω) ∈ Λ := fun i o g ω => by
    rw [hVeq]
    exact hΦmem i o _
  refine ⟨fun i o g ω => labelValue n w L t i o g τ ξ (Φ i o (V i o g ω)), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- each label is determined by its block, finite, measurable, with the bound
    intro i hi hiK o g ho
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω ω' h
      simp only [hVdep i o g ω ω' h]
    · refine Set.Finite.subset (Λ.finite_toSet.image (labelValue n w L t i o g τ ξ)) ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨Φ i o (V i o g ω), hmemV i o g ω, rfl⟩
    · intro ω
      have hS : MeasurableSet {ω' | Φ i o (V i o 0 ω') ∈
          labelValue n w L t i o g τ ξ ⁻¹'
            {labelValue n w L t i o g τ ξ (Φ i o (V i o g ω))}} := hΦmeas i o _
      have hS' := (hmp g).measurable hS
      refine MeasurableSet.congr hS' ?_
      ext ω'
      simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, ← hVeq]
    · obtain ⟨Y, hY, hYae⟩ := hblock i hi hiK o g ho
      set θ := translate (m := m) (blockShift w L g) with hθ
      let Mg : Config m → ℝ := fun ω => (2 * B + ξ) * (Bad i o).indicator 1 (θ ω)
      have hMgm : Measurable Mg :=
        ((measurable_const.indicator (hBadm i o)).comp (hmp g).measurable).const_mul _
      have hk : 1 ≤ 8 * (m + 1) := by omega
      have hbξ : 0 ≤ 2 * B + ξ := by positivity
      have hMgn : eLpNorm Mg (8 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal ε₅ := by
        refine eLpNorm_le_ofReal_of_lintegral_le hMgm.aestronglyMeasurable hk hε₅ ?_
        have heq : (fun ω => ENNReal.ofReal (|Mg ω| ^ (8 * (m + 1)))) =
            (θ ⁻¹' Bad i o).indicator (fun _ => ENNReal.ofReal ((2 * B + ξ) ^ (8 * (m + 1)))) := by
          funext ω
          by_cases hω : θ ω ∈ Bad i o
          · have hω' : ω ∈ θ ⁻¹' Bad i o := hω
            rw [indicator_of_mem hω']
            simp only [Mg]
            rw [indicator_of_mem hω, Pi.one_apply, mul_one, abs_of_nonneg hbξ]
          · have hω' : ω ∉ θ ⁻¹' Bad i o := hω
            rw [indicator_of_notMem hω']
            simp only [Mg]
            rw [indicator_of_notMem hω, mul_zero, abs_zero, zero_pow (by omega), ENNReal.ofReal_zero]
        have hmeas : MeasurableSet (θ ⁻¹' Bad i o) := (hmp g).measurable (hBadm i o)
        rw [heq, lintegral_indicator_const hmeas,
          (hmp g).measure_preimage (hBadm i o).nullMeasurableSet]
        calc ENNReal.ofReal ((2 * B + ξ) ^ (8 * (m + 1))) * M.P (Bad i o)
            ≤ ENNReal.ofReal ((2 * B + ξ) ^ (8 * (m + 1))) *
                ((Λ.card : ℝ≥0∞) * ENNReal.ofReal α) := by
              gcongr
              exact hBadP i o
          _ = ENNReal.ofReal ((2 * B + ξ) ^ (8 * (m + 1)) * ((Λ.card : ℝ) * α)) := by
              rw [ENNReal.ofReal_mul (pow_nonneg hbξ _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
                ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal (ε₅ ^ (8 * (m + 1))) := ENNReal.ofReal_le_ofReal hmerge
      have h1 := eLpNorm_add_le_ofReal hk hε₀ hξ.le hY (eLpNorm_const_le_ofReal (P := M.P) hξ.le hk)
      have h2 := eLpNorm_add_le_ofReal hk (by positivity) hε₅ h1 hMgn
      refine ⟨fun ω => Y ω + ξ + Mg ω, h2, ?_⟩
      filter_upwards [hYae] with ω hω u hu v hv
      have ha := meshIndex_mem_meshBox (τ := τ) hw hτ hu
      have hb := meshIndex_mem_meshBox (τ := τ) hw hτ hv
      have hab : (meshIndex w L t o g τ u, meshIndex w L t o g τ v) ∈ meshPairs m L τ :=
        Finset.mem_product.mpr ⟨ha, hb⟩
      have hval : labelValue n w L t i o g τ ξ (Φ i o (V i o g ω)) u v =
          ξ * Φ i o (V i o g ω) ⟨_, hab⟩ := by
        unfold labelValue codeAt
        rw [ite_eq_left (show (u, v) ∈ blockFacePairs n w L t i o g from ⟨hu, hv⟩),
          dite_eq_left hab]
      have herr := hΦerr i o (θ ω) ⟨_, hab⟩
      rw [← hVeq] at herr
      have hbound := hω u hu v hv
      have hclip := abs_sub_clipAt_le hB (V i o g ω ⟨_, hab⟩)
      rw [hVpt] at herr hclip
      change |normSlabTime M K A ω n P i u v -
          labelValue n w L t i o g τ ξ (Φ i o (V i o g ω)) u v| ≤
        Y ω + ξ + (2 * B + ξ) * (Bad i o).indicator 1 (θ ω)
      rw [hval]
      set N := normSlabTime M K A ω n P i u v
      set Ψ₀ := labelPsi M K A n P i (block n w L t i o g) ω u v
      set x := labelPsi M K A n P i (block n w L t i o g) ω
        (blockRep w L t o g τ (((i : ℤ) - 1) * n) (meshIndex w L t o g τ u))
        (blockRep w L t o g τ ((i : ℤ) * n) (meshIndex w L t o g τ v))
      set a : ℝ := ξ * (Φ i o (V i o g ω) ⟨_, hab⟩ : ℝ)
      have t1 := abs_sub_le N Ψ₀ a
      have t2 := abs_sub_le Ψ₀ x a
      have t3 := abs_sub_le x (clipAt B x) a
      linarith only [t1, t2, t3, herr, hbound, hclip]
  · -- every value has probability at least `α`
    intro i _ _ o g _ ω
    have hS := hΦmeas i o {Φ i o (V i o 0 (translate (blockShift w L g) ω))}
    have h1 := hΦmass i o (translate (blockShift w L g) ω)
    have hS' : MeasurableSet {ω' | Φ i o (V i o 0 ω') =
        Φ i o (V i o 0 (translate (blockShift w L g) ω))} := hS
    rw [← (hmp g).measure_preimage hS'.nullMeasurableSet] at h1
    refine h1.trans (measure_mono fun ω' hω' => ?_)
    have hω'' : Φ i o (V i o 0 (translate (blockShift w L g) ω')) =
        Φ i o (V i o 0 (translate (blockShift w L g) ω)) := hω'
    change labelValue n w L t i o g τ ξ (Φ i o (V i o g ω')) =
      labelValue n w L t i o g τ ξ (Φ i o (V i o g ω))
    rw [hVeq i o g ω', hVeq i o g ω, hω'']
  · -- the values are bounded functions on `Γ_G`
    intro i _ _ o g _
    exact ⟨B + ξ, fun ω p _ => abs_labelValue_le hB hξ (hmemV i o g ω) _ _⟩
  · -- the translation property, at every `ω` and on all pairs
    intro i _ _ o g _ m' ω u v
    change labelValue n w L t i o (g + m') τ ξ
        (Φ i o (V i o (g + m') (translate (-blockShift w L m') ω)))
        (u + blockShift w L m') (v + blockShift w L m') =
      labelValue n w L t i o g τ ξ (Φ i o (V i o g ω)) u v
    rw [hVtr, labelValue_add_blockShift]

end CurvatureVariance.Paper.Gain
