/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Moments
public import CurvatureVariance.Paper.Proofs.Mean.MeanCentered
public import CurvatureVariance.Paper.Proofs.Mean.MeanInterpolation
public import CurvatureVariance.Paper.Proofs.Mean.MeanMoments
public import CurvatureVariance.Paper.Proofs.Mean.MeanPairs
public import CurvatureVariance.Paper.Proofs.Mean.MeanRowGeometry
public import CurvatureVariance.Paper.Proofs.Mean.MeanUpper
import CurvatureVariance.Infra.FPP.TimeConstant
import CurvatureVariance.Paper.Proofs.Geometry.SupportSubgradient
import CurvatureVariance.Paper.Proofs.Mean.Classical
import CurvatureVariance.Paper.Proofs.Mean.MeanMesh
import CurvatureVariance.Paper.Proofs.Mean.MeanWidth
import CurvatureVariance.Paper.Proofs.Moments.Scales
import CurvatureVariance.Paper.Proofs.Responses.Finiteness
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The fluctuations in the proof of Lemma `lem:smallmean`

The proof of Lemma `lem:smallmean` bounds the fluctuations as [AB26] does,
with equations `eq:parent`, `eq:profiledifference` and `eq:modulus` in place of [AB26, (4.4)],
[AB26, (2.2)] and [AB26, (5.2)]. That bound is the second paragraph of the proof of
[AB26, Lemma 7.1], whose Lean is
`IsotropicVariance.Paper.Proofs.SmallMean.lintegral_fluct_pow_le_of_pair` and
`IsotropicVariance.Paper.Proofs.SmallMean.lintegral_fluct_pow_le`. Its steps, in the order of the
Lean:

* `exists_smallMean_high`: `E[D^{8d}] ≤ C` at one pair of points, from equation `eq:parent`
  (in place of [AB26, (4.4)]). The bound is at one pair, not over the cubes.
* `eLpNorm_centered_le_of_evariance_div`: `E[D²]` from the hypothesis on `Var[T/Q_s]`.
* `exists_smallMean_pair`, the mesh: at each mesh point Hölder's inequality interpolates between the
  two moments (`E[D^{4d}] ≤ C E[D²]^c`, as in the second paragraph of the proof of
  [AB26, Lemma 7.1]), the mesh of spacing `h(sQ_s)^{1/2}` costs its number of points, and equation
  `eq:modulus`, at this pair with its own slope and subgradient, extends the bound to the
  cubes: subtracting `ζ_{t'}·(v − u)` from `T(u,v)` and from its mean changes nothing (the proof of
  Lemma `lem:smallmean`).
* `exists_smallMean_slab_pair`: equation `eq:profiledifference` passes to `T^{(i)}`.
* `exists_smallMean_rows`: the cube pairs of consecutive rows (as in the paper, slopes within
  `s^{δ/100−1/4}/4` of `t`, and `4^{δ/100−1/4} + 1/4 < 1`), so that the differences of their points
  are `(s,y)` with `y ∈ 𝒟(s)`.

The steps follow the model, with one reading. [AB26] applies its modulus to the slab time, and
centres at `E[T^{(i)}]`. The paper's equation `eq:modulus` is for `T`, and its `Z_i` is centred at
`E[T(u,v)]`, so here the mesh and the modulus are for `T`, and equation `eq:profiledifference` is
applied at the end, uniformly on the cubes, rather than at each mesh point.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Mean

open CurvatureVariance.Paper CurvatureVariance.Paper.Contracts CurvatureVariance.Infra.FPP

/-- A bound on `Var[X/Q]`, the form of the hypothesis of Lemma `lem:smallmean`, bounds the second
moment of `X − E[X]`. -/
theorem eLpNorm_centered_le_of_evariance_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) {B Q : ℝ} (hB : 0 ≤ B) (hQ : 0 < Q)
    (hv : evariance (fun ω => X ω / Q) P ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm (fun ω => X ω - ∫ ω', X ω' ∂P) 2 P ≤ ENNReal.ofReal (B * Q) := by
  apply eLpNorm_centered_le_of_evariance hX (mul_nonneg hB hQ.le)
  have he : evariance X P = evariance (fun ω => Q * (X ω / Q)) P := by
    congr 1
    funext ω
    field_simp
  rw [he, evariance_mul]
  calc ENNReal.ofReal (Q ^ 2) * evariance (fun ω => X ω / Q) P
      ≤ ENNReal.ofReal (Q ^ 2) * ENNReal.ofReal (B ^ 2) := by gcongr
    _ = ENNReal.ofReal ((B * Q) ^ 2) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      ring

/-- **The `8d`-th moment at one pair** (equation `eq:parent` in place of [AB26, (4.4)], in the proof
of Lemma `lem:smallmean`; `E[D^{8d}] ≤ C` in the second paragraph of the proof of
[AB26, Lemma 7.1]): for `y ∈ 𝒟(s)`, `‖T(0,(s,y)) − E T‖_{8d} ≤ Br Q_s`. -/
theorem exists_smallMean_high {m : ℕ} (hparent : ParentStatement m) (bd : Bounds m)
    (hbd : bd.Valid) (Cstar : ℝ) :
    ∃ Br : ℝ, 0 < Br ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
      ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
      Premise M K A N → RangeA M K A N Cstar →
      ∀ s : ℕ, (N : ℝ) / 8 ≤ s → (s : ℝ) ≤ N / 4 → ∀ y ∈ premiseDomain M s,
        eLpNorm (fun ω => passageTimeReal ω 0 ((s : ℤ), y) -
            ∫ ω', passageTimeReal ω' 0 ((s : ℤ), y) ∂M.P)
          ((8 * (m + 1) : ℕ) : ℝ≥0∞) M.P ≤ ENNReal.ofReal (Br * Q M K A s) := by
  obtain ⟨C, hC, hp⟩ := hparent bd hbd Cstar
  let p : ℝ := ((8 * (m + 1) : ℕ) : ℝ)
  let D : ℝ := (2 * (1 + ((Nat.ceil p).factorial : ℝ))) ^ (1 / p)
  have hp1 : 1 ≤ p := by
    dsimp only [p]
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) m]
  have hD : 0 < D := Real.rpow_pos_of_pos (by positivity) _
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  let θ₀ : ℝ := 1 / 100 + C / Real.log 2
  have hθ₀ : 0 < θ₀ := by positivity
  refine ⟨2 * D * θ₀, by positivity, fun K hK => ?_⟩
  obtain ⟨N₀, hp⟩ := hp (1 / 8) (by norm_num) K hK
  refine ⟨max N₀ 8, ?_⟩
  intro M hM hfit N hN A hA hPrem hRange s hs₁ hs₂ y hy
  have : IsProbabilityMeasure M.P := hM.probP
  have : IsProbabilityMeasure M.F := hM.probF
  obtain ⟨a, ha, hexp⟩ := hM.assumptionW.1
  have hFi := IsIIDWeights.integrable_passageTime hM.iid (integrable_coe_of_exp ha hexp)
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast ((le_max_right _ _).trans hN)
  have hspos : (0 : ℝ) < s := by linarith only [hN8, hs₁]
  have hQ : 0 < Q M K A s := mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hspos _)
  have hpow := Real.rpow_nonneg hspos.le ((3 : ℝ) / 4 + M.δ / 100)
  have hP := hp M hM hfit N ((le_max_left _ _).trans hN) A hA hPrem hRange s
    (by linarith only [hs₁]) (by linarith only [hs₂, hN8]) y
    (hy.trans (by linarith only [hpow]))
  set T : Config m → ℝ := fun ω => passageTimeReal ω 0 ((s : ℤ), y) with hT
  set μ₀ : ℝ := M.μ.1 (point ((s : ℤ), y))
  have hX := isOs_add_const (P := M.P) (by positivity : 0 < Q M K A s / 100) (mul_pos hC hQ) hP
  have hX' : CurvatureVariance.IsOs M.P 1 (θ₀ * Q M K A s) (fun ω => |T ω - μ₀|) := by
    have he : Q M K A s / 100 + C * Q M K A s / Real.log 2 = θ₀ * Q M K A s := by
      dsimp only [θ₀]
      ring
    rw [he] at hX
    simpa only [sub_add_cancel] using hX
  obtain ⟨Y, _, hY0, hY, hYn⟩ := exists_centered_majorant_of_isOs (fun _ : Unit => T)
    (fun _ => μ₀) univ (fun _ => hFi _ _) hX' (mul_pos hθ₀ hQ) hp1
    (Eventually.of_forall fun ω _ _ => le_rfl)
  have hpcast : ENNReal.ofReal p = ((8 * (m + 1) : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
  rw [hpcast] at hYn
  have hle : eLpNorm (fun ω => T ω - ∫ ω', T ω' ∂M.P) ((8 * (m + 1) : ℕ) : ℝ≥0∞) M.P ≤
      eLpNorm Y ((8 * (m + 1) : ℕ) : ℝ≥0∞) M.P := by
    apply eLpNorm_mono_ae (((hFi _ _).aestronglyMeasurable).sub aestronglyMeasurable_const)
    filter_upwards [hY] with ω hω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hY0 ω)]
    exact hω () (mem_univ _)
  refine hle.trans (hYn.trans (le_of_eq ?_))
  congr 1
  dsimp only [D]
  ring

/-- **The fluctuation of `T` on a pair of cubes** (the second paragraph of the proof of
[AB26, Lemma 7.1], whose Lean is
`IsotropicVariance.Paper.Proofs.SmallMean.lintegral_fluct_pow_le_of_pair`): for every `σ > 0`, if
`Var[T/Q_s]` is small on `𝒟(s)` and `N` is large, then `sup_{I×I'} |T(u,v) − E T(u,v)|` has `L^{4d}`
norm at most `σ Q_s`, for a pair of cubes of slope `|t − t₀| ≤ s^{δ/100−1/4}`, with `t` and the
subgradient `P` those of the pair (the proof of Lemma `lem:smallmean`).

The constants as in the paper: `h` from the modulus, then the mesh, then the variance tolerance,
all before `K`, and then `N`. -/
theorem exists_smallMean_pair {m : ℕ} (hparent : ParentStatement m)
    (hmodulus : ModulusStatement m) (bd : Bounds m) (hbd : bd.Valid)
    (Cstar b : ℝ) (hb : 1 ≤ b) {σ : ℝ} (hσ : 0 < σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
      ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
      Premise M K A N → RangeA M K A N Cstar →
      ∀ s : ℕ, (N : ℝ) / 8 ≤ s → (s : ℝ) ≤ N / 4 →
      ∀ (t : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
      IsCubePair M K A s b t I I' → ‖t - M.t₀‖ ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
      ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P →
      (∀ u ∈ I, ∀ v ∈ I', (v - u).2 ∈ premiseDomain M s) →
      (∀ y ∈ premiseDomain M s,
        evariance (fun ω => passageTimeReal ω 0 ((s : ℤ), y) / Q M K A s) M.P ≤
          ENNReal.ofReal c) →
      ∃ Y : Config m → ℝ, AEMeasurable Y M.P ∧ (∀ ω, 0 ≤ Y ω) ∧
        (∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I',
          |passageTimeReal ω u v - ∫ ω', passageTimeReal ω' u v ∂M.P| ≤ Y ω) ∧
        eLpNorm Y ((4 * (m + 1) : ℕ) : ℝ≥0∞) M.P ≤ ENNReal.ofReal (σ * Q M K A s) := by
  classical
  obtain ⟨Br, hBr, hhigh⟩ := exists_smallMean_high hparent bd hbd Cstar
  let η := σ / 8
  have hη : 0 < η := by positivity
  obtain ⟨h, hh, hmod⟩ := hmodulus bd hbd Cstar b hb η hη
  let H : ℝ := (4 * ((m : ℝ) + 1) * (((m : ℝ) + 1) * b / h + 1)) ^ (m + 1)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let σ' : ℝ := σ / (2 * (H ^ 2 + 1))
  have hσ' : 0 < σ' := by positivity
  have hHσ : H ^ 2 * σ' ≤ σ / 2 := by
    have he : σ' * (2 * (H ^ 2 + 1)) = σ := by dsimp only [σ']; field_simp
    nlinarith only [he, hσ'.le]
  let δ₂ := interpDelta m Br σ'
  have hδ₂ : 0 < δ₂ := interpDelta_pos m hBr hσ'
  refine ⟨δ₂ ^ 2, by positivity, fun K hK => ?_⟩
  obtain ⟨Nh, hhigh⟩ := hhigh K hK
  obtain ⟨Nm, hmod⟩ := hmod K hK (1 / 8) (by norm_num) (by norm_num)
  refine ⟨max (max Nh Nm) 8, ?_⟩
  intro M hM hfit N hN A hA hPrem hRange s hs₁ hs₂ t I I' hpair ht P hP hdom hvar
  have : IsProbabilityMeasure M.P := hM.probP
  have : IsProbabilityMeasure M.F := hM.probF
  obtain ⟨aF, haF, hexp⟩ := hM.assumptionW.1
  have hFi := IsIIDWeights.integrable_passageTime hM.iid (integrable_coe_of_exp haF hexp)
  have hNh : Nh ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNm : Nm ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN8 : (8 : ℝ) ≤ N := by exact_mod_cast ((le_max_right _ _).trans hN)
  have hspos : (0 : ℝ) < s := by linarith only [hN8, hs₁]
  have hQ : 0 < Q M K A s := mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hspos _)
  have hW : 0 < W M K A s := Real.sqrt_pos.mpr (mul_pos hspos hQ)
  have hsN : s ≤ N := by exact_mod_cast (show (s : ℝ) ≤ N by linarith only [hs₂, hN8])
  obtain ⟨Z, hZn, hZ⟩ := hmod M hM hfit N hNm A hA hPrem hRange s (by linarith only [hs₁]) hsN
    t I I' hpair ht P hP
  have hZm : AEMeasurable Z M.P :=
    (aestronglyMeasurable_of_eLpNorm_ne_top
      (hZn.trans_lt ENNReal.ofReal_lt_top).ne).aemeasurable
  have hp48 : ((4 * (m + 1) : ℕ) : ℝ≥0∞) ≤ ((8 * (m + 1) : ℕ) : ℝ≥0∞) := by norm_cast; omega
  have hZ4 := (eLpNorm_le_eLpNorm_of_exponent_le hp48).trans hZn
  obtain ⟨p, z, z', a, a', rfl, rfl, ha, hab, ha', ha'b, _⟩ := hpair
  let U := (finite_transverseCube p z a).toFinset
  let V := (finite_transverseCube (p + s) z' a').toFinset
  let ρ := h * W M K A s
  let R := ((m : ℝ) + 1) * b * W M K A s
  have hρ : 0 < ρ := mul_pos hh hW
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hrad (u : Vertex m) (hu : u ∈ U) :
      ‖point u - WithLp.toLp 2 ((p : ℝ), z)‖ ≤ R := by
    have hh := norm_cube_point_sub_center_le ha
      (by simpa only [U, Finset.mem_coe, Set.Finite.mem_toFinset] using hu)
    exact hh.trans (by
      simpa only [R, mul_assoc] using mul_le_mul_of_nonneg_left hab
        (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1))
  have hrad' (v : Vertex m) (hv : v ∈ V) :
      ‖point v - WithLp.toLp 2 (((p + s : ℤ) : ℝ), z')‖ ≤ R := by
    have hh := norm_cube_point_sub_center_le ha'
      (by simpa only [V, Finset.mem_coe, Set.Finite.mem_toFinset] using hv)
    exact hh.trans (by
      simpa only [R, mul_assoc] using mul_le_mul_of_nonneg_left ha'b
        (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1))
  obtain ⟨G, hGU, hGcard, hGcover⟩ := exists_mesh U _ hρ hR hrad
  obtain ⟨G', hGV, hG'card, hG'cover⟩ := exists_mesh V _ hρ hR hrad'
  have hratio : R / ρ = ((m : ℝ) + 1) * b / h := by dsimp only [R, ρ]; field_simp
  rw [hratio] at hGcard hG'card
  let sel : Vertex m → Vertex m := fun u => if hu : u ∈ U then (hGcover u hu).choose else 0
  let sel' : Vertex m → Vertex m := fun v => if hv : v ∈ V then (hG'cover v hv).choose else 0
  have hsel (u : Vertex m) (hu : u ∈ U) :
      sel u ∈ G ∧ ‖point u - point (sel u)‖ ≤ ρ := by
    dsimp only [sel]
    rw [dite_eq_left hu]
    exact (hGcover u hu).choose_spec
  have hsel' (v : Vertex m) (hv : v ∈ V) :
      sel' v ∈ G' ∧ ‖point v - point (sel' v)‖ ≤ ρ := by
    dsimp only [sel']
    rw [dite_eq_left hv]
    exact (hG'cover v hv).choose_spec
  let F : (Vertex m × Vertex m) → Config m → ℝ := fun uv ω => passageTimeReal ω uv.1 uv.2
  let profile : (Vertex m × Vertex m) → ℝ := fun uv => inner ℝ P (point uv.2 - point uv.1)
  let pick : (Vertex m × Vertex m) → (Vertex m × Vertex m) := fun uv => (sel uv.1, sel' uv.2)
  -- at each mesh point, Hölder's inequality between the second and the `8d`-th moment
  have hmesh : ∀ uv ∈ G ×ˢ G', eLpNorm (fun ω => F uv ω - ∫ ω', F uv ω' ∂M.P)
      ((4 * (m + 1) : ℕ) : ℝ≥0∞) M.P ≤ ENNReal.ofReal (σ' * Q M K A s) := by
    intro uv huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    have huI : uv.1 ∈ transverseCube p z a := by
      simpa only [U, Finset.mem_coe, Set.Finite.mem_toFinset] using hGU hu
    have hvI : uv.2 ∈ transverseCube (p + s) z' a' := by
      simpa only [V, Finset.mem_coe, Set.Finite.mem_toFinset] using hGV hv
    have he : uv.2 - uv.1 = ((s : ℤ), (uv.2 - uv.1).2) := by
      apply Prod.ext
      · change uv.2.1 - uv.1.1 = s
        rw [huI.1, hvI.1]
        ring
      · rfl
    have hy := hdom uv.1 huI uv.2 hvI
    rw [eLpNorm_passageTime_centered_eq hM uv.1 uv.2 _, he]
    exact eLpNorm_meanMoment_le_of_two_of_double
      (((measurable_passageTime_real 0 _).sub_const _).aestronglyMeasurable) hQ hBr hσ'
      (eLpNorm_centered_le_of_evariance_div (measurable_passageTime_real 0 _).aemeasurable
        hδ₂.le hQ (hvar _ hy))
      (hhigh M hM hfit N hNh A hA hPrem hRange s hs₁ hs₂ _ hy)
  -- equation `eq:modulus`, at this pair with its slope and its subgradient
  have hmod' : ∀ᵐ ω ∂M.P, ∀ uv ∈ (U : Set _) ×ˢ (V : Set _),
      |(F uv ω - profile uv) - (F (pick uv) ω - profile (pick uv))| ≤ Z ω := by
    filter_upwards [hZ] with ω hω
    intro uv huv
    have huI : uv.1 ∈ transverseCube p z a := by
      simpa only [U, Finset.mem_coe, Set.Finite.mem_toFinset] using huv.1
    have hvI : uv.2 ∈ transverseCube (p + s) z' a' := by
      simpa only [V, Finset.mem_coe, Set.Finite.mem_toFinset] using huv.2
    have hsI : sel uv.1 ∈ transverseCube p z a := by
      simpa only [U, Finset.mem_coe, Set.Finite.mem_toFinset] using hGU (hsel uv.1 huv.1).1
    have hsI' : sel' uv.2 ∈ transverseCube (p + s) z' a' := by
      simpa only [V, Finset.mem_coe, Set.Finite.mem_toFinset] using hGV (hsel' uv.2 huv.2).1
    have hh := hω uv.1 huI (sel uv.1) hsI uv.2 hvI (sel' uv.2) hsI'
      (hsel uv.1 huv.1).2 (hsel' uv.2 huv.2).2
    dsimp only [F, profile, pick]
    rw [inner_add_right, inner_sub_right, inner_sub_right] at hh
    convert hh using 1
    congr 1
    simp only [inner_sub_right]
    ring
  have hp4 : (2 : ℝ≥0∞) ≤ ((4 * (m + 1) : ℕ) : ℝ≥0∞) := by norm_cast; omega
  obtain ⟨Y₂, hY₂m, hY₂0, hY₂, hY₂n⟩ := exists_centered_majorant_of_mesh hp4
    F profile (fun uv => measurable_passageTime_real uv.1 uv.2) (fun uv => hFi uv.1 uv.2)
    ((U : Set _) ×ˢ (V : Set _)) (G ×ˢ G') pick
    (fun uv huv => Finset.mem_product.mpr ⟨(hsel uv.1 huv.1).1, (hsel' uv.2 huv.2).1⟩)
    Z hZm hmod' (mul_nonneg hσ'.le hQ.le) (mul_nonneg hη.le hQ.le) hmesh hZ4
  have hcount : ((G ×ˢ G').card : ℝ) * σ' ≤ σ / 2 := by
    have hcc : ((G ×ˢ G').card : ℝ) ≤ H ^ 2 := by
      rw [Finset.card_product, Nat.cast_mul, pow_two]
      exact mul_le_mul hGcard hG'card (Nat.cast_nonneg _) hH
    exact (mul_le_mul_of_nonneg_right hcc hσ'.le).trans hHσ
  refine ⟨Y₂, hY₂m, hY₂0, ?_, hY₂n.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · filter_upwards [hY₂] with ω hω
    intro u hu v hv
    apply hω (u, v)
    exact ⟨by simpa only [U, Finset.mem_coe, Set.Finite.mem_toFinset] using hu,
      by simpa only [V, Finset.mem_coe, Set.Finite.mem_toFinset] using hv⟩
  · have hh' := mul_le_mul_of_nonneg_right hcount hQ.le
    dsimp only [η]
    nlinarith only [hh', mul_pos hσ hQ]

/-- **The fluctuation of `T^{(i)}` on a pair of cubes**: equation `eq:profiledifference`, in place
of [AB26, (2.2)] (the proof of Lemma `lem:smallmean`), transfers
`exists_smallMean_pair` to the slab time, with the centre `E T(u,v)` of the paper's `Z_i`. The
threshold depends on `K`, and the variance tolerance is chosen before `K`. -/
theorem exists_smallMean_slab_pair {m : ℕ} (hparent : ParentStatement m)
    (hmodulus : ModulusStatement m) (hdifference : ProfileDifferenceStatement m)
    (bd : Bounds m) (hbd : bd.Valid) (Cstar b : ℝ) (hb : 1 ≤ b) {σ : ℝ} (hσ : 0 < σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
      ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
      Premise M K A N → RangeA M K A N Cstar →
      ∀ s : ℕ, (N : ℝ) / 8 ≤ s → (s : ℝ) ≤ N / 4 →
      ∀ (t : EuclideanSpace ℝ (Fin m)) (I I' : Set (Vertex m)),
      IsCubePair M K A s b t I I' → ‖t - M.t₀‖ ≤ (s : ℝ) ^ (M.δ / 100 - 1 / 4) →
      ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P →
      (∀ u ∈ I, ∀ v ∈ I', (v - u).2 ∈ premiseDomain M s) →
      (∀ y ∈ premiseDomain M s,
        evariance (fun ω => passageTimeReal ω 0 ((s : ℤ), y) / Q M K A s) M.P ≤
          ENNReal.ofReal c) →
      ∃ Y : Config m → ℝ, AEMeasurable Y M.P ∧ (∀ ω, 0 ≤ Y ω) ∧
        (∀ᵐ ω ∂M.P, ∀ u ∈ I, ∀ v ∈ I',
          |slabTimeReal ω u.1 v.1 u v - ∫ ω', passageTimeReal ω' u v ∂M.P| ≤ Y ω) ∧
        eLpNorm Y ((4 * (m + 1) : ℕ) : ℝ≥0∞) M.P ≤ ENNReal.ofReal (σ * Q M K A s) := by
  obtain ⟨c, hc, hprofile⟩ := exists_smallMean_pair hparent hmodulus bd hbd Cstar b hb
    (show 0 < σ / 2 by positivity)
  obtain ⟨C, hC, hdifference⟩ := hdifference bd hbd Cstar
  have hdifference := hdifference b hb
  let p : ℕ := 4 * (m + 1)
  let D : ℝ := (2 * (1 + ((Nat.ceil (p : ℝ)).factorial : ℝ))) ^ (1 / (p : ℝ)) * C
  have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos (by positivity) _) hC
  obtain ⟨slog, _, hlogsmall⟩ := log_sq_le_mul_Q bd hbd (16 * C + D) (σ / 2) (by positivity)
  refine ⟨c, hc, fun K hK => ?_⟩
  obtain ⟨Np, hprofile⟩ := hprofile K hK
  obtain ⟨Nd, hdifference⟩ := hdifference K hK
  refine ⟨max (max Np Nd) (max 64 ⌈8 * max slog (Real.exp 1)⌉₊), ?_⟩
  intro M hM hfit N hN A hA hprem hrange s hs₁ hs₂ t I I' hpair ht P hP hdom hvar
  have : IsProbabilityMeasure M.P := hM.probP
  have hNp : Np ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNd : Nd ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN64 : (64 : ℝ) ≤ N := by
    exact_mod_cast (((le_max_left _ _).trans (le_max_right _ _)).trans hN : 64 ≤ N)
  have hNlarge : 8 * max slog (Real.exp 1) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast
      (((le_max_right _ _).trans (le_max_right _ _)).trans hN :
        ⌈8 * max slog (Real.exp 1)⌉₊ ≤ N))
  have hslarge : max slog (Real.exp 1) ≤ (s : ℝ) := by linarith only [hNlarge, hs₁]
  have hslog : slog ≤ (s : ℝ) := (le_max_left _ _).trans hslarge
  have hsexp : Real.exp 1 ≤ (s : ℝ) := (le_max_right _ _).trans hslarge
  have hs8 : (8 : ℝ) ≤ s := by linarith only [hN64, hs₁]
  have hspos : (0 : ℝ) < s := by linarith only [hs8]
  have hs2 : 2 ≤ s := by exact_mod_cast (show (2 : ℝ) ≤ s by linarith only [hs8])
  have hQ : 0 < Q M K A s := mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hspos _)
  have hsqrt : Real.sqrt (N : ℝ) ≤ s := by
    apply Real.sqrt_le_iff.2
    refine ⟨hspos.le, ?_⟩
    have hh := mul_le_mul_of_nonneg_right hs8 hspos.le
    nlinarith only [hs₁, hh]
  have hs2N : (s : ℝ) ≤ 2 * N := by linarith only [hs₂, hN64]
  have ht' : ‖t - M.t₀‖ ≤ 3 / 2 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) := ht.trans
    (le_mul_of_one_le_left (Real.rpow_nonneg hspos.le _) (by norm_num))
  obtain ⟨Yt, hYtm, hYt0, hYt, hYtn⟩ := hprofile M hM hfit N hNp A hA hprem hrange s hs₁ hs₂
    t I I' hpair ht P hP hdom hvar
  obtain ⟨X, hX, hcomparison⟩ := hdifference M hM hfit N hNd A hA hrange s hsqrt hs2N t I I'
    hpair ht'
  have hp0 : (0 : ℝ) < p := by dsimp [p]; positivity
  have hp1 : (1 : ℝ≥0∞) ≤ p := by norm_cast; dsimp [p]; omega
  have hXm : AEMeasurable (fun ω => max (X ω) 0) M.P := hX.1.max aemeasurable_const
  have hXnorm : eLpNorm (fun ω => max (X ω) 0) (p : ℝ≥0∞) M.P ≤ ENNReal.ofReal D := by
    simpa only [ENNReal.ofReal_natCast] using eLpNorm_pos_le_of_isOs hX hC hp0
  let a : ℝ := C * Real.log (N : ℝ) ^ 2
  have ha : 0 ≤ a := mul_nonneg hC.le (sq_nonneg _)
  have hloga : a + D ≤ σ / 2 * Q M K A s := by
    have hNpos : (0 : ℝ) < N := by linarith only [hN64]
    have hlogs1 : 1 ≤ Real.log (s : ℝ) := by
      have hh := Real.log_le_log (Real.exp_pos 1) hsexp
      simpa only [Real.log_exp] using hh
    have hlogs0 : 0 ≤ Real.log (s : ℝ) := zero_le_one.trans hlogs1
    have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith only [hN64])
    have hlogN : Real.log (N : ℝ) ≤ 4 * Real.log (s : ℝ) := by
      have hN8s : (N : ℝ) ≤ 8 * s := by linarith only [hs₁]
      have hlog2 : Real.log 2 ≤ Real.log (s : ℝ) :=
        Real.log_le_log two_pos (by linarith only [hs8])
      calc Real.log (N : ℝ) ≤ Real.log (8 * (s : ℝ)) := Real.log_le_log hNpos hN8s
        _ = 3 * Real.log 2 + Real.log s := by
            rw [Real.log_mul (by norm_num) hspos.ne', show (8 : ℝ) = 2 ^ 3 by norm_num,
              Real.log_pow]
            norm_num
        _ ≤ 4 * Real.log s := by linarith only [hlog2]
    have hlogsq : Real.log (N : ℝ) ^ 2 ≤ 16 * Real.log (s : ℝ) ^ 2 := by
      have hh := (sq_le_sq₀ hlogN0 (by positivity : 0 ≤ 4 * Real.log (s : ℝ))).2 hlogN
      nlinarith only [hh]
    have hlogs1sq : 1 ≤ Real.log (s : ℝ) ^ 2 := one_le_pow₀ hlogs1
    have hh₁ := mul_le_mul_of_nonneg_left hlogsq hC.le
    have hh₂ := mul_le_mul_of_nonneg_left hlogs1sq hD.le
    have hsmall := hlogsmall M hM hfit s hslog K hK A hA
    dsimp only [a]
    nlinarith only [hh₁, hh₂, hsmall]
  have hanorm : eLpNorm (fun _ : Config m => a) (p : ℝ≥0∞) M.P = ENNReal.ofReal a := by
    rw [eLpNorm_const _ (by exact_mod_cast (show p ≠ 0 by dsimp [p]; omega))
      (IsProbabilityMeasure.ne_zero M.P)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg ha]
  let Y : Config m → ℝ := fun ω => Yt ω + (a + max (X ω) 0)
  refine ⟨Y, hYtm.add (aemeasurable_const.add hXm),
    fun ω => add_nonneg (hYt0 ω) (add_nonneg ha (le_max_right _ _)), ?_, ?_⟩
  · obtain ⟨q, z, z', d, d', rfl, rfl, _, _, _, _, _⟩ := hpair
    filter_upwards [hYt, hcomparison] with ω hωt hωd
    intro u hu v hv
    have hu₁ : u.1 = q := hu.1
    have hv₁ : v.1 = q + s := hv.1
    have hfinite : slabTime ω u.1 v.1 u v ≠ ⊤ :=
      CurvatureVariance.Paper.Responses.slabTime_ne_top ω
        (by rw [hu.1, hv.1]; omega : u.1 + 2 ≤ v.1)
        (by constructor <;> omega : u.1 ≤ u.1 ∧ u.1 ≤ v.1)
        (by constructor <;> omega : u.1 ≤ v.1 ∧ v.1 ≤ v.1)
    have hcomp := hωd u hu v hv
    have hTD : passageTimeReal ω u v ≤ slabTimeReal ω u.1 v.1 u v := by
      simpa only [passageTimeReal, slabTimeReal, ENNReal.coe_toReal] using
        ENNReal.toReal_mono hfinite hcomp.1
    have htri := abs_sub_le (slabTimeReal ω u.1 v.1 u v) (passageTimeReal ω u v)
      (∫ ω', passageTimeReal ω' u v ∂M.P)
    rw [abs_of_nonneg (sub_nonneg.mpr hTD)] at htri
    have htbound := hωt u hu v hv
    have hmax := le_max_left (X ω) 0
    have hupper := hcomp.2
    change _ ≤ Yt ω + (a + max (X ω) 0)
    change _ ≤ a + X ω at hupper
    linarith only [htri, htbound, hupper, hmax]
  · have herror : eLpNorm (fun ω => a + max (X ω) 0) (p : ℝ≥0∞) M.P ≤
        ENNReal.ofReal (σ / 2 * Q M K A s) := by
      calc _ ≤ eLpNorm (fun _ : Config m => a) (p : ℝ≥0∞) M.P +
          eLpNorm (fun ω => max (X ω) 0) (p : ℝ≥0∞) M.P := eLpNorm_add_le hp1
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal D := add_le_add hanorm.le hXnorm
        _ = ENNReal.ofReal (a + D) := (ENNReal.ofReal_add ha hD.le).symm
        _ ≤ ENNReal.ofReal (σ / 2 * Q M K A s) := ENNReal.ofReal_le_ofReal hloga
    calc _ ≤ eLpNorm Yt (p : ℝ≥0∞) M.P +
        eLpNorm (fun ω => a + max (X ω) 0) (p : ℝ≥0∞) M.P := eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (σ / 2 * Q M K A s) + ENNReal.ofReal (σ / 2 * Q M K A s) :=
        add_le_add hYtn herror
      _ = ENNReal.ofReal (σ * Q M K A s) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- The side of the cubes against the range of `z`: for `N` large,
`(d−1)^{1/2} w ≤ s^{3/4+δ/100}/16` for `s ≥ N/8`, from the first bound of equation `eq:scales`.
The threshold depends on `Cstar` and on the bounds, not on `K`. -/
theorem exists_smallMean_width {m : ℕ} (hscales : ScalesStatement m) (bd : Bounds m)
    (hbd : bd.Valid) (Cstar : ℝ) :
    ∃ N₀ : ℕ, ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A → RangeA M K A N Cstar →
      ∀ s : ℕ, (N : ℝ) / 8 ≤ s →
        Real.sqrt m * wInt M K A s ≤ (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (zero_lt_one.trans_le hbd.law.one_le_m)
  have hroot : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  obtain ⟨N₁, hN₁⟩ := Moments.exists_width_margin hscales bd hbd Cstar
    (η := 1 / (32 * Real.sqrt m)) (by positivity)
  refine ⟨max 8 N₁, ?_⟩
  intro K hK M hM hfit N hN A hA hRange s hs
  have hN8 : 8 ≤ N := (le_max_left _ _).trans hN
  have hNR : (8 : ℝ) ≤ N := by exact_mod_cast hN8
  have hs1 : (1 : ℝ) ≤ s := by linarith only [hNR, hs]
  have hNsqrt : Real.sqrt N ≤ (N : ℝ) := by
    apply Real.sqrt_le_left (by positivity) |>.2
    have hh : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := mul_nonneg (by positivity) (by linarith only [hNR])
    nlinarith only [hh]
  have hW := hN₁ K hK M hM hfit N ((le_max_right _ _).trans hN) A hA hRange s
    (by linarith only [hNsqrt, hs, hNR])
  have hw := mean_wInt_le_two_W hM hK hA hs1
  have hstep := mul_le_mul_of_nonneg_left hw hroot.le
  have hstep' := mul_le_mul_of_nonneg_left hW (show 0 ≤ 2 * Real.sqrt m by positivity)
  have heq : 2 * Real.sqrt m * ((1 / (32 * Real.sqrt m)) *
      (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100)) =
      (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 16 := by
    field_simp
    ring
  rw [heq] at hstep'
  nlinarith only [hstep, hstep']

/-- **The fluctuations on the rows** (the proof of Lemma `lem:smallmean`):
for `θ > 0`, if `Var[T/Q_s]` is small on `𝒟(s)` and `N` is large, then for
`8w|k − j| ≤ s^{3/4+δ/100}` the supremum of `|T^{(i)}(u,v) − E T(u,v)|` over `u ∈ I_i(j)`,
`v ∈ I_{i+1}(k)` has `L^{4d}` norm at most `θ Q_s`. The pair of cubes has its own slope `t'`, and
`ζ_{t'}` is a subgradient at it. The slopes are within `s^{δ/100−1/4}/4` of `t`:
`exists_row_cube_pair` has `|t' − t| ≤ s^{δ/100−1/4}/8` for the centres, and `3 s^{δ/100−1/4}/16`
for the points, so that the condition `4^{δ/100−1/4} + 1/4 < 1` of the paper is
`mean_reference_slope_bound`, with `13/16`. -/
theorem exists_smallMean_rows {m : ℕ} (hparent : ParentStatement m)
    (hmodulus : ModulusStatement m) (hdifference : ProfileDifferenceStatement m)
    (hscales : ScalesStatement m) (bd : Bounds m) (hbd : bd.Valid) (Cstar : ℝ) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ cvar : ℝ, 0 < cvar ∧ ∀ K : ℕ, 10 ^ 4 ≤ K → ∃ N₀ : ℕ,
      ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ N : ℕ, N₀ ≤ N → ∀ A : ℝ, 1 ≤ A →
      Premise M K A N → RangeA M K A N Cstar →
      ∀ s : ℕ, (N : ℝ) / 8 ≤ s → (s : ℝ) ≤ N / 4 → ∀ y₀ : Fin m → ℤ,
      ‖transversePoint y₀ - (s : ℝ) • M.t₀‖ ≤ s * (N : ℝ) ^ (M.δ / 100 - 1 / 4) →
      (∀ y ∈ premiseDomain M s,
        evariance (fun ω => passageTimeReal ω 0 ((s : ℤ), y) / Q M K A s) M.P ≤
          ENNReal.ofReal cvar) →
      ∀ (i : Fin s) (j k : Fin m → ℤ),
      (wInt M K A s : ℝ) * ‖transversePoint (k - j)‖ ≤
        (s : ℝ) ^ ((3 : ℝ) / 4 + M.δ / 100) / 8 →
      ∃ X : Config m → ℝ, eLpNorm X ((4 * (m + 1) : ℕ) : ℝ≥0∞) M.P ≤
        ENNReal.ofReal (θ * Q M K A s) ∧
        ∀ᵐ ω ∂M.P,
          ∀ u ∈ rowCube s (wInt M K A s) ((s : ℝ)⁻¹ • transversePoint y₀) i j,
          ∀ v ∈ rowCube s (wInt M K A s) ((s : ℝ)⁻¹ • transversePoint y₀) ((i : ℤ) + 1) k,
            |slabTimeReal ω ((i : ℤ) * s) (((i : ℤ) + 1) * s) u v -
              ∫ ω', passageTimeReal ω' 0 ((s : ℤ), v.2 - u.2) ∂M.P| ≤ X ω := by
  obtain ⟨cvar, hcvar, hsmall⟩ := exists_smallMean_slab_pair hparent hmodulus hdifference
    bd hbd Cstar 2 (by norm_num) hθ
  obtain ⟨Nw, hwidth⟩ := exists_smallMean_width hscales bd hbd Cstar
  refine ⟨cvar, hcvar, fun K hK => ?_⟩
  obtain ⟨Np, hsmall⟩ := hsmall K hK
  refine ⟨max (max Np Nw) 64, ?_⟩
  intro M hM hfit N hN A hA hPrem hRange s hs₁ hs₂ y₀ hy₀ hvar i j k hjump
  have hNp : Np ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNw : Nw ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN64 : (64 : ℝ) ≤ N := by exact_mod_cast ((le_max_right _ _).trans hN)
  have hs8 : (8 : ℝ) ≤ s := by linarith only [hN64, hs₁]
  have hsR : (0 : ℝ) < s := by linarith only [hs8]
  have hs : 0 < s := by exact_mod_cast hsR
  have hs1 : (1 : ℝ) ≤ s := by linarith only [hs8]
  have hW : 0 < W M K A s := Real.sqrt_pos.mpr (mul_pos hsR
    (mul_pos (zero_lt_one.trans_le hA) (Real.rpow_pos_of_pos hsR _)))
  have hw : 0 < wInt M K A s := Nat.ceil_pos.mpr hW
  have hwW := mean_wInt_le_two_W hM hK hA hs1
  have hwsmall := hwidth K hK M hM hfit N hNw A hA hRange s hs₁
  let t := (s : ℝ)⁻¹ • transversePoint y₀
  have hst : (s : ℝ) • t = transversePoint y₀ := by
    dsimp only [t]
    rw [smul_smul, mul_inv_cancel₀ hsR.ne', one_smul]
  have htN : ‖t - M.t₀‖ ≤ (N : ℝ) ^ (M.δ / 100 - 1 / 4) := by
    rw [← hst, ← smul_sub, norm_smul, Real.norm_of_nonneg hsR.le] at hy₀
    exact (mul_le_mul_iff_of_pos_left hsR).mp hy₀
  have ht : ‖t - M.t₀‖ ≤ (13 : ℝ) / 16 * (s : ℝ) ^ (M.δ / 100 - 1 / 4) :=
    htN.trans (mean_reference_slope_bound hM.delta_le_one hsR hs₂)
  obtain ⟨τ, I, I', hcover, hcover', hpair, hτ, hdom⟩ :=
    exists_row_cube_pair M hs hw hwW hwsmall hst ht (i : ℤ) j k hjump
  obtain ⟨P, hP⟩ := Proofs.Geometry.exists_isSubgradient M.μ (slopeVec τ)
  obtain ⟨X, _, _, hX, hXn⟩ := hsmall M hM hfit N hNp A hA hPrem hRange s hs₁ hs₂ τ I I' hpair hτ
    P hP hdom hvar
  refine ⟨X, hXn, ?_⟩
  filter_upwards [hX] with ω hω
  intro u hu v hv
  have hh := hω u (hcover hu) v (hcover' hv)
  have he : v - u = ((s : ℤ), v.2 - u.2) := by
    apply Prod.ext
    · change v.1 - u.1 = s
      rw [hu.1, hv.1]
      ring
    · rfl
  rw [integral_passageTime_sub hM u v, he, hu.1, hv.1] at hh
  exact hh

end CurvatureVariance.Paper.Mean
