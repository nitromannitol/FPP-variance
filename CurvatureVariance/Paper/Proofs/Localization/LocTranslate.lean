/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.LocFrame
public import CurvatureVariance.Paper.Proofs.ShortLengths.Translate
public import CurvatureVariance.Infra.FPP.Hypotheses
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import CurvatureVariance.Paper.Proofs.Moments.Basic

/-!
# Lemma `lem:localization`: stationarity

The proof of Lemma `lem:localization`: "By stationarity, we may assume that
`|ū| ≤ d^{1/2}`." The radius of Lemma `lem:localization` is not measurable as such, and the lower
integral does not see that: the translation is a measurable bijection which preserves the law, so
`∫⁻ F ∘ θ_a = ∫⁻ F` for every `F` (`lintegral_comp_translate`).

* `deviation_le_of_shift`: a walk maps along the translation, and with it the distance to `[u, v]`;
* `isGeodesic_of_map`, `isSlabGeodesic_of_map`: geodesics pull back along the translation;
* `lintegral_locRadius_le`, `lintegral_locRadiusSlab_le`: the moments of the radii of two cubes are
  at most those of the translated cubes.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Loc

open CurvatureVariance.Paper CurvatureVariance.Infra.FPP Radius
open CurvatureVariance.Infra.Percolation (latticeShift)

variable {m : ℕ}

/-- The translation is a measurable bijection. -/
noncomputable def translateEquiv (a : Vertex m) : Config m ≃ᵐ Config m where
  toFun := translate a
  invFun := translate (-a)
  left_inv ω := by
    show translate (-a) (translate a ω) = ω
    rw [translate_translate, neg_add_cancel, translate_zero]
  right_inv ω := by
    show translate a (translate (-a) ω) = ω
    rw [translate_translate, add_neg_cancel, translate_zero]
  measurable_toFun := measurable_translate a
  measurable_invFun := measurable_translate (-a)

/-- **Stationarity for the lower integral**, with no measurability of `F`. -/
theorem lintegral_comp_translate {M : Model m} (hM : M.Standing) (a : Vertex m)
    (F : Config m → ℝ≥0∞) : ∫⁻ ω, F (translate a ω) ∂M.P = ∫⁻ ω, F ω ∂M.P :=
  (Moments.standing_measurePreserving_translate hM a).lintegral_comp_emb
    (translateEquiv a).measurableEmbedding F

/-- The distance to `[u, v]` is invariant under a translation. -/
theorem infDist_segment_add (x u v a : Vertex m) :
    Metric.infDist (point (x + a)) (segment ℝ (point (u + a)) (point (v + a))) =
      Metric.infDist (point x) (segment ℝ (point u) (point v)) := by
  simp only [point_add]
  have h := segment_translate_image ℝ (point a) (point u) (point v)
  rw [add_comm (point u), add_comm (point v), ← h, add_comm (point x)]
  exact Metric.infDist_image (IsometryEquiv.addLeft (point a)).isometry

/-- **The deviation under a translation**: if the paths of `geo` pull back to paths of `geo'` along
the translation by `a`, then the deviation of `I, I'` for `geo` is at most that of the translated
cubes for `geo'`. -/
theorem deviation_le_of_shift (a : Vertex m)
    {geo geo' : ∀ {u v : Vertex m}, (latticeGraph m).Walk u v → Prop}
    (hgeo : ∀ {u v : Vertex m} (γ : (latticeGraph m).Walk u v),
      geo (γ.map (latticeShift a).toHom) → geo' γ)
    {I I' I₀ I₀' : Set (Vertex m)} (hI : ∀ u ∈ I, u - a ∈ I₀) (hI' : ∀ v ∈ I', v - a ∈ I₀') :
    deviation geo I I' ≤ deviation geo' I₀ I₀' := by
  unfold deviation
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv =>
    iSup_le fun γ => iSup_le fun hγ => iSup_le fun x => iSup_le fun hx => ?_
  obtain ⟨u₀, rfl⟩ : ∃ u₀ : Vertex m, u = latticeShift a u₀ := ⟨u - a, by simp⟩
  obtain ⟨v₀, rfl⟩ : ∃ v₀ : Vertex m, v = latticeShift a v₀ := ⟨v - a, by simp⟩
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀ : (latticeGraph m).Walk u₀ v₀,
      γ = γ₀.map (latticeShift a).toHom := ⟨(walkShiftEquiv a u₀ v₀).symm γ,
        ((walkShiftEquiv a u₀ v₀).apply_symm_apply γ).symm⟩
  have hx' : x ∈ (γ₀.map (latticeShift a).toHom).support := hx
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hx'
  obtain ⟨x₀, hx₀, rfl⟩ := hx'
  have e := infDist_segment_add x₀ u₀ v₀ a
  have hu₀ : u₀ ∈ I₀ := by simpa using hI _ hu
  have hv₀ : v₀ ∈ I₀' := by simpa using hI' _ hv
  have hγ₀ := hgeo γ₀ hγ
  change ENNReal.ofReal (Metric.infDist (point (x₀ + a))
    (segment ℝ (point (u₀ + a)) (point (v₀ + a)))) ≤ _
  rw [e]
  exact le_iSup_of_le u₀ (le_iSup_of_le hu₀ (le_iSup_of_le v₀
    (le_iSup_of_le hv₀ (le_iSup_of_le γ₀ (le_iSup_of_le hγ₀ (le_iSup_of_le x₀
    (le_iSup_of_le hx₀ le_rfl)))))))

/-- The walk map along a translation is injective on paths. -/
theorem isPath_of_map (a : Vertex m) {u v : Vertex m} (γ : (latticeGraph m).Walk u v)
    (h : (γ.map (latticeShift a).toHom).IsPath) : γ.IsPath :=
  SimpleGraph.Walk.IsPath.of_map h

/-- A geodesic for `ω` pulls back to a geodesic for the translated configuration. -/
theorem isGeodesic_of_map (a : Vertex m) (ω : Config m) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v) (h : IsGeodesic ω (γ.map (latticeShift a).toHom)) :
    IsGeodesic (translate a ω) γ := by
  refine ⟨isPath_of_map a γ h.1, ?_⟩
  rw [← walkCost_map_latticeShift, passageTime_translate]
  exact h.2

/-- A geodesic of the slab `[p, q]` for `ω` pulls back to a geodesic of the slab
`[p − a₁, q − a₁]` for the translated configuration. -/
theorem isSlabGeodesic_of_map (a : Vertex m) (ω : Config m) (p q : ℤ) {u v : Vertex m}
    (γ : (latticeGraph m).Walk u v)
    (h : IsSlabGeodesic ω p q (γ.map (latticeShift a).toHom)) :
    IsSlabGeodesic (translate a ω) (p - a.1) (q - a.1) γ := by
  refine ⟨isPath_of_map a γ h.1, fun e he => ?_, ?_⟩
  · have h1 : Sym2.map (latticeShift a).toHom e ∈ (γ.map (latticeShift a).toHom).edges := by
      rw [SimpleGraph.Walk.edges_map]
      exact List.mem_map_of_mem he
    have h2 : Sym2.map (· + a) e ∈ slabEdges p q := h.2.1 _ h1
    have h3 : Sym2.map (· + a) e ∈ slabEdges ((p - a.1) + a.1) ((q - a.1) + a.1) := by
      rw [sub_add_cancel, sub_add_cancel]; exact h2
    exact (Proofs.ShortLengths.map_mem_slabEdges_iff a e).1 h3
  · rw [← walkCost_map_latticeShift, Proofs.ShortLengths.slabTime_translate]
    simpa using h.2.2

/-- A cube, translated. -/
theorem sub_mem_transverseCube {p : ℤ} {c : EuclideanSpace ℝ (Fin m)} {a₀ : ℝ} (a : Vertex m)
    {u : Vertex m} (hu : u ∈ transverseCube p c a₀) :
    u - a ∈ transverseCube (p - a.1) (c - transversePoint a.2) a₀ := by
  refine ⟨by simp [hu.1], fun j => ?_⟩
  have := hu.2 j
  simp only [Prod.snd_sub, Pi.sub_apply, Int.cast_sub, PiLp.sub_apply, transversePoint_apply]
  convert this using 2
  ring

/-- The moments of the radius for `T`, under a translation. -/
theorem lintegral_locRadius_le {M : Model m} (hM : M.Standing) (a : Vertex m)
    {I I' I₀ I₀' : Set (Vertex m)} (hI : ∀ u ∈ I, u - a ∈ I₀) (hI' : ∀ v ∈ I', v - a ∈ I₀')
    (W : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ ω, locRadius ω I I' W ^ p ∂M.P ≤ ∫⁻ ω, locRadius ω I₀ I₀' W ^ p ∂M.P := by
  rw [← lintegral_comp_translate hM a fun ω => locRadius ω I₀ I₀' W ^ p]
  refine lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hp
  simp only [locRadius]
  gcongr
  exact deviation_le_of_shift a (fun γ h => isGeodesic_of_map a ω γ h) hI hI'

/-- The moments of the radius for a slab passage time, under a translation. -/
theorem lintegral_locRadiusSlab_le {M : Model m} (hM : M.Standing) (a : Vertex m)
    {I I' I₀ I₀' : Set (Vertex m)} (hI : ∀ u ∈ I, u - a ∈ I₀) (hI' : ∀ v ∈ I', v - a ∈ I₀')
    (q r : ℤ) (W : ℝ) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ ω, locRadiusSlab ω q r I I' W ^ p ∂M.P ≤
      ∫⁻ ω, locRadiusSlab ω (q - a.1) (r - a.1) I₀ I₀' W ^ p ∂M.P := by
  rw [← lintegral_comp_translate hM a fun ω => locRadiusSlab ω (q - a.1) (r - a.1) I₀ I₀' W ^ p]
  refine lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hp
  simp only [locRadiusSlab]
  gcongr
  exact deviation_le_of_shift a (fun γ h => isSlabGeodesic_of_map a ω q r γ h) hI hI'

end CurvatureVariance.Paper.Localization.Loc
