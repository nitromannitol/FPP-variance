/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Example.Definitions
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Tactic.FunProp

/-!
# Continuity of translating a test function

The topology on `𝓓` is Mathlib's locally convex inductive-limit topology. Near any translation
parameter all supports lie in one compact ball. On that fixed-support space continuity is
checked in the supremum norm of every derivative.
-/

@[expose] public section
open Set TopologicalSpace Function
open scoped Distributions Topology
namespace IsotropicVariance.Infra.Example

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation of a test function, with the usual pullback sign. -/
noncomputable def translate (f : 𝓓((⊤ : Opens E), ℝ)) (x : E) : 𝓓((⊤ : Opens E), ℝ) where
  toFun y := f (y - x)
  contDiff' := f.contDiff.comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (Homeomorph.subRight x)
  tsupport_subset' := by simp

lemma tsupport_translate_subset (f : 𝓓((⊤ : Opens E), ℝ))
    (hf : tsupport ⇑f ⊆ Metric.closedBall 0 1) (x : E) :
    tsupport ⇑(translate f x) ⊆ Metric.closedBall x 1 := by
  intro y hy
  have heq : ⇑(translate f x) = ⇑f ∘ Homeomorph.subRight x := rfl
  rw [heq, tsupport_comp_eq_preimage] at hy
  simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, Homeomorph.subRight_apply, sub_zero] using hf hy

/-- Every derivative of a smooth compactly supported function is uniformly continuous. -/
lemma uniformContinuous_iteratedFDeriv (f : 𝓓((⊤ : Opens E), ℝ)) (i : ℕ) :
    UniformContinuous (iteratedFDeriv ℝ i f) :=
  (f.contDiff.continuous_iteratedFDeriv (by simp)).uniformContinuous_of_tendsto_cocompact
    (f.hasCompactSupport.iteratedFDeriv i).is_zero_at_infty

/-- Translation is continuous in any fixed-support space that contains all the supports
for the parameter family. -/
lemma continuous_translate_supported {X : Type*} [TopologicalSpace X]
    (f : 𝓓((⊤ : Opens E), ℝ)) (p : X → E) (hp : Continuous p) (K : Compacts E)
    (hs : ∀ x, tsupport ⇑(translate f (p x)) ⊆ K) :
    Continuous (fun x => (⟨translate f (p x), (translate f (p x)).contDiff,
      support_subset_iff'.mp ((subset_tsupport _).trans (hs x))⟩ :
        𝓓_{K}(E, ℝ))) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuous_iff.mp (uniformContinuous_iteratedFDeriv f i)
    (ε / 2) (half_pos hε)
  filter_upwards [hp.continuousAt.eventually (Metric.ball_mem_nhds (p x) hδ)] with y hy
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).mpr ?_)
    (half_lt_self hε)
  intro z
  change dist (iteratedFDeriv ℝ i (fun z => f (z - p y)) z)
    (iteratedFDeriv ℝ i (fun z => f (z - p x)) z) ≤ ε / 2
  rw [iteratedFDeriv_comp_sub, iteratedFDeriv_comp_sub]
  exact (hu (by simpa only [Metric.mem_ball, dist_sub_left] using hy)).le

/-- Translation into Mathlib's LF test-function space is continuous. The support bound
is used only to choose one fixed compact support in a neighborhood of each parameter. -/
theorem continuous_translate [ProperSpace E] (f : 𝓓((⊤ : Opens E), ℝ))
    (hf : tsupport ⇑f ⊆ Metric.closedBall 0 1) : Continuous (translate f) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let K : Compacts E := ⟨Metric.closedBall x₀ 2, isCompact_closedBall x₀ 2⟩
  let U := Metric.ball x₀ 1
  have hs (x : U) : tsupport ⇑(translate f x) ⊆ K := by
    intro y hy
    have hy' : dist y x ≤ 1 := tsupport_translate_subset f hf x hy
    have hx : dist (x : E) x₀ < 1 := x.2
    change dist y x₀ ≤ 2
    calc
      dist y x₀ ≤ dist y x + dist (x : E) x₀ := dist_triangle _ _ _
      _ ≤ 1 + 1 := add_le_add hy' hx.le
      _ = 2 := by norm_num
  let lift : U → 𝓓_{K}(E, ℝ) := fun x =>
    ⟨translate f x, (translate f x).contDiff,
      support_subset_iff'.mp ((subset_tsupport _).trans (hs x))⟩
  have hlift : Continuous lift := continuous_translate_supported f Subtype.val
    continuous_subtype_val K hs
  have hinc := TestFunction.continuous_ofSupportedIn (Ω := (⊤ : Opens E)) (F := ℝ) (n := ⊤)
    (K_sub_Ω := subset_univ (K : Set E))
  have hlocal : Continuous (fun x : U => translate f (x : E)) := by
    convert hinc.comp hlift using 1
    funext x
    rfl
  have hon : ContinuousOn (translate f) U := continuousOn_iff_continuous_domRestrict.mpr hlocal
  exact hon.continuousAt (Metric.ball_mem_nhds x₀ zero_lt_one)

/-- Reflection followed by translation is continuous in the LF topology. -/
theorem continuous_reflectTranslate {m : ℕ} (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ : tsupport ⇑χ ⊆ Metric.closedBall 0 1) :
    Continuous (TestFunction.reflectTranslate χ) := by
  let f := TestFunction.reflectTranslate χ 0
  have hf : tsupport ⇑f ⊆ Metric.closedBall 0 1 := by
    intro y hy
    have heq : ⇑f = ⇑χ ∘ Homeomorph.subLeft (0 : Pt m) := rfl
    rw [heq, tsupport_comp_eq_preimage] at hy
    simpa [dist_eq_norm] using hχ hy
  have heq : TestFunction.reflectTranslate χ = translate f := by
    funext x
    apply TestFunction.ext
    intro y
    change χ (x - y) = χ (0 - (y - x))
    congr 1
    abel
  rw [heq]
  exact continuous_translate f hf

end IsotropicVariance.Infra.Example
