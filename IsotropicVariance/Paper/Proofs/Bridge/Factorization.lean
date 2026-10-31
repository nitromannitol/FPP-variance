/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Model
public import IsotropicVariance.Infra.Example.LocalDensity
public import IsotropicVariance.Infra.Instances.TestCoding
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The information of a compact set determines what agrees on it

Item (1) of Assumption `ass:local` says that `ρ(ν, x)` depends only on the restriction of `ν`
to the closed unit ball around `x` (`WhiteNoiseConfig.AgreeOn`). The interface asks for more:
measurability for the information of that ball (`Setting.determined`). On a standard Borel
carrier the two are equivalent for Borel functions:

- **Blackwell's theorem** (`measurable_comap_of_factors`): a Borel function constant on the
  fibers of a Borel map `f` into a Polish space is measurable for the σ-algebra pulled back by
  `f`. The images by `f` of a Borel set saturated by its fibers and of its complement are
  disjoint analytic sets, which the Lusin separation theorem separates by a Borel set.
- The block `𝓓_K` of a compact `K` is second countable
  (`Infra.Instances.secondCountable_testBlock`), so the values of a configuration on a dense
  sequence of `𝓓_K` determine its restriction to `K`
  (`agreeOn_of_eq_on_seq`); these values are measurable for the information of `K`.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

namespace IsotropicVariance.Paper.Proofs.Bridge

/-- **Blackwell's theorem**: a Borel function constant on the fibers of a Borel map from a
standard Borel space to a Polish space is measurable for the pulled-back σ-algebra. -/
theorem measurable_comap_of_factors {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) {h : X → ℝ} (hh : Measurable h)
    (hfac : ∀ x x', f x = f x' → h x = h x') :
    Measurable[MeasurableSpace.comap f inferInstance] h := by
  intro B hB
  have hA : MeasurableSet (h ⁻¹' B) := hh hB
  have hs := hA.analyticSet_image hf
  have ht := hA.compl.analyticSet_image hf
  have hd : Disjoint (f '' (h ⁻¹' B)) (f '' (h ⁻¹' B)ᶜ) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
    exact hx' (show h x' ∈ B by rw [hfac x' x hxx']; exact hx)
  obtain ⟨u, hsu, htu, hu⟩ := hs.measurablySeparable ht hd
  refine ⟨u, hu, ?_⟩
  ext x
  constructor
  · intro hx
    by_contra hxB
    exact Set.disjoint_left.mp htu ⟨x, hxB, rfl⟩ hx
  · intro hx
    exact hsu ⟨x, hx, rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A test function supported in `K`, as an element of the block `𝓓_K`. -/
noncomputable def toSupportedIn (K : Compacts E) (φ : 𝓓((⊤ : Opens E), ℝ))
    (hφ : tsupport ⇑φ ⊆ K) : 𝓓_{K}(E, ℝ) :=
  ⟨φ, φ.contDiff, fun _ hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hφ h))⟩

theorem ofSupportedIn_toSupportedIn (K : Compacts E) (φ : 𝓓((⊤ : Opens E), ℝ))
    (hφ : tsupport ⇑φ ⊆ K) :
    TestFunction.ofSupportedIn (subset_univ _) (toSupportedIn K φ hφ) = φ :=
  TestFunction.ext fun _ => rfl

/-- Two configurations equal on a dense sequence of the block `𝓓_K` agree on `K`. -/
theorem agreeOn_of_eq_on_seq {K : Compacts E} {d : ℕ → 𝓓_{K}(E, ℝ)} (hd : DenseRange d)
    {ν ν' : WhiteNoiseConfig E}
    (h : ∀ n, ν (TestFunction.ofSupportedIn (subset_univ _) (d n)) =
      ν' (TestFunction.ofSupportedIn (subset_univ _) (d n))) :
    WhiteNoiseConfig.AgreeOn (K : Set E) ν ν' := by
  intro φ hφ
  have hι := TestFunction.continuous_ofSupportedIn (n := ⊤) (F := ℝ) (Ω := (⊤ : Opens E))
    (K := K) (subset_univ _)
  have heq := hd.equalizer ((map_continuous ν).comp hι) ((map_continuous ν').comp hι) (funext h)
  have := congrFun heq (toSupportedIn K φ hφ)
  simpa only [Function.comp_apply, ofSupportedIn_toSupportedIn] using this

variable {m : ℕ}

/-- **Measurability for the information of a compact set**: on a standard Borel carrier, a Borel
function of the configuration that only depends on its restriction to a compact `K` is
measurable for the information of `K`. -/
theorem measurable_info_of_agreeOn [StandardBorelSpace (WhiteNoiseConfig (Pt m))]
    (K : Compacts (Pt m)) {h : WhiteNoiseConfig (Pt m) → ℝ} (hh : Measurable h)
    (hfac : ∀ ν ν', WhiteNoiseConfig.AgreeOn (K : Set (Pt m)) ν ν' → h ν = h ν') :
    Measurable[Paper.Noise.info Paper.Noise.white (K : Set (Pt m))] h := by
  have := Infra.Instances.secondCountable_testBlock K
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq 𝓓_{K}(Pt m, ℝ)
  let f : WhiteNoiseConfig (Pt m) → ℕ → ℝ := fun ν n =>
    ν (TestFunction.ofSupportedIn (subset_univ _) (d n))
  have hf : Measurable f :=
    Measurable.of_eval fun n => Infra.Example.measurable_whiteNoise_eval _
  have hc := measurable_comap_of_factors hf hh
    (fun ν ν' hνν' => hfac ν ν' (agreeOn_of_eq_on_seq hd (fun n => congrFun hνν' n)))
  have hle : MeasurableSpace.comap f inferInstance ≤
      Paper.Noise.info Paper.Noise.white (K : Set (Pt m)) := by
    change (⨆ n, (inferInstance : MeasurableSpace ℝ).comap (fun g : ℕ → ℝ => g n)).comap f ≤ _
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun n => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (TestFunction.ofSupportedIn (subset_univ _) (d n))
      (le_iSup_of_le (d n).tsupport_subset le_rfl)
  exact hc.mono hle le_rfl

/-- **Item (1) of Assumption `ass:local` as measurability** (`Setting.determined`): a white-noise
local density at `x` is measurable for the information of the closed unit ball around `x`. -/
theorem measurable_density_closedBall [StandardBorelSpace (WhiteNoiseConfig (Pt m))]
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) (x : Pt m) :
    Measurable[Paper.Noise.info Paper.Noise.white (Metric.closedBall x 1)] fun ν => ρ ν x :=
  measurable_info_of_agreeOn ⟨Metric.closedBall x 1, isCompact_closedBall x 1⟩
    (hρ.measurable.comp (measurable_id.prodMk measurable_const))
    (fun ν ν' h => hρ.determined x ν ν' h)

end IsotropicVariance.Paper.Proofs.Bridge
