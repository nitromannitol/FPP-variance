/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Localization.ModulusAssembly
public import CurvatureVariance.Paper.Proofs.Localization.ModulusRerouting
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith
import CurvatureVariance.Paper.Proofs.Moments.ExpArrayGeometry

/-!
# Lemma `lem:modulus`: the two events

The last sentence of the proof of Lemma `lem:modulus`, for fixed `N`, `A`, `ℓ` and a pair of cubes
`I`, `I'`. For the supremum `Z` of equation `eq:modulus`:

* on `{R ≤ 1/g}`, the first vertex `x` and the last vertex `x'` of a geodesic lie in the boxes, and
  `Z ≤ 4D + 2 C(b) g Q_ℓ`, by the rerouting (`abs_modulus_le_of_reroute`);
* on `{R > 1/g}`, `Z ≤ 2 X + sup φ`, for the variable `X ≤ O₁(C(b) Q_ℓ)` of Proposition
  `prop:profiles` (`abs_modulus_le_of_abs_le`), and Hölder's inequality with the moment of order
  `16d` of `R`, Lemma `lem:localization` at `p = 16d`, gives the factor `C(b) g`.

This is `exists_modulus_bound`, with the rerouting of the paper's proof in place of the subslabs of
the proof of [AB26, Lemma 5.2], and with the moment of order `16d` of `R`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Localization.Modulus

variable {m : ℕ}

/-- `((x^{2p})^{1/(2p)}) = x` for `x ≥ 0` and `p ≥ 1`. -/
theorem pow_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : 1 ≤ p) :
    (x ^ (2 * p)) ^ (1 / (2 * (p : ℝ))) = x := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h := Real.pow_rpow_inv_natCast hx (n := 2 * p) (by omega)
  rwa [show ((2 * p : ℕ) : ℝ)⁻¹ = 1 / (2 * (p : ℝ)) by push_cast; rw [one_div]] at h

/-- **The two events.** With `I = transverseCube p c a`, `I' = transverseCube (p + ℓ) c' a'`, boxes
of half-side `ρ` at the hyperplanes `p + s` and `p + ℓ − s`, a variable `Y` as `D` on these boxes
(`hY`), `Xᵢ` from Proposition `prop:profiles` on `I × I'`, the change `D` of `φ` under a move of
one endpoint, and the moment of order `16d` of `R`: one random variable `X` dominates the quantity
of equation `eq:modulus`, with
`‖X‖_{8d} ≤ c_p 4θ + 2D + (c_{2p} 2θᵢ + F) g Cr`, `c_p = 2(1 + p!)`, `p = 8d`. -/
theorem exists_modulus_bound (M : Model m) (hM : M.Standing) {p : ℤ} {ℓ s : ℕ}
    (hs2 : 2 * s ≤ ℓ) {c c' t : EuclideanSpace ℝ (Fin m)} {a a' : ℝ} {P₀ : Pt m}
    (hP₀ : IsSubgradient M.μ (slopeVec t) P₀) {Wl g h ρ θ θi D F Cr T : ℝ} (hWl : 0 < Wl)
    (hg : 0 < g) (hθ : 0 < θ) (hθi : 0 < θi) (hD : 0 ≤ D) (hF : 0 ≤ F) (hCr : 0 ≤ Cr)
    (hcc : ‖c' - c - (ℓ : ℝ) • t‖ ≤ 2 * Real.sqrt ((m : ℝ) + 1)) (hT : ‖t‖ ≤ T)
    (ha : a ≤ 2 * ρ) (ha' : a' ≤ 2 * ρ)
    (hρ : (1 + T) * (g⁻¹ * Wl) + max a a' / 2 + 4 * Real.sqrt ((m : ℝ) + 1) ≤ ρ)
    (hgeo : ∀ᵐ ω ∂M.P, ∀ u v : Vertex m, ∃ γ : (latticeGraph m).Walk u v,
      γ.IsPath ∧ walkCost ω γ = passageTime ω u v)
    (hY : ∃ Y : Config m → ℝ, CurvatureVariance.IsOs M.P 1 θ Y ∧ ∀ᵐ ω ∂M.P,
      (∀ u ∈ transverseCube p c (2 * ρ), ∀ x ∈ transverseCube (p + s) (c + (s : ℝ) • t) (2 * ρ),
        |passageTimeReal ω u x - M.μ.1 (point x - point u)| ≤ Y ω) ∧
      (∀ x ∈ transverseCube (p + ((ℓ : ℤ) - s)) (c' - (s : ℝ) • t) (2 * ρ),
        ∀ v ∈ transverseCube (p + ℓ) c' (2 * ρ),
          |passageTimeReal ω x v - M.μ.1 (point v - point x)| ≤ Y ω))
    (hXi : ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 θi X ∧ ∀ᵐ ω ∂M.P,
      ∀ u ∈ transverseCube p c a, ∀ v ∈ transverseCube (p + ℓ) c' a',
        |passageTimeReal ω u v - M.μ.1 (point v - point u)| ≤ X ω)
    (hD₁ : ∀ u ∈ transverseCube p c a, ∀ u₂ ∈ transverseCube p c a,
      ‖point u - point u₂‖ ≤ h * Wl →
      ∀ x ∈ transverseCube (p + s) (c + (s : ℝ) • t) (2 * ρ),
        |supportExcess M.μ P₀ (point x - point u₂) - supportExcess M.μ P₀ (point x - point u)| ≤ D)
    (hD₂ : ∀ v ∈ transverseCube (p + ℓ) c' a', ∀ v₂ ∈ transverseCube (p + ℓ) c' a',
      ‖point v - point v₂‖ ≤ h * Wl →
      ∀ x ∈ transverseCube (p + ((ℓ : ℤ) - s)) (c' - (s : ℝ) • t) (2 * ρ),
        |supportExcess M.μ P₀ (point v₂ - point x) - supportExcess M.μ P₀ (point v - point x)| ≤ D)
    (hFb : ∀ u ∈ transverseCube p c a, ∀ v ∈ transverseCube (p + ℓ) c' a',
      supportExcess M.μ P₀ (point v - point u) ≤ F)
    (hR : ∫⁻ ω, locRadius ω (transverseCube p c a) (transverseCube (p + ℓ) c' a') Wl ^
        (2 * (8 * (m + 1))) ∂M.P ≤ ENNReal.ofReal (Cr ^ (2 * (8 * (m + 1))))) :
    ∃ X : Config m → ℝ,
      eLpNorm X (8 * (m + 1) : ℕ) M.P ≤ ENNReal.ofReal
        (2 * (1 + ((8 * (m + 1)).factorial : ℝ)) * (4 * θ) + 2 * D +
          (2 * (1 + ((2 * (8 * (m + 1))).factorial : ℝ)) * (2 * θi) + F) * (g * Cr)) ∧
      ∀ᵐ ω ∂M.P, ∀ u ∈ transverseCube p c a, ∀ u₂ ∈ transverseCube p c a,
        ∀ v ∈ transverseCube (p + ℓ) c' a', ∀ v₂ ∈ transverseCube (p + ℓ) c' a',
        ‖point u - point u₂‖ ≤ h * Wl → ‖point v - point v₂‖ ≤ h * Wl →
        |passageTimeReal ω u v - passageTimeReal ω u₂ v₂ -
          inner ℝ P₀ (point v - point u - point v₂ + point u₂)| ≤ X ω := by
  classical
  have := hM.probP
  set I := transverseCube p c a with hIdef
  set I' := transverseCube (p + ℓ) c' a' with hI'def
  obtain ⟨Y, hYO, hYb⟩ := hY
  obtain ⟨Xi, hXiO, hXib⟩ := hXi
  set E := {ω : Config m | ENNReal.ofReal g⁻¹ < locRadius ω I I' Wl} with hEdef
  have hEm : MeasurableSet E := measurableSet_lt measurable_const (measurable_locRadius I I' Wl)
  have hPE := measure_lt_locRadius_le hg hR
  set pp : ℕ := 8 * (m + 1) with hpp
  have hp1 : 1 ≤ pp := by omega
  set Z : Config m → ℝ := fun ω => max (2 * Xi ω) 0 + F with hZ
  set X : Config m → ℝ := fun ω => max (4 * Y ω) 0 + 2 * D + E.indicator Z ω with hX
  have hsub : I ⊆ transverseCube p c (2 * ρ) := fun x hx =>
    ⟨hx.1, fun j => (hx.2 j).trans (by linarith only [ha])⟩
  have hsub' : I' ⊆ transverseCube (p + ℓ) c' (2 * ρ) := fun x hx =>
    ⟨hx.1, fun j => (hx.2 j).trans (by linarith only [ha'])⟩
  refine ⟨X, ?_, ?_⟩
  · -- the `L^{8d}` bound
    have h4Y := (Infra.Os.isOs_mul_iff (show (0 : ℝ) < 4 by norm_num)).mpr hYO
    have h2Xi := (Infra.Os.isOs_mul_iff two_pos).mpr hXiO
    have e1 := eLpNorm_max_le_of_isOs h4Y (by positivity) hp1
    have e3 := eLpNorm_const_of_nonneg (P := M.P) (by positivity : (0 : ℝ) ≤ 2 * D) hp1
    have mXi : AEStronglyMeasurable (fun ω => max (2 * Xi ω) 0) M.P :=
      (h2Xi.1.max aemeasurable_const).aestronglyMeasurable
    have mZ : AEStronglyMeasurable Z M.P := mXi.add aestronglyMeasurable_const
    have hgCr : 0 ≤ g * Cr := mul_nonneg hg.le hCr
    have e4 : eLpNorm (E.indicator Z) pp M.P ≤
        (ENNReal.ofReal (2 * (1 + ((2 * pp).factorial : ℝ)) * (2 * θi)) + ENNReal.ofReal F) *
          ENNReal.ofReal (g * Cr) := by
      refine (eLpNorm_indicator_le hEm mZ hp1).trans ?_
      gcongr
      · have hp2 : 1 ≤ 2 * pp := by omega
        refine (eLpNorm_add_le (by exact_mod_cast hp2)).trans ?_
        gcongr
        · exact eLpNorm_max_le_of_isOs h2Xi (by positivity) hp2
        · exact (eLpNorm_const_of_nonneg hF hp2).le
      · calc M.P E ^ (1 / (2 * (pp : ℝ)))
            ≤ ENNReal.ofReal ((g * Cr) ^ (2 * pp)) ^ (1 / (2 * (pp : ℝ))) := by
              gcongr
          _ = ENNReal.ofReal (((g * Cr) ^ (2 * pp)) ^ (1 / (2 * (pp : ℝ)))) :=
              ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
          _ = ENNReal.ofReal (g * Cr) := by rw [pow_rpow_two_mul hgCr hp1]
    have hXeq : X = ((fun ω => max (4 * Y ω) 0) + fun _ => 2 * D) + E.indicator Z := by
      funext ω; simp only [hX, Pi.add_apply]
    have hp1' : (1 : ℝ≥0∞) ≤ (pp : ℝ≥0∞) := by exact_mod_cast hp1
    rw [hXeq]
    calc eLpNorm (((fun ω => max (4 * Y ω) 0) + fun _ => 2 * D) + E.indicator Z) pp M.P
        ≤ eLpNorm ((fun ω => max (4 * Y ω) 0) + fun _ => 2 * D) pp M.P +
            eLpNorm (E.indicator Z) pp M.P := eLpNorm_add_le hp1'
      _ ≤ (eLpNorm (fun ω => max (4 * Y ω) 0) pp M.P + eLpNorm (fun _ => 2 * D) pp M.P) +
            eLpNorm (E.indicator Z) pp M.P := by
          gcongr
          exact eLpNorm_add_le hp1'
      _ ≤ (ENNReal.ofReal (2 * (1 + (pp.factorial : ℝ)) * (4 * θ)) + ENNReal.ofReal (2 * D)) +
            (ENNReal.ofReal (2 * (1 + ((2 * pp).factorial : ℝ)) * (2 * θi)) +
              ENNReal.ofReal F) * ENNReal.ofReal (g * Cr) := by
          gcongr
          exact e3.le
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) hF, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  · -- the domination
    filter_upwards [hgeo, hYb, hXib] with ω hgω hYω hXiω
    intro u hu u₂ hu₂ v hv v₂ hv₂ huu hvv
    have hXω : 4 * Y ω + 2 * D ≤ X ω ∧ (ω ∈ E → 2 * Xi ω + F ≤ X ω) := by
      have i0 : 0 ≤ E.indicator Z ω :=
        indicator_nonneg (fun ω _ => add_nonneg (le_max_right _ _) hF) ω
      have k1 := le_max_left (4 * Y ω) 0
      have k3 := le_max_right (4 * Y ω) 0
      have hXe : X ω = max (4 * Y ω) 0 + 2 * D + E.indicator Z ω := rfl
      refine ⟨by rw [hXe]; linarith only [k1, i0], fun hω => ?_⟩
      have hZe : E.indicator Z ω = max (2 * Xi ω) 0 + F := indicator_of_mem hω Z
      rw [hXe, hZe]
      have k5 := le_max_left (2 * Xi ω) 0
      linarith only [k3, k5, hD]
    by_cases hω : ω ∈ E
    · have hb := abs_modulus_le_of_abs_le (T := passageTimeReal ω) M.μ P₀ hXiω
        (fun u _ v _ => ⟨supportExcess_nonneg hP₀ _, hFb u ‹_› v ‹_›⟩) hu hu₂ hv hv₂
      exact hb.trans (hXω.2 hω)
    · have hRle : locRadius ω I I' Wl ≤ ENNReal.ofReal g⁻¹ := not_lt.mp hω
      have hg' : 0 ≤ g⁻¹ := inv_nonneg.mpr hg.le
      have htri : ∀ a b c, passageTimeReal ω a c ≤ passageTimeReal ω a b + passageTimeReal ω b c :=
        fun a b c => by
          have := Infra.FPP.passageTime_triangle ω a b c
          unfold passageTimeReal; exact_mod_cast this
      -- the first vertex and the last vertex of a geodesic lie in the boxes
      have hsp : ∀ u ∈ I, ∀ v ∈ I', ∃ x ∈ transverseCube (p + s) (c + (s : ℝ) • t) (2 * ρ),
          ∃ x' ∈ transverseCube (p + ((ℓ : ℤ) - s)) (c' - (s : ℝ) • t) (2 * ρ),
            passageTimeReal ω u v = passageTimeReal ω u x + passageTimeReal ω x x' +
              passageTimeReal ω x' v := by
        intro u hu v hv
        obtain ⟨γ, hγp, hγc⟩ := hgω u v
        obtain ⟨x, x', γ₁, γ₂, γ₃, hsplit, hx1, hx1', -, -⟩ := exists_first_last γ
          (k := p + s) (k' := p + ((ℓ : ℤ) - s)) (by rw [hu.1]; omega) (by omega)
          (by rw [hv.1]; omega)
        have hxγ : x ∈ γ.support := by
          rw [hsplit, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inl γ₁.end_mem_support
        have hxγ' : x' ∈ γ.support := by
          rw [hsplit, SimpleGraph.Walk.mem_support_append_iff,
            SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (Or.inr γ₃.start_mem_support)
        refine ⟨x, ⟨hx1, fun j => ?_⟩, x', ⟨hx1', fun j => ?_⟩,
          passageTimeReal_eq_add_add hγc hsplit⟩
        · have := abs_offset_le_of_locRadius_le (L := (s : ℤ)) hWl hg' hcc hT hRle hu hv ⟨hγp, hγc⟩
            hxγ hx1 j
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Int.cast_natCast] at this ⊢
          have h4 : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_nonneg _
          linarith only [this, hρ, h4]
        · have := abs_offset_le_of_locRadius_le (L := (ℓ : ℤ) - s) hWl hg' hcc hT hRle hu hv
            ⟨hγp, hγc⟩ hxγ' hx1' j
          have hcj := (Moments.ExpArray.abs_apply_le_norm (c' - c - (ℓ : ℝ) • t) j).trans hcc
          simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Int.cast_sub,
            Int.cast_natCast] at this hcj ⊢
          have : |(x'.2 j : ℝ) - (c' j - s * t j)| ≤
              |(x'.2 j : ℝ) - (c j + (ℓ - s) * t j)| + |c' j - c j - ℓ * t j| := by
            have := abs_add_le ((x'.2 j : ℝ) - (c j + (ℓ - s) * t j)) (-(c' j - c j - ℓ * t j))
            rw [abs_neg] at this
            calc |(x'.2 j : ℝ) - (c' j - s * t j)|
                = |(x'.2 j : ℝ) - (c j + (ℓ - s) * t j) + -(c' j - c j - ℓ * t j)| := by
                  congr 1; ring
              _ ≤ _ := this
          linarith only [this, ‹|(x'.2 j : ℝ) - (c j + (ℓ - s) * t j)| ≤ _›, hcj, hρ]
      have hb := abs_modulus_le_of_reroute (T := passageTimeReal ω) htri M.μ P₀
        (close := fun a b => ‖point a - point b‖ ≤ h * Wl)
        (fun a b hab => by rwa [norm_sub_rev]) hsp
        (fun u hu x hx => hYω.1 u (hsub hu) x hx) (fun x hx v hv => hYω.2 x hx v (hsub' hv))
        hD₁ hD₂ hu hu₂ hv hv₂ huu hvv
      exact hb.trans hXω.1

end CurvatureVariance.Paper.Localization.Modulus
