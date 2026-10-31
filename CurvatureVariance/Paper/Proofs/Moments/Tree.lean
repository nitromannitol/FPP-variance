/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Moments.ConnectorRoute
public import CurvatureVariance.Paper.Proofs.Moments.Scales
public import CurvatureVariance.Paper.Contracts.Geometry
public import CurvatureVariance.Paper.Contracts.Inputs
import CurvatureVariance.Infra.FPP.TimeConstantNorm
import CurvatureVariance.Paper.Proofs.Moments.ParentBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma `lem:tree`, equation `eq:tree`: real `s`

The proof of Lemma `lem:tree`: the chaining of [AB26, Lemma 4.1], with the changes of the paper.

The length `s` is real, as in the paper. The chaining of the modules `Moments.Shear`,
`Moments.Chaining`, `Moments.ConnectorLinks` and `Moments.ConnectorPremise` is the cited chaining on
a sheared box, and it is already over a real length: a link is `exists_premise_link`, where the
longitudinal displacement of two lattice points is an integer within `√d` of the real length. So
nothing is rounded here, and there is no ceiling of `s`. The theorem `exists_tree_premise` is the
chaining with `r : ℝ`, on `SupportStatement`, with equation `eq:scales` as the two hypotheses `hW`
and `htt`.

The steps of the paper's proof:

* the points `ū_j(u) ∓ 2^{−j}s(1,t)` are `chainPoint` with `sg = ∓1`. The cells of `shearBox` cut
  the cube and the longitudinal interval together, so the points `q_j(1,t)` of the thickening are
  the longitudinal coordinate of the box centers, as in `thicken_subset_shearBox`;
* the slope margin: the paper has `4/5 < 2^{1/4−δ/100}`. The Lean uses `θ < 1` with `λ|t − t₀| ≤ θ
  λ^{3/4+δ/100}` for `λ ≤ s` (`slope_facts`), which is that bound at `θ = 4/5`, and the rest of the
  ball of `𝒟(λ)` pays for the transverse deviation (`link_numeric`);
* the chain stops at the fixed scale `L₁` (`J = ⌊log₂⌊r/L₁⌋⌋`), so at most a bounded number of
  edges remain to `u` (`isOs_final_step`), and the union bound over them is in `exists_isOs_chain`;
* the deterministic term of a link is `C(b)2^{−j}Q_s + C2^j/s` (`chain_link_bounds`), which is the
  paper's `C(b)2^{−j}Q_s + C` after the sum;
* `Q_{2^{−j}s} ≤ 2^{−j/4}Q_s` (`Q_div_two_pow_le`) stands for the paper's `2^{−2j/5}`: a weaker
  decay, which is all the sum needs.

* `exists_tree_premise`: the chain, for one orientation, under the hypotheses on `s`.
* `treeStatement`: the contract `TreeStatement`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Moments

open CurvatureVariance.Paper CurvatureVariance.Infra.Os

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- The constant of `exists_tree_premise` is positive (stated apart, so that `positivity` runs in a
small context). -/
private theorem tree_Cb_pos (m : ℕ) {CS b ε₁ C₁ θf : ℝ} (hCS : 0 < CS) (hθf : 0 ≤ θf) :
    0 < 2 * ((m : ℝ) + 1) * (1 / (1 - ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹) ^ 2) +
      (1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * θf +
      2 * CS * (36 * m * b ^ 2 + 144 * m * (ε₁ + 1) ^ 2 + 64 * ε₁ ^ 2 + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The link costs are nonnegative. -/
private theorem tree_linkCostBound_nonneg (M : Model m) (T : ℝ) {CS R₂ r : ℝ} (hCS : 0 ≤ CS)
    (hr : 0 ≤ r) (t : E) (j : ℕ) : 0 ≤ linkCostBound M T CS R₂ r t j := by
  unfold linkCostBound; positivity

/-- The constant `L₁` of `exists_tree_premise`. -/
private theorem tree_L₁_bounds {a b c : ℝ} (ha : 0 ≤ a) :
    a ≤ 29 / 32 * (2 * max a (max b c)) ∧ b ≤ 29 / 32 * (2 * max a (max b c)) ∧
      c ≤ 29 / 32 * (2 * max a (max b c)) := by
  have h1 := le_max_left a (max b c)
  have h2 := le_max_right a (max b c)
  have h3 := le_max_left b c
  have h4 := le_max_right b c
  have h0 : 0 ≤ max a (max b c) := ha.trans h1
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [h0, h1, h2, h3, h4]

/-- The constant `Lf₀` of `exists_tree_premise` is nonnegative. -/
private theorem tree_Lf₀_nonneg {T L s ε Y ρ : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hε : 0 ≤ ε) (hY : 0 ≤ Y) (hρ : 0 ≤ ρ) :
    0 ≤ (2 + T) * L / 16 + s * (ε * L + Y + 1) + 2 * (2 + T) * L + ρ := by
  positivity

/-- The constant `C₁` of `exists_tree_premise` is positive. -/
private theorem tree_C₁_pos {T ρ ε Y : ℝ} (hT : 0 ≤ T) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hY : 0 ≤ Y) :
    0 < (1 + T) * (1 / 32 + 2 * ρ + 2) + ε + 2 * Y + 5 := by
  positivity

/-- The transverse margin of `exists_tree_premise`, over abstract reals. -/
private theorem tree_margin {s θ' ε bW x Y R : ℝ} (hs : 0 ≤ s) (hθ : θ' < 1) (hx : 0 ≤ x)
    (hε : ε = (1 - θ') / (12 * s + 12)) (hW : bW ≤ ε * x) (hY : 12 * s * Y ≤ (1 - θ') / 2 * x)
    (hR : R ≤ bW / 2 + Y) : 12 * s * R ≤ (1 - θ') * x := by
  have hk : 0 < 1 - θ' := by linarith only [hθ]
  have hd : 0 < 12 * s + 12 := by linarith only [hs]
  have h3 : 6 * s * ε ≤ (1 - θ') / 2 := by
    rw [hε, ← mul_div_assoc, div_le_div_iff₀ hd (by norm_num)]
    linarith only [hk]
  have h2 := mul_le_mul_of_nonneg_left hW (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hs)
  have h4 := mul_le_mul_of_nonneg_right h3 hx
  have h9 := mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hs)
  have e1 : 6 * s * (ε * x) = 6 * s * ε * x := by ring
  have e2 : 12 * s * (bW / 2 + Y) = 6 * s * bW + 12 * s * Y := by ring
  have e3 : (1 - θ') * x = (1 - θ') / 2 * x + (1 - θ') / 2 * x := by ring
  linarith only [h2, h4, h9, e1, e2, e3, hY]

/-- The final steps of the chain of `exists_tree_premise`, over abstract reals. -/
private theorem tree_final_numeric {R₁ R₂ r x V T L s ε Y bW ρ : ℝ} (hx : 1 ≤ x)
    (hR₁ : R₁ ≤ r / 32) (hrJ : r / x < 2 * L) (hV0 : 0 ≤ V) (hV : V ≤ 2 + T) (hL : 1 ≤ L)
    (hs : 0 ≤ s) (hε : 0 ≤ ε) (hY : 0 ≤ Y + 1) (hR₂ : R₂ ≤ bW / 2 + (Y + 1)) (hW : bW ≤ ε * r) :
    R₁ / x * V + s * (R₂ / x) + r / x * V + ρ ≤
      (2 + T) * L / 16 + s * (ε * L + Y + 1) + 2 * (2 + T) * L + ρ := by
  have hx0 : 0 < x := by linarith only [hx]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have a1 : R₁ / x ≤ L / 16 := by
    calc R₁ / x ≤ (r / 32) / x := div_le_div_of_nonneg_right hR₁ hx0.le
      _ = (r / x) / 32 := by ring
      _ ≤ L / 16 := by linarith only [hrJ]
  have e1 : R₁ / x * V ≤ (2 + T) * L / 16 := by
    calc R₁ / x * V ≤ L / 16 * (2 + T) := mul_le_mul a1 hV hV0 (by linarith only [hL])
      _ = (2 + T) * L / 16 := by ring
  have e2 : s * (R₂ / x) ≤ s * (ε * L + Y + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ hs
    calc R₂ / x ≤ (ε * r / 2 + (Y + 1)) / x :=
          div_le_div_of_nonneg_right (by linarith only [hR₂, hW]) hx0.le
      _ = ε / 2 * (r / x) + (Y + 1) / x := by ring
      _ ≤ ε / 2 * (2 * L) + (Y + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left hrJ.le (by linarith only [hε]))
            (div_le_self hY hx)
      _ = ε * L + Y + 1 := by ring
  have e3 : r / x * V ≤ 2 * (2 + T) * L := by
    calc r / x * V ≤ (2 * L) * (2 + T) := mul_le_mul hrJ.le hV hV0 (by linarith only [hL])
      _ = 2 * (2 + T) * L := by ring
  linarith only [e1, e2, e3]

/-- The two factors of the cardinality in `exists_tree_premise`, over abstract reals. -/
private theorem tree_card_numeric {R₁ R₂ ρ ε Y T r n C bW : ℝ} (hr1 : 1 ≤ r) (hρ1 : 1 ≤ ρ)
    (hε : 0 ≤ ε) (hY : 1 ≤ Y) (hT : 0 ≤ T) (hR₁ : R₁ = r / 64 + ρ + 1)
    (hC : C = (1 + T) * (1 / 32 + 2 * ρ + 2) + ε + 2 * Y + 5) (hn : n ≤ 1 + T)
    (hR₁0 : 0 < R₁) (hR₂ : R₂ ≤ bW / 2 + (Y + 1)) (hW : bW ≤ ε * r) :
    2 * R₁ + 3 ≤ C * r ∧ 2 * R₁ * n + 2 * R₂ + 3 ≤ C * r := by
  have hr0 : 0 ≤ r := by linarith only [hr1]
  have hρr : ρ ≤ ρ * r := le_mul_of_one_le_right (by linarith only [hρ1]) hr1
  have hεr : 0 ≤ ε * r := mul_nonneg hε hr0
  have hYr : Y ≤ Y * r := le_mul_of_one_le_right (by linarith only [hY]) hr1
  have hTr : 0 ≤ T * (r / 32 + 2 * (ρ * r) + 2 * r) :=
    mul_nonneg hT (by linarith only [hρr, hρ1, hr1])
  have hCr : C * r = (1 + T) * (r / 32 + 2 * (ρ * r) + 2 * r) + ε * r + 2 * (Y * r) + 5 * r := by
    rw [hC]; ring
  refine ⟨by linarith only [hR₁, hCr, hρr, hεr, hYr, hY, hTr, hr1], ?_⟩
  have h1 : 2 * R₁ * n ≤ (1 + T) * (r / 32 + 2 * ρ + 2) := by
    calc 2 * R₁ * n ≤ 2 * R₁ * (1 + T) :=
          mul_le_mul_of_nonneg_left hn (by linarith only [hR₁0])
      _ = (1 + T) * (r / 32 + 2 * ρ + 2) := by rw [hR₁]; ring
  have hT₁ : (1 + T) * (2 * ρ + 2) ≤ (1 + T) * (2 * (ρ * r) + 2 * r) :=
    mul_le_mul_of_nonneg_left (by linarith only [hρr, hr1]) (by linarith only [hT])
  linarith only [h1, hT₁, hR₂, hW, hCr, hYr, hr1]

/-- **The chaining of Lemma `lem:tree` at a real length** (its proof). For `r ≥ r₀`
with the transverse margin `b W_r ≤ ε r^{3/4+δ/100}` and `r|t − t₀|^{2+δ} ≤ Q_r`, both from equation
`eq:scales`, a cube of side at most `b W_r` with center `(p, c)`, a slope
`|t − t₀| ≤ θ r^{δ/100−1/4}`, and a lattice point `a` within `√d` of `(p, c) + sg·r(1, t)`,
`sg = ±1`: `sup_u (T(a, u) − (−sg ζ_t)·(u − a)) ≤ O₁(C(b) Q_r)` over the thickening of the cube by
`r/64`.

The length `r` is real, and the two hypotheses stand for the computations of `eq:scales`. -/
theorem exists_tree_premise (hSupp : Contracts.SupportStatement m) (bd : Bounds m)
    (hbd : bd.Valid) {θ : ℝ} (hθ : θ < 1) {b : ℝ} (hb : 1 ≤ b) :
    ∃ r₀ ε Cb : ℝ, 0 < ε ∧ 0 < Cb ∧ ∀ M : Model m, M.Standing → M.Fits bd →
      ∀ K : ℕ, 10 ^ 4 ≤ K → ∀ A : ℝ, 1 ≤ A → ∀ N : ℕ,
      Premise M K A N → ∀ r : ℝ, r₀ ≤ r → r ≤ N / 2 →
      b * W M K A r ≤ ε * r ^ ((3 : ℝ) / 4 + M.δ / 100) →
      ∀ (p : ℤ) (c t : E) (a₀ : ℝ), 0 ≤ a₀ → a₀ ≤ b * W M K A r →
      ‖t - M.t₀‖ ≤ θ * r ^ (M.δ / 100 - 1 / 4) →
      r * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Q M K A r →
      ∀ P : Pt m, IsSubgradient M.μ (slopeVec t) P → ∀ sg : ℝ, (sg = 1 ∨ sg = -1) →
      ∀ a : Vertex m,
      ‖point a - (WithLp.toLp 2 ((p : ℝ), c) + (sg * r) • slopeVec t)‖ ≤
        Real.sqrt ((m : ℝ) + 1) →
      ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (Cb * Q M K A r) X ∧
        ∀ ω, ∀ u ∈ thicken (transverseCube p c a₀) t (r / 64),
          passageTimeReal ω a u - inner ℝ ((-sg) • P) (point u - point a) ≤ X ω := by
  obtain ⟨cS, CS, r₁, hcS, hCS, hr₁, -, hsupp⟩ := hSupp bd hbd
  obtain ⟨lo, hi, hlo, hhi, hμ₀⟩ := Infra.FPP.PtNorm.exists_bounds bd.law.μ
  obtain ⟨θ₀, hθ₀, hw₀⟩ := exists_isOs_weight hbd.law
  let ρ := Real.sqrt ((m : ℝ) + 1)
  have hρ : ρ = Real.sqrt ((m : ℝ) + 1) := rfl
  have hρ1 : 1 ≤ ρ := by rw [hρ, Real.one_le_sqrt]; linarith only [Nat.cast_nonneg (α := ℝ) m]
  let T₀ := bd.T
  have hT₀ : T₀ = bd.T := rfl
  have hT₀0 : 0 ≤ T₀ := hbd.T_nonneg
  let ε₁ := roundSlack m T₀
  have hε₁ : ε₁ = roundSlack m T₀ := rfl
  have hε₁ρ : ε₁ = (2 + T₀) * ρ := by rw [hε₁, roundSlack]
  have hε₁1 : 1 ≤ ε₁ := one_le_roundSlack m hT₀0
  let θ' := max θ 0
  have hθ' : θ' = max θ 0 := rfl
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hθ'1 : θ' < 1 := max_lt hθ one_pos
  have hsm : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hk : 0 < 1 - θ' := by linarith only [hθ'1]
  have hε₁0 : 0 ≤ ε₁ := by linarith only [hε₁1]
  have hE0 : 0 ≤ ε₁ + 1 := by linarith only [hε₁1]
  have hρ0 : 0 ≤ ρ := by linarith only [hρ1]
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ, 2 * ε₁ + 1 ≤ 29 / 32 * L₁ ∧ (4 * ε₁ / (1 - θ')) ^ 2 ≤ 29 / 32 * L₁ ∧
      (4 / r₁) ^ 5 ≤ 29 / 32 * L₁ := ⟨_, tree_L₁_bounds (by linarith only [hε₁1])⟩
  have hL₁1 : 1 ≤ L₁ := by linarith only [hL₁.1, hε₁1]
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (1 - θ') / (12 * Real.sqrt m + 12) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; exact div_pos hk (by linarith only [hsm])
  obtain ⟨Lf₀, hLf₀⟩ : ∃ Lf₀ : ℝ, Lf₀ = (2 + T₀) * L₁ / 16 + Real.sqrt m * (ε * L₁ + ε₁ + 1) +
      2 * (2 + T₀) * L₁ + ρ := ⟨_, rfl⟩
  have hLf₀0 : 0 ≤ Lf₀ := by
    rw [hLf₀]
    exact tree_Lf₀_nonneg hT₀0 (by linarith only [hL₁1]) hsm hεpos.le hε₁0 hρ0
  let θf := θ₀ * (((m : ℝ) + 1) * Lf₀ + 1) + 2 * (hi * Lf₀)
  have hθf : θf = θ₀ * (((m : ℝ) + 1) * Lf₀ + 1) + 2 * (hi * Lf₀) := rfl
  have hθf0 : 0 ≤ θf :=
    add_nonneg (mul_nonneg hθ₀.le (add_nonneg (mul_nonneg (Nat.cast_add_one_pos m).le hLf₀0)
      zero_le_one)) (mul_nonneg zero_le_two (mul_nonneg hhi.le hLf₀0))
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = (1 + T₀) * (1 / 32 + 2 * ρ + 2) + ε + 2 * ε₁ + 5 := ⟨_, rfl⟩
  have hC₁pos : 0 < C₁ := by
    rw [hC₁]
    exact tree_C₁_pos hT₀0 hρ0 hεpos.le hε₁0
  let Cb := 2 * ((m : ℝ) + 1) * (1 / (1 - ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹) ^ 2) +
      (1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * θf +
      2 * CS * (36 * m * b ^ 2 + 144 * m * (ε₁ + 1) ^ 2 + 64 * ε₁ ^ 2 + 2)
  have hCb : Cb = 2 * ((m : ℝ) + 1) * (1 / (1 - ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹) ^ 2) +
      (1 + ((m : ℝ) + 1) * (|Real.log C₁| + 4) / Real.log 2) * θf +
      2 * CS * (36 * m * b ^ 2 + 144 * m * (ε₁ + 1) ^ 2 + 64 * ε₁ ^ 2 + 2) := rfl
  have hCbpos : 0 < Cb := tree_Cb_pos m hCS hθf0
  let r₀ := max (64 * (ρ + 1)) (max L₁ (max ((2 / r₁) ^ 5)
    ((24 * Real.sqrt m * (ε₁ + 1) / (1 - θ')) ^ 2)))
  have hr₀ : r₀ = max (64 * (ρ + 1)) (max L₁ (max ((2 / r₁) ^ 5)
    ((24 * Real.sqrt m * (ε₁ + 1) / (1 - θ')) ^ 2))) := rfl
  refine ⟨r₀, ε, Cb, hεpos, hCbpos, ?_⟩
  intro M hM hfit K hK A hA N hPrem r hr₀r hrN hW p c t a₀ ha₀ ha₀W ht htt P hP sg hsg a ha
  -- the model: its support bounds, norm bounds and weights, from those at `bd`
  obtain ⟨h24, -⟩ := hsupp M hM hfit
  have hμ := hμ₀
  rw [← hfit.μ_eq] at hμ
  have hw := hw₀
  rw [← hfit.P_eq] at hw
  have hδ := hM.delta_pos
  have hδ1 := hM.delta_le_one
  have hT : ‖M.t₀‖ ≤ T₀ := hfit.t₀_le
  -- the regime
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK
  have hKr : (10000 : ℝ) ≤ K := by exact_mod_cast hK
  have hr64 : 64 * (ρ + 1) ≤ r := le_trans (le_max_left _ _) hr₀r
  have hrL : L₁ ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr₀r
  have hr5 : (2 / r₁) ^ 5 ≤ r :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hr₀r
  have hr24 : (24 * Real.sqrt m * (ε₁ + 1) / (1 - θ')) ^ 2 ≤ r :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hr₀r
  have hr1 : (1 : ℝ) ≤ r := by linarith only [hr64, hρ1]
  have hr0 : (0 : ℝ) < r := by linarith only [hr1]
  let e : ℝ := (3 : ℝ) / 4 + M.δ / 100
  have he : e = (3 : ℝ) / 4 + M.δ / 100 := rfl
  have hre : r ^ e ≤ r := by
    calc r ^ e ≤ r ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr1 (by rw [he]; linarith only [hδ1])
      _ = r := Real.rpow_one _
  obtain ⟨hslope0, htr0⟩ := slope_facts hM hr1 ht hθ
  have hslope : ∀ lam : ℝ, 0 < lam → lam ≤ r → lam * ‖t - M.t₀‖ ≤ θ' * lam ^ e :=
    fun lam hl hlr => hslope0 lam hl hlr
  have ht5 : ‖t - M.t₀‖ ≤ r ^ (-(1 : ℝ) / 5) :=
    htr0.trans (Real.rpow_le_rpow_of_exponent_le hr1 (by linarith only [hδ1]))
  have ht1 : ‖t - M.t₀‖ ≤ 1 :=
    ht5.trans (Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num))
  have htr : ‖t - M.t₀‖ ≤ r₁ / 2 := by
    have := rpow_neg_fifth_le (div_pos two_pos hr₁ : (0 : ℝ) < 2 / r₁) hr5
    rw [one_div_div] at this
    exact ht5.trans this
  have htn : ‖t‖ ≤ 1 + T₀ := (norm_le_of_norm_sub_le_one ht1).trans (by linarith only [hT])
  have hV : ‖slopeVec t‖ ≤ 2 + T₀ := (norm_slopeVec_le t).trans (by linarith only [htn])
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = r / 64 + ρ + 1 := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, R₂ = a₀ / 2 + ρ * (1 + ‖t‖) + 1 := ⟨_, rfl⟩
  have hρt0 : 0 ≤ ρ * (1 + ‖t‖) := mul_nonneg hρ0 (add_nonneg zero_le_one (norm_nonneg t))
  have hR₁pos : 0 < R₁ := by rw [hR₁]; linarith only [hr0, hρ0]
  have hR₂pos : 0 < R₂ := by rw [hR₂]; linarith only [ha₀, hρt0]
  have hR₁r : R₁ ≤ r / 32 := by rw [hR₁]; linarith only [hr64]
  have hρt : ρ * (1 + ‖t‖) ≤ ε₁ := by
    calc ρ * (1 + ‖t‖) ≤ ρ * (2 + T₀) :=
          mul_le_mul_of_nonneg_left (by linarith only [htn]) (by linarith only [hρ1])
      _ = ε₁ := by rw [hε₁ρ]; ring
  have hR₂le : R₂ ≤ b * W M K A r / 2 + (ε₁ + 1) := by
    rw [hR₂]; linarith only [ha₀W, hρt]
  have hre0 : 0 ≤ r ^ e := Real.rpow_nonneg hr0.le e
  have hWe : b * W M K A r ≤ ε * r ^ e := hW
  have hWr : b * W M K A r ≤ ε * r := hWe.trans (mul_le_mul_of_nonneg_left hre hεpos.le)
  have hmarg : 12 * Real.sqrt m * R₂ ≤ (1 - θ') * r ^ e := by
    have h5 : 12 * Real.sqrt m * (ε₁ + 1) ≤ (1 - θ') / 2 * r ^ e := by
      have h6 : 24 * Real.sqrt m * (ε₁ + 1) / (1 - θ') ≤ Real.sqrt r := by
        rw [Real.le_sqrt (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsm) hE0) hk.le)
          hr0.le]
        exact hr24
      have h7 : Real.sqrt r ≤ r ^ e := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hr1 (by rw [he]; linarith only [hδ])
      have h8 := (div_le_iff₀ hk).mp (h6.trans h7)
      linarith only [h8]
    exact tree_margin hsm hθ'1 hre0 hε hWe h5 hR₂le
  obtain ⟨hJ, hrJ, h2J⟩ := generation_facts (by linarith only [hL₁1]) hrL
  generalize Nat.log 2 ⌊r / L₁⌋₊ = J at hJ hrJ h2J
  -- the final steps
  have hsg1 : |sg| ≤ 1 := by rcases hsg with rfl | rfl <;> norm_num
  have hfinal : ∀ u ∈ shearBox p c t R₁ R₂,
      ‖point u - point (chainPoint p c t R₁ R₂ r sg a J u)‖ ≤ Lf₀ := by
    intro u hu
    rw [hLf₀]
    exact (norm_sub_chainPoint_le hR₁pos hR₂pos hr0.le hsg1 ha J hu).trans
      (tree_final_numeric (one_le_pow₀ (by norm_num)) hR₁r hrJ (norm_nonneg _) hV hL₁1 hsm
        hεpos.le hE0 hR₂le hWr)
  -- the sheared box is nonempty
  have hU : (shearBox p c t R₁ R₂).Nonempty := by
    refine ⟨(p, fun k => round (c k)), mem_shearBox.mpr ⟨?_, fun k => ?_⟩⟩
    · simp [shearTau, hR₁pos]
    · have h := abs_sub_round (c k)
      have hR₂' : 1 / 2 < R₂ := by
        rw [hR₂]; linarith only [ha₀, hρt0]
      simp only [shearW, shearTau, sub_self, zero_smul, sub_zero, PiLp.sub_apply,
        Infra.FPP.transversePoint_apply]
      rw [abs_sub_comm]
      linarith only [h, hR₂']
  -- the chain
  obtain ⟨X, hX, hXb⟩ := exists_chain_premise hM hT h24 hCS hr₁ hθ₀ hw hhi.le
    (fun z => (hμ z).2) hK2 hA hPrem hsg ha hP ht1 htr hθ'0 hθ'1 hslope hR₁pos hR₂pos hr0 hR₁r
    hrN hmarg hL₁ hJ hfinal hU
  refine ⟨X, ?_, fun ω u hu => hXb ω u ?_⟩
  · refine hX.mono_scale zero_le_one ?_ ?_
    · have hA0 : (0 : ℝ) < A := by linarith only [hA]
      have hQ := Q_pos M K hA0 hr0
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcardpos : (1 : ℝ) ≤ (shearBox p c t R₁ R₂).card := by exact_mod_cast hU.card_pos
      have hm1 : (0 : ℝ) < 1 + Real.log (2 * (shearBox p c t R₁ R₂).card) := by
        have := Real.log_nonneg (by linarith only [hcardpos] : (1 : ℝ) ≤ 2 * _)
        linarith only [this]
      have hθfpos : 0 < θ₀ * (((m : ℝ) + 1) * Lf₀ + 1) + 2 * (hi * Lf₀) :=
        add_pos_of_pos_of_nonneg (mul_pos hθ₀ (add_pos_of_nonneg_of_pos
          (mul_nonneg (Nat.cast_add_one_pos m).le hLf₀0) one_pos))
          (mul_nonneg zero_le_two (mul_nonneg hhi.le hLf₀0))
      have hsum0 : 0 ≤ ∑ j ∈ Finset.range J, Real.log (2 * (linkCard m j : ℝ)) / Real.log 2 *
          Q M K A (r / 2 ^ j) := by
        refine Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (Real.log_nonneg ?_)
          hlog2.le) (Q_pos M K hA0 (div_pos hr0 (pow_pos two_pos j))).le
        have : (1 : ℝ) ≤ linkCard m j := by
          unfold linkCard; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
        linarith only [this]
      have hcost0 : 0 ≤ ∑ j ∈ Finset.range J, linkCostBound M T₀ CS R₂ r t j :=
        Finset.sum_nonneg fun j _ => tree_linkCostBound_nonneg M T₀ hCS.le hr0.le t j
      have hlogc : 0 < Real.log (2 * (shearBox p c t R₁ R₂).card) / Real.log 2 :=
        div_pos (Real.log_pos (by linarith only [hcardpos])) hlog2
      have := mul_pos hlogc hθfpos
      linarith only [hsum0, hcost0, this]
    · -- the scale
      have he4 : (1 : ℝ) / 4 ≤ 1 / 2 - M.δ / K := by
        have : M.δ / K ≤ 1 / 4 := by
          rw [div_le_iff₀ (by linarith only [hKr])]; linarith only [hδ1, hKr]
        linarith only [this]
      have hcard : ((shearBox p c t R₁ R₂).card : ℝ) ≤ (C₁ * r) ^ (m + 1) := by
        refine (card_shearBox_le p c t hR₁pos.le hR₂pos.le).trans ?_
        obtain ⟨hf1, hf2⟩ := tree_card_numeric hr1 hρ1 hεpos.le hε₁1 hT₀0 hR₁ hC₁ htn hR₁pos hR₂le
          hWr
        have h0 : 0 ≤ 2 * R₁ * ‖t‖ + 2 * R₂ + 3 := by
          have := mul_nonneg (mul_nonneg zero_le_two hR₁pos.le) (norm_nonneg t)
          linarith only [this, hR₂pos]
        rw [pow_succ']
        exact mul_le_mul hf1 (pow_le_pow_left₀ h0 hf2 m) (pow_nonneg h0 m)
          (mul_nonneg hC₁pos.le hr0.le)
      have h := premise_scale_le M K (T := T₀) (t := t) hA hr1 he4 (by linarith only [hb]) hCS.le
        hθf0 hC₁pos (Finset.card_pos.mpr hU) hcard hR₂pos.le hR₂le hL₁1 h2J htt
      rw [hCb]
      exact h
  · exact thicken_subset_shearBox (by rw [hR₁]; linarith only)
      (by rw [hR₂]; linarith only) hu

/-- **Lemma `lem:tree`, equation `eq:tree`**, from equation `eq:scales` and equation `eq:support`,
for real `s`. The union bound (`Infra.Os.isOs_finset_sup'`) and the sum rule ([AKM, Lemma A.4]) are
used directly in `exists_isOs_chain`, so the premises `OsUnionStatement` and `SignedOsSumStatement`
of the implication are not used here. -/
theorem treeStatement (hScales : Contracts.ScalesStatement m)
    (hSupp : Contracts.SupportStatement m) (_hUnion : Contracts.OsUnionStatement.{0, 0})
    (_hSum : Contracts.SignedOsSumStatement.{0, 0}) : Contracts.TreeStatement m := by
  intro bd hbd Cstar b hb
  obtain ⟨r₀, ε, Cb, hε, hCb, hprem⟩ := exists_tree_premise hSupp bd hbd (θ := 4 / 5)
    (by norm_num) hb
  obtain ⟨r₂, hr₂, hcost⟩ := exists_slope_cost hScales bd hbd Cstar
  have hb0 : 0 < b := by linarith only [hb]
  obtain ⟨Nw, hNw⟩ := exists_width_margin hScales bd hbd Cstar (div_pos hε hb0)
  set S₀ := max r₀ r₂ with hS₀
  refine ⟨2 * Cb, by positivity, fun K hK => ⟨max Nw (max 2 ⌈(16 * S₀) ^ 2⌉₊), ?_⟩⟩
  intro M hM hfit N hN A hA hPrem hRange s hs1 hs2 p c t a₀ ha₀ ha₀W ht P hP a a' ha ha'
  have := hM.probP
  have hNw' : Nw ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNS : ⌈(16 * S₀) ^ 2⌉₊ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hS₀1 : 1 ≤ S₀ := hr₂.trans (le_max_right _ _)
  have hSs : S₀ ≤ s := by
    have h1 : (16 * S₀) ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNS)
    have h2 : 16 * S₀ ≤ Real.sqrt N := Real.le_sqrt_of_sq_le h1
    linarith only [h2, hs1]
  have hs1' : 1 ≤ s := hS₀1.trans hSs
  have hspos : 0 < s := by linarith only [hs1']
  have hsr₀ : r₀ ≤ s := (le_max_left _ _).trans hSs
  have hsr₂ : r₂ ≤ s := (le_max_right _ _).trans hSs
  have hse0 : 0 ≤ s ^ (M.δ / 100 - 1 / 4) := Real.rpow_nonneg hspos.le _
  have hQ : 0 < Q M K A s := Q_pos M K (by linarith only [hA]) hspos
  have hW : b * W M K A s ≤ ε * s ^ ((3 : ℝ) / 4 + M.δ / 100) := by
    have h := hNw K hK M hM hfit N hNw' A hA hRange s hs1
    calc b * W M K A s ≤ b * (ε / b * s ^ ((3 : ℝ) / 4 + M.δ / 100)) :=
          mul_le_mul_of_nonneg_left h hb0.le
      _ = ε * s ^ ((3 : ℝ) / 4 + M.δ / 100) := by field_simp
  have htt : s * ‖t - M.t₀‖ ^ (2 + M.δ) ≤ Q M K A s :=
    hcost K hK M hM hfit N hN2 A hA hRange s hs1 hsr₂ t (by linarith only [ht, hse0])
  have key : ∀ sg : ℝ, (sg = 1 ∨ sg = -1) → ∀ x : Vertex m,
      ‖point x - (WithLp.toLp 2 ((p : ℝ), c) + (sg * s) • slopeVec t)‖ ≤
        Real.sqrt ((m : ℝ) + 1) →
      ∃ X : Config m → ℝ, CurvatureVariance.IsOs M.P 1 (Cb * Q M K A s) X ∧
        ∀ ω, ∀ u ∈ thicken (transverseCube p c a₀) t (s / 64),
          passageTimeReal ω x u - inner ℝ ((-sg) • P) (point u - point x) ≤ X ω :=
    fun sg hsg x hx => hprem M hM hfit K hK A hA N hPrem s hsr₀ hs2 hW p c t a₀ ha₀ ha₀W ht htt
      P hP sg hsg x hx
  obtain ⟨X₁, hX₁, hb₁⟩ := key (-1) (Or.inr rfl) a (by
    rw [show ((-1 : ℝ) * s) • slopeVec t = -(s • slopeVec t) by rw [neg_one_mul, neg_smul],
      ← sub_eq_add_neg]
    exact ha)
  obtain ⟨X₂, hX₂, hb₂⟩ := key 1 (Or.inl rfl) a' (by rw [one_mul]; exact ha')
  refine ⟨fun ω => max (X₁ ω) 0 + max (X₂ ω) 0, ?_, Eventually.of_forall fun ω u hu => ⟨?_, ?_⟩⟩
  · have h := isOs_add (Parent.isOs_max_zero hX₁) (Parent.isOs_max_zero hX₂) (by positivity)
      (by positivity)
    convert h using 2
    ring
  · have h := hb₁ ω u hu
    rw [neg_neg, one_smul] at h
    linarith only [h, le_max_left (X₁ ω) 0, le_max_right (X₂ ω) 0]
  · have h := hb₂ ω u hu
    rw [passageTimeReal_symm, show (-(1 : ℝ)) • P = -P from neg_one_smul ℝ P, inner_neg_left,
      ← inner_neg_right, neg_sub] at h
    linarith only [h, le_max_right (X₁ ω) 0, le_max_left (X₂ ω) 0]

end CurvatureVariance.Paper.Moments
