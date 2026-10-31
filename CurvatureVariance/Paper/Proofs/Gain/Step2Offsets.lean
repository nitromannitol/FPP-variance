/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Defs.Gain
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Uniform offsets and subcubes

Two elementary facts behind the bound `C(1 + |j − k| + L^{1/2})/L`, for uniform offsets, of the
probability that some index `z` with `|z − j| ≤ C(1 + |j − k| + L^{1/2})` lies outside the indices
`j_G + {⌈L^{1/2}⌉, …, L − 1 − ⌈L^{1/2}⌉}^{d−1}` of the block `G` (the event `E` of the proof of
Lemma `lem:residual`):

* **Counting offsets** (`card_offsets_bad_le`): a set `S` of fine-cube indices inside a box of
  side `s` fails to lie in the subcube index set `subIndices L o g` of every block `g` for at most
  `m (s + 2⌈√L⌉) L^{m−1}` of the `L^m` offsets `o ∈ {0, …, L − 1}^m` (`d − 1 = m`), a fraction at
  most `m (s + 2⌈√L⌉)/L`.
* **Subcube membership** (`mem_subcubeFace_of_fineIndex_mem`): a point whose fine-cube index lies
  in `subIndices L o g` lies in the subcube of the block on its hyperplane (`subcubeFace`); a point
  of the row cube `I_i(j)` of Section `sec:cubes` has its fine-cube index within one of `j` in each
  coordinate (`fineIndex_point_mem_of_mem_rowCube`).
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Gain

variable {m : ℕ}

/-- The fine-cube indices of the subcube of the block `g` with offset `o`: in each coordinate,
`L g + o + ⌈√L⌉ ≤ j < L g + o + L − ⌈√L⌉`, as in the definition of `Γ_G` before Lemma
`lem:labels`. -/
def subIndices (L : ℕ) (o g : Fin m → ℤ) : Set (Fin m → ℤ) :=
  {j | ∀ c, (L : ℤ) * g c + o c + ⌈Real.sqrt L⌉₊ ≤ j c ∧
    j c + ⌈Real.sqrt L⌉₊ < (L : ℤ) * g c + o c + L}

/-! ### One coordinate -/

open Classical in
/-- **Bad residues in one coordinate**: the residues `r ∈ {0, …, L − 1}` for which no translate
`L g + r + [q, L − q)` contains the integer interval `[lo, hi]` number at most `hi − lo + 2q`. -/
theorem card_bad_residues_le {L : ℕ} (hL : 1 ≤ L) {q lo hi : ℤ}
    (h0 : 0 ≤ hi - lo + 2 * q) :
    (({r : Fin L | ¬ ∃ g : ℤ, (L : ℤ) * g + r + q ≤ lo ∧ hi + q < (L : ℤ) * g + r + L} :
        Finset (Fin L)).card : ℤ) ≤ hi - lo + 2 * q := by
  classical
  have hL0 : (0 : ℤ) < L := by exact_mod_cast hL
  set bad : Finset (Fin L) := {r : Fin L | ¬ ∃ g : ℤ, (L : ℤ) * g + r + q ≤ lo ∧
    hi + q < (L : ℤ) * g + r + L}
  -- the residue of `lo − q − r`
  set τ : Fin L → ℤ := fun r => (lo - q - r) % L
  have hτinj : Set.InjOn τ (bad : Set (Fin L)) := by
    intro r _ r' _ h
    have hmod : (lo - q - r) % (L : ℤ) = (lo - q - r') % L := h
    have hdvd : (L : ℤ) ∣ (r' : ℤ) - r := by
      have := Int.emod_emod_of_dvd (lo - q - r) (dvd_refl (L : ℤ))
      rw [Int.emod_emod_of_dvd _ (dvd_refl _)] at this
      have h' := Int.ModEq.dvd (show (lo - q - r) ≡ (lo - q - r') [ZMOD L] from hmod)
      have : (lo - q - r') - (lo - q - r) = (r : ℤ) - r' := by ring
      rw [this] at h'
      exact (dvd_neg.mpr h').trans (by rw [neg_sub])
    have hr : (r : ℤ) < L := by exact_mod_cast r.isLt
    have hr' : (r' : ℤ) < L := by exact_mod_cast r'.isLt
    have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
    have hr0' : (0 : ℤ) ≤ r' := Int.natCast_nonneg _
    have hzero : (r' : ℤ) - r = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      have hc1 : c < 1 := by
        by_contra hge
        push Not at hge
        have : (L : ℤ) * 1 ≤ L * c := mul_le_mul_of_nonneg_left hge hL0.le
        linarith
      have hc2 : -1 < c := by
        by_contra hge
        push Not at hge
        have : (L : ℤ) * c ≤ L * (-1) := mul_le_mul_of_nonneg_left hge hL0.le
        linarith
      have : c = 0 := by omega
      rw [hc, this, mul_zero]
    exact Fin.ext (by exact_mod_cast (sub_eq_zero.1 hzero).symm)
  have hmaps : ∀ r ∈ bad, τ r ∈ Finset.Ico (L + lo - hi - 2 * q) L := by
    intro r hr
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    have hdiv := Int.mul_ediv_add_emod (lo - q - r) L
    have hτ0 : 0 ≤ τ r := Int.emod_nonneg _ hL0.ne'
    have hτL : τ r < L := Int.emod_lt_of_pos _ hL0
    rw [Finset.mem_Ico]
    refine ⟨?_, hτL⟩
    by_contra hlt
    push Not at hlt
    apply hr
    refine ⟨(lo - q - r) / L, ?_, ?_⟩
    · have : (L : ℤ) * ((lo - q - r) / L) = lo - q - r - τ r := by
        simp only [τ]; linarith
      rw [this]; linarith
    · have : (L : ℤ) * ((lo - q - r) / L) = lo - q - r - τ r := by
        simp only [τ]; linarith
      rw [this]; linarith
  have hcard := Finset.card_le_card_of_injOn τ hmaps hτinj
  rw [Int.card_Ico] at hcard
  have e : L - (L + lo - hi - 2 * q) = hi - lo + 2 * q := by ring
  rw [e] at hcard
  calc ((bad.card : ℕ) : ℤ) ≤ ((hi - lo + 2 * q).toNat : ℤ) := by exact_mod_cast hcard
    _ = hi - lo + 2 * q := Int.toNat_of_nonneg h0

/-! ### All coordinates -/

/-- If every coordinate of `S` admits a block whose subcube interval contains it, one block works
for all coordinates at once. -/
theorem exists_subset_subIndices_of_forall {L : ℕ} {o : Fin m → ℤ} {S : Set (Fin m → ℤ)}
    (h : ∀ c, ∃ g : ℤ, ∀ j ∈ S, (L : ℤ) * g + o c + ⌈Real.sqrt L⌉₊ ≤ j c ∧
      j c + ⌈Real.sqrt L⌉₊ < (L : ℤ) * g + o c + L) :
    ∃ g : Fin m → ℤ, S ⊆ subIndices L o g := by
  choose g hg using h
  exact ⟨g, fun j hj c => hg c j hj⟩

/-- The number of functions `σ : Fin m → Fin L` whose value at `c` satisfies `P` is
`#{r | P r} · L^{m−1}`. -/
theorem card_filter_apply_eq {L : ℕ} (c : Fin m) (P : Fin L → Prop) [DecidablePred P] :
    (({σ : Fin m → Fin L | P (σ c)} : Finset (Fin m → Fin L)).card) =
      ({r : Fin L | P r} : Finset (Fin L)).card * L ^ (m - 1) := by
  classical
  let e := Equiv.piSplitAt c (fun _ : Fin m => Fin L)
  have hcard : ({σ : Fin m → Fin L | P (σ c)} : Finset (Fin m → Fin L)).card =
      ((({r : Fin L | P r} : Finset (Fin L)) ×ˢ
        (Finset.univ : Finset ({j : Fin m // j ≠ c} → Fin L))).card) := by
    refine Finset.card_bij (fun σ _ => e σ) ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      simp [e, Equiv.piSplitAt, hσ]
    · intro σ _ σ' _ h
      exact e.injective h
    · intro p hp
      refine ⟨e.symm p, ?_, by simp⟩
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
        and_true] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : (e.symm p) c = p.1 := by simp [e, Equiv.piSplitAt]
      rwa [this]
  rw [hcard, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]

open Classical in
/-- **Counting bad offsets** (the proof of Lemma `lem:residual`): if every index of `S` lies in the
box `∏_c [lo_c, hi_c]` with `hi_c − lo_c ≤ s`, then `S` fails to lie in the subcube index set of
every block for at most `m (s + 2⌈√L⌉) L^{m−1}` offsets `σ ∈ {0, …, L − 1}^m`. -/
theorem card_offsets_bad_le {L : ℕ} (hL : 1 ≤ L) {S : Set (Fin m → ℤ)} {lo hi : Fin m → ℤ}
    {s : ℤ} (hS : ∀ j ∈ S, ∀ c, lo c ≤ j c ∧ j c ≤ hi c) (hlohi : ∀ c, lo c ≤ hi c)
    (hs : ∀ c, hi c - lo c ≤ s) :
    ((({σ : Fin m → Fin L | ¬ ∃ g, S ⊆ subIndices L (fun c => ((σ c : ℕ) : ℤ)) g} :
        Finset (Fin m → Fin L)).card : ℕ) : ℤ) ≤
      m * (s + 2 * ⌈Real.sqrt L⌉₊) * L ^ (m - 1) := by
  classical
  set q : ℤ := ((⌈Real.sqrt L⌉₊ : ℕ) : ℤ)
  have hq : 0 ≤ q := Int.natCast_nonneg _
  -- coordinatewise bad residues
  let badc : Fin m → Finset (Fin L) := fun c =>
    {r : Fin L | ¬ ∃ g : ℤ, (L : ℤ) * g + r + q ≤ lo c ∧ hi c + q < (L : ℤ) * g + r + L}
  have hsub : ({σ : Fin m → Fin L | ¬ ∃ g, S ⊆ subIndices L (fun c => ((σ c : ℕ) : ℤ)) g} :
      Finset (Fin m → Fin L)) ⊆
      Finset.univ.biUnion fun c => ({σ : Fin m → Fin L | σ c ∈ badc c} :
        Finset (Fin m → Fin L)) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    by_contra hall
    push Not at hall
    apply hσ
    apply exists_subset_subIndices_of_forall
    intro c
    have hc := hall c
    simp only [badc, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hc
    obtain ⟨g, h1, h2⟩ := hc
    refine ⟨g, fun j hj => ⟨?_, ?_⟩⟩
    · linarith [(hS j hj c).1]
    · linarith [(hS j hj c).2]
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_biUnion_le (s := Finset.univ) (t := fun c => ({σ : Fin m → Fin L |
    σ c ∈ badc c} : Finset (Fin m → Fin L)))
  have hterm : ∀ c, (({σ : Fin m → Fin L | σ c ∈ badc c} : Finset (Fin m → Fin L)).card : ℤ) ≤
      (s + 2 * q) * L ^ (m - 1) := by
    intro c
    rw [card_filter_apply_eq c (fun r => r ∈ badc c)]
    have hb := card_bad_residues_le hL (q := q) (lo := lo c) (hi := hi c)
      (by linarith [hlohi c])
    have hfilt : ({r : Fin L | r ∈ badc c} : Finset (Fin L)) = badc c := by
      ext r; simp
    rw [hfilt]
    push_cast
    exact mul_le_mul_of_nonneg_right (hb.trans (by linarith [hs c])) (by positivity)
  calc (({σ : Fin m → Fin L | ¬ ∃ g, S ⊆ subIndices L (fun c => ((σ c : ℕ) : ℤ)) g} :
        Finset (Fin m → Fin L)).card : ℤ)
      ≤ ∑ c : Fin m, (({σ : Fin m → Fin L | σ c ∈ badc c} : Finset (Fin m → Fin L)).card : ℤ) := by
        exact_mod_cast hcard.trans hunion
    _ ≤ ∑ _c : Fin m, (s + 2 * q) * L ^ (m - 1) := Finset.sum_le_sum fun c _ => hterm c
    _ = m * (s + 2 * q) * L ^ (m - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Subcubes -/

/-- **A point whose fine-cube index lies in the subcube index set lies in the subcube** of the
block on its hyperplane. -/
theorem mem_subcubeFace_of_fineIndex_mem {w L : ℕ} (hw : 0 < w) {t : EuclideanSpace ℝ (Fin m)}
    {o g : Fin m → ℤ} {x : Vertex m} (hx : fineIndex w t (point x) ∈ subIndices L o g) :
    x ∈ subcubeFace w L t o g x.1 := by
  refine ⟨rfl, fun k => ?_⟩
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  obtain ⟨h1, h2⟩ := hx k
  set z : ℝ := (x.2 k : ℝ) - x.1 * t k
  have hfi : fineIndex w t (point x) k = ⌊z / w⌋ := rfl
  rw [hfi] at h1 h2
  have hfl := Int.floor_le (z / w)
  have hlt := Int.lt_floor_add_one (z / w)
  have h1' : ((L : ℤ) * g k + o k + ⌈Real.sqrt L⌉₊ : ℝ) ≤ (⌊z / w⌋ : ℝ) := by exact_mod_cast h1
  have h2' : (⌊z / w⌋ : ℝ) + 1 ≤ ((L : ℤ) * g k + o k + L - ⌈Real.sqrt L⌉₊ : ℝ) := by
    have : ⌊z / w⌋ + 1 ≤ (L : ℤ) * g k + o k + L - ⌈Real.sqrt L⌉₊ := by omega
    exact_mod_cast this
  push_cast at h1' h2'
  constructor
  · have := mul_le_mul_of_nonneg_left (h1'.trans hfl) hw0.le
    rw [mul_div_cancel₀ _ hw0.ne'] at this
    linarith
  · have := mul_lt_mul_of_pos_left (hlt.trans_le h2') hw0
    rw [mul_div_cancel₀ _ hw0.ne'] at this
    linarith

/-- **Row cubes and fine cubes**: a point of the row cube `I_i(j)` of Section `sec:cubes` (`s = n`)
has its fine-cube index within one of `j` in each coordinate (`⌊ins t⌋` versus `ins t`). -/
theorem fineIndex_point_mem_of_mem_rowCube {n w : ℕ} (hw : 0 < w)
    {t : EuclideanSpace ℝ (Fin m)} {i : ℤ} {j : Fin m → ℤ} {x : Vertex m}
    (hx : x ∈ rowCube n w t i j) (k : Fin m) :
    j k - 1 ≤ fineIndex w t (point x) k ∧ fineIndex w t (point x) k ≤ j k := by
  obtain ⟨hx1, hx2⟩ := hx
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj : ⌊((x.2 k : ℝ) - ⌊(i : ℝ) * n * t k⌋) / w⌋ = j k := congrFun hx2 k
  have hfi : fineIndex w t (point x) k = ⌊((x.2 k : ℝ) - (i : ℝ) * n * t k) / w⌋ := by
    simp only [fineIndex, point, transversePoint, hx1]
    push_cast
    ring_nf
  rw [hfi, ← hj]
  set a : ℝ := (i : ℝ) * n * t k
  have ha1 := Int.floor_le a
  have ha2 := Int.lt_floor_add_one a
  constructor
  · have : ((x.2 k : ℝ) - ⌊a⌋) / w - 1 ≤ ((x.2 k : ℝ) - a) / w := by
      rw [div_sub_one hw0.ne', div_le_div_iff_of_pos_right hw0]
      linarith
    have h := Int.floor_mono this
    rw [Int.floor_sub_one] at h
    exact h
  · apply Int.floor_mono
    exact div_le_div_of_nonneg_right (by linarith) hw0.le

end CurvatureVariance.Paper.Gain
