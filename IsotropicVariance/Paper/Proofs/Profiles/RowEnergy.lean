/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Proofs.Profiles.RowEnergySetup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import IsotropicVariance.Paper.Proofs.SmallMean.ChainGeometry

/-!
# Equation `eq:rowenergy`: the bound on the slab minimum and its indices

The proof of Lemma `lem:rowenergy`. With the cubes `I_i(j)` of equation `eq:cubes`,
the curvature bound `|v − u| ≥ s + Q_s|k − j|²/6 − m Q_s/3` (`dist_gridCube_ge`, `W_s² = s Q_s`)
and the profile bound (equation `eq:profiles`) for the slab passage times `D_i` give, for every
sequence `k₀ = 0, k₁, …, k_M` with `W_s |k_i − k_{i−1}| ≤ s/2`,
`s + Q_s |Δk_i|²/6 − inf_{I_{i−1}(k_{i−1}) × I_i(k_i)} D_i ≤ m Q_s/3 + Z_i(k_{i−1}, k_i)` with
`Z_i ≤ O_1(θ)` independent over `i`. Keeping half of the penalty, the exponential union bound
over these sequences (`isOs_sup_penalized`) bounds the supremum, and the lexicographically least
minimizer of equation `eq:F` has indices `J_i` forming such a sequence; the points `i s e₁` give
the upper bound on `F`. Combining,
`|F − Ms| + Q_s Σ|J_i − J_{i−1}|² ≤ C M Q_s + O_1(C Q_s)`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace IsotropicVariance.Paper.Proofs.Profiles

open Cited Infra.Os Infra.Slab

variable {m : ℕ}

/-- The arithmetic of the end of the proof of Lemma `lem:rowenergy`: from the lower bound on `F`
along the indices `J`, the bound of the penalized supremum `Ψ = U + θ M L`, and the upper bound `F
− Ms ≤ Ψ₀ = U₀ + θ M L`. -/
lemma row_combine {a Q Sig M θ L φJ U U₀ mQ : ℝ} (hQ : 0 ≤ Q) (hSig : 0 ≤ Sig)
    (hθL : 0 ≤ θ * M * L)
    (hlow : -a + Q / 6 * Sig - mQ ≤ φJ) (hJ : φJ - Q / 12 * Sig ≤ U + θ * M * L)
    (hup : a ≤ U₀ + θ * M * L) :
    |a| + Q * Sig - (25 * (θ * M * L) + 12 * mQ) ≤ 13 * max U₀ 0 + 12 * max U 0 := by
  have hB : -a + Q / 12 * Sig ≤ mQ + U + θ * M * L := by linarith
  have hU := le_max_left U 0
  have hU0 := le_max_right U 0
  have hU₀ := le_max_left U₀ 0
  have hU₀0 := le_max_right U₀ 0
  have hQS : 0 ≤ Q * Sig := mul_nonneg hQ hSig
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    nlinarith
  · rw [abs_of_neg ha]
    nlinarith

open scoped Classical in
/-- The summand of the proof of Lemma `lem:rowenergy`: the profile functional of the pair `(I_i(j),
I_{i+1}(k))` if `W|k − j| ≤ s/2`, zero otherwise. -/
noncomputable def rowPhi (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) (f : Pt m × Pt m → ℝ) : ℝ :=
  if W * zNorm (k - j) ≤ s / 2 then profileFun (gridPair s W i j k) f else 0

lemma measurable_rowPhi (s W : ℝ) (i : ℕ) (j k : Fin m → ℤ) :
    Measurable (rowPhi (m := m) s W i j k) := by
  unfold rowPhi
  split_ifs
  · exact measurable_profileFun _
  · exact measurable_const

lemma rowPhi_of_le {s W : ℝ} {i : ℕ} {j k : Fin m → ℤ} (h : W * zNorm (k - j) ≤ s / 2)
    (f : Pt m × Pt m → ℝ) : rowPhi s W i j k f = profileFun (gridPair s W i j k) f := by
  simp [rowPhi, h]

/-- On the event where the version `f` is the slab passage time `D_i`, the profile
functional bounds `|D_i(u, v) − |v − u||` on `I_i(j) × I_{i+1}(k)`. -/
lemma abs_slabTime_sub_le_rowPhi (X : Setting m) (b : ℝ) {s W : ℝ} (hs : 0 ≤ s) (hW : 0 ≤ W)
    {i : ℕ} {j k : Fin m → ℤ} (h : W * zNorm (k - j) ≤ s / 2) {f : Pt m × Pt m → ℝ}
    (hf : Continuous f) (ω : X.Ω)
    (hev : ∀ u ∈ (chainSlab s 0 i).set, ∀ v ∈ (chainSlab s 0 i).set,
      f (u, v) = X.slabTime b (chainSlab s 0 i) ω u v)
    {u v : Pt m} (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k) :
    |X.slabTime b (chainSlab s 0 i) ω u v - dist u v| ≤ rowPhi s W i j k f := by
  rw [rowPhi_of_le h, ← hev u (SmallMean.gridCube_subset_set hs W i j hu) v
    (SmallMean.gridCube_succ_subset_set hs W i k hv)]
  exact le_profileFun _ hW hW hf (gridCube_subset_first s W hW i j k hu)
    (gridCube_subset_second s W hW i j k hv)

lemma sum_row_lower {M : ℕ} (s Q c : ℝ) (z φ D : Fin M → ℝ)
    (h : ∀ i, s + Q / 6 * z i - c * Q - φ i ≤ D i) :
    M * s + Q / 6 * ∑ i, z i - c * M * Q - ∑ i, φ i ≤ ∑ i, D i := by
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  have hL : ∑ i, (s + Q / 6 * z i - c * Q - φ i) =
      M * s + Q / 6 * ∑ i, z i - c * M * Q - ∑ i, φ i := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  linarith

lemma sum_row_upper {M : ℕ} (s : ℝ) (φ D : Fin M → ℝ) (h : ∀ i, D i ≤ s + φ i) :
    ∑ i, D i ≤ M * s + ∑ i, φ i := by
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  exact hsum

/-- One term of the lower bound: `D_i(u, v) ≥ s + Q|k − j|²/6 − mQ/3 − φ_i(j, k)`. -/
lemma slabTime_ge_row (X : Setting m) (b : ℝ) {s W Q : ℝ} (hs : 0 < s) (hW : 0 ≤ W)
    (hWm : 4 * Real.sqrt m * W ≤ s) (hWQ : W ^ 2 = s * Q)
    {i : ℕ} {j k : Fin m → ℤ} (h : W * zNorm (k - j) ≤ s / 2) {f : Pt m × Pt m → ℝ}
    (hf : Continuous f) (ω : X.Ω)
    (hev : ∀ u ∈ (chainSlab s 0 i).set, ∀ v ∈ (chainSlab s 0 i).set,
      f (u, v) = X.slabTime b (chainSlab s 0 i) ω u v)
    {u v : Pt m} (hu : u ∈ gridCube s W 0 i j) (hv : v ∈ gridCube s W 0 (i + 1) k) :
    s + Q / 6 * zNorm (k - j) ^ 2 - m / 3 * Q - rowPhi s W i j k f ≤
      X.slabTime b (chainSlab s 0 i) ω u v := by
  have h1 := abs_slabTime_sub_le_rowPhi X b hs.le hW h hf ω hev hu hv
  have h2 := dist_gridCube_ge hs hW hWm h hu hv
  have h3 : W ^ 2 * (zNorm (k - j) ^ 2 / 2 - m) / (3 * s) =
      Q / 6 * zNorm (k - j) ^ 2 - m / 3 * Q := by
    rw [hWQ]; field_simp; ring
  rw [h3] at h2
  linarith [neg_abs_le (X.slabTime b (chainSlab s 0 i) ω u v - dist u v)]

/-- **The lower bound on `F` along the indices `J`**. -/
lemma row_lower (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ} {s W Q : ℝ}
    (hs : 0 < s) (hW : 0 < W) (hWm : 4 * Real.sqrt m * W ≤ s) (hWQ : W ^ 2 = s * Q)
    (V : Fin M → Pt m × Pt m → ℝ) (hVc : ∀ i, Continuous (V i)) (ω : X.Ω)
    (hev : ∀ i : Fin M, ∀ u ∈ (chainSlab s 0 i).set, ∀ v ∈ (chainSlab s 0 i).set,
      V i (u, v) = X.slabTime b (chainSlab s 0 i) ω u v) :
    -(X.F b M s 0 ω - M * s) + Q / 6 * (∑ i : Fin M,
        zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2) - m / 3 * M * Q ≤
      ∑ i : Fin M, rowPhi s W i (X.J b M s W 0 ω i.castSucc) (X.J b M s W 0 ω i.succ) (V i) := by
  have hmin := Paper.isLexLeastMinimizer_lexMinimizer b (X.isValidChain ω hs.le) M 0
  have hF : X.F b M s 0 ω = ∑ i : Fin M, X.slabTime b (chainSlab s 0 i) ω
      (lexMinimizer b (X.ρ ω) M s 0 i.castSucc) (lexMinimizer b (X.ρ ω) M s 0 i.succ) :=
    hmin.2.1.symm
  have hterm : ∀ i : Fin M, s + Q / 6 * zNorm (X.J b M s W 0 ω i.succ -
      X.J b M s W 0 ω i.castSucc) ^ 2 - m / 3 * Q -
      rowPhi s W i (X.J b M s W 0 ω i.castSucc) (X.J b M s W 0 ω i.succ) (V i) ≤
      X.slabTime b (chainSlab s 0 i) ω (lexMinimizer b (X.ρ ω) M s 0 i.castSucc)
        (lexMinimizer b (X.ρ ω) M s 0 i.succ) := by
    intro i
    have hu := lexMinimizer_mem_gridCube b (X.isValidChain ω hs.le) M hW 0 i.castSucc
    have hv := lexMinimizer_mem_gridCube b (X.isValidChain ω hs.le) M hW 0 i.succ
    rw [Fin.val_castSucc] at hu
    rw [Fin.val_succ] at hv
    exact slabTime_ge_row X b hs hW.le hWm hWQ (J_step X hb hs hW hWm ω i) (hVc i) ω (hev i) hu hv
  have hsum := sum_row_lower s Q (m / 3) _ _ _ hterm
  rw [← hF] at hsum
  generalize X.F b M s 0 ω = F at hsum ⊢
  linarith

/-- The straight chain `x_i = i s e₁`. -/
noncomputable def straightChain (M : ℕ) (s : ℝ) : Fin (M + 1) → Pt m :=
  fun i => (0 : Pt m) + ((i : ℝ) * s) • e₁

lemma F_le_straight (X : Setting m) (b : ℝ) {M : ℕ} {s : ℝ} (hs : 0 ≤ s) (ω : X.Ω) :
    X.F b M s 0 ω ≤ ∑ i : Fin M, X.slabTime b (chainSlab s 0 i) ω
      (straightChain M s i.castSucc) (straightChain M s i.succ) :=
  ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact slabSum_nonneg _ _ _ _ _ _⟩
    (⟨straightChain M s, isAdmissible_straight M s hs (0 : Pt m)⟩ :
      {x : Fin (M + 1) → Pt m // IsAdmissible M s 0 x})

lemma straightChain_mem {M : ℕ} {s W : ℝ} (hW : 0 ≤ W) (i : ℕ) (i' : Fin (M + 1))
    (hi : (i' : ℕ) = i) : straightChain (m := m) M s i' ∈ gridCube s W 0 i 0 := by
  refine ⟨by simp [straightChain, hi], fun k => ?_⟩
  simp [straightChain]
  exact hW

lemma dist_straightChain {M : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin M) :
    dist (straightChain (m := m) M s i.castSucc) (straightChain M s i.succ) = s := by
  rw [dist_comm, dist_eq_norm]
  simp only [straightChain, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one,
    zero_add]
  rw [← sub_smul, show ((i : ℝ) + 1) * s - i * s = s by ring, norm_smul, norm_e₁, mul_one,
    Real.norm_eq_abs, abs_of_pos hs]

/-- **The upper bound on `F` from the points `i s e₁`**. -/
lemma row_upper (X : Setting m) (b : ℝ) {M : ℕ} {s W : ℝ}
    (hs : 0 < s) (hW : 0 ≤ W)
    (V : Fin M → Pt m × Pt m → ℝ) (hVc : ∀ i, Continuous (V i)) (ω : X.Ω)
    (hev : ∀ i : Fin M, ∀ u ∈ (chainSlab s 0 i).set, ∀ v ∈ (chainSlab s 0 i).set,
      V i (u, v) = X.slabTime b (chainSlab s 0 i) ω u v) :
    X.F b M s 0 ω - M * s ≤ ∑ i : Fin M, rowPhi s W i 0 0 (V i) := by
  have h0 : W * zNorm ((0 : Fin m → ℤ) - 0) ≤ s / 2 := by
    simp [zNorm]; positivity
  have hterm : ∀ i : Fin M, X.slabTime b (chainSlab s 0 i) ω (straightChain M s i.castSucc)
      (straightChain M s i.succ) ≤ s + rowPhi s W i 0 0 (V i) := by
    intro i
    have h1 := abs_slabTime_sub_le_rowPhi X b hs.le hW h0 (hVc i) ω (hev i)
      (straightChain_mem hW i i.castSucc (by simp)) (straightChain_mem hW (i + 1) i.succ (by simp))
    rw [dist_straightChain hs] at h1
    exact le_add_of_sub_left_le ((le_abs_self _).trans h1)
  have hsum := sum_row_upper s _ _ hterm
  have hF := F_le_straight X b hs.le ω (M := M)
  generalize X.F b M s 0 ω = F at hF ⊢
  linarith

/-! ## The sequences of indices -/

open scoped Classical in
/-- The sequences `k₁, …, k_M` (with `k₀ = 0`) with coordinates in `[−L, L]` and steps
`W|k_i − k_{i−1}| ≤ s/2`. -/
noncomputable def rowSeqs (M : ℕ) (L : ℤ) (s W : ℝ) : Finset (Fin M → Fin m → ℤ) :=
  (Fintype.piFinset fun _ : Fin M => Fintype.piFinset fun _ : Fin m => Finset.Icc (-L) L).filter
    fun k => ∀ i : Fin M, W * zNorm (k i - Infra.Arrays.pathPt 0 k i) ≤ s / 2

lemma pathPt_zero_seq (M : ℕ) (n : ℕ) :
    Infra.Arrays.pathPt (0 : Fin m → ℤ) (0 : Fin M → Fin m → ℤ) n = 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [Infra.Arrays.pathPt]

lemma zero_mem_rowSeqs {M : ℕ} {L : ℤ} (hL : 0 ≤ L) {s W : ℝ} (hs : 0 ≤ s) :
    (0 : Fin M → Fin m → ℤ) ∈ rowSeqs M L s W := by
  classical
  simp only [rowSeqs, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun _ _ => ⟨by simp [hL], by simp [hL]⟩, fun i => ?_⟩
  rw [pathPt_zero_seq]
  simp [zNorm]
  positivity

/-- The indices `J_1, …, J_M` of the minimizer as a sequence. -/
noncomputable def jSeq (X : Setting m) (b : ℝ) (M : ℕ) (s W : ℝ) (ω : X.Ω) :
    Fin M → Fin m → ℤ :=
  fun i => X.J b M s W 0 ω i.succ

lemma pathPt_jSeq (X : Setting m) (b : ℝ) {M : ℕ} {s : ℝ} (hs : 0 ≤ s) (W : ℝ) (ω : X.Ω)
    (i : Fin M) :
    Infra.Arrays.pathPt 0 (jSeq X b M s W ω) i = X.J b M s W 0 ω i.castSucc := by
  obtain ⟨n, hn⟩ := i
  cases n with
  | zero =>
    simp only [Infra.Arrays.pathPt]
    rw [show (Fin.castSucc ⟨0, hn⟩ : Fin (M + 1)) = 0 from rfl, J_zero X b M hs W ω]
  | succ n =>
    simp only [Infra.Arrays.pathPt, show n < M by omega, ↓reduceDIte, jSeq]
    rfl

lemma jSeq_mem (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ} {s W : ℝ} (hs : 0 < s)
    (hW : 0 < W) (hWm : 4 * Real.sqrt m * W ≤ s) {L : ℤ} (hL : (M : ℝ) * s / (4 * W) + 1 ≤ L)
    (ω : X.Ω) : jSeq X b M s W ω ∈ rowSeqs M L s W := by
  classical
  simp only [rowSeqs, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun i l => ?_, fun i => ?_⟩
  · have h := (abs_J_le X hb hs hW ω i.succ l).trans hL
    rw [← Int.cast_abs, Int.cast_le] at h
    exact abs_le.mp h
  · rw [pathPt_jSeq X b hs.le W ω]
    exact J_step X hb hs hW hWm ω i

/-! ## The exponential moments of the summands -/

lemma gridPair_first_subset_chainSlab {s W : ℝ} (hs : 0 ≤ s) (i : ℕ) (j k : Fin m → ℤ) :
    (gridPair s W i j k).first ⊆ (chainSlab s 0 i).set := fun u hu => by
  have := cubePair_first_subset_set (gridPair s W i j k) hs hu
  rwa [gridPair_slab_set] at this

lemma gridPair_second_subset_chainSlab {s W : ℝ} (hs : 0 ≤ s) (i : ℕ) (j k : Fin m → ℤ) :
    (gridPair s W i j k).second ⊆ (chainSlab s 0 i).set := fun v hv => by
  have := cubePair_second_subset_set (gridPair s W i j k) hs hv
  rwa [gridPair_slab_set] at this

/-- The exponential moment of a summand of the proof of Lemma `lem:rowenergy`: `E exp(φ_i(j, k)/θ)
≤ 2`, from the profile bound (equation `eq:profiles`) of the pair `(I_i(j), I_{i+1}(k))` when `W|k
− j| ≤ s/2` (zero otherwise). -/
lemma rowPhi_moment (X : Setting m) (b : ℝ) {s W θ : ℝ} (hs : 0 < s) (hW : 0 ≤ W) (hθ : 0 < θ)
    {i : ℕ} {j k : Fin m → ℤ} {V : X.Ω → Pt m × Pt m → ℝ} (hVc : ∀ ω, Continuous (V ω))
    (hae : ∀ᵐ ω ∂X.P, ∀ u ∈ (chainSlab s 0 i).set, ∀ v ∈ (chainSlab s 0 i).set,
      V ω (u, v) = X.slabTime b (chainSlab s 0 i) ω u v)
    (hprof : W * zNorm (k - j) ≤ s / 2 → IsOs X.P 1 θ fun ω =>
      ⨆ (u : (gridPair s W i j k).first) (v : (gridPair s W i j k).second),
        |X.slabTime b (gridPair s W i j k).slab ω u v - dist (u : Pt m) v|) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (rowPhi s W i j k (V ω) / θ)) ∂X.P ≤ 2 := by
  by_cases h : W * zNorm (k - j) ≤ s / 2
  · have H := hprof h
    have heq : (fun ω => rowPhi s W i j k (V ω)) =ᵐ[X.P] fun ω =>
        ⨆ (u : (gridPair s W i j k).first) (v : (gridPair s W i j k).second),
          |X.slabTime b (gridPair s W i j k).slab ω u v - dist (u : Pt m) v| := by
      filter_upwards [hae] with ω hω
      rw [rowPhi_of_le h, profileFun_eq_iSup _ hW hW (hVc ω)]
      refine iSup_congr fun u => iSup_congr fun v => ?_
      rw [hω u (gridPair_first_subset_chainSlab hs.le i j k u.2) v
        (gridPair_second_subset_chainSlab hs.le i j k v.2), slabTime_gridPair]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (rowPhi s W i j k (V ω) / θ)) ∂X.P
        = ∫⁻ ω, ENNReal.ofReal (Real.exp ((⨆ (u : (gridPair s W i j k).first)
            (v : (gridPair s W i j k).second),
            |X.slabTime b (gridPair s W i j k).slab ω u v - dist (u : Pt m) v|) / θ)) ∂X.P :=
          lintegral_congr_ae (heq.mono fun ω hω => by simp only [hω])
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (⨆ (u : (gridPair s W i j k).first)
            (v : (gridPair s W i j k).second),
            |X.slabTime b (gridPair s W i j k).slab ω u v - dist (u : Pt m) v|) 0 / θ) ^
              (1 : ℝ))) ∂X.P := by
          refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          rw [Real.rpow_one]
          exact div_le_div_of_nonneg_right (le_max_left _ _) hθ.le
      _ ≤ 2 := H.2
  · simp only [rowPhi, h, ↓reduceIte, zero_div, Real.exp_zero, ENNReal.ofReal_one,
      lintegral_const, measure_univ, mul_one]
    norm_num

/-! ## The bound of equation `eq:rowenergy` -/

lemma aemeasurable_zNorm_sub_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → Fin m → ℤ} (hf : AEMeasurable f P) (hg : AEMeasurable g P) :
    AEMeasurable (fun ω => zNorm (f ω - g ω) ^ 2) P := by
  have hm : Measurable (fun p : (Fin m → ℤ) × (Fin m → ℤ) => zNorm (p.1 - p.2) ^ 2) :=
    measurable_of_countable _
  have h := hm.comp_aemeasurable (hf.prodMk hg)
  exact h

lemma aemeasurable_rowSum (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ} {s W Q : ℝ}
    (hs : 0 < s) (C : ℝ) :
    AEMeasurable (fun ω => |X.F b M s 0 ω - M * s| + Q * ∑ i : Fin M,
      zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2 - C) X.P := by
  have h1 : AEMeasurable (fun ω => |X.F b M s 0 ω - M * s|) X.P := by
    have h := (aemeasurable_F X hb hs 0 M).sub_const ((M : ℝ) * s)
    have h' := continuous_abs.measurable.comp_aemeasurable h
    exact h'
  have h2 : ∀ i : Fin M, AEMeasurable (fun ω =>
      zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2) X.P := fun i =>
    aemeasurable_zNorm_sub_sq (aemeasurable_J X hb hs 0 M W i.succ)
      (aemeasurable_J X hb hs 0 M W i.castSucc)
  have h3 : AEMeasurable (fun ω => ∑ i : Fin M,
      zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2) X.P :=
    Finset.aemeasurable_fun_sum _ fun i _ => h2 i
  have h4 := (h1.add (h3.const_mul Q)).sub_const C
  exact h4

/-- The penalized sum along a sequence `k` (the summands of the union bound). -/
noncomputable def rowPen (s W cθ : ℝ) {M : ℕ} (V : Fin M → Pt m × Pt m → ℝ)
    (k : Fin M → Fin m → ℤ) : ℝ :=
  ∑ i : Fin M, (rowPhi s W i (Infra.Arrays.pathPt 0 k i) (k i) (V i) -
    cθ * ∑ l : Fin m, ((k i l : ℝ) - (Infra.Arrays.pathPt 0 k i l : ℝ)) ^ 2)

lemma rowPen_jSeq (X : Setting m) (b : ℝ) {M : ℕ} {s : ℝ} (hs : 0 ≤ s) (W cθ : ℝ)
    (V : Fin M → Pt m × Pt m → ℝ) (ω : X.Ω) :
    rowPen s W cθ V (jSeq X b M s W ω) =
      ∑ i : Fin M, rowPhi s W i (X.J b M s W 0 ω i.castSucc) (X.J b M s W 0 ω i.succ) (V i) -
        cθ * ∑ i : Fin M, zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2 := by
  unfold rowPen
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pathPt_jSeq X b hs W ω, zNorm_sub_sq]
  rfl

lemma rowPen_zero {M : ℕ} (s W cθ : ℝ) (V : Fin M → Pt m × Pt m → ℝ) :
    rowPen s W cθ V 0 = ∑ i : Fin M, rowPhi s W i 0 0 (V i) := by
  unfold rowPen
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [pathPt_zero_seq]

/-- The pointwise inequality of the end of the proof of Lemma `lem:rowenergy`, on the event where
the versions are the slab passage times. -/
lemma row_pointwise (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ} {s W Q θ : ℝ}
    (hs : 0 < s) (hW : 0 < W) (hWm : 4 * Real.sqrt m * W ≤ s) (hWQ : W ^ 2 = s * Q)
    (hQ : 0 < Q) (hθ : 0 < θ) {c : ℝ} (hc : 0 < c) (hcθ : c * θ = Q / 12)
    (V : Fin M → Pt m × Pt m → ℝ) (hVc : ∀ i, Continuous (V i)) (ω : X.Ω)
    (hev : ∀ i : Fin M, ∀ u ∈ (chainSlab s 0 i).set, ∀ v ∈ (chainSlab s 0 i).set,
      V i (u, v) = X.slabTime b (chainSlab s 0 i) ω u v)
    {L : ℤ} (hLr : (M : ℝ) * s / (4 * W) + 1 ≤ L) (hS : (rowSeqs M L s W).Nonempty) :
    |X.F b M s 0 ω - M * s| + Q * ∑ i : Fin M,
      zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2 -
        (25 * (θ * M * penaltyLog c m) + 12 * (m / 3 * M * Q)) ≤
      13 * max (({0} : Finset (Fin M → Fin m → ℤ)).sup' (Finset.singleton_nonempty _)
        (rowPen s W (c * θ) V) - θ * M * penaltyLog c m) 0 +
      12 * max ((rowSeqs M L s W).sup' hS (rowPen s W (c * θ) V) - θ * M * penaltyLog c m) 0 := by
  have hlow := row_lower X hb hs hW hWm hWQ V hVc ω hev
  have hup := row_upper X b hs hW.le V hVc ω hev
  have hJ : rowPen s W (c * θ) V (jSeq X b M s W ω) ≤
      (rowSeqs M L s W).sup' hS (rowPen s W (c * θ) V) :=
    Finset.le_sup' _ (jSeq_mem X hb hs hW hWm hLr ω)
  rw [rowPen_jSeq X b hs.le W (c * θ) V ω] at hJ
  have h0 : ({0} : Finset (Fin M → Fin m → ℤ)).sup' (Finset.singleton_nonempty _)
      (rowPen s W (c * θ) V) = ∑ i : Fin M, rowPhi s W i 0 0 (V i) := by
    rw [Finset.sup'_singleton, rowPen_zero]
  rw [h0]
  have hθL : 0 ≤ θ * M * penaltyLog c m :=
    mul_nonneg (by positivity) (penaltyLog_pos hc m).le
  have hSig : 0 ≤ ∑ i : Fin M,
      zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  generalize X.F b M s 0 ω = F at hlow hup ⊢
  generalize (∑ i : Fin M,
      zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2) = Sig at hlow hJ hSig ⊢
  generalize (∑ i : Fin M, rowPhi s W i (X.J b M s W 0 ω i.castSucc)
      (X.J b M s W 0 ω i.succ) (V i)) = φJ at hlow hJ
  generalize (∑ i : Fin M, rowPhi s W i 0 0 (V i)) = P0 at hup ⊢
  generalize (rowSeqs M L s W).sup' hS (rowPen s W (c * θ) V) = PS at hJ ⊢
  have hcS : c * θ * Sig = Q / 12 * Sig := by rw [hcθ]
  exact row_combine (a := F - M * s) (Q := Q) (Sig := Sig) (M := M) (θ := θ)
    (L := penaltyLog c m) (φJ := φJ) (U := PS - θ * M * penaltyLog c m)
    (U₀ := P0 - θ * M * penaltyLog c m) (mQ := m / 3 * M * Q) hQ.le hSig hθL
    (by linarith) (by linarith) (by linarith)

/-- **The bound of equation `eq:rowenergy`**, given the profile bound `O_1(θ)` of equation
`eq:profiles` for the pairs `(I_i(j), I_{i+1}(k))` with `W|k − j| ≤ s/2`:
`|F − Ms| + Q Σ|J_i − J_{i−1}|² ≤ (25 θ L + 4 m Q) M + O_1(25 θ)`, `L = penaltyLog`. -/
theorem rowEnergy_bound (X : Setting m) {b : ℝ} (hb : X.IsUpperBound b) {M : ℕ} {s W Q θ : ℝ}
    (hs : 0 < s) (hW : 0 < W) (hWm : 4 * Real.sqrt m * W ≤ s) (hWQ : W ^ 2 = s * Q)
    (hQ : 0 < Q) (hθ : 0 < θ)
    (hprof : ∀ (i : ℕ) (j k : Fin m → ℤ), W * zNorm (k - j) ≤ s / 2 → IsOs X.P 1 θ fun ω =>
      ⨆ (u : (gridPair s W i j k).first) (v : (gridPair s W i j k).second),
        |X.slabTime b (gridPair s W i j k).slab ω u v - dist (u : Pt m) v|) :
    IsOs X.P 1 (13 * θ + 12 * θ) fun ω => |X.F b M s 0 ω - M * s| + Q * ∑ i : Fin M,
      zNorm (X.J b M s W 0 ω i.succ - X.J b M s W 0 ω i.castSucc) ^ 2 -
        (25 * (θ * M * penaltyLog (Q / (12 * θ)) m) + 12 * (m / 3 * M * Q)) := by
  obtain ⟨V, hVm, hVc, hind, hae⟩ := exists_iIndep_slabTime_versions X hb
    (fun i : Fin M => chainSlab s 0 i) (pairwise_disjoint_interior_chainSlab hs 0 M)
  have hVmeas : ∀ i, Measurable (V i) := fun i =>
    Measurable.of_eval fun q => (hVm i).comp (measurable_id.prodMk measurable_const)
  set c := Q / (12 * θ) with hc
  have hcpos : 0 < c := by positivity
  have hcθ : c * θ = Q / 12 := by rw [hc]; field_simp
  have hmom : ∀ (i : Fin M) (j k : Fin m → ℤ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (rowPhi s W i j k (V i ω) / θ)) ∂X.P ≤ 2 :=
    fun i j k => rowPhi_moment X b hs hW.le hθ (fun ω => hVc i ω)
      (hae.mono fun ω hω => hω i) (hprof i j k)
  set L : ℤ := ⌈(M : ℝ) * s / (4 * W)⌉ + 1 with hLdef
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ (M : ℝ) * s / (4 * W) := by positivity
    have := Int.ceil_nonneg this
    omega
  have hLr : (M : ℝ) * s / (4 * W) + 1 ≤ L := by
    rw [hLdef]; push_cast; linarith [Int.le_ceil ((M : ℝ) * s / (4 * W))]
  have HU := isOs_sup_penalized V hVmeas hind (fun i j k => rowPhi s W i j k)
    (fun i j k => measurable_rowPhi s W i j k) hθ hcpos hmom (rowSeqs M L s W)
    ⟨0, zero_mem_rowSeqs hL0 hs.le⟩
  have HU₀ := isOs_sup_penalized V hVmeas hind (fun i j k => rowPhi s W i j k)
    (fun i j k => measurable_rowPhi s W i j k) hθ hcpos hmom {0} (Finset.singleton_nonempty _)
  have H13 := (isOs_mul_iff (P := X.P) (s := 1) (a := 13) (by norm_num)).mpr (isOs_pos HU₀)
  have H12 := (isOs_mul_iff (P := X.P) (s := 1) (a := 12) (by norm_num)).mpr (isOs_pos HU)
  refine IsOs.mono (isOs_add H13 H12 (by positivity) (by positivity)) zero_le_one
    (by positivity) (aemeasurable_rowSum X hb hs _) ?_
  filter_upwards [hae] with ω hω
  exact row_pointwise X hb hs hW hWm hWQ hQ hθ hcpos hcθ (fun i => V i ω) (fun i => hVc i ω) ω
    (fun i => hω i) hLr _

end IsotropicVariance.Paper.Proofs.Profiles
