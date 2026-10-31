/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Proofs.Gain.InfluenceDefs
import CurvatureVariance.Paper.Proofs.Responses.Slabs

/-!
# Resampling a block missed by the tubes

The deterministic part of the `L¹` influence bound of Lemma `lem:fewtranslates`: as in the proof of
[AB26, Lemma 6.4], with the cube indices of the minimizing chains, resampling `G` changes `F_v` only
if, for the old or the new weights, the cells within distance `R_i(J_{i−1}, J_i)` of the segment
`[J_{i−1}, J_i]` meet `G`.

* `slabMin_le_of_not_tubeMeets`: if the tube of slab `i + 1` of a minimizing tuple `Y` of `z` misses
  a block of that slab, then weights `z'` agreeing with `z` off the block do not increase `F`.
  The proof keeps `Y` as a competitor. The other slab distances are unchanged, because the slabs
  are edge-disjoint. In slab `i + 1`, a slab geodesic of `z` stays in the tube (the tube property
  `TubeBound`), so it avoids the block (`Gain.slabTime_le_of_disjoint_tube`).
* `targetMin_resample_eq_of_not_allTubesMeet`: if some minimizing tuple of the old weights and
  some of the new weights both have tubes missing the block, then `F` is unchanged by resampling
  the block. Apply the first result in both directions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace CurvatureVariance.Paper.Gain

open CurvatureVariance.Paper

variable {m : ℕ}

/-- If the tube of slab `i + 1` of a minimizing tuple `Y` of `z` misses the index box of a block,
then weights `z'` that agree with `z` off that block do not increase `F`. -/
theorem slabMin_le_of_not_tubeMeets {M : Model m} {Cd T : ℝ} (hT : TubeBound M Cd T) {K : ℕ}
    {A : ℝ} (hA : 1 ≤ A) {n ℓ : ℕ} (hn : 1 ≤ n) {y : Fin m → ℤ} (ht : ‖targetSlope ℓ y‖ ≤ T) {L : ℕ}
    (i : Fin K) (o g : Fin m → ℤ) {z z' : Config m}
    (hgeo : ∀ (p q : ℤ) (u v : Vertex m), slabTime z p q u v ≠ ⊤ →
      ∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic z p q γ)
    (hz' : ∀ e : Edge m,
      e.1 ∉ block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) o g → z' e = z e)
    {Y : Fin (K + 1) → Fin m → ℤ} (hY : IsMinTuple M z n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y)
    (hnot : ¬ TubeMeets M K A Cd n ℓ y L i o g z Y) :
    slabMin M z' n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) ≤
      slabMin M z n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) := by
  set w := wInt M K A n with hw
  set t := targetSlope ℓ y with htdef
  set G := block n w L t ((i : ℕ) + 1) o g with hG
  have hGsub : G ⊆ slabEdges (((i : ℕ) : ℤ) * n) ((((i : ℕ) : ℤ) + 1) * n) := by
    intro e he
    have h := he.1
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h
  refine (Responses.slabMin_le_tupleCost hY.1 z').trans ?_
  rw [← hY.2]
  unfold tupleCost
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Prod.fst_zero, zero_add]
  by_cases hk : k = i
  · rw [hk]
    set J₀ := tupleIndex n w t Y i.castSucc with hJ₀
    set J₁ := tupleIndex n w t Y i.succ with hJ₁
    set u := tuplePoint (0 : Vertex m) n Y i.castSucc with hu
    set v := tuplePoint (0 : Vertex m) n Y i.succ with hv
    have hp : ((i : ℕ) : ℤ) * n = ((((i : ℕ) + 1 : ℕ) : ℤ) - 1) * n := by push_cast; ring
    have hq : (((i : ℕ) : ℤ) + 1) * n = (((i : ℕ) + 1 : ℕ) : ℤ) * n := by push_cast; ring
    rw [hp, hq]
    by_cases hfin : slabTime z (((((i : ℕ) + 1 : ℕ) : ℤ) - 1) * n)
        ((((i : ℕ) + 1 : ℕ) : ℤ) * n) u v = ⊤
    · rw [hfin]
      exact le_top
    have hu' : u ∈ rowCube n w t ((((i : ℕ) + 1 : ℕ) : ℤ) - 1) J₀ := by
      have hi1 : ((((i : ℕ) + 1 : ℕ) : ℤ) - 1) = ((i.castSucc : ℕ) : ℤ) := by
        simp only [Fin.val_castSucc]; push_cast; ring
      rw [hi1]
      refine ⟨?_, rfl⟩
      simp only [hu, tuplePoint, Prod.fst_zero, zero_add]
    have hv' : v ∈ rowCube n w t (((i : ℕ) + 1 : ℕ) : ℤ) J₁ := by
      have hi1 : (((i : ℕ) + 1 : ℕ) : ℤ) = ((i.succ : ℕ) : ℤ) := by
        simp only [Fin.val_succ]
      rw [hi1]
      refine ⟨?_, rfl⟩
      simp only [hv, tuplePoint, Prod.fst_zero, zero_add]
    refine Gain.slabTime_le_of_disjoint_tube (T := tubeIndices J₀ J₁
      (slabRadius M K A Cd z n t ((i : ℕ) + 1) J₀ J₁)) (hgeo _ _ u v hfin)
      (fun γ hγ e he => hT K A hA z n hn t ht ((i : ℕ) + 1) (by omega) J₀ J₁ u hu' v hv' γ hγ
        e he (fineIndex (wInt M K A n) t (edgeMid e))
        (by simp [transversePoint, EuclideanSpace.norm_eq])) ?_ hz'
    exact Set.disjoint_left.2 fun j hj hjT => hnot ⟨j, hj, hjT⟩
  · have hik : (i : ℕ) ≠ (k : ℕ) := fun h => hk (Fin.ext h).symm
    have hd : Disjoint G (slabEdges (((k : ℕ) : ℤ) * n) ((((k : ℕ) : ℤ) + 1) * n)) := by
      have h := Responses.pairwise_disjoint_slabEdges (m := m) 0 n hik
      simp only [zero_add] at h
      exact h.mono_left hGsub
    refine le_of_eq (Responses.restrictedTime_congr _ _ _ fun e he => ?_)
    exact hz' e fun hGe => Set.disjoint_left.1 hd hGe he

/-- **Resampling a block changes `F` only if, for the old or the new weights, the tube of every
minimizing tuple meets the block** (the proof of Lemma `lem:fewtranslates`). -/
theorem targetMin_resample_eq_of_not_allTubesMeet {M : Model m} {Cd T : ℝ}
    (hT : TubeBound M Cd T)
    {K : ℕ} {A : ℝ} (hA : 1 ≤ A) {n ℓ : ℕ} (hn : 1 ≤ n) {y : Fin m → ℤ}
    (ht : ‖targetSlope ℓ y‖ ≤ T) {L : ℕ} (i : Fin K) (o g : Fin m → ℤ) {x x' : Config m}
    (hgeo : ∀ (p q : ℤ) (u v : Vertex m), slabTime x p q u v ≠ ⊤ →
      ∃ γ : (latticeGraph m).Walk u v, IsSlabGeodesic x p q γ)
    (hgeo' : ∀ (p q : ℤ) (u v : Vertex m),
      slabTime (resample (block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) o g) x x')
        p q u v ≠ ⊤ →
      ∃ γ : (latticeGraph m).Walk u v,
        IsSlabGeodesic (resample (block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) o g)
          x x') p q γ)
    (h1 : ¬ AllTubesMeet M K A Cd n ℓ y L i o g x)
    (h2 : ¬ AllTubesMeet M K A Cd n ℓ y L i o g
      (resample (block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) o g) x x')) :
    targetMin M (resample (block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) o g) x x')
      n K ℓ y = targetMin M x n K ℓ y := by
  classical
  set G := block n (wInt M K A n) L (targetSlope ℓ y) ((i : ℕ) + 1) o g with hG
  have hex : ∀ z : Config m, ¬ AllTubesMeet M K A Cd n ℓ y L i o g z →
      ∃ Y, IsMinTuple M z n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) Y ∧
        ¬ TubeMeets M K A Cd n ℓ y L i o g z Y := by
    intro z hz
    by_contra hc
    exact hz fun Y hY => by_contra fun hn => hc ⟨Y, hY, hn⟩
  obtain ⟨Y, hY, hY'⟩ := hex x h1
  obtain ⟨Z, hZ, hZ'⟩ := hex _ h2
  have hle1 : slabMin M (resample G x x') n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) ≤
      slabMin M x n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) :=
    slabMin_le_of_not_tubeMeets hT hA hn ht i o g hgeo
      (fun e he => by
        show (if e.1 ∈ G then x' e else x e) = x e
        split_ifs with h
        exacts [absurd h he, rfl]) hY hY'
  have hle2 : slabMin M x n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) ≤
      slabMin M (resample G x x') n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y) :=
    slabMin_le_of_not_tubeMeets hT hA hn ht i o g hgeo'
      (fun e he => by
        show x e = (if e.1 ∈ G then x' e else x e)
        split_ifs with h
        exacts [absurd h he, rfl]) hZ hZ'
  unfold targetMin
  rw [le_antisymm hle1 hle2]

end CurvatureVariance.Paper.Gain
