/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import CurvatureVariance.Paper.Contracts.Responses
import CurvatureVariance.Infra.FPP.Walks
import Mathlib.Tactic.Linarith

/-!
# Locality and positive responses of the minimum of Section `sec:gain`

The deterministic minimum comparison behind equation `eq:blocksum`
(`Σ_G (F^G − F)₊² ≤ Q_n² Σ_i Y_i(x_{i−1}, x_i)`), for the restricted slab distances and the
admissible tuples of Section `sec:gain`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace CurvatureVariance.Paper.Responses

variable {m : ℕ}

/-- A restricted passage time reads only weights in its allowed edge set. -/
theorem restrictedTime_congr (E : Set (Sym2 (Vertex m))) (u v : Vertex m)
    {ω ω' : Config m} (h : ∀ e : Edge m, e.1 ∈ E → ω e = ω' e) :
    restrictedTime ω E u v = restrictedTime ω' E u v := by
  unfold restrictedTime
  congr 1
  funext γ
  congr 1
  funext hγ
  exact congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞))
    (Infra.FPP.walkCost_congr ω γ fun e he => h e (hγ e he))

/-- The infimum defining a restricted distance is measurable. -/
theorem measurable_restrictedTime (E : Set (Sym2 (Vertex m))) (u v : Vertex m) :
    Measurable fun ω : Config m => restrictedTime ω E u v := by
  unfold restrictedTime
  exact Measurable.iInf fun γ => Measurable.iInf fun _ =>
    (Infra.FPP.measurable_walkCost γ).coe_nnreal_ennreal

/-- The cost of any fixed tuple is measurable. -/
theorem measurable_tupleCost (u : Vertex m) (n : ℕ) {K : ℕ}
    (Y : Fin (K + 1) → Fin m → ℤ) : Measurable fun ω => tupleCost ω u n Y := by
  unfold tupleCost slabTime
  exact Finset.measurable_sum _ fun _ _ => measurable_restrictedTime _ _ _

/-- The countable infimum over tuples is measurable, including when it is infinite. -/
theorem measurable_slabMin (M : Model m) (n K : ℕ) (t : EuclideanSpace ℝ (Fin m))
    (u v : Vertex m) : Measurable fun ω => slabMin M ω n K t u v := by
  unfold slabMin
  exact Measurable.iInf fun Y => Measurable.iInf fun _ => measurable_tupleCost u n Y

/-- The real minimum used in the Efron–Stein terms is measurable. -/
theorem measurable_targetMin (M : Model m) (n K ℓ : ℕ) (y : Fin m → ℤ) :
    Measurable fun ω => targetMin M ω n K ℓ y :=
  (measurable_slabMin M n K (targetSlope ℓ y) 0 ((ℓ : ℤ), y)).ennreal_toReal

/-- A competing tuple bounds the constrained minimum. -/
theorem slabMin_le_tupleCost {M : Model m} {n K : ℕ} {t : EuclideanSpace ℝ (Fin m)}
    {u v : Vertex m} {Y : Fin (K + 1) → Fin m → ℤ}
    (hY : IsAdmissibleTuple M n K t u v Y) (ω : Config m) :
    slabMin M ω n K t u v ≤ tupleCost ω u n Y := iInf₂_le Y hY

/-- Positive response of the minimum: the old minimizing tuple is still a competitor after
replacement. Finiteness is needed when taking real parts of extended distances. -/
theorem slabMin_sub_le_slabTime_sub {M : Model m} {n K : ℕ}
    {t : EuclideanSpace ℝ (Fin m)} {u v : Vertex m} {ω ω' : Config m}
    {Y : Fin (K + 1) → Fin m → ℤ} (hY : IsMinTuple M ω n K t u v Y)
    (hfin : ∀ j : Fin K, slabTime ω' (u.1 + (j : ℤ) * n)
      (u.1 + ((j : ℤ) + 1) * n) (tuplePoint u n Y j.castSucc)
      (tuplePoint u n Y j.succ) ≠ ⊤)
    (hfinOld : ∀ j : Fin K, slabTime ω (u.1 + (j : ℤ) * n)
      (u.1 + ((j : ℤ) + 1) * n) (tuplePoint u n Y j.castSucc)
      (tuplePoint u n Y j.succ) ≠ ⊤)
    (i : Fin K)
    (heq : ∀ j : Fin K, j ≠ i →
      slabTime ω' (u.1 + (j : ℤ) * n) (u.1 + ((j : ℤ) + 1) * n)
        (tuplePoint u n Y j.castSucc) (tuplePoint u n Y j.succ) =
      slabTime ω (u.1 + (j : ℤ) * n) (u.1 + ((j : ℤ) + 1) * n)
        (tuplePoint u n Y j.castSucc) (tuplePoint u n Y j.succ)) :
    (slabMin M ω' n K t u v).toReal - (slabMin M ω n K t u v).toReal ≤
      slabTimeReal ω' (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
        (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ) -
      slabTimeReal ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
        (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ) := by
  have hnew : (slabMin M ω' n K t u v).toReal ≤ (tupleCost ω' u n Y).toReal :=
    ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun j _ => hfin j)
      (slabMin_le_tupleCost hY.1 ω')
  rw [← hY.2]
  have hdiff : (tupleCost ω' u n Y).toReal - (tupleCost ω u n Y).toReal =
      slabTimeReal ω' (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
        (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ) -
      slabTimeReal ω (u.1 + (i : ℤ) * n) (u.1 + ((i : ℤ) + 1) * n)
        (tuplePoint u n Y i.castSucc) (tuplePoint u n Y i.succ) := by
    unfold tupleCost slabTimeReal
    rw [ENNReal.toReal_sum fun j _ => hfin j,
      ENNReal.toReal_sum fun j _ => hfinOld j, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_single i (fun j _ hj => by rw [heq j hj, sub_self])
      (fun h => False.elim (h (Finset.mem_univ i)))
  linarith only [hnew, hdiff]

end CurvatureVariance.Paper.Responses
