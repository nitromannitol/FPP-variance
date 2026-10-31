/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Paper.Defs.Geometry

/-!
# Coordinates of points of `ℝ × ℝ^m`

The longitudinal and transverse coordinates `Pt.lon` and `Pt.tr` of
`IsotropicVariance.Paper.Defs.Geometry` under the vector operations, `Pt.mk` and `e₁`: the simp
set shared by the whole library. The transverse lemmas come in a vector form and a coordinatewise
form (`…_apply`). All are `rfl` lemmas, so `dsimp` uses them too.
-/

@[expose] public section

namespace IsotropicVariance.Paper.Pt

variable {m : ℕ}

/-! ### The longitudinal coordinate -/

@[simp] theorem lon_add (x y : Pt m) : lon (x + y) = lon x + lon y := rfl

@[simp] theorem lon_sub (x y : Pt m) : lon (x - y) = lon x - lon y := rfl

@[simp] theorem lon_neg (x : Pt m) : lon (-x) = -lon x := rfl

@[simp] theorem lon_smul (c : ℝ) (x : Pt m) : lon (c • x) = c * lon x := rfl

@[simp] theorem lon_zero : lon (0 : Pt m) = 0 := rfl

@[simp] theorem lon_mk (t : ℝ) (y : EuclideanSpace ℝ (Fin m)) : lon (mk t y) = t := rfl

@[simp] theorem lon_e₁ : lon (e₁ : Pt m) = 1 := rfl

/-! ### The transverse coordinates -/

@[simp] theorem tr_add (x y : Pt m) : tr (x + y) = tr x + tr y := rfl

@[simp] theorem tr_sub (x y : Pt m) : tr (x - y) = tr x - tr y := rfl

@[simp] theorem tr_neg (x : Pt m) : tr (-x) = -tr x := rfl

@[simp] theorem tr_smul (c : ℝ) (x : Pt m) : tr (c • x) = c • tr x := rfl

@[simp] theorem tr_zero : tr (0 : Pt m) = 0 := rfl

@[simp] theorem tr_mk (t : ℝ) (y : EuclideanSpace ℝ (Fin m)) : tr (mk t y) = y := rfl

@[simp] theorem tr_e₁ : tr (e₁ : Pt m) = 0 := rfl

/-! ### The transverse coordinates, coordinatewise -/

@[simp] theorem tr_add_apply (x y : Pt m) (k : Fin m) : tr (x + y) k = tr x k + tr y k := rfl

@[simp] theorem tr_sub_apply (x y : Pt m) (k : Fin m) : tr (x - y) k = tr x k - tr y k := rfl

@[simp] theorem tr_neg_apply (x : Pt m) (k : Fin m) : tr (-x) k = -tr x k := rfl

@[simp] theorem tr_smul_apply (c : ℝ) (x : Pt m) (k : Fin m) : tr (c • x) k = c * tr x k := rfl

@[simp] theorem tr_zero_apply (k : Fin m) : tr (0 : Pt m) k = 0 := rfl

@[simp] theorem tr_e₁_apply (k : Fin m) : tr (e₁ : Pt m) k = 0 := rfl

end IsotropicVariance.Paper.Pt
