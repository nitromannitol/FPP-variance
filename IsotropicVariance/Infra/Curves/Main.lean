/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import IsotropicVariance.Infra.Curves.Bounds
public import IsotropicVariance.Infra.Curves.Concat
public import IsotropicVariance.Infra.Curves.ContinuousMap
public import IsotropicVariance.Infra.Curves.LipschitzReparam

/-!
# Rectifiable curve costs and the Lipschitz working form

`RectifiableCurve` is a continuous BV curve on the unit parameter interval, with `length`
given by metric variation and `cost` by the Stieltjes arc-length measure. Its reparametrization,
subarc and concatenation operations preserve the literal costs. In finite-dimensional real
normed spaces, `cost_eq_lintegral_speed` identifies this cost with the derivative formula on
Lipschitz curves, and `iInf_cost_rectifiable_eq_derivative` bridges the two infima.
-/
