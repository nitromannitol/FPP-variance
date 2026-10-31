# Fluctuation bounds for first-passage percolation, formalized in Lean 4

A machine-checked **Lean 4** formalization of the main results of two papers:

> Scott Armstrong and Ahmed Bou-Rabee,
> *Curvature and variance in lattice first-passage percolation* (2026),
> formalized in the library `CurvatureVariance`;
>
> Scott Armstrong and Ahmed Bou-Rabee,
> *Fluctuation bounds for rotationally invariant first-passage percolation* (2026),
> formalized in the library `IsotropicVariance`.

This is the release of October 31, 2026. Both papers are included under [`papers/`](papers/):
[papers/CurvatureVariance.pdf](papers/CurvatureVariance.pdf) and
[papers/IsotropicVariance.pdf](papers/IsotropicVariance.pdf).

In first-passage percolation, the passage time between two points is the least total weight of a
path joining them, for random weights. Kesten asked for a bound of order $n^{1-\varepsilon}$ on its
variance over a distance $n$ [Kes93, Remark 1], and bounds of order $n/\log n$ were long the best
known. Basu, Sidoravicius and Sly [BSS26] broke this barrier for rotationally invariant
first-passage percolation, building on [BSS23]. The first paper concerns first-passage percolation
on $\mathbb Z^d$, in every dimension, with independent weights that have an exponential moment and
vanish with probability less than the critical probability of bond percolation. Let $\xi$ be a
direction, rational or irrational, in which the time constant $\mu$ has a positive definite
quadratic expansion with a power remainder on the hyperplane orthogonal to $\xi$. The paper proves
that the passage time $T(0,x)$ has an exponential moment on the scale
$\vert x\vert^{(1-\varepsilon)/2}$ around $\mu(x)$ for every lattice point $x$ within distance
$\vert x\vert^{3/4}$ of the ray through $\xi$, so that its variance is at most a constant times
$\vert x\vert^{1-\varepsilon}$; the exponent and the constant depend only on the dimension, the
law of the weights and the constants of the expansion, not on the direction. The second paper
concerns random metrics on $\mathbb R^d$, in every dimension, whose density is a bounded local
function of white noise or of a Poisson process and is equivariant under rotations and
translations. It proves that the passage time $T(0,x)$ has an exponential moment on the scale
$\vert x\vert^{(1-\varepsilon)/2}$ around $\mu\vert x\vert$, where $\mu$ is the time constant,
so that its variance is at most a constant times $\vert x\vert^{1-\varepsilon}$. Both papers
modify the induction on scales of [BSS23] and [BSS26], which compares passage times with sums of
independent passage times across slabs, and the first paper states the lattice versions of the
results of the second and explains how their proofs change. Neither paper uses a result of [BSS23]
or [BSS26] as an input.

The formalization is written in Lean 4 on top of Mathlib. It contains the main theorem of the first
paper and the two main theorems of the second, with exactly the papers' hypotheses, and every result
of the literature that their proofs use, each stated as the papers use it and proved here. The
libraries also prove the variance bounds that follow from the main theorems: for the first paper,
the bound stated after its Theorem 1.1, and the bound
$\mathrm{Var}~T(0,\lfloor n\xi\rfloor)\le n^{1-\varepsilon}$ uniformly in the direction; for the
second paper, the bounds at the points $te_1$ and at every point $x$ with $\vert x\vert$ large.
Every main theorem is also restated using Mathlib alone and checked by Lean's comparator
([below](#independent-statement-check)). The libraries contain no `sorry` and use no axioms beyond
Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`).

Both papers are included ([below](#the-papers)): the lattice paper in its version of October 31,
2026 (18 pages), and the continuum paper in the version submitted to arXiv on October 30, 2026
(19 pages). Statement numbers are those of these versions.

[![Build and verify](https://github.com/nitromannitol/FPP-variance/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/FPP-variance/actions/workflows/build.yml)
[![Comparators](https://github.com/nitromannitol/FPP-variance/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/nitromannitol/FPP-variance/actions/workflows/comparators.yml)

## The main results

The main results are in [CurvatureVariance/Statements/Main](CurvatureVariance/Statements/Main)
and [IsotropicVariance/Statements/Main](IsotropicVariance/Statements/Main), one theorem per file.
The blocks below are the exact Lean statements.

### Lattice first-passage percolation: Theorem 1.1

Let $d\ge2$, and give each edge $e$ between nearest neighbours of $\mathbb Z^d$ a nonnegative random
weight $\tau_e$, independently with a common law $\nu$. The passage time between
$x,y\in\mathbb Z^d$ is $T(x,y)=\inf_\pi\sum_{e\in\pi}\tau_e$, where the infimum is over the
nearest-neighbour paths $\pi$ from $x$ to $y$. Let $p_c(d)$ be the critical probability of bond
percolation on $\mathbb Z^d$.

> **Assumption (W).** The law $\nu$ is supported in $[0,\infty)$, $\nu(\lbrace0\rbrace)\lt p_c(d)$,
> and $\int e^{ax}\,\nu(dx)\lt\infty$ for some $a\gt0$.

Under (W), the time constant $\mu(x)=\lim_{n\to\infty}n^{-1}T(0,nx)$ exists almost surely for
$x\in\mathbb Z^d$ and extends to a norm on $\mathbb R^d$ [ADH, Theorems 2.1, 2.5 and 2.6].

> **Assumption (Curv).** The unit vector $\xi$ satisfies (Curv) with the constants
> $\delta\in(0,1]$, $r\gt0$, $\Lambda\ge0$ and $\lambda\gt0$ if there exist a linear function
> $\ell_H$ and a quadratic form $q_H$ on the hyperplane $H=\xi^\perp$, with
> $q_H(h)\ge\lambda\vert h\vert^2$ for every $h\in H$, such that
> $\vert\mu(\xi+h)-\mu(\xi)-\ell_H(h)-q_H(h)\vert\le\Lambda\vert h\vert^{2+\delta}$ for every
> $h\in H$ with $\vert h\vert\le r$.
>
> **Theorem 1.1.** Let $d\ge2$, and let $\nu$ satisfy (W). For all $\delta\in(0,1]$, $r\gt0$,
> $\Lambda\ge0$ and $\lambda\gt0$, there exist $\varepsilon\gt0$ and $C\lt\infty$ such that, for
> every unit vector $\xi$ satisfying (Curv) with these constants and every
> $x\in\mathbb Z^d\setminus\lbrace0\rbrace$ within distance $\vert x\vert^{3/4}$ of the ray
> $\mathbb R_+\xi$,
> $\mathbb E\bigl[\exp\bigl(\vert T(0,x)-\mu(x)\vert/(C\vert x\vert^{(1-\varepsilon)/2})\bigr)\bigr]\le2$.

As the paper notes, Theorem 1.1 implies that
$\mathrm{Var}[T(0,x)]\le2C^2\vert x\vert^{1-\varepsilon}$ for every such $x$
([below](#lattice-first-passage-percolation-variance-bounds)). The direction is arbitrary: it need
not be a coordinate direction, nor rational, and $\varepsilon$ and $C$ do not depend on it.

`CurvatureVariance.lintegral_exp_passageTime_le`, in
[LintegralExpPassageTimeLe.lean](CurvatureVariance/Statements/Main/LintegralExpPassageTimeLe.lean):

```lean
theorem lintegral_exp_passageTime_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - μ.1 (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2
```

Assumption (Curv) with the constants $\delta,r,\Lambda,\lambda$ is
`CurvatureVariance.AssumptionCWith`, in
[AssumptionCWith.lean](CurvatureVariance/Statements/Curvature/AssumptionCWith.lean), where `M` is
the paper's $\Lambda$, `c` is its $\lambda$, and $\xi^\perp$ is `(Submodule.span ℝ {ξ})ᗮ`:

```lean
def AssumptionCWith {m : ℕ} (μ : PtNorm m) (ξ : Pt m) (δ r M c : ℝ) : Prop :=
  ∃ ℓ : Module.Dual ℝ (Submodule.span ℝ {ξ})ᗮ, ∃ q : QuadraticForm ℝ (Submodule.span ℝ {ξ})ᗮ,
    (∀ h, c * ‖h‖ ^ 2 ≤ q h) ∧
      ∀ h : (Submodule.span ℝ {ξ})ᗮ, ‖h‖ ≤ r →
        |μ.1 (ξ + h) - μ.1 ξ - ℓ h - q h| ≤ M * ‖h‖ ^ (2 + δ)
```

The quantifiers are in the order of the paper: the constants first, then $\varepsilon$ and $C$, then
the direction $\xi$ and the point $x$. So $\varepsilon$ and $C$ depend only on $m$, the law and the
constants. The law $\nu$ is `F`, a probability measure on `ℝ≥0`, and `point x` is the lattice point
$x$ as a point of $\mathbb R^d$. The hypothesis on $x$ asks for a point $\beta\xi$ with $\beta\ge0$
within distance $\vert x\vert^{3/4}$ of $x$; since the ray is closed, this is the paper's condition.
As in the continuum theorems, $C\lt\infty$ is a real number `C` with `0 < C`, and the conclusion
also asserts that the passage time is almost everywhere measurable
([Reading the Lean statements](#reading-the-lean-statements)).

### Lattice first-passage percolation: variance bounds

The paper notes after Theorem 1.1 that its bound implies
$\mathrm{Var}[T(0,x)]\le2C^2\vert x\vert^{1-\varepsilon}$ for every such $x$. The library proves
this sentence as `CurvatureVariance.Paper.Closing.variance_passageTime_le`, in
[Main.lean](CurvatureVariance/Paper/Closing/Main.lean), whose conclusion is that of Theorem 1.1
together with this bound, for the same $\varepsilon$ and $C$; the variance is `evariance`, with
values in $[0,\infty]$. The floor $\lfloor n\xi\rfloor$ below is taken coordinatewise.

**Uniform in the direction.** A further corollary of Theorem 1.1 is
`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`, in
[EvariancePassageTimeFloorVertexLeUniform.lean](CurvatureVariance/Statements/Main/EvariancePassageTimeFloorVertexLeUniform.lean):
under (W), for all constants $\delta,r,\Lambda,\lambda$ as in Theorem 1.1, there exist
$\varepsilon\gt0$ and an integer $n_0$ such that
$\mathrm{Var}~T(0,\lfloor n\xi\rfloor)\le n^{1-\varepsilon}$ for every integer $n\ge n_0$ and
every unit vector $\xi$ satisfying (Curv) with these constants. It follows from the variance bound
after Theorem 1.1, since $\lfloor n\xi\rfloor$ lies within distance $\sqrt d$ of the point $n\xi$
of the ray, with a smaller $\varepsilon$ that absorbs the constant $2C^2$. If (Curv) holds with
common constants at every vector of a set of unit vectors, one exponent and one threshold serve the
whole set.

**One direction, under a hypothesis of its own.** The library also proves a statement that the
paper does not make, `CurvatureVariance.evariance_passageTime_floorVertex_le`, in
[EvariancePassageTimeFloorVertexLe.lean](CurvatureVariance/Statements/Main/EvariancePassageTimeFloorVertexLe.lean).
It is not a corollary of Theorem 1.1. For a nonzero $\xi$, not necessarily a unit vector, and a
linear hyperplane $H$ with $\mathbb R^d=\mathbb R\xi\oplus H$, not necessarily orthogonal to $\xi$,
it assumes `AssumptionCAt μ ξ H`, a linear functional and a positive definite quadratic form on $H$
that expand $\mu$ near $\xi$ with a remainder bound and constants of its own. It gives
$\varepsilon\gt0$ and $n_0$, which may depend on the direction, with
$\mathrm{Var}~T(0,\lfloor n\xi\rfloor)\le n^{1-\varepsilon}$ for $n\ge n_0$. It is proved from the
intermediate results of the proof of Theorem 1.1, applied at this one direction.

<details>
<summary>The exact Lean statements of the variance sentence, the uniform bound and the one-direction bound</summary>

```lean
theorem variance_passageTime_le {m : ℕ} (hm : 1 ≤ m)
    (F : Measure ℝ≥0) [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ x : Vertex m, x ≠ 0 →
        (∃ β : ℝ, 0 ≤ β ∧ ‖point x - β • ξ‖ ≤ ‖point x‖ ^ (3 / 4 : ℝ)) →
          AEMeasurable (fun ω => (passageTime ω 0 x : ℝ)) P ∧
            ∫⁻ ω, ENNReal.ofReal (Real.exp
                (|(passageTime ω 0 x : ℝ) - μ.1 (point x)| /
                  (C * ‖point x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2 ∧
            evariance (fun ω => (passageTime ω 0 x : ℝ)) P ≤
              ENNReal.ofReal (2 * C ^ 2 * ‖point x‖ ^ (1 - ε))
```

```lean
theorem evariance_passageTime_floorVertex_le_uniform {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (δ r M c : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ ξ : Pt m, ‖ξ‖ = 1 → AssumptionCWith μ ξ δ r M c →
      ∀ n : ℕ, n₀ ≤ n →
        evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P ≤
          ENNReal.ofReal ((n : ℝ) ^ (1 - ε))
```

```lean
theorem evariance_passageTime_floorVertex_le {m : ℕ} (hm : 1 ≤ m) (F : Measure ℝ≥0)
    [IsProbabilityMeasure F] (hW : AssumptionW m F) (P : Measure (Config m))
    [IsProbabilityMeasure P] (hP : IsIIDWeights P F) (μ : PtNorm m) (hμ : IsTimeConstant P μ)
    (ξ : Pt m) (hξ : ξ ≠ 0) (H : Submodule ℝ (Pt m)) (hH : IsCompl (Submodule.span ℝ {ξ}) H)
    (hC : AssumptionCAt μ ξ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      evariance (fun ω => (passageTime ω 0 (floorVertex ((n : ℝ) • ξ)) : ℝ)) P ≤
        ENNReal.ofReal ((n : ℝ) ^ (1 - ε))
```

</details>

### Rotationally invariant first-passage percolation: Theorem 1.1

Let $\omega$ be Gaussian white noise on $\mathbb R^d$, $d\ge2$, let $\chi$ be a smooth radial
function supported in the closed unit ball, and let $\psi$ be a continuous function with values
between two positive constants. The random density is $\rho=\psi(\chi\ast\omega)$, and the passage
time between $u,v\in\mathbb R^d$ is $T(u,v)=\inf_{\pi:u\to v}\int_\pi\rho(x)\vert dx\vert$, where
the infimum is over the rectifiable curves $\pi$ from $u$ to $v$. By subadditivity, the time
constant $\mu=\lim_{t\to\infty}t^{-1}\mathbb E[T(0,te_1)]$ exists.

> **Theorem 1.1.** For the density $\rho=\psi(\chi\ast\omega)$, there exist $\varepsilon\gt0$ and
> $C\lt\infty$ such that, for every $x\in\mathbb R^d$ with $\vert x\vert\ge1$,
> $\mathbb E\bigl[\exp\bigl(\vert T(0,x)-\mu\vert x\vert\vert/(C\vert x\vert^{(1-\varepsilon)/2})\bigr)\bigr]\le2$.

As the paper notes, Theorem 1.1 implies that
$\mathrm{Var}[T(0,x)]\le2C^2\vert x\vert^{1-\varepsilon}$ for $\vert x\vert\ge1$
([below](#rotationally-invariant-first-passage-percolation-variance-bounds)).

`IsotropicVariance.lintegral_exp_passageTime_le`, in
[LintegralExpPassageTimeLe.lean](IsotropicVariance/Statements/Main/LintegralExpPassageTimeLe.lean):

```lean
theorem lintegral_exp_passageTime_le {m : ℕ} (hm : 1 ≤ m) {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ =>
        t⁻¹ * ∫ ω, passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁) ∂P) atTop (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (convolutionDensity χ ψ (W ω)) 0 x - μ * ‖x‖| /
                (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2
```

The time constant is not a parameter of the theorem: the conclusion asserts that the limit defining
$\mu$ exists, and bounds the exponential moment with this $\mu$. The constants $\varepsilon$ and
$C$ are chosen after $\mu$ and before the point $x$, as in the paper.

### Rotationally invariant first-passage percolation: Theorem 1.2 (general densities)

> **Assumption A.** Let $d\ge2$, and let $\omega$ be Gaussian white noise or a homogeneous Poisson
> process on $\mathbb R^d$. The density $\rho(\omega,x)$ is jointly Borel measurable, and:
>
> 1. *Locality:* $\rho(\omega,x)=\rho(\omega',x)$ whenever $\omega$ and $\omega'$ agree on the
>    closed unit ball centered at $x$;
> 2. *Boundedness:* $0\lt\inf_{\omega,x}\rho(\omega,x)\le\sup_{\omega,x}\rho(\omega,x)\lt\infty$;
> 3. *Equivariance under rigid motions:* $\rho(\omega\circ g^{-1},gx)=\rho(\omega,x)$ for every
>    composition $g$ of a rotation and a translation.
>
> The passage time $T$ and the time constant $\mu$ are defined as above.
>
> **Theorem 1.2.** Under Assumption A, there exist $\varepsilon\gt0$ and $C\lt\infty$ such that,
> for every $x\in\mathbb R^d$ with $\vert x\vert\ge1$,
> $\mathbb E\bigl[\exp\bigl(\vert T(0,x)-\mu\vert x\vert\vert/(C\vert x\vert^{(1-\varepsilon)/2})\bigr)\bigr]\le2$.

Since $\psi(\chi\ast\omega)$ satisfies Assumption A also when $\omega$ is a Poisson process,
Theorem 1.2 contains Theorem 1.1. The library states Theorem 1.2 as two theorems, one for each
noise.

For white noise: `IsotropicVariance.lintegral_exp_passageTime_le_of_isWhiteNoise`, in
[LintegralExpPassageTimeLeOfIsWhiteNoise.lean](IsotropicVariance/Statements/Main/LintegralExpPassageTimeLeOfIsWhiteNoise.lean):

```lean
theorem lintegral_exp_passageTime_le_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, passageTime (ρ (W ω)) 0 (t • e₁) ∂P) atTop
        (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (ρ (W ω)) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2
```

For the Poisson process: `IsotropicVariance.lintegral_exp_passageTime_le_of_isPoissonProcess`, in
[LintegralExpPassageTimeLeOfIsPoissonProcess.lean](IsotropicVariance/Statements/Main/LintegralExpPassageTimeLeOfIsPoissonProcess.lean):

```lean
theorem lintegral_exp_passageTime_le_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ μ : ℝ, Tendsto (fun t : ℝ => t⁻¹ * ∫ ω, passageTime (ρ (η ω)) 0 (t • e₁) ∂P) atTop
        (𝓝 μ) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : Pt m, 1 ≤ ‖x‖ →
        AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 x) P ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
              (|passageTime (ρ (η ω)) 0 x - μ * ‖x‖| / (C * ‖x‖ ^ ((1 - ε) / 2)))) ∂P ≤ 2
```

### Rotationally invariant first-passage percolation: variance bounds

The paper notes after Theorem 1.1 that its bound implies
$\mathrm{Var}[T(0,x)]\le2C^2\vert x\vert^{1-\varepsilon}$ for $\vert x\vert\ge1$, and Theorem 1.2
gives the same bound under Assumption A. The library also proves these variance bounds, in the form
$\mathrm{Var}~T(0,x)\le\vert x\vert^{1-\varepsilon}$, which follows by decreasing $\varepsilon$.
Each comes in two forms: at the points $te_1$ for every $t\ge t_0$, and at every point $x$ with
$\vert x\vert\ge r_0$, with $\varepsilon$ and $r_0$ chosen before $x$. Each has the hypotheses of
the theorem in the first column of the table, and its conclusion also asserts that the passage time
is almost everywhere measurable. All six are in the namespace `IsotropicVariance`.

| Hypotheses | At the points $te_1$ | At every point $x$ |
|---|---|---|
| Theorem 1.1 | [`variance_passageTime_le`](IsotropicVariance/Statements/Main/VariancePassageTimeLe.lean) | [`variance_passageTime_le_norm`](IsotropicVariance/Statements/Main/VariancePassageTimeLeNorm.lean) |
| Theorem 1.2, white noise | [`variance_passageTime_le_of_isWhiteNoise`](IsotropicVariance/Statements/Main/VariancePassageTimeLeOfIsWhiteNoise.lean) | [`variance_passageTime_le_norm_of_isWhiteNoise`](IsotropicVariance/Statements/Main/VariancePassageTimeLeNormOfIsWhiteNoise.lean) |
| Theorem 1.2, Poisson process | [`variance_passageTime_le_of_isPoissonProcess`](IsotropicVariance/Statements/Main/VariancePassageTimeLeOfIsPoissonProcess.lean) | [`variance_passageTime_le_norm_of_isPoissonProcess`](IsotropicVariance/Statements/Main/VariancePassageTimeLeNormOfIsPoissonProcess.lean) |

<details>
<summary>The exact Lean statements of the six variance bounds</summary>

```lean
theorem variance_passageTime_le {m : ℕ} (hm : 1 ≤ m) {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε))
```

```lean
theorem variance_passageTime_le_norm {m : ℕ} (hm : 1 ≤ m) {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P) (χ : 𝓓((⊤ : Opens (Pt m)), ℝ))
    (hχ_radial : ∀ x y : Pt m, ‖x‖ = ‖y‖ → χ x = χ y)
    (hχ_support : tsupport ⇑χ ⊆ Metric.closedBall 0 1) (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    (a b : ℝ) (ha : 0 < a) (hψ_bounds : ∀ r, a ≤ ψ r ∧ ψ r ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ∧
        evariance (fun ω => passageTime (convolutionDensity χ ψ (W ω)) 0 x) P ≤
          ENNReal.ofReal (‖x‖ ^ (1 - ε))
```

```lean
theorem variance_passageTime_le_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (ρ (W ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε))
```

```lean
theorem variance_passageTime_le_norm_of_isWhiteNoise {m : ℕ} (hm : 1 ≤ m) {Ω : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → WhiteNoiseConfig (Pt m)} (hW : IsWhiteNoise W P)
    {ρ : WhiteNoiseConfig (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity WhiteNoiseConfig.AgreeOn WhiteNoiseConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (ρ (W ω)) 0 x) P ∧
        evariance (fun ω => passageTime (ρ (W ω)) 0 x) P ≤ ENNReal.ofReal (‖x‖ ^ (1 - ε))
```

```lean
theorem variance_passageTime_le_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
      AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 (t • e₁)) P ∧
        evariance (fun ω => passageTime (ρ (η ω)) 0 (t • e₁)) P ≤
          ENNReal.ofReal (t ^ (1 - ε))
```

```lean
theorem variance_passageTime_le_norm_of_isPoissonProcess {m : ℕ} (hm : 1 ≤ m) {lam : ℝ≥0}
    (hlam : 0 < lam) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {η : Ω → Measure (Pt m)} (hη : IsPoissonProcess lam η P)
    {ρ : Measure (Pt m) → Pt m → ℝ}
    (hρ : IsLocalDensity PoissonConfig.AgreeOn PoissonConfig.IsMovedBy ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r₀ : ℝ, ∀ x : Pt m, r₀ ≤ ‖x‖ →
      AEMeasurable (fun ω => passageTime (ρ (η ω)) 0 x) P ∧
        evariance (fun ω => passageTime (ρ (η ω)) 0 x) P ≤ ENNReal.ofReal (‖x‖ ^ (1 - ε))
```

</details>

### Reading the Lean statements

- **Dimension and points.** The dimension is $d=m+1$ with `1 ≤ m`. Space is `Pt m`, the product
  $\mathbb R\times\mathbb R^m$ with the Euclidean norm, and the lattice is
  `Vertex m = ℤ × (Fin m → ℤ)`; a point is a pair $(s,y)$ with $y\in\mathbb R^m$ (or
  $\mathbb Z^m$), and $e_1=(1,0)$. In the continuum theorems, `x : Pt m` is a point, `‖x‖` its
  Euclidean norm, and $te_1$ is `t • e₁`. In the lattice Theorem 1.1, `x : Vertex m` is a lattice
  point, `point x` is the same point in `Pt m`, and `‖point x‖` is its Euclidean norm $\vert x\vert$.
- **No preferred coordinate in the lattice theorems.** There the product
  $\mathbb R\times\mathbb R^m$ is only an indexing of the $d$ coordinates of $\mathbb R^d$ and
  $\mathbb Z^d$. The paper orders the coordinates so that the first component of $\xi$ has the
  largest absolute value; it makes this choice inside the proof, and the statements make none. In
  Theorem 1.1 and the uniform theorem the direction `ξ` is any unit vector of `Pt m` (`‖ξ‖ = 1`, for
  the Euclidean norm), $H=\xi^\perp$ is `(Submodule.span ℝ {ξ})ᗮ`, and the ray $\mathbb R_+\xi$
  is the set of the points `β • ξ` with `0 ≤ β`. In the one-direction theorem `ξ` is any nonzero
  point and `H` any linear hyperplane complementary to it (`IsCompl (Submodule.span ℝ {ξ}) H`, that
  is, $\mathbb R^d=\mathbb R\xi\oplus H$). In the uniform and one-direction theorems,
  `floorVertex x` is the vertex whose coordinates are the floors of the coordinates of `x`, so that
  $\lfloor n\xi\rfloor$ is `floorVertex ((n : ℝ) • ξ)`. The vector $e_1$ appears only in the
  literal statements of three cited results, [ADH, Theorems 2.1, 2.5 and 2.6], which are stated at
  $e_1$ as Auffinger, Damron and Hanson state them (see
  [the cited results](#the-cited-results-proved)).
- **The variance.** `evariance X P` is Mathlib's variance with values in $[0,\infty]$,
  $\int(X-\mathbb E X)^2dP$. A bound by the finite number `ENNReal.ofReal (n ^ (1 - ε))` therefore
  also asserts that the passage time has finite variance, and no value that Lean assigns by
  convention can make the bound hold vacuously.
- **The lattice model.** A weight configuration is `Config m`, a weight in $[0,\infty)$ on every
  edge; `F` is the common law $\nu$ of the weights, a probability measure on `ℝ≥0`, and `P` is the
  law of the configuration, under which the weights are independent with law `F`
  (`IsIIDWeights P F`). The time constant is a norm `μ` on $\mathbb R^d$ with
  $T(0,nx)/n\to\mu(x)$ almost surely for every $x\in\mathbb Z^d$ (`IsTimeConstant P μ`), and
  `μ.1 y` is its value at the point `y`. Both notions exist under (W) and determine their object
  (`exists_isIIDWeights`, `IsIIDWeights.unique`, `exists_isTimeConstant`, `IsTimeConstant.unique`),
  so the theorems are the paper's statements about the weights and their time constant.
  `AssumptionW m F` is (W): some exponential moment of `F` is finite, and $F(\lbrace0\rbrace)$ is
  smaller than $p_c(d)=\sup\lbrace p:\theta(p)=0\rbrace$, the critical probability of bond
  percolation on $\mathbb Z^d$; the support of `F` lies in $[0,\infty)$ by its type.
  `AssumptionCWith μ ξ δ r M c` is (Curv) with constants at the unit vector `ξ`: the linear function
  is a `Module.Dual ℝ` on $\xi^\perp$, the quadratic form a `QuadraticForm ℝ` on $\xi^\perp$
  bounded below by `c` (the paper's $\lambda$) times $\vert h\vert^2$, the remainder is bounded by
  `M` (the paper's $\Lambda$) times $\vert h\vert^{2+\delta}$, and $\vert h\vert$ is the
  Euclidean norm. `AssumptionCAt μ ξ H`, the hypothesis of the one-direction theorem, which the
  paper does not state, is an expansion of the same form at `ξ` and `H`, with a positive definite
  quadratic form (`QuadraticForm ℝ H` with `PosDef`) and constants of its own.
- **The noise.** The noise is defined on a standard Borel probability space $(\Omega,P)$. White
  noise is a measurable map `W` into the distributions on $\mathbb R^d$ such that, for every test
  function $\varphi$, $W(\varphi)$ is a centered Gaussian with variance $\int\varphi^2$
  (`IsWhiteNoise W P`). The Poisson process of intensity $\lambda\gt0$ is a measurable random
  locally finite counting measure whose counts of disjoint bounded Borel sets are independent
  Poisson variables with means $\lambda$ times their volumes (`IsPoissonProcess lam η P`). Both
  exist (`exists_isWhiteNoise`, `exists_isPoissonProcess`).
- **The densities.** In Theorem 1.1 of the continuum paper, `χ` is a smooth compactly supported
  function, radial by `hχ_radial` and supported in the closed unit ball by `hχ_support`;
  `convolutionDensity χ ψ ν` is the density $x\mapsto\psi(\nu(\chi(x-\cdot)))$, that is,
  $\psi(\chi\ast\nu)$. In Theorem 1.2, a density is a function `ρ` of the noise configuration and
  the point, and `IsLocalDensity agree moved ρ` is Assumption A, with the restrictions (`AgreeOn`)
  and the motions (`IsMovedBy`) of white-noise or Poisson configurations: `ρ` is jointly
  measurable, (1) its value at $x$ is determined by the restriction of the noise to the closed unit
  ball centered at $x$, (2) it lies between constants `a` and `b` with `0 < a`, and (3) it is
  equivariant under the proper rigid motions, the affine isometries whose linear part has
  determinant one (`IsProperRigidMotion`), which are the compositions of a rotation and a
  translation.
- **The passage time.** In the continuum theorems, `passageTime σ u v` is the infimum of the cost
  $\int_\pi\sigma(x)\vert dx\vert$ over the rectifiable curves from `u` to `v`, the cost being
  the integral against arc length. In the lattice theorems, `passageTime ω u v` is $T(u,v)$, a
  number in $[0,\infty)$ (`ℝ≥0`), and `(passageTime ω 0 x : ℝ)` is the same number as a real. The
  conclusions of the lattice Theorem 1.1 and of the continuum theorems also assert that the passage
  time is almost everywhere measurable, so that its expectation and its variance are those of a
  random variable.
- **The exponential moment.** In the exponential-moment theorems, Theorem 1.1 of the lattice paper
  and Theorems 1.1 and 1.2 of the continuum paper, $\mathbb E[\exp(Y)]$ is
  `∫⁻ ω, ENNReal.ofReal (Real.exp Y) ∂P`, the Lebesgue integral of a function with values in
  $[0,\infty]$: `Real.exp` is the real exponential, and `ENNReal.ofReal` maps its values into
  $[0,\infty]$. The bound by $2$ therefore also asserts that the exponential moment is finite, and
  it needs no integrability hypothesis. In the exponent, `‖x‖ ^ ((1 - ε) / 2)` is the real power
  $\vert x\vert^{(1-\varepsilon)/2}$ and `μ * ‖x‖` is $\mu\vert x\vert$; in the lattice
  theorem, `‖point x‖ ^ ((1 - ε) / 2)` is $\vert x\vert^{(1-\varepsilon)/2}$, `μ.1 (point x)` is
  $\mu(x)$, and `‖point x‖ ^ (3 / 4 : ℝ)` is $\vert x\vert^{3/4}$.
- **The time constant in the continuum theorems.** The conclusions of Theorems 1.1 and 1.2 begin
  with `∃ μ : ℝ`, followed by `Tendsto (fun t => t⁻¹ * ∫ ω, … ∂P) atTop (𝓝 μ)`: the limit
  $\mu=\lim_{t\to\infty}t^{-1}\mathbb E[T(0,te_1)]$ exists, and the bound holds with this $\mu$.
  Here `∫` is the expectation, Mathlib's Bochner integral. For $t\ge1$ the passage time is almost
  everywhere measurable, by the measurability conjunct, and lies between $0$ and $bt$, where $b$ is
  an upper bound of the density, so the integral is its expectation and not a value that Lean
  assigns by convention.
- **The constant $C$.** In the exponential-moment theorems of both papers, $C\lt\infty$ is a real
  number `C` with `0 < C`. Positivity excludes $C=0$, at which Lean's convention $y/0=0$ would make
  the exponential moment equal to $1$ and the bound true for every random variable.

## Definitions

The definitions the main theorems use, with the papers' notation. All are in
[CurvatureVariance/Statements](CurvatureVariance/Statements) and
[IsotropicVariance/Statements](IsotropicVariance/Statements).

**Lattice first-passage percolation** (namespace `CurvatureVariance`).

| Lean | Meaning |
|---|---|
| [`Vertex m`](CurvatureVariance/Statements/Lattice/Vertex.lean), [`latticeGraph m`](CurvatureVariance/Statements/Lattice/LatticeGraph.lean), [`Edge m`](CurvatureVariance/Statements/Lattice/Edge.lean) | $\mathbb Z^d=\mathbb Z\times\mathbb Z^m$, its nearest-neighbour graph and its edges |
| [`Config m`](CurvatureVariance/Statements/Lattice/Config.lean) | weight configurations: a weight in $[0,\infty)$ on every edge |
| [`walkCost ω p`](CurvatureVariance/Statements/Lattice/WalkCost.lean), [`passageTime ω u v`](CurvatureVariance/Statements/Lattice/PassageTime.lean) | the total weight of a path, and $T(u,v)$, its infimum over the paths from $u$ to $v$ |
| [`Pt m`](CurvatureVariance/Statements/Space/Pt.lean), [`PtNorm m`](CurvatureVariance/Statements/Space/PtNorm.lean), [`point x`](CurvatureVariance/Statements/Space/Point.lean), [`transversePoint y`](CurvatureVariance/Statements/Space/TransversePoint.lean), [`floorVertex x`](CurvatureVariance/Statements/Space/FloorVertex.lean), [`e₁`](CurvatureVariance/Statements/Space/EOne.lean) | $\mathbb R^d$ with the Euclidean norm, the norms on $\mathbb R^d$, a vertex as a point of $\mathbb R^d$, a vertex of $\mathbb Z^m$ as a point of $\mathbb R^m$, the coordinatewise floor $\lfloor x\rfloor\in\mathbb Z^d$ of $x\in\mathbb R^d$, and $e_1$ (used only by cited results) |
| [`openGraph m S`](CurvatureVariance/Statements/Percolation/OpenGraph.lean), [`percolationProb m p`](CurvatureVariance/Statements/Percolation/PercolationProb.lean), [`bondCriticalProb m`](CurvatureVariance/Statements/Percolation/BondCriticalProb.lean) | the graph of open edges; $\theta(p)$, the probability that the open cluster of the origin is infinite when each edge is open independently with probability $p$; and $p_c(d)=\sup\lbrace p:\theta(p)=0\rbrace$ |
| [`IsIIDWeights P F`](CurvatureVariance/Statements/Weights/IsIIDWeights.lean) | under `P`, the weights are independent, each with law `F` |
| [`AssumptionW m F`](CurvatureVariance/Statements/Weights/AssumptionW.lean) | Assumption (W) on the law $\nu$ (`F`) of the weights |
| [`IsTimeConstant P μ`](CurvatureVariance/Statements/TimeConstant/IsTimeConstant.lean) | $T(0,nx)/n\to\mu(x)$ almost surely, for every $x\in\mathbb Z^d$ |
| [`AssumptionCWith μ ξ δ r M c`](CurvatureVariance/Statements/Curvature/AssumptionCWith.lean) | Assumption (Curv) on the time constant at the unit vector `ξ`, on $\xi^\perp$, with the constants $\delta$, $r$, $\Lambda$ (`M`) and $\lambda$ (`c`) |
| [`AssumptionCAt μ ξ H`](CurvatureVariance/Statements/Curvature/AssumptionCAt.lean) | an expansion of the form of (Curv) at the direction `ξ` and the hyperplane `H`, with constants of its own; the hypothesis of the one-direction theorem, which the paper does not state |

**Rotationally invariant first-passage percolation** (namespace `IsotropicVariance`).

| Lean | Meaning |
|---|---|
| [`Pt m`](IsotropicVariance/Statements/Space/Pt.lean), [`e₁`](IsotropicVariance/Statements/Space/EOne.lean), [`IsProperRigidMotion g`](IsotropicVariance/Statements/Space/IsProperRigidMotion.lean) | $\mathbb R^d$ with the Euclidean norm, $e_1$, and the rigid motions that preserve orientation |
| [`RectifiableCurve E`](IsotropicVariance/Statements/Curves/RectifiableCurve.lean), [`RectifiableCurve.cost ρ γ`](IsotropicVariance/Statements/Curves/RectifiableCurveCost.lean), [`RectifiableCurve.arcLengthMeasure γ`](IsotropicVariance/Statements/Curves/RectifiableCurveArcLengthMeasure.lean) | continuous curves of finite length parametrized by $[0,1]$; the cost $\int_\pi\rho(x)\vert dx\vert$, against the arc-length measure (with [`length`](IsotropicVariance/Statements/Curves/RectifiableCurveLength.lean), [`cumulativeLength`](IsotropicVariance/Statements/Curves/RectifiableCurveCumulativeLength.lean) and [`lengthFunction`](IsotropicVariance/Statements/Curves/RectifiableCurveLengthFunction.lean)) |
| [`passageTime σ u v`](IsotropicVariance/Statements/Curves/PassageTime.lean) | $T(u,v)$, the infimum of the cost over the rectifiable curves from $u$ to $v$ |
| [`WhiteNoiseConfig E`](IsotropicVariance/Statements/Configurations/WhiteNoiseConfig.lean) | distributions on $E$, the configurations of white noise, with the σ-algebra generated by the evaluations at test functions |
| [`WhiteNoiseConfig.AgreeOn S`](IsotropicVariance/Statements/Configurations/WhiteNoiseConfigAgreeOn.lean), [`WhiteNoiseConfig.IsMovedBy g`](IsotropicVariance/Statements/Configurations/WhiteNoiseConfigIsMovedBy.lean) | two distributions agree on every test function supported in $S$; a distribution is the image of another under $g$ |
| [`PoissonConfig.AgreeOn S`](IsotropicVariance/Statements/Configurations/PoissonConfigAgreeOn.lean), [`PoissonConfig.IsMovedBy g`](IsotropicVariance/Statements/Configurations/PoissonConfigIsMovedBy.lean) | two measures have the same restriction to $S$; a measure is the image of another under $g$ |
| [`IsWhiteNoise W P`](IsotropicVariance/Statements/Noise/IsWhiteNoise.lean), [`IsPoissonProcess lam η P`](IsotropicVariance/Statements/Noise/IsPoissonProcess.lean) | Gaussian white noise; the homogeneous Poisson process of intensity $\lambda$ |
| [`IsLocalDensity agree moved ρ`](IsotropicVariance/Statements/Assumption/IsLocalDensity.lean) | Assumption A |
| [`convolutionDensity χ ψ ν`](IsotropicVariance/Statements/Density/ConvolutionDensity.lean), [`TestFunction.reflectTranslate χ x`](IsotropicVariance/Statements/Density/TestFunctionReflectTranslate.lean) | the density $\psi(\chi\ast\nu)$, and the test function $y\mapsto\chi(x-y)$ |

From Mathlib: `evariance`, `Measure`, `IsProbabilityMeasure`, `StandardBorelSpace`,
`AEMeasurable`, the integrals `∫` (Bochner) and `∫⁻` (Lebesgue, with values in $[0,\infty]$),
`ENNReal.ofReal`, `Real.exp`, the limit `Tendsto … atTop (𝓝 μ)`, `Submodule`, `Submodule.span`, the
orthogonal complement `ᗮ`, `IsCompl`, `Module.Dual`, `QuadraticForm` and its `PosDef`, the test
functions `𝓓(Ω, ℝ)`, and `tsupport`.

## The cited results, proved

Every result of the literature that the proofs use is stated in the form the papers use it,
in `Statements/Inputs` (lattice) and `Statements/Cited` (continuum), and proved. Statements
specialized to the papers' hypotheses say so in their documentation.

**Lattice paper** (namespace `CurvatureVariance`).

| Lean | Result |
|---|---|
| [`exists_tendsto_passageTime_div`](CurvatureVariance/Statements/Inputs/ExistsTendstoPassageTimeDiv.lean) | [ADH, Theorem 2.1] under (W): $T(0,ne_1)/n$ converges almost surely and in $L^1$ |
| [`timeConstant_pos`](CurvatureVariance/Statements/Inputs/TimeConstantPos.lean) | [ADH, Theorem 2.5] under (W): $\mu(e_1)\gt0$ |
| [`pos_iff_forall_pos_of_isLatticeSymmetric`](CurvatureVariance/Statements/Inputs/PosIffForallPosOfIsLatticeSymmetric.lean) | [ADH, Theorem 2.6]: a continuous, subadditive, homogeneous function invariant under the symmetries of $\mathbb Z^d$ is positive away from $0$ if and only if it is positive at $e_1$ |
| [`exists_isTimeConstant`](CurvatureVariance/Statements/Companions/ExistsIsTimeConstant.lean) | [ADH, Theorems 2.1, 2.5 and 2.6]: under (W) the time constant exists and extends to a norm |
| [`measure_abs_passageTime_sub_integral_le`](CurvatureVariance/Statements/Inputs/MeasureAbsPassageTimeSubIntegralLe.lean) | [ADH, Theorem 3.13] under (W): Gaussian concentration of $T(0,x)$ at scale $\Vert x\Vert_1^{1/2}$, for the first bound of (2.5) |
| [`integral_passageTime_le_timeConstant_add`](CurvatureVariance/Statements/Inputs/IntegralPassageTimeLeTimeConstantAdd.lean) | [ADH, Theorem 3.33] under (W): $\mathbb ET(0,x)\le\mu(x)+C(\vert x\vert\log\vert x\vert)^{1/2}$, the second bound of (2.5) |
| [`measure_exists_isPath_walkCost_lt_le`](CurvatureVariance/Statements/Inputs/MeasureExistsIsPathWalkCostLtLe.lean) | Kesten's bound on paths of small passage time [Kes86, Proposition 5.8], which assumes $\nu(\lbrace0\rbrace)\lt p_T(d)$, the critical probability for a finite expected cluster size; since $p_T(d)=p_c(d)$ [DCT, Theorem 1.1], it holds under (W), and it is stated in that form: long self-avoiding paths from the origin have passage time at least a constant times their number of edges, with exponentially small exceptional probability |
| [`ae_exists_isPath_walkCost_eq_passageTime`](CurvatureVariance/Statements/Inputs/AeExistsIsPathWalkCostEqPassageTime.lean) | [ADH, Proposition 4.4]: geodesics exist almost surely |
| [`measure_reachable_sphere_le`](CurvatureVariance/Statements/Inputs/MeasureReachableSphereLe.lean) | the sharpness of the phase transition of bond percolation [DCT, Theorem 1.1(1)]: below $p_c(d)$, the probability that the origin is joined by open edges to distance $n$ decays exponentially in $n$. It gives $p_T(d)=p_c(d)$, by which Kesten's bound holds under (W) |
| [`bondCriticalProb_bounds`](CurvatureVariance/Statements/Inputs/BondCriticalProbBounds.lean), [`bondCriticalProb_pos`](CurvatureVariance/Statements/Companions/BondCriticalProbPos.lean) | $1/(2d)\le p_c(d)\le1$; in particular (W) can be met |
| [`variance_mul_log_le_of_entropy_le`](CurvatureVariance/Statements/Inputs/VarianceMulLogLeOfEntropyLe.lean) | [BR, Proposition 2.1], the modified Poincaré inequality, in the instance the paper applies (through Proposition 1.3 of the continuum paper) |
| [`blm_proposition1`](CurvatureVariance/Statements/Inputs/BlmProposition1.lean) | [BLM, Proposition 1], the Efron–Stein inequality, used in the proof of Lemma 6.3, which applies the proof of Lemma 6.3 of the continuum paper |
| [`IsOs.measure_ge_le`](CurvatureVariance/Statements/Inputs/IsOsMeasureGeLe.lean), [`isOs_of_measure_ge_le`](CurvatureVariance/Statements/Inputs/IsOsOfMeasureGeLe.lean) | [AKM, Lemma A.1]: tail bounds and the $\mathcal O_s$ notation |
| [`IsOs.mul`](CurvatureVariance/Statements/Inputs/IsOsMul.lean) | [AKM, Lemma A.3(ii)]: the product rule, used in the proof of Lemma 4.4 |
| [`exists_isOs_integral`](CurvatureVariance/Statements/Inputs/ExistsIsOsIntegral.lean) | [AKM, Lemma A.4]: the sum rule, which gives (1.2) |

**Rotationally invariant first-passage percolation** (namespace `IsotropicVariance.Cited`).

| Lean | Result |
|---|---|
| [`IsOs.measure_ge_le`](IsotropicVariance/Statements/Cited/IsOsMeasureGeLe.lean), [`isOs_of_measure_ge_le`](IsotropicVariance/Statements/Cited/IsOsOfMeasureGeLe.lean) | [AKM, Lemma A.1]: tail bounds and the $\mathcal O_s$ notation ([`IsOs`](IsotropicVariance/Statements/Cited/IsOs.lean)) |
| [`isOs_integral_of_one_le`](IsotropicVariance/Statements/Cited/IsOsIntegralOfOneLe.lean) | [AKM, Lemma A.4]: the sum rule for $s\ge1$, which gives the paper's (1.7) |
| [`blm_corollary3`](IsotropicVariance/Statements/Cited/BlmCorollary3.lean), [`blm_theorem7`](IsotropicVariance/Statements/Cited/BlmTheorem7.lean) | [BLM, Corollary 3 and Theorem 7], concentration by the entropy method, the latter in the form the paper uses: the two tails of the first bound of Lemma 2.1 |
| [`hn_lemma4_2`](IsotropicVariance/Statements/Cited/HnLemma42.lean) | [HN, Lemma 4.2], a deterministic lemma that turns a doubling inequality into a rate of convergence: the second bound of Lemma 2.1 |
| [`blm_proposition1`](IsotropicVariance/Statements/Cited/BlmProposition1.lean) | [BLM, Proposition 1], the Efron–Stein inequality, used in the proof of Lemma 6.3 |
| [`variance_mul_log_le_of_entropy_le`](IsotropicVariance/Statements/Cited/VarianceMulLogLeOfEntropyLe.lean) | [BR, Proposition 2.1], the paper's Proposition 1.3, in the instance the paper applies |

## Formalization notes

[docs/FORMALIZATION-NOTES.md](docs/FORMALIZATION-NOTES.md) lists every place where a Lean statement differs in form from the printed one, and the places where the formal proofs take a different route from the printed proofs. The lattice paper included here is *Curvature and variance in lattice first-passage percolation*, in its version of October 31, 2026. The continuum paper included here is *Fluctuation bounds for rotationally invariant first-passage percolation*, in the version submitted to arXiv on October 30, 2026. No entry changes the main results: the main theorems are proved under the papers' hypotheses and use only the standard axioms. The main theorems of both papers, Theorem 1.1 of the lattice paper and Theorems 1.1 and 1.2 of the continuum paper, bound an exponential moment of $T(0,x)$. The formalization also proves the variance bounds stated after Theorem 1.1 in both papers. For the lattice paper, it also proves two variance bounds at the points $\lfloor n\xi\rfloor$ that the paper does not state: one uniform in the direction, a corollary of that variance bound (`CurvatureVariance.evariance_passageTime_floorVertex_le_uniform`), and one at a single direction under a hypothesis of its own, which is not a corollary of Theorem 1.1 (`CurvatureVariance.evariance_passageTime_floorVertex_le`). For the continuum paper, it proves, as corollaries with the same axioms, variance bounds at the points $te_1$, and the same bounds at every point $x$ with $|x|$ large enough (`IsotropicVariance.variance_passageTime_le`, `IsotropicVariance.variance_passageTime_le_norm` and their companions for the two noises).

[docs/bss-errata](docs/bss-errata) contains two checked lists of the errors and proof gaps found in the two papers of Basu, Sidoravicius and Sly, [BSS23] (73 items) and [BSS26] (78 items). They come from written review, made while trying to formalize those papers, and are not formalized in Lean. Neither list refutes a main theorem. Neither paper formalized here uses a result of [BSS23] or [BSS26] as an input.

| Source | Deviations |
|---|---:|
| Curvature and variance in lattice first-passage percolation | 19 |
| Fluctuation bounds for rotationally invariant first-passage percolation | 14 |
| **Total** | **33** |

The deviations are mostly conventions, explicit quantifiers in place of "sufficiently large", and cited results stated in the form the papers use. The deviations of cited results are counted with the paper that uses them. The main items, among the deviations and the notes:

- **Concentration in Lemma 2.1 (continuum paper).** The formal proof derives the Gaussian tails of $T_t$ from the two inequalities of Boucheron, Lugosi and Massart that the paper cites, and it also uses the deterministic bound $T_t\le(\sup\rho)t$, so that the range of the tail bound of their Theorem 7 contains every deviation.
- **Variables that depend only on their block (continuum paper, Lemmas 6.2 and 6.3).** Lemma 6.2 is formalized with variables $X_G$ that depend only on their block, as its construction gives. This is the form the proof of Lemma 6.3 uses, in which the arrays built from the variables of different slabs are independent.
- **Cited works.** Theorem 7 of Boucheron, Lugosi and Massart is stated in the case $K=1$, the case the continuum paper uses. Kesten's estimate, which the lattice paper cites from Kesten's Saint-Flour notes together with the sharpness of the percolation phase transition, is proved from the theorem of Duminil-Copin and Tassion that the paper cites, rather than assumed. The theorems of the survey on the time constant are stated as printed, in the direction $e_1$.

## Repository layout

| Path | Contents |
|---|---|
| [CurvatureVariance/Statements](CurvatureVariance/Statements) | The lattice statements: Theorem 1.1, the variance bound uniform in the direction, and the one-direction theorem, which the paper does not state (`Main`); the definitions they use; the cited results (`Inputs`); and the existence and uniqueness of the notions the main theorems use (`Companions`) |
| [IsotropicVariance/Statements](IsotropicVariance/Statements) | The statements of the continuum paper: the main theorems (`Main`), the definitions they use, the cited results (`Cited`), and the existence of the noises (`Companions`) |
| [CurvatureVariance](CurvatureVariance), [IsotropicVariance](IsotropicVariance) (other directories) | The proofs, organized by the sections of the papers, and the supporting library |
| [Audit](Audit) | The Mathlib-only comparator challenges and their solutions, one directory per main theorem |
| [docs/FORMALIZATION-NOTES.md](docs/FORMALIZATION-NOTES.md) | Formalization notes: the deviations of the Lean statements from the printed ones, and the differences of route between the formal and the printed proofs |
| [docs/bss-errata](docs/bss-errata) | Checked lists of the errors and gaps found in the two papers of Basu, Sidoravicius and Sly (written review, not formalized) |
| [papers/CurvatureVariance.pdf](papers/CurvatureVariance.pdf), [papers/IsotropicVariance.pdf](papers/IsotropicVariance.pdf) | The two papers |
| [scripts](scripts) | The source, metadata, axiom and comparator checks |

Every Lean file is a module of Lean's module system.

## Building and checking

Install [elan](https://github.com/leanprover/elan), then, from the repository root:

```sh
lake exe cache get && lake build
```

`lake exe cache get` downloads the Mathlib build cache; `lake build` builds both libraries and the
comparator challenges and solutions. The build prints one `declaration uses sorry` warning for each
theorem of the comparator challenges `Audit/*/Challenge.lean`, whose proofs are left as `sorry` by
design (see [Independent statement check](#independent-statement-check)), and no other warning.
The toolchain is `leanprover/lean4:v4.35.0-rc2` (from [lean-toolchain](lean-toolchain)), with
Mathlib `v4.35.0-rc2`, pinned by its commit in [lake-manifest.json](lake-manifest.json). The Mathlib
cache covers Mathlib only: the first build compiles both libraries from source. This takes about
1 CPU-hour in all (about 0.6 for `CurvatureVariance` and 0.5 for `IsotropicVariance`), about half an
hour of wall time with eight parallel compiles, and, by estimate, under an hour on a 4-core GitHub
runner. A single compile uses less than 2 GB of memory. Keep the committed `lake-manifest.json`, and
do not run `lake update`.

To print the axioms of the main theorems, of the cited results and of the comparator theorems, and
to check that each depends only on `propext`, `Classical.choice` and `Quot.sound`:

```sh
lake env lean scripts/Axioms.lean    # print the axioms
python3 scripts/check-axioms.py      # print and check them
```

To check the source requirements (every file a module; no `sorry`, `admit`, `axiom`, `opaque` or
`set_option` outside the comparator challenges; file sizes; the comparator configurations) and the
metadata (`CITATION.cff`, `formalization.yaml`, the license, the workflows, and the Lean blocks of
this README):

```sh
python3 scripts/check-lean-sources.py
python3 scripts/check-metadata.py
```

### Independent statement check

So that the main theorems can be checked without reading the libraries, each is restated using
only Mathlib in a file `Audit/<Name>/Challenge.lean`, which defines every notion the theorem uses
and leaves its proof as an intentional `sorry`. The Solution, `Audit/<Name>/Solution.lean`, states
the same theorems over the same definitions and proves each of them from the library. Lean's
[comparator](https://github.com/leanprover/comparator), configured by
`Audit/<Name>/comparator.json`, checks that the two files state the same theorems, that the
Solution uses only the standard axioms, and replays the Solution through Lean's kernel and the
independent kernel checkers bundled with the toolchain.

| Challenge | Main theorem |
|---|---|
| [Audit/LatticeVariance](Audit/LatticeVariance) | Lattice paper, Theorem 1.1 |
| [Audit/IsotropicMetric](Audit/IsotropicMetric) | Continuum paper, Theorem 1.1 |
| [Audit/WhiteNoiseGeneral](Audit/WhiteNoiseGeneral) | Continuum paper, Theorem 1.2, white noise |
| [Audit/PoissonGeneral](Audit/PoissonGeneral) | Continuum paper, Theorem 1.2, Poisson process |

**Lattice paper** ([Audit/LatticeVariance](Audit/LatticeVariance), about 240 lines). The Challenge
defines, from Mathlib alone, the lattice $\mathbb Z^d$, the passage time, the critical probability
of bond percolation, the product law of the weights (`weightLaw`), the time constant as the explicit
limit $\mu(x)=\lim_{n\to\infty}\mathbb E~T(0,\lfloor nx\rfloor)/n$, Assumption (W), and
Assumption (Curv) with the constants $\delta,r,\Lambda,\lambda$ at a unit vector $\xi$, on
$\xi^\perp$ (`AssumptionCWith`). It states Theorem 1.1, the exponential moment at every
$x\in\mathbb Z^d\setminus\lbrace0\rbrace$ within distance $\vert x\vert^{3/4}$ of the ray
$\mathbb R_+\xi$, with $\varepsilon$ and $C$ chosen before $\xi$ and $x$
(`LatticeVariance.lintegral_exp_passageTime_le`), and the variance bound uniform in the direction
that follows, with $\varepsilon$ and $n_0$ chosen before $\xi$
(`LatticeVariance.variance_passageTime_floorVertex_le_uniform`). Five further theorems certify
these definitions: under `weightLaw` the weights are independent with law $F$, and
it is the only such law (`weightLaw_iid`, `eq_weightLaw`); the limit defining $\mu$ exists
(`tendsto_integral_passageTime_div`); $\mu$ is a norm (`timeConstant_isNorm`); and
$T(0,nx)/n\to\mu(x)$ almost surely for every $x\in\mathbb Z^d$ (`ae_tendsto_passageTime_div`).
That (W) can be met, since $p_c(d)\geq1/(2d)\gt0$, is proved in the library
(`CurvatureVariance.bondCriticalProb_bounds`), not in the Challenge.

**Continuum paper, Theorem 1.1** ([Audit/IsotropicMetric](Audit/IsotropicMetric), about 250 lines).
The Challenge defines, from Mathlib alone, $\mathbb R^d=\mathbb R\times\mathbb R^m$, Gaussian white
noise as a measurable random distribution $W$ with $W(\varphi)$ centered Gaussian of variance
$\int\varphi^2$, the density $\psi(\chi\ast W)$, rectifiable curves with their arc-length cost, and
the passage time. It states Theorem 1.1, the exponential moment with the time constant given by its
defining limit (`IsotropicMetric.lintegral_exp_passageTime_le`), and the variance bounds that
follow, at the points $te_1$ (`IsotropicMetric.variance_passageTime_le`) and at every point, with
$\varepsilon$ and $r_0$ before $x$ (`IsotropicMetric.variance_passageTime_le_norm`). A further
theorem certifies that white noise exists on a standard Borel probability space
(`IsotropicMetric.exists_isWhiteNoise`).

**Continuum paper, Theorem 1.2, white noise** ([Audit/WhiteNoiseGeneral](Audit/WhiteNoiseGeneral),
about 300 lines). The Challenge defines the same objects, the restriction of white-noise
configurations to a set and their motion by a rigid motion, and Assumption A (jointly measurable,
determined by the noise in the closed unit ball, between two positive constants, equivariant under
proper rigid motions). It states Theorem 1.2 for white noise
(`WhiteNoiseGeneral.lintegral_exp_passageTime_le_of_isWhiteNoise`) and the variance bounds that
follow, at the points $te_1$ (`WhiteNoiseGeneral.variance_passageTime_le_of_isWhiteNoise`) and at
every point (`WhiteNoiseGeneral.variance_passageTime_le_norm_of_isWhiteNoise`). Further theorems
certify that white noise exists (`WhiteNoiseGeneral.exists_isWhiteNoise`) and that the density
$\psi(\chi\ast\omega)$ of Theorem 1.1 satisfies Assumption A
(`WhiteNoiseGeneral.isLocalDensity_convolutionDensity`).

**Continuum paper, Theorem 1.2, Poisson process** ([Audit/PoissonGeneral](Audit/PoissonGeneral),
about 270 lines). The Challenge defines the homogeneous Poisson process of intensity $\lambda\gt0$,
a measurable random measure whose counts of disjoint bounded Borel sets are independent Poisson
variables with means $\lambda$ times their volumes, the restriction and the image of its
configurations, and Assumption A. It states Theorem 1.2 for the Poisson process
(`PoissonGeneral.lintegral_exp_passageTime_le_of_isPoissonProcess`) and the variance bounds that
follow, at the points $te_1$ (`PoissonGeneral.variance_passageTime_le_of_isPoissonProcess`) and at
every point (`PoissonGeneral.variance_passageTime_le_norm_of_isPoissonProcess`). A further theorem
certifies that the Poisson process exists (`PoissonGeneral.exists_isPoissonProcess`).

To run the comparators as the Palomar registry does (requires `bubblewrap`; on Ubuntu 24.04 also
`sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`), after the build:

```sh
scripts/verify-comparators.sh                    # all four
scripts/verify-comparators.sh LatticeVariance    # one of them
```

After the build, one comparator run takes about 6 to 13 minutes on a 16-core machine: it builds and
exports the Challenge and the Solution and replays the Solution through the three kernels.

## The papers

The two papers are included for reference:
- [papers/CurvatureVariance.pdf](papers/CurvatureVariance.pdf), lattice first-passage percolation:
  the version of October 31, 2026 (18 pages).
- [papers/IsotropicVariance.pdf](papers/IsotropicVariance.pdf), rotationally invariant
  first-passage percolation: the version submitted to arXiv on October 30, 2026 (19 pages).

[docs/FORMALIZATION-NOTES.md](docs/FORMALIZATION-NOTES.md) lists every deviation of the Lean statements from
the printed ones in these versions, and the differences of route between the formal and the printed
proofs.

## How this was built

The Lean code was written with AI assistance, by Claude Opus 5.5 and GPT-6.1 Sol agents, under the
direction of the authors. Every proof is checked by the Lean kernel. The models, tools and review
process are disclosed in [formalization.yaml](formalization.yaml), following the
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The Lean development is by **Scott Armstrong** and **Ahmed Bou-Rabee**. To cite it, use
[CITATION.cff](CITATION.cff), and please also cite the papers:

```bibtex
@unpublished{ArmstrongBouRabee2026Lattice,
  author = {Armstrong, Scott and Bou-Rabee, Ahmed},
  title  = {Curvature and variance in lattice first-passage percolation},
  year   = {2026},
  note   = {Preprint}
}

@unpublished{ArmstrongBouRabee2026Isotropic,
  author = {Armstrong, Scott and Bou-Rabee, Ahmed},
  title  = {Fluctuation bounds for rotationally invariant first-passage percolation},
  year   = {2026},
  note   = {Preprint}
}

@software{FPPVariance,
  author = {Armstrong, Scott and Bou-Rabee, Ahmed},
  title  = {{FPPVariance}: a {Lean} 4 formalization of fluctuation bounds for lattice and
            rotationally invariant first-passage percolation},
  year   = {2026},
  date   = {2026-10-31},
  url    = {https://github.com/nitromannitol/FPP-variance}
}
```

Funding: Scott Armstrong was supported by the European Research Council (ERC) under the European
Union's Horizon Europe research and innovation programme, grant agreement No. 101200828.

## License

The Lean code, the scripts and the documentation are licensed under Apache 2.0; see
[LICENSE](LICENSE). The papers in `papers/` are © the authors, all rights reserved, and are
included for reference; they are not covered by the Apache 2.0 license.

## References

- [ADH] A. Auffinger, M. Damron and J. Hanson, *50 Years of First-Passage Percolation*, University
  Lecture Series 68, American Mathematical Society, 2017; numbering as in
  [arXiv:1511.03262v2](https://arxiv.org/abs/1511.03262v2).
- [AKM] S. Armstrong, T. Kuusi and J.-C. Mourrat, *Quantitative Stochastic Homogenization and
  Large-Scale Regularity*, Grundlehren der mathematischen Wissenschaften 352, Springer, 2019;
  numbering as in [arXiv:1705.05300v2](https://arxiv.org/abs/1705.05300v2).
- [BLM] S. Boucheron, G. Lugosi and P. Massart, Concentration inequalities using the entropy
  method, *Annals of Probability* **31** (2003), 1583–1614.
- [BSS23] R. Basu, V. Sidoravicius and A. Sly, Rotationally invariant first passage percolation:
  Concentration and scaling relations, [arXiv:2312.14143](https://arxiv.org/abs/2312.14143) (2023).
- [BSS26] R. Basu, V. Sidoravicius and A. Sly, Rotationally invariant first passage percolation:
  Breaking the $n/\log n$ variance barrier, [arXiv:2604.01214](https://arxiv.org/abs/2604.01214)
  (2026).
- [BR] M. Benaïm and R. Rossignol, Exponential concentration for first passage percolation through
  modified Poincaré inequalities, *Annales de l'Institut Henri Poincaré, Probabilités et
  Statistiques* **44** (2008), 544–573;
  [arXiv:math/0609730v2](https://arxiv.org/abs/math/0609730v2).
- [DCT] H. Duminil-Copin and V. Tassion, A new proof of the sharpness of the phase transition for
  Bernoulli percolation on $\mathbb Z^d$, *L'Enseignement Mathématique* **62** (2016);
  [arXiv:1502.03051](https://arxiv.org/abs/1502.03051).
- [HN] C. D. Howard and C. M. Newman, Geodesics and spanning trees for Euclidean first-passage
  percolation, *Annals of Probability* **29** (2001), 577–623.
- [Kes86] H. Kesten, Aspects of first passage percolation, in *École d'Été de Probabilités de
  Saint-Flour XIV – 1984*, Lecture Notes in Mathematics 1180, Springer, 1986, 125–264.
- [Kes93] H. Kesten, On the speed of convergence in first-passage percolation, *Annals of Applied
  Probability* **3** (1993), 296–338.
