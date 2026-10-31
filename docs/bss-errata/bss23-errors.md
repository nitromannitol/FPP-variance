# Corrections needed in the 2023 paper of Basu, Sidoravicius and Sly

Let $X_n=T(0,ne_1)$ be the passage time in the model of the paper, let $\mu=\lim_{n\to\infty}\mathbb EX_n/n$, and let $Q_n$ be the regularized concentration scale defined on printed page 12. Write $W_n=\sqrt{nQ_n}$. The random transversal fluctuation is written $\mathcal W_n$ in this note to distinguish it from $W_n$. All locators below refer to the printed pages of *Rotationally invariant first passage percolation: concentration and scaling relations*, arXiv:2312.14143v1, December 21, 2023. Unnumbered displays are identified by the lemma and their position.

**Proved.** The large-parameter probability assertion for $S^{(n)}_{z,u}$ in Lemma 5.2 is false for nondegenerate bounded Riemannian models. There is a contradiction using an independent variance lower bound, without assuming Theorem 3 of the paper. The bad event $B^{(3)}$ on page 65 occurs in every environment because its endpoint columns are allowed to coincide, so its claimed small probability in Lemma 10.4 would be possible only if that lemma's entire scale hypothesis were independently ruled out. The event $G^{(3)}_{i,j}$ on page 70 also contradicts its claimed high probability in a nondegenerate Gaussian Riemannian model: it compares the wrong two environments. Several further displayed statements and implications in Sections 5, 7, 8, 10 and 11 are incorrect. Their corrections, proofs, and limitations are set out below.

**Conditional assessment.** No counterexample to Theorems 1, 2 or 3 is established here. Their printed proofs require corrections. Many of the defects below have local repairs. A complete corrected proof for the full axiomatic model class is not supplied here; in particular, the unrestricted large-parameter local statement in Section 8 is not certified. The result that the large-parameter event is false must be distinguished from the claim that the main theorems are false.

The contradiction for the first defect uses the independent bound $\mathop{\mathrm{Var}}X_R\ge cR^{1/4}(\log(2+R))^{-1/4}$, proved by local modification and orthogonal projections in a separate verification of the Riemannian model, equation (MV29) (not included here). That proof does not use the fluctuation theorems of BSS23. The other corrections below follow by inspecting the printed definitions and by the elementary calculations given here. A sign, index, or center with a unique local correction is classified as a typographical error. An unjustified inference requiring a further argument is classified as a proof gap. The false large-parameter scale has no uniquely determined textual correction. The review's exact coverage is recorded near the end.

## 1. The large-parameter event in Lemma 5.2

### 1.1. The printed assertion

**Proved transcription.** On page 34, the second branch of the unnumbered definition is

$$
S^{(n)}_{z,u}
=\left\{\Gamma_{3zn}\le \frac{\mu}{10}z^{1/10}Q_n\right\}
\cap\left\{\sup_{v,v'\in B_{3zn}(u)}
\left|X_{vv'}-\mu|v-v'|\right|
\le \frac{\mu}{10}z^{1/10}Q_n\right\},
\qquad zW_n\gt n^{1-10\epsilon}.
$$

Lemma 5.2, on the same page, asserts that there is $D>0$, independent of $n,z,u$, such that for every $n\ge1$ and $z\ge10$,

$$
\mathbb P(S^{(n)}_{z,u})\ge
1-\exp\{1-D(zn)^{\epsilon\theta/2}\}.
$$

The absolute-value bars, the radius $3zn$, and the scale $z^{1/10}Q_n$ have been checked in the rendered page. The relevant displays have no equation numbers.

### 1.2. A contradiction that does not use Theorem 3

**Proved, using the independent lower bound (MV29).** Fix a sufficiently large $n=h$ and put $R=zh$ and $\eta=\epsilon\theta/2$. In a bounded Riemannian model with density between $d_-$ and $d_+$, both $X_R$ and $\mu R$ belong to $[d_-R,d_+R]$. The points $0$ and $Re_1$ belong to $B_{3R}(0)$. Consequently the printed event and its probability bound would give

$$
\mathop{\mathrm{Var}}X_R
\le \mathbb E[(X_R-\mu R)^2]
\le \frac{\mu^2}{100}Q_h^2(R/h)^{1/5}
+(d_+-d_-)^2R^2\exp\{1-DR^\eta\}.
$$

For fixed $h$, the right side is $O_h(R^{1/5})$. Equation (MV29) gives instead

$$
\mathop{\mathrm{Var}}X_R\ge
cR^{1/4}(\log(2+R))^{-1/4}.
$$

The quotient $R^{1/4}(\log(2+R))^{-1/4}/R^{1/5}$ tends to infinity. This is a contradiction. The cited lower bound applies, for example, to a nonzero smooth nonnegative radial kernel and a smooth bounded strictly increasing density map driven by Gaussian white noise. No result of Section 10 or 11 of BSS23 is used in this contradiction. The independent lower bound is an explicit input; Assumption 9 alone, with its weaker exponent $1/6$, would not contradict an upper bound of order $R^{1/5}$.

**Conditional alternative, using the stated main theorems.** A mean-based argument also gives an inconsistency test. The event implies

$$
\mathbb EX_R-\mu R
\le C_hR^{1/10}+CR\exp\{1-DR^\eta\}.
$$

The lower half of BSS23 Theorem 3 and (MV29) would give $\mathbb EX_R-\mu R\ge cR^{1/8}(\log(2+R))^{-1/8}$, which contradicts the display. This alternative is conditional on Theorem 3 and must not be presented as an independent proof of that theorem.

### 1.3. Classification and direct uses

**Proved classification.** This is a substantive false scale assertion. There is no unique typographical correction. Enlarging the tolerance changes estimates that are actually used in the subsequent deterministic arguments.

| Direct location | What the printed proof uses | What survives |
| --- | --- | --- |
| Lemma 5.2, pages 34–35 | The second branch is dismissed with “follows similarly.” | The displayed assertion is false. The first branch can be retained separately. |
| Lemma 5.3, page 35 | The large-detour case subtracts at most $6\mu z^{1/10}Q_n/10$ from a Euclidean excess. | The comparison is not justified by an event having the claimed probability. A replacement for the global conclusion is proved below. |
| Theorem 5.4, page 38 | Lemmas 5.2 and 5.3 are combined for all $z$. | The printed unrestricted proof has a gap. Restricting both lemmas gives only the corresponding restricted tail. |
| Definition of $L^{(n),R}$ and $L^{(n),L}$ and Lemma 8.1, page 47 | The event contains $S^{(n2^j)}_{z,(xn,yW_n)}$ for every indicated $j$. | It is valid to restrict to parameters for which all these factors use the first branch. The unrestricted probability assertion does not follow. |
| Lemma 8.2, pages 49–51 | Page 49 uses the first branch in Case 1. Case 2 on pages 50–51 uses the $z^{1/10}Q_{n2^j}$ tolerance. | Fixed-parameter Case 1 can be separated. The unrestricted Case 2 needs another event and another proof. It has additional defects listed in Section 4 below. |
| Lemma 10.2, pages 63–64, and Lemma 10.4, pages 66–67 | These use $S^{(Mn)}_{n^\epsilon,0}$. | For each fixed $M$ and sufficiently large $n$, these uses lie in the first branch. Their other errors are separate. |
| Definition of $D^{(1)}$, page 82, and Lemma 12.8, page 86 | The factors have parameter $R/2$ at base $n$. | They lie in the first branch when $R$ is fixed before $n$ grows. |
| Definitions on page 89 and Lemma 12.18, page 90 | The factors have parameter $R/10$ at bases $n2^\ell$, with $\ell\le\ell_{\max}$. | They also lie in the first branch when $R,M$ are fixed before $n$ grows. |

**Proved regime check.** The bound $Q_H\le C\sqrt H$ gives $W_H\le CH^{3/4}$. Thus $zW_H\le H^{1-10\epsilon}$ for all sufficiently large $H$ when $z$ is fixed, or when $z=n^\epsilon$ and $H\ge n$ with $M$ fixed. For local applications with base $n$ and $z\le n^{1/8}$, every larger dyadic base $H\ge n$ satisfies $zW_H\le CH^{7/8}\le H^{1-10\epsilon}$ eventually. This checks the parameter range. It does not by itself check the deterministic arguments that use the events.

Beyond the block uses already listed, global-confinement applications of Lemmas 5.2–5.3 occur on pages 58, 59 and 72, at fixed normalized widths after the other constants have been chosen. The chaining application on page 87 uses the $O$ part of Lemma 5.2, rather than its false large-parameter $S$ assertion. Theorem 5.4 is invoked on pages 65, 66, 78, 80, 83 and 86. These uses need a valid global tail theorem; they cannot simply cite the false unrestricted auxiliary assertion.

### 1.4. A correct coarse replacement for large global detours

**Proved from Assumptions 1, 4–6 and Lemma 2.1.** For every fixed $0\lt \delta<1/2$, there are $c,C,R_0>0$ such that, for every $R\ge R_0$, the event

$$
\Gamma_{3R}\le R^\delta,
\qquad
\sup_{v,v'\in B_{3R}(0)}
|X_{vv'}-\mu|v-v'||\le CR^{1/2+\delta}
$$

has probability at least $1-C\exp(-cR^{\delta\kappa/2})$. Constants depend on $\delta$ and the model. This statement uses a larger tolerance than the false event.

**Proof.** There are $O(R^4)$ ordered pairs of lattice mesh points in the ball enlarged by two units. For pairs at distance at least one, Assumptions 4 and 5, together with rotation invariance, give an error of order $R^{1/2+\delta}$ outside probability $C\exp(-cR^{\delta\kappa})$. Distances in a fixed bounded interval are covered by the local passage-time bound and finitely many unit connectors. The bound $\sqrt R\log^2R=o(R^{1/2+\delta})$ absorbs the nonrandom error. A union bound absorbs the factor $R^4$. The local-distance part of $\Gamma_{3R}$ and the triangle inequality extend the mesh estimate to real endpoints. Finally, Lemma 2.1 bounds the probability of $\Gamma_{3R}\gt R^\delta$ by $C\exp(-cR^{\delta\kappa/2})$ for sufficiently large $R$, since every fixed power of $\log R$ is smaller than $R^{\delta/2}$. Translation gives the same statement about a deterministic center.

**Proved consequence for the canonical geodesic, using Assumption 8.** Let $\alpha$ be the exponent in the definition of $Q_n$ and choose $\delta=\alpha/8$. For sufficiently large $n$ and every $z\ge10$ satisfying $zW_n\gt n^{1-10\epsilon}$, the coarse replacement excludes a canonical geodesic from $0$ to $ne_1$ having distance at least $zW_n$ from the segment, except with probability $C\exp(-c(zn)^{\delta\kappa/2})$.

**Proof.** Put $R=zn$. At the first such departure, the point $u$ has distance $zW_n$ from the segment and belongs to $B_{3R}(0)$ for large $n$, since $W_n\le n$. Elementary ellipse geometry gives

$$
|u|+|ne_1-u|-n
\ge c\min\{(zW_n)^2/n,zW_n\}
\ge cz n^{-10\epsilon}W_n.
$$

Assumption 8 bounds the sum of the two passage distances along the canonical geodesic by $X_n+C\Gamma_{3R}$. The coarse event would therefore imply

$$
c\mu z n^{-10\epsilon}W_n
\le C'(zn)^{1/2+\delta}+C'\Gamma_{3R}.
$$

But $Q_n\ge Q_1n^\alpha$, so the quotient of the left side by $(zn)^{1/2+\delta}$ is at least

$$
c' z^{1/2-\delta}n^{\alpha/2-10\epsilon-\delta}.
$$

The exponent $\alpha/2-10\epsilon-\delta=3\alpha/8-10\epsilon$ is positive for the printed choices of parameters. The quotient tends to infinity uniformly for $z\ge10$. This proves the assertion. This argument does not prove the all-path assertion of Lemma 5.3 under only the axioms as printed.

**Conditional global repair.** Combining this proved large-parameter bound with a corrected proof of the first-branch global bound gives Theorem 5.4 at large $n$, with some positive stretched-exponential exponent. This supplies an alternative to the erroneous second branch for the global geodesic conclusion. It does not repair the local event of Lemma 8.1 or Case 2 of Lemma 8.2.

**Proved bounded-metric alternative, conditional on the first-branch transversal bound.** The replacement in the earlier check report is also valid. If $V_n$ is distance from the segment, $d_-\le\rho\le d_+$ and $\varrho=d_+/d_-$, then $V_n\le\varrho n$. Put $U_n=\varrho n/W_n$ and $v_n=n^{1-10\epsilon}/(2W_n)$. From $W_n\le Cn^{3/4}$ one gets $U_n\ge cn^{1/4}$ and

$$
v_n=U_n n^{-10\epsilon}/(2\varrho)
\ge cU_n^{1-40\epsilon}.
$$

For $v_n\lt z\le U_n$, use monotonicity and the first-branch estimate at $v_n$. Since $1-40\epsilon>1/2$, a tail $C\exp(-cz^\eta)$ in the first branch becomes a global tail $C\exp(-c'z^{\eta/2})$. For $z\gt U_n$ the event is empty. This proves precisely the bounded-metric consequence claimed by the earlier referee, rather than the original auxiliary event.

## 2. Further errors in the printed Section 5 proof

**Proved transcription and algebraic corrections.** The following defects are separate from the false large-parameter branch. The table gives the literal inconsistency and a correct local replacement. These replacements do not certify the entire chaining proof with its printed numerical constants.

| Locator and printed expression | Inconsistency and correction | Uses and status |
| --- | --- | --- |
| Page 34, proof of Lemma 5.1: “by Lemma 7.3, $Q_{2n+\vert y'\vert W_n}\le CQ_n$.” | This forward citation is unnecessary. Lemma 4.5, $Q_{3m/2}\le D_6Q_m$, gives $Q_{3n}\le D_6^3Q_n$ by three iterations. Since $\vert y'\vert W_n\le n$, it gives the stated bound. | Proved citation repair. It avoids making Section 5 depend on the later record argument. |
| Page 34, last union bound in Lemma 5.2: a sum over $v,v'$ of the probability that the displayed supremum is $\le\mu n^\epsilon Q_{3n}/10$. | The event to be bounded is a large deviation, so its sign must be $\ge$; the summand must concern the fixed mesh pair. There are $O(n^4)$ ordered mesh pairs, rather than the displayed $Cn^2$. Endpoint rounding requires reducing the threshold by its rounding error. | Proved repair: apply (3), Lemma 4.4 and $Q_{6n+O(1)}\le C Q_{3n}$ to each pair, then sum $Cn^4e^{-cn^{\epsilon\theta}}$. In the first branch $z\le Cn^{1/2}$, so this is at most $C'e^{-c'(zn)^{\epsilon\theta/2}}$ for large $n$. The proof must also use $\Gamma_{3n}$ rather than the unexplained $\Gamma_{zn}$ at that line. |
| Page 36, after (64): $\cdots+5\Gamma_{zn}$ in a lower bound, followed by $-5n^\theta$. | A concatenation error is subtracted, and the first branch only states $\Gamma_{3n}\le z^{2\theta/\kappa}n^\epsilon$. | Proved local replacement: subtract $5\Gamma_{3n}$ and then $5z^{2\theta/\kappa}n^\epsilon$. Since $z\le Cn^{1/2}$, this is $O(n^{\epsilon+\theta/\kappa})=o(n^\epsilon Q_{3n})$, because $\theta/\kappa\lt \alpha$. The positive geometric term still dominates this error. |
| Page 36, definition of $f$: $f(0)=v_1$, $f(n)=v_2$, and $\sup_{x\in[0,1]}\vert f(x)\vert \le n^{9/10}$. | The function is the second coordinate of a point on a vertical line. The endpoints must be their second coordinates, and the domain is $[0,n]$. | Proved notational repair. The following chaining argument uses the domain $[0,n]$. |
| Page 36: $r_j=(1+\tfrac12(1-2^{-\theta(j+1)})z)W_n\le zW_n/2$. | The displayed inequality is false for large $j$, since $r_j\to(1+z/2)W_n$. For $z\ge4$ the valid bound is $r_j\le3zW_n/4$. | Proved local repair. At the last step on page 38, replace the asserted gap $zW_n/2$ by $zW_n/4$ and decrease the resulting geometric constants. The gain remains of order $z^2n^{3\epsilon}Q_n$, so the power comparison with $n^\epsilon Q_{3n}$ survives. |
| Page 37, last event inclusion before page 38: $1/(1000\theta^2)$ multiplies $(\vert y-y'\vert +z2^{\theta j})Q_{n2^{-j}}$. | The preceding calculation and the definition of $H$ have coefficient $\theta^2/1000$. The reciprocal coefficient is not controlled by the preceding geometric bound. | Proved typographical repair: use $\theta^2/1000$. |

**Conditional limitation.** To conclude the all-path versions from these corrections, one must justify decomposing the cost of an arbitrary competing path into passage distances with the claimed error. Assumption 8 and the definition of $\Gamma_n$ on page 13 are stated for canonical optimal paths, whereas Lemmas 5.3 and 8.2 concern arbitrary paths. In the Riemannian model this lower decomposition follows from additivity of the length integral along subarcs. For an abstract model it requires a stated additional property or a separate argument. The table above repairs the displayed algebra; it does not silently strengthen Assumption 8. The occurrences of the same all-path decomposition in Sections 8 and 10 carry the same qualification.

## 3. Section 7: saturation, record scales, and truncation

### 3.1. Exact saturation in Lemma 7.1 need not occur

**Proved error.** Page 42 asserts the existence of a finite $x_*\ge1$ with

$$
\mathbb P(|X_n-\mathbb EX_n|\gt x_*\widehat Q_n)
=\exp(1-x_*^\theta).
$$

This does not follow from the infimum defining $\widehat Q_n$. The issue is a strict-tail endpoint, and is relevant when the passage law has atoms. For the scalar nonnegative variable $X=2+\varepsilon$, with $\mathbb P(\varepsilon=1)=\mathbb P(\varepsilon=-1)=1/2$, one has $|X-\mathbb EX|=1$ and $\widehat Q=1$. At every $x\ge1$ the strict tail is zero and the proposed right side is positive. No equality exists. This is a counterexample to the saturation inference, not a counterexample to a passage-time theorem.

**Proved replacement, conditional on Lemma 6.4 and the mean bound of Lemma 4.4.** Suppose $Q_n\le C\widehat Q_n$ at a quasi-record. The number $q=3\widehat Q_n/4$ fails the defining tail inequality. Hence there is $x>1$ such that, with $t=xq/Q_n$,

$$
t>3/(4C),\qquad
\mathbb P(|X_n-\mathbb EX_n|\gt tQ_n)
\gt \exp\{1-(4Ct/3)^\theta\}.
$$

Lemma 6.4 and $\mathbb EX_n-\mu n\le D_1Q_n$ give an upper bound $\exp\{1-((t-D_1)/R)^{4\theta/3}\}$ for $t\gt D_1$. Since $4\theta/3\gt \theta$, these bounds force $t\le T(C,D_1,R,\theta)\lt \infty$. Thus the displayed tail probability is at least $p=\exp\{1-(4CT/3)^\theta\}>0$, and

$$
\mathop{\mathrm{Var}}X_n\ge \frac{9p}{16C^2}Q_n^2.
$$

This proves the required conclusion without exact saturation. At an actual record, $C=1$ and $t>3/4$. Splitting the two-sided tail gives one side with probability at least $p/2$ at distance more than $3Q_n/4$ from the mean. The opposite side has uniformly positive mass by centering and the integrable tail bound (3): if its probability were $\delta$, its first moment would be at most $Q_n\int_0^\infty\min\{\delta,e^{1-s^\theta}\}\,ds$, which tends to zero with $\delta$. The two sets are separated by more than $3Q_n/4$. An interval of radius $Q_n/3$ cannot meet both. This gives the anti-concentration conclusion (87), with a possibly smaller positive constant.

**Proved dependency.** Lemma 7.3 uses the exact saturation again in (86), on pages 43–44. Lemma 7.1 and (87) survive through the preceding repair. The intermediate first-moment integral on page 44 must also contain the factor $Q_{n'}$ after the substitution $t=sQ_{n'}$; its omission is a dimensional typographical error.

### 3.2. The range and constants in Lemma 7.2 are inconsistent

**Proved transcription.** On page 42 the lemma reads

$$
L\in[C_{10},n^{-1/(2C_{11})}],
\qquad m\in[nL^{-C_9},nL^{-1}].
$$

The upper endpoint of the $L$ interval tends to zero, whereas $C_{10}$ is chosen large. This makes the stated assertion vacuous for large $n$, so it cannot supply the record points used later. The proof on page 43 also changes the exponent among $C_9,C_{11},C_2$, and prints an inequality in the wrong direction when absorbing a prefactor into a power of $L$.

**Proved replacement when the regularizing supremum is attained.** Set $b=\log D_6/\log(3/2)$. For a higher-exponent quasi-record $n$, choose an $\alpha$-record $m$ attaining the $\alpha$ envelope at $n/L$. Lemma 4.5 and the higher-exponent quasi-record property give

$$
D_6^{-1}L^{-b}Q_n
\le Q_{n/L}
=\left(\frac{n/L}{m}\right)^\alpha\widehat Q_m
\le CL^{-\alpha}(m/n)^{\alpha'-\alpha}Q_n.
$$

It follows that

$$
m\ge n(CD_6)^{-1/(\alpha'-\alpha)}
L^{-(b-\alpha)/(\alpha'-\alpha)},\qquad m\le n/L.
$$

Choose $C_{11}$ larger than the exponent in this display and then $C_{10}$ large enough to absorb the prefactor. The corrected assertion has

$$
C_{10}\le L\le n^{1/(2C_{11})},
\qquad nL^{-C_{11}}\le m\le n/L.
$$

In particular $m\ge\sqrt n$. If attainment or continuity of the real-scale envelope is not established, the same calculation gives approximate records, with a fixed extra quasi-record factor. Promoting them to exact records requires an attainment argument. The printed proof's last step instead writes a strict inequality between regularized $Q$ values which is impossible for an $\alpha$-regularized envelope; it must use the raw $\widehat Q$ or argue through the first maximizing scale. No general real-scale attainment theorem is certified here.

**Proved dependency.** The nonempty record-scale interval is needed in the proof of Proposition 9.2, page 52, and the choice of $m$ in Lemma 10.9, page 72. The higher quasi-record argument and the resulting bounded gaps in record scales also enter Proposition 10.13. These uses require the corrected lemma, rather than its vacuous printed version. The final choice of a divisor $m=n/k$ in Lemma 10.9 can be made by rounding $n/r$ for a nearby record $r$; this changes $m$ by at most a bounded factor and keeps a record in $[m/2,2m]$.

### 3.3. The truncation in Lemma 7.3 is reversed

**Proved error.** On page 44 the definition is, apart from a stray printed $E$ before its final center,

$$
\overline X_{a_{i-1}a_i}^{\Lambda_i}
=\min\{\max\{X_{a_{i-1}a_i}^{\Lambda_i},\mu|a_i-a_{i-1}|+M^\epsilon Q_n\},
\mu|a_i-a_{i-1}|-M^\epsilon Q_n\}.
$$

For $b=M^\epsilon Q_n>0$ and $c=\mu|a_i-a_{i-1}|$, the function $\min\{\max\{x,c+b\},c-b\}$ is identically $c-b$. It does not agree with $x$ on the event $V$ where $|x-c|\le b$. Thus the inference $|X_{Mn}-\Phi|\le Q_n$ on $A\cap J\cap V\cap B$ is not justified by the printed truncation.

**Proved unique local correction.** Use the projection to $[c-b,c+b]$:

$$
\overline X=\min\{\max\{X,c-b\},c+b\}.
$$

It equals $X$ on $|X-c|\le b$, and changing the noise in one column changes every truncated passage for that column by at most $2b$. Therefore it changes the infimum $\Phi$ by at most $2b$. The bounded-difference argument on page 45 applies to the independent column environments, even though passages within a column are not independent.

**Proved further typographical correction.** After bounding $\mathbb P(|\Phi-\mathbb E\Phi|\gt M^{2/3}Q_n)$, page 45 prints a bound on $|X_{Mn}-\Phi|$ at threshold $(1+M^{2/3})Q_n$. The required statement has $\mathbb E\Phi$ in place of $\Phi$. The triangle inequality and $|X_{Mn}-\Phi|\le Q_n$ give exactly that correction. It supplies the deterministic center required by (87). The final strict margin can be arranged by choosing the exceptional probability less than the anti-concentration constant, rather than equal to it.

## 4. Section 8: comparison strips, the large-parameter construction, and Corollary 8.3

### 4.1. The comparison strips point in the wrong direction

**Proved error and local correction.** In the first intersection defining $L^{(n),R}_{x,x',y,z}$ on page 47, the first index of $H^{(2^jn)}$ is printed as $x2^{-j}-1$. By the definition of $H$ on page 33, this controls the strip from $(x-2^j)n$ to $xn$. The proof on pages 48–49 needs the strip from $xn$ to $(x+2^j)n$. Its index is $x2^{-j}$. In the first intersection for $L^{(n),L}$ the converse error occurs: the printed index $x2^{-j}$ must be $x2^{-j}-1$.

For example, with $x=0$, the right-moving event as printed controls $[-2^jn,0]$ when the proof uses $[0,2^jn]$. This is a coordinate identity, not a probabilistic issue. Swapping these two first indices is the unique correction consistent with the stated strips and reflection. The terminal-strip factors in the definitions need no corresponding swap. The union bound in Lemma 8.1 is unchanged by translation of the strips. It begins with $\le$, not the printed equality to a sum of exponential upper bounds.

**Conditional dependency.** This repairs the strip alignment used in Case 1 of Lemma 8.2. It must be propagated to the local events used in Lemma 9.4, the favorable events $C^{(2)}$ on page 61, Lemma 10.4 and the Section 12 proxies. It does not repair their large-parameter probabilities.

### 4.2. The scale $j_*$ in Case 2 is not defined by the printed formula

**Proved error.** On page 50 the formula is

$$
j_*=j_{\max}\wedge\max\{j:zW_n\le2^{j-5}n\}.
$$

The set in braces contains every sufficiently large integer, so it has no maximum. Restricting the maximum implicitly to $j\le j_{\max}$ does not solve the intended problem: when nonempty its maximum is always $j_{\max}$. The argument needs the first crossover scale.

Simply replacing $\max$ by $\min$ is insufficient. Put $A=zW_n$ and suppose the first crossover $J$ is below $j_{\max}$. Then the printed first branch has $a_{J-1}\lt A$, whereas the printed second branch starts with $a_J=n2^{J-5}\ge A$. Thus $a_{J-1}-a_J<0$. The later claim on page 50 that $a_j-a_{j+1}\ge A^{9/10}$ fails at that transition. The prose actually prints $\le A^{9/10}$ at the first occurrence, although the subsequent lower bound requires $\ge$.

**Proved replacement for this geometric construction only.** Let $J$ be the smaller of $j_{\max}$ and the first nonnegative integer with $2^Jn\ge32A$. For sufficiently large $A$, put $B=A-JA^{9/10}$ and use

$$
a_j=\begin{cases}
A-jA^{9/10},&j\lt J,\\
B2^{9(j-J)/10},&j\ge J.
\end{cases}
$$

Here $J=O(\log A)$, since $n\ge1$, so $A/2\le B\le A$ for sufficiently large $A$. It follows that $A/2\le a_j\le A2^{9j/10}$, $a_j-a_{j+1}=A^{9/10}$ for $j\lt J$, including $j=J-1$, and $a_{j+1}/a_j=2^{9/10}$ for $j\ge J$. If $J\lt j_{\max}$, then $a_j/(2^jn)\le1/32$ for $j\ge J$. These are the monotonicity and small-slope properties needed for the two geometric comparisons, with adjusted numerical constants.

**Conditional limitation.** This corrects the sequence, not the whole proof of Case 2. That proof still invokes the false large-parameter event. Page 51 also writes a stopping condition containing both $u_2$ and $u'_2$, rather than using $u'_2$ in both distances. Page 50 writes $Q_{n2^j}\le\sqrt{n2^j}\le2^{-5}(zW_n)^{1/2}$, whereas the displayed crossover could at most give a bound with a positive fixed constant times $(zW_n)^{1/2}$, together with the model-dependent constant in (4). These are local formula defects. No complete corrected unrestricted version of Lemmas 8.1–8.2 is proved here.

**Conditional statement still needed.** For the full abstract class, the unresolved replacement is an explicitly defined event $\widetilde L^{(n),R}_{x,x',y,z}$ with $\mathbb P((\widetilde L^{(n),R}_{x,x',y,z})^c)\le C\exp(-cz^\eta)$, for some $c,C,\eta>0$, on which every class $\Xi^{(n),R}_{x,x',y,k,z}$ with $0\le k\le\lfloor\log_2(x'-x)-1\rfloor$ has passage excess at least $c'\mu z^{1/3}Q_n$, uniformly for sufficiently large $n$, $x'\gt x$ and sufficiently large $z$. A reflected statement is needed as well. No complete replacement event and proof for this unrestricted statement is known from the arguments verified in this audit. This is a precise limit of the audit, rather than a claim that the intended local conclusion is false.

### 4.3. Corollary 8.3 states the wrong probability direction

**Proved error.** On page 51, equation (93) prints

$$
\mathbb P\left(
\inf_{\gamma'\in\Xi^{(n),R}_{x,x',y,k,z}}
\{X_{\gamma'}-X_{\gamma'(0),\gamma'(1)}\}
\ge \frac{\mu z^{1/3}}{4000}Q_n\right)
\le \exp(1-Dz^{\epsilon\theta/2}),
$$

and gives $1\le k\le\lfloor\log_2(x-x')-1\rfloor$. The right-moving class is defined for $x'\gt x$, so $\log_2(x-x')$ is not real. Moreover Lemma 8.2 says that the event inside the probability contains $L^{(n),R}$; Lemma 8.1 assigns that event high probability. An upper bound tending to zero is the opposite conclusion.

**Proved unique correction, conditional on valid versions of Lemmas 8.1–8.2.** Replace the $k$ interval by $1\le k\le\lfloor\log_2(x'-x)-1\rfloor$ and the right side by $1-\exp(1-Dz^{\epsilon\theta/2})$, with probability direction $\ge$. Equivalently, bound the probability of the strict complementary event by $\exp(1-Dz^{\epsilon\theta/2})$. Event inclusion proves this immediately. The left-moving statement follows by reflection with $x-x'>0$.

**Proved direct use.** Lemma 9.4 on page 54 invokes this corollary to bound the probability of a bad local crossing. That use requires the corrected complementary-event inequality. Later local uses in Section 10 invoke Lemma 8.2 and its event directly, rather than the incorrectly printed equation (93).

**Conditional range issue.** The favorable event $C^{(2)}$ on page 61 includes $k=0,1$, while Lemma 8.2 and Corollary 8.3 state only $k\ge1$. In particular Lemma 10.7 uses $k=0$ explicitly. A corrected local lemma must include $k=0$, or the application must be rescaled to base $n/2$ with endpoint intervals covered and constants adjusted. The calculations for the small-parameter case have no singularity at $j=0$, but the extension is not a literal consequence of the printed statement. No unrestricted $k=0$ theorem is certified here.

## 5. Section 10: localization and resampling

### 5.1. Errors in the barrier proof of Lemma 10.2

**Proved transcription and inconsistency.** Page 63 gives $b^-_1=(-4\Theta n/3,4\Theta W_n/3)$ and $b^-_2=(4\Theta n/3,4\Theta W_n/3)$, the same heights as $b^+_1,b^+_2$. These cannot define the lower barrier in Figure 15 or enclose the central rectangle in (99). Their second coordinates must be $-4\Theta W_n/3$. The following description also repeats the left vertical line twice. The subsequent exit test on pages 63–64 says $y=\pm3\Theta n/2$, whereas the intended sides are vertical and require an $x$ coordinate. These formulas need to be aligned with the endpoints of the chosen barrier crossings, rather than just changing a letter while leaving unmatched endpoints.

**Conditional geometric repair.** With lower endpoints at negative height and the stated small transversal bound, take proper subcrossings of the upper and lower geodesics between $x=-4\Theta n/3$ and $x=4\Theta n/3$. Their heights stay in disjoint bands about $\pm4\Theta W_n/3$. Join their corresponding endpoints on the two vertical lines. The resulting boundary encloses $[-\Theta n,\Theta n]\times[-\Theta W_n,\Theta W_n]$ and lies inside $\Lambda^+$. A path with endpoints in that central rectangle which reaches a vertical side has Euclidean excess at least $cn$; a path escaping through a barrier permits the stated substitution. This is the construction shown schematically in Figure 15. Its probabilistic use remains conditional on valid barrier-deviation and path-decomposition estimates.

```text
        x = -4 Theta n/3                  x = 4 Theta n/3
                 |---- upper crossing ----|
                 |    central rectangle   |
                 |---- lower crossing ----|
```

The crossings lie in disjoint bands about heights $4\Theta W_n/3$ and $-4\Theta W_n/3$. The vertical joins use the crossing endpoints on the displayed lines.

**Proved sign repair.** On page 64 the preceding displayed calculation correctly gives, with $q=Q_{8\Theta n/3}$,

$$
X^{\gamma'}_{w_1w_2}-X^{\gamma^+}_{w_1w_2}\ge q-3\Gamma_{Mn}.
$$

The next chain instead adds $q-3\Gamma_{Mn}$ when replacing the excursion by the cheaper barrier segment, and ends with $X_{\gamma'}+3q$. That proves no positive penalty. The correct substitution is

$$
X_{\gamma'(0),\gamma'(1)}
\le X_{\widehat\gamma}
\le X_{\gamma'}-q+6\Gamma_{Mn}.
$$

It gives $X_{\gamma'}-X_{\gamma'(0),\gamma'(1)}\ge q-6\Gamma_{Mn}\ge2Q_n$ after choosing $\Theta$ large and then $n$ large. Indeed $q/Q_n\ge(8\Theta/3)^\alpha$, and the event $S^{(Mn)}_{n^\epsilon,0}$ bounds $\Gamma_{Mn}=o(Q_n)$ for fixed $M$. The norm-error terms elsewhere on page 64 must be bounded at the actual base $Mn$, by $C(M)n^\epsilon Q_{3Mn}$, rather than the printed smaller $n^\epsilon Q_{3n}$; they remain $o(n)$ by (4). These repairs preserve the localization argument conditional on the geometric and path inputs. Lemma 10.2 is used in Corollary 10.3 and in the bad event $B^{(4)}$ below.

### 5.2. The printed bad event $B^{(3)}$ occurs in every environment

**Proved error.** On page 65 the unnumbered definition takes a maximum over $0\le i,i',i''\le M$ and $y,y'\in[-MW_n,MW_n]$, and then over $(x_1,y_1),(x_2,y_2)\in\gamma_{i,y,i',y'}$ with $|x_1-i''n|,|x_2-i''n|\le\log^3n$. It declares the event bad when $|y_1-y_2|\ge W_n/4$. There is no restriction $i\ne i'$.

Choose $i=i'=i''=0$, $y=0$, and $y'=W_n/2$. The two endpoints of $\gamma_{0,0,0,W_n/2}$ themselves satisfy the two horizontal constraints and have vertical separation $W_n/2$. Thus $B^{(3)}$ is the whole probability space. Consequently $B=\bigcup_{r=1}^5B^{(r)}$ has probability one. The proposed estimate $\mathbb P(B)\le M^{-90}$ is therefore impossible at any scale satisfying the hypothesis $Q_{Mn}\le M^{1/10}Q_n$ of Lemma 10.4. This does not exhibit a scale satisfying that hypothesis; it shows that the printed bad-event argument cannot work without independently ruling out the entire hypothesis, which is the later argument's objective at record scales. The unconditional defect is that the purportedly rare event is deterministic.

**Proved replacement, conditional on the small-parameter shape event and Assumption 8.** Restrict this maximum to distinct endpoint columns, $0\le i,i'\le M$ with $i\ne i'$, retaining both orders. For fixed $M$ the absolute endpoint slope is at most $2MW_n/n=o(1)$. To check the geometric step on page 66, put $e=(q-p)/|q-p|$ for the endpoints of one of these geodesics. For two tested points in their path order with difference $\Delta$, the sum of the three chord lengths minus $|q-p|$ is at least

$$
|\Delta|-e\cdot\Delta
\ge(1-|e_2|)|\Delta_2|-|\Delta_1|
\ge W_n/5
$$

for sufficiently large $n$, since $|\Delta_1|\le2\log^3n$ and $|\Delta_2|\ge W_n/4$. If the geodesic leaves $B_{3Mn}(0)$, use its first exit instead to obtain a larger chord excess with all tested points in that ball. The first branch of $S^{(Mn)}_{n^\epsilon,0}$ and Assumption 8 then give the contradiction on pages 66–67: its metric errors are $O_M(n^\epsilon Q_n)$, while $W_n/Q_n=\sqrt{n/Q_n}\ge cn^{1/4}$. This proves the intended bound for the corrected $B^{(3)}$ at large $n$.

The missing distinct-column restriction is a hypothesis error with a local repair, rather than a counterexample to the intended geometric estimate. All subsequent uses in Lemmas 10.6–10.7 concern geodesics between distinct columns. Their use of the corrected exclusion therefore survives, conditional on the other event estimates.

**Proved additional correction in Lemma 10.4.** The probability bound for the local event on page 66 must retain the exponent $\eta=\epsilon\theta/2$ of Lemma 8.1, rather than the displayed $\theta$. With local parameter at least $c\Theta^{1/200}$ this still suffices: $\Theta^{\eta/200}$ grows as $(\log M)^{(5/2)\theta/\epsilon}$, and $\theta/\epsilon=10^6$. It dominates $\log M$. The powers of $\Theta$ in the stated path penalty must likewise be obtained from $z^{1/3}$, rather than increased without justification. For fixed $M$, any resulting positive constant times $Q_{\Theta n}$ still dominates $n^\epsilon$ as $n$ grows. The proof's indices $i+\Theta$ and $i-\Theta$ and its left/right event must be aligned consistently with the chosen pair; these changes do not justify applying the right-moving event to a left-moving path.

More explicitly, that page first places a path in $\Xi^{(\Theta n),L}$, but then writes $L^{(n),R}$ for the controlling event. For the left-moving path starting at column $i$, the corrected event has superscript $(\Theta n),L$ and first two indices $i/\Theta,0$. Its parameter is a fixed small constant times $\Theta^{88/100}W_n/W_{\Theta n}$. Decreasing the printed constant $1/6$ accommodates the unit error from taking floors of crossing heights. For the actual definition using $J_i-J_{i+\Theta}$, start instead at column $i+\Theta$. These are scale and orientation corrections to the invocation of the local lemma; their probability remains conditional on a valid version covering $k=0$.

### 5.3. The bad event excludes the wrong direction of disagreement

**Proved error.** Page 65 defines

$$
B^{(4)}=\bigcup_{i,j}\{C_{i,j}\cap(C^{\mathrm{loc}}_{i,j})^c\}.
$$

Page 67 then says that this definition implies $B^c\cap C^{\mathrm{loc}}_{i,j}\subset C_{i,j}$. It does not: a point with $C^{\mathrm{loc}}_{i,j}$ true and $C_{i,j}$ false is not excluded by the printed $B^{(4)}$.

**Proved replacement, conditional on Lemma 10.2.** Replace each disagreement event in $B^{(4)}$ by $C_{i,j}\mathbin{\triangle}C^{\mathrm{loc}}_{i,j}$. The pair of environments is exchangeable conditional on the noise inside $\Lambda^{++}_{i,j}$: the two outside completions are independent and have the same law. Thus Lemma 10.2 also bounds the reverse disagreement, and

$$
\mathbb P(C_{i,j}\mathbin{\triangle}C^{\mathrm{loc}}_{i,j})\le2M^{-100}.
$$

A union bound changes only the fixed prefactor in Lemma 10.4. The required inclusion now holds. Alternatively one can reverse the disagreement in $B^{(4)}$ and retain its original direction separately for Corollary 10.3. Proposition 10.5, Lemmas 10.6–10.7 and Lemma 10.10 all need the corrected inclusion.

### 5.4. The interior resampling event compares the wrong environments

**Proved error.** On page 70 the event is printed as

$$
G^{(3)}_{i,j}
=\left\{\sup_{\gamma'\subset\Lambda^-_{i,j}}
|X^{\omega^{ij}}_{\gamma'}-X_{\gamma'}|=0\right\}.
$$

The block $\Lambda_{i,j}$ has just been replaced by $\omega'$ to define $\omega^{ij}$. Thus $\omega^{ij}$ agrees with $\omega'$ in the interior, not with $\omega$. Lemma 10.8 nevertheless claims $\mathbb P((G^{(3)}_{i,j})^c)\le n^{-10}$ by Assumption 12.

In the smooth Gaussian model with nonzero kernel and strictly increasing $\psi$, the printed event has probability zero once the inner rectangle has nonempty interior and is more than one kernel radius from the block boundary. If all short curve integrals agree in that interior, dividing integrals on shrinking line segments by their lengths shows that the two continuous densities agree at a fixed interior point. The old and new densities at that point are independent atomless transforms of a nondegenerate Gaussian. Their equality has probability zero. This is a concrete contradiction to the high-probability claim, independent of any fluctuation theorem.

**Proved unique correction.** The second passage must be $X^{\omega'}_{\gamma'}$. Compare $\omega'$ with the hybrid which retains $\omega'$ inside the block and uses $\omega$ outside. The first part of Assumption 12 gives exactly the asserted high-probability equality for these two environments. The exterior event $G^{(4)}$ correctly compares $\omega^{ij}$ with $\omega$ and requires no analogous change. The intersection defining $G_{i,j}$ at the bottom of page 70 also has the undefined letter $F^{(k)}_{i,j}$ where it must have $G^{(k)}_{i,j}$.

**Proved dependency.** The corrected $G^{(3)}$ is exactly what is needed to transfer the fresh favorable path in $H_{i,j}$ to $\omega^{ij}$ in Lemma 10.10, page 74. The event $G_{i,j}$ and its probability are then used in Proposition 10.11 and Theorem 10.12. Without the correction, the quoted event has probability zero in the example above.

### 5.5. The favorable-path construction in Lemma 10.9 needs three corrections

**Proved geometric inconsistency.** Page 72 defines

$$
\Delta_i=[(i-1)m+\log^2n,im-\log^2n]
\times[\log^2n,W_m-\log^2n],
$$

but puts both endpoints of $\gamma_i$ at height $W_n/2$. The same page chooses $W_n/W_m\ge\sqrt{n/m}\ge4T$. With $T\ge1$, these endpoints lie above $\Delta_i$, so the event $W_i$ requiring $\gamma_i\subset\Delta_i$ is empty. The asserted positive product probability cannot hold for those rectangles.

**Proved replacement, conditional on Proposition 9.2 and a valid global transversal bound.** Replace $W_m$ by $W_n$ in the definition of $\Delta_i$. Use a strengthened version of (102) whose vertical interval is $[-TW_{n_*},TW_{n_*}]$, rather than its printed much wider interval $[-Tn_*,Tn_*]$. The strengthened version follows from the global transversal tail by choosing $T$ so that its failure probability is less than $\delta_*/2$. The first and last endpoint margins of size $n_*^{9/10}$ are much larger than $W_{n_*}$, so the horizontal containment in (102) is also valid. Since $TW_m\le W_n/4$, translation to height $W_n/2$ now places the favorable middle path inside the corrected $\Delta_i$ with room to spare. The strips remain disjoint, and for the fixed ratio $n/m$, their width $W_n=o(m)$ is allowed by Assumption 12. To transfer the paths, use the equality supplied on a further inner buffer of width $\log^2m$; the favorable paths have polynomial margins, so this buffer does not change their probability estimate.

**Proved passage-time inconsistency.** The connector event $V_i$ on page 72 allows

$$
X_{\widehat\gamma_i}\le2\mu|\widehat\gamma_i(1)-\widehat\gamma_i(0)|
+\tfrac12(n/m)^{-1}Q_n.
$$

The sum on page 73 instead charges only $\mu$ times the connector lengths. Their total length has order $n^{9/10}$ when $n/m$ is fixed. An additional copy of this length cannot be absorbed in $Q_n\le C\sqrt n$.

**Proved replacement, conditional on Lemma 4.4, (3), and the transversal bound.** Remove the factor $2$. This stronger connector estimate still has probability tending to one: connector lengths are at most $2m^{9/10}$, the nonrandom errors are $O(Q_{2m^{9/10}})$ by Lemma 4.4, and $Q_{2m^{9/10}}/Q_n\to0$ by regular growth. The concentration bound (3) makes the probability of an error of a fixed multiple of $Q_n$ tend to zero. The global transversal tail and the same scale comparisons keep the connector inside the buffered rectangle. If $k=n/m$, summing the $k+1$ connector error allowances costs at most $(k+1)Q_n/(2k)\le Q_n$. Summing the middle-path gains gives $kQ_m\ge2R^{10}Q_n$. Therefore the corrected concatenation bound is

$$
X^{\omega'}_{\gamma'}
\le\mu(n-2n^{8/10})-2R^{10}Q_n+Q_n+o(Q_n)
\le\mu(n-2n^{8/10})-R^{10}Q_n.
$$

The last line on page 73 prints $\ge$ instead of the required $\le$ and drops the factors $Q_n$ attached to $R^{10}$. This display gives the correct direction and factors. The intersections over connector events must include $i=0$, and the concatenation must list $\gamma_2$ after $\widehat\gamma_1$, rather than repeating $\gamma_1$.

**Conditional dependency.** With these changes, Lemma 10.9's construction gives the favorable-path probability from the stated record and transversal inputs. The original printed construction does not. Its conclusion is used only through $H_{i,j}$ in Lemma 10.10 and Proposition 10.11.

### 5.6. Signs and endpoints in the detour substitutions

**Proved algebraic corrections.** These are distinct occurrences of the same reversal of a path improvement.

| Locator and printed claim | Correct consequence and proof | Downstream use |
| --- | --- | --- |
| Lemma 10.6, page 68: the isolated subarc inequality ends with $X^\gamma_{w_1d_1}+3\Gamma-Q_n$. | Cancelling the unchanged exterior subarcs gives $X^{\gamma'}_{d_1d_2}\le X^\gamma_{d_1d_2}+3\Gamma-Q_n$. The index $w_1d_1$ on the competing path is incorrect. Substitution then gives $X_{\check\gamma}\le X_\gamma+6\Gamma-Q_n\lt X_\gamma$. | This repairs the contradiction used to rule out the excursion in Lemma 10.6. |
| Lemma 10.7, page 69: $X_{\check\gamma}\le X_\gamma-6\Gamma_{10Mn}+Q_n\lt X_\gamma$. | The preceding line gives $X^\gamma_{d_1d_2}\ge X^{\gamma'}_{d_1d_2}-3\Gamma_{10Mn}+Q_n$, so the replacement costs at most $X^\gamma_{d_1d_2}+3\Gamma_{10Mn}-Q_n$. Thus $X_{\check\gamma}\le X_\gamma+6\Gamma_{10Mn}-Q_n\lt X_\gamma$. | The error is small because $Q_n\ge c n^\alpha$ and $\Gamma_{10Mn}\le n^\epsilon$, with $\epsilon\lt \alpha$. Proposition 10.5 needs this corrected direction. |
| Lemma 10.10, page 74: $X^{\omega^{ij}}_{v_bv_c}\le\mu(n-n^{8/10})-R^{10}Q_n$. | The definition of $H_{i,j}$ has length $n-2n^{8/10}$. That stronger bound, transferred by the corrected $G^{(3)}$, is required to cancel both end pieces of length $n^{8/10}$. | Without the $2$, the cancellation on page 75 does not follow from the cited inequality. |
| Lemma 10.10, page 74: the second short connector is written $X^{\omega^{ij}}_{v_du_3}$. | It is $X^{\omega^{ij}}_{v_du_2}$, as used in the final concatenation. The endpoint $u_3=(Mn,0)$ is far away. | Unique endpoint correction in the six-piece route of page 75. |
| Lemma 10.10, page 75: $X^{\omega^{ij}}_{u_0u_1}\le X_{u_0u_1}-n^\epsilon$ and the corresponding inequality for $u_2,u_3$. | The absolute-value definition of $G^{(2)}$ gives $\le X_{u_0u_1}+n^\epsilon$, and similarly for $u_2,u_3$. | Replacing a negative error by the correct positive error changes only the $O(n^\epsilon)$ term in the gain. For example the gain is at least $[R^{10}-8\mu R^2-3R-2]Q_n-Cn^\epsilon$, which is at least $R^{10}Q_n/2$ after choosing $R$ and then $n$ large. |

The lower bound for $X_{u_1u_2}$ on page 73 does use a lower norm deviation. The definition of $C^{(3)}$ on page 61 contains absolute-value bars, so that particular inference is valid; omission of those bars in text extraction would produce a spurious additional objection.

### 5.7. The measurability assertion in Proposition 10.11 is incomplete

**Proved defect.** Immediately after (103), on page 75, the proof says that $C^{\mathrm{loc}}_{i,j}$ and $H_{i,j}$ are measurable with respect to $\omega_{\Lambda^{++}_{i,j}}$ and $\omega'_{\Lambda_{i,j}}$. As defined on page 62, $C^{\mathrm{loc}}_{i,j}$ also uses the independent outside completion $\omega^{\mathrm{loc}}$. In the abstract setting $H_{i,j}$ is defined using full-environment costs in $\omega'$, so Assumption 12 gives high-probability locality, not deterministic measurability in the block.

**Proved repair.** In the conditional resampling identity, condition additionally on the full independent completion $\omega^{\mathrm{loc}}$ and on the full fresh field $\omega'$. These independent variables do not change conditional expectations of the original $X$ when the original revealed noise is fixed. The conditional expectation of $X-X^{\omega^{ij}}$ still depends on the fresh field only through its block restriction. Thus its squared norm is unchanged by the enlarged conditioning. Both indicators are now measurable, so insertion of their product in the squared conditional expectation is valid. The Jensen and fourth-moment bounds (104)–(105) are unchanged. Equivalently, include all auxiliary independent noise in the initial sigma-field of the martingale on pages 76–77; $X$ is independent of that initial field, so its initial conditional expectation is constant. This gives a complete justification of this conditioning step without assuming exact locality beyond the printed hypotheses.

### 5.8. The factor depending on $\Theta$ is dropped in Theorem 10.12

**Proved correction.** Equations (106) and the power-mean step give, for $K\le CM^{8/5}$,

$$
\mathop{\mathrm{Var}}X_{Mn}
\ge\frac{R^{20}Q_n^2}{8K}
\left(\frac{\delta M}{80\Theta^2}-2KM^{-40}\right)^2
\ge c\delta^2R^{20}\Theta^{-4}M^{2/5}Q_n^2
$$

for sufficiently large $M$. The printed next line on page 77 omits $\Theta^{-4}$ in writing $C_1Q_n^2M^{2/5}$. A constant independent of $M$ cannot absorb this factor, because $\Theta$ grows as a fixed power of $\log M$. Retain it instead. Since $\Theta\le2\lceil\log^{1000/\epsilon^2}M\rceil$ for large $M$, the quantity $\Theta^{-4}M^{1/5}$ tends to infinity. The corrected bound still contradicts $Q_{Mn}^2\le M^{1/5}Q_n^2$ by (5), after choosing $M$ large. Thus this omission is repairable and does not cost the record-growth conclusion. It must be tracked rather than absorbed into a uniform constant.

The middle sum on page 76 also changes its index endpoint from $M$ to $n$. All these indices refer to columns, and must retain $M$. The final square-root lower bound for $\mathop{\mathrm{SD}}X_n$ on page 78 has $\delta$ rather than $\sqrt\delta$; decreasing the constant makes the weaker displayed conclusion valid when $0\lt \delta\le1$.

## 6. Section 11: incorrect centering and the final tail direction

### 6.1. The short endpoint rectangles are centered at the wrong length

**Proved error.** On page 79, both $G_\zeta$ and $G_\zeta^*$ are defined using the conditions

$$
|Y^{\pm}_{R_{\zeta n}}-n\mu|\le\epsilon'Q_n/10,
\qquad
|Y^{\pm}_{R_{\zeta n}^*}-n\mu|\le\epsilon'Q_n/10.
$$

Their rectangles have horizontal length $\zeta n$, not $n$. Lemmas 4.6 and 4.8 center these quantities at $\zeta n\mu$. For fixed $0\lt \zeta<1/3$, the difference $(1-\zeta)n\mu$ is of order $n$, whereas $Q_n=O(\sqrt n)$. In particular the asserted high-probability bounds for these printed events are false: those lemmas imply $Y^\pm_{R_{\zeta n}}/n\to\zeta\mu$ in probability, so the printed events have probability tending to zero.

**Proved unique correction, conditional on Lemmas 4.6 and 4.8.** Replace $n\mu$ by $\zeta n\mu$ in all four conditions. Then their failure probabilities are at most $2\exp\{1-c(\epsilon'Q_n/Q_{\zeta n})^\theta\}$ and are small by $Q_{\zeta n}/Q_n\le\zeta^\alpha$. The proof compares endpoint connectors of the same length, so their deterministic centers cancel after this correction. The subsequent sentence “so $\mathbb P[G_\zeta]\lt \epsilon'/10$” must have $G_\zeta^c$. The symbol $C_i$ at the bottom of page 79 must be the event $E_i$ just defined.

**Proved dependency.** These events are used in the contradiction proving Lemma 11.2 on page 80. Lemma 11.2 feeds both Lemma 11.3 and Proposition 11.1, so both lower bounds need the corrected events. The independent-resampling convention required there is already stated on page 4: each outside completion is independent. Disjoint retained regions then do give independent full hybrid environments. That independence is not an additional defect.

### 6.2. The concatenation argument in Lemma 11.3 controls the wrong path

**Proved error.** Page 80 defines $\gamma'$ to be a path minimizing subject to confinement in the $\delta W_{Mn}$ neighborhood, and then gives a probability bound that this same $\gamma'$ is confined. That event holds by definition. The needed event is that the concatenation $\gamma$ of the $M$ short geodesics is confined, which gives $X_\gamma\ge X_{\gamma'}$.

The same paragraph writes $\delta W_{Mn}\ge\delta M^{1/2+\alpha}W_n$. The regular growth definition gives only $W_{Mn}/W_n\ge M^{(1+\alpha)/2}$. The exponent on $\alpha$ is missing a factor of $1/2$.

**Proved replacement, conditional on a valid Theorem 5.4 and Lemma 11.2.** Choose $M$ so large that

$$
M\,\mathbb P\left(V_n\gt \delta M^{(1+\alpha)/2}W_n\right)\lt \delta/2,
$$

where $V_n$ is distance from the segment, or use a valid segment-distance version of the Section 5 bound. A union bound over the short geodesics shows that their concatenation lies in the larger tube with probability at least $1-\delta/2$. On that event $X_\gamma\ge X_{\gamma'}$. Lemma 11.2 at scale $Mn$ now gives $\mathbb P(X_\gamma\ge X_{Mn}+\delta Q_{Mn})\ge\delta/2$. Always $X_\gamma\ge X_{Mn}$, so

$$
M\mathbb EX_n\ge\mathbb EX_\gamma
\ge\mathbb EX_{Mn}+\frac{\delta^2}{2}Q_{Mn}
\ge\mu Mn+\frac{\delta^2}{2}M^\alpha Q_n.
$$

The first inequality follows from the concatenation inequality in Assumption 7. The printed equality $\mathbb EX_\gamma=M\mathbb EX_n$ on page 81 is unnecessary and is not guaranteed for all the listed discrete conventions. The display proves the desired large-scale lower mean bound with coefficient $\delta^2/(2M^{1-\alpha})$. Extending a positive lower bound to every real $n\ge1$ additionally requires positive mean excess on compact scale intervals; that final compact-scale issue is not verified here.

**Proved additional qualification, conditional on the first-branch shape event and Assumption 8.** Lemma 11.2's “in particular” statement concerns distance from the line, whereas $\Psi_{n,\delta}$ is defined using distance from the segment. This is not an immediate set inclusion: a path can leave the segment neighborhood by a longitudinal overshoot. The missing estimate follows from the first-branch event with a fixed parameter. First, a geodesic leaving $B_{3n}(0)$ has a chord excess of order $n$, which contradicts its $O(n^\epsilon Q_n)$ metric error there. Inside that ball, a longitudinal overshoot of at least $\delta W_n/2$ has chord excess at least $\delta W_n$. Assumption 8 and the shape event bound that excess by $O(n^\epsilon Q_n)$, again a contradiction for fixed $\delta>0$ and large $n$, since $W_n/Q_n\ge cn^{1/4}$. Thus the probability of such an overshoot tends to zero. A path with line distance at most $\delta W_n/2$ and longitudinal overshoot at most $\delta W_n/2$ has segment distance less than $\delta W_n$. Applying Lemma 11.2 and decreasing its constant therefore gives the stated positive-probability line fluctuation. This supplies the missing segment-to-line justification rather than identifying the two definitions.

### 6.3. The tail substitution in Lemma 11.4 does not give a small error

**Proved gap.** On page 81, in the proof of (109), the first-moment truncation uses threshold $\delta^{3\alpha/7}Q_n$, and the ensuing probability bound leaves an unspecified $x$ in

$$
\delta^{-1/2}\exp(-cx^\theta\delta^{-3\alpha\theta/7}).
$$

At that truncation threshold one must set $x=\delta^{3\alpha/7}$. The expression then becomes $\delta^{-1/2}e^{-c}$, which does not tend to zero. Thus the last inequality in the printed proof is not justified by the preceding estimate. Assigning a value to the free $x$ is insufficient to repair it.

**Proved replacement, conditional on Lemma 9.4 and the rectangle moment bounds.** Put $r=3\alpha/14$ and truncate at $\delta^rQ_n$. For $0\lt \delta<1$, the new threshold is larger than $\delta^{3\alpha/7}Q_n$, so it is in the range of Lemma 9.4. Its probability bound is now

$$
\mathbb P(|Y^-_{R_{n,\delta W_n}}-X_n|\ge\delta^rQ_n)
\le C\left[e^{-\delta^{-\epsilon\theta/4}}
+\delta^{-1/2}e^{-c\delta^{-3\alpha\theta/14}}
+e^{-n^{\kappa/100}}\right].
$$

The first two terms tend to zero as $\delta\downarrow0$. The second moment of the difference is at most $C_1Q_n^2$, uniformly in small $\delta$: both the thin-rectangle minimum and $X_n$ lie between the canonical rectangle's minimum and maximum, whose centered second moments are bounded by Lemmas 4.6 and 4.8. Cauchy–Schwarz gives

$$
\frac{\mathbb E|Y^-_{R_{n,\delta W_n}}-X_n|}{Q_n}
\le\delta^r+C_1^{1/2}
\mathbb P(|Y^-_{R_{n,\delta W_n}}-X_n|\ge\delta^rQ_n)^{1/2}.
$$

Choose $\delta$ small and then $n$ sufficiently large. The right side is at most $D_4/2$, proving (109) and the intended conclusion of Lemma 11.4 from its stated inputs. This repairs a tail-scale gap with a change of truncation exponent; it is not just deletion of an undefined variable. The corresponding scale comparison printed on page 54 is $Q_{\varepsilon n}\le\varepsilon^{-\alpha}Q_n$; the useful and valid comparison is the stronger $Q_{\varepsilon n}\le\varepsilon^\alpha Q_n$, directly from the regularized envelope.

### 6.4. The last concentration inequality proves the wrong tail

**Proved error.** Equation (110) on page 82 asks for an upper bound on a lower deviation of $S=\sum_iY_{i,\delta}^{-,\Lambda_{i,\rho}}$. The final unnumbered display instead bounds

$$
\mathbb P\left(S-\mathbb ES\ge\tfrac12c\rho^{-1}Q_{\rho n}\right)\le\varepsilon/8.
$$

This does not imply (110). The event in (110), by the preceding mean bound, is contained in $\{S-\mathbb ES\le-c\rho^{-1}Q_{\rho n}/2\}$.

**Proved unique correction, conditional on the stated mean and second-moment estimates.** Replace $\ge$ by $\le$ and insert a minus sign before the threshold. No concentration theorem beyond a variance calculation is needed. The independent summands satisfy $\mathop{\mathrm{Var}}Y_{i,\delta}^{-,\Lambda_{i,\rho}}\le C_0Q_{\rho n}^2$ by integrating the stated stretched-exponential bound. There are $\rho^{-1}$ summands. Chebyshev's inequality gives

$$
\mathbb P\left(S-\mathbb ES\le-\tfrac12c\rho^{-1}Q_{\rho n}\right)
\le \frac{4C_0\rho}{c^2}.
$$

Choose $\rho\le c^2\varepsilon/(32C_0)$. This proves (110) from those inputs.

## 7. Additional errors at the definition and dependency interfaces

### 7.1. The maximum in the definition of transversal fluctuation

**Proved typographical error.** Page 12, equation (7), says that distance from the line is equivalently

$$
\mathcal W_{uv}:=\left|\max_{w\in\gamma_{uv}}e\cdot(w-u)\right|,
$$

where $e$ is a perpendicular unit vector. It must be $\max_{w\in\gamma_{uv}}|e\cdot(w-u)|$. For a path whose endpoints lie on the horizontal axis and which visits $(n/2,-1)$ without going above the axis, the printed expression with $e=e_2$ is zero, whereas distance from the line is one. The corrected formula is independent of the sign of $e$. The statements about both positive and negative excursions in Sections 5 and 8 require this correction. Distance from the segment, used by $\Upsilon$ on page 35, is a stronger confinement quantity than distance from the line and does control the corrected definition.

### 7.2. The initial concentration constant is inverted

**Proved constant correction.** On page 12, immediately before and in (4), the upper bound is printed with coefficient $D_0^{1/\kappa}$. Assumption 4 has exponent $-D_0x^\kappa$, so the direct consequence is instead

$$
\widehat Q_n\le D_0^{-1/\kappa}\sqrt n,
\qquad Q_n\le D_0^{-1/\kappa}\sqrt n.
$$

For $x\ge1$, substitute $xD_0^{-1/\kappa}$ into Assumption 4 and use $x^\kappa\ge x^\theta$; for $x<1$ the target tail bound exceeds one. Taking the regularizing supremum gives the bound for $Q_n$, since $\alpha<1/2$. The positive power printed in (4) is not the consequence of Assumption 4 and can fail when that assumption's valid constant is decreased. All the arguments above use $C\sqrt n$, so this inversion changes no power exponent.

### 7.3. The logarithmic error bounds need a base-scale qualifier

**Proved endpoint qualification.** Assumption 11 on page 8 gives threshold $x\log^{1/\kappa}n$ without an explicit lower base-scale restriction. At $n=1$ its threshold is zero. Letting $x\to\infty$ would force all the indicated passage times to be unchanged almost surely by exterior resampling. This does not hold in the finite-range Gaussian Riemannian model when the kernel crosses the boundary of the width-one strip. For example, shifting a nonnegative Gaussian direction just outside the source boundary raises the density on a small ball about the source and cannot lower it elsewhere. Strict increase of $\psi$ makes the cost increase uniformly on a smaller source ball. Every path to the opposite boundary must cross that ball, so the passage time is a nonconstant function of this outside direction. It cannot be invariant under independent resampling of the outside field. This is also the base-scale qualification recorded in the independent model verification.

The intended repair is to require Assumption 11 only for sufficiently large $n$, or to use $\log(2+n)$ in an all-scale statement and verify that statement. The large-block uses in Sections 7, 9, 10 and 11 have $n$ tending to infinity, and do not need a statement at $n=1$. This endpoint qualification should not be confused with the substantive large-$z$ defect in Lemma 5.2.

**Proved related error.** Lemma 2.1 on page 13 explicitly says “for any $n\ge1$” and bounds $\mathbb P(\Gamma_n\gt Cx\log^Cn)$ by $\exp(1-x^\kappa)$. At $n=1$ this would force $\Gamma_1=0$ almost surely. In a Riemannian metric with density at least $d_->0$, the first maximum in the definition of $\Gamma_1$ is at least $d_-$, by taking two points at Euclidean distance one. Thus the asserted tail has left side one and right side tending to zero. Use a large-scale version or replace the logarithm by $\log(2+n)$ and adjust constants. All uses audited above have large base scales and survive this endpoint correction.

### 7.4. The concrete-model assertion needs nondegeneracy

**Proved literal counterexample to Theorem 1.1.** Page 6 permits a smooth nonnegative radial compactly supported kernel $K$ without requiring $K\not\equiv0$. With $K=0$ the Riemannian density is the deterministic constant $\psi(0)$, so $X_n=\psi(0)n$ and $\mathop{\mathrm{Var}}X_n=0$. Theorem 1.1 on page 8 says that all the described models satisfy the Section 1.2 assumptions, including Assumption 9's positive polynomial variance lower bound. It is false for this permitted choice. Require a nondegenerate metric in that concrete-model assertion; for Gaussian noise, a nonzero kernel and a nonconstant density map are sufficient in the independent verification cited above. This does not refute Theorems 1–3 under their stated Section 1.2 hypotheses, since the deterministic model fails those hypotheses. The deferred verification of Theorem 1.1 is separate from the main proof audited here.

### 7.5. The Section 12 proxy omits two endpoint intervals

**Proved mismatch.** The first page of Section 12, page 82, claims $D_{i,j}\subset C_{i,j}$. Its $D^{(2)}$ intersection runs over $j-R\le j'\le j+R$. The target $C^{(2)}$ on page 61 runs over $j-R-1\le j'\le j+R+1$. The missing two endpoint intervals are not supplied by the stated intersections. Moreover, the use of Lemma 8.2 there includes the $k=0$ issue already recorded above.

**Conditional local repair.** Enlarge the $D^{(2)}$ range by those two endpoint indices and use a local-deviation statement covering $k=0$. For fixed $R$ this adds a fixed number of factors. The ensuing probability estimates must be checked with the enlarged event. The percolation proof in Section 12 has not been checked line by line here, so this observation is not a certification that no further change is needed in it. On page 86, the union bound also prints $\mathbb P(B)\ge1-M^{1000}$ where the preceding estimates give $1-M^{-1000}$ after adjusting constants.

## 8. Dependencies of the main theorems

**Proved dependency audit.** The following table describes printed dependencies, not the truth or falsehood of the conclusions.

| Conclusion | Printed route | Consequence of the defects |
| --- | --- | --- |
| Theorem 1 | Page 78 uses Proposition 10.13 and the definition of $\widehat Q_n$. Proposition 10.13 uses Theorem 10.12 and Proposition 9.2. | It inherits the record, local-deviation, localization and resampling corrections in Sections 7–10 and the required Section 12 input. |
| Theorem 2(i) | Page 78 uses Theorem 5.4 and Proposition 10.13. | It has the direct unrestricted Section 5 dependency as well as the variance-comparison dependency. |
| Theorem 3, upper bound | Page 78 uses Lemma 4.4 and Proposition 10.13. | Lemma 4.4 is not affected by the false large-parameter branch, but the printed proof of Proposition 10.13 has the dependencies above. |
| Theorem 3, lower bound | Pages 80–81 use Lemmas 11.2–11.3 and Proposition 10.13. | It additionally needs the corrected short-rectangle centers and the corrected concatenation event. |
| Theorem 2(ii) | Pages 78 and 81–82 use Proposition 11.1, Lemma 11.4, Lemma 11.3 and Proposition 10.13. | It is also affected. The final lower-tail direction is wrong as printed. It is not independent of the defects merely because it is not listed among the first three immediate Section 5 dependencies. |
| Propositions 2.2 and 2.3 | Page 78 uses Proposition 10.13 together with the earlier rectangle and lower-tail estimates. | The same variance-comparison dependencies remain. |

**Proved unaffected interfaces.** The false second branch of $S$ is introduced after the results of Sections 3 and 4. Those earlier statements do not acquire a dependency on it. The apparent forward citation in Lemma 5.1 can be replaced by the already available Lemma 4.5, as shown above. The direct $S$ uses in the block proof listed in Section 1.3 are small-parameter uses. These facts explain why removing the false branch may be possible, but they do not certify the full proof. No theorem about an unrelated lattice model, and no OpenAI theorem about exponential lattice FPP, is needed in this audit.

## 9. What was checked and what remains conditional

**Proved scope of source inspection.** The local PDF was read and searched directly. The formulas underlying the principal findings were checked against rendered pages 34, 37, 42–45, 47, 50–51, 63–64, 70, 72, 74–75, 79 and 82. Printed page numbers agree with PDF page numbers in this version.

| Source portion | Line-by-line verification completed here | What was only inspected or spot-checked |
| --- | --- | --- |
| Section 5, pages 33–38 | The event definitions, Lemma 5.2's union-bound setup, the first large-detour comparison in Lemma 5.3, the formula for $r_j$, the last event inclusion on page 37, and the implication asserted in Theorem 5.4 were checked display by display. The contradiction in Section 1.2 and the coarse replacement in Section 1.4 are proved here. | The full small-parameter chaining proof with all constants $1000$, $500$, $20$ and arbitrary $\mu$ was read but is not certified. Its constants and the all-path decomposition must be treated as further proof obligations. |
| Section 7, pages 41–45 | The saturation inference, the corrected variance and anti-concentration argument, the record-scale inequalities, the truncation algebra, the bounded-difference step, and the final deterministic-center substitution were checked. | Exact real-scale record attainment in the full abstract class and the imported percolation estimates used for (90)–(91) were not reproved. |
| Section 8, pages 46–51 | The endpoint classes, strip coordinates, union-bound direction, the large-parameter crossover and its failed transition, and the event inclusion needed for (93) were checked. | The detailed geometric inequalities in Case 1 were inspected, but neither the entire Case 1 proof nor a corrected unrestricted Case 2 is certified. |
| Section 10, pages 59–78 | All pages were read. The definitions and their stated inclusions, the event/environment comparisons, the specific substitutions listed in Section 5, the favorable-path dimensions and cost sum, the conditional-variance identity with its measurability repair, the fourth-moment estimate, and the power-mean exponents were checked. | The planarity and path-splicing arguments of Lemmas 10.2 and 10.6–10.7 are conditional on their explicit geometric and path-decomposition inputs. The proof of Proposition 10.1 is deferred to Section 12 and was not re-proved. |
| Section 11, pages 78–82 | The centers in $G_\zeta,G_\zeta^*$, the corrected two-copy comparison at the level of its stated inputs, the corrected concatenation and mean inequality, the repaired truncation exponent in (109), and the final lower-deviation argument were checked. | Lemma 9.4's full proof and the resulting thin-rectangle estimate were used as conditional inputs. Compact-scale positivity needed for an all-real-$n$ lower mean statement was not checked. |
| Other dependencies | The statements of the standing assumptions, the definitions on pages 4 and 11–13, Lemmas 4.4–4.5, Proposition 9.2's record-scale interface, Lemma 9.4's use of Corollary 8.3 on page 54, and the direct $S$ uses on pages 82–90 were checked at the cited interfaces. | Sections 3–4, 6, 9, 12 and 13 were not independently refereed in full. The model-verification proof of (MV29) was checked at its statement, independence declaration, projection calculation and exponent; its entire local-modification construction was not re-refereed. |

The status “proved” attached to a correction means that the displayed implication or counterexample has been established. A correction whose use depends on an earlier lemma retains the explicit conditional marker. None of these labels means that the entire corrected paper has been refereed.

## 10. Summary for the authors

**Proved findings.** The large-parameter event in Lemma 5.2 is false at the printed scale. The contradiction can be made directly at the level of the variance, without using Theorem 3. The bad event $B^{(3)}$ in Lemma 10.4 occurs deterministically because equal endpoint columns are not excluded. Separately, the high-probability interior equality in Lemma 10.8 compares the wrong environments and has probability zero in a nondegenerate smooth Gaussian example. The record proof contains an unjustified exact-saturation assertion, a vacuous scale range, and a reversed truncation. The local proof contains reversed strip indices, an undefined crossover with a further transition inconsistency, and a reversed corollary. The block proof needs the symmetric direction of localization agreement, corrected path substitutions, correctly sized favorable rectangles and connector costs, and an explicit conditioning argument. The lower-bound proof uses the wrong deterministic centers for its short rectangles, an insufficient truncation scale in Lemma 11.4, and the wrong final deviation direction.

**Conditional repair assessment.** The local changes proved above repair several of these steps from their stated inputs. A coarse metric estimate supplies a valid substitute for the large global-detour argument. For bounded metrics, the earlier referee's monotonicity argument also recovers a global transversal tail from the small-parameter branch, with a smaller positive exponent. Neither argument is a correction of the false event itself. The remaining task is to state and prove a corrected local-deviation lemma in the parameter range actually needed, including $k=0$, then propagate the corrected events and verify the deferred percolation argument. Alternatively, restrict every local invocation to the first branch and prove that this restriction suffices throughout the argument, with the other corrections applied. Exact record attainment and arbitrary-path decomposition should be made explicit where needed.

**Theorem status.** The printed proofs of all three main theorems are affected, including both parts of Theorem 2. Their conclusions under the Section 1.2 hypotheses are not refuted by this audit. The separate concrete-model assertion, Theorem 1.1, needs a nondegeneracy qualification because its literal model definition permits a zero kernel. The earlier Section 3–4 interfaces are not affected by the false large-parameter branch; their complete correctness was not reassessed here. A corrected proof for the full model class, rather than an assertion that all discrepancies are typographical, is needed before claiming that every main theorem follows from the axioms exactly as printed.
