# The Third Borwein Conjecture for $n\ge31{,}147$

## Abstract

Let

```math
B_n(q)=\prod_{\substack{1\le j\le 5n\\5\nmid j}}(1-q^j)
      =\sum_{m=0}^{10n^2}c_n(m)q^m.
```

We prove that, for every integer $n\ge31147$, the coefficient $c_n(m)$ is nonnegative when $5\mid m$ and nonpositive otherwise. We also determine all zero coefficients in this range. The proof combines a Rogers--Ramanujan 5-dissection at the low-degree edge, explicit saddle-point estimates near the two edges, and a finite-product Fourier estimate in the interior. Reciprocal symmetry supplies the upper half of the polynomial. A Lean 4 development mechanically checks the final theorem and its analytic dependencies; it is supporting verification rather than a substitute for the mathematical argument presented here. No assertion about $n<31147$ is made or needed.

## Related work

Chen Wang proved the first Borwein conjecture by analytic methods [CW]. Wang and Krattenthaler subsequently developed a saddle-point approach giving a new proof of the first conjecture and a proof of the second [WK]. Their discussion of the modulus-five third conjecture, in §11, identifies the residue classes $3,4\pmod5$ as requiring sharper estimates because the corresponding infinite-product coefficients vanish. Liuquan Wang's Proposition 3.6 records this vanishing explicitly [LW]. The present argument uses these identities before coefficient extraction and combines the four fifth-root contributions before estimating their magnitudes. This preserves cancellation in the estimates needed to cover every coefficient for $n\ge31147$, including the two weak residue classes. The claim here is this explicit large-$n$ theorem and its zero classification; a comprehensive novelty or priority determination is not claimed.

## 1. Statement of the result

The product has $4n$ factors and degree

```math
D=\sum_{\substack{1\le j\le5n\\5\nmid j}}j=10n^2.
```

Because $4n$ is even, replacing $q$ by $q^{-1}$ gives

```math
c_n(m)=c_n(D-m). \tag{1.1}
```

Our main result is the following.

**Theorem 1 (large-$n$ sign theorem).** For integers $n\ge31147$ and $m\ge0$,

```math
\left(\mathbf 1_{5\mid m}-\mathbf 1_{5\nmid m}\right)c_n(m)\ge0. \tag{1.2}
```

Thus $c_n(m)\ge0$ if $5\mid m$, and $c_n(m)\le0$ if $5\nmid m$. For $m>D$ the assertion is immediate because the coefficient is zero.

The inequalities inside the degree can be sharpened to an exact zero classification. Define

```math
Z_n^-=\{5j+3,5j+4:0\le j<n\}\cup\{7,5n+8,5n+9\} \tag{1.3}
```

and

```math
Z_n=Z_n^-\cup\{D-r:r\in Z_n^-\}. \tag{1.4}
```

**Theorem 2 (zero set).** If $n\ge31147$ and $0\le m\le D$, then

```math
c_n(m)=0\quad\Longleftrightarrow\quad m\in Z_n. \tag{1.5}
```

Moreover, the two parts of (1.4) are disjoint and

```math
|Z_n|=4n+6. \tag{1.6}
```

The threshold is the first integer allowed by the explicit endpoint constants used below. We do not claim it is optimal for this method. The paper concerns only $n\ge31147$; it neither proves nor assumes the sign conjecture for smaller $n$.

## 2. Infinite-product cancellation and the first tail

Write

```math
G(q)=\frac{(q;q)_\infty}{(q^5;q^5)_\infty},\qquad
T_n(q)=\prod_{\substack{j>5n\\5\nmid j}}(1-q^j)^{-1},
\qquad B_n(q)=G(q)T_n(q). \tag{2.1}
```

For

```math
R_t(Q)=\sum_{j\ge0}\frac{Q^{j^2+(t-1)j}}{(Q;Q)_j},
\qquad g=R_1,\quad h=R_2,
```

the classical Rogers--Ramanujan 5-dissection is

```math
G(q)=g(q^5)^2-qg(q^5)h(q^5)-q^2h(q^5)^2. \tag{2.2}
```

The coefficients of the three series in $q^5$ are nonnegative. In particular,

```math
[q^{5j+3}]G=[q^{5j+4}]G=0. \tag{2.3}
```

For the two weak residue classes, cancellation is therefore imposed before coefficient extraction:

```math
c_n(m)=[q^m]G(q)(T_n(q)-1),\qquad m\equiv3,4\pmod5. \tag{2.4}
```

This identity is used on the whole coefficient contour. Retaining $T_n-1$ is essential because its small size controls both the main arcs and the complementary arcs.

The recurrences $R_t=R_{t+1}+Q^tR_{t+2}$ give the formal-series identity

```math
\mathcal D(Q):=\frac{gh+h^2-g^2}{1-Q}
=\sum_{j\ge0}Q^{2j(j+1)}R_{2j+2}R_{2j+3}
=\sum_{K\ge0}d_KQ^K. \tag{2.5}
```

Consequently $d_0=1$, $d_1=0$, and $d_K>0$ for $K\ge2$. Expanding the first block of the finite tail yields, exactly,

```math
c_n(5n+5K+a)=-d_K,\qquad
a\in\{3,4\},\quad0\le K\le n-1. \tag{2.6}
```

Together with (2.2), this proves the required signs at the lowest degrees and identifies the lower zeros $5j+3$, $5j+4$ for $0\le j<n$, as well as the exceptional zeros $7$, $5n+8$, and $5n+9$. The restriction $K\le n-1$ in (2.6) is part of the statement and is not silently extended.

## 3. The endpoint saddle

Put

```math
h_0(z)=\frac{\operatorname{Li}_2(e^{-z})-\pi^2/6}{z},
\qquad R(z)=h_0(5z)-h_0(z). \tag{3.1}
```

For real $\tau\ge0$,

```math
R(\tau)=\int_0^1\log\!\left(\sum_{j=0}^4e^{-j\tau x}\right)dx. \tag{3.2}
```

If the five weights are normalized to a probability distribution, differentiation shows

```math
R''(\tau)=\int_0^1x^2\operatorname{Var}_\tau(J)\,dx>0. \tag{3.3}
```

Hence $-R'$ decreases strictly from $1$ to $0$, and the saddle equation

```math
-R'(\tau)=\frac{k}{5n^2} \tag{3.4}
```

has a unique positive solution for $0<k<5n^2$. Set $w_0=\tau/(5n)$. For the strong residue classes $a=0,1,2$ take $k=m$; for the weak classes $a=3,4$ use the shifted index $k=m-5n$, reflecting the first nonzero term of $T_n-1$.

The four dominant fifth-root cusps combine into an explicit signed main term. With

```math
P(n,k)=\frac{\exp\{nR(\tau)+kw_0-w_0/6\}}
 {5\sqrt{2\pi R''(\tau)}\,n^{3/2}}>0, \tag{3.5}
```

the endpoint analysis proves a relative error bounded by

```math
\mathcal E(\tau,w_0)=15\sqrt{w_0}+15e^{-\tau}+60w_0
+50w_0^{-3}e^{-1/(30w_0)}. \tag{3.6}
```

Under

```math
\tau\ge\frac{11}{2},\qquad 0<w_0\le0.0013, \tag{3.7}
```

one has $\mathcal E<0.85<1$. Thus the sign of the main term determines the coefficient. The estimate comes from the eta transformation at the four fifth roots, a first-tail expansion in the weak classes, an all-angle periodic-product gap, and a Gaussian replacement with explicit remainder. The inequalities are uniform over the stated range.

The endpoint ranges meet the exact first-tail range once $n\ge31147$. Numerically, the governing exact comparison is

```math
31146<\frac{2\pi^2/15}{25(0.0013)^2}<31147. \tag{3.8}
```

This explains the stated integer threshold.

## 4. The interior Fourier estimate

It remains to treat the lower-half coefficients for which the saddle satisfies $0\le\tau\le11/2$. Cauchy's formula is applied directly to the finite product on the circle $|q|=e^{-\tau/(5n)}$. The four fifth-root neighborhoods are combined before absolute values are taken. This preserves the residue-dependent phase and, in the weak classes, the small factor already visible in (2.4).

The main phase has the required sign in every residue class. The rest of the circle is controlled by three ingredients:

1. smoothing the logarithm of the finite product and bounding the smoothing loss explicitly;
2. Dirichlet approximation of the angle, followed by separate estimates for nonresonant frequencies and resonant finite sums;
3. denominator-dependent localization, including a combined-difference treatment of the denominator-$5$ cusp.

Near a dominant cusp, Euler--Maclaurin expansion supplies the leading phase and a controlled correction. The local integral is replaced by its Gaussian limit with a uniform error. On the complementary arcs, the localization gap makes the modulus exponentially smaller than the main contribution. The parameter interval $0\le\tau\le11/2$ is divided into 128 rational cells, and the five residue classes are checked using outward rational bounds. Each cell theorem is uniform in $n\ge31147$ and in every coefficient whose normalized position lies in that cell; no enumeration of values of $n$ or coefficients is involved.

The resulting interior estimate is strict:

```math
\operatorname{sgn}_5(m)c_n(m)>0 \tag{4.1}
```

outside the already identified zero positions, where $\operatorname{sgn}_5(m)=1$ for $5\mid m$ and $-1$ otherwise. Full constants, the localization lemmas, and all uniform error budgets appear in the accompanying [analytic derivation](proof/analysis.md), §§7--9.

## 5. Completion and zeros

Fix $n\ge31147$. By (1.1), it is enough to consider $0\le m\le5n^2$. The low-degree identities of §2 cover $m\le5n$ and the first weak tail. If the normalized coefficient position is below the boundary $-R'(11/2)$, the endpoint estimate of §3 applies. At or above that boundary, the interior estimate of §4 applies. These cases cover the lower half, and reciprocal symmetry covers the upper half. This proves Theorem 1.

The low-degree and first-tail identities show that every member of $Z_n^-$ is a zero. The strict endpoint and interior inequalities show that there are no further zeros in the lower half. Reflection gives precisely the second set in (1.4). Every member of $Z_n^-$ is strictly below $5n^2$ for $n\ge2$, so the lower set and its reflection are disjoint. The two progressions contribute $2n$ elements and the exceptional set contributes three, whence $|Z_n^-|=2n+3$ and $|Z_n|=4n+6$. This proves Theorem 2.

## 6. Supporting Lean verification

The accompanying Lean 4 source tree formalizes the same large-$n$ result. The principal declarations are:

| Mathematical statement | Lean declaration | Hypotheses |
|---|---|---|
| Lower-half weak sign | `Borwein.CertifiedLargeN.half_integer_sign` | `31147 ≤ n`, `m ≤ 5*n^2` |
| All coefficients, including those beyond the degree | `Borwein.CertifiedLargeN.coefficient_sign` | `31147 ≤ n` |
| Strict lower-half sign off the listed zeros | `Borwein.CertifiedLargeNZeroHalf.strict_sign_of_not_mem` | `31147 ≤ n`, `m ≤ 5*n^2`, `m ∉ lowerZeros n` |
| Lower-half zero equivalence | `Borwein.CertifiedLargeNZeroHalf.zero_iff` | `31147 ≤ n`, `m ≤ 5*n^2` |
| Full zero equivalence inside the degree | `Borwein.CertifiedLargeNZeroSet.coefficient_zero_iff` | `31147 ≤ n`, `m ≤ totalDegree n` |
| Full zero-set equality and count | `Borwein.CertifiedLargeNZeroSet.zero_set_eq`, `zero_count` | `31147 ≤ n` |

The formal proof uses the same division into an initial range, endpoint region, and interior region. In `CertifiedLargeN.half_sign`, the interior hypothesis is the normalized inequality

```math
-R'(11/2)\le \frac{m}{5n^2}\le1, \tag{6.1}
```

while its complement is passed to the endpoint theorem; the weak endpoint uses $(m-5n)/(5n^2)$. The zero theorem adds the strict sign result outside the explicitly defined finite set and then reflects across degree $10n^2$. These declarations take no hypothesis about coefficients with $n<31147$ and no finite-computation premise.

All 451 local source modules in this edition were rebuilt in an empty output tree using Lean 4.32.2 and the pinned third-party library binaries. A subsequent axiom audit checked the three publication theorems and reported only `propext`, `Classical.choice`, and `Quot.sound`. No previous Borwein compiler artifacts or external numerical data were used. The build record and exact reproduction commands accompany the sources. Lean checks the formal declarations and their dependency chain; whether the definitions faithfully encode the intended coefficient problem remains a mathematical review task.

## 7. Scope and reproducibility

The proof of Theorems 1 and 2 is uniform for all $n\ge31147$. It requires neither a computation through $n=31146$ nor any claim about the conjecture for all $n$. The analytic source includes explicit interval comparisons used to discharge uniform inequalities; those comparisons certify parameter ranges, not a finite table of polynomial coefficients. The Lean supplement contains source code only and has no external binary data dependency.

The detailed mathematical proof is supplied as [proof/analysis.md](proof/analysis.md). Sections 1--10 give the analytic argument; §§11--12 document its interval comparisons and the fixed endpoint threshold. Smaller-$n$ computations and unrelated historical diagnostics are omitted from this edition.

## AI disclosure

OpenAI Codex contributed substantially to the mathematical derivation, formalization, computation of certified bounds, editing, and preparation of the release. Additional parallel AI agents assisted proof and review tasks and preparation of this edition. Suggestions and audit material from other AI systems also informed parts of the work. AI-assisted review is not independent human peer review. No personal author is named.

## References

- **[CW]** Chen Wang, *An analytic proof of the Borwein Conjecture*, Advances in Mathematics **394** (2022), Article 108028. [DOI: 10.1016/j.aim.2021.108028](https://doi.org/10.1016/j.aim.2021.108028); [arXiv:1901.10886](https://arxiv.org/abs/1901.10886).
- **[WK]** Chen Wang and Christian Krattenthaler, *An asymptotic approach to Borwein-type sign pattern theorems*, arXiv:2201.12415 (2022), especially §11. [arXiv record](https://arxiv.org/abs/2201.12415); [author-hosted full text](https://www.mat.univie.ac.at/~kratt/artikel/borwein2.pdf).
- **[LW]** Liuquan Wang, *Sign Changes of Coefficients of Powers of the Infinite Borwein Product*, arXiv:2108.03932, version 3, Proposition 3.6 and its proof (for the 5-dissection used in (2.2)). [Versioned full text](https://arxiv.org/html/2108.03932v3); [arXiv record](https://arxiv.org/abs/2108.03932).
