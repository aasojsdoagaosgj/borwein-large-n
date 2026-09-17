# Analytic derivation for the large-n theorem

This derivation accompanies [paper.md](../paper.md). Its scope is precisely
the coefficient signs and zero classification for $n\ge31147$.
The mathematical displays in §§1--10 retain the integrated analytic source;
the surrounding status text has been updated for this edition. Finite
coefficient runs below the threshold and unrelated historical diagnostics
are omitted. Section numbers are retained for cross-reference to formulas.
The [Lean supplement](../lean/README.md) supplies the formal dependency chain.

## 1. Claims, notation, and proof dependencies

### Theorem A

For integers $n\ge31147$ and $0\le m\le10n^2$,

```math
c_n(m)\ge0\quad(5\mid m),\qquad c_n(m)\le0\quad(5\nmid m).
\tag{1.1}
```

For the same range of $n$, the zero set is

```math
\begin{aligned}
Z_n^-&=\{5j+3,5j+4:0\le j<n\}\cup\{7,5n+8,5n+9\},\\
Z_n&=Z_n^-\cup(10n^2-Z_n^-),\qquad |Z_n|=4n+6.
\end{aligned}
\tag{1.2}
```

The following sections give the analytic argument. The supporting Lean development proves the large-n sign theorem and zero classification; independent human peer review is not claimed.

| Stage | Content | Principal dependencies |
|---|---|---|
| §2–3 | 5-dissection of the infinite product, nonnegative kernel, and first-tail formula | classical identities, formal power series |
| §4–5 | explicit relative error at the endpoint | eta transformation, tail expansion, all-angle gap |
| §6 | endpoint region for $n\ge31147$ | §3, §5 |
| §7–9 | absolute error on the fixed interior interval | phase lower bound, localization of the finite product, Gaussian integral |
| §10 | passage to all coefficients and the zero set | §6, §9, reciprocal symmetry |

We do not assume the implicit eventual theorem from the original notes. Nor do we depend on the earlier notes' theorem for all small primes; the interior estimate for $p=5$ that is needed here is given in this manuscript.

Put $D=10n^2$ and $\zeta=e^{2\pi i/5}$. Since there are $4n$ factors,

```math
c_n(m)=c_n(D-m).
\tag{1.3}
```

Inversion sends a residue class $a$ to $-a\bmod5$, while preserving the desired sign.

The basic functions are

```math
\begin{aligned}
h(z)&=\frac{\operatorname{Li}_2(e^{-z})-\pi^2/6}{z},\\
R(z)&=h(5z)-h(z),\qquad
C=\frac{2\pi^2}{15},\quad A=\frac C5.
\end{aligned}
\tag{1.4}
```

The branch of $h$ is taken from the right half-plane. For real $\tau\ge0$,

```math
R(\tau)=\int_0^1\log\left(\sum_{j=0}^4e^{-j\tau x}\right)dx,\quad
R(0)=\log5,\quad R'(0)=-1,\quad R''(0)=\frac23.
\tag{1.5}
```

Using the weights $\Pr(J=j)\propto e^{-j\tau x}$ gives

```math
R''(\tau)=\int_0^1x^2\operatorname{Var}(J)\,dx>0.
\tag{1.6}
```

Thus $-R'$ decreases strictly from $1$ to $0$. If $0<k<5n^2$, then

```math
-R'(\tau)=\frac{k}{5n^2}
\tag{1.7}
```

has a unique positive solution. The case $k=5n^2$ is treated at $\tau=0$.

## 2. The 5-dissection of the infinite product and the zero residue classes

Define $(a;Q)_j=\prod_{r=0}^{j-1}(1-aQ^r)$. Then

```math
G(q)=\frac{(q;q)_\infty}{(q^5;q^5)_\infty},\qquad
T_n(q)=\prod_{\substack{j>5n\\5\nmid j}}(1-q^j)^{-1},\qquad B_n=GT_n.
\tag{2.1}
```

Let the Rogers–Ramanujan series be

```math
R_t(Q)=\sum_{j\ge0}\frac{Q^{j^2+(t-1)j}}{(Q;Q)_j},\qquad
g=R_1,\quad h_R=R_2
\tag{2.2}
```

The classical sum-product identities [RR] give

```math
g(Q)=\frac1{(Q,Q^4;Q^5)_\infty},\qquad
h_R(Q)=\frac1{(Q^2,Q^3;Q^5)_\infty}.
```

The classical 5-dissection [W21, proof of Proposition 3.6] is

```math
G(q)=g(q^5)^2-qg(q^5)h_R(q^5)-q^2h_R(q^5)^2.
\tag{2.3}
```

This form also follows from the continued-fraction representation in the same reference by setting $Q=q^5$, taking the continued-fraction product ratio to be $h_R(Q)/g(Q)$, and multiplying by $(q^{25};q^{25})_\infty/(q^5;q^5)_\infty=g(Q)h_R(Q)$.

The three series in $Q$ on the right have nonnegative coefficients, and

```math
[q^{5j+3}]G=[q^{5j+4}]G=0.
\tag{2.4}
```

Consequently, if $m\equiv3,4\bmod5$, then exactly

```math
c_n(m)=[q^m]\{G(q)(T_n(q)-1)\}.
\tag{2.5}
```

Equation (2.5) is used in the coefficient integral over the entire circle. It is not an operation that subtracts $G$ only from the main term on the major arc.

Moreover, every coefficient of $g^2$ and $gh_R$ is positive. In $h_R^2$, only the coefficient of $Q^1$ vanishes; those of $Q^0$ and $Q^K$ for $K\ge2$ are positive. The latter follows because every integer $K\ge2$ can be formed from parts $2$ and $3$. Hence $[q^7]G=0$, and we do not invoke an unconditional strict negative sign that would include the small indices.

## 3. A nonnegative kernel and an exact formula for the first tail coefficients

From the definition, canceling the factor $1-Q^j$ in the numerator of the difference and writing $j=i+1$ gives

```math
R_t=R_{t+1}+Q^tR_{t+2}.
\tag{3.1}
```

Put $W_t=R_{t+1}^2-QR_tR_{t+2}$. Substitution of (3.1) yields

```math
W_t=(1-Q)R_{t+1}R_{t+2}+Q^{2t+2}W_{t+2}.
\tag{3.2}
```

Iterating and sending the lowest degree of the remainder to infinity, as a formal power series we obtain

```math
\frac{R_{t+1}^2-QR_tR_{t+2}}{1-Q}
=\sum_{j\ge0}Q^{2j(t+j)}R_{t+2j+1}R_{t+2j+2}.
\tag{3.3}
```

In particular, since $QR_3=g-h_R$,

```math
\mathcal D(Q):=\frac{gh_R+h_R^2-g^2}{1-Q}
=\sum_{j\ge0}Q^{2j(j+1)}R_{2j+2}R_{2j+3}
=\sum_{K\ge0}d_KQ^K.
\tag{3.4}
```

The right-hand side is nonnegative, with $d_0=1,d_1=0$. The $j=0$ term contains $Q^2/(1-Q)$, so $d_K>0$ for $K\ge2$.

Expanding by the number of factors selected from the tail gives

```math
T_n(q)=1+q^{5n}\frac{q+q^2+q^3+q^4}{1-q^5}+O(q^{10n+2}).
\tag{3.5}
```

After multiplication by (2.3), both residue classes 3 and 4 contain $(g^2-gh_R-h_R^2)/(1-Q)=-\mathcal D$. Therefore

```math
\boxed{c_n(5n+5K+a)=-d_K\quad(a=3,4,\ 0\le K\le n-1).}
\tag{3.6}
```

The relevant degrees are at most $10n-1$, so the remainder in (3.5) does not contribute. This formula holds for every $n$ and is not extended to $K\ge n$.


## 4. The endpoint main term and explicit error

Define $\tau,w_0,x_0$ by

```math
-R'(\tau)=\frac{k}{5n^2},\qquad w_0=\frac{\tau}{5n},\qquad x_0=e^{-\tau},
```

and assume

```math
\tau\ge11/2,\qquad 0<w_0\le0.0013
\tag{4.1}
```

The positive main term and error budget are

```math
P(n,k)=
\frac{\exp\{nR(\tau)+kw_0-w_0/6\}}
 {5\sqrt{2\pi R''(\tau)}\,n^{3/2}},
\tag{4.2}
```

```math
\mathcal E(\tau,w_0)=15\sqrt{w_0}+15e^{-\tau}+60w_0
+50w_0^{-3}e^{-1/(30w_0)}.
\tag{4.3}
```

### Endpoint Estimate E

Taking $k=m-5n$ in the two weak residue classes and $k=m$ in the three strong residue classes,

```math
\left|\frac{c_n(m)}{-P(n,m-5n)}-1\right|\le\mathcal E
\quad(m\equiv3,4\bmod5),
\tag{4.4}
```

```math
\left|\frac{c_n(m)}{\sigma_aP(n,m)}-1\right|\le\mathcal E
\quad(m\equiv a\bmod5,\ a=0,1,2),
\tag{4.5}
```

```math
(\sigma_0,\sigma_1,\sigma_2)=\left(\frac{5+\sqrt5}{2},-\sqrt5,-\frac{5-\sqrt5}{2}\right).
```

The error decreases with $\tau$ and increases with $w_0$. Monotonicity of the last term follows from $1/30-3w_0>0$. Hence

```math
\mathcal E\le \mathcal E(11/2,0.0013)
=0.84662267115518262237\ldots<0.85<1.
\tag{4.6}
```

We derive (4.4)–(4.5) in the next section.

## 5. Proof of the endpoint estimate

### 5.1. An all-angle gap for positive-coefficient periodic products

Let $\mathscr P\in\{g^2,gh_R,h_R^2\}$. The product weights have period 5, and their weights on the nonzero residue classes are, respectively,

```math
(2,0,0,2),\quad(1,1,1,1),\quad(0,2,2,0).
```

They satisfy $\sum b_r=4,\sum rb_r=10$. If $0<v\le0.0065$ and $\operatorname{dist}(\theta,2\pi\mathbb Z)\ge3v/4$, then

```math
|\mathscr P(e^{-v+i\theta})|
\le\mathscr P(e^{-v})e^{-1/(5v)}.
\tag{5.1}
```

Indeed, retaining only the first term of the logarithmic series gives a loss of at least

```math
S=\sum_{k\ge1}b_ke^{-vk}(1-\cos k\theta)=\frac{N_v(0)}{1-e^{-5v}}-\Re\frac{N_v(\theta)}{1-e^{-5v+i5\theta}},
\quad N_v(\theta)=\sum_{r=1}^4b_re^{-rv+ir\theta}.
```

Write $\theta=2\pi b/5+\epsilon$, $|\epsilon|\le\pi/5$. When $|\epsilon|\ge2v$, the squared denominator and $1-\cos t\ge2t^2/\pi^2$ for $|t|\le\pi$ give

```math
S\ge\frac{4-10v}{5v}\left(1-\frac1{\sqrt{1+16e^{-5v}/\pi^2}}\right)\ge\frac{0.2}{v}.
```

When $|\epsilon|\le2v$, put $t=\epsilon/v$ and $C_b=\sum b_re^{2\pi ibr/5}$. Because the weights are symmetric, $C_b$ is real; $C_0=4$, while $C_b\le\sqrt5-1<1.25$ if $b\ne0\bmod5$.

```math
S=\frac{4-C_b/(1+t^2)}{5v}+E,\qquad |E|<13.
\tag{5.2}
```

Here we use $|N_v(\theta)-C_b|\le30v$ and $|1-e^{-5v+i5\epsilon}|\ge5v/(1+5v)$. For $d=5v-i5\epsilon$, $|d|\le5\sqrt5v$, [Coth] gives

```math
\left|\frac1{1-e^{-d}}-\frac1d\right|\le\frac12+\frac{|d|}{12(1-|d|^2/(4\pi^2))}<0.507.
```

The numerator- and denominator-replacement errors on the nonzero-angle side are at most $6.195+2.028$, and the error on the real-axis side is at most $2+4(0.507)=4.028$, for a total below 13. If $b=0$, then $|t|\ge3/4$, so the main term is at least $0.288/v$; if $b\ne0$, it is at least $0.55/v$. After subtracting $13v\le0.0845$, it is still at least $0.2/v$, proving (5.1).

This argument is not a check obtained by sampling angles. Scalar comparisons are handled by certificates E01–E06.

### 5.2. The eta transformation and an upper bound on the positive real axis

Applying the transformation law [Eta] to $q=\zeta^\ell e^{-w}$ gives

```math
G(\zeta^\ell e^{-w})
=\kappa_\ell e^{A/w-w/6}U_\ell(w),\quad
(\kappa_1,\kappa_2,\kappa_3,\kappa_4)
=(e^{-i\pi/5},1,1,e^{i\pi/5}),
\tag{5.3}
```

```math
U_\ell(w)=
\frac{(\zeta^{-\ell^{-1}}e^{-4\pi^2/(25w)};
        \zeta^{-\ell^{-1}}e^{-4\pi^2/(25w)})_\infty}
     {(e^{-4\pi^2/(5w)};e^{-4\pi^2/(5w)})_\infty}.
\tag{5.4}
```

Here $\ell^{-1}$ is the inverse modulo 5. The multiplier uses the Dedekind sums $s(\ell,5)=(1/5,0,0,-1/5)$. Also,

```math
G(e^{-w})=\sqrt5 e^{-C/w-w/6}U_0(w),\quad
U_0(w)=\frac{(e^{-4\pi^2/w};e^{-4\pi^2/w})_\infty}
 {(e^{-4\pi^2/(5w)};e^{-4\pi^2/(5w)})_\infty}.
\tag{5.5}
```

For $w=w_0+iy$, $|y|\le3w_0/4$, we have $\Re(1/w)\ge16/(25w_0)$. From $|\log(z;z)_\infty|\le |z|/(1-|z|)^2$ and $(4\pi^2/25)(16/25)>1$, throughout the range (4.1),

```math
|U_\ell(w)-1|\le10e^{-1/w_0}\quad(\ell=0,\ldots,4).
\tag{5.6}
```

Use the root filter in (2.3) to extract the three $\mathscr P$. With $w=v/5$, each primitive-root term is at most $1.001e^{A/w}$ and the $q=1$ term at most $0.001e^{A/w}$. Removing the coefficients $q,q^2$ costs a factor at most $e^{2w}$, so

```math
\mathscr P(e^{-v})\le2e^{C/v}\qquad(0<v\le0.0065).
\tag{5.7}
```

Certificates E07–E10 and E36–E37 verify the numerical margins.

### 5.3. Tail expansion and combination of the four arcs

With $x=e^{-5nw}$ and $|x|=x_0$, put

```math
\Lambda(x)=\frac15\operatorname{Li}_2(x^5)-\operatorname{Li}_2(x),\qquad
L_\ell(x)=\sum_{\substack{j\ge1\\5\nmid j}}\frac{x^j}{j}\left(\frac{\zeta^{\ell j}}{1-\zeta^{\ell j}}+\frac12\right).
```

The exact tail logarithm is

```math
\log T_n(\zeta^\ell e^{-w})=\sum_{j\ge1}\frac{x^j}{j}\left\{\frac1{\zeta^{-\ell j}e^{jw}-1}-\frac1{e^{5jw}-1}\right\}.
```

Expanding it gives

```math
\log T_n(\zeta^\ell e^{-w})
=\frac{\Lambda(x)}{5w}+L_\ell(x)+E_\ell(w,x),
\qquad |E_\ell(w,x)|\le\frac{5|w|x_0}{1-x_0}.
\tag{5.8}
```

We verify uniformity of the error. If $|\Im t|\le3\Re t/4$, then for a nontrivial fifth root $\xi$,

```math
\left|\frac{d}{dt}\frac1{\xi^{-1}e^t-1}\right|=\frac1{2(\cosh\Re t-\cos(\Im t-\arg\xi))}\le4.
```

For $\Re t\le1$ use the angular distance $2\pi/5-3/4$, and for $\Re t\ge1$ use $\cosh1-1$. Also, from $\Re(t^2)\ge0$ and the partial-fraction expansion of coth,

```math
\left|\frac1{e^t-1}-\frac1t+\frac12\right|\le\frac{|t|}{12}.
```

Thus the first-order remainder in each brace is less than $5j|w|$ when $5\nmid j$, and at most $j|w|/2$ when $5\mid j$. Summing the series gives (5.8). We have not assumed that $x_0/w_0\to0$.

If $C_a=\sum_{\ell=1}^4\zeta^{-a\ell}\kappa_\ell$, then

```math
(C_0,C_1,C_2,C_3,C_4)=(\sigma_0,\sigma_1,\sigma_2,0,0).
```

For the two weak residue classes, $S_a(x)=\sum\zeta^{-a\ell}\kappa_\ell e^{L_\ell(x)}$ satisfies $S_a(0)=0,S_a'(0)=-1$. The derivative calculation is checked as follows. If $V_a=\sum\zeta^{-a\ell}\kappa_\ell/(1-\zeta^\ell)$, then $V_a-V_{a-1}=C_a$ and $\sum_aV_a=0$. Since $C_3=C_4=0$, we obtain $V_2=V_3=V_4=-1$, and hence $S_a'(0)=V_{a-1}+C_a/2=-1$.

The absolute value of the coefficient of degree $j$ in $L_\ell$ is at most $1/j$, so

```math
|S_a(x)+x|\le8x_0^2.
```

The error in the four-root sum resulting from exponentiating (5.8) is at most $25|w|x_0$. Using $(C+\Lambda(x))/(5w)=nR(5nw)$ gives

```math
\sum_{\ell=1}^4\zeta^{-a\ell}\kappa_\ell e^{A/w-w/6}
(T_n(\zeta^\ell e^{-w})-1)
=-x e^{nR(5nw)-w/6}(1+\epsilon(w)),
\tag{5.9}
```

```math
|\epsilon(w)|\le8x_0+25|w|.
```

The term $-1$ cancels exactly because $C_a=0$. The eta remainder is always retained in the form $(G-G_{\rm main})(T_n-1)$. For the three strong residue classes, use $S_a(0)=\sigma_a\ne0$; the same relative-error bound applies. For example, $|S_a(x)-\sigma_a|/|\sigma_a|\le8x_0$ follows from $\min|\sigma_a|=(5-\sqrt5)/2>1$. The numerical comparisons are E11–E15 and E35.

### 5.4. Integrals over the minor arcs and of the eta remainder

Let $r=e^{-w_0}$. Positivity of the tail coefficients gives, on the entire circle,

```math
|T_n(q)-1|\le T_n(r)-1\le\frac{x_0}{w_0}e^{x_0/w_0}.
\tag{5.10}
```

Indeed, estimating the tail logarithm by geometric series gives

```math
\log T_n(r)\le4\frac{x_0}{1-x_0}+\frac4{5w_0}\frac{x_0}{1-x_0}\le\frac{x_0}{w_0}.
```

On the region whose angular distance from all five fifth roots is at least $3w_0/4$, applying (5.1) and (5.7) to $Q=q^5$ gives

```math
|G(q)|\le6\exp\left(\frac A{w_0}-\frac{0.04}{w_0}\right).
\tag{5.11}
```

In the weak case retain the factor (5.10), so $x_0r^{-m}=r^{-k}$, where $k=m-5n$. From $\Lambda(x_0)\ge-x_0/(1-x_0)$ and

```math
0.04-x_0-\frac{x_0}{5(1-x_0)}>\frac1{30},
```

the minor-arc contribution divided by (4.2) is at most

```math
16w_0^{-3}e^{-1/(30w_0)}.
```

Specifically, §5.5 gives $E''(w_0)\le0.67/w_0^3$, so the prefactor is $6\sqrt{2\pi\cdot0.67}\,e^{w_0/6}w_0^{-5/2}$, bounded by $16w_0^{-3}$.

Near $q=1$ use (5.5), and for the eta remainder at the primitive roots use (5.6). Each exponential gap from the main term is at least $0.9/w_0$; even the crude prefactor $100w_0^{-5/2}$ is absorbed into $w_0^{-3}e^{-1/(30w_0)}$. With margin, allocate to the entire excluded part

```math
50w_0^{-3}e^{-1/(30w_0)}
\tag{5.12}
```

In the strong case use $T_n(r)\le e^{x_0/w_0}$; with $k=m$ the same bound results. The comparisons are E16–E21.

### 5.5. Gaussian replacement and the prefactor

```math
F(w)=nR(5nw)=\frac A w+Q_n(w),\quad Q_n(w)=\frac1{5w}\sum_{j\ge1}\frac{a_je^{-5njw}}{j^2},
```

where $a_j=-1$ if $5\nmid j$, and $a_j=4$ if $5\mid j$. For $r=2,3$ and $|y|\le3w_0/4$,

```math
w_0^{r+1}|Q_n^{(r)}(w_0+iy)|
\le\frac45r!\sum_{j\ge1}\frac{x_0^j}{j^2}
\sum_{h=0}^r\frac{(\tau j)^h}{h!}.
\tag{5.13}
```

For $\tau\ge11/2,h\le3$, $\tau^he^{-\tau j}$ decreases with $\tau$. Set $T_*=11/2$, $x_*=e^{-T_*}$, and

```math
B_2=\frac85(1+T_*+T_*^2/2)\frac{x_*}{1-x_*}<0.142,
```

```math
B_3=\frac{24}5\left[(1+T_*+T_*^2/2)\frac{x_*}{1-x_*}+\frac{T_*^3}{6}\frac{x_*}{(1-x_*)^2}\right].
```

Writing $E(w)=F(w)+kw$, the saddle condition $E'(w_0)=0$ and

```math
\frac{0.38}{w_0^3}\le E''(w_0)\le\frac{0.67}{w_0^3},\qquad
|E'''(w_0+iy)|\le\frac{2.56}{w_0^4}
\tag{5.14}
```

follow. Computing the real part of $A/w$ exactly and bounding the quadratic term of $Q_n$ gives

```math
\Re E(w_0+iy)-E(w_0)\le-\frac{0.097y^2}{w_0^3},
\tag{5.15}
```

because $A/(1+(3/4)^2)-B_2/2>0.097$.

Linear interpolation between the two exponents gives

```math
\left|e^{E(w_0+iy)-E(w_0)}-e^{-E''(w_0)y^2/2}\right|\le\frac{2.56|y|^3}{6w_0^4}e^{-0.097y^2/w_0^3}.
```

Integrating and dividing by $J_0=\sqrt{2\pi/E''(w_0)}$ gives at most $14.9\sqrt{w_0}$. Including the complete Gaussian tail gives at most $15\sqrt{w_0}$.

The error from the amplitude in (5.9) and from $e^{-iy/6}$ is at most $8x_0+32w_0$. Specifically, $|w|\le5w_0/4$ and $|e^{-iy/6}-1|\le(w_0/8)e^{w_0/8}$ show that the coefficient of $w_0$ is

```math
31.25+e^{w_0/8}(1+8x_0+31.25w_0)/8<32.
```

The comparison remains valid under the new upper bounds by substituting $x_0<0.005,w_0<0.002$. The ratio of the absolute integral to $J_0$ is at most $\sqrt{0.67/0.194}<1.86$, so the amplitude contributes at most $15x_0+60w_0$. Together with (5.12), this gives (4.3). The comparisons are E22–E33.

After combining the four arcs with the same $y$, the weak-case factor $-xe^{mw}=-e^{kw}$ shifts the location by $5n$. No extra “factor 4 from the four roots” is multiplied in at this stage.

```math
\frac{e^{E(w_0)-w_0/6}}{2\pi}\sqrt{\frac{2\pi}{E''(w_0)}}=\frac{e^{nR(\tau)+kw_0-w_0/6}}{5\sqrt{2\pi R''(\tau)}\,n^{3/2}},
```

where $E''(w_0)=25n^3R''(\tau)$ was used. This is (4.2), and (4.4)–(4.5) follow.

## 6. The endpoint region for $n\ge31147$

```math
\rho=-5R'(11/2)=0.2131128927124522702188745809\ldots.
\tag{6.1}
```

Since $\Lambda(e^{-\tau})<0$ and

```math
\frac{d}{d\tau}\Lambda(e^{-\tau})=\log((1-e^{-5\tau})/(1-e^{-\tau}))>0,
```

we have

```math
0<-R'(\tau)<C/\tau^2,\qquad w_0^2<C/(5k).
\tag{6.2}
```

If $k\ge5n$ and $n\ge31147$, then

```math
w_0^2<C/(25n)\le(0.0013)^2.
```

Comparison E34 verifies $C/(25(0.0013)^2)<31147$.

Consider $0\le m\le\rho n^2$.

- For $a=0,1,2$: when $m\le5n$, the coefficient agrees with that of $G$; when $m>5n$, apply the endpoint estimate with $k=m$.
- For $a=3,4$: when $m\le5n$, it is zero; when $0<k=m-5n<5n$, use (3.6); when $k\ge5n$, apply the endpoint estimate.

Whenever a saddle is needed, $k\le m\le\rho n^2$, so $\tau\ge11/2$. Thus all coefficients at the left endpoint have the desired sign. The right endpoint follows from (1.3). The zero coefficients in this range occur only at the positions listed in (1.2).

The finite decimal expansion of $\rho$ must not be rounded upward to enlarge the domain. The region is defined by the exact function value in (6.1).


## 7. Sign and quantitative lower bound for the interior main phase

Define the amplitudes at the primitive roots by

```math
\lambda_\ell(z)=\sum_{j=1}^4\left(\frac j5-\frac12\right)
\{\log(1-\zeta^{\ell j}e^{-z})-\log(1-\zeta^{\ell j})\},\qquad
\mathcal A_\ell(z)=e^{\lambda_\ell(z)}.
```

The branches are chosen continuously from $z=0$. On the real axis, pairing the conjugate terms $j$ and $5-j$ gives $|\mathcal A_\ell(\tau)|=1$.

```math
\Phi_a(e^{-\tau})=\sum_{\ell=1}^4\zeta^{-a\ell}\mathcal A_\ell(\tau).
\tag{7.1}
```

Put $x=e^{-\tau}$, $v=(1-x)/(1+x)$, and

```math
\alpha=\arctan(v\cot(\pi/5)),\quad
\beta=\arctan(v\cot(2\pi/5)),\quad
U=(\alpha+2\beta)/5,\quad V_0=(2\alpha-\beta)/5.
```

Pairing conjugate roots and converting a sum of two cosines into a product gives

```math
\Phi_a(x)=4\cos(3\pi a/5+U)\cos(-\pi a/5+V_0).
\tag{7.2}
```

Both $U$ and $V_0$ increase strictly from $0$ to $\pi/10$ as $v$ ranges over $[0,1]$. For example,

```math
V_0'\ge v_*=\frac{\sin(2\pi/5)-\cot(2\pi/5)}5>0,\quad
U'\ge u_*=\frac{\sin(\pi/5)\cos(\pi/5)+2\sin(2\pi/5)\cos(2\pi/5)}5>0.
```

The ranges of the angles imply $\Phi_0>0$ and $\Phi_a<0$ for $a\ne0$ and $x>0$. For the two weak residue classes,

```math
-\Phi_3=4\cos(\pi/5-U)\sin(\pi/10-V_0),\quad
-\Phi_4=4\sin(\pi/10-U)\cos(\pi/5+V_0).
```

Using $\sin y\ge2y/\pi$ and $1-v\ge x$, we obtain
$8\cos(\pi/5)v_*/\pi>1/4$ and
$8\cos(3\pi/10)u_*/\pi>1/4$.
The three strong residue classes have a positive constant lower bound. Hence

```math
\epsilon_a\Phi_a(x)\ge x/4,\qquad
\epsilon_0=1,\quad\epsilon_1=\cdots=\epsilon_4=-1.
\tag{7.3}
```

The numerical comparisons are B01–B05.

## 8. All-angle localization with denominator-dependent parameters

Let $n\ge N=31147$, $0\le\tau\le11/2$, and $r=e^{-\tau/(5n)}$.
In Dirichlet approximation we use the common value $Q=4139$ throughout and choose a reduced fraction $a/b$, with $b\le Q$, such that
$|\theta/(2\pi)-a/b|\le1/(bQ)$. Put $t=5n(\theta-2\pi a/b)$.
The following parameters are used only after the approximant has been chosen, so they do not alter the covering of the circle.

| denominator | $\eta$ | $K$ | $L$ | upper bound $\kappa_*$ for the geometric-series kernel |
|---|---:|---:|---|---:|
| $5\nmid b$ | $11313/1250000$ | 718 | $\log(2/\eta)$ | $\kappa(Z_1)$ |
| $5\mid b$ | $113/40000$ | 2717 | $\log(2/\eta)$ | $\kappa(Z_5)$ |

Throughout this section, $\eta,K,L$ mean the values in the applicable row. Set
$Z_1=(11/2)K/N+10\pi K/Q$ and $Z_5=(11/2)K/N+2\pi K/Q$, and use the function $\kappa$ of §8.3 directly in interval arithmetic. No rounded fixed constant is substituted into the error budget.
The truncation tail is $\delta=10e^{-\eta K}/(\eta K)$, and the error in the resonant sums is $4\kappa_*L/n$.

### 8.1. Competition with smoothed denominators not divisible by 5

Let $h(z)=\int_0^1\log(1-e^{-zx})dx$ and $M(\tau)=\sup_t\Re h(\tau-it)$.
The maximum principle in the right half-plane, together with $\Re h\to-\infty$ at the origin and $h\to0$ at infinity, shows that $M$ is nonnegative and nonincreasing. Put $f(y)=\log|2\sin(y/2)|$. On the unit circle the mean is $t^{-1}\int_0^t f(y)dy$. Each subsequent period moves the mean of the first period toward zero.
The unique zero of
$H(t)=tf(t)+\sum_{k\ge1}\sin(kt)/k^2$ in $(\pi,2\pi)$ is the maximum point. Bounding 1,000 terms and the tail by $1/1000$ encloses $H(4.97)>0$ and $f(4.97)<1/5$, and therefore $M(0)<1/5$.

The numerator radius is retained in the smoothing increment. If $0\le\rho\le1$, then

```math
|1-\rho e^{iv}|\ge\rho|1-e^{iv}|,
\quad
\frac{|1-\rho e^{-\delta+iv}|}{|1-\rho e^{iv}|}
\le1+\frac{\rho(1-e^{-\delta})}{|1-\rho e^{iv}|}
\le1+\frac{\delta}{2|\sin(v/2)|}.
\tag{8.19}
```

The difference of the squares in the first inequality is
$(1-\rho)(1+\rho-2\rho\cos v)\ge0$.
The singularities have measure zero, and the logarithmic upper bound is locally integrable.
If $\mathcal L(u)=(1+u)\log(1+u)-u\log u$, integration using
$|\sin(v/2)|\ge|v|/\pi$ for $|v|\le\pi$ shows that the mean over a period is at most $\mathcal L(\delta/2)$.
The mean over an interval from the origin of length $s\ge1$ is at most $2\pi$ times the periodic mean; if $s\ge2$, it is at most $\pi$ times that mean. For an interval shorter than one period, bound it by the entire period; for a longer interval, split it into complete periods and a remainder. The concavity of $\mathcal L$ implies that $\mathcal L(bu)/b$ is nonincreasing for $b\ge1$.

Another bound that retains the real radius is, for $u>0$,

```math
\log|1-e^{-u-\delta+iv}|-\log|1-e^{-u+iv}|
\le\log(1+\delta/u).
\tag{8.16}
```

This follows by integrating the derivative bound $1/(e^u-1)\le1/u$ for variation of the radius. With $u=b\tau x$ and $\delta=b\eta$, integration bounds the increment by $\mathcal L(\eta/\tau)$.

Write $\mathcal H_b$ for the resonant main term below. First suppose $\tau\le1/2$. Then $R(\tau)\ge R(1/2)>1.189$.
For $b=1$ and $|t|\le2$, the inequality
$|1-\rho e^{itx}|\le\max(1,2|\sin(tx/2)|)$, valid for every radius, gives

```math
\mathcal H_1\le4(1-\pi/6)\log(2\sin1).
```

Indeed, the logarithm is nonpositive when $|t|x\le\pi/3$, and the remaining interval has length at most $1-\pi/6$.
If $|t|\ge2$, then $\mathcal H_1\le0.8+4\pi\mathcal L(\eta/2)$.
In either case, $R-\mathcal H_1>0.025$.
For $b\ge2$, every factor has absolute value at most 1 when the angular length $b|t|<1$; otherwise
$\mathcal H_b\le0.4+4\pi\mathcal L(\eta)$, so $R-\mathcal H_b>0.1$.

For $\tau\ge1/2$, put $A_0=\pi^2/6$ and $B(\tau)=\operatorname{Li}_2(e^{-\tau})$. Then
$M(\tau)\le B(\tau)^2/(4A_0\tau)$ and
$R(\tau)\ge(C-B(\tau))/\tau$.
The first inequality follows from $|\operatorname{Li}_2(e^{-\tau+it})|\le B(\tau)$ and maximization of a quadratic.
Cover $[1/2,11/2]$ by 200 intervals $[u,v]$ of width $1/40$ and enclose

```math
\frac{C-B(u)-B(u)^2/A_0}{v}-4\mathcal L(\eta/u)>0.025,
\quad
\frac{C-B(u)-B(u)^2/(2A_0)}{v}-2\mathcal L(\eta/u)>0.1
\tag{8.20}
```

The first inequality applies to $b=1$, and the second to $b\ge2$.
The upper bound for $B$ uses 100 terms and a positive geometric-series tail.
The proof of $R(1/2)>1.189$ also uses five positive terms of $\operatorname{Li}_2(e^{-5/2})$.
Throughout the range, $R>0.238$. These statements are checked by L00a–L11.

### 8.2. Nonresonant error frequency by frequency

The inequality $|1-ue^{iv}|\le e^{\eta/2}|1-ue^{-\eta+iv}|$ gives

```math
\frac1n\log|B_n(re^{i\theta})|
\le2\eta-\frac1n\Re\sum_{l\ge1}\frac{e^{-\eta l}}l
\left(\sum_{j=1}^{5n}e^{-l\tau j/(5n)+ilj\theta}
-\sum_{j=1}^{n}e^{-l\tau j/n+i5lj\theta}\right).
\tag{8.1}
```

For $d=1,5$, put $g=\gcd(b,d)$ and $B=b/g$. The following nonresonant sums are always taken over the subset satisfying **$b\nmid dl$**.
If $r_{d,l}=\operatorname{dist}(dla,b\mathbb Z)$, then

```math
\left\|\frac{dl\theta}{2\pi}\right\|\ge\frac{r_{d,l}-dl/Q}{b},
\quad
\left|\sum e^{-\alpha j+idlj\theta}\right|\le\frac{b}{2(r_{d,l}-dl/Q)}.
\tag{8.17}
```

The latter follows from the geometric series and Abel summation for monotone positive weights.
Writing the distance as $r_{d,l}=gr$, and assuming $\epsilon=dK/(gQ)<1$, we have

```math
\frac1{r-dl/(gQ)}\le\frac1r+\frac{d l}{gQ(1-\epsilon)r^2}.
\tag{8.21}
```

Within each block of length $B$, each nonzero distance $r$ occurs at most twice.
When the decreasing positive weights are rearranged, missing resonant terms may be filled with zeros without invalidating the upper bound.

```math
S_0=\sum_{l=1}^K\frac{e^{-\eta l}}{l\lceil l/2\rceil},\quad
T(B)=S_0+\frac{2(1+\log K)e^{-\eta B}}{B(1-e^{-\eta B})},\quad
U(B)=\frac{\pi^2}{3(1-e^{-\eta B})}.
\tag{8.22}
```

The first block is at most $S_0$. The remainder of the $j$th block, for $j\ge1$, is bounded using
$e^{-\eta jB}/(jB)$ and
$\sum_{i\le K}1/\lceil i/2\rceil\le2(1+\log K)$.
The inverse-square sum in one block is at most
$2\sum_{r\ge1}r^{-2}=\pi^2/3$.
Consequently, the normalized nonresonant error on the $d$ side is at most

```math
\frac{b}{2gn}\left[T(B)+\frac{d}{gQ(1-\epsilon)}U(B)\right]
\tag{8.23}
```

Both $T$ and $U$ decrease as $B$ increases.
If $5\nmid b$ and $b>2K$, two frequencies at the same distance would satisfy
$l_1\equiv\pm l_2\pmod b$.
For two distinct frequencies this would require $l_1+l_2=b>2K$, which is impossible.
In this case each distance occurs at most once, so $T,U$ in (8.23) may be replaced respectively by
$S_1=\sum_{l\le K}e^{-\eta l}/l^2$ and $\pi^2/6$.
This removes both the loss incurred by applying $dK/Q$ to every frequency and the loss from double occurrence for large denominators.

### 8.3. Resonant sums and classification of all denominators

For $A=l(\tau-it)$ and $M=n$ or $5n$,

```math
\sum_{j=1}^M e^{-Aj/M}-M\int_0^1e^{-Ax}dx
=(1-e^{-A})\left(\frac1{e^{A/M}-1}-\frac M A\right).
\tag{8.12}
```

At $A=0$ this is interpreted by continuous extension. The partial-fraction expansion of $\coth$ gives, for $|z|<2\pi$,

```math
\left|\frac1{e^z-1}-\frac1z\right|
\le\kappa(|z|)=\frac12+\frac{|z|}{12(1-|z|^2/(4\pi^2))}.
\tag{8.13}
```

Here $|A/M|\le(11/2)K/N+10\pi K/(bQ)$.
Using $b\ge1$ in the case $5\nmid b$ and $b\ge5$ in the case $5\mid b$ gives the tabulated value of $\kappa_*$.
Since $|1-e^{-A}|\le2$, the total error from the two resonant sums is at most $4\kappa_*L/n$.
The tail coefficients for the finite sums and continuous main terms are at most 4 and 6 respectively, so their combined tail is at most $\delta$.
The resonant main term is

```math
\mathcal H_b=\begin{cases}
\displaystyle\frac4b\int_0^1\log|1-e^{-b\eta-b(\tau-it)x}|dx,&5\nmid b,\\
\displaystyle\frac1j\int_0^1\log\left|\sum_{r=0}^4e^{-rj(\eta+(\tau-it)x)}\right|dx,&b=5j.
\end{cases}
\tag{8.3}
```

For $b=5j$ and $j\ge2$, $\mathcal H_b\le R(j\tau)/j\le R(\tau)/2$.
In general, $4\log2/b$ is an upper bound when $5\nmid b$, and $5\log5/b$ when $5\mid b$.
The coefficient $\gamma_b$ in the rough nonresonant bound $\gamma_b bL/n$ is
$[2(1-K/Q)]^{-1}+[2(1-5K/Q)]^{-1}$ for denominators not divisible by 5, and $0.6/(1-K/Q)$ for denominators divisible by 5.
When $b=5$, all terms on the $d=5$ side are resonant, so $\gamma_5=[2(1-K/Q)]^{-1}$.
When $b=1$, there are no nonresonant terms.

| denominator | gap from the main term, or upper bound for the main term | nonresonant estimate |
|---|---|---|
| $b=1$ | gap $0.025$ | $0$ |
| $2\le b\le100,\ 5\nmid b$ | gap $0.1$ | rough bound, $b\le100$ |
| $100<b\le1436,\ 5\nmid b$ | main term at most $4\log2/101$ | (8.23), $b\le1436,B\ge101$ |
| $1436<b\le Q,\ 5\nmid b$ | main term at most $4\log2/1437$ | single occurrence: $S_1,\pi^2/6$ |
| $5<b\le300,\ 5\mid b$ | gap $0.238/2$ | rough bound, $b\le300$ |
| $300<b\le Q,\ 5\mid b$ | main term at most $5\log5/301$ | (8.23), $B_1\ge301,B_5\ge61$ |
| $b=5$, outside the major arcs | next-term gap $0.00992$ | $\gamma_5 5L/n$ |

In each row, a gap greater than $1/1000$ remains after subtracting $2\eta$, the resonant error, the nonresonant error, and the tail.
The comparison is made at the threshold $N$; thereafter the $1/n$ terms and the argument bounds for the geometric series decrease.
All interval comparisons are L12–L19 in [localization_certificate.json](../computation/results/localization_certificate.json).

### 8.3a. The denominator-5 gap obtained by combining equal differences

Let $p_j(z)=e^{-jz}/\sum_{r=0}^4e^{-rz}$ and $z=\eta+\tau x$.
Before replacing individual products by their worst-case values, combine them for each difference $d$:

```math
W_d(z)=\sum_{j=0}^{4-d}p_j(z)p_{j+d}(z)
=\frac{\sum_{j=0}^{4-d}y^{2j+d}}{(1+y+y^2+y^3+y^4)^2},\quad y=e^{-z}
\tag{8.24}
```

Writing $S(y)=1+y+\cdots+y^4$, we have
$dW_d/dy=(1-y)Q_d(y)/S(y)^3$.
In ascending order, the coefficients are

| $d$ | coefficients of $Q_d$ |
|---|---|
| 1 | $(1,0,0,-4,-7,-7,-4,0,0,1)$ |
| 2 | $(0,2,2,4,2,2,4,2,2)$ |
| 3 | $(0,0,3,4,8,8,4,3)$ |
| 4 | $(0,0,0,4,6,6,4)$ |

For $d=2,3,4$, the function is increasing in $y$ and hence decreasing in $z$.
For $d=1$, the coefficients of $(1+t)^9Q_1(t/(1+t))$ are
$(1,9,36,80,95,24,-98,-148,-90,-20)$.
There is one sign change, so Descartes' rule of signs, together with $Q_1(0)>0$ and $Q_1(1)<0$, shows that there is exactly one zero in $(0,1)$.
Thus $W_1(z)$ is unimodal and its minimum on an interval occurs at an endpoint.
These polynomial identities are also checked by integer arithmetic.

Let $m=400$, set
$g_{d,i}=\min(W_d(0),W_d(\eta+(11/2)i/m))$, and put $g_{d,m+1}=0$.
This is a monotone lower envelope.
For each characteristic function,

```math
-\log\left|\sum_jp_je^{ijtx}\right|
\ge\sum_{d=1}^4W_d(z)(1-\cos(dtx)).
```

With $b_i=i/m$, the integral of the step function is at least
$\sum_i(g_{d,i}-g_{d,i+1})b_i(1-\operatorname{sinc}(dtb_i))$.
For $0\le a\le2$ and $|v|\ge a$, use

```math
1-\operatorname{sinc}v\ge a^2/6-a^4/120
\tag{8.8}
```

On the first half-period this follows from monotonicity of $\operatorname{sinc}$ and the Taylor lower bound; for $|v|\ge\pi$, it follows from $1-1/\pi>8/15$.
If $|t|\ge6/5$ and $a_{d,i}=\min(2,(6/5)db_i)$, then

```math
\Gamma=\sum_{d=1}^4\sum_{i=1}^{400}(g_{d,i}-g_{d,i+1})b_i
\left(a_{d,i}^2/6-a_{d,i}^4/120\right)>0.00992.
\tag{8.9}
```

The interval lower endpoint is greater than $0.00992$; all digits are recorded in the certificate.
Radial smoothing does not increase the value on the real axis of a sum with positive coefficients, so $\mathcal H_5\le R-\Gamma$.
Taking the major arcs to be
$|\theta-2\pi\ell/5|\le(6/5)/(5n)$ also handles the case $b=5$ outside those arcs.
Therefore, everywhere outside the major arcs,

```math
\frac1n\log|B_n(re^{i\theta})|\le R(\tau)-1/1000.
\tag{8.4}
```

The entire angular range has been covered analytically. No extrapolation from a finite sample of angles is used.


## 9. Combining the four roots before estimating the interior integral

Let $0\le\tau\le11/2$ and $z=\tau-it$. The small box is $|t|\le h=2/5$ and the large box is $|t|\le6/5$. For a nontrivial fifth root $\xi$ and $0\le x\le1$, the quantity $|1-\xi e^{-zx}|$ exceeds $d=0.75$ in the small box and 0.05 in the large box. Use the angular distances $2\pi/5-h$ and $2\pi/5-6/5$. Abbreviate $A_\ell=\mathcal A_\ell=e^{\lambda_\ell}$.

### 9.1. First Euler–Maclaurin correction and second-order remainder

For $f\in C^2[0,1]$,

```math
\left|\sum_{r=0}^{n-1}f((r+\alpha)/n)-n\int_0^1f
-B_1(\alpha)(f(1)-f(0))\right|\le\frac1{8n}\int_0^1|f''|.
\tag{9.16}
```

The Peano kernel on one small interval is $(\alpha-u)_+-(1-u)^2/2-B_1(\alpha)(1-u)$, whose absolute value is at most $1/8$. Rescale each interval and telescope the endpoint differences. For $C^3$ functions, also extracting $B_2(\alpha)\Delta f'/(2n)$ gives

```math
\sum_{r=0}^{n-1}f((r+\alpha)/n)
=n\int_0^1 f+B_1(\alpha)\Delta f+\frac{B_2(\alpha)}{2n}\Delta f'+\varepsilon,
\qquad |\varepsilon|\le\frac1{n^2}\int_0^1|f'''|.
\tag{9.24}
```

The third-order kernel is $(\alpha-u)_+^2/2-(1-u)^3/6-B_1(\alpha)(1-u)^2/2-B_2(\alpha)(1-u)/2$. Since $|B_1|\le1/2$ and $|B_2|\le1/6$, its absolute value is at most $1/2+1/6+1/4+1/12=1$. The kernel annihilates polynomials of degree at most two. Summing over the small intervals proves (9.24).

Apply this to $f_j(x)=\log(1-\zeta^{\ell j}e^{-zx})$ with $\alpha=j/5$. The main integral is $nR(z)$, and the first endpoint difference is $\lambda_\ell(z)$ from §7. Set $b_j=B_2(j/5)$. Then

```math
B_n(\zeta^\ell e^{-z/(5n)})
=e^{nR(z)}A_\ell(z)e^{D_\ell(z)/n+\varepsilon_{\ell,n}(z)},
\qquad |\varepsilon_{\ell,n}|\le3400/n^2,
\tag{9.25}
```

```math
D_\ell(z)=\frac z2\sum_{j=1}^4b_j
\left(\frac{\zeta^{\ell j}e^{-z}}{1-\zeta^{\ell j}e^{-z}}
-\frac{\zeta^{\ell j}}{1-\zeta^{\ell j}}\right).
```

In the small box, $|z|<5.6$ and $|f_j'''(x)|\le2|z|^3e^{-\tau x}/d^3$, so the sum of the four integrals is at most $8(5.6)^3/d^3<3400$. In the large box use only (9.16), giving a logarithmic remainder at most $7200/n$.

### 9.2. Combination retaining the small factor

Put $x=e^{-\tau}$ and $M=1.54$. On the real axis, $|A_\ell(\tau)|=1$. In the small box, $|\lambda_\ell'|\le0.8x/d$ implies $|A_\ell(z)|\le e^{0.4(0.8)/d}<M$. In the large box, estimate the amplitude directly from its product representation. The sums of the absolute positive and negative exponents are each 0.4; using $1<|1-\xi|\le2$ and $0.05<|1-\xi e^{-z}|\le2$ gives $|A_\ell(z)|\le80^{2/5}<6$.

```math
a_1=\frac{0.8Mx}{d},\qquad
a_2=\frac M2\left(\frac{0.8x}{d^2}+\left(\frac{0.8x}{d}\right)^2\right).
\tag{9.18}
```

Thus the change in $A_\ell(\tau-it)$ from the real axis is at most $a_1|t|$, and the remainder after its linear term is at most $a_2t^2$.

```math
\Psi_a(z)=\sum_{\ell=1}^4\zeta^{-a\ell}A_\ell(z),\qquad
\Theta_a(z)=\sum_{\ell=1}^4\zeta^{-a\ell}A_\ell(z)D_\ell(z).
\tag{9.26}
```

We have $\Psi_a(\tau)=\Phi_a(e^{-\tau})$. For the weak residue classes $a=3,4$, the constant term at $x=0$ vanishes, giving $\Psi_a(z)=e^{-z}G_a(e^{-z})$. Each amplitude is analytic for $|e^{-z}|<1$ and continues analytically to the small box used here. The error bounds below do not rely on this factorization alone: they use the exact real-axis $\Phi_a$ and the $x$ factor in the derivatives.

Here $b_1=b_4=1/150$ and $b_2=b_3=-11/150$. For conjugate terms use $u/(1-u)+u^{-1}/(1-u^{-1})=-1$ to obtain

```math
D_\ell(z)=-z/30+ze^{-z}C_\ell(e^{-z}),\qquad
C_\ell(y)=\frac12\sum_{j=1}^4b_j\frac{\zeta^{\ell j}}{1-\zeta^{\ell j}y}.
\tag{9.27}
```

Consequently $\Theta_a=-z\Psi_a/30+ze^{-z}\sum\zeta^{-a\ell}A_\ell C_\ell$. The first Euler–Maclaurin correction therefore retains the small factor in the weak residue classes. With $Z=(\tau^2+h^2)^{1/2}$ and $p_a=|\Phi_a(e^{-\tau})|$,

```math
D_* =Z\left(\frac1{30}+\frac{2x}{25d}\right),\qquad
|\Theta_a|\le\frac Z{30}(p_a+4ha_1)+\frac{8MZx}{25d}=:T_a.
\tag{9.28}
```

We used $\sum|b_j|=4/25$. For each root the remaining exponentiation error satisfies

```math
\left|e^{D_\ell/n+\varepsilon_{\ell,n}}-1-D_\ell/n\right|
\le\frac{(3400+D_*^2/2)e^{D_*/N+3400/N^2}}{n^2}.
\tag{9.29}
```

No $x$ factor is claimed for this second-order remainder; it is handled by the explicit $n^{-2}$ bound.

### 9.3. Gaussian replacement and symmetric integration

Let $v_x$ be the variance of the real distribution $\Pr(J=j)\propto e^{-j\tau x}$, and put $V=\int_0^1x^2v_x\,dx$ and $W_r=\int_0^1x^rv_x\,dx$ for $r=3,4$. Then $V\le4/3$. Direct interval integration in §9.4 gives $V>1/80$ throughout.

For $Y=J-\mathbb EJ$, we have $|Y|\le4$ and $v_x\le4$. Translation preserves the absolute value of the characteristic function. Since $J-2\in[-2,2]$, for $|\omega|\le0.4$,
$|\mathbb Ee^{i\omega Y}|=|\mathbb Ee^{i\omega(J-2)}|\ge\cos(2|\omega|)\ge\cos0.8>0.69$.
Also $|\mathbb EYe^{i\omega Y}|\le0.4v_x$, and the second, third and fourth absolute-moment bounds are $v_x,4v_x,16v_x$. Substitution into the third and fourth logarithmic derivatives gives the coefficients

```math
4/.69+4.8/.69^2+2.048/.69^3<23,
\quad16/.69+37.6/.69^2+30.72/.69^3+9.8304/.69^4<240.
```

Hence $|R'''|\le23W_3$ and $|R^{(4)}|\le240W_4$. The inequality $1-\cos y\ge(1/2-1.6^2/24)y^2$ for $|y|\le1.6$ gives $\Re F_n\le-\beta nVt^2$, where $\beta=0.39$. Under the saddle condition $-R'(\tau)=m/(5n^2)$, define

```math
P_{\rm bulk}=\frac{e^{nR(\tau)+m\tau/(5n)}}{5\sqrt{2\pi V}\,n^{3/2}},\quad
F_n(t)=n(R(\tau-it)-R(\tau)+iR'(\tau)t),\quad G_0=-nVt^2/2.
```

Writing $D=F_n-G_0$ and $C_3=inR'''(\tau)t^3/6$ gives $|D|\le(23/6)nW_3|t|^3$ and $|D-C_3|\le10nW_4t^4$. The second-order remainder formula, integrated along the segment between exponents, yields

```math
|e^{F_n}-e^{G_0}-C_3e^{G_0}|
\le\left(10nW_4t^4+\frac{529}{72}n^2W_3^2t^6\right)e^{-\beta nVt^2}.
\tag{9.30}
```

Write $A(t)=\Psi_a(\tau-it)$, $A_0=\Phi_a$, and $A_1=A'(0)$. Then

```math
\begin{aligned}
A(t)e^{F_n}-A_0e^{G_0}={}&A_0(e^{F_n}-e^{G_0}-C_3e^{G_0})\\
&+(A(t)-A_0)(e^{F_n}-e^{G_0})
+(A(t)-A_0-A_1t)e^{G_0}+(A_0C_3+A_1t)e^{G_0}.
\end{aligned}
\tag{9.13}
```

The last term vanishes exactly on a symmetric interval. For the others use the change bound $4a_1|t|$ and the quadratic remainder $4a_2t^2$. Integrating the even Gaussian moments over the real line and dividing by $\sqrt{2\pi/(nV)}$ gives the error coefficient

```math
H_a=\frac1{\sqrt{2\beta}}\left[
p_a\left(\frac{240W_4}{32\beta^2V^2}+\frac{2645W_3^2}{192\beta^3V^3}\right)
+4\left(\frac{23a_1W_3}{8\beta^2V^2}+\frac{a_2}{2\beta V}\right)\right].
\tag{9.31}
```

The first bracket is multiplied by the combined main term $p_a$, rather than 4. The extracted first Euler–Maclaurin correction contributes at most $T_a/(n\sqrt{2\beta})$. Define the remaining coefficient by

```math
U=\frac{4M}{\sqrt{2\beta}}(3400+D_*^2/2)e^{D_*/N+3400/N^2}
\tag{9.32}
```

Its error is at most $U/n^2$.

Cover the intermediate angles $[0.4,1.2]$ by sixteen intervals $[u,v]$ of width $1/20$. On each interval set $c=\tfrac12(\sin(2v)/(2v))^2$, so that $1-\cos y\ge cy^2$ for $|y|\le4v$. Interval verification gives $cu^2>0.052$ on all sixteen intervals. The profile variance lower bounds directly give $0.052V>0.00074$ and $Vh^2/2>0.001$. With the updated prefactor 34:

| Part | Normalized upper bound |
|---|---|
| Minor arcs | $15n^{3/2}e^{-n/1000}$ |
| Intermediate major-arc angles | $34\sqrt n\,e^{-37n/50000}$ |
| Extension to the full Gaussian | $8e^{-n/1000}$ |

Each is less than $1/n$ for $n\ge N$. Compare logarithms at the threshold and use the derivative $c-\alpha/n>0$ thereafter. Therefore

```math
\left|\frac{c_n(m)}{P_{\rm bulk}}-\Phi_{m\bmod5}(e^{-\tau})\right|
\le\frac{H_a+T_a/\sqrt{2\beta}+3}{n}+\frac U{n^2}.
\tag{9.33}
```

The Cauchy variable is $\theta=2\pi\ell/5+t/(5n)$, and $\sqrt{2\pi/(nV)}/(2\pi\cdot5n)$ supplies the prefactor in $P_{\rm bulk}$.

### 9.4. Interval verification over all parameters

Set $\tau_i=(11/2)i/128$ and $x_j=j/200$. On every complete rectangle enclose

```math
v_x=\sum_{j<k}(k-j)^2\frac{e^{-(j+k)\tau x}}{(\sum_{r=0}^4e^{-r\tau x})^2}
```

Multiply by exact monomial integration weights and sum to enclose $V,W_3,W_4$. Evaluate the phases from (7.2) on the same complete intervals. Retain a separate lower phase bound for each residue class and combine $p_a$ with the error formula using interval arithmetic.

All 128 intervals verify positivity of the five phases, $V>1/80$, and five error-to-phase ratios below 0.98: 1,408 comparisons in total. The variance lower endpoint is approximately 0.01423554 and the largest upper ratio approximately 0.37280682. This is an enclosure of all 25,600 rectangles, not extrapolation from samples. [certify_profiles.py](../computation/verification/certify_profiles.py) and [profile_certificate.json](../computation/results/profile_certificate.json) record every interval. Since the $1/n$ and $1/n^2$ terms decrease for all $n\ge N$, the same comparison applies throughout that range.


## 10. Connection to all coefficients and the zero set

Let $n\ge31147$. Section 6 covers $0\le m\le\rho n^2$, where $\rho=-5R'(11/2)$. For $\rho n^2\le m\le5n^2$, the unshifted saddle-point equation has a solution with $0\le\tau\le11/2$, and the uniform comparison of §9.4 makes the error in (9.33) smaller than the signed main term. Thus every interior coefficient has strictly the desired sign. The right half follows by reciprocal symmetry.

The zero coefficients are precisely those in $\{5j+3,5j+4:0\le j<n\}\cup\{7\}$, arising from agreement with the infinite product; $5n+8,5n+9$, arising from $d_1=0$ in the first tail formula; and their reflections. Every other coefficient has a strict sign by the endpoint and interior estimates, so (1.2) follows as well.

## 11. Supporting interval certificates

### 11.1. Interval certificates

The accompanying code used interval arithmetic in mpmath 1.3.0 at 60 decimal digits to check the following:

- `certify_scalars.py`: 82 comparisons in total: 37 endpoint, five phase, and 40 interior comparisons.
- `certify_localization.py`: 421 comparisons, including the classification of every denominator and all 200 radial intervals.
- `certify_profiles.py`: all 128 intervals and 1,408 comparisons.
- `certify_resonant_gap.py`: integer verification of the polynomial identity for each difference and the basis for monotonicity, together with an enclosure of the uniform gap on 400 intervals.

Decimal inputs are supplied as strings or integer ratios, and the lower endpoint of each difference interval is required to be strictly positive. Conversion to ordinary floating-point numbers is not used for decisions. Version 0.6 removed an unused $B$-check from the previous version, and v0.7 checks the sixteen intermediate-arc intervals as G16_0–G16_15. Comparisons G17–G18 directly derive the intermediate-arc and Gaussian-tail decay rates from the lower variance bound; G20 handles the $N$-dependence of the prefactor; and E34 and G25 explicitly check the connection to the endpoint region.

The results are recorded in [scalar_certificate.json](../computation/results/scalar_certificate.json), [localization_certificate.json](../computation/results/localization_certificate.json), [profile_certificate.json](../computation/results/profile_certificate.json), and [resonant_gap_certificate.json](../computation/results/resonant_gap_certificate.json). These do not constitute an independent formal verification of the analytic reasoning or of the library and code as a whole.

## 12. The fixed endpoint threshold

After a simultaneous search over several parameters, v0.7 regenerated the interval certificates at $N=31147$. The upper endpoint-error bound is approximately (0.84662267), below the adopted value (0.85). The upper bound for the major-arc error-to-phase ratio is also less than one.

The limitation identified here is the endpoint condition at the fixed value $w_{\max}=0.0013$:

```math
31146<\frac{C}{25w_{\max}^2}=31146.6805557\ldots<31147.
\tag{12.1}
```

[threshold_boundary_certificate.json](../computation/results/threshold_boundary_certificate.json) verifies both inequalities by interval arithmetic. Thus, with this endpoint condition unchanged, the integer threshold cannot be lowered to 31146 or below. This is not a proof of optimality over all parameter choices or reorganizations of the proof. Possibilities such as changing $w_{\max}$ further, improving the endpoint error formula, or using coverage of a different coefficient region remain open. The best value found in a search must be distinguished from an absolute mathematical lower bound.

## 13. Provenance and references

The analytic derivation grew from AI-assisted working notes and successive
revisions of cancellation estimates and explicit constants. OpenAI Codex
contributed mathematical derivations, implementations and exposition;
additional parallel AI agents and suggestions from other AI systems contributed
to proof, review and publication tasks. No personal author is named, and
independent human peer review is not claimed. This edition preserves the
mathematical core while selecting only material needed for the large-n result.

- **[RR]** NIST DLMF, [§17.2(vi), Rogers–Ramanujan identities](https://dlmf.nist.gov/17.2#vi).
- **[Eta]** NIST DLMF, [§23.18, Dedekind eta modular transformations](https://dlmf.nist.gov/23.18).
- **[Coth]** NIST DLMF, [§4.36.3, partial fraction expansion of coth](https://dlmf.nist.gov/4.36#E3).
- **[W21]** Liuquan Wang, [Sign Changes of Coefficients of Powers of the Infinite Borwein Product](https://arxiv.org/html/2108.03932v3), Proposition 3.6 and its proof.
- **[WK22]** Chen Wang and Christian Krattenthaler, [An asymptotic approach to Borwein-type sign pattern theorems](https://arxiv.org/html/2201.12415v1), especially the discussion in §11 of cancellation for the third conjecture.

The Rogers–Ramanujan identities, the 5-dissection of the infinite product, the eta transformation, and the saddle-point method are established tools. A comprehensive literature search has not been completed concerning the novelty of the nonnegative-kernel identity, its application to the finite tail, the eventual theorem, the effective threshold, or the zero-set classification.
