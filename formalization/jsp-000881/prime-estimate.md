# The six-affine-form prime count

## Estimate used by Lean

The counting argument needs the single instance `PrimeUniformity.GowersUniformityEstimate 5 1280`. Let $Q=\lfloor\exp((\log X)^{1/10})\rfloor$ and let $f$ be the difference of the prime-supported von Mangoldt weight and the finite Cramér weight on $[1,X]$, extended by zero to $\mathbb F_p$. The bound is

$$
\lVert f\rVert_{U^5(\mathbb F_p)}^{32} \le C(\log X)^{-1280}
$$

for one $C>0$, every sufficiently large $X$, and every prime $32X<p\le64X$. The interval-to-field normalization is proved in [IntervalMoment.lean](../prime-uniformity/PrimeUniformity/IntervalMoment.lean). The full derivation of the fixed estimate uses the [Lean 4.34.1 compatibility layer](../prime-uniformity/compat/README.md).

## Scales and transfer

Set $T=2^k$, $Z=k^7$, and $X=4000k^{14}T$. Each of the five companion weights is $O(k^2)$, the ambient field sum has size $O(k^{28}4^k)$, and the fixed estimate gives a $U^5$ norm of $O(k^{-40})$. Thus each of the six single-factor replacements costs $O(k^{-2}4^k)$. The triangular rectangle weights have Fourier $\ell^1$ norm 1. The uniform positive Cramér main term therefore yields a lower bound for the actual prime weights. [PrimeReduction.lean](Jsp000881/PrimeReduction.lean)

The resulting rectangle count is uniform over all retained parameters at the same scale. There are $\gg k^{28}$ retained planes, each contributing $\gg 4^k/k^6$ fresh prime tuples. Pairwise intersections cost at most $O(k^{56})$ tuples in total. This leaves a lower bound of order $k^{22}4^k$ against a perimeter bound of $3600000000k^{21}4^k$. The ratio tends to infinity along these cutoffs, which suffices to rule out a positive linear asymptotic. [Scaled.lean](Jsp000881/Scaled.lean)

## Mathematical references

Li uses Bienvenu's uniform prime-pattern theorem. Kravitz, Woo, and Xu give a related paper route in their Theorem 3.1, with ordinary von Mangoldt weights. For the two-dimensional six-form instance, the coefficients and intercepts have size $O((\log T)^{14})$, the directions are pairwise independent, and the parameter sieve gives a uniform positive lower bound for the local factors. The contribution of proper prime powers is $o(T^2)$. The Lean proof realizes the needed instance through the fixed Gowers bound and finite Cramér main term above. [Li](https://arxiv.org/abs/2606.25849v1) · [Bienvenu, Proposition 2.1](https://arxiv.org/abs/1607.06625) · [Kravitz–Woo–Xu, Theorem 3.1](https://arxiv.org/abs/2512.03292)

Green and Sawhney's Proposition 4.4 gives the quantitative prime-uniformity benchmark. The local formalization combines its own descent argument with the pinned upstream Gowers inverse theorem and prime-prefix estimate. [Green–Sawhney](https://arxiv.org/abs/2410.04189)
