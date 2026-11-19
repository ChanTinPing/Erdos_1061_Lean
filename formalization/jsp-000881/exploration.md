# Development notes for the fixed-denominator construction

The proof uses the integral $q=1$ family from §3 of Eric Li's paper. The following notes record the construction and earlier exploratory routes. The [package README](README.md) gives the route used by the final Lean theorem. [Li, arXiv:2606.25849v1](https://arxiv.org/abs/2606.25849v1)

## Parameter box and local admissibility

Put $W=508(2\cdot3\cdot5\cdot7\cdot11\cdot31\cdot127)$. Choose $\alpha,\beta,\gamma$ as multiples of $W$ in intervals of lengths $Z^2,Z,Z$. For integer lattice coordinates $n,m$, use

$$
y_1=508n,\qquad y_3=3918+508m,\qquad
r=15y_1,\qquad s=31y_3,\qquad t=-1-\beta r-\gamma s.
$$

The plane uses $y_2=\alpha s+462\beta t$, $y_4=-\alpha r+462\gamma t$, $x_i=y_i+t$ for $1\le i\le4$, and $x_5=t$. The last coordinate is determined by

$$
508x_6=15(x_1+x_2)+31(x_3+x_4)-508x_5-462.
$$

The right side is divisible by 508. At $n=m=0$, the six residues are nonzero modulo every prime dividing $W$. For $p\nmid W$, the zero-affine-form obstructions each impose two congruence conditions. Their total main term is bounded by $3\sum_{j\ge13}j^{-2}$ times the number of parameter triples. Summing the boundary errors leaves a positive proportion of locally admissible planes. [Plane.lean](Jsp000881/Plane.lean) · [ParameterSieve.lean](Jsp000881/ParameterSieve.lean)

## Counting and duplicate control

In the two-height rectangle, the six forms are positive, and their directions are pairwise independent. A lower bound of order $T^2/(\log T)^6$ per retained plane gives a superlinear count after summing over the parameter box. The difference between two distinct skew-symmetric plane maps has rank two, so two planes can share at most one point in the affine slice. The formal count removes these duplicates and uses ordered prime tuples to recover the ordered integer solutions. [Counting.lean](Jsp000881/Counting.lean) · [Prime-counting notes](prime-estimate.md)

## Earlier alternative routes

Restricting the same two-height construction to finitely many fixed planes or finitely many direction templates yields at most linear growth under the associated upper-bound argument. The restriction to finitely many templates cuts down the number of parameter triples that supply prime tuples.

Another approach sought three positive integers $K,M,N$ with $K+M=N$ and equal abundancy indices $\sigma(n)/n$. This would leave two free variables in the construction with one new prime per coefficient. The [rational valuation search](valuation_search.py) checked a finite family of such seeds. In the largest recorded search, the coprime core satisfied $w\le10{,}000$ and the tested valuations were at most 8. It found no triple in that range.

These alternatives explain the choice of a growing family of integer planes for the final proof.
