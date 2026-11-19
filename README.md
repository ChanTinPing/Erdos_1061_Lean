# Erdős Problem #1061 in Lean 4

This repository gives an unconditional Lean proof that the number of ordered solutions to Erdős Problem #1061 has no positive linear asymptotic. The corresponding Justin Sun Prize catalog entry is **JSP-000881**. [Original problem](https://www.erdosproblems.com/1061) · [Prize catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000881)

## Statement

Let $\sigma(n)$ be the sum of the positive divisors of $n$. For a real cutoff $x$, let $S(x)$ count the ordered pairs of positive integers $(a,b)$ with $a+b\le x$ and $\sigma(a)+\sigma(b)=\sigma(a+b)$. The original question asks whether $S(x)\sim cx$ as $x\to\infty$ for some real $c>0$. The Lean proof gives the negative answer.

```lean
theorem not_linear_asymptotic : ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x)
```

The [submission theorem](formalization/jsp-000881/compat/UpstreamJspReduction.lean) is `Jsp000881.erdos_1061 : ¬ Jsp000881.OriginalQuestion`. Lean checks that the original count and the proof's count `S` agree at every real cutoff. It then transports `Jsp000881.not_linear_asymptotic` to the original question. [Statement correspondence](formalization/jsp-000881/Jsp000881/OriginalProblem.lean) · [Formal Conjectures reference](https://github.com/google-deepmind/formal-conjectures/blob/b576d527b271b936f9e61c0e367c302d7386bc80/FormalConjectures/ErdosProblems/1061.lean)

## Proof outline and attribution

The mathematical solution is due to **Eric Li**, *A resolution of Erdős Problem 1061 on the sum-of-divisors function*, arXiv:2606.25849v1, Theorem 1.1. Li proves a stronger growth result at every fixed logarithmic scale. This project formalizes the original negative answer using a fixed-denominator family from Li's construction. [Paper](https://arxiv.org/abs/2606.25849v1)

1. Construct a family of integer planes carrying six affine forms. Six distinct primes in the prescribed order give an ordered solution to the divisor-sum equation. The parameter sieve and intersection bounds control local obstructions and duplicate counts. [Construction and counting package](formalization/jsp-000881/README.md)
2. Establish a positive main term for the Cramér model and transfer it to the actual prime weights in the six forms. The transfer uses the fixed estimate `PrimeUniformity.GowersUniformityEstimate 5 1280` for the normalized fifth-order Gowers cube moment. The resulting count rules out $S(x)\sim cx$. [Counting reduction](formalization/jsp-000881/Jsp000881/PrimeReduction.lean)
3. Discharge the prime-uniformity estimate with the interval Gowers inverse theorem, the prime number theorem in arithmetic progressions, and the Vaughan Type I and Type II rank-descent arguments developed here. The final entry point supplies both descent branches to the counting reduction. [Prime-uniformity package](formalization/prime-uniformity/) · [Proof dependencies](formalization/prime-uniformity/compat/README.md)

The Lean formalization project is maintained by [@ChanTinPing](https://github.com/ChanTinPing). It uses pinned Lean developments from [OpenAI Math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean) and [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612). The adapted scalar Weyl argument carries its original attribution and [Apache 2.0 license text](formalization/prime-uniformity/LICENSE-APACHE).

## Verify the proof

With Git, Elan, and PowerShell 7 installed, run this from the repository root.

```powershell
pwsh -NoProfile -File ./Verify.ps1
```

The [verification script](Verify.ps1) installs Lean 4.34.1 as needed, fetches the pinned upstream revision, builds the proof, and checks the final theorem's transitive axioms. The first build can take substantial time. The script saves the local build and audit output to `.lake/verify/proof-build.log`. [Dependency and cache notes](formalization/prime-uniformity/compat/README.md)

The development build reported only `propext`, `Classical.choice`, and `Quot.sound`. The script fails on `sorryAx` or any other axiom outside that set. [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
