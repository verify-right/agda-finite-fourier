# Weighted character sums

A finite weighted sum is linear in its weights. For a mask $M$, background $b$ and excess $s$,

$$
\sum_x(b+sM(x))f(x)=b\sum_x f(x)+s\sum_x M(x)f(x).
$$

`two-level` in [WeightedSums.agda](../src/Algebra/WeightedSums.agda) proves this over a commutative ring. If $M$ counts an enumeration, `integrate-count` replaces the last sum by a sum over that enumeration, including repeated samples.

## A subgroup filter

In $C_4$, take $H=\{0,2\}$ and weights $(4,3,4,3)$. The total weight is 14. The four character sums, before and after normalization, are:

| Frequency | Character | Sum | Normalized |
|---|---|---:|---:|
| 0 | $(1,1,1,1)$ | 14 | 1 |
| 1 | $(1,i,-1,-i)$ | 0 | 0 |
| 2 | $(1,-1,1,-1)$ | 2 | 1/7 |
| 3 | $(1,-i,-1,i)$ | 0 | 0 |

A nonconstant character has zero sum on the full group under the separation hypothesis. It contributes on $H$ only if its restriction there is trivial (or, for cancellation, the restriction satisfies separation). For subgroup size $h$ and index $o$, the total mass is $h(bo+s)$ and the retained numerator is $sh$.

The normalized coefficient is $s/(bo+s)$ when division is available. `retained-ratio` instead proves the denominator-cleared identity. `lemma6-1` applies these coefficients to a translated Fourier expansion using one-sided inversion.

In [WeightedExamples.agda](../src/Fourier/WeightedExamples.agda), work modulo 17: $i=4$ and $1/7=5$. `multipliers` computes $(1,0,5,0)$; `all-signals` proves the formula for every four-entry signal and translation. The complex table above explains the calculation; the checked instance uses modular arithmetic.

More generally, [InvariantWeight.agda](../src/Fourier/InvariantWeight.agda) proves cancellation for any weight invariant under separating translations, not just a subgroup indicator. Constant weight recovers ordinary character orthogonality. [CountingMeasure.agda](../src/Fourier/CountingMeasure.agda) derives counting inversion from ordinary Fourier inversion.

## Source

This is the ideal finite averaging identity in *Dirichlet L-functions and the Critical Line*, §6, Lemma 6.1. Compare Alpöge–Claude [ChCore.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean#L22-L54) (`sum_A`, `mem_psi`) and [SharesOfCounts.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThickFrames/SharesOfCounts.lean) (`shares_of_counts`). The latter controls empirical coset counts; this library proves the exact algebra, not that approximation or the analytic estimates. See also [Conrad, Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf).
