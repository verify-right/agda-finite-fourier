# Finite sums and the Kronecker delta

Work in the finite field $\mathbb{F}_5$: all arithmetic is modulo 5.

## Finite sums

For the vector $f=(2,4,1)$:

$$
\sum_i f(i)=2+4+1=2 \pmod 5
$$

Multiplying every entry by 3 and then summing gives the same
result as multiplying the sum by 3 (`sum-mulˡ`).

## Kronecker delta

The [Kronecker delta](https://en.wikipedia.org/wiki/Kronecker_delta)
is 1 when its indices agree and 0 otherwise.

To select the second entry of $f$ (index 1):

$$
\sum_j \delta_{1j}f(j)
=0\cdot2+1\cdot4+0\cdot1=4
$$

This is exactly what `select` proves.

Fourier inversion uses this identity to recover individual
coefficients from a sum.

[Agda source](../src/Algebra/FiniteSums.agda).
