# Cyclic convolution

Work in $\mathbb{F}_{17}$ with polynomials modulo $x^4-1$.

Consider

$$
f(x)=1+2x^3,\qquad g(x)=3+x.
$$

Ordinary multiplication gives

$$
f(x)g(x)=3+x+6x^3+2x^4.
$$

Since $x^4=1$ in the quotient ring, the result is

$$
5+x+6x^3.
$$

This is cyclic convolution:

$$
(f*g)(z)=\sum_{i=0}^{3} f(i)g((z-i)\bmod 4).
$$

The coefficient vectors are

| | Coefficients |
|---|---|
| $f$ | $(1,0,0,2)$ |
| $g$ | $(3,1,0,0)$ |
| $f*g$ | $(5,1,0,6)$ |

The `fiber-sum` theorem proves that this single-sum formula
agrees with our general convolution definition.

The `convolution-transform` theorem proves that we can
compute the same product using pointwise multiplication
in Fourier coordinates.

Cyclic convolution uses $x^n-1$.
ML-KEM and ML-DSA instead use negacyclic convolution
modulo $x^n+1$.

Proofs: [Fourier/GroupConvolution.agda](../src/Fourier/GroupConvolution.agda).
