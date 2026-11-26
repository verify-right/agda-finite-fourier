# Fourier algebra isomorphism

Work in $\mathbb{F}_5$ with cyclic convolution of length two.

The Fourier transform is

$$
T(a,b)=(a+b,a-b).
$$

It preserves addition and transforms convolution
into pointwise multiplication.

## Computing multiplicative inverses

Suppose we want to find $g$ such that

$$
f*g=(1,0)
$$

for $f=(2,1)$.

First transform $f$:

$$
T(f)=(3,1).
$$

Compute the reciprocal of each coordinate modulo 5:

$$
(3^{-1},1^{-1})=(2,1).
$$

Apply the inverse Fourier transform:

$$
g=T^{-1}(2,1)=3T(2,1)=(4,3).
$$

Check using cyclic convolution:

$$
(2,1)*(4,3)=(1,0).
$$

We replaced a polynomial inversion problem with
independent scalar inversions.

This is what `synthesize-inverse` proves.

Proofs: [Fourier/Algebra.agda](../src/Fourier/Algebra.agda).
