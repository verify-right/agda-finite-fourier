# Fourier inversion and convolution

Work in $\mathbb{F}_5$.

## Two-point transform

The simplest nontrivial Fourier transform is

$$
T(a,b)=(a+b,a-b).
$$

For example:

$$
T(2,1)=(3,1).
$$

## Orthogonality and cancellation

The two character vectors are $(1,1)$ and $(1,-1)$.
Their scalar product is $1-1=0$.

The transform matrix therefore satisfies

$$
K=\begin{pmatrix}1&1\\1&-1\end{pmatrix},
\qquad K^2=2I.
$$

This is `orthogonality`.

## Inversion

Applying the transform twice gives

$$
T(T(2,1))=T(3,1)=(4,2).
$$

The inverse of 2 modulo 5 is 3. Multiplying by 3 recovers
$(2,1)$.

This is `inversion`.

## Convolution

Take $f=(2,1)$ and $g=(3,4)$.

Their cyclic convolution is

$$
f*g=(2\cdot3+1\cdot4,\;2\cdot4+1\cdot3)=(0,1).
$$

Compare the two calculations:

| Convolve, then transform | Transform, then multiply |
|---|---|
| $T(0,1)=(1,4)$ | $T(f)=(3,1)$ |
| | $T(g)=(2,4)$ |
| | $(3\cdot2,1\cdot4)=(1,4)$ |

Both give the same result.

This is the convolution theorem, the mathematical foundation
of polynomial multiplication using number-theoretic transforms.

[Agda source](../src/Fourier/Two.agda).
