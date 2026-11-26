# Bicharacters and Fourier equivalence

Work in $\mathbb{F}_{17}$ with the cyclic group
$\mathbb{Z}/4\mathbb{Z}$.

## Bicharacters

Define $K(k,x)=4^{kx}$ modulo 17.

A bicharacter is a character in both arguments:

$$
K(k,x+y)=K(k,x)K(k,y)
$$

$$
K(k+l,x)=K(k,x)K(l,x)
$$

Its character table is

$$
K=
\begin{pmatrix}
1&1&1&1\\
1&4&16&13\\
1&16&1&16\\
1&13&16&4
\end{pmatrix}
$$

## Orthogonality

Define the reciprocal kernel $L(x,k)=4^{-kx}$.

Character orthogonality gives

$$
LK=KL=4I.
$$

These are `left-gram` and `right-gram`.

## Linear equivalence

Since the inverse of 4 modulo 17 is 13,

$$
K^{-1}=13L.
$$

We can move between coefficient and evaluation
representations without losing information.

Both transforms preserve addition and scalar multiplication.

This is what `Dual.equivalence` proves, provided both
character families satisfy the separation conditions
and the group order is invertible.

[Agda proofs](../src/Fourier/Duality.agda).
