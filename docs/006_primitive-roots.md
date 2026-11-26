# Primitive roots and Fourier inversion

Work in $\mathbb{F}_{17}$.

The powers of 4 are

$$
4^0=1,\quad 4^1=4,\quad 4^2=16,\quad 4^3=13,\quad 4^4=1.
$$

The smallest positive exponent giving 1 is 4.
We call 4 a primitive fourth root of unity.

## Why primitive roots matter

Using $q=4$, define the Fourier kernel

$$
K(k,x)=q^{kx}.
$$

Distinct powers give distinct characters.
Character orthogonality then gives

$$
LK=KL=4I,
$$

where $L(x,k)=q^{-kx}$.

Since 4 is invertible modulo 17, the transform is invertible.

## What can go wrong?

The number 16 has order two modulo 17.
Using it for a four-point transform produces repeated rows.
The transform loses information and cannot be inverted.

A root of unity must have the correct order.

[Agda proofs](../src/Fourier/Cyclic.agda).
