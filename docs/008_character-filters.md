# Character filters

Work in $\mathbb{F}_{17}$ on the cyclic group
$\mathbb{Z}/4\mathbb{Z}$.

## Encoding a set

Consider the set $A=\{1,3\}$.

Its membership vector is $(0,1,0,1)$.

Using the primitive root 4, define its spectrum:

$$
S(k)=\sum_{x\in A}4^{kx}.
$$

| $k$ | $S(k)$ |
|---|---|
| 0 | 2 |
| 1 | 0 |
| 2 | 15 |
| 3 | 0 |

The inverse Fourier transform recovers $(0,1,0,1)$.

This is what `filter-count` proves. If an element occurs
several times, the result counts its occurrences in the
coefficient ring.

## Cosets and cancellation

Our set is the coset $1+H$, where $H=\{0,2\}$.

For any character $\chi$,

$$
\sum_{x\in 1+H}\chi(x)
=\chi(1)\sum_{h\in H}\chi(h).
$$

For $\chi(x)=4^x$, the inner sum is $1+16=0$ modulo 17.

For $\chi(x)=16^x$, the inner sum is $1+1=2$.

Characters therefore distinguish cosets through their
restrictions to subgroups.

This cancellation is used in number theory, harmonic
analysis and coding theory.

[Agda proofs](../src/Fourier/Filters.agda).
