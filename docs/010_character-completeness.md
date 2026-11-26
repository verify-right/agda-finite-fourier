# Character completeness

Consider the cyclic group of order four over $\mathbb{F}_{17}$.

Every character is determined by its value at the generator 1:

$$
\chi(x)=\chi(1)^x.
$$

Since adding 1 four times gives 0,

$$
\chi(1)^4=1.
$$

There are exactly four possible values:

| $\chi(1)$ | Character values |
|---|---|
| 1 | $(1,1,1,1)$ |
| 4 | $(1,4,16,13)$ |
| 16 | $(1,16,1,16)$ |
| 13 | $(1,13,16,4)$ |

These are precisely the rows of our Fourier matrix.

## Constructive enumeration

Given an unknown character, search the table for a matching row.

Completeness guarantees that a match exists.
Uniqueness guarantees that exactly one index matches.

`RootDual.enumerate` returns the index together with
a proof that the character agrees with that row.

Proofs: [Fourier/CyclicDual.agda](../src/Fourier/CyclicDual.agda).
