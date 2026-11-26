# Character orthogonality

## Characters

Consider the cyclic group $\mathbb{Z}/4\mathbb{Z}$
and arithmetic in $\mathbb{F}_{17}$.

Since 4 is a primitive fourth root of unity modulo 17,
we can define a character $\chi(x)=4^x$.

A character turns group addition into multiplication:

$$
\chi(x+y)=\chi(x)\chi(y)
$$

## Character cancellation

| $x$ | $\chi(x)$ |
|---|---|
| 0 | 1 |
| 1 | 4 |
| 2 | 16 |
| 3 | 13 |

The character sum is

$$
S=1+4+16+13=0\pmod{17}.
$$

Why does it vanish?

Translation by 1 permutes the group elements without
changing the sum. But it also multiplies every character
value by 4.

Therefore $S=4S$, so $3S=0$.

Since 3 is invertible modulo 17, we obtain $S=0$.

This is what `annihilates-sum` and `character-zero` prove.

## Why the ring matters

Consider arithmetic modulo 15 instead.

The number 4 has order two, but its character sum is

$$
S=1+4=5\pmod{15}.
$$

Translation still gives $3S=0$, but $S$ is not zero.

The problem is that 3 is a zero divisor modulo 15.

Our general theorem requires the character differences
to have no common nonzero annihilator. This is weaker
than requiring an invertible difference.

## Fourier orthogonality

Distinct characters cancel when paired with each other's
inverse:

$$
\sum_x \chi_i(x)\chi_j(x)^{-1}=4\delta_{ij}.
$$

This is the orthogonality identity needed for Fourier inversion.

References:
- [Character theory](https://en.wikipedia.org/wiki/Character_theory)
- [Zero divisor](https://en.wikipedia.org/wiki/Zero_divisor)
- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf).

[Agda proofs](../src/Fourier/Characters.agda).
