# Quotient characters

Project the cyclic group of order four onto the cyclic
group of order two by parity.

The kernel is $\{0,2\}$.

The two quotient characters, pulled back to the original
group, are

- $(1,1,1,1)$
- $(1,-1,1,-1)$

Their average is $(1,0,1,0)$, the indicator of the kernel.

This is what `Quotient.average` proves whenever the quotient
character table satisfies column separation and its order
is invertible in the coefficient ring.

Proofs: [Fourier/QuotientFilter.agda](../src/Fourier/QuotientFilter.agda).

## Point filters

For the identity quotient, every fiber contains exactly
one element.

The coset indicator therefore becomes the Kronecker delta:

$$
\mathbf{1}_{\pi(x)=\pi(y)}=\delta_{xy}.
$$

The point filter is a special case of the quotient filter,
not a separate theorem requiring an independent proof.
