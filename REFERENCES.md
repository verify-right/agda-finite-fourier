# References

## Finite sums

- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf), §4, equations (4.1)–(4.4).
The derivation of Fourier inversion uses Kronecker delta selection, exchange of finite sums and distributivity.

- openai/math,  [FourierIdentities.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/FourierIdentities.lean): `Spectral.freq_congr`, `freq_add`, `freq_scale` and `freq_back`.

## Orthogonality and Fourier inversion

- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf). Character orthogonality and Fourier inversion.
- openai/math [FourierIdentities.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/FourierIdentities.lean). Theorems `Spectral.orth`, `freq_back` and `freq_inv`.
- Mathlib, [FiniteAbelian/Orthogonality.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean). Theorem `AddChar.expect_eq_ite`.
