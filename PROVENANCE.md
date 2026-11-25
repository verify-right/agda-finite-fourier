# Provenance

## Finite sums

**Mathematics:** Keith Conrad,
[Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf),
§4, equations (4.1)–(4.4).
The derivation of Fourier inversion uses Kronecker delta selection,
exchange of finite sums and distributivity.

**Formalization:** OpenAI,
[FourierIdentities.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/FourierIdentities.lean),
particularly `Spectral.freq_congr`, `freq_add`, `freq_scale`
and `freq_back`.

The Agda development reconstructs the required finite-sum
identities over arbitrary commutative rings, rather than
specializing them to complex numbers.
