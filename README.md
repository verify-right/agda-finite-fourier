# Finite Fourier theory in Agda

Constructive proofs of finite Fourier identities. Uses commutative rings from Agda standard lib.

The goal: develop reusable mathematics for number-theoretic transforms, cryptography and error-correcting codes.

## Results

### Finite sums, linearity, exchange of summation and Kronecker delta.

[FiniteSums.agda](src/Algebra/FiniteSums.agda):

Finite-sum identities over arbitrary commutative rings (including finite fields, polynomial rings e.g. numbers module 5).

Uses equality `≈` from the ring (setoid equality).

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `select : ∀ n (i : Fin n) (f : Fin n → Carrier) → sum n (λ j → delta i j * f j) ≈ f i` | Kronecker delta selection | A delta-weighted sum selects one entry. |
| `delta-sym : ∀ {n} (i j : Fin n) → delta i j ≈ delta j i` | Delta symmetry | Equality of indices is symmetric. |

Agda stdlib wrappers:

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `sum-cong : ∀ n (f g : Fin n → Carrier) → (∀ i → f i ≈ g i) → sum n f ≈ sum n g` | Congruence | Pointwise equal functions have equal sums. |
| `sum-zero : ∀ n → sum n (λ _ → 0#) ≈ 0#` | Zero sum | Summing zeros gives zero. |
| `sum-add : ∀ n (f g : Fin n → Carrier) → sum n (λ i → f i + g i) ≈ sum n f + sum n g` | Additivity | A sum distributes over addition. |
| `sum-mulˡ : ∀ n c (f : Fin n → Carrier) → sum n (λ i → c * f i) ≈ c * sum n f` | Left linearity | A constant factor can be taken outside a sum. |
| `sum-mulʳ : ∀ n c (f : Fin n → Carrier) → sum n (λ i → f i * c) ≈ sum n f * c` | Right linearity | The corresponding right multiplication law. |
| `sum-swap : ∀ m n (f : Fin m → Fin n → Carrier) → sum m (λ i → sum n (f i)) ≈ sum n (λ j → sum m (λ i → f i j))` | Exchange of finite sums | Rows and columns can be summed in either order. |

References:
- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf), §4, equations (4.1)–(4.4). The derivation of Fourier inversion uses Kronecker delta selection, exchange of finite sums and distributivity.
- openai/math,  [FourierIdentities.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/FourierIdentities.lean): `Spectral.freq_congr`, `freq_add`, `freq_scale` and `freq_back`.

## Orthogonality and Fourier inversion

Inversion argument generalized from complex numbers to commutative rings, with orthogonality and the required multiplicative inverse supplied explicitly.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `fixed-by-unit-implies-zero : ∀ q inv s → inv * (q + (- 1#)) ≈ 1# → q * s ≈ s → s ≈ 0#` | Cancellation | If multiplying by `q` leaves a value unchanged and `q − 1` is invertible, that value is zero. |
| [`character-sum-zero`](src/Fourier/Orthogonality.agda) | Character cancellation under translation | A character sum vanishes when translation preserves the sum and scales it by an appropriate factor. |
| [`unnormalized-inversion`](src/Fourier/Inversion.agda) | $LK=sI \implies L(Kf)=sf$| Applying the forward and backward transforms recovers the original input multiplied by a constant. |
| [`normalized-inversion`](src/Fourier/Inversion.agda) | $s^{-1}L(Kf)=f$| Removing the scaling factor recovers the original input exactly. |

References:
- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf). Character orthogonality and Fourier inversion.
- openai/math [FourierIdentities.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/FourierIdentities.lean). Theorems `Spectral.orth`, `freq_back` and `freq_inv`.
- Mathlib, [FiniteAbelian/Orthogonality.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean). Theorem `AddChar.expect_eq_ite`.

## Convolution and two-point Fourier transform

[Convolution](src/Fourier/Convolution.agda) over commutative rings.
The convolution theorem requires a multiplicative kernel, but
neither orthogonality nor division.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `convolution-hom` | $\widehat{f*g}=\hat f\cdot\hat g$ | Convolution becomes pointwise multiplication. |

[Two-point Fourier transform](src/Fourier/Two.agda)
on the cyclic group of order two.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `orthogonality : OrthogonalPair 2 two K K` | $K^2=2I$ | The two character rows are orthogonal. |
| `roundtrip : (f : Fin 2 → Carrier) (x : Fin 2) → transform K (transform K f) x ≈ two * f x` | $K(Kf)=2f$ | Applying the transform twice doubles the input. |
| `inversion` | $2^{-1}K(Kf)=f$ | Exact recovery when 2 is invertible. |
| `convolution-theorem` | $\widehat{f*g}=\hat f\cdot\hat g$ | XOR convolution becomes pointwise multiplication. |

References:
- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf), Exercise 4.10(b), p. 18.
- openai/math, [FourierIdentities.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/FourierIdentities.lean): `Spectral.freq_cyclic`.
- [Convolution theorem](https://en.wikipedia.org/wiki/Convolution_theorem).

## Number-theoretic transforms

[Examples](src/Fourier/Examples.agda) computed modulo 17.

| Agda theorem | Meaning |
|---|---|
| `four` | Four-point NTT. |
| `eight` | Eight-point NTT. |
| `product` | Polynomial multiplication using an NTT. |
| `nonorthogonal-sum` | Counterexample to orthogonality modulo 15. |

References:
- J. M. Pollard, [The Fast Fourier Transform in a Finite field](https://doi.org/10.1090/S0025-5718-1971-0301966-0), 1971.

## Character orthogonality

[Characters](src/Fourier/Characters.agda) of finite abelian groups
with values in a commutative ring.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `annihilates-sum` | $(\chi(t)-1)\sum_x\chi(x)=0$ | Character differences annihilate the character sum. |
| `character-zero` | $\sum_x\chi(x)=0$ | The sum vanishes when the differences have trivial common annihilator. |
| `gram` | $\sum_k U_x(k)V_y(k)=n\delta_{xy}$ | Orthogonality of reciprocal, separating character families. |

References:
- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf).
- Mathlib, [Orthogonality.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean): `AddChar.expect_eq_ite`.
- Agda stdlib, [CommutativeMonoid.Sum](https://github.com/agda/agda-stdlib/blob/v2.4.1/src/Algebra/Properties/CommutativeMonoid/Sum.agda): `∑-permute`.

## Bicharacters and Fourier equivalence

[Bicharacters](src/Fourier/Pairing.agda) and
[Fourier duality](src/Fourier/Duality.agda).

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `left-gram` | $LK=nI$ | Column orthogonality. |
| `right-gram` | $KL=nI$ | Row orthogonality. |
| `matrix-linear` | Linearity | The transform preserves addition and scalar multiplication. |
| `equivalence` | $K^{-1}=n^{-1}L$ | Mutually inverse linear transforms when both character families separate and the group order is invertible. |

References:
- [Bicharacter](https://en.wikipedia.org/wiki/Bicharacter).
- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf).
- Mathlib, [ZMod.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/ZMod.lean).

## Cyclic Fourier inversion

[Cyclic Fourier transforms](src/Fourier/Cyclic.agda)
over integral domains containing a primitive root of unity.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `Root.table` | $K(k,x)=q^{kx}$ | Character table generated by a root of unity. |
| `Root.injective` | $q^i=q^j\implies i=j$ | Distinct indices give distinct powers of a primitive root. |
| `Root.cyclic-inversion` | $K^{-1}=n^{-1}L$ | Fourier inversion when the length is invertible. |

References:
- J. M. Pollard, [The Fast Fourier Transform in a Finite Field](https://doi.org/10.1090/S0025-5718-1971-0301966-0), 1971.
- Isabelle AFP, [Number Theoretic Transform](https://isa-afp.org/entries/Number_Theoretic_Transform.html).
- Mathlib, [Number-theoretic transform PR #41924](https://github.com/leanprover-community/mathlib4/pull/41924).
- [Primitive roots of unity](https://en.wikipedia.org/wiki/Root_of_unity).

## Group convolution

[GroupConvolution.agda](src/Fourier/GroupConvolution.agda)

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `fiber-sum` | $(f*g)(z)=\sum_x f(x)g(z-x)$ | Reduces convolution to a single sum. |
| `convolution-transform` | $\widehat{f*g}=\hat f\cdot\hat g$ | Fourier transforms turn group convolution into pointwise multiplication. |

References:
- Keith Conrad, [Characters of Finite Abelian Groups](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf).
- [Circular convolution](https://en.wikipedia.org/wiki/Circular_convolution).
- openai/math, [FourierIdentities.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/FourierIdentities.lean): `Spectral.freq_cyclic`.

## Additive characters and character filters

[AdditiveKernel.agda](src/Fourier/AdditiveKernel.agda),
[Filters.agda](src/Fourier/Filters.agda)

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `primitive-inversion` | $LK=nI$ | Fourier inversion from a primitive additive character and regularity of nonzero coefficients. |
| `primitive-duality` | $K^{-1}=n^{-1}L$ | Two-sided inversion when the group order is invertible. |
| `filter-count` | Fourier reconstruction | Recover the multiplicity of each element in a finite collection. |
| `absent`, `present` | Membership indicator | Recover set membership from its spectrum, assuming an injective enumeration for `present`. |
| `vanishes`, `survives` | Coset character sums | Only characters trivial on the subgroup survive, when nontrivial restrictions satisfy separation. |

References:
- openai/math, [FiniteFourier.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean): `transform_inversion`.
- Mathlib, [AddCharacter.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean): `sum_mulShift`.
- grh-lean, [FiniteFourier.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/General/Analysis/FiniteFourier.lean): `sum_addChar_dotProduct`, `sum_addChar_trace_mul`.

## Fourier algebra isomorphism

[Algebra.agda](src/Fourier/Algebra.agda)

| Agda theorem | Meaning |
|---|---|
| `fourier-isomorphism : Hom.IsRingIsomorphism to` | Fourier transformation is a ring isomorphism between convolution and pointwise multiplication. |
| `inverse-coordinates` | A convolution inverse becomes a pointwise reciprocal. |
| `synthesize-inverse` | Construct a convolution inverse from pointwise reciprocals. |

Requires a separated bicharacter and an invertible group order.

References:
- P. J. Nicholson, [Algebraic Theory of Finite Fourier Transforms](https://doi.org/10.1016/S0022-0000(71)80014-4), 1971, Theorem 3.1.
- Agda stdlib: `Algebra.Construct.Pointwise`,
  `Algebra.Morphism.RingMonomorphism`.
