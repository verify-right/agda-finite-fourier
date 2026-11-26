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

See: [Conrad]; [OpenAI FourierIdentities.lean] `Spectral.freq_congr`, `freq_add`, `freq_scale` and `freq_back`.

## Orthogonality and Fourier inversion

Inversion argument generalized from complex numbers to commutative rings, with orthogonality and the required multiplicative inverse supplied explicitly.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `fixed-by-unit-implies-zero : ∀ q inv s → inv * (q + (- 1#)) ≈ 1# → q * s ≈ s → s ≈ 0#` | Cancellation | If multiplying by `q` leaves a value unchanged and `q − 1` is invertible, that value is zero. |
| [`character-sum-zero`](src/Fourier/Orthogonality.agda) | Character cancellation under translation | A character sum vanishes when translation preserves the sum and scales it by an appropriate factor. |
| [`unnormalized-inversion`](src/Fourier/Inversion.agda) | $LK=sI \implies L(Kf)=sf$| Applying the forward and backward transforms recovers the original input multiplied by a constant. |
| [`normalized-inversion`](src/Fourier/Inversion.agda) | $s^{-1}L(Kf)=f$| Removing the scaling factor recovers the original input exactly. |

See: [Conrad]; [OpenAI FourierIdentities.lean] `Spectral.orth`, `freq_back` and `freq_inv`;  [Mathlib Orthogonality.lean] `AddChar.expect_eq_ite`.

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
| `convolution-theorem` | $\widehat{f*g}=\hat f\cdot\hat g$ | XOR [convolution](https://en.wikipedia.org/wiki/Convolution_theorem) becomes pointwise multiplication. |

See: [Conrad] exercise 4.10(b) p. 18; [OpenAI FourierIdentities.lean] `Spectral.freq_cyclic`

## Number-theoretic transforms

[Examples](src/Fourier/Examples.agda) computed modulo 17.

| Agda theorem | Meaning |
|---|---|
| `four` | Four-point NTT. |
| `eight` | Eight-point NTT. |
| `product` | Polynomial multiplication using an NTT. |
| `nonorthogonal-sum` | Counterexample to orthogonality modulo 15. |

See: [Pollard].

## Character orthogonality

[Characters](src/Fourier/Characters.agda) of finite abelian groups
with values in a commutative ring.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `annihilates-sum` | $(\chi(t)-1)\sum_x\chi(x)=0$ | Character differences annihilate the character sum. |
| `character-zero` | $\sum_x\chi(x)=0$ | The sum vanishes when the differences have trivial common annihilator. |
| `gram` | $\sum_k U_x(k)V_y(k)=n\delta_{xy}$ | Orthogonality of reciprocal, separating character families. |

See: [Conrad]; [Mathlib Orthogonality.lean] `AddChar.expect_eq_ite`; Agda stdlib [CommutativeMonoid.Sum](https://github.com/agda/agda-stdlib/blob/v2.4.1/src/Algebra/Properties/CommutativeMonoid/Sum.agda): `∑-permute`.

## Bicharacters and Fourier equivalence

[Bicharacters](src/Fourier/Pairing.agda) and
[Fourier duality](src/Fourier/Duality.agda).

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `left-gram` | $LK=nI$ | Column orthogonality. |
| `right-gram` | $KL=nI$ | Row orthogonality. |
| `matrix-linear` | Linearity | The transform preserves addition and scalar multiplication. |
| `equivalence` | $K^{-1}=n^{-1}L$ | Mutually inverse linear transforms when [both character](https://en.wikipedia.org/wiki/Bicharacter) families separate and the group order is invertible. |

See: [Conrad]; [Mathlib ZMod.lean].

## Cyclic Fourier inversion

[Cyclic Fourier transforms](src/Fourier/Cyclic.agda)
over integral domains containing a primitive root of unity.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `Root.table` | $K(k,x)=q^{kx}$ | Character table generated by a root of unity. |
| `Root.injective` | $q^i=q^j\implies i=j$ | Distinct indices give distinct powers of a [primitive root](https://en.wikipedia.org/wiki/Root_of_unity). |
| `Root.cyclic-inversion` | $K^{-1}=n^{-1}L$ | Fourier inversion when the length is invertible. |

See: [Pollard]; [Isabelle NTT]; [Mathlib NTT PR #41924]

## Group convolution

[GroupConvolution.agda](src/Fourier/GroupConvolution.agda)

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `fiber-sum` | $(f*g)(z)=\sum_x f(x)g(z-x)$ | Reduces convolution to a single sum. |
| `convolution-transform` | $\widehat{f*g}=\hat f\cdot\hat g$ | Fourier transforms turn group convolution into pointwise multiplication. |

See: [Conrad]; Wiki [circular convolution](https://en.wikipedia.org/wiki/Circular_convolution); [OpenAI FourierIdentities.lean]: `Spectral.freq_cyclic`.

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

See: [OpenAI FiniteFourier.lean] `transform_inversion`; [Mathlib AddCharacter.lean] `sum_mulShift`; [Compressed GRH LocalHomUnit.lean] `sum_addChar_dotProduct`, `sum_addChar_trace_mul`.

## Fourier algebra isomorphism

[Algebra.agda](src/Fourier/Algebra.agda)

| Agda theorem | Meaning |
|---|---|
| `fourier-isomorphism : Hom.IsRingIsomorphism to` | Fourier transformation is a ring isomorphism between convolution and pointwise multiplication. |
| `inverse-coordinates` | A convolution inverse becomes a pointwise reciprocal. |
| `synthesize-inverse` | Construct a convolution inverse from pointwise reciprocals. |

Requires a separated bicharacter and an invertible group order.

See: [Nicholson]; Agda stdlib: `Algebra.Construct.Pointwise`, `Algebra.Morphism.RingMonomorphism`.

## Character completeness

Every character occurs in an injective Fourier table over
a nontrivial integral domain with decidable equality.

| Agda theorem | Meaning |
|---|---|
| [`Basis.complete`](src/Fourier/Complete.agda) | Constructively find the index of any character in the table. |
| [`RootDual.unique`](src/Fourier/CyclicDual.agda) | Distinct indices define distinct cyclic characters. |
| [`RootDual.enumerate`](src/Fourier/CyclicDual.agda) | Enumerate all cyclic characters using a primitive root of unity, assuming the group order is invertible. |

See: [Conrad]; [Mathlib Duality.lean]
`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`.

## Constructive enumeration

[CyclicDual.agda](src/Fourier/CyclicDual.agda)

Given an unknown character, search the table for a matching row.

Completeness guarantees that a match exists.
Uniqueness guarantees that exactly one index matches.

`RootDual.enumerate` returns the index together with
a proof that the character agrees with that row.

## Product-group Fourier transforms

[ProductTable.agda](src/Fourier/ProductTable.agda)

| Agda theorem | Mathematical content |
|---|---|
| `Restrict.factors` | Every character on a product group factors into characters on its two axes. |
| `Tables.complete` | Complete character tables on both axes give a complete product table. |
| `Tables.factorization` | The product Fourier transform equals successive transforms along each axis. |

See: [Conrad], [Good], [OpenAI ChineseRemainder.lean]: `Grove.gale_tide`, `Grove.graft_ford`.

The product factorization does not require coprimality.
The Good–Thomas FFT additionally requires a CRT reindexing
between cyclic and product coordinates.

## Quotient characters

[QuotientFilter.agda](src/Fourier/QuotientFilter.agda)

A character trivial on the kernel of a quotient map
factors uniquely through that quotient.

| Theorem | Result |
|---|---|
| `Descend.factors`, `Descend.unique` | Universal property of character descent. |
| `all-trivial`, `distinct-pulls` | Complete, distinct enumeration of characters trivial on the kernel. |
| `average` | Character average gives the kernel indicator. |
| `scaled-coset` | Character sum detects membership in a coset. |

Constructive counterpart of [OpenAI RayOrthogonality.lean],
`sum_characters_unit` and `average_characters`,
using an explicit quotient and section.

Related to [Alpöge–Claude ChBalance.lean] and [Conrad].

The point filter in [Filters.agda](src/Fourier/Filters.agda)
is the special case of `scaled-coset` where the quotient
map is the identity.

## References

### Mathematical literature

- Keith [Conrad], *Characters of Finite Abelian Groups*, §4.
- P. J. [Nicholson], *Algebraic Theory of Finite Fourier Transforms* (1971), Theorem 3.1.
- J. M. [Pollard], *The Fast Fourier Transform in a Finite Field* (1971).
- I. J. [Good], *The Interaction Algorithm and Practical Fourier Analysis* (1958).
- [Milne], *Class Field Theory*.

### Related formalizations

- [OpenAI FourierIdentities.lean] - inversion and convolution.
- [OpenAI ChineseRemainder.lean] - product transforms and CRT.
- [OpenAI FiniteFourier.lean] - primitive additive characters.
- [OpenAI RayOrthogonality.lean] - quotient character filters.
- [Alpöge–Claude ChBalance.lean] - arithmetic character sums.
- [Compressed GRH LocalHomUnit.lean] - additive character orthogonality and matrix Fourier inversion.
- [Mathlib Orthogonality.lean] - character orthogonality.
- [Mathlib Duality.lean] - finite abelian group duality.
- [Mathlib MulChar Duality.lean] - multiplicative character duality.
- [Mathlib AddCharacter.lean] - primitive additive characters.
- [Mathlib ZMod.lean] - cyclic Fourier transforms.
- [Isabelle NTT] - verified number-theoretic transforms.
- [When Agda met Vampire] - FFT formalization in Agda.

[Conrad]: https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf
[Nicholson]: https://doi.org/10.1016/S0022-0000(71)80014-4
[Pollard]: https://doi.org/10.1090/S0025-5718-1971-0301966-0
[Good]: https://doi.org/10.1111/j.2517-6161.1958.tb00300.x
[Milne]: https://www.jmilne.org/math/CourseNotes/CFT.pdf
[OpenAI FourierIdentities.lean]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/FourierIdentities.lean
[OpenAI ChineseRemainder.lean]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FourierTransform/ChineseRemainder.lean
[OpenAI FiniteFourier.lean]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean
[OpenAI RayOrthogonality.lean]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean
[Alpöge–Claude ChBalance.lean]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean
[Compressed GRH LocalHomUnit.lean]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/GaussSum/LocalHomUnit.lean
[Mathlib Orthogonality.lean]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean
[Mathlib Duality.lean]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/FiniteAbelian/Duality.lean
[Mathlib MulChar Duality.lean]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/MulChar/Duality.lean
[Mathlib AddCharacter.lean]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean
[Mathlib ZMod.lean]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/ZMod.lean
[Isabelle NTT]: https://isa-afp.org/entries/Number_Theoretic_Transform.html
[When Agda met Vampire]: https://arxiv.org/abs/2602.18844
[Mathlib NTT PR #41924]: https://github.com/leanprover-community/mathlib4/pull/41924
