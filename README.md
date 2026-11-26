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