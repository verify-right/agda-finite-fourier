# Theorems

## [Finite sums](src/Algebra/FiniteSums.agda)

All identities work in any commutative ring `R` (including finite fields, polynomial rings e.g. numbers module 5).

Equality `≈` is defined in the ring (setoid equality).

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `sum-cong : ∀ n (f g : Fin n → Carrier) → (∀ i → f i ≈ g i) → sum n f ≈ sum n g` | Congruence | Pointwise equal functions have equal sums. |
| `sum-zero : ∀ n → sum n (λ _ → 0#) ≈ 0#` | Zero sum | Summing zeros gives zero. |
| `sum-add : ∀ n (f g : Fin n → Carrier) → sum n (λ i → f i + g i) ≈ sum n f + sum n g` | Additivity | A sum distributes over addition. |
| `sum-mulˡ : ∀ n c (f : Fin n → Carrier) → sum n (λ i → c * f i) ≈ c * sum n f` | Left linearity | A constant factor can be taken outside a sum. |
| `sum-mulʳ : ∀ n c (f : Fin n → Carrier) → sum n (λ i → f i * c) ≈ sum n f * c` | Right linearity | The corresponding right multiplication law. |
| `sum-swap : ∀ m n (f : Fin m → Fin n → Carrier) → sum m (λ i → sum n (f i)) ≈ sum n (λ j → sum m (λ i → f i j))` | Exchange of finite sums | Rows and columns can be summed in either order. |
| `select : ∀ n (i : Fin n) (f : Fin n → Carrier) → sum n (λ j → delta i j * f j) ≈ f i` | Kronecker delta selection | A delta-weighted sum selects one entry. |
| `delta-sym : ∀ {n} (i j : Fin n) → delta i j ≈ delta j i` | Delta symmetry | Equality of indices is symmetric. |
