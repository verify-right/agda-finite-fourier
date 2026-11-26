{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Inversion (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Algebra.FiniteSums R

-- K indexes frequencies by rows and input positions by columns.
transform : ∀ {n} → (Fin n → Fin n → Carrier) → (Fin n → Carrier) → Fin n → Carrier
transform {n} K f k = sum n (λ x → K k x * f x)

-- The pairing is supplied explicitly. This theorem does not assert that an
-- arbitrary character family over an arbitrary ring is orthogonal.
record OrthogonalPair (n : ℕ) (size : Carrier)
  (forward backward : Fin n → Fin n → Carrier) : Set where
  field
    orthogonal : ∀ x y → sum n (λ k → backward x k * forward k y) ≈ size * delta x y
open OrthogonalPair

unnormalized-inversion : ∀ {n} {size} {K L : Fin n → Fin n → Carrier} →
  OrthogonalPair n size K L → (f : Fin n → Carrier) → (x : Fin n) →
  transform L (transform K f) x ≈ size * f x
unnormalized-inversion {n} {size} {K} {L} O f x =
  trans (sum-cong n _ _ (λ k → sym (sum-mulˡ n (L x k) (λ y → K k y * f y))))
  (trans (sum-swap n n (λ k y → L x k * (K k y * f y)))
  (trans (sum-cong n _ _ (λ y → trans
    (sum-cong n _ _ (λ k → sym (*-assoc (L x k) (K k y) (f y))))
    (sum-mulʳ n (f y) (λ k → L x k * K k y))))
  (trans (sum-cong n _ _ (λ y → trans (*-cong (orthogonal O x y) refl)
    (*-assoc size (delta x y) (f y))))
  (trans (sum-mulˡ n size (λ y → delta x y * f y))
    (*-cong refl (select n x f))))))

normalized-inversion : ∀ {n} {size inv : Carrier} {K L : Fin n → Fin n → Carrier} →
  OrthogonalPair n size K L → inv * size ≈ 1# → (f : Fin n → Carrier) → (x : Fin n) →
  inv * transform L (transform K f) x ≈ f x
normalized-inversion O unit f x =
  trans (*-cong refl (unnormalized-inversion O f x))
    (trans (sym (*-assoc _ _ _)) (trans (*-cong unit refl) (*-identityˡ (f x))))
