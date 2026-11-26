{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Convolution (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Algebra.FiniteSums R
import Fourier.Inversion R as FT
import Algebra.Properties.CommutativeSemigroup as CS
module Mul = CS *-commutativeSemigroup

-- Push a pair of indices forward along any binary operation. This form does
-- not need a group, subtraction, invertibility, associativity, or a unit.
convolution : ∀ {n} → (Fin n → Fin n → Fin n) →
  (Fin n → Carrier) → (Fin n → Carrier) → Fin n → Carrier
convolution {n} op f g z = sum n (λ x → sum n (λ y → delta z (op x y) * (f x * g y)))

select-weighted : ∀ n (w : Fin n → Carrier) (t : Fin n) c →
  sum n (λ z → w z * (delta z t * c)) ≈ w t * c
select-weighted n w t c = trans (sum-cong n _ _ (λ z →
  trans (sym (*-assoc (w z) (delta z t) c))
  (*-cong (trans (*-comm (w z) (delta z t)) (*-cong (delta-sym z t) refl)) refl)))
  (trans (sum-mulʳ n c (λ z → delta t z * w z)) (*-cong (select n t w) refl))

-- A multiplicative kernel converts pushforward convolution into pointwise
-- multiplication. No orthogonality or division by n is needed here.
convolution-hom : ∀ {n} (op : Fin n → Fin n → Fin n)
  (K : Fin n → Fin n → Carrier) →
  (∀ k x y → K k (op x y) ≈ K k x * K k y) →
  (f g : Fin n → Carrier) (k : Fin n) →
  FT.transform K (convolution op f g) k ≈ FT.transform K f k * FT.transform K g k
convolution-hom {n} op K character f g k =
  trans (sum-cong n _ _ (λ z → sym (sum-mulˡ n (K k z)
    (λ x → sum n (λ y → delta z (op x y) * (f x * g y))))))
  (trans (sum-swap n n (λ z x → K k z * sum n (λ y → delta z (op x y) * (f x * g y))))
  (trans (sum-cong n _ _ (λ x → trans
    (sum-cong n _ _ (λ z → sym (sum-mulˡ n (K k z) (λ y → delta z (op x y) * (f x * g y)))))
    (trans (sum-swap n n (λ z y → K k z * (delta z (op x y) * (f x * g y))))
      (sum-cong n _ _ (λ y → select-weighted n (K k) (op x y) (f x * g y))))))
  (trans (sum-cong n _ _ (λ x → trans
    (sum-cong n _ _ (λ y → trans (*-cong (character k x y) refl)
      (Mul.medial (K k x) (K k y) (f x) (g y))))
    (sum-mulˡ n (K k x * f x) (λ y → K k y * g y))))
  (sum-mulʳ n (FT.transform K g k) (λ x → K k x * f x)))))
