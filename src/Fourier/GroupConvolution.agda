{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.GroupConvolution (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Fourier.Enumeration
open import Algebra.FiniteSums R
open import Fourier.Reindex R
open import Fourier.Convolution R
open import Fourier.Inversion R

module On {n} (G : Group n) where
  open Group G using (_∙_; neg; translate)

  difference : (Fin n → Carrier) → (Fin n → Carrier) → Fin n → Carrier
  difference f g z = sum n (λ x → f x * g (neg x ∙ z))

  fiber-sum : ∀ f g z → convolution _∙_ f g z ≈ difference f g z
  fiber-sum f g z = sum-cong n _ _ (λ x → trans
    (sum-cong n _ _ (λ y → *-cong
      (trans (delta-sym z (x ∙ y)) (transport-delta (translate x) y z)) refl))
    (select n (neg x ∙ z) (λ y → f x * g y)))

  convolution-transform : ∀ (K : Fin n → Fin n → Carrier) →
    (∀ k x y → K k (x ∙ y) ≈ K k x * K k y) → ∀ f g k →
    transform K (difference f g) k ≈ transform K f k * transform K g k
  convolution-transform K mult f g k = trans
    (sum-cong n _ _ (λ z → *-cong refl (sym (fiber-sum f g z))))
    (convolution-hom _∙_ K mult f g k)
