{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Algebra.WeightedSums (R : CommutativeRing 0ℓ 0ℓ) where
open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Algebra.FiniteSums R

-- A constant background b and an excess s carried by the mask h.
moment : ∀ {n} → (Fin n → Carrier) → (Fin n → Carrier) → Carrier
moment {n} w f = sum n (λ x → w x * f x)

two-level : ∀ {n} b s (h f : Fin n → Carrier) →
  moment (λ x → b + s * h x) f ≈ b * sum n f + s * moment h f
two-level {n} b s h f = trans (sum-cong n _ _ λ x →
  trans (distribʳ (f x) b (s * h x)) (+-cong refl (*-assoc s (h x) (f x))))
  (trans (sum-add n _ _) (+-cong (sum-mulˡ n b f) (sum-mulˡ n s _)))

-- The mask counts an enumeration, with multiplicities.
count : ∀ {m n} → (Fin m → Fin n) → Fin n → Carrier
count {m} h x = sum m (λ i → delta (h i) x)

integrate-count : ∀ {m n} (h : Fin m → Fin n) f →
  moment (count h) f ≈ sum m (λ i → f (h i))
integrate-count {m} {n} h f = trans (sum-cong n _ _ λ x →
  sym (sum-mulʳ m (f x) (λ i → delta (h i) x)))
  (trans (sum-swap n m _) (sum-cong m _ _ λ i → select n (h i) f))
