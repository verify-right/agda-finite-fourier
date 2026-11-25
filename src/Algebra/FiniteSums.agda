{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Algebra.FiniteSums (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as N
open import Data.Fin.Base using (Fin)
import Data.Fin.Base as F
import Algebra.Properties.CommutativeSemigroup as CS
module Add = CS +-commutativeSemigroup

sum : (n : ℕ) → (Fin n → Carrier) → Carrier
sum N.zero f = 0#
sum (N.suc n) f = f F.zero + sum n (λ i → f (F.suc i))

sum-cong : ∀ n (f g : Fin n → Carrier) → (∀ i → f i ≈ g i) → sum n f ≈ sum n g
sum-cong N.zero f g p = refl
sum-cong (N.suc n) f g p = +-cong (p F.zero) (sum-cong n _ _ (λ i → p (F.suc i)))

sum-zero : ∀ n → sum n (λ _ → 0#) ≈ 0#
sum-zero N.zero = refl
sum-zero (N.suc n) = trans (+-cong refl (sum-zero n)) (+-identityˡ 0#)

sum-add : ∀ n (f g : Fin n → Carrier) → sum n (λ i → f i + g i) ≈ sum n f + sum n g
sum-add N.zero f g = sym (+-identityˡ 0#)
sum-add (N.suc n) f g = trans (+-cong refl (sum-add n _ _))
  (Add.interchange (f F.zero) (g F.zero) (sum n (λ i → f (F.suc i))) (sum n (λ i → g (F.suc i))))

sum-mulˡ : ∀ n c (f : Fin n → Carrier) → sum n (λ i → c * f i) ≈ c * sum n f
sum-mulˡ N.zero c f = sym (zeroʳ c)
sum-mulˡ (N.suc n) c f = trans (+-cong refl (sum-mulˡ n c _)) (sym (distribˡ c _ _))

sum-mulʳ : ∀ n c (f : Fin n → Carrier) → sum n (λ i → f i * c) ≈ sum n f * c
sum-mulʳ N.zero c f = sym (zeroˡ c)
sum-mulʳ (N.suc n) c f = trans (+-cong refl (sum-mulʳ n c _)) (sym (distribʳ c _ _))

sum-swap : ∀ m n (f : Fin m → Fin n → Carrier) →
  sum m (λ i → sum n (f i)) ≈ sum n (λ j → sum m (λ i → f i j))
sum-swap N.zero n f = sym (sum-zero n)
sum-swap (N.suc m) n f = trans (+-cong refl (sum-swap m n (λ i → f (F.suc i))))
  (sym (sum-add n (f F.zero) (λ j → sum m (λ i → f (F.suc i) j))))

delta : ∀ {n} → Fin n → Fin n → Carrier
delta F.zero F.zero = 1#
delta F.zero (F.suc j) = 0#
delta (F.suc i) F.zero = 0#
delta (F.suc i) (F.suc j) = delta i j

select : ∀ n (i : Fin n) (f : Fin n → Carrier) →
  sum n (λ j → delta i j * f j) ≈ f i
select (N.suc n) F.zero f = trans (+-cong (*-identityˡ (f F.zero))
  (trans (sum-cong n _ _ (λ j → zeroˡ (f (F.suc j)))) (sum-zero n))) (+-identityʳ (f F.zero))
select (N.suc n) (F.suc i) f = trans (+-cong (zeroˡ (f F.zero)) (select n i (λ j → f (F.suc j)))) (+-identityˡ (f (F.suc i)))

delta-sym : ∀ {n} (i j : Fin n) → delta i j ≈ delta j i
delta-sym F.zero F.zero = refl
delta-sym F.zero (F.suc j) = refl
delta-sym (F.suc i) F.zero = refl
delta-sym (F.suc i) (F.suc j) = delta-sym i j
