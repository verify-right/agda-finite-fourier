{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (Monoid)

module Algebra.FinitePowerOrder {a ℓ} (M : Monoid a ℓ) where

open Monoid M
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; >-nonZero)
import Data.Nat.Properties as N
open import Data.Nat.Divisibility using (_∣_; ∣⇒≤)
open import Data.Nat.GCD using (gcd; gcd-GCD; gcd[m,n]∣m; gcd[m,n]∣n; module Bézout)
open import Data.Nat.Primality using (Prime)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Fin.Properties as F
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
import Relation.Binary.PropositionalEquality as E
open E using (_≡_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Reasoning.Setoid setoid
import Algebra.Properties.Monoid.Mult M as Mult

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ n = n Mult.× x

Period : Carrier → ℕ → Set ℓ
Period x n = (x ^ n) ≈ ε

unit-power : ∀ n → ε ^ n ≈ ε
unit-power zero = refl
unit-power (suc n) = trans (identityˡ (ε ^ n)) (unit-power n)

period-multiple : ∀ x n → Period x n → ∀ k → Period x (k ℕ.* n)
period-multiple x n h k = trans (sym (Mult.×-assocˡ x k n))
  (trans (Mult.×-congʳ k h) (unit-power k))

-- A known period supplies the left inverse needed to cancel a power.
cancel-power : ∀ x t i → i ≤ t → Period x t → ∀ {u v} →
  x ^ i ∙ u ≈ x ^ i ∙ v → u ≈ v
cancel-power x t i i≤t ht {u} {v} eq = begin
  u                         ≈⟨ sym (identityˡ u) ⟩
  ε ∙ u                     ≈⟨ ∙-cong (sym inverse) refl ⟩
  (x ^ (t ∸ i) ∙ x ^ i) ∙ u ≈⟨ assoc _ _ _ ⟩
  x ^ (t ∸ i) ∙ (x ^ i ∙ u) ≈⟨ ∙-cong refl eq ⟩
  x ^ (t ∸ i) ∙ (x ^ i ∙ v) ≈⟨ sym (assoc _ _ _) ⟩
  (x ^ (t ∸ i) ∙ x ^ i) ∙ v ≈⟨ ∙-cong inverse refl ⟩
  ε ∙ v                     ≈⟨ identityˡ v ⟩
  v                         ∎
  where
  inverse : x ^ (t ∸ i) ∙ x ^ i ≈ ε
  inverse = trans (sym (Mult.×-homo-+ x (t ∸ i) i))
    (trans (Mult.×-congˡ (E.trans (N.+-comm (t ∸ i) i) (N.m+[n∸m]≡n i≤t))) ht)

collision-period : ∀ x t i j → i ≤ t → i ≤ j → Period x t →
  x ^ i ≈ x ^ j → Period x (j ∸ i)
collision-period x t i j i≤t i≤j ht eq = cancel-power x t i i≤t ht
  (trans (sym (Mult.×-homo-+ x i (j ∸ i)))
    (trans (Mult.×-congˡ (N.m+[n∸m]≡n i≤j))
      (trans (sym eq) (sym (identityʳ (x ^ i))))))

