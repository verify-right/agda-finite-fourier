{-# OPTIONS --safe --without-K #-}

module Fourier.Examples where

open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as N
open import Data.Integer.Base using (ℤ; +_; _^_; _%ℕ_)
open import Data.Integer.Properties using (+-*-commutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Data.Fin.Base as F
import Data.Vec.Base as V
import Fourier.Inversion +-*-commutativeRing as FT

ntt : ∀ {n} → ℤ → V.Vec ℤ n → V.Vec ℕ n
ntt root xs = V.tabulate λ i →
  FT.transform
    (λ k j → root ^ (F.toℕ k N.* F.toℕ j))
    (V.lookup xs) i %ℕ 17

four : ntt (+ 4) (V.tabulate {n = 4} λ i → + (F.toℕ i))
  ≡ 6 V.∷ 7 V.∷ 15 V.∷ 6 V.∷ V.[]
four = refl

eight : ntt (+ 2) (V.tabulate {n = 8} λ i → + (F.toℕ i))
  ≡ 11 V.∷ 8 V.∷ 14 V.∷ 6 V.∷ 13 V.∷ 3 V.∷ 12 V.∷ 1 V.∷ V.[]
eight = refl

f g : V.Vec ℤ 4
f = (+ 1) V.∷ (+ 2) V.∷ (+ 0) V.∷ (+ 0) V.∷ V.[]
g = (+ 3) V.∷ (+ 1) V.∷ (+ 0) V.∷ (+ 0) V.∷ V.[]

product-values : V.Vec ℕ 4
product-values =
  V.zipWith (λ a b → (a N.* b) N.% 17)
    (ntt (+ 4) f) (ntt (+ 4) g)

product : V.map (λ a → (13 N.* a) N.% 17)
  (ntt (+ 13) (V.map +_ product-values))
  ≡ 3 V.∷ 7 V.∷ 2 V.∷ 0 V.∷ V.[]
product = refl

-- Exact root order is insufficient over rings with zero divisors.

order-two : (4 N.* 4) N.% 15 ≡ 1
order-two = refl

inverse-of-two : (8 N.* 2) N.% 15 ≡ 1
inverse-of-two = refl

nonorthogonal-sum : (1 N.+ 4) N.% 15 ≡ 5
nonorthogonal-sum = refl
