{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ)
module Fourier.CyclicDual (R : CommutativeRing 0ℓ 0ℓ) (m : ℕ) where

open CommutativeRing R
open import Fourier.CyclicGroup m
open import Fourier.Cyclic R m
open import Fourier.Separation R
open import Fourier.Characters R
open import Fourier.Duality R
open import Fourier.Inversion R
import Algebra.FinitePowerOrder *-monoid as O
import Fourier.Complete R as C
open import Relation.Nullary.Decidable using (Dec)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product.Base using (Σ)
import Relation.Binary.PropositionalEquality as E

module RootDual (q : Carrier) (period : O.Period q p) where
  open Root q period
  unique : Exact → ∀ i j → (∀ t → K i t ≈ K j t) → i E.≡ j
  unique exact i j eq = injective exact i j (trans (sym (generator i)) (trans (eq (wrap 1)) (generator j)))

  enumerate : Exact → NonzeroRegular → (u : Carrier) → u * order p ≈ 1# →
    (∀ a b → Dec (a ≈ b)) → ¬ (1# ≈ 0#) → ∀ c → Σ I (λ k → ∀ x → value c x ≈ K k x)
  enumerate exact reg u unit dec nz = C.Basis.complete cyclic cyclic table reg dec nz inj
    where
    open LinearEquivalence (cyclic-inversion exact reg u unit)
    inj : ∀ f g → (∀ i → transform K f i ≈ transform K g i) → ∀ i → f i ≈ g i
    inj f g eq i = trans (sym (left f i)) (trans (Linear.respects from-linear _ _ eq i) (left g i))
