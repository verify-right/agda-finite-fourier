{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Data.Nat.Base as N using (ℕ; suc)
module Fourier.Cyclic (R : CommutativeRing 0ℓ 0ℓ) (m : ℕ) where

open CommutativeRing R
open import Fourier.CyclicGroup m
open import Data.Fin.Base using (toℕ)
import Data.Fin.Properties as FP
import Data.Nat.Properties as NP
import Data.Nat.DivMod as D
import Algebra.Properties.Monoid.Mult *-monoid as Pow
import Algebra.FinitePowerOrder *-monoid as O
open import Fourier.Characters R
open import Fourier.Pairing R
open import Fourier.Duality R
open import Fourier.Separation R
import Relation.Binary.PropositionalEquality as E
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (_,_)

open import Fourier.Power *-commutativeMonoid public using (power-product)

module Root (q : Carrier) (period : O.Period q p) where
  phase : ℕ → Carrier
  phase = O._^_ q

  reduced : ∀ a → phase (D._%_ a p) ≈ phase a
  reduced a = sym (trans (Pow.×-congˡ (D.m≡m%n+[m/n]*n a p))
    (trans (Pow.×-homo-+ q (D._%_ a p) (D._/_ a p N.* p))
    (trans (*-cong refl (O.period-multiple q p period (D._/_ a p))) (*-identityʳ _))))

  wrap-phase : ∀ a → phase (toℕ (wrap a)) ≈ phase a
  wrap-phase a = trans (Pow.×-congˡ (repr a)) (reduced a)

  K : I → I → Carrier
  K k x = phase (toℕ k N.* toℕ x)

  swap : ∀ k x → K k x ≈ K x k
  swap k x = Pow.×-congˡ (NP.*-comm (toℕ k) (toℕ x))

  row-law : ∀ k x y → K k (x ⊕ y) ≈ K k x * K k y
  row-law k x y = trans (sym (Pow.×-assocˡ q a (toℕ (x ⊕ y))))
    (trans (Pow.×-congʳ a (trans (wrap-phase (b N.+ c)) (Pow.×-homo-+ q b c)))
    (trans (power-product (phase b) (phase c) a)
    (*-cong (Pow.×-assocˡ q a b) (Pow.×-assocˡ q a c))))
    where
    a = toℕ k
    b = toℕ x
    c = toℕ y

  table : Bicharacter cyclic cyclic
  table = record { K = K ; col-e = λ _ → refl ; row-e = λ k → swap k _
    ; row-mul = row-law ; col-mul = λ x k l → trans (swap (k ⊕ l) x)
        (trans (row-law x k l) (*-cong (swap x k) (swap x l))) }

  generator : ∀ x → K x (wrap 1) ≈ phase (toℕ x)
  generator x = trans (sym (Pow.×-assocˡ q a (toℕ (wrap 1))))
    (Pow.×-congʳ a (trans (wrap-phase 1) (Pow.×-homo-1 q)))
    where a = toℕ x

  Exact = ∀ r → 0 N.< r → r N.< p → ¬ O.Period q r

  no-collision : Exact → ∀ i j → toℕ i N.< toℕ j → ¬ (phase (toℕ i) ≈ phase (toℕ j))
  no-collision least i j h eq = least (toℕ j N.∸ toℕ i) (NP.m<n⇒0<n∸m h)
    (NP.≤-<-trans (NP.m∸n≤m (toℕ j) (toℕ i)) (FP.toℕ<n j))
    (O.collision-period q p (toℕ i) (toℕ j) (NP.<⇒≤ (FP.toℕ<n i)) (NP.<⇒≤ h) period eq)

  injective : Exact → ∀ i j → phase (toℕ i) ≈ phase (toℕ j) → i E.≡ j
  injective least i j eq with NP.<-cmp (toℕ i) (toℕ j)
  ... | tri≈ _ h _ = FP.toℕ-injective h
  ... | tri< h _ _ = ⊥-elim (no-collision least i j h eq)
  ... | tri> _ _ h = ⊥-elim (no-collision least j i h (sym eq))

  cyclic-inversion : Exact → NonzeroRegular → (u : Carrier) → u * order p ≈ 1# → LinearEquivalence p
  cyclic-inversion least reg = Dual.equivalence cyclic cyclic table
    (S.columns (λ x y neq → wrap 1 , λ eq → neq (injective least x y
      (trans (sym (generator x)) (trans (swap x (wrap 1))
        (trans eq (trans (swap (wrap 1) y) (generator y))))))))
    (S.rows (λ k l neq → wrap 1 , λ eq → neq (injective least k l
      (trans (sym (generator k)) (trans eq (generator l))))))
    where module S = Domain cyclic cyclic table reg
