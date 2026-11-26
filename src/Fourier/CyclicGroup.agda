{-# OPTIONS --safe --without-K #-}
open import Data.Nat.Base as N using (ℕ; suc; _+_; _∸_)
module Fourier.CyclicGroup (m : ℕ) where

import Data.Nat.Properties as NP
open import Data.Nat.DivMod as D using (_%_; _mod_)
open import Data.Fin.Base as F using (Fin; toℕ)
import Data.Fin.Properties as FP
open import Relation.Binary.PropositionalEquality as E
open import Data.Product.Base using (_,_)
open import Fourier.Enumeration
p = suc m
I = Fin p
wrap : ℕ → I
wrap a = a mod p
repr : ∀ a → toℕ (wrap a) ≡ a % p
repr a = FP.toℕ-fromℕ< (D.m%n<n a p)
small : ∀ i → toℕ i % p ≡ toℕ i
small i = D.m<n⇒m%n≡m (FP.toℕ<n i)
eta : ∀ i → wrap (toℕ i) ≡ i
eta i = FP.toℕ-injective (trans (repr (toℕ i)) (small i))
_⊕_ : I → I → I
i ⊕ j = wrap (toℕ i + toℕ j)
neg : I → I
neg i = wrap (p ∸ toℕ i)

wrap-add : ∀ a b → wrap a ⊕ wrap b ≡ wrap (a + b)
wrap-add a b = FP.toℕ-injective (trans (repr (toℕ (wrap a) + toℕ (wrap b)))
  (trans (cong (λ z → z % p) (cong₂ _+_ (repr a) (repr b)))
  (trans (sym (D.%-distribˡ-+ a b p)) (sym (repr (a + b))))))

left-wrap : ∀ a j → wrap a ⊕ j ≡ wrap (a + toℕ j)
left-wrap a j = trans (cong (wrap a ⊕_) (sym (eta j))) (wrap-add a (toℕ j))

comm : ∀ i j → i ⊕ j ≡ j ⊕ i
comm i j = cong wrap (NP.+-comm (toℕ i) (toℕ j))

assoc : ∀ i j k → (i ⊕ j) ⊕ k ≡ i ⊕ (j ⊕ k)
assoc i j k = trans (left-wrap (toℕ i + toℕ j) k)
  (trans (cong wrap (NP.+-assoc (toℕ i) (toℕ j) (toℕ k)))
  (trans (cong wrap (NP.+-comm (toℕ i) _))
  (trans (sym (left-wrap (toℕ j + toℕ k) i)) (comm (j ⊕ k) i))))

inv : ∀ i → neg i ⊕ i ≡ F.zero
inv i = trans (left-wrap (p ∸ toℕ i) i) (FP.toℕ-injective
  (trans (repr ((p ∸ toℕ i) + toℕ i)) (trans (cong (_% p) (trans (NP.+-comm (p ∸ toℕ i) (toℕ i))
    (NP.m+[n∸m]≡n (NP.<⇒≤ (FP.toℕ<n i))))) (D.n%n≡0 p))))

cyclic : Group p
cyclic = record { _∙_ = _⊕_ ; e = F.zero ; neg = neg ; laws = record
  { comm = comm ; isGroup = record { ⁻¹-cong = cong neg
    ; inverse = inv , (λ i → trans (comm i (neg i)) (inv i))
    ; isMonoid = record { identity = eta , (λ i → trans (comm i F.zero) (eta i))
      ; isSemigroup = record { assoc = assoc ; isMagma = record
        { isEquivalence = isEquivalence ; ∙-cong = cong₂ _⊕_ } } } } } }
