{-# OPTIONS --safe --without-K #-}
module Fourier.Enumeration where

open import Algebra.Structures using (IsAbelianGroup)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
import Data.Fin.Permutation as P
open import Relation.Binary.PropositionalEquality as E using (_≡_; cong; trans; sym)

-- The carrier IS its enumeration. A different ordering is a Fin permutation.
record Group (n : ℕ) : Set where
  field
    _∙_ : Fin n → Fin n → Fin n
    e : Fin n
    neg : Fin n → Fin n
    laws : IsAbelianGroup _≡_ _∙_ e neg
  open IsAbelianGroup laws public using (assoc; inverseʳ; inverseˡ; identityʳ; identityˡ; comm)

  translate : Fin n → P.Permutation n n
  translate t = P.permutation (t ∙_) (neg t ∙_)
    (λ x → trans (sym (assoc t (neg t) x))
      (trans (cong (_∙ x) (inverseʳ t)) (identityˡ x)))
    (λ x → trans (sym (assoc (neg t) t x))
      (trans (cong (_∙ x) (inverseˡ t)) (identityˡ x)))
