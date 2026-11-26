{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Separation (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (¬_)
open import Data.Product.Base using (Σ; _,_)
open import Fourier.Enumeration
open import Fourier.Characters R
open import Fourier.Pairing R
import Algebra.Properties.AbelianGroup +-abelianGroup as A
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as M

NonzeroRegular = ∀ d → ¬ (d ≈ 0#) → Regular d

-- If ia is inverse to a, and ia b = 1, then a = b.
recover : ∀ a ia b → ia * a ≈ 1# → ia * b ≈ 1# → a ≈ b
recover a ia b ua ub = trans (sym (*-identityʳ a)) (trans (*-cong refl (sym ub))
  (trans (sym (*-assoc a ia b)) (trans (*-cong (trans (*-comm a ia) ua) refl) (*-identityˡ b))))

module Domain {n} (H G : Group n) (B : Bicharacter H G) (reg : NonzeroRegular) where
  open Table H G B

  columns : (∀ x y → x Relation.Binary.PropositionalEquality.≢ y →
    Σ _ (λ t → ¬ (K t x ≈ K t y))) → Columns
  columns distinguish x y neq with distinguish x y neq
  ... | t , apart = witness _ t (reg _ (λ zero →
    apart (recover _ _ _ (reciprocal (col x) t)
      (A.x∙y⁻¹≈ε⇒x≈y _ 1# zero))))

  rows : (∀ k l → k Relation.Binary.PropositionalEquality.≢ l →
    Σ _ (λ t → ¬ (K k t ≈ K l t))) → Rows
  rows distinguish k l neq with distinguish k l neq
  ... | t , apart = witness _ t (reg _ (λ zero →
    apart (sym (recover _ _ _ (reciprocal (col t) l)
      (trans (*-comm (L t l) (K k t)) (A.x∙y⁻¹≈ε⇒x≈y _ 1# zero))))))
