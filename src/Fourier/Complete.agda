{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Complete (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (any?; all?; ¬∀⇒∃¬)
open import Data.Product.Base using (Σ; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Fourier.Characters R
open import Fourier.Duality R
open import Fourier.Pairing R
open import Fourier.Enumeration
open import Fourier.Inversion R
open import Algebra.FiniteSums R
open import Fourier.Separation R
import Algebra.Properties.AbelianGroup +-abelianGroup as A

-- Completeness follows from injectivity of the Fourier map, with no
-- classification theorem or prior enumeration of all homomorphisms.
module Basis {n} (H G : Group n) (B : Bicharacter H G)
  (reg : NonzeroRegular) (dec : ∀ a b → Dec (a ≈ b)) (nontrivial : ¬ (1# ≈ 0#))
  (inject : ∀ f g → (∀ k → transform (Bicharacter.K B) f k ≈ transform (Bicharacter.K B) g k)
                   → ∀ x → f x ≈ g x) where
  open Bicharacter B

  complete : (c : Character G) → Σ (Fin n) (λ k → ∀ x → value c x ≈ K k x)
  complete c with any? (λ k → all? (λ x → dec (value c x) (K k x)))
  ... | yes hit = hit
  ... | no miss = ⊥-elim (nontrivial (trans (sym (trivial-at-e (opposite c)))
      (inject f (λ _ → 0#) vanished (Group.e G))))
    where
    f = value (opposite c)
    van : ∀ k → transform K f k ≈ 0#
    van k with ¬∀⇒∃¬ n (λ x → value c x ≈ K k x) (λ x → dec _ _) (λ h → miss (k , h))
    ... | t , apart = character-zero G (product (row k) (opposite c))
      (witness _ t (reg _ (λ zero → apart (recover _ _ _ (reciprocal c t)
        (trans (*-comm (f t) (K k t)) (A.x∙y⁻¹≈ε⇒x≈y _ 1# zero))))))
    vanished : ∀ k → transform K f k ≈ transform K (λ _ → 0#) k
    vanished k = trans (van k) (sym (trans (sum-cong n _ _ (λ x → zeroʳ (K k x))) (sum-zero n)))
