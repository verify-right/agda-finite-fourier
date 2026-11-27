{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.InvariantWeight (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Algebra.FiniteSums R
open import Fourier.Characters R
open import Fourier.Enumeration
open import Fourier.Reindex R
open import Algebra.WeightedSums R
import Algebra.Properties.Ring ring as RP
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as M

module Shift {n} (G : Group n) (c : Character G) (w : Fin n → Carrier) where
  q = value c
  total = moment w q
  annihilates : ∀ t → (∀ x → w (Group._∙_ G t x) ≈ w x) → (q t + (- 1#)) * total ≈ 0#
  annihilates t invariant = trans (distribʳ total (q t) (- 1#))
    (trans (+-cong fixed (RP.-1*x≈-x total)) (-‿inverseʳ total))
    where
    fixed : q t * total ≈ total
    fixed = trans (sym (sum-mulˡ n (q t) _)) (trans (sum-cong n _ _ λ x →
      trans (M.x∙yz≈y∙xz (q t) (w x) (q x)) (*-cong (sym (invariant x)) (sym (mult c t x))))
      (translate-sum G t (λ x → w x * q x)))

  coset-cancel : ∀ {m} (h : Fin m → Fin n) → (∀ j x → w (Group._∙_ G (h j) x) ≈ w x) →
    Separates (λ j → q (h j)) → total ≈ 0#
  coset-cancel h inv sep = sep total (λ j → annihilates (h j) (inv j))

-- Same type as Fourier.Characters.character-zero, with the constant unit weight.
ordinary : ∀ {n} (G : Group n) (c : Character G) → Separates (value c) → sum n (value c) ≈ 0#
ordinary {n} G c sep = trans (sym (sum-cong n _ _ (λ i → *-identityˡ (value c i))))
  (Shift.coset-cancel G c (λ _ → 1#) (λ i → i) (λ _ _ → refl) sep)
