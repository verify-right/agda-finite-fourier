{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Orthogonality (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Algebra.FiniteSums R
import Algebra.Properties.Ring as RingProps
module RP = RingProps ring

-- The ordinary character-translation proof, stated so its requirements are
-- constructive over rings with zero divisors: q - 1 must have an inverse.
fixed-by-unit-implies-zero : ∀ q inv s → inv * (q + (- 1#)) ≈ 1# → q * s ≈ s → s ≈ 0#
fixed-by-unit-implies-zero q inv s unit fixed =
  trans (sym (*-identityˡ s))
  (trans (*-cong (sym unit) refl)
  (trans (*-assoc inv (q + (- 1#)) s)
  (trans (*-cong refl (trans (distribʳ s q (- 1#))
    (trans (+-cong fixed (RP.-1*x≈-x s)) (-‿inverseʳ s))))
    (zeroʳ inv))))

-- shift-preserves-sum is a finite reindexing certificate, normally proved
-- from bijectivity of translation in the finite group. Eigenvalue records
-- the character multiplication law. No classical excluded middle is used.
character-sum-zero : ∀ n (χ : Fin n → Carrier) (shift : Fin n → Fin n) q inv →
  (∀ i → χ (shift i) ≈ q * χ i) →
  sum n (λ i → χ (shift i)) ≈ sum n χ →
  inv * (q + (- 1#)) ≈ 1# → sum n χ ≈ 0#
character-sum-zero n χ shift q inv eigen reindex unit =
  fixed-by-unit-implies-zero q inv (sum n χ) unit
    (trans (sym (sum-mulˡ n q χ))
      (trans (sum-cong n _ _ (λ i → sym (eigen i))) reindex))
