{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Reindex (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base as F using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Permutation as P using (Permutation; _⟨$⟩ʳ_; _⟨$⟩ˡ_)
open import Relation.Binary.PropositionalEquality as E using (_≢_)
open import Relation.Nullary.Decidable using (yes; no)
open import Fourier.Sums R
open import Fourier.Enumeration using (Group)

diagonal : ∀ {n} (i : Fin n) → delta i i ≈ 1#
diagonal F.zero = refl
diagonal (F.suc i) = diagonal i

off : ∀ {n} (i j : Fin n) → i ≢ j → delta i j ≈ 0#
off F.zero F.zero p = Data.Empty.⊥-elim (p E.refl) where import Data.Empty
off F.zero (F.suc j) p = refl
off (F.suc i) F.zero p = refl
off (F.suc i) (F.suc j) p = off i j (λ eq → p (E.cong F.suc eq))

transport-delta : ∀ {m n} (π : Permutation m n) i j →
  delta (π ⟨$⟩ʳ i) j ≈ delta (π ⟨$⟩ˡ j) i
transport-delta π i j with (π ⟨$⟩ʳ i) ≟ j
... | yes E.refl rewrite P.inverseˡ π {i} = trans (diagonal (π ⟨$⟩ʳ i)) (sym (diagonal i))
... | no p = trans (off _ _ p) (sym (off _ _ (λ eq →
  p (E.trans (E.cong (π ⟨$⟩ʳ_) (E.sym eq)) (P.inverseʳ π)))))

reindex : ∀ {m n} (π : Permutation m n) (f : Fin n → Carrier) →
  sum m (λ i → f (π ⟨$⟩ʳ i)) ≈ sum n f
reindex {m} {n} π f =
  trans (sum-cong m _ _ (λ i → sym (select n (π ⟨$⟩ʳ i) f)))
  (trans (sum-swap m n (λ i j → delta (π ⟨$⟩ʳ i) j * f j))
  (sum-cong n _ _ (λ j → trans
    (sum-cong m _ _ (λ i → *-cong (transport-delta π i j) refl))
    (select m (π ⟨$⟩ˡ j) (λ _ → f j)))))

translate-sum : ∀ {n} (G : Group n) t (f : Fin n → Carrier) →
  sum n (λ i → f (Group._∙_ G t i)) ≈ sum n f
translate-sum G t = reindex (Group.translate G t)
