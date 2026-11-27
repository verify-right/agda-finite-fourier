{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.NormalizedSelector (R : CommutativeRing 0ℓ 0ℓ) where
open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Fourier.Enumeration
open import Algebra.FiniteSums R
open import Fourier.Characters R
open import Fourier.Inversion R
open import Fourier.WeightedSelector R
open import Algebra.WeightedSums R
import Relation.Binary.PropositionalEquality as E
import Fourier.Filters R as Filters

module On {n m} (G : Group n) (H : Group m) (h : Fin m → Fin n)
  (he : h (Group.e H) E.≡ Group.e G)
  (hm : ∀ x y → h (Group._∙_ H x y) E.≡ Group._∙_ G (h x) (h y))
  (b s mu : Carrier) (unit : mu * (b * order n + s * order m) ≈ 1#) where
  module B = Bias G h b s
  module C (c : Character G) = Filters.Coset G H h he hm c (Group.e G)
  data Mode (c : Character G) : Set where
    principal : (∀ x → value c x ≈ 1#) → Mode c
    retained : Separates (value c) → (∀ j → value c (h j) ≈ 1#) → Mode c
    discarded : Separates (value c) → Separates (value (C.restrict c)) → Mode c

  multiplier : ∀ {c} → Mode c → Carrier
  multiplier (principal _) = 1#
  multiplier (retained _ _) = mu * (s * order m)
  multiplier (discarded _ _) = 0#

  coefficient : ∀ c (t : Mode c) → mu * B.coeff c ≈ multiplier t
  coefficient c (principal one) = trans (*-cong refl (B.principal c one)) unit
  coefficient c (retained sep one) = *-cong refl (B.Sub.retained H he hm c sep one)
  coefficient c (discarded sep z) = trans (*-cong refl (B.Sub.discarded H he hm c sep z)) (zeroʳ mu)

  module Table (cs : Fin n → Character G) (a : Fin n → Fin n → Carrier)
    (gram-law : OrthogonalPair n (order n) a (λ x j → value (cs j) x))
    (v : Carrier) (vu : v * order n ≈ 1#) (modes : ∀ j → Mode (cs j)) where
    module A = B.Analysis cs a gram-law v vu
    lemma6-1 : ∀ f u → mu * moment B.weight (λ x → f (Group._∙_ G u x)) ≈
      sum n (λ j → (A.fourier f j * value (cs j) u) * multiplier (modes j))
    lemma6-1 f u = trans (A.weighted-selector mu f u)
      (sum-cong n _ _ λ j → *-cong refl (coefficient (cs j) (modes j)))
