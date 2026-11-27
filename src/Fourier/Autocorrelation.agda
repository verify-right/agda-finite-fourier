{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (AbelianGroup; CommutativeRing)
open import Level using (0ℓ)
module Fourier.Autocorrelation (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base using (Fin)
import Data.Fin.Permutation as P
import Algebra.Properties.AbelianGroup
import Relation.Binary.PropositionalEquality as E
open import Fourier.Enumeration using (Group)
open import Fourier.Inversion R using (transform)
open import Algebra.FiniteSums R using (sum-cong)
open import Fourier.Reindex R using (reindex)
import Fourier.GroupConvolution R as C

module On {n} (G : Group n) (K : Fin n → Fin n → Carrier)
  (mult : ∀ k x y → K k (Group._∙_ G x y) ≈ K k x * K k y) where

  open Group G using (neg)
  private
    group : AbelianGroup 0ℓ 0ℓ
    group = record { isAbelianGroup = Group.laws G }
    module A = Algebra.Properties.AbelianGroup group
    reversal = P.permutation neg neg A.⁻¹-involutive A.⁻¹-involutive

  reversed-transform : ∀ f k → transform K (λ x → f (neg x)) k ≈ transform (λ j x → K j (neg x)) f k
  reversed-transform f k = trans (sum-cong n _ _ λ x → *-cong
    (reflexive (E.cong (K k) (E.sym (A.⁻¹-involutive x)))) refl)
    (reindex reversal (λ x → K k (neg x) * f x))

  autocorrelation : ∀ f k → transform K (C.On.difference G f (λ x → f (neg x))) k
    ≈ transform K f k * transform (λ j x → K j (neg x)) f k
  autocorrelation f k = trans (C.On.convolution-transform G K mult f (λ x → f (neg x)) k)
    (*-cong refl (reversed-transform f k))
