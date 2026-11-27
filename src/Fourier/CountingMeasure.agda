{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.CountingMeasure (R : CommutativeRing 0ℓ 0ℓ) where
open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Algebra.WeightedSums R
open import Fourier.Inversion R
open import Algebra.FiniteSums R
open import Fourier.Enumeration
open import Fourier.Pairing R
import Fourier.Characters
import Fourier.Filters R as Old

module Image {n m} (h : Fin m → Fin n) where
  samples : (Fin n → Fin n → Carrier) → Fin n → Carrier
  samples K k = sum m (λ j → K k (h j))

  analysis-count : ∀ K k → transform K (count h) k ≈ samples K k
  analysis-count K k = trans (sum-cong n _ _ (λ x → *-comm _ _)) (integrate-count h (K k))

  invert-count : ∀ K L size → OrthogonalPair n size K L → ∀ x →
    transform L (samples K) x ≈ size * count h x
  invert-count K L size gram x = trans (sum-cong n _ _ λ k → *-cong refl (sym (analysis-count K k)))
    (unnormalized-inversion gram (count h) x)

  module Original (D G : Group n) (B : Bicharacter D G) where
    open Table D G B
    module F = Old.Filter.OnSet D G B h
    weighted-count : Columns → ∀ c w → c * Fourier.Characters.order R n ≈ w → ∀ x →
      c * transform L F.spectrum x ≈ w * F.count x
    weighted-count cols c w factor x = trans (*-cong refl (invert-count K L _ (left-gram cols) x))
      (trans (sym (*-assoc _ _ _)) (*-cong factor (sum-cong m _ _ (λ j → delta-sym (h j) x))))
