{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.FlatSpectrum (R : CommutativeRing 0ℓ 0ℓ) where
open CommutativeRing R
open import Fourier.Enumeration
open import Fourier.Characters R
open import Algebra.FiniteSums R
open import Algebra.WeightedSums R
import Fourier.Autocorrelation R as A
import Fourier.GroupConvolution R as C
open import Data.Fin.Base using (Fin)

module On {n} (G : Group n) (f : Fin n → Carrier) where
  open Group G using (neg; e)
  corr = C.On.difference G f (λ x → f (neg x))

  -- Covers both a difference set's two-level correlation and a Hadamard impulse.
  spectrum : ∀ b s → (∀ x → corr x ≈ b + s * delta e x) → (c : Character G) →
    moment (value c) f * moment (λ x → value c (neg x)) f ≈ b * sum n (value c) + s
  spectrum b s law c = trans (sym (F.autocorrelation f e))
    (trans (sum-cong n _ _ λ x → trans (*-cong refl (law x)) (*-comm _ _))
    (trans (two-level b s (delta e) (value c)) (+-cong refl
      (trans (*-cong refl (trans (select n e (value c)) (trivial-at-e c))) (*-identityʳ s)))))
    where module F = A.On G (λ _ → value c) (λ _ → mult c)

  flat : ∀ t → (∀ x → corr x ≈ t * delta e x) → (c : Character G) →
    moment (value c) f * moment (λ x → value c (neg x)) f ≈ t
  flat t law c = trans (spectrum 0# t (λ x → trans (law x) (sym (+-identityˡ _))) c)
    (trans (+-cong (zeroˡ _) refl) (+-identityˡ t))

  row-sum-square : ∀ t → (∀ x → corr x ≈ t * delta e x) → sum n f * sum n f ≈ t
  row-sum-square t law = trans (*-cong (sym ones) (sym ones)) (flat t law trivial)
    where
    trivial : Character G
    trivial = record { value = λ _ → 1# ; trivial-at-e = refl ; mult = λ _ _ → sym (*-identityˡ _) }
    ones : moment (λ _ → 1#) f ≈ sum n f
    ones = sum-cong n _ _ (λ x → *-identityˡ (f x))
