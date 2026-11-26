{-# OPTIONS --safe --without-K #-}

open import Algebra.Bundles using (CommutativeMonoid)

module Fourier.Power {a ℓ} (M : CommutativeMonoid a ℓ) where

open import Algebra.Properties.CommutativeMonoid.Mult M
  public renaming (×-distrib-+ to power-product)
