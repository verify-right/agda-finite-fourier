{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeMonoid)
module Fourier.Power {a ℓ} (M : CommutativeMonoid a ℓ) where

open CommutativeMonoid M
open import Data.Nat.Base using (zero; suc)
import Algebra.Properties.Monoid.Mult monoid as P
import Algebra.Properties.CommutativeSemigroup commutativeSemigroup as S

power-product : ∀ x y j → j P.× (x ∙ y) ≈ (j P.× x) ∙ (j P.× y)
power-product x y zero = sym (identityˡ ε)
power-product x y (suc j) = trans (∙-cong refl (power-product x y j))
  (S.interchange x y (j P.× x) (j P.× y))
