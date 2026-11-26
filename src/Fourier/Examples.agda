{-# OPTIONS --safe --without-K #-}
module Fourier.Examples where

open import Data.Nat.Base using (ℕ; _*_; _+_)
import Data.Fin.Base as F
import Data.Vec.Base as V
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Modular using (normalize)
import Shared.ModularPower 15 as P
import ModuloRing 15 as M
import Fourier.Inversion M.commutativeRing as FT

-- All numbers are residues modulo 17. The exponentiation is reduced at each
-- step, so these examples evaluate directly with Agda's normalizer.
kernel : ℕ → ∀ {n} → F.Fin n → F.Fin n → ℕ
kernel root i j = P.powMod root (F.toℕ i * F.toℕ j)

example : ∀ n → ℕ → V.Vec ℕ n
example n root = V.tabulate (λ i → normalize 15 (FT.transform (kernel root) F.toℕ i))

four : example 4 4 ≡ 6 V.∷ 7 V.∷ 15 V.∷ 6 V.∷ V.[]
four = refl

eight : example 8 2 ≡ 11 V.∷ 8 V.∷ 14 V.∷ 6 V.∷ 13 V.∷ 3 V.∷ 12 V.∷ 1 V.∷ V.[]
eight = refl

-- In Z/15Z, 4 has exact order two and 2 is invertible, but 1+4 is not 0.
-- Thus exact order plus an inverse for the length does not imply the
-- orthogonality needed for inversion over an arbitrary commutative ring.
order-two : normalize 13 (4 * 4) ≡ 1
order-two = refl
not-order-one : normalize 13 4 ≡ 4
not-order-one = refl
inverse-of-two : normalize 13 (8 * 2) ≡ 1
inverse-of-two = refl
nonorthogonal-sum : normalize 13 (1 + 4) ≡ 5
nonorthogonal-sum = refl
