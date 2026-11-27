{-# OPTIONS --safe --without-K #-}
module Fourier.IntegerCorrelationExamples where
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_])
open import Data.Integer.Properties using (+-*-commutativeRing)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Vec.Base using (lookup; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Fourier.CyclicGroup
import Fourier.FlatSpectrum +-*-commutativeRing as Flat
open import Algebra.WeightedSums +-*-commutativeRing
open import Algebra.FiniteSums +-*-commutativeRing
-- All cyclic orders m+1, arbitrary integer coefficients.
module Cyclic (m : ℕ) where
  module G = Fourier.CyclicGroup m
  module For (f : G.I → ℤ) where
    open Flat.On G.cyclic f
    augmentation-square : (∀ x → corr x ≡ (+ G.p) Z.* delta zero x) →
      sum G.p f Z.* sum G.p f ≡ + G.p
    augmentation-square = row-sum-square (+ G.p)

signs : Fin 4 → ℤ
signs = lookup ((+ 1) ∷ (+ 1) ∷ (+ 1) ∷ -[1+ 0 ] ∷ [])
module G4 = Fourier.CyclicGroup 3
module Row = Flat.On G4.cyclic signs
impulse : ∀ x → Row.corr x ≡ (+ 4) Z.* delta zero x
impulse zero = refl
impulse (suc zero) = refl
impulse (suc (suc zero)) = refl
impulse (suc (suc (suc zero))) = refl
square = Cyclic.For.augmentation-square 3 signs impulse

-- Positive weights on C2 can have a negative signed-character coefficient.
negative-mode : moment (lookup ((+ 1) ∷ (+ 2) ∷ []))
  (lookup ((+ 1) ∷ -[1+ 0 ] ∷ [])) ≡ -[1+ 0 ]
negative-mode = refl
