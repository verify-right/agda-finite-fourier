{-# OPTIONS --safe --without-K #-}
module Fourier.WeightedExamples where
open import Data.Nat.Base using (ℕ; _*_)
open import Data.Fin.Base as F using (Fin; zero; suc)
import Data.Fin.Properties as FP
import Data.Nat.Properties as NP
open import Relation.Nullary.Decidable using (from-yes)
open import Data.Vec.Base as V using (tabulate; []; _∷_)
import Relation.Binary.PropositionalEquality as E
import Algebra.ModuloRing 15 as R
import Fourier.CyclicGroup 3 as G
import Fourier.CyclicGroup 1 as H
import Fourier.Cyclic R.commutativeRing 3 as Cy
module K = Cy.Root 4 E.refl
open import Fourier.Pairing R.commutativeRing
open import Fourier.Characters R.commutativeRing
open import Fourier.Inversion R.commutativeRing
open import Algebra.FiniteSums R.commutativeRing
open import Fourier.NormalizedSelector R.commutativeRing
open import Fourier.WeightedSelector R.commutativeRing
open import Algebra.WeightedSums R.commutativeRing
import Fourier.FlatSpectrum R.commutativeRing as Flat

h : Fin 2 → Fin 4
h zero = zero
h (suc zero) = suc (suc zero)
cs = Bicharacter.row K.table
module S = On G.cyclic H.cyclic h E.refl
  (from-yes (FP.all? (λ i → FP.all? (λ j → h (i H.⊕ j) FP.≟ (h i G.⊕ h j)))))
  3 1 11 E.refl
one = G.wrap 1
sep : ∀ j inv → R._≈_ (inv * (K.K j one Data.Nat.Base.+ R.negative 1)) 1 → Separates (K.K j)
sep j inv eq = witness (K.K j) one (unit-regular _ inv eq)
restricted : ∀ j → R._≈_ (8 * (K.K j (h (suc zero)) Data.Nat.Base.+ R.negative 1)) 1 →
  Separates (λ x → K.K j (h x))
restricted j eq = witness (λ x → K.K j (h x)) (suc zero) (unit-regular (K.K j (h (suc zero)) Data.Nat.Base.+ R.negative 1) 8 eq)
modes : ∀ j → S.Mode (cs j)
modes zero = S.principal (λ _ → E.refl)
modes j@(suc zero) = S.discarded (sep j 6 E.refl) (restricted j E.refl)
modes j@(suc (suc zero)) = S.retained (sep j 8 E.refl) (λ { zero → E.refl ; (suc zero) → E.refl })
modes j@(suc (suc (suc zero))) = S.discarded (sep j 10 E.refl) (restricted j E.refl)

analysis = λ j x → K.K (G.neg j) x
gram4 : OrthogonalPair 4 (order 4) analysis (λ x j → K.K j x)
OrthogonalPair.orthogonal gram4 = from-yes (FP.all? (λ x → FP.all? (λ y →
  R.normalize (sum 4 (λ j → K.K j x * analysis j y)) NP.≟ R.normalize (order 4 * delta x y))))
module Exact = S.Table cs analysis gram4 13 E.refl modes
all-signals = Exact.lemma6-1

multipliers : tabulate (λ j → R.normalize (11 * S.B.coeff (cs j))) E.≡ 1 ∷ 0 ∷ 5 ∷ 0 ∷ []
multipliers = E.refl

row : Fin 4 → ℕ
row = V.lookup (1 ∷ 1 ∷ 1 ∷ 16 ∷ [])
module Row = Flat.On G.cyclic row
impulse : ∀ x → R._≈_ (Row.corr x) (4 * delta zero x)
impulse = from-yes (FP.all? (λ x → R.normalize (Row.corr x) NP.≟ R.normalize (4 * delta zero x)))
flat-row = Row.flat 4 impulse
