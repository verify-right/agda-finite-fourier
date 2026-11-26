{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Two (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base using (Fin)
import Data.Fin.Base as F
import Algebra.Properties.Ring as RingProps
import Fourier.Inversion R as FT
open FT using (OrthogonalPair; transform)
module RP = RingProps ring

-- Character table of the cyclic group of order two.
K : Fin 2 → Fin 2 → Carrier
K F.zero F.zero = 1#
K F.zero (F.suc F.zero) = 1#
K (F.suc F.zero) F.zero = 1#
K (F.suc F.zero) (F.suc F.zero) = - 1#

two : Carrier
two = 1# + 1#

negative-square : (- 1#) * (- 1#) ≈ 1#
negative-square = trans (RP.-1*x≈-x (- 1#)) (RP.-‿involutive 1#)

orth00 : 1# * 1# + (1# * 1# + 0#) ≈ two * 1#
orth00 = trans (+-cong (*-identityˡ 1#)
  (trans (+-cong (*-identityˡ 1#) refl) (+-identityʳ 1#))) (sym (*-identityʳ two))

orth01 : 1# * 1# + (1# * (- 1#) + 0#) ≈ two * 0#
orth01 = trans (+-cong (*-identityˡ 1#)
  (trans (+-cong (*-identityˡ (- 1#)) refl) (+-identityʳ (- 1#))))
  (trans (-‿inverseʳ 1#) (sym (zeroʳ two)))

orth10 : 1# * 1# + ((- 1#) * 1# + 0#) ≈ two * 0#
orth10 = trans (+-cong (*-identityˡ 1#)
  (trans (+-cong (*-identityʳ (- 1#)) refl) (+-identityʳ (- 1#))))
  (trans (-‿inverseʳ 1#) (sym (zeroʳ two)))

orth11 : 1# * 1# + ((- 1#) * (- 1#) + 0#) ≈ two * 1#
orth11 = trans (+-cong (*-identityˡ 1#)
  (trans (+-cong negative-square refl) (+-identityʳ 1#))) (sym (*-identityʳ two))

orthogonality : OrthogonalPair 2 two K K
OrthogonalPair.orthogonal orthogonality F.zero F.zero = orth00
OrthogonalPair.orthogonal orthogonality F.zero (F.suc F.zero) = orth01
OrthogonalPair.orthogonal orthogonality (F.suc F.zero) F.zero = orth10
OrthogonalPair.orthogonal orthogonality (F.suc F.zero) (F.suc F.zero) = orth11

roundtrip : (f : Fin 2 → Carrier) (x : Fin 2) →
  transform K (transform K f) x ≈ two * f x
roundtrip = FT.unnormalized-inversion orthogonality

inversion : (half : Carrier) → half * two ≈ 1# →
  (f : Fin 2 → Carrier) (x : Fin 2) → half * transform K (transform K f) x ≈ f x
inversion half unit = FT.normalized-inversion orthogonality unit

-- Group addition on C₂ (exclusive-or).
_⊕_ : Fin 2 → Fin 2 → Fin 2
F.zero ⊕ y = y
F.suc F.zero ⊕ F.zero = F.suc F.zero
F.suc F.zero ⊕ F.suc F.zero = F.zero

character : ∀ k x y → K k (x ⊕ y) ≈ K k x * K k y
character F.zero F.zero F.zero = sym (*-identityˡ 1#)
character F.zero F.zero (F.suc F.zero) = sym (*-identityˡ 1#)
character F.zero (F.suc F.zero) F.zero = sym (*-identityˡ 1#)
character F.zero (F.suc F.zero) (F.suc F.zero) = sym (*-identityˡ 1#)
character (F.suc F.zero) F.zero F.zero = sym (*-identityˡ 1#)
character (F.suc F.zero) F.zero (F.suc F.zero) = sym (*-identityˡ (- 1#))
character (F.suc F.zero) (F.suc F.zero) F.zero = sym (*-identityʳ (- 1#))
character (F.suc F.zero) (F.suc F.zero) (F.suc F.zero) = sym negative-square

import Fourier.Convolution R as Conv

convolution-theorem : (f g : Fin 2 → Carrier) (k : Fin 2) →
  transform K (Conv.convolution _⊕_ f g) k ≈ transform K f k * transform K g k
convolution-theorem = Conv.convolution-hom _⊕_ K character
