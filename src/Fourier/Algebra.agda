{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing; RawRing)
open import Level using (0ℓ)
module Fourier.Algebra (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_)
open import Fourier.Enumeration
open import Algebra.FiniteSums R
open import Fourier.Convolution R
open import Fourier.Characters R using (order)
open import Fourier.Pairing R
open import Fourier.Duality R

module Split {n} (H G : Group n) (B : Bicharacter H G) where
  open Table H G B
  A = Signal n
  _∼_ : A → A → Set
  f ∼ g = ∀ i → f i ≈ g i
  _⊞_ _⊙_ _⋆_ : A → A → A
  (f ⊞ g) i = f i + g i
  (f ⊙ g) i = f i * g i
  _⋆_ = convolution (Group._∙_ G)
  neg : A → A
  neg f i = - f i
  O I E : A
  O _ = 0#
  I _ = 1#
  E i = delta i (Group.e G)

  import Algebra.Construct.Pointwise (Fin n) as PW

  pointwise : CommutativeRing 0ℓ 0ℓ
  pointwise = PW.commutativeRing R

  module Iso (cols : Columns) (rows : Rows) (u : Carrier) (unit : u * order n ≈ 1#) where
    linear = Dual.equivalence H G B cols rows u unit
    open LinearEquivalence linear public
    add = Linear.adds to-linear
    mul = diagonalizes
    one : to E ∼ I
    one k = trans (sum-cong n _ _ (λ j → trans (*-comm _ _) (*-cong (delta-sym j (Group.e G)) refl)))
      (trans (select n (Group.e G) (K k)) (row-e k))
    reflect : ∀ f g → to f ∼ to g → f ∼ g
    reflect f g p i = trans (sym (left f i))
      (trans (Linear.respects from-linear _ _ p i) (left g i))
    inverse-mul : ∀ f g → from (f ⊙ g) ∼ (from f ⋆ from g)
    inverse-mul f g = reflect _ _ (λ i → trans (right _ i)
      (sym (trans (mul (from f) (from g) i) (*-cong (right f i) (right g i)))))
    inverse-one : from I ∼ E
    inverse-one = reflect _ _ (λ i → trans (right I i) (sym (one i)))

    convolution-raw : RawRing 0ℓ 0ℓ
    convolution-raw = record
      { Carrier = A
      ; _≈_ = _∼_
      ; _+_ = _⊞_
      ; _*_ = _⋆_
      ; -_ = neg
      ; 0# = O
      ; 1# = E
      }

    import Algebra.Properties.Ring ring as RP
    import Algebra.Morphism.Structures as Morph
    module Hom = Morph.RingMorphisms convolution-raw
      (CommutativeRing.rawRing pointwise)

    forward-zero : to O ∼ O
    forward-zero k = trans (sum-cong n _ _ (λ j → zeroʳ (K k j))) (sum-zero n)
    forward-neg : ∀ f → to (neg f) ∼ neg (to f)
    forward-neg f k = trans (Linear.respects to-linear _ _
      (λ j → sym (RP.-1*x≈-x (f j))) k)
      (trans (Linear.scales to-linear (- 1#) f k) (RP.-1*x≈-x (to f k)))

    fourier-isomorphism : Hom.IsRingIsomorphism to
    fourier-isomorphism = record
      { surjective = λ g → from g , λ {z} eq i →
          trans (Linear.respects to-linear z (from g) eq i) (right g i)
      ; isRingMonomorphism = record { injective = λ {f} {g} → reflect f g
        ; isRingHomomorphism = record { -‿homo = forward-neg ; isSemiringHomomorphism = record
          { 1#-homo = one ; isNearSemiringHomomorphism = record { *-homo = mul
            ; +-isMonoidHomomorphism = record { ε-homo = forward-zero ; isMagmaHomomorphism = record
              { homo = add ; isRelHomomorphism = record { cong = λ {f} {g} → Linear.respects to-linear f g } } } } } } } }

    import Algebra.Morphism.RingMonomorphism
      (Hom.IsRingIsomorphism.isRingMonomorphism fourier-isomorphism)
      as Mono

    convolution-ring : CommutativeRing 0ℓ 0ℓ
    convolution-ring = record
      { RawRing convolution-raw
      ; isCommutativeRing = Mono.isCommutativeRing
          (CommutativeRing.isCommutativeRing pointwise)
      }

    -- Multiplicative inverses can be checked, or constructed, frequency by frequency.
    inverse-coordinates : ∀ f g → (f ⋆ g) ∼ E → (to f ⊙ to g) ∼ I
    inverse-coordinates f g inverse i = trans (sym (mul f g i))
      (trans (Linear.respects to-linear _ _ inverse i) (one i))

    synthesize-inverse : ∀ f v → (to f ⊙ v) ∼ I → (f ⋆ from v) ∼ E
    synthesize-inverse f v reciprocal = reflect _ _ (λ i → trans (mul f (from v) i)
      (trans (*-cong refl (right v i)) (trans (reciprocal i) (sym (one i)))))
