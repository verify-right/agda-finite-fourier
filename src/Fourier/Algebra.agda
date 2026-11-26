{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
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
open import Relation.Binary.Structures using (IsEquivalence)
import Algebra.Structures as S

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

  eqv : IsEquivalence _∼_
  eqv = record { refl = λ i → refl ; sym = λ p i → sym (p i)
    ; trans = λ p q i → trans (p i) (q i) }

  additive : S.IsAbelianGroup _∼_ _⊞_ O neg
  additive = record { comm = λ f g i → +-comm (f i) (g i) ; isGroup = record
    { ⁻¹-cong = λ p i → -‿cong (p i)
    ; inverse = (λ f i → -‿inverseˡ (f i)) , (λ f i → -‿inverseʳ (f i))
    ; isMonoid = record { identity = (λ f i → +-identityˡ (f i)) , (λ f i → +-identityʳ (f i))
      ; isSemigroup = record { assoc = λ f g h i → +-assoc (f i) (g i) (h i)
        ; isMagma = record { isEquivalence = eqv ; ∙-cong = λ p q i → +-cong (p i) (q i) } } } } }

  pointwise : CommutativeRing 0ℓ 0ℓ
  pointwise = record { _≈_ = _∼_ ; _+_ = _⊞_ ; _*_ = _⊙_ ; -_ = neg ; 0# = O ; 1# = I
    ; isCommutativeRing = record { *-comm = λ f g i → *-comm (f i) (g i)
      ; isRing = record { +-isAbelianGroup = additive ; *-cong = λ p q i → *-cong (p i) (q i)
        ; *-assoc = λ f g h i → *-assoc (f i) (g i) (h i)
        ; *-identity = (λ f i → *-identityˡ (f i)) , (λ f i → *-identityʳ (f i))
        ; distrib = (λ f g h i → distribˡ (f i) (g i) (h i)) , (λ f g h i → distribʳ (f i) (g i) (h i)) } } }

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

    -- Interpret expressions in the source and at a single frequency.
    data Expr : Set where
      var : A → Expr
      idₘ : Expr
      plus times : Expr → Expr → Expr
    eval : Expr → A
    eval (var f) = f
    eval idₘ = E
    eval (plus a b) = eval a ⊞ eval b
    eval (times a b) = eval a ⋆ eval b
    at : Expr → Fin n → Carrier
    at (var f) = to f
    at idₘ = I
    at (plus a b) = at a ⊞ at b
    at (times a b) = at a ⊙ at b
    sound : ∀ a → to (eval a) ∼ at a
    sound (var _) i = refl
    sound idₘ = one
    sound (plus a b) i = trans (add _ _ i) (+-cong (sound a i) (sound b i))
    sound (times a b) i = trans (mul _ _ i) (*-cong (sound a i) (sound b i))
    lift-law : ∀ a b → at a ∼ at b → eval a ∼ eval b
    lift-law a b p = reflect _ _ (λ i → trans (sound a i) (trans (p i) (sym (sound b i))))
    convolution-ring : CommutativeRing 0ℓ 0ℓ
    convolution-ring = record { _≈_ = _∼_ ; _+_ = _⊞_ ; _*_ = _⋆_ ; -_ = neg ; 0# = O ; 1# = E
      ; isCommutativeRing = record
        { *-comm = λ f g → lift-law (times (var f) (var g)) (times (var g) (var f)) (λ i → *-comm _ _)
        ; isRing = record { +-isAbelianGroup = additive
          ; *-cong = λ {f} {g} {h} {j} p q → lift-law (times (var f) (var h)) (times (var g) (var j))
              (λ i → *-cong (Linear.respects to-linear f g p i) (Linear.respects to-linear h j q i))
          ; *-assoc = λ f g h → lift-law (times (times (var f) (var g)) (var h))
              (times (var f) (times (var g) (var h))) (λ i → *-assoc _ _ _)
          ; *-identity = (λ f → lift-law (times idₘ (var f)) (var f) (λ i → *-identityˡ _)) ,
                         (λ f → lift-law (times (var f) idₘ) (var f) (λ i → *-identityʳ _))
          ; distrib = (λ f g h → lift-law (times (var f) (plus (var g) (var h)))
              (plus (times (var f) (var g)) (times (var f) (var h))) (λ i → distribˡ _ _ _)) ,
              (λ f g h → lift-law (times (plus (var g) (var h)) (var f))
              (plus (times (var g) (var f)) (times (var h) (var f))) (λ i → distribʳ _ _ _)) } } }

    import Algebra.Properties.Ring ring as RP
    import Algebra.Morphism.Structures as Morph
    module Hom = Morph.RingMorphisms (CommutativeRing.rawRing convolution-ring)
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

    -- Multiplicative inverses can be checked, or constructed, frequency by frequency.
    inverse-coordinates : ∀ f g → (f ⋆ g) ∼ E → (to f ⊙ to g) ∼ I
    inverse-coordinates f g inverse i = trans (sym (mul f g i))
      (trans (Linear.respects to-linear _ _ inverse i) (one i))

    synthesize-inverse : ∀ f v → (to f ⊙ v) ∼ I → (f ⋆ from v) ∼ E
    synthesize-inverse f v reciprocal = reflect _ _ (λ i → trans (mul f (from v) i)
      (trans (*-cong refl (right v i)) (trans (reciprocal i) (sym (one i)))))
