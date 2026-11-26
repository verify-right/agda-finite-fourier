{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.AdditiveKernel (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Nullary.Negation using (¬_)
import Relation.Binary.PropositionalEquality as E
open import Fourier.Enumeration
open import Fourier.Characters R
open import Fourier.Pairing R
open import Fourier.Separation R
open import Fourier.Inversion R
import Algebra.Bundles as Bundles
import Algebra.Structures as S

-- Ring operations on the finite INDEX type. R above is the coefficient ring.
module IndexRing {n} (add mul : Fin n → Fin n → Fin n) (neg : Fin n → Fin n)
  (z one : Fin n) (laws : S.IsCommutativeRing E._≡_ add mul neg z one) where
  open S.IsCommutativeRing laws using () renaming
    (+-isAbelianGroup to additive-group; distribˡ to dist; *-comm to commute; zeroʳ to times-zero)
  G : Group n
  G = record { _∙_ = add ; neg = neg ; e = z ; laws = additive-group }
  A : Bundles.AbelianGroup 0ℓ 0ℓ
  A = record { isAbelianGroup = additive-group }
  import Algebra.Properties.Group (Bundles.AbelianGroup.group A) as GP

  module Primitive (ψ : Character G) where
    K : Fin n → Fin n → Carrier
    K k x = value ψ (mul k x)
    swap : ∀ k x → K k x ≈ K x k
    swap k x = E.subst (λ a → K k x ≈ value ψ a) (commute k x) refl
    rows-multiply : ∀ k x y → K k (add x y) ≈ K k x * K k y
    rows-multiply k x y = E.subst (λ a → value ψ a ≈ _) (E.sym (dist k x y))
      (mult ψ (mul k x) (mul k y))
    at-zero : ∀ k → K k z ≈ 1#
    at-zero k = E.subst (λ a → value ψ a ≈ 1#) (E.sym (times-zero k)) (trivial-at-e ψ)
    table : Bicharacter G G
    table = record { K = K ; row-e = at-zero ; row-mul = rows-multiply
      ; col-e = λ x → trans (swap z x) (at-zero x)
      ; col-mul = λ x k l → trans (swap (add k l) x)
          (trans (rows-multiply x k l) (*-cong (swap x k) (swap x l))) }

    -- A positive witness form of nontriviality of every nonzero multiplicative shift.
    PrimitiveWitness = ∀ d → d E.≢ z → Σ (Fin n) (λ t → ¬ (K t d ≈ 1#))

    distinguish : PrimitiveWitness → ∀ x y → x E.≢ y →
      Σ (Fin n) (λ t → ¬ (K t x ≈ K t y))
    distinguish prim x y neq with prim (add x (neg y)) (λ h → neq (GP.x∙y⁻¹≈ε⇒x≈y x y h))
    ... | t , nontrivial = t , λ same → nontrivial (trans (rows-multiply t x (neg y))
      (trans (*-cong same refl) (trans (*-comm (K t y) (K t (neg y)))
        (reciprocal (Bicharacter.row table t) y))))

    primitive-inversion : NonzeroRegular → PrimitiveWitness → ∀ f x →
      transform (Bicharacter.L table) (transform K f) x ≈ order n * f x
    primitive-inversion reg prim = unnormalized-inversion (Table.left-gram G G table
      (Domain.columns G G table reg (distinguish prim)))

    open import Fourier.Duality R using (LinearEquivalence; module Dual)

    primitive-duality : NonzeroRegular → PrimitiveWitness →
      (u : Carrier) → u * order n ≈ 1# → LinearEquivalence n
    primitive-duality reg prim = Dual.equivalence G G table
      (Domain.columns G G table reg (distinguish prim))
      (Domain.rows G G table reg row-apart)
      where
      row-apart : ∀ k l → k E.≢ l → Σ (Fin n) (λ t → ¬ (K k t ≈ K l t))
      row-apart k l neq with distinguish prim k l neq
      ... | t , apart = t , λ eq → apart (trans (swap t k) (trans eq (swap l t)))
