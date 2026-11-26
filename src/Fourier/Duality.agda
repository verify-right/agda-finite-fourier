{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Duality (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Function.Bundles using (Inverse)
open import Data.Product.Base using (_,_)
import Data.Vec.Functional.Relation.Binary.Equality.Setoid setoid as V
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Fourier.Enumeration
open import Fourier.Characters R
open import Algebra.FiniteSums R
open import Fourier.Inversion R
open import Fourier.Pairing R
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as M

Signal : ℕ → Set
Signal n = Fin n → Carrier

record Linear {n} (T : Signal n → Signal n) : Set where
  field
    respects : ∀ f g → (∀ i → f i ≈ g i) → ∀ i → T f i ≈ T g i
    adds : ∀ f g i → T (λ j → f j + g j) i ≈ T f i + T g i
    scales : ∀ c f i → T (λ j → c * f j) i ≈ c * T f i
open Linear

matrix-linear : ∀ {n} (K : Fin n → Fin n → Carrier) → Linear (transform K)
respects (matrix-linear {n} K) f g eq i = sum-cong n _ _ (λ j → *-cong refl (eq j))
adds (matrix-linear {n} K) f g i = trans (sum-cong n _ _ (λ j → distribˡ (K i j) (f j) (g j)))
  (sum-add n _ _)
scales (matrix-linear {n} K) c f i = trans (sum-cong n _ _ (λ j → M.x∙yz≈y∙xz (K i j) c (f j)))
  (sum-mulˡ n c _)

record LinearEquivalence (n : ℕ) : Set where
  field
    to from : Signal n → Signal n
    to-linear : Linear to
    from-linear : Linear from
    left : ∀ f i → from (to f) i ≈ f i
    right : ∀ g k → to (from g) k ≈ g k

asInverse : ∀ {n} → LinearEquivalence n →
  Inverse (V.≋-setoid n) (V.≋-setoid n)
asInverse E = record
  { to = to
  ; from = from
  ; to-cong = λ p → respects to-linear _ _ p
  ; from-cong = λ p → respects from-linear _ _ p
  ; inverse =
      (λ p i → trans (respects to-linear _ _ p i) (right _ i)) ,
      (λ p i → trans (respects from-linear _ _ p i) (left _ i))
  }
  where
  open LinearEquivalence E

module Dual {n} (H G : Group n) (B : Bicharacter H G) where
  open Table H G B
  unscaled-left = λ cols → unnormalized-inversion (left-gram cols)
  unscaled-right = λ rows → unnormalized-inversion (right-gram rows)

  equivalence : Columns → Rows → (u : Carrier) → u * order n ≈ 1# → LinearEquivalence n
  equivalence cols rows u unit = record
    { to = transform K ; from = λ g x → u * transform L g x
    ; to-linear = matrix-linear K ; from-linear = inv-linear
    ; left = normalized-inversion (left-gram cols) unit
    ; right = λ g k → trans (scales (matrix-linear K) u (transform L g) k)
        (normalized-inversion (right-gram rows) unit g k) }
    where
    inv-linear : Linear (λ g x → u * transform L g x)
    respects inv-linear f g eq i = *-cong refl (respects (matrix-linear L) f g eq i)
    adds inv-linear f g i = trans (*-cong refl (adds (matrix-linear L) f g i))
      (distribˡ u _ _)
    scales inv-linear c f i = trans (*-cong refl (scales (matrix-linear L) c f i))
      (M.x∙yz≈y∙xz u c _)
