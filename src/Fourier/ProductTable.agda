{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.ProductTable (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (Σ; _,_)
import Relation.Binary.PropositionalEquality as E
open import Fourier.Enumeration
open import Fourier.Characters R
open import Algebra.FiniteSums R
open import Fourier.Inversion R

module Axes {m n} (G : Group m) (H : Group n) where
  module G = Group G
  module H = Group H
  -- Characters on pairs, written in curried coordinates.
  record PairCharacter : Set where
    field
      v : Fin m → Fin n → Carrier
      neutral : v G.e H.e ≈ 1#
      splits : ∀ x a y b → v (x G.∙ y) (a H.∙ b) ≈ v x a * v y b
  module Restrict (p : PairCharacter) where
    open PairCharacter p
    fst : Character G
    Character.value fst x = v x H.e
    Character.trivial-at-e fst = neutral
    Character.mult fst x y = E.subst (λ t → v (x G.∙ y) t ≈ _) (H.identityˡ H.e) (splits x H.e y H.e)
    snd : Character H
    Character.value snd y = v G.e y
    Character.trivial-at-e snd = neutral
    Character.mult snd a b = E.subst (λ t → v t (a H.∙ b) ≈ _) (G.identityˡ G.e) (splits G.e a G.e b)
    factors : ∀ x y → v x y ≈ value fst x * value snd y
    factors x y = E.subst₂ (λ a b → v a b ≈ _) (G.identityʳ x) (H.identityˡ y) (splits x H.e G.e y)

  module Tables (U : Fin m → Character G) (V : Fin n → Character H) where
    K = λ i x → value (U i) x
    L = λ j y → value (V j) y
    entry = λ i j x y → K i x * L j y

    row : Fin m → Fin n → PairCharacter
    PairCharacter.v (row i j) = entry i j
    PairCharacter.neutral (row i j) = trans (*-cong (trivial-at-e (U i)) (trivial-at-e (V j))) (*-identityˡ 1#)
    PairCharacter.splits (row i j) x a y b = trans (*-cong (mult (U i) x y) (mult (V j) a b))
      (M.medial _ _ _ _)
      where import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as M

    complete : (∀ c → Σ _ (λ i → ∀ x → value c x ≈ K i x)) →
      (∀ c → Σ _ (λ j → ∀ y → value c y ≈ L j y)) →
      ∀ p → Σ _ (λ i → Σ _ (λ j → ∀ x y → PairCharacter.v p x y ≈ entry i j x y))
    complete left right p with left (Restrict.fst p) | right (Restrict.snd p)
    ... | i , hi | j , hj = i , j , λ x y → trans (Restrict.factors p x y) (*-cong (hi x) (hj y))

    factorization : ∀ (f : Fin m → Fin n → Carrier) i j → sum m (λ x → sum n (λ y → entry i j x y * f x y)) ≈
      transform K (λ x → transform L (f x) j) i
    factorization f i j = sum-cong m _ _ (λ x → trans
      (sum-cong n _ _ (λ y → *-assoc (K i x) (L j y) (f x y)))
      (sum-mulˡ n (K i x) (λ y → L j y * f x y)))
